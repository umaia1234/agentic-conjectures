// Seeded simulated-annealing search for long shortest mortal words in binary,
// 2-image-bounded NFAs on N states (default N = 7).  Lower bounds only.
//
// A candidate is an ordered pair of letters whose one-letter rows have size
// at most two.  Its score is -1 if the pair is not globally 2-image-bounded
// (explored from all singletons), 0 if it has no mortal word, and otherwise
// the BFS distance from the full state set to the empty set.  A move replaces
// one row of one letter.  Moves to invalid or complete candidates are always
// rejected; other moves are accepted by the Metropolis rule.
//
// Seeds are read from a text file: each non-empty line holds 2*N row masks
// (letter a rows 0..N-1, then letter b rows 0..N-1), bit t of a row mask meaning
// that the state goes to t.  Lines with fewer masks describe smaller automata
// and are padded with dead states (empty rows) up to N states.  Restart r
// starts from seed r mod (number of seeds); with no seed file ("-"), or if the
// seed is not a valid incomplete automaton, it starts from a random valid one.
//
// Usage: ./prog seeds.txt threads restarts steps seed [first_restart]
// Restart r uses its own generator seeded from (seed, r), so its trajectory
// does not depend on the thread count; "restart r finished" lines report the
// best automaton of each restart, and every new global best is printed with a
// shortest mortal word.

#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#ifndef NFA_STATES
#define NFA_STATES 7
#endif

namespace {

constexpr int N = NFA_STATES;
static_assert(N >= 2 && N <= 7, "subsets are stored in 8-bit masks");
constexpr int SUBSETS = 1 << N;
constexpr int FULL = SUBSETS - 1;
using Rows = std::array<std::uint8_t, N>;
using Action = std::array<std::uint8_t, SUBSETS>;
using Seen = std::array<std::uint64_t, (SUBSETS + 63) / 64>;

struct Rng {
  std::uint64_t s;
  std::uint64_t next() {
    std::uint64_t z = (s += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
  }
  double uniform() { return (next() >> 11) * (1.0 / 9007199254740992.0); }
};

std::vector<std::uint8_t> options;  // row masks of size <= 2

bool test_and_set(Seen& seen, int s) {
  const std::uint64_t bit = 1ULL << (s & 63);
  if (seen[s >> 6] & bit) return true;
  seen[s >> 6] |= bit;
  return false;
}

void fill(const Rows& rows, Action& act) {
  act[0] = 0;
  for (int s = 1; s < SUBSETS; ++s) {
    act[s] = static_cast<std::uint8_t>(act[s & (s - 1)] | rows[__builtin_ctz(s)]);
  }
}

int score(const Action& a, const Action& b, std::string* word) {
  std::uint8_t stack[SUBSETS];
  int sp = 0;
  Seen seen{};
  for (int q = 0; q < N; ++q) {
    stack[sp++] = static_cast<std::uint8_t>(1 << q);
    test_and_set(seen, 1 << q);
  }
  while (sp) {
    const int s = stack[--sp];
    for (const int t : {static_cast<int>(a[s]), static_cast<int>(b[s])}) {
      if (__builtin_popcount(static_cast<unsigned>(t)) > 2) return -1;
      if (!test_and_set(seen, t)) stack[sp++] = static_cast<std::uint8_t>(t);
    }
  }
  std::uint8_t queue[SUBSETS];
  std::uint8_t dist[SUBSETS];
  std::uint8_t parent[SUBSETS];
  std::uint8_t via[SUBSETS];
  int head = 0, tail = 0;
  Seen visited{};
  queue[tail++] = FULL;
  dist[FULL] = 0;
  test_and_set(visited, FULL);
  while (head < tail) {
    const int s = queue[head++];
    for (int l = 0; l < 2; ++l) {
      const int t = l == 0 ? a[s] : b[s];
      if (test_and_set(visited, t)) continue;
      dist[t] = static_cast<std::uint8_t>(dist[s] + 1);
      parent[t] = static_cast<std::uint8_t>(s);
      via[t] = static_cast<std::uint8_t>(l);
      if (t == 0) {
        if (word) {
          std::string w;
          for (int c = 0; c != FULL; c = parent[c]) w.push_back(via[c] ? 'b' : 'a');
          word->assign(w.rbegin(), w.rend());
        }
        return dist[t];
      }
      queue[tail++] = static_cast<std::uint8_t>(t);
    }
  }
  return 0;
}

std::string show(const Rows& rows) {
  std::string out = "[";
  for (int q = 0; q < N; ++q) {
    out += q ? ",[" : "[";
    bool first = true;
    for (int t = 0; t < N; ++t) {
      if (rows[q] & (1 << t)) {
        out += first ? "" : ",";
        out += std::to_string(t);
        first = false;
      }
    }
    out += "]";
  }
  return out + "]";
}

}  // namespace

int main(int argc, char** argv) {
  const std::string seed_file = argc > 1 ? argv[1] : "";
  const int threads = argc > 2 ? std::max(1, std::atoi(argv[2])) : 1;
  const long restarts = argc > 3 ? std::atol(argv[3]) : 60;
  const long steps = argc > 4 ? std::atol(argv[4]) : 2000000;
  const std::uint64_t base_seed = argc > 5 ? std::strtoull(argv[5], nullptr, 10) : 1;
  const long first_restart = argc > 6 ? std::atol(argv[6]) : 0;
  for (int s = 0; s < (1 << N); ++s) {
    if (__builtin_popcount(static_cast<unsigned>(s)) <= 2) {
      options.push_back(static_cast<std::uint8_t>(s));
    }
  }

  std::vector<std::pair<Rows, Rows>> seeds;
  if (!seed_file.empty() && seed_file != "-") {
    std::ifstream in(seed_file);
    std::string line;
    while (std::getline(in, line)) {
      std::istringstream ss(line);
      std::vector<int> masks;
      int m;
      while (ss >> m) masks.push_back(m);
      if (masks.empty()) continue;
      const int n = static_cast<int>(masks.size()) / 2;
      if (2 * n != static_cast<int>(masks.size()) || n > N) continue;
      Rows a{}, b{};
      for (int q = 0; q < n; ++q) {
        a[q] = static_cast<std::uint8_t>(masks[q]);
        b[q] = static_cast<std::uint8_t>(masks[n + q]);
      }
      seeds.emplace_back(a, b);
    }
  }
  std::printf("N=%d seeds=%zu threads=%d restarts=%ld steps=%ld seed=%llu "
              "first_restart=%ld\n",
              N, seeds.size(), threads, restarts, steps,
              static_cast<unsigned long long>(base_seed), first_restart);
  std::fflush(stdout);

  std::mutex lock;
  std::atomic<int> global_best{-1};
  std::atomic<long> next_restart{0};
  std::vector<std::thread> pool;
  for (int t = 0; t < threads; ++t) {
    pool.emplace_back([&]() {
      for (;;) {
        const long r = first_restart + next_restart.fetch_add(1);
        if (r >= first_restart + restarts) break;
        Rng rng{base_seed * 1000003ULL + static_cast<std::uint64_t>(r)};
        Rows ra{}, rb{};
        Action a{}, b{};
        int value = -1;
        if (!seeds.empty()) {
          ra = seeds[r % seeds.size()].first;
          rb = seeds[r % seeds.size()].second;
          fill(ra, a);
          fill(rb, b);
          value = score(a, b, nullptr);
        }
        while (value < 1) {  // random valid incomplete start
          for (int q = 0; q < N; ++q) {
            ra[q] = options[rng.next() % options.size()];
            rb[q] = options[rng.next() % options.size()];
          }
          fill(ra, a);
          fill(rb, b);
          value = score(a, b, nullptr);
        }
        int best = value;
        Rows best_a = ra, best_b = rb;
        for (long step = 0; step < steps; ++step) {
          const double temp = 1.5 * (1.0 - static_cast<double>(step) / steps) + 0.05;
          const bool which = rng.next() & 1;
          const int q = static_cast<int>(rng.next() % N);
          Rows& rows = which ? rb : ra;
          const std::uint8_t old = rows[q];
          const std::uint8_t neu = options[rng.next() % options.size()];
          if (neu == old) continue;
          rows[q] = neu;
          Action& act = which ? b : a;
          fill(rows, act);
          const int v = score(a, b, nullptr);
          const bool accept =
              v >= 1 && (v >= value || rng.uniform() < std::exp((v - value) / temp));
          if (!accept) {
            rows[q] = old;
            fill(rows, act);
            continue;
          }
          value = v;
          if (value > best) {
            best = value;
            best_a = ra;
            best_b = rb;
          }
          if (value >= global_best) {
            std::lock_guard<std::mutex> guard(lock);
            if (value > global_best) {
              global_best = value;
              std::string word;
              score(a, b, &word);
              std::printf("restart=%ld step=%ld best=%d word=%s a=%s b=%s\n", r, step,
                          value, word.c_str(), show(ra).c_str(), show(rb).c_str());
              std::fflush(stdout);
            }
          }
        }
        std::lock_guard<std::mutex> guard(lock);
        std::printf("restart %ld finished best=%d a=%s b=%s\n", r, best,
                    show(best_a).c_str(), show(best_b).c_str());
        std::fflush(stdout);
      }
    });
  }
  for (auto& th : pool) th.join();
  std::printf("done global_best=%d\n", global_best.load());
  return 0;
}
