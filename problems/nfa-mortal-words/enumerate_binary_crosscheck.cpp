// Independent cross-check enumerator for ordered binary 2-image-bounded NFAs.
//
// This program deliberately shares no code with enumerate_binary_canonical.cpp
// and uses different algorithms for every step:
//
// * A letter is an N x N Boolean matrix packed row-major into a uint64
//   (bit q*N+t means t is in q.x).  Letters are generated row by row; a row
//   with three or more entries is pruned because then |{q}.x| >= 3 already
//   violates the definition for the one-letter word x.  For N <= 5 the program
//   also counts, by brute force over all 2^(N*N) matrices, the letters that are
//   2-image-bounded on their own and checks that the row-by-row generator
//   produced exactly that many.
// * A single letter x is 2-image-bounded on its own iff every orbit
//   {q}, {q}.x, {q}.x^2, ... stays within sets of size <= 2; this is tested by
//   iterating each orbit until it repeats.
// * A pair (a, b) is tested by a set-at-a-time closure of the family of
//   subsets reachable from the singletons (frontier expansion on a bitmask
//   indexed by subsets).
// * The shortest mortal length is computed by a backward fixpoint: K_0 = {∅},
//   K_t = K_{t-1} ∪ {S : S.a ∈ K_{t-1} or S.b ∈ K_{t-1}}, restricted to the
//   subsets reachable from the full set; the answer is the least t with the
//   full set in K_t.
// * Symmetry: mode "full" examines every ordered pair of letters with no
//   reduction at all (feasible for N <= 5).  Mode "orbit" lets the SECOND
//   letter run over the maximum-matrix representative of each S_N-orbit and
//   the first letter over all letters, weighting each pair by the orbit size,
//   which is computed by listing the orbit explicitly.
//
// Usage: ./prog full|orbit [threads]
// Prints labelled ordered counts in the same key=value format as the other
// enumerators, followed by one "pair a=... b=..." line per examined maximizer.

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#ifndef NFA_STATES
#define NFA_STATES 5
#endif

static const int kN = NFA_STATES;
static const int kSubsets = 1 << kN;
static const int kFull = kSubsets - 1;
static_assert(NFA_STATES >= 1 && NFA_STATES <= 6, "families are 64-bit masks");

typedef std::uint64_t Matrix;

struct Letter {
  Matrix m;
  std::uint8_t image[1 << NFA_STATES];  // image[S] = S.x
};

static unsigned row_of(Matrix m, int q) {
  return static_cast<unsigned>((m >> (q * kN)) & ((1u << kN) - 1));
}

static unsigned bits(unsigned x) {
  unsigned c = 0;
  for (; x; x >>= 1) c += x & 1u;
  return c;
}

static void fill_images(Letter* x) {
  for (int s = 0; s < kSubsets; ++s) {
    unsigned img = 0;
    for (int q = 0; q < kN; ++q) {
      if ((s >> q) & 1) img |= row_of(x->m, q);
    }
    x->image[s] = static_cast<std::uint8_t>(img);
  }
}

// Orbit iteration of one letter on each singleton.
static bool letter_alone_ok(Matrix m) {
  for (int q = 0; q < kN; ++q) {
    unsigned cur = 1u << q;
    // There are at most 1 + N + N(N-1)/2 sets of size <= 2, so an orbit that
    // stays small repeats within that many steps.
    for (int step = 0; step <= kSubsets; ++step) {
      unsigned nxt = 0;
      for (int p = 0; p < kN; ++p) {
        if ((cur >> p) & 1) nxt |= row_of(m, p);
      }
      if (bits(nxt) > 2) return false;
      cur = nxt;
    }
  }
  return true;
}

static void generate_rows(int q, Matrix partial, std::vector<Matrix>* out) {
  if (q == kN) {
    if (letter_alone_ok(partial)) out->push_back(partial);
    return;
  }
  for (unsigned row = 0; row < (1u << kN); ++row) {
    if (bits(row) > 2) continue;  // {q}.x = row must have size <= 2
    generate_rows(q + 1, partial | (static_cast<Matrix>(row) << (q * kN)), out);
  }
}

static std::uint64_t kSmall = 0;  // family of subsets of size <= 2

static bool pair_ok(const Letter& a, const Letter& b) {
  std::uint64_t reach = 0;
  for (int q = 0; q < kN; ++q) reach |= 1ULL << (1u << q);
  std::uint64_t frontier = reach;
  while (frontier) {
    std::uint64_t next = 0;
    for (std::uint64_t f = frontier; f; f &= f - 1) {
      const int s = __builtin_ctzll(f);
      next |= (1ULL << a.image[s]) | (1ULL << b.image[s]);
    }
    if (next & ~kSmall) return false;
    frontier = next & ~reach;
    reach |= next;
  }
  return true;
}

// Returns the shortest mortal length, or -1 if the pair has no mortal word.
static int shortest_mortal(const Letter& a, const Letter& b, bool* error) {
  std::uint64_t family = 1ULL << kFull;
  std::uint64_t frontier = family;
  while (frontier) {
    std::uint64_t next = 0;
    for (std::uint64_t f = frontier; f; f &= f - 1) {
      const int s = __builtin_ctzll(f);
      next |= (1ULL << a.image[s]) | (1ULL << b.image[s]);
    }
    frontier = next & ~family;
    family |= next;
  }
  if (!(family & 1ULL)) return -1;
  std::uint64_t kill = 1ULL;  // {∅}
  int t = 0;
  while (!((kill >> kFull) & 1ULL)) {
    std::uint64_t add = 0;
    for (std::uint64_t f = family & ~kill; f; f &= f - 1) {
      const int s = __builtin_ctzll(f);
      if (((kill >> a.image[s]) & 1ULL) || ((kill >> b.image[s]) & 1ULL)) {
        add |= 1ULL << s;
      }
    }
    if (!add) {
      *error = true;
      return -1;
    }
    kill |= add;
    ++t;
  }
  return t;
}

static std::string show(Matrix m) {
  std::string out = "[";
  for (int q = 0; q < kN; ++q) {
    out += q ? ",[" : "[";
    bool first = true;
    for (int t = 0; t < kN; ++t) {
      if ((row_of(m, q) >> t) & 1) {
        out += first ? "" : ",";
        out += std::to_string(t);
        first = false;
      }
    }
    out += "]";
  }
  return out + "]";
}

static Matrix relabel(Matrix m, const int* sigma) {
  Matrix out = 0;
  for (int q = 0; q < kN; ++q) {
    for (int t = 0; t < kN; ++t) {
      if ((row_of(m, q) >> t) & 1) out |= 1ULL << (sigma[q] * kN + sigma[t]);
    }
  }
  return out;
}

struct Totals {
  std::uint64_t examined = 0, bounded = 0, incomplete = 0;
  std::uint64_t hist[(1 << NFA_STATES) + 1] = {0};
  int best = -1;
  std::vector<std::pair<Matrix, Matrix> > best_pairs;  // (a, b) as examined
  bool error = false;
};

int main(int argc, char** argv) {
  const auto t0 = std::chrono::steady_clock::now();
  if (argc < 2 || (std::strcmp(argv[1], "full") && std::strcmp(argv[1], "orbit"))) {
    std::fprintf(stderr, "usage: %s full|orbit [threads]\n", argv[0]);
    return 2;
  }
  const bool orbit_mode = std::strcmp(argv[1], "orbit") == 0;
  int threads = argc > 2 ? std::atoi(argv[2]) : 1;
  if (threads < 1) threads = 1;
  for (int s = 0; s < kSubsets; ++s) {
    if (bits(static_cast<unsigned>(s)) <= 2) kSmall |= 1ULL << s;
  }

  std::vector<Matrix> mats;
  generate_rows(0, 0, &mats);
  if (kN <= 5) {
    std::uint64_t brute = 0;
    for (Matrix m = 0; m < (1ULL << (kN * kN)); ++m) brute += letter_alone_ok(m);
    std::printf("bruteforce_self_bounded_letters=%" PRIu64 " generated=%zu %s\n", brute,
                mats.size(), brute == mats.size() ? "MATCH" : "MISMATCH");
    if (brute != mats.size()) return 1;
  }
  std::vector<Letter> letters(mats.size());
  for (std::size_t i = 0; i < mats.size(); ++i) {
    letters[i].m = mats[i];
    fill_images(&letters[i]);
  }

  // Second-letter list with weights.
  std::vector<std::size_t> second;
  std::vector<std::uint64_t> weight;
  if (!orbit_mode) {
    for (std::size_t i = 0; i < letters.size(); ++i) {
      second.push_back(i);
      weight.push_back(1);
    }
  } else {
    std::vector<std::vector<int> > group;
    std::vector<int> sigma(kN);
    for (int q = 0; q < kN; ++q) sigma[q] = q;
    do group.push_back(sigma); while (std::next_permutation(sigma.begin(), sigma.end()));
    std::vector<std::uint8_t> rep(letters.size(), 0);
    std::vector<std::uint64_t> osize(letters.size(), 0);
    std::atomic<std::size_t> cursor(0);
    std::vector<std::thread> pool;
    for (int t = 0; t < threads; ++t) {
      pool.emplace_back([&]() {
        std::vector<Matrix> orbit;
        for (;;) {
          const std::size_t i = cursor.fetch_add(1);
          if (i >= letters.size()) break;
          bool is_max = true;
          orbit.clear();
          for (const auto& g : group) {
            const Matrix img = relabel(letters[i].m, g.data());
            if (img > letters[i].m) {
              is_max = false;
              break;
            }
            orbit.push_back(img);
          }
          if (!is_max) continue;
          std::sort(orbit.begin(), orbit.end());
          rep[i] = 1;
          osize[i] = static_cast<std::uint64_t>(
              std::unique(orbit.begin(), orbit.end()) - orbit.begin());
        }
      });
    }
    for (auto& th : pool) th.join();
    std::uint64_t sum = 0;
    for (std::size_t i = 0; i < letters.size(); ++i) {
      if (!rep[i]) continue;
      second.push_back(i);
      weight.push_back(osize[i]);
      sum += osize[i];
    }
    std::printf("orbit_representatives=%zu orbit_size_sum=%" PRIu64 " %s\n", second.size(),
                sum, sum == letters.size() ? "MATCH" : "MISMATCH");
    if (sum != letters.size()) return 1;
  }
  std::printf("N=%d mode=%s letters=%zu second_letters=%zu setup_seconds=%.1f\n", kN,
              orbit_mode ? "orbit" : "full", letters.size(), second.size(),
              std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
  std::fflush(stdout);

  // Blocks of second letters against all first letters.
  const std::size_t kBlock = 16;
  const std::size_t nblocks = (second.size() + kBlock - 1) / kBlock;
  std::atomic<std::size_t> next_block(0);
  std::mutex lock;
  Totals total;
  std::vector<std::thread> pool;
  for (int t = 0; t < threads; ++t) {
    pool.emplace_back([&]() {
      Totals mine;
      for (;;) {
        const std::size_t blk = next_block.fetch_add(1);
        if (blk >= nblocks) break;
        const std::size_t lo = blk * kBlock;
        const std::size_t hi = std::min(second.size(), lo + kBlock);
        for (std::size_t ia = 0; ia < letters.size(); ++ia) {
          const Letter& a = letters[ia];
          for (std::size_t j = lo; j < hi; ++j) {
            const Letter& b = letters[second[j]];
            ++mine.examined;
            if (!pair_ok(a, b)) continue;
            mine.bounded += weight[j];
            const int len = shortest_mortal(a, b, &mine.error);
            if (len < 0) continue;
            mine.incomplete += weight[j];
            mine.hist[len] += weight[j];
            if (len > mine.best) {
              mine.best = len;
              mine.best_pairs.clear();
            }
            if (len == mine.best) mine.best_pairs.push_back(std::make_pair(a.m, b.m));
          }
        }
      }
      std::lock_guard<std::mutex> guard(lock);
      total.examined += mine.examined;
      total.bounded += mine.bounded;
      total.incomplete += mine.incomplete;
      for (int d = 0; d <= kSubsets; ++d) total.hist[d] += mine.hist[d];
      total.error = total.error || mine.error;
      if (mine.best > total.best) {
        total.best = mine.best;
        total.best_pairs.clear();
      }
      if (mine.best == total.best) {
        total.best_pairs.insert(total.best_pairs.end(), mine.best_pairs.begin(),
                                mine.best_pairs.end());
      }
    });
  }
  for (auto& th : pool) th.join();
  if (total.error) {
    std::printf("ERROR: backward fixpoint stalled\n");
    return 1;
  }
  std::sort(total.best_pairs.begin(), total.best_pairs.end());

  std::printf("pairs_examined=%" PRIu64 "\n", total.examined);
  std::printf("ordered_2_image_bounded=%" PRIu64 " ordered_incomplete=%" PRIu64
              " maximum_shortest_mortal_length=%d\n",
              total.bounded, total.incomplete, total.best);
  std::printf("ordered_histogram={");
  bool first = true;
  for (int d = 1; d <= kSubsets; ++d) {
    if (!total.hist[d]) continue;
    std::printf("%s%d: %" PRIu64, first ? "" : ", ", d, total.hist[d]);
    first = false;
  }
  std::printf("}\n");
  std::printf("labelled_maximizers=%" PRIu64 " examined_maximizer_pairs=%zu\n",
              total.best > 0 ? total.hist[total.best] : 0, total.best_pairs.size());
  for (const auto& p : total.best_pairs) {
    std::printf("pair a=%s b=%s\n", show(p.first).c_str(), show(p.second).c_str());
  }
  std::printf("threads=%d elapsed_seconds=%.1f\n", threads,
              std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
  return 0;
}
