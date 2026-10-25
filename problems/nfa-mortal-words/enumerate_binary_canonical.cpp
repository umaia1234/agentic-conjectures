// Exhaustive enumeration of ordered binary 2-image-bounded NFAs on N labelled
// states with a state-relabelling (S_N) reduction on the first letter.
//
// Scope and reduction (default N = 5; compile with -DNFA_STATES=n for n<=6):
//
// * Global 2-image-boundedness (|q.w| <= 2 for all q, w) implies that every
//   one-letter row has size <= 2 and that each letter is 2-image-bounded on
//   its own (words over a single letter are words).  Letters are therefore
//   drawn from the R^N row-restricted letters, R = 1 + N + N(N-1)/2, and only
//   "self-bounded" letters are paired.  Pairs containing any other letter are
//   not 2-image-bounded and contribute nothing to the counts below.
// * S_N acts on letters by relabelling states.  The first letter a runs over
//   one canonical representative (minimum code) of every S_N-orbit of
//   self-bounded letters; the second letter b runs over all self-bounded
//   letters.  Each labelled ordered pair (a', b') is S_N-equivalent to a pair
//   (a, b) with a canonical, and for fixed a' in the orbit of a the map
//   b' -> sigma(b') is a bijection.  Hence weighting every examined pair by
//   |orbit(a)| reproduces exact labelled ordered counts.
// * For each examined pair the global filter explores all subsets reachable
//   from singletons, and the shortest mortal length is a BFS distance from the
//   full state set to the empty set in the powerset automaton.
//
// Output: labelled ordered counts and histogram, the maximum shortest mortal
// length, and every maximizer up to state relabelling (ordered letters), each
// listed as its S_N-canonical pair.  Usage: ./prog [threads] [record_min]
// (record_min > 0 additionally reports orbit counts for every length >=
// record_min).

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <mutex>
#include <set>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#ifndef NFA_STATES
#define NFA_STATES 5
#endif

namespace {

constexpr int N = NFA_STATES;
static_assert(N >= 1 && N <= 6, "subset masks are stored in 64-bit words");
constexpr int SUBSETS = 1 << N;
constexpr int FULL = SUBSETS - 1;

using Rows = std::array<std::uint8_t, N>;
using Action = std::array<std::uint8_t, SUBSETS>;

std::vector<std::uint8_t> row_options;          // masks of size <= 2
std::array<int, SUBSETS> row_index;             // mask -> option index or -1
std::uint64_t R = 0;                            // number of row options
std::uint64_t LETTERS = 0;                      // R^N
std::vector<std::array<int, N>> perms;          // all permutations of states
std::vector<std::array<std::uint8_t, SUBSETS>> perm_mask;  // sigma on masks

int popcount(unsigned x) { return __builtin_popcount(x); }

Rows decode(std::uint64_t code) {
  Rows rows{};
  for (int q = 0; q < N; ++q) {
    rows[q] = row_options[code % R];
    code /= R;
  }
  return rows;
}

std::uint64_t encode(const Rows& rows) {
  std::uint64_t code = 0;
  for (int q = N - 1; q >= 0; --q) code = code * R + row_index[rows[q]];
  return code;
}

Rows apply_perm(int p, const Rows& rows) {
  Rows out{};
  for (int q = 0; q < N; ++q) out[perms[p][q]] = perm_mask[p][rows[q]];
  return out;
}

Action make_action(const Rows& rows) {
  Action act{};
  act[0] = 0;
  for (int s = 1; s < SUBSETS; ++s) {
    act[s] = static_cast<std::uint8_t>(act[s & (s - 1)] | rows[__builtin_ctz(s)]);
  }
  return act;
}

bool self_bounded(const Action& act) {
  std::uint64_t seen = 0;
  std::uint8_t stack[SUBSETS];
  int sp = 0;
  for (int q = 0; q < N; ++q) {
    stack[sp++] = static_cast<std::uint8_t>(1 << q);
    seen |= 1ULL << (1 << q);
  }
  while (sp) {
    const std::uint8_t t = act[stack[--sp]];
    if (popcount(t) > 2) return false;
    if (!((seen >> t) & 1ULL)) {
      seen |= 1ULL << t;
      stack[sp++] = t;
    }
  }
  return true;
}

bool pair_bounded(const Action& a, const Action& b) {
  std::uint64_t seen = 0;
  std::uint8_t stack[SUBSETS];
  int sp = 0;
  for (int q = 0; q < N; ++q) {
    stack[sp++] = static_cast<std::uint8_t>(1 << q);
    seen |= 1ULL << (1 << q);
  }
  while (sp) {
    const std::uint8_t s = stack[--sp];
    const std::uint8_t x = a[s];
    const std::uint8_t y = b[s];
    if (popcount(x) > 2 || popcount(y) > 2) return false;
    if (!((seen >> x) & 1ULL)) {
      seen |= 1ULL << x;
      stack[sp++] = x;
    }
    if (!((seen >> y) & 1ULL)) {
      seen |= 1ULL << y;
      stack[sp++] = y;
    }
  }
  return true;
}

// Shortest word mapping the full set to the empty set, or -1.
int mortal_distance(const Action& a, const Action& b) {
  std::uint8_t queue[SUBSETS];
  std::uint8_t dist[SUBSETS];
  int head = 0, tail = 0;
  queue[tail++] = FULL;
  dist[FULL] = 0;
  std::uint64_t seen = 1ULL << FULL;
  while (head < tail) {
    const std::uint8_t s = queue[head++];
    const std::uint8_t x = a[s];
    const std::uint8_t y = b[s];
    if (x == 0 || y == 0) return dist[s] + 1;
    if (!((seen >> x) & 1ULL)) {
      seen |= 1ULL << x;
      dist[x] = static_cast<std::uint8_t>(dist[s] + 1);
      queue[tail++] = x;
    }
    if (!((seen >> y) & 1ULL)) {
      seen |= 1ULL << y;
      dist[y] = static_cast<std::uint8_t>(dist[s] + 1);
      queue[tail++] = y;
    }
  }
  return -1;
}

std::string format_rows(const Rows& rows) {
  std::string out = "[";
  for (int q = 0; q < N; ++q) {
    if (q) out += ",";
    out += "[";
    bool first = true;
    for (int t = 0; t < N; ++t) {
      if (rows[q] & (1 << t)) {
        if (!first) out += ",";
        out += std::to_string(t);
        first = false;
      }
    }
    out += "]";
  }
  return out + "]";
}

// Minimum of (code(sigma a), code(sigma b)) over sigma, as a single integer.
std::uint64_t canonical_pair(const Rows& a, const Rows& b) {
  std::uint64_t best = UINT64_MAX;
  for (std::size_t p = 0; p < perms.size(); ++p) {
    const std::uint64_t key =
        encode(apply_perm(static_cast<int>(p), a)) * LETTERS +
        encode(apply_perm(static_cast<int>(p), b));
    best = std::min(best, key);
  }
  return best;
}

struct Stats {
  std::uint64_t pairs_examined = 0;
  std::uint64_t bounded = 0;
  std::uint64_t incomplete = 0;
  std::array<std::uint64_t, SUBSETS + 1> hist{};
  std::array<std::uint64_t, SUBSETS + 1> hist_unweighted{};
  int max_len = -1;
  std::vector<std::pair<std::uint32_t, std::uint32_t>> record;  // (a idx, b idx)
  std::vector<std::pair<std::uint32_t, std::uint32_t>> high;    // len >= record_min
  std::vector<int> high_len;
};

Rows rows_of(const Action& act) {
  Rows rows{};
  for (int q = 0; q < N; ++q) rows[q] = act[1 << q];
  return rows;
}

double seconds_since(std::chrono::steady_clock::time_point t0) {
  return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
}

template <class F>
void run_parallel(unsigned threads, F&& body) {
  std::vector<std::thread> pool;
  for (unsigned t = 0; t < threads; ++t) pool.emplace_back(body, t);
  for (auto& th : pool) th.join();
}

}  // namespace

int main(int argc, char** argv) {
  const auto t0 = std::chrono::steady_clock::now();
  unsigned threads = argc > 1 ? static_cast<unsigned>(std::atoi(argv[1])) : 1;
  if (threads == 0) threads = 1;
  const int record_min = argc > 2 ? std::atoi(argv[2]) : 0;

  row_index.fill(-1);
  for (int s = 0; s < SUBSETS; ++s) {
    if (popcount(s) <= 2) {
      row_index[s] = static_cast<int>(row_options.size());
      row_options.push_back(static_cast<std::uint8_t>(s));
    }
  }
  R = row_options.size();
  LETTERS = 1;
  for (int q = 0; q < N; ++q) LETTERS *= R;

  std::array<int, N> pi{};
  for (int q = 0; q < N; ++q) pi[q] = q;
  do {
    perms.push_back(pi);
    std::array<std::uint8_t, SUBSETS> pm{};
    for (int s = 0; s < SUBSETS; ++s) {
      int t = 0;
      for (int q = 0; q < N; ++q) {
        if (s & (1 << q)) t |= 1 << pi[q];
      }
      pm[s] = static_cast<std::uint8_t>(t);
    }
    perm_mask.push_back(pm);
  } while (std::next_permutation(pi.begin(), pi.end()));
  const std::uint64_t group_order = perms.size();

  // Phase 1: all self-bounded letters, in increasing code order.
  std::vector<std::vector<Action>> parts(threads);
  run_parallel(threads, [&](unsigned t) {
    const std::uint64_t lo = LETTERS * t / threads;
    const std::uint64_t hi = LETTERS * (t + 1) / threads;
    for (std::uint64_t code = lo; code < hi; ++code) {
      const Action act = make_action(decode(code));
      if (self_bounded(act)) parts[t].push_back(act);
    }
  });
  std::vector<Action> sb_act;
  for (auto& part : parts) {
    sb_act.insert(sb_act.end(), part.begin(), part.end());
    std::vector<Action>().swap(part);
  }

  // Phase 2: canonical representatives (minimum code in the S_N-orbit) and
  // orbit sizes |S_N| / |stabiliser|.
  std::vector<std::uint8_t> is_canon(sb_act.size(), 0);
  std::vector<std::uint32_t> stab(sb_act.size(), 0);
  std::atomic<std::size_t> next_letter{0};
  run_parallel(threads, [&](unsigned) {
    for (;;) {
      const std::size_t begin = next_letter.fetch_add(4096);
      if (begin >= sb_act.size()) break;
      const std::size_t end = std::min(sb_act.size(), begin + 4096);
      for (std::size_t i = begin; i < end; ++i) {
        const Rows rows = rows_of(sb_act[i]);
        const std::uint64_t code = encode(rows);
        bool minimal = true;
        std::uint32_t fixed = 0;
        for (std::size_t p = 0; p < perms.size(); ++p) {
          const std::uint64_t c = encode(apply_perm(static_cast<int>(p), rows));
          if (c < code) {
            minimal = false;
            break;
          }
          if (c == code) ++fixed;
        }
        is_canon[i] = minimal ? 1 : 0;
        stab[i] = fixed;
      }
    }
  });
  std::vector<std::uint32_t> canon;
  std::vector<std::uint64_t> orbit_size;
  std::uint64_t orbit_total = 0;
  for (std::size_t i = 0; i < sb_act.size(); ++i) {
    if (!is_canon[i]) continue;
    canon.push_back(static_cast<std::uint32_t>(i));
    orbit_size.push_back(group_order / stab[i]);
    orbit_total += group_order / stab[i];
  }
  std::vector<std::uint8_t>().swap(is_canon);
  std::vector<std::uint32_t>().swap(stab);
  std::printf("N=%d row_options=%llu letters=%llu self_bounded_letters=%zu "
              "canonical_self_bounded_letters=%zu orbit_size_sum=%llu "
              "setup_seconds=%.1f\n",
              N, static_cast<unsigned long long>(R),
              static_cast<unsigned long long>(LETTERS), sb_act.size(), canon.size(),
              static_cast<unsigned long long>(orbit_total), seconds_since(t0));
  std::fflush(stdout);
  if (orbit_total != sb_act.size()) {
    std::printf("ERROR: orbit sizes do not sum to the number of letters\n");
    return 1;
  }

  // Phase 3: every canonical first letter against every self-bounded second
  // letter, in blocks of first letters so that each second letter is loaded
  // from memory once per block.
  constexpr std::size_t BLOCK = 16;
  const std::size_t blocks = (canon.size() + BLOCK - 1) / BLOCK;
  std::atomic<std::size_t> next_block{0};
  std::atomic<std::size_t> done_blocks{0};
  std::mutex merge_mutex;
  Stats total;
  run_parallel(threads, [&](unsigned) {
    Stats local;
    for (;;) {
      const std::size_t blk = next_block.fetch_add(1);
      if (blk >= blocks) break;
      const std::size_t k0 = blk * BLOCK;
      const std::size_t k1 = std::min(canon.size(), k0 + BLOCK);
      std::array<Action, BLOCK> a{};
      for (std::size_t k = k0; k < k1; ++k) a[k - k0] = sb_act[canon[k]];
      for (std::uint32_t bi = 0; bi < sb_act.size(); ++bi) {
        const Action& b = sb_act[bi];
        for (std::size_t k = k0; k < k1; ++k) {
          const Action& ak = a[k - k0];
          ++local.pairs_examined;
          if (!pair_bounded(ak, b)) continue;
          const std::uint64_t w = orbit_size[k];
          local.bounded += w;
          const int d = mortal_distance(ak, b);
          if (d < 0) continue;
          local.incomplete += w;
          local.hist[d] += w;
          ++local.hist_unweighted[d];
          if (d > local.max_len) {
            local.max_len = d;
            local.record.clear();
          }
          if (d == local.max_len) local.record.emplace_back(canon[k], bi);
          if (record_min > 0 && d >= record_min) {
            local.high.emplace_back(canon[k], bi);
            local.high_len.push_back(d);
          }
        }
      }
      const std::size_t done = done_blocks.fetch_add(1) + 1;
      if (N >= 6 && done % 50 == 0) {
        std::fprintf(stderr, "progress %zu/%zu blocks %.1fs\n", done, blocks,
                     seconds_since(t0));
      }
    }
    std::lock_guard<std::mutex> lock(merge_mutex);
    total.pairs_examined += local.pairs_examined;
    total.bounded += local.bounded;
    total.incomplete += local.incomplete;
    for (int d = 0; d <= SUBSETS; ++d) {
      total.hist[d] += local.hist[d];
      total.hist_unweighted[d] += local.hist_unweighted[d];
    }
    if (local.max_len > total.max_len) {
      total.max_len = local.max_len;
      total.record.clear();
    }
    if (local.max_len == total.max_len) {
      total.record.insert(total.record.end(), local.record.begin(), local.record.end());
    }
    total.high.insert(total.high.end(), local.high.begin(), local.high.end());
    total.high_len.insert(total.high_len.end(), local.high_len.begin(),
                          local.high_len.end());
  });

  std::printf("canonical_first_letters=%zu pairs_examined=%llu\n", canon.size(),
              static_cast<unsigned long long>(total.pairs_examined));
  if constexpr (N <= 5) {
    std::printf("ordered_raw=%llu ", 1ULL << (2 * N * N));
  }
  std::printf("ordered_row_restricted=%llu ordered_2_image_bounded=%llu "
              "ordered_incomplete=%llu maximum_shortest_mortal_length=%d\n",
              static_cast<unsigned long long>(LETTERS * LETTERS),
              static_cast<unsigned long long>(total.bounded),
              static_cast<unsigned long long>(total.incomplete), total.max_len);
  std::printf("ordered_histogram={");
  bool first = true;
  for (int d = 1; d <= SUBSETS; ++d) {
    if (!total.hist[d]) continue;
    std::printf("%s%d: %llu", first ? "" : ", ", d,
                static_cast<unsigned long long>(total.hist[d]));
    first = false;
  }
  std::printf("}\n");
  std::printf("canonical_first_letter_histogram={");
  first = true;
  for (int d = 1; d <= SUBSETS; ++d) {
    if (!total.hist_unweighted[d]) continue;
    std::printf("%s%d: %llu", first ? "" : ", ", d,
                static_cast<unsigned long long>(total.hist_unweighted[d]));
    first = false;
  }
  std::printf("}\n");

  // Maximizers up to state relabelling (ordered letters) and up to
  // relabelling plus letter swap.
  std::set<std::uint64_t> orbits, orbits_swap;
  for (const auto& [ai, bi] : total.record) {
    const Rows ra = rows_of(sb_act[ai]);
    const Rows rb = rows_of(sb_act[bi]);
    const std::uint64_t c = canonical_pair(ra, rb);
    orbits.insert(c);
    orbits_swap.insert(std::min(c, canonical_pair(rb, ra)));
  }
  const std::uint64_t labelled_max = total.max_len > 0 ? total.hist[total.max_len] : 0;
  std::printf("labelled_maximizers=%llu canonical_first_letter_maximizer_pairs=%zu "
              "maximizer_orbits_relabelling=%zu maximizer_orbits_relabelling_swap=%zu\n",
              static_cast<unsigned long long>(labelled_max), total.record.size(),
              orbits.size(), orbits_swap.size());
  int idx = 0;
  for (const std::uint64_t c : orbits) {
    const Rows a = decode(c / LETTERS);
    const Rows b = decode(c % LETTERS);
    std::printf("maximizer %d a=%s b=%s\n", idx++, format_rows(a).c_str(),
                format_rows(b).c_str());
  }
  if (record_min > 0) {
    std::map<int, std::set<std::uint64_t>> by_len;
    for (std::size_t i = 0; i < total.high.size(); ++i) {
      by_len[total.high_len[i]].insert(canonical_pair(rows_of(sb_act[total.high[i].first]),
                                                      rows_of(sb_act[total.high[i].second])));
    }
    for (const auto& [len, set] : by_len) {
      std::printf("length %d: orbits_relabelling=%zu\n", len, set.size());
    }
  }
  std::printf("threads=%u elapsed_seconds=%.1f\n", threads, seconds_since(t0));
  return 0;
}
