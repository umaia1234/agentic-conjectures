// Fast deterministic random lower-bound search for binary, 2-image-bounded
// five-state NFAs.  Every generated one-letter row has size at most two; the
// full word-closure condition is still checked before mortality is measured.

#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

namespace {

constexpr int N = 5;
constexpr int SUBSETS = 1 << N;
using Rows = std::array<std::uint8_t, N>;
using Action = std::array<std::uint8_t, SUBSETS>;

struct SplitMix64 {
  std::uint64_t state;
  std::uint64_t next() {
    std::uint64_t z = (state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
  }
};

Action make_action(const Rows& rows) {
  Action action{};
  for (int subset = 0; subset < SUBSETS; ++subset) {
    int image = 0;
    for (int state = 0; state < N; ++state) {
      if (subset & (1 << state)) image |= rows[state];
    }
    action[subset] = static_cast<std::uint8_t>(image);
  }
  return action;
}

bool two_image_bounded(const Action& a, const Action& b) {
  std::array<std::uint8_t, SUBSETS> stack{};
  int top = 0;
  std::uint32_t seen = 0;
  for (int state = 0; state < N; ++state) {
    const int singleton = 1 << state;
    seen |= 1u << singleton;
    stack[top++] = static_cast<std::uint8_t>(singleton);
  }
  while (top) {
    const int subset = stack[--top];
    for (const int target : {static_cast<int>(a[subset]),
                             static_cast<int>(b[subset])}) {
      if (__builtin_popcount(static_cast<unsigned>(target)) > 2) return false;
      if (!(seen & (1u << target))) {
        seen |= 1u << target;
        stack[top++] = static_cast<std::uint8_t>(target);
      }
    }
  }
  return true;
}

int shortest_mortal(const Action& a, const Action& b, std::string* word) {
  std::array<std::uint8_t, SUBSETS> queue{};
  std::array<std::int8_t, SUBSETS> distance{};
  std::array<std::int8_t, SUBSETS> previous{};
  std::array<std::int8_t, SUBSETS> previous_letter{};
  distance.fill(-1);
  previous.fill(-1);
  int head = 0, tail = 0;
  constexpr int full = SUBSETS - 1;
  queue[tail++] = full;
  distance[full] = 0;
  while (head < tail) {
    const int subset = queue[head++];
    for (int letter = 0; letter < 2; ++letter) {
      const int target = letter == 0 ? a[subset] : b[subset];
      if (distance[target] >= 0) continue;
      distance[target] = static_cast<std::int8_t>(distance[subset] + 1);
      previous[target] = static_cast<std::int8_t>(subset);
      previous_letter[target] = static_cast<std::int8_t>(letter);
      queue[tail++] = static_cast<std::uint8_t>(target);
    }
  }
  if (distance[0] < 0) return -1;
  std::string reversed;
  for (int current = 0; current != full; current = previous[current]) {
    reversed.push_back(previous_letter[current] == 0 ? 'a' : 'b');
  }
  word->assign(reversed.rbegin(), reversed.rend());
  return distance[0];
}

std::string format_rows(const Rows& rows) {
  std::string result = "[";
  for (int state = 0; state < N; ++state) {
    if (state) result += ",";
    result += "[";
    bool first = true;
    for (int target = 0; target < N; ++target) {
      if (rows[state] & (1 << target)) {
        if (!first) result += ",";
        result += std::to_string(target);
        first = false;
      }
    }
    result += "]";
  }
  return result + "]";
}

}  // namespace

int main(int argc, char** argv) {
  const std::uint64_t samples =
      argc > 1 ? std::stoull(argv[1]) : 100'000'000ULL;
  const std::uint64_t seed =
      argc > 2 ? std::stoull(argv[2]) : 20'260'811ULL;
  std::vector<std::uint8_t> allowed;
  for (int subset = 0; subset < SUBSETS; ++subset) {
    if (__builtin_popcount(static_cast<unsigned>(subset)) <= 2) {
      allowed.push_back(static_cast<std::uint8_t>(subset));
    }
  }
  if (allowed.size() != 16) return 2;

  SplitMix64 rng{seed};
  std::uint64_t bounded = 0, incomplete = 0;
  int best = -1;
  for (std::uint64_t candidate = 0; candidate < samples; ++candidate) {
    Rows rows_a{}, rows_b{};
    for (int state = 0; state < N; ++state) {
      rows_a[state] = allowed[rng.next() & 15u];
      rows_b[state] = allowed[rng.next() & 15u];
    }
    const Action a = make_action(rows_a);
    const Action b = make_action(rows_b);
    if (!two_image_bounded(a, b)) continue;
    ++bounded;
    std::string word;
    const int distance = shortest_mortal(a, b, &word);
    if (distance < 0) continue;
    ++incomplete;
    if (distance <= best) continue;
    best = distance;
    std::cout << "candidate=" << candidate << " best_length=" << best
              << " word=" << word << " a=" << format_rows(rows_a)
              << " b=" << format_rows(rows_b) << '\n';
  }
  std::cout << "done samples=" << samples << " bounded=" << bounded
            << " incomplete=" << incomplete << " best=" << best << '\n';
}
