// Exhaustive n=4, k=2 binary search with letter-swap reduction.
//
// Every globally 2-image-bounded letter has rows of size at most two (apply a
// one-letter word to a singleton).  There are therefore 11^4 = 14,641 possible
// letters.  We examine each unordered pair of letters once; swapping a and b
// preserves image-boundedness and shortest mortality, so this is exhaustive for
// the extremal value.  Weighted counters reconstruct ordered-pair counts.

#include <array>
#include <atomic>
#include <cstdint>
#include <iostream>
#include <mutex>
#include <string>
#include <vector>

#ifdef _OPENMP
#include <omp.h>
#endif

namespace {

#ifndef NFA_STATES
#define NFA_STATES 4
#endif

constexpr int N = NFA_STATES;
constexpr int SUBSETS = 1 << N;
constexpr int MAX_DISTANCE = SUBSETS - 1;
using LetterRows = std::array<std::uint8_t, N>;
using SubsetAction = std::array<std::uint8_t, SUBSETS>;

const std::array<int, SUBSETS> POPCOUNT = [] {
  std::array<int, SUBSETS> result{};
  for (int subset = 0; subset < SUBSETS; ++subset) {
    result[subset] = __builtin_popcount(static_cast<unsigned>(subset));
  }
  return result;
}();

std::vector<LetterRows> generate_letters() {
  std::vector<std::uint8_t> allowed_rows;
  for (int subset = 0; subset < SUBSETS; ++subset) {
    if (POPCOUNT[subset] <= 2) {
      allowed_rows.push_back(static_cast<std::uint8_t>(subset));
    }
  }

  std::vector<LetterRows> letters;
  std::size_t letter_count = 1;
  for (int state = 0; state < N; ++state) letter_count *= allowed_rows.size();
  letters.reserve(letter_count);
  for (std::size_t code = 0; code < letter_count; ++code) {
    std::size_t remaining = code;
    LetterRows rows{};
    for (int state = 0; state < N; ++state) {
      rows[state] = allowed_rows[remaining % allowed_rows.size()];
      remaining /= allowed_rows.size();
    }
    letters.push_back(rows);
  }
  return letters;
}

SubsetAction make_action(const LetterRows& rows) {
  SubsetAction action{};
  for (int subset = 0; subset < SUBSETS; ++subset) {
    std::uint8_t image = 0;
    for (int state = 0; state < N; ++state) {
      if ((subset & (1 << state)) != 0) {
        image = static_cast<std::uint8_t>(image | rows[state]);
      }
    }
    action[subset] = image;
  }
  return action;
}

bool is_two_image_bounded(const SubsetAction& first,
                          const SubsetAction& second) {
  std::array<std::uint8_t, SUBSETS> stack{};
  int stack_size = 0;
  std::uint16_t seen = 0;
  for (int state = 0; state < N; ++state) {
    const std::uint8_t singleton = static_cast<std::uint8_t>(1 << state);
    stack[stack_size++] = singleton;
    seen = static_cast<std::uint16_t>(seen | (1u << singleton));
  }

  while (stack_size != 0) {
    const std::uint8_t subset = stack[--stack_size];
    const std::array<std::uint8_t, 2> targets = {first[subset], second[subset]};
    for (std::uint8_t target : targets) {
      if (POPCOUNT[target] > 2) {
        return false;
      }
      const std::uint16_t target_bit = static_cast<std::uint16_t>(1u << target);
      if ((seen & target_bit) == 0) {
        seen = static_cast<std::uint16_t>(seen | target_bit);
        stack[stack_size++] = target;
      }
    }
  }
  return true;
}

int shortest_mortal_distance(const SubsetAction& first,
                             const SubsetAction& second) {
  std::array<std::uint8_t, SUBSETS> queue{};
  std::array<std::uint8_t, SUBSETS> distance{};
  int head = 0;
  int tail = 0;
  constexpr std::uint8_t full_set = SUBSETS - 1;
  queue[tail++] = full_set;
  std::uint16_t seen = static_cast<std::uint16_t>(1u << full_set);

  while (head < tail) {
    const std::uint8_t subset = queue[head++];
    const std::array<std::uint8_t, 2> targets = {first[subset], second[subset]};
    for (std::uint8_t target : targets) {
      if (target == 0) {
        return static_cast<int>(distance[subset]) + 1;
      }
      const std::uint16_t target_bit = static_cast<std::uint16_t>(1u << target);
      if ((seen & target_bit) == 0) {
        seen = static_cast<std::uint16_t>(seen | target_bit);
        distance[target] = static_cast<std::uint8_t>(distance[subset] + 1);
        queue[tail++] = target;
      }
    }
  }
  return -1;
}

std::string format_rows(const LetterRows& rows) {
  std::string output = "[";
  for (int state = 0; state < N; ++state) {
    if (state != 0) output += ",";
    output += "{";
    bool first = true;
    for (int destination = 0; destination < N; ++destination) {
      if ((rows[state] & (1 << destination)) != 0) {
        if (!first) output += ",";
        output += std::to_string(destination);
        first = false;
      }
    }
    output += "}";
  }
  output += "]";
  return output;
}

}  // namespace

int main() {
  const std::vector<LetterRows> rows = generate_letters();
  std::vector<SubsetAction> actions;
  actions.reserve(rows.size());
  for (const LetterRows& letter : rows) actions.push_back(make_action(letter));

  std::uint64_t ordered_bounded = 0;
  std::uint64_t ordered_incomplete = 0;
  std::array<std::uint64_t, MAX_DISTANCE + 1> ordered_histogram{};
  int global_maximum = -1;
  std::size_t witness_first = 0;
  std::size_t witness_second = 0;
  std::mutex witness_mutex;

#pragma omp parallel
  {
    std::uint64_t local_bounded = 0;
    std::uint64_t local_incomplete = 0;
    std::array<std::uint64_t, MAX_DISTANCE + 1> local_histogram{};
    int local_maximum = -1;
    std::size_t local_first = 0;
    std::size_t local_second = 0;

#pragma omp for schedule(dynamic, 1)
    for (std::size_t first_index = 0; first_index < actions.size(); ++first_index) {
      for (std::size_t second_index = first_index; second_index < actions.size();
           ++second_index) {
        const std::uint64_t ordered_weight = first_index == second_index ? 1 : 2;
        const SubsetAction& first = actions[first_index];
        const SubsetAction& second = actions[second_index];
        if (!is_two_image_bounded(first, second)) continue;
        local_bounded += ordered_weight;
        const int distance = shortest_mortal_distance(first, second);
        if (distance < 0) continue;
        local_incomplete += ordered_weight;
        local_histogram[distance] += ordered_weight;
        if (distance > local_maximum) {
          local_maximum = distance;
          local_first = first_index;
          local_second = second_index;
        }
      }
    }

#pragma omp atomic
    ordered_bounded += local_bounded;
#pragma omp atomic
    ordered_incomplete += local_incomplete;
    for (int distance = 1; distance <= MAX_DISTANCE; ++distance) {
#pragma omp atomic
      ordered_histogram[distance] += local_histogram[distance];
    }
    if (local_maximum >= 0) {
      std::lock_guard<std::mutex> lock(witness_mutex);
      if (local_maximum > global_maximum) {
        global_maximum = local_maximum;
        witness_first = local_first;
        witness_second = local_second;
      }
    }
  }

  const std::uint64_t ordered_raw =
      static_cast<std::uint64_t>(rows.size()) * rows.size();
  const std::uint64_t unordered_examined =
      static_cast<std::uint64_t>(rows.size()) * (rows.size() + 1) / 2;
  std::cout << "letters=" << rows.size() << " unordered_examined=" << unordered_examined
            << " ordered_raw=" << ordered_raw << '\n';
  std::cout << "ordered_2_image_bounded=" << ordered_bounded
            << " ordered_incomplete=" << ordered_incomplete
            << " maximum_shortest_mortal_length=" << global_maximum << '\n';
  std::cout << "ordered_histogram={";
  bool first_entry = true;
  for (int distance = 1; distance <= MAX_DISTANCE; ++distance) {
    if (ordered_histogram[distance] == 0) continue;
    if (!first_entry) std::cout << ",";
    std::cout << distance << ":" << ordered_histogram[distance];
    first_entry = false;
  }
  std::cout << "}\n";
  std::cout << "witness_letter_indices=(" << witness_first << "," << witness_second
            << ") a=" << format_rows(rows[witness_first])
            << " b=" << format_rows(rows[witness_second]) << '\n';
}
