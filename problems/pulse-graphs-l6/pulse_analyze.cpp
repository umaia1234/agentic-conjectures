#include <array>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

static bool prime_count(int x) { return x == 2 || x == 3 || x == 5; }

int main(int argc, char **argv) {
    const int expected_n = argc > 1 ? std::stoi(argv[1]) : 6;
    if (expected_n < 1 || expected_n > 6) return 2;

    std::string line;
    std::uint64_t graph_count = 0;
    int global_maximum = 0;
    std::uint64_t attaining_count = 0;
    std::vector<std::pair<int, int>> first_best_arcs;
    std::vector<int> first_best_cycle;

    // Input is the simple text format emitted by nauty-directg -T:
    // one line "n m u1 v1 ... um vm" per loopless digraph.
    while (std::getline(std::cin, line)) {
        if (line.empty() || line[0] == '>' || line[0] == '<') continue;
        std::istringstream input(line);
        int n, m;
        if (!(input >> n >> m)) continue;
        if (n != expected_n) {
            std::cerr << "unexpected n=" << n << "\n";
            return 2;
        }

        std::array<unsigned, 6> incoming{};
        std::array<std::array<bool, 6>, 6> seen_arc{};
        std::vector<std::pair<int, int>> arcs;
        for (int i = 0; i < m; ++i) {
            int u, v;
            if (!(input >> u >> v) || u == v || u < 0 || u >= n || v < 0 || v >= n ||
                seen_arc[u][v]) {
                std::cerr << "malformed arc list\n";
                return 2;
            }
            seen_arc[u][v] = true;
            incoming[v] |= 1U << u;
            arcs.emplace_back(u, v);
        }
        int extra;
        if (input >> extra) {
            std::cerr << "extra input field\n";
            return 2;
        }

        const unsigned state_count = 1U << n;
        std::array<unsigned char, 64> successor{};
        for (unsigned state = 0; state < state_count; ++state) {
            unsigned next = 0;
            for (int v = 0; v < n; ++v) {
                if (prime_count(__builtin_popcount(state & incoming[v]))) next |= 1U << v;
            }
            successor[state] = static_cast<unsigned char>(next);
        }

        // Enumerate every directed cycle of this exact functional graph.
        std::array<bool, 64> processed{};
        int graph_maximum = 0;
        std::vector<int> graph_best_cycle;
        for (int start = 0; start < static_cast<int>(state_count); ++start) {
            if (processed[start]) continue;
            std::array<signed char, 64> position;
            position.fill(-1);
            std::vector<int> path;
            int state = start;
            while (!processed[state] && position[state] < 0) {
                position[state] = static_cast<signed char>(path.size());
                path.push_back(state);
                state = successor[state];
            }
            if (!processed[state] && position[state] >= 0) {
                const int length = static_cast<int>(path.size()) - position[state];
                if (length > graph_maximum) {
                    graph_maximum = length;
                    graph_best_cycle.assign(path.begin() + position[state], path.end());
                }
            }
            for (int visited : path) processed[visited] = true;
        }

        ++graph_count;
        if (graph_maximum > global_maximum) {
            global_maximum = graph_maximum;
            attaining_count = 1;
            first_best_arcs = arcs;
            first_best_cycle = graph_best_cycle;
            std::cerr << "new_max=" << global_maximum << " graph=" << graph_count
                      << " arcs=" << m << "\n";
        } else if (graph_maximum == global_maximum) {
            ++attaining_count;
        }
    }

    std::cout << "graphs=" << graph_count << " max_period=" << global_maximum
              << " attaining_unlabeled=" << attaining_count << "\n";
    std::cout << "arcs=";
    for (std::size_t i = 0; i < first_best_arcs.size(); ++i) {
        if (i) std::cout << ',';
        std::cout << first_best_arcs[i].first << "->" << first_best_arcs[i].second;
    }
    std::cout << "\ncycle=";
    for (std::size_t i = 0; i < first_best_cycle.size(); ++i) {
        if (i) std::cout << ',';
        std::cout << first_best_cycle[i];
    }
    std::cout << "\n";
}
