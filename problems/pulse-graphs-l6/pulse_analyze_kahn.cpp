#include <array>
#include <cstdint>
#include <iostream>
#include <queue>
#include <sstream>
#include <string>

// Independent upper-bound checker. Unlike pulse_analyze.cpp, it finds cycles
// by Kahn-peeling all noncycle states from each functional graph.
int main(int argc, char **argv) {
    const int n_expected = argc > 1 ? std::stoi(argv[1]) : 6;
    if (n_expected < 1 || n_expected > 6) return 2;

    std::uint64_t graphs = 0;
    std::uint64_t attaining = 0;
    int global_maximum = 0;
    std::string line;
    while (std::getline(std::cin, line)) {
        if (line.empty() || line[0] == '>' || line[0] == '<') continue;
        std::istringstream input(line);
        int n, m;
        if (!(input >> n >> m) || n != n_expected) return 2;

        std::array<unsigned, 6> incoming{};
        std::array<std::array<bool, 6>, 6> seen{};
        for (int i = 0; i < m; ++i) {
            int u, v;
            if (!(input >> u >> v) || u < 0 || u >= n || v < 0 || v >= n || u == v ||
                seen[u][v]) return 2;
            seen[u][v] = true;
            incoming[v] |= 1U << u;
        }
        int extra;
        if (input >> extra) return 2;

        const int state_count = 1 << n;
        std::array<unsigned char, 64> successor{};
        std::array<unsigned char, 64> indegree{};
        for (int state = 0; state < state_count; ++state) {
            int next = 0;
            for (int v = 0; v < n; ++v) {
                const int count = __builtin_popcount(static_cast<unsigned>(state) & incoming[v]);
                if (count == 2 || count == 3 || count == 5) next |= 1 << v;
            }
            successor[state] = static_cast<unsigned char>(next);
            ++indegree[next];
        }

        std::queue<int> peel;
        std::array<bool, 64> removed{};
        for (int state = 0; state < state_count; ++state) {
            if (indegree[state] == 0) peel.push(state);
        }
        while (!peel.empty()) {
            const int state = peel.front();
            peel.pop();
            removed[state] = true;
            const int next = successor[state];
            if (--indegree[next] == 0) peel.push(next);
        }

        int graph_maximum = 0;
        std::array<bool, 64> counted{};
        for (int start = 0; start < state_count; ++start) {
            if (removed[start] || counted[start]) continue;
            int length = 0;
            int state = start;
            do {
                counted[state] = true;
                ++length;
                state = successor[state];
            } while (state != start);
            if (length > graph_maximum) graph_maximum = length;
        }

        ++graphs;
        if (graph_maximum > global_maximum) {
            global_maximum = graph_maximum;
            attaining = 1;
        } else if (graph_maximum == global_maximum) {
            ++attaining;
        }
    }

    std::cout << "graphs=" << graphs << " max_period=" << global_maximum
              << " attaining_unlabeled=" << attaining << " method=kahn\n";
}
