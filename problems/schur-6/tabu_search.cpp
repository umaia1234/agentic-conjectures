// Local search for sum-free k-colorings of [1, n] (C++17, standard library only).
//
// Positions are integers 1..n, or folded positions p = min(x, n+1-x) when
// --palindromic is given (then c(x) = c(n+1-x) by construction).  Every
// Schur triple x + y = z <= n becomes a "cell": the set of its distinct
// positions (one, two or three of them).  A cell is violated when all its
// positions share a color.  Moves recolor one position; a recolored position
// may not return to its old color for a randomised tabu tenure (aspiration
// on new bests).  Two objectives:
//   default      number of violated cells (TabuCol-style tabu search, with a
//                random perturbation of the best coloring after stagnation);
//   --breakout   sum of cell weights over violated cells; whenever no move
//                lowers it, the weight of every violated cell grows by one
//                (Morris' breakout method), and every --smooth such bumps
//                all weights are halved (rounding up).
// Optional frame constraints (--frame Q D or --frame6 Q, as in
// template_sat.py) fix or forbid colors at folded positions.
//
// Output: the best coloring found (fewest violated cells), in the six-row
// format read by verify.py and check_partition.cpp (colors renumbered by
// least element).  Exit status 0 iff it is sum-free.
//
// Usage: tabu_search --maximum N [--palindromic] [--frame Q D | --frame6 Q]
//          [--no-middle] [--colors K] [--seed S] [--seconds T] [--start FILE]
//          [--output FILE] [--stagnation I] [--perturb M] [--breakout]
//          [--smooth B]
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace {

struct Options {
    int n = 538;
    int k = 6;
    bool palindromic = false;
    int frame_q = 0, frame_d = 0, frame6_q = 0;
    bool middle = true;
    std::uint64_t seed = 1;
    double seconds = 60.0;
    std::string start, output;
    long stagnation = 200000;
    int perturb = 10;
    bool breakout = false;
    long smooth = 1000;
};

Options parse(int argc, char** argv) {
    Options o;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        auto next = [&]() -> std::string {
            if (i + 1 >= argc) {
                std::cerr << "missing value for " << a << "\n";
                std::exit(2);
            }
            return argv[++i];
        };
        if (a == "--maximum") o.n = std::stoi(next());
        else if (a == "--colors") o.k = std::stoi(next());
        else if (a == "--palindromic") o.palindromic = true;
        else if (a == "--frame") {
            o.frame_q = std::stoi(next());
            o.frame_d = std::stoi(next());
        } else if (a == "--frame6") o.frame6_q = std::stoi(next());
        else if (a == "--no-middle") o.middle = false;
        else if (a == "--seed") o.seed = std::stoull(next());
        else if (a == "--seconds") o.seconds = std::stod(next());
        else if (a == "--start") o.start = next();
        else if (a == "--output") o.output = next();
        else if (a == "--stagnation") o.stagnation = std::stol(next());
        else if (a == "--perturb") o.perturb = std::stoi(next());
        else if (a == "--breakout") o.breakout = true;
        else if (a == "--smooth") o.smooth = std::stol(next());
        else {
            std::cerr << "unknown option " << a << "\n";
            std::exit(2);
        }
    }
    return o;
}

struct Incidence {
    int a, b, cell;  // other members (b = -1 for two-position cells)
};

}  // namespace

int main(int argc, char** argv) {
    const Options o = parse(argc, argv);
    const int n = o.n, k = o.k;
    const int width = o.palindromic ? (n + 1) / 2 : n;
    auto fold = [&](int x) { return o.palindromic ? std::min(x, n + 1 - x) : x; };

    // Cells (deduplicated position sets of Schur triples).
    std::set<std::vector<int>> cell_set;
    for (int x = 1; 2 * x <= n; ++x) {
        for (int y = x; x + y <= n; ++y) {
            std::vector<int> c = {fold(x), fold(y), fold(x + y)};
            std::sort(c.begin(), c.end());
            c.erase(std::unique(c.begin(), c.end()), c.end());
            if (c.size() == 1) {
                std::cerr << "position " << c[0] << " can never be colored\n";
                return 1;
            }
            cell_set.insert(c);
        }
    }
    const std::vector<std::vector<int>> cells(cell_set.begin(), cell_set.end());
    std::vector<std::vector<Incidence>> inc(width + 1);
    for (int id = 0; id < static_cast<int>(cells.size()); ++id) {
        const auto& c = cells[id];
        for (std::size_t i = 0; i < c.size(); ++i) {
            int a = -1, b = -1;
            for (std::size_t j = 0; j < c.size(); ++j) {
                if (j == i) continue;
                (a < 0 ? a : b) = c[j];
            }
            inc[c[i]].push_back({a, b, id});
        }
    }

    // Allowed colors (0-based) from the frame.
    std::vector<std::vector<char>> allowed(width + 1, std::vector<char>(k, 1));
    if (o.frame_q > 0 || o.frame6_q > 0) {
        if (!o.palindromic || k != 6) {
            std::cerr << "frames need --palindromic and 6 colors\n";
            return 2;
        }
        const int big_n = n + 1, d = o.frame_d;
        const bool full = o.frame_q > 0;
        const int q = full ? o.frame_q : o.frame6_q;
        for (int p = 1; p <= width; ++p) {
            int must = -1;
            if (full) {
                for (int j = 1; j <= 4; ++j)
                    if (p < j) allowed[p][j - 1] = 0;
                if (p < d || (q - d < p && p < q)) allowed[p][4] = 0;
                if (p == d || p == big_n - 2 * q) must = 4;
            }
            if (p < q) allowed[p][5] = 0;
            if (p == q || (o.middle && p > big_n - 2 * q)) must = 5;
            if (must >= 0)
                for (int j = 0; j < k; ++j) allowed[p][j] = (j == must) && allowed[p][j];
        }
    }
    std::vector<std::vector<int>> choices(width + 1);
    for (int p = 1; p <= width; ++p) {
        for (int j = 0; j < k; ++j)
            if (allowed[p][j]) choices[p].push_back(j);
        if (choices[p].empty()) {
            std::cerr << "frame leaves no color at position " << p << "\n";
            return 1;
        }
    }

    std::mt19937_64 rng(o.seed);
    std::vector<int> col(width + 1, 0);
    for (int p = 1; p <= width; ++p) col[p] = choices[p][rng() % choices[p].size()];
    if (!o.start.empty()) {
        std::ifstream in(o.start);
        if (!in) {
            std::cerr << "cannot open " << o.start << "\n";
            return 2;
        }
        std::string line;
        int row = 0;
        while (std::getline(in, line)) {
            auto h = line.find('#');
            if (h != std::string::npos) line.erase(h);
            std::istringstream ss(line);
            int x;
            bool any = false;
            while (ss >> x) {
                any = true;
                if (x >= 1 && x <= width && row < k && allowed[x][row]) col[x] = row;
            }
            if (any) ++row;
        }
    }

    // raw[p][j]: cells through p whose other members all have color j;
    // wsum[p][j]: the same, weighted.  weight[c] = 1 without --breakout.
    std::vector<long> weight(cells.size(), 1);
    std::vector<std::vector<long>> raw(width + 1, std::vector<long>(k, 0));
    std::vector<std::vector<long>> wsum(width + 1, std::vector<long>(k, 0));
    long violated = 0;
    auto rebuild = [&]() {
        for (int p = 1; p <= width; ++p) {
            std::fill(raw[p].begin(), raw[p].end(), 0);
            std::fill(wsum[p].begin(), wsum[p].end(), 0);
            for (const auto& e : inc[p]) {
                if (e.b < 0 || col[e.a] == col[e.b]) {
                    ++raw[p][col[e.a]];
                    wsum[p][col[e.a]] += weight[e.cell];
                }
            }
        }
        violated = 0;
        for (const auto& c : cells) {
            bool same = true;
            for (int q : c) same = same && col[q] == col[c[0]];
            violated += same;
        }
    };
    rebuild();
    auto apply = [&](int p, int to) {
        const int from = col[p];
        for (const auto& e : inc[p]) {
            const long w = weight[e.cell];
            if (e.b < 0) {
                --raw[e.a][from];
                ++raw[e.a][to];
                wsum[e.a][from] -= w;
                wsum[e.a][to] += w;
            } else {
                if (col[e.b] == from) { --raw[e.a][from]; wsum[e.a][from] -= w; }
                if (col[e.b] == to) { ++raw[e.a][to]; wsum[e.a][to] += w; }
                if (col[e.a] == from) { --raw[e.b][from]; wsum[e.b][from] -= w; }
                if (col[e.a] == to) { ++raw[e.b][to]; wsum[e.b][to] += w; }
            }
        }
        violated += raw[p][to] - raw[p][from];
        col[p] = to;
    };
    long bumps = 0;
    auto bump = [&]() {
        for (std::size_t id = 0; id < cells.size(); ++id) {
            const auto& c = cells[id];
            bool same = true;
            for (int q : c) same = same && col[q] == col[c[0]];
            if (!same) continue;
            ++weight[id];
            for (int q : c) ++wsum[q][col[q]];
        }
        if (++bumps % o.smooth == 0) {
            for (auto& w : weight) w = (w + 1) / 2;
            rebuild();
        }
    };

    long best = violated;
    std::vector<int> best_col = col;
    std::vector<std::vector<long>> tabu(width + 1, std::vector<long>(k, 0));
    const auto t0 = std::chrono::steady_clock::now();
    long it = 0, last_improve = 0, perturbations = 0;
    std::cerr << "cells=" << cells.size() << " start_violations=" << violated << "\n";
    const auto& score = o.breakout ? wsum : raw;
    while (violated > 0) {
        ++it;
        if ((it & 1023) == 0) {
            const double el = std::chrono::duration<double>(
                std::chrono::steady_clock::now() - t0).count();
            if (el > o.seconds) break;
        }
        long best_delta = 1L << 60;
        int bp = -1, bj = -1, ties = 0;
        for (int p = 1; p <= width; ++p) {
            const int cur = col[p];
            if (raw[p][cur] == 0) continue;  // only positions in a violated cell
            for (int j : choices[p]) {
                if (j == cur) continue;
                const long delta = score[p][j] - score[p][cur];
                const bool aspiration = violated + raw[p][j] - raw[p][cur] < best;
                if (tabu[p][j] > it && !aspiration) continue;
                if (delta < best_delta) {
                    best_delta = delta;
                    bp = p;
                    bj = j;
                    ties = 1;
                } else if (delta == best_delta && rng() % (++ties) == 0) {
                    bp = p;
                    bj = j;
                }
            }
        }
        if (o.breakout && best_delta >= 0) {
            bump();
            continue;
        }
        if (bp < 0) continue;
        const int old = col[bp];
        apply(bp, bj);
        tabu[bp][old] = it + 7 + static_cast<long>(rng() % 10) + violated * 6 / 10;
        if (violated < best) {
            best = violated;
            best_col = col;
            last_improve = it;
            std::cerr << "it=" << it << " best=" << best << "\n";
        } else if (!o.breakout && it - last_improve > o.stagnation) {
            // Restart from the best coloring with a random perturbation.
            col = best_col;
            for (int m = 0; m < o.perturb; ++m) {
                const int p = 1 + static_cast<int>(rng() % width);
                col[p] = choices[p][rng() % choices[p].size()];
            }
            rebuild();
            for (auto& t : tabu) std::fill(t.begin(), t.end(), 0);
            last_improve = it;
            ++perturbations;
        }
    }
    const double el = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - t0).count();
    col = best_col;
    rebuild();
    std::cerr << "done iterations=" << it << " seconds=" << el << " best=" << best
              << " recomputed=" << violated << " perturbations=" << perturbations
              << " bumps=" << bumps << "\n";
    // Expand to [1, n] and renumber colors by least element.
    std::vector<std::vector<int>> rows(k);
    for (int x = 1; x <= n; ++x) rows[col[fold(x)]].push_back(x);
    std::sort(rows.begin(), rows.end(), [](const auto& a, const auto& b) {
        if (a.empty() || b.empty()) return b.empty() && !a.empty();
        return a[0] < b[0];
    });
    std::ostringstream out;
    for (const auto& r : rows) {
        for (std::size_t i = 0; i < r.size(); ++i) out << (i ? " " : "") << r[i];
        out << "\n";
    }
    if (!o.output.empty()) {
        std::ofstream f(o.output);
        f << out.str();
    } else {
        std::cout << out.str();
    }
    std::cerr << "best_violated_cells=" << violated << "\n";
    return violated == 0 ? 0 : 1;
}
