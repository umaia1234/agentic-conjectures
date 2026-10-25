// Second, independent checker for Schur partitions (C++17, standard library only).
//
// Input: a text file with one line per color class listing its integers
// ('#' starts a comment), as in published_536.col.  The program checks that
// the classes partition [1, maximum] exactly, and that no class contains
// x, y, x + y (x = y allowed).  Unlike verify.py, which iterates over the
// members of each class, this checker builds a label array and scans every
// pair 1 <= x <= y with x + y <= maximum.  It also reports two structural
// properties used in the README: palindromic (c(x) = c(maximum + 1 - x)) and
// sum-free modulo maximum + 1.  Exit status 0 iff the partition is valid.
//
// Usage: check_partition FILE MAXIMUM [COLORS=6]
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

int main(int argc, char** argv) {
    if (argc < 3 || argc > 4) {
        std::cerr << "usage: " << argv[0] << " FILE MAXIMUM [COLORS=6]\n";
        return 2;
    }
    const long n = std::atol(argv[2]);
    const long k = argc == 4 ? std::atol(argv[3]) : 6;
    if (n < 1 || k < 1) {
        std::cerr << "MAXIMUM and COLORS must be positive\n";
        return 2;
    }
    std::ifstream in(argv[1]);
    if (!in) {
        std::cerr << "cannot open " << argv[1] << "\n";
        return 2;
    }
    std::vector<long> label(n + 1, -1);
    std::vector<long> sizes;
    long problems = 0;
    std::string line;
    while (std::getline(in, line)) {
        const auto hash = line.find('#');
        if (hash != std::string::npos) line.erase(hash);
        std::istringstream tokens(line);
        std::vector<long> row;
        long v;
        while (tokens >> v) row.push_back(v);
        if (!tokens.eof()) {
            std::cerr << "non-integer token in input\n";
            return 2;
        }
        if (row.empty()) continue;
        const long color = static_cast<long>(sizes.size());
        sizes.push_back(static_cast<long>(row.size()));
        for (long x : row) {
            if (x < 1 || x > n) {
                std::cout << "out of range: " << x << "\n";
                ++problems;
            } else if (label[x] != -1) {
                std::cout << "duplicate: " << x << "\n";
                ++problems;
            } else {
                label[x] = color;
            }
        }
    }
    if (static_cast<long>(sizes.size()) != k) {
        std::cout << "expected " << k << " classes, found " << sizes.size() << "\n";
        ++problems;
    }
    for (long x = 1; x <= n; ++x) {
        if (label[x] == -1) {
            std::cout << "missing: " << x << "\n";
            ++problems;
        }
    }
    long triples = 0, checked = 0;
    for (long x = 1; 2 * x <= n; ++x) {
        for (long y = x; x + y <= n; ++y) {
            ++checked;
            if (label[x] != -1 && label[x] == label[y] && label[y] == label[x + y]) {
                if (triples < 20) {
                    std::cout << "monochromatic: color " << label[x] + 1 << ": " << x
                              << " + " << y << " = " << x + y << "\n";
                }
                ++triples;
            }
        }
    }
    bool palindromic = true;
    for (long x = 1; x <= n; ++x) palindromic = palindromic && label[x] == label[n + 1 - x];
    // Sum-free modulo n + 1: x + y = z + (n + 1) with x, y, z in [1, n].
    long modular = 0;
    for (long x = 1; x <= n; ++x) {
        for (long y = x; y <= n; ++y) {
            const long z = x + y - (n + 1);
            if (z >= 1 && label[x] != -1 && label[x] == label[y] && label[y] == label[z]) {
                ++modular;
            }
        }
    }
    const bool valid = problems == 0 && triples == 0;
    std::cout << "maximum=" << n << " colors=" << sizes.size() << " sizes=";
    for (std::size_t i = 0; i < sizes.size(); ++i) std::cout << (i ? "," : "") << sizes[i];
    std::cout << "\npairs_checked=" << checked << " monochromatic_triples=" << triples
              << " structural_problems=" << problems << "\n";
    std::cout << "palindromic=" << (palindromic ? "yes" : "no")
              << " modular_triples_mod_" << n + 1 << "=" << modular << "\n";
    std::cout << "valid=" << (valid ? "true" : "false") << "\n";
    return valid ? 0 : 1;
}
