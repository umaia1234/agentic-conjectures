// Erdős problem #424 -- the arithmetic (residue) part of the complement.
//
// Call n "factorable" if n + 1 = x * y with 2 <= x < y and x % 3 != 1,
// y % 3 != 1.  Every member of S other than 2 and 3 is factorable, because
// its two distinct factors are members and members are never 1 mod 3 (Lean:
// AgenticConjectures.Erdos424.mod_three_ne_one).  So an admissible n >= 4
// (n % 3 != 1) that is not factorable is excluded from S for purely
// arithmetic reasons.  This program does not compute S at all: it marks
// the factorable n <= N with a plain double loop and prints their counts by
// class mod 6 at the same checkpoints as the two sieves.
//
// Usage: erdos424_factorable N

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

typedef unsigned long long ull;

int main(int argc, char **argv) {
    if (argc != 2) {
        std::fprintf(stderr, "usage: %s N   (N >= 10)\n", argv[0]);
        return 2;
    }
    const ull N = std::strtoull(argv[1], nullptr, 10);
    if (N < 10 || N > (1ULL << 40)) {
        std::fprintf(stderr, "require 10 <= N <= 2^40\n");
        return 2;
    }
    std::vector<ull> F(N / 64 + 1, 0);
    for (ull x = 2; x * (x + 1) <= N + 1; ++x) {
        if (x % 3 == 1) continue;
        for (ull r = 0; r < 3; r += 2) {  // cofactors y > x with y % 3 == r, r in {0, 2}
            ull y = x + 1;
            while (y % 3 != r) ++y;
            for (; x * y <= N + 1; y += 3) {
                const ull n = x * y - 1;
                F[n / 64] |= 1ULL << (n % 64);
            }
        }
    }

    std::vector<ull> marks;
    for (ull p = 10;; p *= 10) {
        if (p <= N) marks.push_back(p);
        if (2 * p <= N) marks.push_back(2 * p);
        if (5 * p <= N) marks.push_back(5 * p);
        if (p > N / 10) break;
    }
    if (marks.back() != N) marks.push_back(N);

    std::printf("impl factorable\n");
    std::printf("limit %llu\n", N);
    // Prefix counts by class mod 6: whole words through masks (a word starting
    // at 64w has offset 64w mod 6), then the tail of the checkpoint's word.
    ull mask6[6][6] = {};
    for (int s0 = 0; s0 < 6; ++s0)
        for (int b = 0; b < 64; ++b) mask6[s0][(s0 + b) % 6] |= 1ULL << b;
    ull c6[6] = {0, 0, 0, 0, 0, 0};
    ull w = 0;  // words [0, w) are already counted
    for (ull M : marks) {
        for (; (w + 1) * 64 <= M + 1; ++w) {
            const int s0 = (int)((w * 64) % 6);
            for (int c = 0; c < 6; ++c) c6[c] += (ull)__builtin_popcountll(F[w] & mask6[s0][c]);
        }
        ull t6[6] = {c6[0], c6[1], c6[2], c6[3], c6[4], c6[5]};
        for (ull n = w * 64; n <= M; ++n)
            if ((F[n / 64] >> (n % 64)) & 1ULL) ++t6[n % 6];
        std::printf("factorable_mod6 %llu %llu %llu %llu %llu %llu %llu\n", M, t6[0], t6[1], t6[2],
                    t6[3], t6[4], t6[5]);
    }
    return 0;
}
