// Erdős problem #424 -- implementation B: generation-by-generation fixed point.
//
// This program follows the upstream definition literally:
//   A_0 = {2, 3},   A_{k+1} = A_k ∪ { x*y - 1 : x, y ∈ A_k, x != y },
// truncated to [0, N].  Because x*y - 1 > max(x, y) for distinct x, y >= 2,
// the truncated iteration equals A_k ∩ [0, N] at every generation, and its
// stable value is S ∩ [0, N].  It uses semi-naive evaluation: generation k+1
// only multiplies pairs with at least one member first seen in generation k
// (the set D_k), against the frozen set A_k.  New products go to a separate
// bitset, so a generation never sees its own output (Jacobi order).  It is
// independent of the ascending sieve erdos424_ascending.cpp: different order
// of generation, different loop nest, separately written statistics; only the
// output format and the 64-bit word hash are shared by design.
//
// Memory: two interleaved bit planes, 2 bits per integer.  Word 2w holds
// "in A_k" for 64w..64w+63; word 2w+1 holds "in D_k" for members of A_k and
// "new in generation k+1" for non-members.  A product only ever sets the
// second plane where the first is clear, so A_k and D_k stay frozen while
// generation k is being formed.
//
// Usage: erdos424_generations N
// Output: the same records as erdos424_ascending, plus "generation k size"
// lines giving |A_k \ A_{k-1}| (k >= 0) within [0, N].

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

typedef unsigned long long ull;

static ull mix64(ull z) {
    z += 0x9e3779b97f4a7c15ULL;
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static inline bool get_bit(const std::vector<ull> &v, ull n) { return (v[n / 64] >> (n % 64)) & 1ULL; }

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
    const ull W = N / 64 + 1;
    std::vector<ull> st(2 * W, 0);  // st[2w]: A_k plane, st[2w+1]: D_k / new plane
    st[0] = st[1] = (1ULL << 2) | (1ULL << 3);
    std::vector<ull> generation_sizes{2};

    for (;;) {
        // Every y in D_k with 2y - 1 <= N, i.e. y <= (N + 1) / 2.
        const ull y_max = (N + 1) / 2;
        for (ull wy = 0; wy <= y_max / 64; ++wy) {
            ull dy = st[2 * wy] & st[2 * wy + 1];
            while (dy) {
                const ull y = wy * 64 + (ull)__builtin_ctzll(dy);
                dy &= dy - 1;
                if (y > y_max) break;
                const ull x_max = (N + 1) / y;  // x * y - 1 <= N
                for (ull wx = 0; wx <= x_max / 64; ++wx) {
                    ull cx = st[2 * wx];
                    while (cx) {
                        const ull x = wx * 64 + (ull)__builtin_ctzll(cx);
                        cx &= cx - 1;
                        if (x > x_max) break;
                        if (x == y) continue;
                        const ull n = x * y - 1;
                        st[2 * (n / 64) + 1] |= (1ULL << (n % 64)) & ~st[2 * (n / 64)];
                    }
                }
            }
        }
        ull added = 0;
        for (ull w = 0; w < W; ++w) {
            const ull fresh = st[2 * w + 1] & ~st[2 * w];
            st[2 * w] |= fresh;
            st[2 * w + 1] = fresh;
            added += (ull)__builtin_popcountll(fresh);
        }
        if (added == 0) break;
        generation_sizes.push_back(added);
    }
    // Keep only the membership plane, compacted in place (index w <= 2w).
    for (ull w = 0; w < W; ++w) st[w] = st[2 * w];
    st.resize(W);
    const std::vector<ull> &cur = st;

    // Statistics, computed directly from the final set.
    ull total = 0;
    for (ull n = 0; n <= N; ++n) total += get_bit(cur, n) ? 1 : 0;
    ull hash = 0x424;
    for (ull w = 0; w < W; ++w) hash = mix64(hash ^ cur[w]);

    std::vector<ull> marks;
    for (ull p = 10;; p *= 10) {
        if (p <= N) marks.push_back(p);
        if (2 * p <= N) marks.push_back(2 * p);
        if (5 * p <= N) marks.push_back(5 * p);
        if (p > N / 10) break;
    }
    if (marks.back() != N) marks.push_back(N);

    std::printf("impl generation-fixed-point\n");
    std::printf("limit %llu\n", N);
    std::printf("count %llu\n", total);
    std::printf("hash %016llx\n", hash);
    // Prefix counts: whole words below the checkpoint, then single bits.
    for (ull M : marks) {
        ull c = 0, w = 0;
        for (; (w + 1) * 64 <= M + 1; ++w) c += (ull)__builtin_popcountll(cur[w]);
        for (ull n = w * 64; n <= M; ++n) c += get_bit(cur, n) ? 1 : 0;
        std::printf("checkpoint %llu %llu\n", M, c);
    }
    // Per-class prefix counts modulo 6 with precomputed masks: a word starting
    // at 64w has offset s = 64w mod 6 in {0, 4, 2}.
    ull mask6[6][6] = {};
    for (int s0 = 0; s0 < 6; ++s0)
        for (int b = 0; b < 64; ++b) mask6[s0][(s0 + b) % 6] |= 1ULL << b;
    for (ull M : marks) {
        ull c6[6] = {0, 0, 0, 0, 0, 0};
        ull w = 0;
        for (; (w + 1) * 64 <= M + 1; ++w) {
            const int s0 = (int)((w * 64) % 6);
            for (int c = 0; c < 6; ++c) c6[c] += (ull)__builtin_popcountll(cur[w] & mask6[s0][c]);
        }
        for (ull n = w * 64; n <= M; ++n)
            if (get_bit(cur, n)) ++c6[n % 6];
        std::printf("checkpoint_mod6 %llu %llu %llu %llu %llu %llu %llu\n", M, c6[0], c6[1],
                    c6[2], c6[3], c6[4], c6[5]);
    }
    // Residue counts: tally n mod 2^5*3^3*5*7*11 = 332640 once, then fold.
    const ull L = 332640;
    std::vector<ull> by_class(L, 0);
    for (ull w = 0; w < W; ++w) {
        ull bitsw = cur[w];
        while (bitsw) {
            const ull n = w * 64 + (ull)__builtin_ctzll(bitsw);
            bitsw &= bitsw - 1;
            ++by_class[n % L];
        }
    }
    const int moduli[] = {2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 14, 15,
                          16, 18, 20, 21, 22, 24, 27, 28, 30, 32, 33, 35, 36};
    for (int m : moduli) {
        std::vector<ull> c(m, 0);
        for (ull s = 0; s < L; ++s) c[s % m] += by_class[s];
        std::string line = "residues " + std::to_string(m);
        for (int r = 0; r < m; ++r) line += " " + std::to_string(c[r]);
        std::printf("%s\n", line.c_str());
    }
    std::string gaps = "first_nonmembers_not_1_mod_3";
    int listed = 0;
    for (ull n = 2; n <= N && listed < 100; ++n) {
        if (n % 3 == 1 || get_bit(cur, n)) continue;
        gaps += " " + std::to_string(n);
        ++listed;
    }
    std::printf("%s\n", gaps.c_str());
    for (std::size_t k = 0; k < generation_sizes.size(); ++k) {
        std::printf("generation %zu %llu\n", k, generation_sizes[k]);
    }
    return 0;
}
