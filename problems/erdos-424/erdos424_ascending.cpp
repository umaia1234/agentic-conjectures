// Erdős problem #424 -- implementation A: ascending push sieve.
//
// S is the least set of naturals containing 2 and 3 and closed under
// (x, y) |-> x*y - 1 for distinct members x != y.  Every product of two
// distinct members exceeds both factors, so membership of n is decided by
// strictly smaller members.  This program scans y = 2, 3, 4, ... in
// increasing order; when y is reached its bit is final, and it pushes
// x*y - 1 for every smaller member x with x*y - 1 <= N.  Each unordered pair
// {x, y} (x < y) is therefore pushed exactly once, after both bits are final.
//
// Usage: erdos424_ascending N
// Output: one "key value..." record per line (see print_report); the
// independent implementation erdos424_generations.cpp prints the same
// records, and verify_counts.py compares them.

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

namespace {

using u64 = std::uint64_t;

// Residues are tallied modulo L = 2^5 * 3^3 * 5 * 7 * 11; every modulus
// reported below divides L.
constexpr u64 kResidueBase = 332640;
constexpr int kModuli[] = {2,  3,  4,  5,  6,  7,  8,  9,  10, 11, 12, 14, 15,
                           16, 18, 20, 21, 22, 24, 27, 28, 30, 32, 33, 35, 36};

u64 mix64(u64 z) {
    z += 0x9e3779b97f4a7c15ULL;
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

std::vector<u64> checkpoints(u64 limit) {
    std::vector<u64> result;
    for (u64 p = 10; p <= limit; p *= 10) {
        for (u64 c : {1ULL, 2ULL, 5ULL}) {
            if (c * p <= limit) result.push_back(c * p);
        }
        if (p > limit / 10) break;
    }
    if (result.empty() || result.back() != limit) result.push_back(limit);
    return result;
}

}  // namespace

int main(int argc, char **argv) {
    if (argc != 2) {
        std::fprintf(stderr, "usage: %s N   (N >= 10)\n", argv[0]);
        return 2;
    }
    const u64 limit = std::strtoull(argv[1], nullptr, 10);
    if (limit < 10 || limit > (1ULL << 40)) {
        std::fprintf(stderr, "require 10 <= N <= 2^40\n");
        return 2;
    }

    // Bit n of the bitset (word n / 64, bit n % 64) records n in S.
    const u64 words = limit / 64 + 1;
    std::vector<u64> bits(words, 0);
    bits[0] |= (1ULL << 2) | (1ULL << 3);

    // Members x that can still be the smaller factor of a product <= N + 1.
    std::vector<u64> small;
    const u64 product_cap = limit + 1;  // need x * y <= N + 1
    const u64 last_y = product_cap / 2;  // y > (N + 1) / 2 never pushes

    for (u64 w = 0; w <= last_y / 64; ++w) {
        u64 done = 0;
        for (;;) {
            // Re-read: pushes from this word may land in it (2y - 1 > y).
            const u64 pending = bits[w] & ~done;
            if (pending == 0) break;
            const int b = __builtin_ctzll(pending);
            done |= 1ULL << b;
            const u64 y = w * 64 + static_cast<u64>(b);
            if (y > last_y) break;
            const u64 x_cap = product_cap / y;  // x * y <= N + 1
            for (u64 x : small) {
                if (x > x_cap) break;  // small is increasing and all x < y
                const u64 n = x * y - 1;
                bits[n >> 6] |= 1ULL << (n & 63);
            }
            if (y <= product_cap / (y + 1)) small.push_back(y);
        }
    }
    // Clear any bits beyond N in the last word (none are ever set, but be
    // explicit so that the hash covers exactly bits 0..N).
    const unsigned tail = static_cast<unsigned>(limit % 64);
    if (tail != 63) bits[words - 1] &= (2ULL << tail) - 1;

    // Statistics.  Set bits are visited in increasing order; a checkpoint M
    // is closed when the first member above M is met (or at the end), so its
    // tallies count exactly the members n <= M.
    const std::vector<u64> marks = checkpoints(limit);
    std::vector<u64> mark_counts(marks.size(), 0);
    std::vector<std::vector<u64>> mark_mod6(marks.size(), std::vector<u64>(6, 0));
    std::vector<u64> residue(kResidueBase, 0);
    u64 count = 0, hash = 0x424, run6[6] = {0, 0, 0, 0, 0, 0};
    std::size_t next_mark = 0;
    auto close_marks_below = [&](u64 n) {
        while (next_mark < marks.size() && marks[next_mark] < n) {
            mark_counts[next_mark] = count;
            for (int c = 0; c < 6; ++c) mark_mod6[next_mark][c] = run6[c];
            ++next_mark;
        }
    };
    u64 base_mod = 0;  // (64 * w) mod L
    for (u64 w = 0; w < words; ++w) {
        u64 word = bits[w];
        hash = mix64(hash ^ word);
        while (word) {
            const int b = __builtin_ctzll(word);
            word &= word - 1;
            close_marks_below(w * 64 + static_cast<u64>(b));
            u64 r = base_mod + static_cast<u64>(b);
            if (r >= kResidueBase) r -= kResidueBase;
            ++residue[r];
            ++run6[r % 6];  // 6 divides L
            ++count;
        }
        base_mod += 64;
        if (base_mod >= kResidueBase) base_mod -= kResidueBase;
    }
    close_marks_below(limit + 1);

    std::printf("impl ascending-push\n");
    std::printf("limit %llu\n", static_cast<unsigned long long>(limit));
    std::printf("count %llu\n", static_cast<unsigned long long>(count));
    std::printf("hash %016llx\n", static_cast<unsigned long long>(hash));
    for (std::size_t i = 0; i < marks.size(); ++i) {
        std::printf("checkpoint %llu %llu\n", static_cast<unsigned long long>(marks[i]),
                    static_cast<unsigned long long>(mark_counts[i]));
    }
    for (std::size_t i = 0; i < marks.size(); ++i) {
        std::printf("checkpoint_mod6 %llu", static_cast<unsigned long long>(marks[i]));
        for (int c = 0; c < 6; ++c) {
            std::printf(" %llu", static_cast<unsigned long long>(mark_mod6[i][c]));
        }
        std::printf("\n");
    }
    for (int m : kModuli) {
        std::string line = "residues " + std::to_string(m);
        for (int r = 0; r < m; ++r) {
            u64 c = 0;
            for (u64 s = static_cast<u64>(r); s < kResidueBase; s += static_cast<u64>(m)) {
                c += residue[s];
            }
            line += " " + std::to_string(c);
        }
        std::printf("%s\n", line.c_str());
    }
    // First non-members outside the excluded class 1 mod 3.
    std::string gaps = "first_nonmembers_not_1_mod_3";
    int listed = 0;
    for (u64 n = 2; n <= limit && listed < 100; ++n) {
        if (n % 3 != 1 && !((bits[n >> 6] >> (n & 63)) & 1ULL)) {
            gaps += " " + std::to_string(n);
            ++listed;
        }
    }
    std::printf("%s\n", gaps.c_str());
    return 0;
}
