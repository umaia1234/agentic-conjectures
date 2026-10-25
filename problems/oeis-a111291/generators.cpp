// generators.cpp -- list the p-generators d <= D (integers with 2 tau(d) | d) with their prime
// factorisations, one per line: "d q1 e1 q2 e2 ...". verify_tail.py re-checks every line.
//
// Usage: generators D
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <vector>

int main(int argc, char** argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: %s D\n", argv[0]);
        return 2;
    }
    const uint64_t D = strtoull(argv[1], nullptr, 10);
    if (D < 4 || D > 2000000000ULL) {
        fprintf(stderr, "D out of range\n");
        return 2;
    }
    // smallest prime factor of every k <= D/2 (every odd part of a multiple of 4 is <= D/4)
    const uint64_t M = D / 2;
    std::vector<uint32_t> spf(M + 1, 0);
    for (uint64_t i = 2; i <= M; i++)
        if (!spf[i])
            for (uint64_t j = i; j <= M; j += i)
                if (!spf[j]) spf[j] = (uint32_t)i;
    uint64_t count = 0;
    std::vector<uint64_t> q, e;
    for (uint64_t d = 4; d <= D; d += 4) {  // 2 tau(d) | d forces 4 | d
        q.clear();
        e.clear();
        uint64_t m = d, t = 1;
        int a = 0;
        while (m % 2 == 0) { m /= 2; a++; }
        q.push_back(2);
        e.push_back((uint64_t)a);
        t *= (uint64_t)(a + 1);
        while (m > 1) {
            const uint64_t p = spf[m];
            uint64_t k = 0;
            while (m % p == 0) { m /= p; k++; }
            q.push_back(p);
            e.push_back(k);
            t *= k + 1;
        }
        if (d % (2 * t) != 0) continue;
        count++;
        printf("%" PRIu64, d);
        for (size_t i = 0; i < q.size(); i++) printf(" %" PRIu64 " %" PRIu64, q[i], e[i]);
        printf("\n");
    }
    fprintf(stderr, "generators <= %" PRIu64 ": %" PRIu64 "\n", D, count);
    return 0;
}
