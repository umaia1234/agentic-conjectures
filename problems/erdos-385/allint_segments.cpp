// Exact classification of F(n) = max{m + p(m) : m < n composite} for Erdos #385.
//
// Method A (all-integer lineage of ep430_experiment.cpp), multithreaded:
//   * Every integer m, of either parity, receives its least prime factor from a
//     segmented sieve that writes the sieving primes in DECREASING order with an
//     unconditional overwrite.  The last write, made by the smallest prime
//     dividing m, therefore wins.  Primes and 0, 1 keep the value 0.
//   * F(n) is evaluated straight from the definition with no parity reduction:
//     F(n) = 1 + R(n), R(n) = max over composite m < n of (m + p(m) - 1).
//   * Output segments are processed independently and in parallel.  A segment
//     of indices [lo, hi] starts its scan at W = max(2, lo - isqrt(hi) - 2).
//     Every composite m < W has m + p(m) - 1 <= W - 1 + isqrt(hi) - 1 = lo - 4,
//     while the even composite among n - 2, n - 1 (both >= W) already gives
//     R(n) >= n - 1 for n >= lo >= 6.  Hence omitted m never change F(n).
//
// Usage: allint_segments N_LO N_HI SEG THREADS
// Index segments are the grid cells (k*SEG, (k+1)*SEG] intersected with
// [N_LO, N_HI]; N_LO >= 6.  Each segment prints one JSON line with the exact
// equality cases F(n) = n, the slack statistics of F(n) - n, and an
// order-independent fingerprint of the whole sequence (n, F(n) - n).
// Diagnostics and timing go to stderr, so stdout is deterministic.

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <thread>
#include <vector>

namespace {

using u32 = std::uint32_t;
using u64 = std::uint64_t;

const u64 kThresholds[] = {0,    1,    2,     3,     5,     10,    20,     50,     100,
                           200,  500,  1000,  2000,  5000,  10000, 20000,  50000,  100000};
constexpr int kNumThresholds = sizeof(kThresholds) / sizeof(kThresholds[0]);
constexpr u32 kBlock = 1u << 19;  // integers per sieve block

u64 isqrt(u64 x) {
    u64 r = static_cast<u64>(std::sqrt(static_cast<long double>(x)));
    while (r * r > x) --r;
    while ((r + 1) * (r + 1) <= x) ++r;
    return r;
}

u64 mix64(u64 z) {
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

struct Segment {
    u64 k = 0, lo = 0, hi = 0;
    u64 count = 0, sum_slack = 0, hash = 0;
    u64 min_slack = ~0ULL, min_slack_n = 0;
    std::vector<u64> equalities;
    u64 last_at_most[kNumThresholds] = {};
};

// Number of thresholds strictly below s, kept incrementally: consecutive
// slacks usually differ by -1, so this rarely moves.
inline int threshold_class(int j, u64 s) {
    while (j < kNumThresholds && kThresholds[j] < s) ++j;
    while (j > 0 && kThresholds[j - 1] >= s) --j;
    return j;
}

[[noreturn]] void die(const char* msg, u64 value) {
    std::fprintf(stderr, "allint_segments: %s (%" PRIu64 ")\n", msg, value);
    std::exit(2);
}

void process_segment(Segment& seg, const std::vector<u32>& primes, std::vector<u32>& lpf) {
    const u64 lo = seg.lo, hi = seg.hi;
    const u64 root = isqrt(hi);
    const u64 start = lo > root + 4 ? lo - root - 2 : 2;
    const u64 m_end = hi;  // scan composites m < hi, i.e. m <= hi - 1
    u64 R = 0;             // max of m + p(m) - 1 over composite m in [start, current)
    // Hot-loop accumulators live in locals; last_n_in_class[j] is the last n
    // whose slack has threshold class j (class kNumThresholds: above all).
    u64 count = 0, sum_slack = 0, hash = 0, min_slack = ~0ULL, min_slack_n = 0;
    u64 last_n_in_class[kNumThresholds + 1] = {};
    int cls = 0;
    u64 cls_lo = ~0ULL, cls_hi = 0;  // cached class interval (cls_lo, cls_hi]
    for (u64 L = start; L < m_end; L += kBlock) {
        const u32 len = static_cast<u32>(std::min<u64>(kBlock, m_end - L));
        const u64 last = L + len - 1;
        std::fill(lpf.begin(), lpf.begin() + len, 0u);
        const std::size_t np = static_cast<std::size_t>(
            std::partition_point(primes.begin(), primes.end(),
                                 [last](u32 q) { return u64(q) * q <= last; }) -
            primes.begin());
        for (std::size_t j = np; j-- > 0;) {
            const u64 p = primes[j];
            u64 first = p * p;
            if (first < L) first = ((L + p - 1) / p) * p;
            u32* a = lpf.data();
            for (u64 i = first - L; i < len; i += p) a[i] = static_cast<u32>(p);
        }
        const u32* a = lpf.data();
        // Warm-up part of the block: indices n = m + 1 < lo are not recorded.
        const u32 rec_from = L + 1 >= lo ? 0 : static_cast<u32>(std::min<u64>(len, lo - 1 - L));
        for (u32 i = 0; i < rec_from; ++i) {
            if (a[i] != 0) {
                const u64 e = L + i + a[i] - 1;
                if (e > R) R = e;
            }
        }
        for (u32 i = rec_from; i < len; ++i) {
            const u64 m = L + i;
            if (a[i] != 0) {
                const u64 e = m + a[i] - 1;
                if (e > R) R = e;
            }
            const u64 n = m + 1;
            // Lean: F(n) >= n for n >= 5, so R(n) + 1 >= n must hold here.
            if (R + 1 < n) die("baseline F(n) >= n violated at n", n);
            const u64 s = R + 1 - n;  // F(n) - n
            ++count;
            sum_slack += s;
            hash += mix64((n << 20) + s);
            if (s < min_slack) {
                min_slack = s;
                min_slack_n = n;
            }
            if (s <= cls_lo || s > cls_hi) {
                cls = threshold_class(cls, s);
                cls_lo = cls > 0 ? kThresholds[cls - 1] : 0;
                cls_hi = cls < kNumThresholds ? kThresholds[cls] : ~0ULL;
                if (cls == 0) cls_lo = ~0ULL;  // class 0 is s == 0: always recheck
            }
            last_n_in_class[cls] = n;
            if (s == 0) seg.equalities.push_back(n);
        }
    }
    seg.count = count;
    seg.sum_slack = sum_slack;
    seg.hash = hash;
    seg.min_slack = min_slack;
    seg.min_slack_n = min_slack_n;
    u64 running = 0;
    for (int t = 0; t < kNumThresholds; ++t) {
        running = std::max(running, last_n_in_class[t]);
        seg.last_at_most[t] = running;
    }
    if (seg.count != hi - lo + 1) die("segment count mismatch at k", seg.k);
}

void print_segment(const Segment& s) {
    std::string out = "{\"k\":" + std::to_string(s.k) + ",\"lo\":" + std::to_string(s.lo) +
                      ",\"hi\":" + std::to_string(s.hi) + ",\"count\":" + std::to_string(s.count) +
                      ",\"equalities\":[";
    for (std::size_t i = 0; i < s.equalities.size(); ++i)
        out += (i ? "," : "") + std::to_string(s.equalities[i]);
    char hash[32];
    std::snprintf(hash, sizeof hash, "%016" PRIx64, s.hash);
    out += "],\"min_slack\":" + std::to_string(s.min_slack) +
           ",\"min_slack_n\":" + std::to_string(s.min_slack_n) +
           ",\"sum_slack\":" + std::to_string(s.sum_slack) + ",\"hash\":\"" + hash +
           "\",\"last_at_most\":[";
    for (int t = 0; t < kNumThresholds; ++t)
        out += (t ? "," : "") + std::to_string(s.last_at_most[t]);
    out += "]}\n";
    std::fputs(out.c_str(), stdout);
}

}  // namespace

int main(int argc, char** argv) {
    if (argc != 5) {
        std::fprintf(stderr, "usage: %s N_LO N_HI SEG THREADS\n", argv[0]);
        return 1;
    }
    const u64 n_lo = std::strtoull(argv[1], nullptr, 10);
    const u64 n_hi = std::strtoull(argv[2], nullptr, 10);
    const u64 seg_size = std::strtoull(argv[3], nullptr, 10);
    const unsigned threads = static_cast<unsigned>(std::strtoul(argv[4], nullptr, 10));
    if (n_lo < 6 || n_hi < n_lo || n_hi > 1000000000000ULL || seg_size == 0 || threads == 0) {
        std::fprintf(stderr, "require 6 <= N_LO <= N_HI <= 10^12, SEG > 0, THREADS > 0\n");
        return 1;
    }
    const auto t0 = std::chrono::steady_clock::now();
    // F(n) - n <= p(m) - 1 < sqrt(N_HI) <= 10^6 < 2^20 for the maximizing m, so
    // the fingerprint key (n << 20) + (F(n) - n) is injective on the run.
    if (isqrt(n_hi) >= (1ULL << 20)) die("N_HI too large for the fingerprint", n_hi);

    // Primes up to isqrt(N_HI) by a plain sieve of Eratosthenes.
    const u64 root = isqrt(n_hi) + 1;
    std::vector<char> composite(root + 1, 0);
    std::vector<u32> primes;
    for (u64 i = 2; i <= root; ++i) {
        if (composite[i]) continue;
        primes.push_back(static_cast<u32>(i));
        for (u64 j = i * i; j <= root; j += i) composite[j] = 1;
    }

    std::vector<Segment> segs;
    for (u64 k = (n_lo - 1) / seg_size; k * seg_size < n_hi; ++k) {
        Segment s;
        s.k = k;
        s.lo = std::max(n_lo, k * seg_size + 1);
        s.hi = std::min(n_hi, (k + 1) * seg_size);
        segs.push_back(s);
    }

    std::atomic<std::size_t> next{0};
    auto worker = [&]() {
        std::vector<u32> lpf(kBlock);
        for (std::size_t i; (i = next.fetch_add(1)) < segs.size();) {
            process_segment(segs[i], primes, lpf);
            std::fprintf(stderr, "allint_segments: segment %" PRIu64 " done\n", segs[i].k);
        }
    };
    std::vector<std::thread> pool;
    for (unsigned t = 1; t < threads; ++t) pool.emplace_back(worker);
    worker();
    for (auto& th : pool) th.join();

    std::printf("{\"program\":\"allint_segments\",\"n_lo\":%" PRIu64 ",\"n_hi\":%" PRIu64
                ",\"seg\":%" PRIu64 ",\"thresholds\":[",
                n_lo, n_hi, seg_size);
    for (int t = 0; t < kNumThresholds; ++t)
        std::printf("%s%" PRIu64, t ? "," : "", kThresholds[t]);
    std::printf("]}\n");
    for (const Segment& s : segs) print_segment(s);
    const double secs =
        std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::fprintf(stderr, "allint_segments: %zu segments, %u threads, %.2f s\n", segs.size(),
                 threads, secs);
    return 0;
}
