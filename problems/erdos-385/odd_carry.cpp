// Exact classification of F(n) = max{m + p(m) : m < n composite} for Erdos #385.
//
// Method B (odd-only lineage of ep430_segmented.cpp), multithreaded:
//   * Only odd integers are sieved.  Odd primes are applied in INCREASING
//     order and an entry keeps the first prime that reaches it, which is its
//     least prime factor.  Primes keep the value 0.
//   * Parity reduction instead of the all-integer recurrence: for n >= 6,
//       F(n) = max(n + [n odd], 1 + max over odd composite m < n of (m + p(m) - 1)),
//     because every even composite m < n contributes m + 2 <= n + [n odd],
//     with equality at m = n - 2 or m = n - 1.
//   * One exact scan carries the running maximum R through the whole run in
//     increasing order.  For each odd m it records the odd index n = m (R
//     before m is added), adds m to R, then records the even index n = m + 1.
//     Worker threads sieve blocks ahead of the scanner in a ring buffer; the
//     scanner consumes the blocks strictly in order.
//   * A run from N_LO = 6 starts at m = 3 with nothing omitted.  A run with a
//     larger N_LO starts at the odd W <= N_LO - 2*isqrt(N_HI) - 9: any omitted
//     odd composite m < W has m + p(m) <= W - 1 + isqrt(N_HI) < N_LO <= n, so
//     it cannot change the maximum above.
//
// Usage: odd_carry N_LO N_HI SEG THREADS
// Output format is identical to allint_segments: one JSON line per index
// segment (k*SEG, (k+1)*SEG] intersected with [N_LO, N_HI].  Diagnostics and
// timing go to stderr, so stdout is deterministic.

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cinttypes>
#include <cmath>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

namespace {

using u32 = std::uint32_t;
using u64 = std::uint64_t;

const u64 kThresholds[] = {0,    1,    2,     3,     5,     10,    20,     50,     100,
                           200,  500,  1000,  2000,  5000,  10000, 20000,  50000,  100000};
constexpr int kNumThresholds = sizeof(kThresholds) / sizeof(kThresholds[0]);
constexpr u32 kOddPerBlock = 1u << 18;  // odd integers per sieve block

u64 floor_sqrt(u64 x) {
    u64 r = static_cast<u64>(std::sqrt(static_cast<long double>(x)));
    while (r > 0 && r * r > x) --r;
    while ((r + 1) * (r + 1) <= x) ++r;
    return r;
}

u64 splitmix_finalize(u64 z) {
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

[[noreturn]] void fail(const char* msg, u64 value) {
    std::fprintf(stderr, "odd_carry: %s (%" PRIu64 ")\n", msg, value);
    std::exit(2);
}

// Statistics of one finished index segment.
struct Stats {
    u64 k = 0, lo = 0, hi = 0;
    u64 count = 0, sum_slack = 0, hash = 0;
    u64 min_slack = ~0ULL, min_slack_n = 0;
    std::vector<u64> equalities;
    u64 last_at_most[kNumThresholds] = {};
};

void print_stats(const Stats& st) {
    char hash[32];
    std::snprintf(hash, sizeof hash, "%016" PRIx64, st.hash);
    std::string out = "{\"k\":" + std::to_string(st.k) + ",\"lo\":" + std::to_string(st.lo) +
                      ",\"hi\":" + std::to_string(st.hi) +
                      ",\"count\":" + std::to_string(st.count) + ",\"equalities\":[";
    for (std::size_t i = 0; i < st.equalities.size(); ++i)
        out += (i ? "," : "") + std::to_string(st.equalities[i]);
    out += "],\"min_slack\":" + std::to_string(st.min_slack) +
           ",\"min_slack_n\":" + std::to_string(st.min_slack_n) +
           ",\"sum_slack\":" + std::to_string(st.sum_slack) + ",\"hash\":\"" + hash +
           "\",\"last_at_most\":[";
    for (int t = 0; t < kNumThresholds; ++t)
        out += (t ? "," : "") + std::to_string(st.last_at_most[t]);
    out += "]}\n";
    std::fputs(out.c_str(), stdout);
    std::fflush(stdout);
}

// Sequential scanner holding the carried maximum and the open segment.
class Scanner {
  public:
    Scanner(u64 n_lo, u64 n_hi, u64 seg) : n_lo_(n_lo), n_hi_(n_hi), seg_(seg) {
        k_ = (n_lo - 1) / seg;
        set_bounds();
        expected_ = n_lo;
    }

    // Consume the odd integers m0, m0 + 2, ..., m0 + 2*(len-1) and their lpf.
    void scan_block(const u32* lpf, u64 m0, u32 len) {
        u32 i = 0;
        while (i < len) {
            const u64 m = m0 + 2 * u64(i);
            if (m >= n_lo_ && m + 1 <= seg_hi_) {
                const u32 stop =
                    static_cast<u32>(std::min<u64>(len, (seg_hi_ - 1 - m0) / 2 + 1));
                fast_range(lpf, m0, i, stop);
                i = stop;
            } else {
                slow_record(m, std::max<u64>(1, R_ + 1 > m ? R_ + 1 - m : 0));
                if (lpf[i] != 0 && m + lpf[i] - 1 > R_) R_ = m + lpf[i] - 1;
                slow_record(m + 1, R_ > m ? R_ - m : 0);
                ++i;
            }
        }
    }

    void finish() {
        if (expected_ != n_hi_ + 1) fail("run ended before N_HI; next n", expected_);
        close_segment();
    }

    std::vector<Stats> done;

  private:
    void set_bounds() {
        seg_lo_ = std::max(n_lo_, k_ * seg_ + 1);
        seg_hi_ = std::min(n_hi_, (k_ + 1) * seg_);
    }

    // Hot loop: every recorded n lies in [n_lo, seg_hi], so no range or
    // segment checks are needed.  Accumulators are locals, written back once.
    void fast_range(const u32* lpf, u64 m0, u32 i0, u32 i1) {
        u64 R = R_, count = count_, sum = sum_slack_, hash = hash_;
        u64 mn = min_slack_, mn_n = min_slack_n_;
        int cls = cls_;
        // Slacks in class cls lie in (cls_lo, cls_hi]; recompute only on exit.
        u64 cls_lo = cls > 0 ? kThresholds[cls - 1] : 0;
        u64 cls_hi = cls < kNumThresholds ? kThresholds[cls] : ~0ULL;
        u64* last_in_class = last_in_class_;
        if (m0 + 2 * u64(i0) != expected_) fail("index sequence skipped n", expected_);
        for (u32 i = i0; i < i1; ++i) {
            const u64 m = m0 + 2 * u64(i);
            for (int parity = 1; parity >= 0; --parity) {
                u64 n, s;
                if (parity == 1) {  // odd n = m: odd witnesses m' <= m - 2
                    n = m;
                    s = R + 1 > n ? R + 1 - n : 0;
                    if (s < 1) s = 1;  // even witness n - 1
                } else {            // even n = m + 1: odd witnesses m' <= m
                    if (lpf[i] != 0 && m + lpf[i] - 1 > R) R = m + lpf[i] - 1;
                    n = m + 1;
                    s = R > m ? R - m : 0;
                }
                ++count;
                sum += s;
                hash += splitmix_finalize((n << 20) + s);
                if (s < mn) {
                    mn = s;
                    mn_n = n;
                }
                if (s - cls_lo - 1 >= cls_hi - cls_lo) {  // s outside (cls_lo, cls_hi]
                    while (cls < kNumThresholds && kThresholds[cls] < s) ++cls;
                    while (cls > 0 && kThresholds[cls - 1] >= s) --cls;
                    cls_lo = cls > 0 ? kThresholds[cls - 1] : 0;
                    cls_hi = cls < kNumThresholds ? kThresholds[cls] : ~0ULL;
                }
                last_in_class[cls] = n;
                if (s == 0) equalities_.push_back(n);
            }
        }
        R_ = R;
        count_ = count;
        sum_slack_ = sum;
        hash_ = hash;
        min_slack_ = mn;
        min_slack_n_ = mn_n;
        cls_ = cls;
        expected_ = m0 + 2 * u64(i1);
    }

    // Generic path for boundary positions.
    void slow_record(u64 n, u64 s) {
        if (n < n_lo_ || n > n_hi_) return;
        if (n > seg_hi_) close_segment();
        if (n != expected_) fail("index sequence skipped n", expected_);
        ++expected_;
        ++count_;
        sum_slack_ += s;
        hash_ += splitmix_finalize((n << 20) + s);
        if (s < min_slack_) {
            min_slack_ = s;
            min_slack_n_ = n;
        }
        while (cls_ < kNumThresholds && kThresholds[cls_] < s) ++cls_;
        while (cls_ > 0 && kThresholds[cls_ - 1] >= s) --cls_;
        last_in_class_[cls_] = n;
        if (s == 0) equalities_.push_back(n);
    }

    void close_segment() {
        Stats st;
        st.k = k_;
        st.lo = seg_lo_;
        st.hi = seg_hi_;
        st.count = count_;
        st.sum_slack = sum_slack_;
        st.hash = hash_;
        st.min_slack = min_slack_;
        st.min_slack_n = min_slack_n_;
        st.equalities.swap(equalities_);
        u64 running = 0;
        for (int t = 0; t < kNumThresholds; ++t) {
            running = std::max(running, last_in_class_[t]);
            st.last_at_most[t] = running;
        }
        if (st.count != st.hi - st.lo + 1) fail("segment incomplete, k", k_);
        done.push_back(std::move(st));
        count_ = sum_slack_ = hash_ = 0;
        min_slack_ = ~0ULL;
        min_slack_n_ = 0;
        std::fill(last_in_class_, last_in_class_ + kNumThresholds + 1, 0);
        ++k_;
        set_bounds();
    }

    const u64 n_lo_, n_hi_, seg_;
    u64 k_ = 0, seg_lo_ = 0, seg_hi_ = 0;
    u64 R_ = 0;  // max of m + p(m) - 1 over odd composite m scanned so far
    u64 expected_ = 0;
    u64 count_ = 0, sum_slack_ = 0, hash_ = 0, min_slack_ = ~0ULL, min_slack_n_ = 0;
    int cls_ = 0;  // number of thresholds strictly below the latest slack
    u64 last_in_class_[kNumThresholds + 1] = {};  // last n per threshold class
    std::vector<u64> equalities_;
};

// Least prime factors of the odd integers m0, m0 + 2, ..., m0 + 2*(len-1).
void sieve_odd_block(u64 m0, u32 len, const std::vector<u32>& odd_primes, u32* lpf) {
    std::memset(lpf, 0, sizeof(u32) * len);
    const u64 m_last = m0 + 2 * u64(len - 1);
    for (u32 p32 : odd_primes) {
        const u64 p = p32;
        if (p * p > m_last) break;
        u64 first = p * p;
        if (first < m0) {
            first = ((m0 + p - 1) / p) * p;
            if ((first & 1ULL) == 0) first += p;
        }
        for (u64 i = (first - m0) >> 1; i < len; i += p) {
            const u32 v = lpf[i];
            lpf[i] = v != 0 ? v : p32;
        }
    }
}

}  // namespace

int main(int argc, char** argv) {
    if (argc != 5) {
        std::fprintf(stderr, "usage: %s N_LO N_HI SEG THREADS\n", argv[0]);
        return 1;
    }
    const u64 n_lo = std::strtoull(argv[1], nullptr, 10);
    const u64 n_hi = std::strtoull(argv[2], nullptr, 10);
    const u64 seg = std::strtoull(argv[3], nullptr, 10);
    const unsigned threads = static_cast<unsigned>(std::strtoul(argv[4], nullptr, 10));
    if (n_lo < 6 || n_hi < n_lo || n_hi > 1000000000000ULL || seg == 0 || threads == 0) {
        std::fprintf(stderr, "require 6 <= N_LO <= N_HI <= 10^12, SEG > 0, THREADS > 0\n");
        return 1;
    }
    const auto t0 = std::chrono::steady_clock::now();
    // Every slack satisfies F(n) - n <= p(m) - 1 < sqrt(N_HI) <= 10^6 < 2^20,
    // so the fingerprint key (n << 20) + s is injective on the whole run.
    if (floor_sqrt(n_hi) >= (1ULL << 20)) fail("N_HI too large for the fingerprint", n_hi);

    // Odd primes up to floor_sqrt(N_HI) + 1 via an odd-only sieve.
    const u64 bound = floor_sqrt(n_hi) + 1;
    std::vector<bool> odd_comp(bound / 2 + 1, false);  // index i <-> 2i + 1
    std::vector<u32> odd_primes;
    for (u64 q = 3; q <= bound; q += 2) {
        if (odd_comp[q / 2]) continue;
        odd_primes.push_back(static_cast<u32>(q));
        for (u64 r = q * q; r <= bound; r += 2 * q) odd_comp[r / 2] = true;
    }

    // Odd m scanned: from the start point through the odd m_last, which
    // records the index n_hi either as m_last or as m_last + 1.
    u64 start = 3;
    const u64 warm = 2 * floor_sqrt(n_hi) + 9;
    if (n_lo > warm + 3) {
        const u64 w = n_lo - warm;
        start = (w & 1ULL) ? w : w - 1;
    }
    const u64 m_last = (n_hi & 1ULL) ? n_hi : n_hi - 1;
    const u64 n_odd = (m_last - start) / 2 + 1;
    const u64 nblocks = (n_odd + kOddPerBlock - 1) / kOddPerBlock;

    const unsigned workers = threads > 1 ? threads - 1 : 1;
    const std::size_t ring = threads > 1 ? 2 * workers : 1;
    std::vector<std::vector<u32>> slot(ring, std::vector<u32>(kOddPerBlock));
    std::vector<u64> ready(ring, ~0ULL), free_for(ring);
    for (std::size_t s = 0; s < ring; ++s) free_for[s] = s;
    std::mutex mu;
    std::condition_variable cv_ready, cv_free;
    std::atomic<u64> next_block{0};

    auto block_start = [&](u64 b) { return start + 2 * b * kOddPerBlock; };
    auto block_len = [&](u64 b) {
        return static_cast<u32>(std::min<u64>(kOddPerBlock, n_odd - b * kOddPerBlock));
    };
    auto sieve_worker = [&]() {
        for (u64 b; (b = next_block.fetch_add(1)) < nblocks;) {
            const std::size_t s = b % ring;
            {
                std::unique_lock<std::mutex> lk(mu);
                cv_free.wait(lk, [&] { return free_for[s] == b; });
            }
            sieve_odd_block(block_start(b), block_len(b), odd_primes, slot[s].data());
            {
                std::lock_guard<std::mutex> lk(mu);
                ready[s] = b;
            }
            cv_ready.notify_all();
        }
    };

    std::printf("{\"program\":\"odd_carry\",\"n_lo\":%" PRIu64 ",\"n_hi\":%" PRIu64
                ",\"seg\":%" PRIu64 ",\"thresholds\":[",
                n_lo, n_hi, seg);
    for (int t = 0; t < kNumThresholds; ++t)
        std::printf("%s%" PRIu64, t ? "," : "", kThresholds[t]);
    std::printf("]}\n");
    std::fflush(stdout);

    std::vector<std::thread> pool;
    if (threads > 1)
        for (unsigned w = 0; w < workers; ++w) pool.emplace_back(sieve_worker);

    Scanner scanner(n_lo, n_hi, seg);
    std::size_t printed = 0;
    for (u64 b = 0; b < nblocks; ++b) {
        const std::size_t s = b % ring;
        if (threads > 1) {
            std::unique_lock<std::mutex> lk(mu);
            cv_ready.wait(lk, [&] { return ready[s] == b; });
        } else {
            sieve_odd_block(block_start(b), block_len(b), odd_primes, slot[s].data());
        }
        scanner.scan_block(slot[s].data(), block_start(b), block_len(b));
        if (threads > 1) {
            {
                std::lock_guard<std::mutex> lk(mu);
                free_for[s] = b + ring;
            }
            cv_free.notify_all();
        }
        while (printed < scanner.done.size()) print_stats(scanner.done[printed++]);
        if ((b & 1023) == 1023)
            std::fprintf(stderr, "odd_carry: scanned through m=%" PRIu64 "\n",
                         block_start(b) + 2 * u64(block_len(b) - 1));
    }
    for (auto& th : pool) th.join();
    scanner.finish();
    while (printed < scanner.done.size()) print_stats(scanner.done[printed++]);
    const double secs =
        std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::fprintf(stderr, "odd_carry: %" PRIu64 " blocks, %u threads, %.2f s\n", nblocks, threads,
                 secs);
    return 0;
}
