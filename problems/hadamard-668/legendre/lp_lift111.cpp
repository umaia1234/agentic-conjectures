// lp_lift111.cpp -- exhaustive Legendre-pair search over the lifts of admissible 3-compressions.
//
// Let (A, B) be a Legendre pair of length L (3 | L) with sum 1, both constant on the orbits of a
// multiplier group H.  With M = L/3, the 3-compression A'(y) = A(y) + A(y+M) + A(y+2M) of A must
// be one of the admissible compressions in adm_file (computed by lp_comp111, which needs both A'
// and B' to be H-invariant and to form a compressed pair).  This program enumerates EVERY
// H-invariant sign vector A whose 3-compression is in adm_file ("lifts"), applies the necessary
// condition PSD_A(k) <= 2L + 2 at every frequency k not divisible by 3 (frequencies 3k are fixed by
// A' and were already checked; one k per <H,-1>-orbit; floating point with tolerance 1e-6, rounding
// error below 1e-9, so no valid A is rejected), and then matches exact integer PAF keys of the
// survivors: key(s) = (L - PAF_A(s)) / 4 at one shift per <H,-1>-orbit, a pair needing
// key_A + key_B = (L + 1) / 2 for every s.  Any pair found is re-verified at all L - 1 shifts.
// The number of examined lifts is compared with the independently computed product of the
// per-orbit choice counts (completeness self-check).
//
// Usage: lp_lift111 L gens adm_file [threads] [pairs_out|-] [survivors_out]
// Build: g++ -O2 -std=c++17 -pthread -o lp_lift111 lp_lift111.cpp
#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <vector>
using namespace std;

static const long double PI_L = 3.14159265358979323846264338327950288L;

int main(int argc, char** argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: %s L gens adm_file [threads] [pairs_out|-] [survivors_out]\n", argv[0]);
        return 2;
    }
    const int L = atoi(argv[1]);
    if (L % 3 != 0 || L % 2 == 0 || L > 1023) { fprintf(stderr, "L must be odd, divisible by 3, <= 1023\n"); return 2; }
    const int M = L / 3;
    const int nthreads = argc > 4 ? atoi(argv[4]) : 3;
    const char* pairs_out = (argc > 5 && strcmp(argv[5], "-") != 0) ? argv[5] : nullptr;
    const char* surv_out = argc > 6 ? argv[6] : nullptr;
    vector<long long> gens;
    {
        stringstream ss(argv[2]);
        string t;
        while (getline(ss, t, ',')) gens.push_back(((stoll(t) % L) + L) % L);
    }
    vector<char> inH(L, 0);
    vector<int> H = {1};
    inH[1] = 1;
    for (size_t i = 0; i < H.size(); i++)
        for (long long g : gens) {
            if (std::gcd((long long)L, g) != 1) { fprintf(stderr, "non-unit generator\n"); return 2; }
            int y = (int)(H[i] * g % L);
            if (!inH[y]) { inH[y] = 1; H.push_back(y); }
        }
    // H-orbits on Z/L, numbered by least element (same convention as the other programs)
    vector<int> orbL(L, -1);
    vector<vector<int>> orbits;
    for (int x = 0; x < L; x++)
        if (orbL[x] < 0) {
            set<int> o;
            for (int h : H) o.insert((int)((long long)h * x % L));
            for (int z : o) orbL[z] = (int)orbits.size();
            orbits.push_back(vector<int>(o.begin(), o.end()));
        }
    const int n = (int)orbits.size();
    if (n > 64) { fprintf(stderr, "n=%d > 64 orbits not supported\n", n); return 2; }
    // orbits of H mod M on Z/M; every H-orbit of Z/L lies over exactly one of them
    vector<int> orbM(M, -1);
    vector<vector<int>> morbs;
    for (int y = 0; y < M; y++)
        if (orbM[y] < 0) {
            set<int> o;
            for (int h : H) o.insert((int)((long long)h * y % M));
            for (int z : o) orbM[z] = (int)morbs.size();
            morbs.push_back(vector<int>(o.begin(), o.end()));
        }
    const int nM = (int)morbs.size();
    vector<vector<int>> over(nM);  // H-orbits over each M-orbit
    vector<int> wm(n);             // points of orbit j over each y of its M-orbit
    for (int j = 0; j < n; j++) {
        int k = orbM[orbits[j][0] % M];
        for (int x : orbits[j])
            if (orbM[x % M] != k) { fprintf(stderr, "orbit projection error\n"); return 3; }
        if (orbits[j].size() % morbs[k].size()) { fprintf(stderr, "weight error\n"); return 3; }
        wm[j] = (int)(orbits[j].size() / morbs[k].size());
        over[k].push_back(j);
    }
    // frequencies not divisible by 3, one per <H,-1>-orbit; shifts: one per <H,-1>-orbit
    vector<int> freqs, shifts;
    {
        vector<char> seen(L, 0);
        for (int k = 1; k < L; k++)
            if (!seen[k]) {
                shifts.push_back(k);
                if (k % 3) freqs.push_back(k);
                for (int h : H) {
                    int y = (int)((long long)h * k % L);
                    seen[y] = seen[L - y] = 1;
                }
            }
    }
    const int F = (int)freqs.size(), NS = (int)shifts.size();
    const double LIM = 2.0 * L + 2.0 + 1e-6;
    vector<double> Gr((size_t)n * F), Gi((size_t)n * F);
    {
        vector<double> R((size_t)n * F), I((size_t)n * F);
        vector<pair<double, int>> var(F);
        for (int f = 0; f < F; f++) var[f] = {0.0, f};
        for (int j = 0; j < n; j++)
            for (int f = 0; f < F; f++) {
                long double re = 0, im = 0;
                for (int x : orbits[j]) {
                    long double a = 2.0L * PI_L * (long double)((long long)freqs[f] * x % L) / L;
                    re += cosl(a);
                    im += sinl(a);
                }
                R[(size_t)j * F + f] = (double)re;
                I[(size_t)j * F + f] = (double)im;
                var[f].first -= (double)(re * re + im * im);
            }
        sort(var.begin(), var.end());  // most selective (largest total weight) first
        for (int j = 0; j < n; j++)
            for (int f = 0; f < F; f++) {
                Gr[(size_t)j * F + f] = R[(size_t)j * F + var[f].second];
                Gi[(size_t)j * F + f] = I[(size_t)j * F + var[f].second];
            }
    }
    // admissible compressions
    vector<vector<int>> adm;
    {
        ifstream in(argv[3]);
        string line;
        while (getline(in, line)) {
            stringstream ss(line);
            vector<int> a;
            int v;
            while (ss >> v) a.push_back(v);
            if (a.empty()) continue;
            if ((int)a.size() != M) { fprintf(stderr, "adm line has %zu entries, expected %d\n", a.size(), M); return 2; }
            for (int y = 0; y < M; y++)
                if (a[y] != a[morbs[orbM[y]][0]]) { fprintf(stderr, "adm entry not invariant\n"); return 2; }
            adm.push_back(a);
        }
    }
    printf("L=%d gens=%s |H|=%zu orbits n=%d M-orbits=%d freq_reps(3 not dividing k)=%d shift_reps=%d admissible_A'=%zu\n",
           L, argv[2], H.size(), n, nM, F, NS, adm.size());
    fflush(stdout);

    unsigned long long examined = 0;
    long double expected = 0;
    vector<uint64_t> surv;
    for (size_t ai = 0; ai < adm.size(); ai++) {
        const vector<int>& a = adm[ai];
        // choices per M-orbit: sign patterns on the orbits over it with the right fibre sum
        vector<vector<uint64_t>> ch(nM);
        long double cnt = 1;
        for (int k = 0; k < nM; k++) {
            const vector<int>& js = over[k];
            for (uint32_t s = 0; s < (1u << js.size()); s++) {
                int sum = 0;
                uint64_t m = 0;
                for (size_t i = 0; i < js.size(); i++) {
                    bool neg = (s >> i) & 1;
                    sum += (neg ? -1 : 1) * wm[js[i]];
                    if (neg) m |= 1ULL << js[i];
                }
                if (sum == a[morbs[k][0]]) ch[k].push_back(m);
            }
            cnt *= (long double)ch[k].size();
        }
        expected += cnt;
        if (cnt == 0) continue;
        // split the M-orbits into two sides with balanced products
        vector<int> ord(nM);
        iota(ord.begin(), ord.end(), 0);
        sort(ord.begin(), ord.end(), [&](int p, int q) { return ch[p].size() > ch[q].size(); });
        vector<int> K1, K2;
        double l1 = 0, l2 = 0;
        for (int k : ord) {
            double lg = log((double)ch[k].size());
            if (l1 <= l2) { K1.push_back(k); l1 += lg; } else { K2.push_back(k); l2 += lg; }
        }
        auto build = [&](const vector<int>& K, vector<uint64_t>& masks, vector<double>& D) {
            masks.assign(1, 0);
            for (int k : K) {
                vector<uint64_t> nm;
                nm.reserve(masks.size() * ch[k].size());
                for (uint64_t m : masks)
                    for (uint64_t c : ch[k]) nm.push_back(m | c);
                masks.swap(nm);
            }
            vector<char> side(n, 0);
            for (int k : K)
                for (int j : over[k]) side[j] = 1;
            D.assign(masks.size() * 2 * F, 0.0);
            for (size_t q = 0; q < masks.size(); q++) {
                double* d = &D[q * 2 * F];
                for (int j = 0; j < n; j++) {
                    if (!side[j]) continue;
                    double sg = (masks[q] >> j & 1) ? -1.0 : 1.0;
                    for (int f = 0; f < F; f++) {
                        d[2 * f] += sg * Gr[(size_t)j * F + f];
                        d[2 * f + 1] += sg * Gi[(size_t)j * F + f];
                    }
                }
            }
        };
        vector<uint64_t> xm, ym;
        vector<double> xD, yD;
        build(K1, xm, xD);
        build(K2, ym, yD);
        atomic<size_t> next(0);
        vector<vector<uint64_t>> sv(nthreads);
        auto worker = [&](int tid) {
            for (;;) {
                size_t q = next.fetch_add(1);
                if (q >= xm.size()) break;
                const double* dx = &xD[q * 2 * F];
                for (size_t r = 0; r < ym.size(); r++) {
                    const double* dy = &yD[r * 2 * F];
                    int f = 0;
                    for (; f < F; f++) {
                        double re = dx[2 * f] + dy[2 * f], im = dx[2 * f + 1] + dy[2 * f + 1];
                        if (re * re + im * im > LIM) break;
                    }
                    if (f == F) sv[tid].push_back(xm[q] | ym[r]);
                }
            }
        };
        vector<thread> th;
        for (int t = 0; t < nthreads; t++) th.emplace_back(worker, t);
        for (auto& t : th) t.join();
        examined += (unsigned long long)xm.size() * ym.size();
        for (auto& v : sv) surv.insert(surv.end(), v.begin(), v.end());
    }
    printf("examined lifts: %llu  [product of choice counts: %.0Lf]  %s\n", examined, expected,
           (long double)examined == expected ? "MATCH" : "MISMATCH");
    printf("PSD survivors: %zu\n", surv.size());
    fflush(stdout);
    if ((long double)examined != expected) return 3;
    if (surv_out) {  // one sign mask per line (bit j set <=> A = -1 on the j-th H-orbit)
        FILE* fs = fopen(surv_out, "w");
        for (uint64_t m : surv) fprintf(fs, "%llu\n", (unsigned long long)m);
        fclose(fs);
    }
    // ---- exact PAF keys: key(s) = (number of i with A(i) != A(i+s)) / 2 = (L - PAF(s)) / 4 ----
    const size_t NSV = surv.size();
    vector<uint16_t> keys(NSV * NS);
    auto seq_of = [&](uint64_t m, vector<int8_t>& A) {
        A.resize(L);
        for (int x = 0; x < L; x++) A[x] = (m >> orbL[x] & 1) ? -1 : 1;
    };
    {
        atomic<size_t> next(0);
        auto kw = [&]() {
            vector<int8_t> A;
            for (;;) {
                size_t i = next.fetch_add(1);
                if (i >= NSV) break;
                seq_of(surv[i], A);
                int s0 = 0;
                for (int x = 0; x < L; x++) s0 += A[x];
                if (s0 != 1) { fprintf(stderr, "sum error\n"); exit(3); }
                for (int t = 0; t < NS; t++) {
                    int s = shifts[t], d = 0;
                    for (int x = 0; x < L - s; x++) d += A[x] != A[x + s];
                    for (int x = L - s; x < L; x++) d += A[x] != A[x + s - L];
                    keys[i * NS + t] = (uint16_t)(d / 2);
                }
            }
        };
        vector<thread> th;
        for (int t = 0; t < nthreads; t++) th.emplace_back(kw);
        for (auto& t : th) t.join();
    }
    vector<uint32_t> idx(NSV);
    iota(idx.begin(), idx.end(), 0);
    auto cmp = [&](uint32_t p, uint32_t q) { return memcmp(&keys[(size_t)p * NS], &keys[(size_t)q * NS], NS * 2) < 0; };
    // memcmp order is a consistent total order on the byte strings; binary search uses the same
    sort(idx.begin(), idx.end(), cmp);
    size_t distinct = 0;
    for (size_t i = 0; i < NSV; i++)
        if (i == 0 || memcmp(&keys[(size_t)idx[i] * NS], &keys[(size_t)idx[i - 1] * NS], NS * 2) != 0) distinct++;
    printf("distinct PAF keys among survivors: %zu\n", distinct);
    const uint16_t half = (uint16_t)((L + 1) / 2);
    unsigned long long pairs = 0;
    FILE* fp = pairs_out ? fopen(pairs_out, "w") : nullptr;
    vector<uint16_t> want(NS);
    vector<int8_t> A, B;
    for (size_t i = 0; i < NSV; i++) {
        bool ok = true;
        for (int t = 0; t < NS; t++) {
            int v = half - keys[(size_t)i * NS + t];
            if (v < 0) { ok = false; break; }
            want[t] = (uint16_t)v;
        }
        if (!ok) continue;
        size_t lo = 0, hi = NSV;
        while (lo < hi) {
            size_t mid = (lo + hi) / 2;
            if (memcmp(&keys[(size_t)idx[mid] * NS], want.data(), NS * 2) < 0) lo = mid + 1; else hi = mid;
        }
        for (size_t r = lo; r < NSV && memcmp(&keys[(size_t)idx[r] * NS], want.data(), NS * 2) == 0; r++) {
            seq_of(surv[i], A);
            seq_of(surv[idx[r]], B);
            for (int s = 1; s < L; s++) {
                int p = 0;
                for (int x = 0; x < L; x++) p += A[x] * A[(x + s) % L] + B[x] * B[(x + s) % L];
                if (p != -2) { fprintf(stderr, "verification failed?!\n"); return 4; }
            }
            pairs++;
            if (fp) fprintf(fp, "%llu %llu\n", (unsigned long long)surv[i], (unsigned long long)surv[idx[r]]);
        }
    }
    if (fp) fclose(fp);
    printf("ordered Legendre pairs found and verified: %llu\n", pairs);
    printf("RESULT L=%d gens=%s admissible=%zu examined=%llu survivors=%zu distinct_keys=%zu pairs=%llu complete\n", L,
           argv[2], adm.size(), examined, NSV, distinct, pairs);
    return 0;
}
