// lp_orbit_search.cpp -- implementation 1 of the multiplier-orbit Legendre-pair search.
//
// Decides, for odd length L and a subgroup H of (Z/LZ)^*, whether there is a Legendre pair
// (A, B) of length L with BOTH A and B constant on the H-orbits of Z/LZ and
// sum(A) = sum(B) = 1 (the standard normalization; negating A or B preserves the pair).
//
// Method (everything is exact except the explicitly bounded floating-point filter):
//  * Orbits O_0 = {0}, O_1, ... of H acting on Z/LZ by multiplication; a candidate is a sign
//    vector eps in {+1,-1}^n with A(x) = eps[orbit(x)].
//  * Meet-in-the-middle over the orbits, keyed by an exact integer vector:
//      - if 3 | L: the 3-compression (u, v, w) = sums of A over x = 0, 1, 2 (mod 3).  For an LP,
//        u + v + w = 1 and N(u + v*w3 + w*w3^2) + N(u' + v'*w3 + w'*w3^2) = 2L + 2 (the LP
//        identity at frequency L/3, w3 = exp(2 pi i / 3), N = squared modulus).  Each of u, v,
//        w is a sum of L/3 signs, so the admissible (u, v, w) form a finite target set T;
//      - otherwise: the sum alone (target 1).
//    The number of examined sign vectors is compared with an exact dynamic-programming count
//    of all sign vectors whose key lies in T (completeness self-check).
//  * Floating-point PSD filter: PSD_A(k) <= 2L + 2 is necessary because
//    PSD_A(k) + PSD_B(k) = 2L + 2 and PSD_B(k) >= 0.  PSD_A is invariant under k -> h k
//    (h in H) and k -> -k, so one frequency per <H,-1>-orbit is checked.  A candidate is
//    rejected only if the computed PSD exceeds 2L + 2 + 1e-6, while the accumulated rounding
//    error is below 1e-9, so no sequence whose true PSD is <= 2L + 2 everywhere is rejected.
//  * Survivors: exact integer periodic autocorrelations PAF_A(s) at one s per <H,-1>-orbit,
//    computed with bitsets.  A pair needs PAF_A(s) + PAF_B(s) = -2 for every s != 0; with
//    key(s) = (L - PAF(s)) / 4 this reads key_A + key_B = (L + 1) / 2 componentwise.
//    Survivors are sorted by key and every complement key is binary-searched.  Any pair
//    found is re-verified on all L - 1 shifts and written out.
//
// Usage: lp_orbit_search L gens [threads] [ybits] [pairs_out|-] [survivors_out]
//   gens: comma-separated generators of H, e.g. "46" or "10,112" ("1" = trivial subgroup).
// Build: g++ -O3 -std=c++17 -pthread -o lp_orbit_search lp_orbit_search.cpp
#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <numeric>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>
#include <utility>
#include <vector>
using namespace std;

static const long double PI_L = 3.14159265358979323846264338327950288L;
typedef unsigned __int128 u128;

int main(int argc, char** argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s L gens [threads] [ybits] [pairs_out|-] [survivors_out]\n", argv[0]);
        return 2;
    }
    const int L = atoi(argv[1]);
    if (L % 2 == 0 || L < 3 || L > 2047) { fprintf(stderr, "L must be odd, 3..2047\n"); return 2; }
    vector<int> gens;
    {
        stringstream ss(argv[2]);
        string t;
        while (getline(ss, t, ',')) gens.push_back(((stoi(t) % L) + L) % L);
    }
    const int nthreads = argc > 3 ? atoi(argv[3]) : 3;
    const int ybits = argc > 4 ? atoi(argv[4]) : 22;
    const char* pairs_out = (argc > 5 && strcmp(argv[5], "-") != 0) ? argv[5] : nullptr;
    const char* surv_out = argc > 6 ? argv[6] : nullptr;
    for (int g : gens)
        if (std::gcd(g, L) != 1) { fprintf(stderr, "generator %d is not a unit\n", g); return 2; }

    // ---- subgroup H and its orbits on Z/LZ ----
    vector<char> inH(L, 0);
    vector<int> H = {1};
    inH[1] = 1;
    for (size_t i = 0; i < H.size(); i++)
        for (int g : gens) {
            int y = (int)((long long)H[i] * g % L);
            if (!inH[y]) { inH[y] = 1; H.push_back(y); }
        }
    sort(H.begin(), H.end());
    vector<int> orb(L, -1);
    vector<vector<int>> orbits;
    for (int x = 0; x < L; x++)
        if (orb[x] < 0) {
            vector<int> o;
            for (int h : H) {
                int y = (int)((long long)h * x % L);
                if (orb[y] < 0) { orb[y] = (int)orbits.size(); o.push_back(y); }
            }
            orbits.push_back(o);
        }
    const int n = (int)orbits.size();
    if (n > 63) { fprintf(stderr, "too many orbits (%d)\n", n); return 2; }

    // ---- frequency / shift representatives: orbits of <H,-1> on nonzero residues ----
    vector<int> rep;
    {
        vector<char> seen(L, 0);
        for (int k = 1; k < L; k++)
            if (!seen[k]) {
                rep.push_back(k);
                for (int h : H) {
                    int y = (int)((long long)h * k % L);
                    seen[y] = 1;
                    seen[(L - y) % L] = 1;
                }
            }
    }
    const int F = (int)rep.size();
    const double LIM = 2.0 * L + 2.0 + 1e-6;

    // ---- orbit Gauss sums S[j][f] = sum_{x in O_j} exp(2 pi i rep[f] x / L) ----
    vector<double> Sre((size_t)n * F), Sim((size_t)n * F);
    for (int j = 0; j < n; j++)
        for (int f = 0; f < F; f++) {
            long double re = 0, im = 0;
            for (int x : orbits[j]) {
                long double a = 2.0L * PI_L * (long double)((long long)rep[f] * x % L) / L;
                re += cosl(a);
                im += sinl(a);
            }
            Sre[(size_t)j * F + f] = (double)re;
            Sim[(size_t)j * F + f] = (double)im;
        }
    // order frequencies by decreasing variance (most selective first)
    vector<int> ord(F);
    {
        vector<pair<double, int>> v;
        for (int f = 0; f < F; f++) {
            double s = 0;
            for (int j = 0; j < n; j++) {
                double a = Sre[(size_t)j * F + f], b = Sim[(size_t)j * F + f];
                s += a * a + b * b;
            }
            v.push_back({-s, f});
        }
        sort(v.begin(), v.end());
        for (int f = 0; f < F; f++) ord[f] = v[f].second;
    }
    vector<double> Gre((size_t)n * F), Gim((size_t)n * F);  // columns in filter order
    for (int j = 0; j < n; j++)
        for (int f = 0; f < F; f++) {
            Gre[(size_t)j * F + f] = Sre[(size_t)j * F + ord[f]];
            Gim[(size_t)j * F + f] = Sim[(size_t)j * F + ord[f]];
        }

    // ---- exact integer key: (u,v,w) = 3-compression if 3 | L, else (sum,0,0) ----
    const bool macro = (L % 3 == 0);
    vector<array<int, 3>> wgt(n);
    for (int j = 0; j < n; j++) {
        wgt[j] = {0, 0, 0};
        for (int x : orbits[j]) wgt[j][macro ? x % 3 : 0]++;
    }
    vector<array<int, 3>> T;
    auto Nrm = [](long long a, long long b, long long c) {
        return a * a + b * b + c * c - a * b - b * c - c * a;
    };
    if (macro) {
        const int m = L / 3;  // each 3-compression entry is a sum of m signs (m is odd)
        vector<char> isnorm(4 * (size_t)L * L + 1, 0);
        for (int pass = 0; pass < 2; pass++)
            for (int u = -m; u <= m; u += 2)
                for (int v = -m; v <= m; v += 2) {
                    int w = 1 - u - v;
                    if (w < -m || w > m || ((w - m) % 2) != 0) continue;
                    long long nn = Nrm(u, v, w);
                    if (pass == 0) { isnorm[nn] = 1; continue; }
                    long long co = 2LL * L + 2 - nn;
                    if (co >= 0 && isnorm[co]) T.push_back({u, v, w});
                }
    } else {
        T.push_back({1, 0, 0});
    }
    printf("L=%d gens=%s |H|=%zu orbits n=%d freq_reps F=%d key=%s targets=%zu\n", L, argv[2],
           H.size(), n, F, macro ? "3-compression" : "sum", T.size());
    if (macro) {
        map<long long, int> tv;
        for (auto& t : T) tv[Nrm(t[0], t[1], t[2])]++;
        printf("admissible PSD(L/3) values:");
        for (auto& p : tv) printf(" %lld", p.first);
        printf("\n");
    }

    // ---- exact DP: number of sign vectors whose key lies in T ----
    const int OFF = L + 1, W = 2 * L + 3;
    auto pack = [&](int a, int b, int c) -> uint64_t {
        return ((uint64_t)(a + OFF) * W + (uint64_t)(b + OFF)) * W + (uint64_t)(c + OFF);
    };
    auto unpack = [&](uint64_t k, int& a, int& b, int& c) {
        c = (int)(k % W) - OFF;
        b = (int)(k / W % W) - OFF;
        a = (int)(k / W / W) - OFF;
    };
    u128 expected = 0;
    {
        unordered_map<uint64_t, u128> dp, nd;
        dp[pack(0, 0, 0)] = 1;
        for (int j = 0; j < n; j++) {
            nd.clear();
            nd.reserve(dp.size() * 2);
            for (auto& kv : dp) {
                int a, b, c;
                unpack(kv.first, a, b, c);
                nd[pack(a + wgt[j][0], b + wgt[j][1], c + wgt[j][2])] += kv.second;
                nd[pack(a - wgt[j][0], b - wgt[j][1], c - wgt[j][2])] += kv.second;
            }
            swap(dp, nd);
        }
        for (auto& t : T) {
            auto it = dp.find(pack(t[0], t[1], t[2]));
            if (it != dp.end()) expected += it->second;
        }
    }
    printf("DP count of sign vectors with key in targets: %llu\n", (unsigned long long)expected);

    // ---- split orbits: X = first n1 orbits, Y = last n2 orbits ----
    const int n2 = min(ybits, n - 1), n1 = n - n2;
    const size_t NY = (size_t)1 << n2, NX = (size_t)1 << n1;
    int FT = F;  // frequencies stored in the Y table (the rest are recomputed on demand)
    while (FT > 1 && (double)NY * FT * 16.0 > 3.0e9) FT--;
    printf("split n1=%d n2=%d stored_freqs=%d\n", n1, n2, FT);
    fflush(stdout);

    // Y table sorted by key: ykey, ymask, yD
    vector<uint64_t> ykey(NY);
    vector<uint32_t> ymask(NY);
    vector<double> yD(NY * 2 * (size_t)FT);
    {
        vector<double> D(NY * 2 * (size_t)FT);
        vector<array<int, 3>> kk(NY);
        array<int, 3> k0 = {0, 0, 0};  // mask 0 = all signs +1
        for (int j = n1; j < n; j++)
            for (int c = 0; c < 3; c++) k0[c] += wgt[j][c];
        kk[0] = k0;
        for (int f = 0; f < FT; f++) {
            double re = 0, im = 0;
            for (int j = n1; j < n; j++) { re += Gre[(size_t)j * F + f]; im += Gim[(size_t)j * F + f]; }
            D[2 * f] = re;
            D[2 * f + 1] = im;
        }
        for (size_t m = 1; m < NY; m++) {
            int j = n1 + __builtin_ctzll(m);
            size_t p = m & (m - 1);
            for (int c = 0; c < 3; c++) kk[m][c] = kk[p][c] - 2 * wgt[j][c];
            const double* dprev = &D[p * 2 * FT];
            double* dm = &D[m * 2 * FT];
            for (int f = 0; f < FT; f++) {
                dm[2 * f] = dprev[2 * f] - 2 * Gre[(size_t)j * F + f];
                dm[2 * f + 1] = dprev[2 * f + 1] - 2 * Gim[(size_t)j * F + f];
            }
        }
        vector<uint64_t> key(NY);
        for (size_t m = 0; m < NY; m++) key[m] = pack(kk[m][0], kk[m][1], kk[m][2]);
        vector<uint32_t> idx(NY);
        iota(idx.begin(), idx.end(), 0);
        sort(idx.begin(), idx.end(), [&](uint32_t a, uint32_t b) {
            return key[a] != key[b] ? key[a] < key[b] : a < b;
        });
        for (size_t q = 0; q < NY; q++) {
            ykey[q] = key[idx[q]];
            ymask[q] = idx[q];
            memcpy(&yD[q * 2 * FT], &D[(size_t)idx[q] * 2 * FT], sizeof(double) * 2 * FT);
        }
    }
    unordered_map<uint64_t, pair<size_t, size_t>> yrange;  // key -> [lo, hi)
    for (size_t q = 0; q < NY;) {
        size_t r = q;
        while (r < NY && ykey[r] == ykey[q]) r++;
        yrange[ykey[q]] = {q, r};
        q = r;
    }
    // X masks sorted by key
    vector<pair<uint64_t, uint32_t>> xs(NX);
    for (size_t x = 0; x < NX; x++) {
        array<int, 3> k = {0, 0, 0};
        for (int j = 0; j < n1; j++) {
            int s = (x >> j & 1) ? -1 : 1;
            for (int c = 0; c < 3; c++) k[c] += s * wgt[j][c];
        }
        xs[x] = {pack(k[0], k[1], k[2]), (uint32_t)x};
    }
    sort(xs.begin(), xs.end());
    vector<pair<size_t, size_t>> xgroups;
    for (size_t q = 0; q < NX;) {
        size_t r = q;
        while (r < NX && xs[r].first == xs[q].first) r++;
        xgroups.push_back({q, r});
        q = r;
    }

    // ---- main meet-in-the-middle loop ----
    atomic<size_t> nextg(0);
    vector<unsigned long long> examined(nthreads, 0);
    vector<vector<uint64_t>> surv(nthreads);
    auto worker = [&](int tid) {
        vector<double> dx(2 * (size_t)F);
        vector<pair<size_t, size_t>> ranges;
        for (;;) {
            size_t g = nextg.fetch_add(1);
            if (g >= xgroups.size()) break;
            int xa, xb, xc;
            unpack(xs[xgroups[g].first].first, xa, xb, xc);
            ranges.clear();
            for (auto& t : T) {
                int ya = t[0] - xa, yb = t[1] - xb, yc = t[2] - xc;
                if (abs(ya) > L || abs(yb) > L || abs(yc) > L) continue;
                auto it = yrange.find(pack(ya, yb, yc));
                if (it != yrange.end()) ranges.push_back(it->second);
            }
            if (ranges.empty()) continue;
            for (size_t q = xgroups[g].first; q < xgroups[g].second; q++) {
                const uint32_t x = xs[q].second;
                for (int f = 0; f < 2 * F; f++) dx[f] = 0;
                for (int j = 0; j < n1; j++) {
                    double s = (x >> j & 1) ? -1.0 : 1.0;
                    for (int f = 0; f < F; f++) {
                        dx[2 * f] += s * Gre[(size_t)j * F + f];
                        dx[2 * f + 1] += s * Gim[(size_t)j * F + f];
                    }
                }
                for (auto& rg : ranges) {
                    examined[tid] += rg.second - rg.first;
                    for (size_t r = rg.first; r < rg.second; r++) {
                        const double* d = &yD[r * 2 * FT];
                        int f = 0;
                        for (; f < FT; f++) {
                            double re = dx[2 * f] + d[2 * f], im = dx[2 * f + 1] + d[2 * f + 1];
                            if (re * re + im * im > LIM) break;
                        }
                        if (f < FT) continue;
                        const uint32_t ym = ymask[r];
                        bool ok = true;
                        for (; f < F && ok; f++) {  // frequencies not stored in the table
                            double re = dx[2 * f], im = dx[2 * f + 1];
                            for (int j = n1; j < n; j++) {
                                double s = (ym >> (j - n1) & 1) ? -1.0 : 1.0;
                                re += s * Gre[(size_t)j * F + f];
                                im += s * Gim[(size_t)j * F + f];
                            }
                            if (re * re + im * im > LIM) ok = false;
                        }
                        if (ok) surv[tid].push_back((uint64_t)x | ((uint64_t)ym << n1));
                    }
                }
            }
        }
    };
    {
        vector<thread> th;
        for (int t = 0; t < nthreads; t++) th.emplace_back(worker, t);
        for (auto& t : th) t.join();
    }
    unsigned long long tot_exam = 0;
    for (auto e : examined) tot_exam += e;
    const bool complete = ((u128)tot_exam == expected);
    vector<uint64_t> S;
    for (auto& v : surv) S.insert(S.end(), v.begin(), v.end());
    vector<vector<uint64_t>>().swap(surv);
    sort(S.begin(), S.end());
    printf("examined sign vectors (key in targets): %llu  [DP: %llu]  %s\n", tot_exam,
           (unsigned long long)expected, complete ? "MATCH" : "MISMATCH");
    printf("PSD survivors: %zu\n", S.size());
    fflush(stdout);
    if (S.size() >= 0xFFFFFFFFull) { fprintf(stderr, "too many survivors\n"); return 2; }
    if (surv_out) {  // one survivor per line: the orbit sign mask (bit j set = orbit j has sign -1)
        FILE* fs = fopen(surv_out, "w");
        for (uint64_t s : S) fprintf(fs, "%llu\n", (unsigned long long)s);
        fclose(fs);
    }

    // ---- exact PAF keys with bitsets (bit = 1 means entry -1) ----
    const int LW = (L + 63) / 64;
    const int WORDS = (2 * L + 63) / 64 + 1;  // doubled sequence + padding word
    vector<vector<uint64_t>> obits(n, vector<uint64_t>(WORDS, 0));
    for (int j = 0; j < n; j++)
        for (int x : orbits[j]) {
            obits[j][x / 64] |= 1ULL << (x % 64);
            obits[j][(x + L) / 64] |= 1ULL << ((x + L) % 64);
        }
    const uint64_t lastmask = (L % 64) ? ((1ULL << (L % 64)) - 1) : ~0ULL;
    auto paf_keys = [&](uint64_t mask, uint16_t* out) {
        vector<uint64_t> b(WORDS, 0);
        for (int j = 0; j < n; j++)
            if (mask >> j & 1)
                for (int w = 0; w < WORDS; w++) b[w] |= obits[j][w];
        for (int f = 0; f < F; f++) {
            const int s = rep[f];
            int dist = 0;  // #{x : A(x) != A(x+s)}
            for (int w = 0; w < LW; w++) {
                int pos = 64 * w + s, wi = pos / 64, sh = pos % 64;
                uint64_t r = b[wi] >> sh;
                if (sh) r |= b[wi + 1] << (64 - sh);
                uint64_t z = b[w] ^ r;
                if (w == LW - 1) z &= lastmask;
                dist += __builtin_popcountll(z);
            }
            if (dist % 2) { fprintf(stderr, "odd disagreement count?!\n"); exit(3); }
            out[f] = (uint16_t)(dist / 2);  // = (L - PAF(s)) / 4
        }
    };
    vector<uint16_t> keys(S.size() * (size_t)F);
    {
        atomic<size_t> nx(0);
        auto kw = [&]() {
            for (;;) {
                size_t i = nx.fetch_add(4096);
                if (i >= S.size()) break;
                size_t e = min(S.size(), i + 4096);
                for (size_t q = i; q < e; q++) paf_keys(S[q], &keys[q * F]);
            }
        };
        vector<thread> th;
        for (int t = 0; t < nthreads; t++) th.emplace_back(kw);
        for (auto& t : th) t.join();
    }
    auto kless = [&](const uint16_t* a, const uint16_t* b) {
        for (int f = 0; f < F; f++)
            if (a[f] != b[f]) return a[f] < b[f];
        return false;
    };
    vector<uint32_t> sidx(S.size());
    iota(sidx.begin(), sidx.end(), 0);
    sort(sidx.begin(), sidx.end(), [&](uint32_t a, uint32_t b) {
        return kless(&keys[(size_t)a * F], &keys[(size_t)b * F]);
    });
    size_t distinct = 0;
    for (size_t q = 0; q < sidx.size(); q++)
        if (q == 0 || kless(&keys[(size_t)sidx[q - 1] * F], &keys[(size_t)sidx[q] * F])) distinct++;
    printf("distinct PAF keys among survivors: %zu\n", distinct);

    // ---- complement search ----
    const int HALF = (L + 1) / 2;
    size_t pairs = 0;
    FILE* pf = pairs_out ? fopen(pairs_out, "w") : nullptr;
    vector<uint16_t> want(F);
    for (size_t q = 0; q < S.size(); q++) {
        const uint16_t* k = &keys[q * F];
        bool bad = false;
        for (int f = 0; f < F; f++) {
            if (k[f] > HALF) { bad = true; break; }
            want[f] = (uint16_t)(HALF - k[f]);
        }
        if (bad) continue;
        auto lo = lower_bound(sidx.begin(), sidx.end(), 0u, [&](uint32_t a, uint32_t) {
            return kless(&keys[(size_t)a * F], want.data());
        });
        for (auto it = lo; it != sidx.end() && !kless(want.data(), &keys[(size_t)*it * F]); ++it) {
            const uint64_t ma = S[q], mb = S[*it];
            vector<int> A(L), B(L);
            for (int x = 0; x < L; x++) {
                A[x] = (ma >> orb[x] & 1) ? -1 : 1;
                B[x] = (mb >> orb[x] & 1) ? -1 : 1;
            }
            bool ok = true;  // exact verification on every shift
            for (int s = 1; s < L && ok; s++) {
                long long p = 0;
                for (int x = 0; x < L; x++) p += A[x] * A[(x + s) % L] + B[x] * B[(x + s) % L];
                if (p != -2) ok = false;
            }
            if (!ok) { fprintf(stderr, "key match failed exact verification?!\n"); exit(4); }
            pairs++;
            if (pf) {
                for (int x = 0; x < L; x++) fputc(A[x] > 0 ? '+' : '-', pf);
                fputc(' ', pf);
                for (int x = 0; x < L; x++) fputc(B[x] > 0 ? '+' : '-', pf);
                fputc('\n', pf);
            }
        }
    }
    if (pf) fclose(pf);
    printf("ordered Legendre pairs (A,B) found in this class: %zu\n", pairs);
    printf("RESULT L=%d gens=%s n=%d examined=%llu survivors=%zu distinct_keys=%zu pairs=%zu %s\n", L,
           argv[2], n, tot_exam, S.size(), distinct, pairs, complete ? "complete" : "INCOMPLETE");
    return complete ? 0 : 1;
}
