// comp_pairs.cpp -- exhaustive enumeration of U_m-invariant compressed Legendre pairs.
//
// Let L = Q * P with P an odd prime, gcd(Q, P) = 1, and let (A, B) be a Legendre pair of
// length L with sum(A) = sum(B) = 1.  The P-compressions c_r = sum_{x = r mod P} A(x) and
// d_r (r in Z/PZ) satisfy, exactly:
//   * c_r, d_r == Q (mod 2) and |c_r|, |d_r| <= Q;  sum(c) = sum(d) = 1;
//   * PAF_c(s) + PAF_d(s) = -2Q for s != 0 (mod P), i.e. PSD_c(t) + PSD_d(t) = 2L + 2 (t != 0).
// If A, B are invariant under a multiplier group whose image mod P contains the order-m
// subgroup U_m of (Z/PZ)^*, then c and d are constant on the cosets of U_m.  This program
// enumerates ALL such U_m-invariant pairs (c, d).
//
// Method: c = (c_0; x_1..x_k) with x_i the value on the i-th coset (k = (P-1)/m).  Meet in
// the middle over the coset values, keyed by the exact partial sum; Parseval pruning
// (sum c^2 <= 2L + 2 - 2Q - min sum d^2); floating-point PSD filter |DFT_c(t)|^2 <= 2L+2
// (+1e-6 tolerance, rounding error < 1e-9); exact integer PAF keys for the survivors and an
// exact complement search.  Prints every admissible c (one that has a partner) and counts.
//
// Usage: comp_pairs P Q m [threads] [admissible_out]
// Build: g++ -O3 -std=c++17 -pthread -o comp_pairs comp_pairs.cpp
#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <set>
#include <thread>
#include <vector>
using namespace std;

static const long double PI_L = 3.14159265358979323846264338327950288L;

int main(int argc, char** argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s P Q m [threads] [admissible_out]\n", argv[0]); return 2; }
    const int P = atoi(argv[1]), Q = atoi(argv[2]), m = atoi(argv[3]);
    const int nthreads = argc > 4 ? atoi(argv[4]) : 3;
    const char* outpath = argc > 5 ? argv[5] : nullptr;
    const int L = P * Q;
    if ((P - 1) % m) { fprintf(stderr, "m must divide P-1\n"); return 2; }
    // primitive root
    int g = 0;
    for (int c = 2; c < P && !g; c++) {
        int x = 1, ord = 0;
        do { x = x * c % P; ord++; } while (x != 1);
        if (ord == P - 1) g = c;
    }
    int h = 1;
    for (int i = 0; i < (P - 1) / m; i++) h = h * g % P;
    vector<int> U;
    for (int i = 0, x = 1; i < m; i++, x = x * h % P) U.push_back(x);
    vector<int> cos_of(P, -1);
    vector<vector<int>> cosets;
    for (int r = 1; r < P; r++)
        if (cos_of[r] < 0) {
            vector<int> c;
            for (int u : U) { int y = r * u % P; cos_of[y] = (int)cosets.size(); c.push_back(y); }
            cosets.push_back(c);
        }
    const int k = (int)cosets.size();
    // frequency / shift representatives: orbits of <U_m, -1> on nonzero residues
    vector<int> rep;
    {
        vector<char> seen(P, 0);
        for (int t = 1; t < P; t++)
            if (!seen[t]) {
                rep.push_back(t);
                for (int u : U) { seen[t * u % P] = 1; seen[(P - t * u % P) % P] = 1; }
            }
    }
    const int F = (int)rep.size();
    const double PSDMAX = 2.0 * L + 2.0, LIM = PSDMAX + 1e-6;
    const int PARS = 2 * L + 2 - 2 * Q;  // sum c^2 + sum d^2
    const int LAM = -2 * Q;
    // Gauss periods E[i][f]
    vector<double> Ere(k * F), Eim(k * F);
    for (int i = 0; i < k; i++)
        for (int f = 0; f < F; f++) {
            long double re = 0, im = 0;
            for (int r : cosets[i]) {
                long double a = 2 * PI_L * (long double)(r * rep[f] % P) / P;
                re += cosl(a);
                im += sinl(a);
            }
            Ere[i * F + f] = (double)re;
            Eim[i * F + f] = (double)im;
        }
    vector<int> vals;
    for (int v = -Q; v <= Q; v += 2) vals.push_back(v);
    const int NV = (int)vals.size();
    // admissible c_0 values: (1 - c0) = m * S with S == k (mod 2) and |S| <= k*Q
    vector<pair<int, int>> c0S;
    for (int c0 : vals) {
        if ((1 - c0) % m) continue;
        int S = (1 - c0) / m;
        if (((S - k * Q) % 2) != 0 || abs(S) > k * Q) continue;
        c0S.push_back({c0, S});
    }
    const int minpart = 1 + m * k;  // smallest possible sum d^2 (all entries +-1)
    printf("P=%d Q=%d m=%d cosets k=%d freq_reps F=%d c0 options:", P, Q, m, k, F);
    for (auto& p : c0S) printf(" %d", p.first);
    printf("\n");
    fflush(stdout);
    const int k1 = k / 2, k2 = k - k1;
    auto enumerate_half = [&](int off, int kk, vector<int>& sum, vector<int>& sq, vector<double>& D,
                              vector<long long>& code) {
        long long N = 1;
        for (int i = 0; i < kk; i++) N *= NV;
        sum.resize(N);
        sq.resize(N);
        D.resize(N * 2 * F);
        code.resize(N);
        for (long long c = 0; c < N; c++) {
            long long t = c;
            int s = 0, q = 0;
            double* d = &D[c * 2 * F];
            for (int f = 0; f < 2 * F; f++) d[f] = 0;
            for (int i = 0; i < kk; i++) {
                int v = vals[t % NV];
                t /= NV;
                s += v;
                q += v * v;
                for (int f = 0; f < F; f++) {
                    d[2 * f] += v * Ere[(off + i) * F + f];
                    d[2 * f + 1] += v * Eim[(off + i) * F + f];
                }
            }
            sum[c] = s;
            sq[c] = q;
            code[c] = c;
        }
    };
    vector<int> xs_sum, xs_sq, ys_sum, ys_sq;
    vector<double> xD, yD0;
    vector<long long> xcode, ycode0;
    enumerate_half(0, k1, xs_sum, xs_sq, xD, xcode);
    enumerate_half(k1, k2, ys_sum, ys_sq, yD0, ycode0);
    // sort Y by (sum, sq)
    const long long NY = (long long)ys_sum.size();
    vector<long long> yi(NY);
    for (long long i = 0; i < NY; i++) yi[i] = i;
    sort(yi.begin(), yi.end(), [&](long long a, long long b) {
        return ys_sum[a] != ys_sum[b] ? ys_sum[a] < ys_sum[b] : ys_sq[a] < ys_sq[b];
    });
    vector<int> ysum(NY), ysq(NY);
    vector<long long> ycode(NY);
    vector<double> yD(NY * 2 * F);
    for (long long q = 0; q < NY; q++) {
        ysum[q] = ys_sum[yi[q]];
        ysq[q] = ys_sq[yi[q]];
        ycode[q] = yi[q];
        memcpy(&yD[q * 2 * F], &yD0[yi[q] * 2 * F], sizeof(double) * 2 * F);
    }
    vector<double>().swap(yD0);
    map<int, pair<long long, long long>> yb;
    for (long long q = 0; q < NY;) {
        long long r = q;
        while (r < NY && ysum[r] == ysum[q]) r++;
        yb[ysum[q]] = {q, r};
        q = r;
    }
    const long long NX = (long long)xs_sum.size();
    atomic<long long> nx(0);
    vector<vector<vector<int>>> surv(nthreads);
    vector<unsigned long long> examined(nthreads, 0);
    auto worker = [&](int tid) {
        for (;;) {
            long long x = nx.fetch_add(1);
            if (x >= NX) break;
            const double* dx = &xD[x * 2 * F];
            for (auto& cs : c0S) {
                int c0 = cs.first;
                auto it = yb.find(cs.second - xs_sum[x]);
                if (it == yb.end()) continue;
                int sqmax = (PARS - minpart - c0 * c0);  // need m*(sqx+sqy) <= sqmax
                for (long long q = it->second.first; q < it->second.second; q++) {
                    if (m * (xs_sq[x] + ysq[q]) > sqmax) break;  // sorted by sq
                    examined[tid]++;
                    const double* d = &yD[q * 2 * F];
                    bool ok = true;
                    for (int f = 0; f < F; f++) {
                        double re = c0 + dx[2 * f] + d[2 * f], im = dx[2 * f + 1] + d[2 * f + 1];
                        if (re * re + im * im > LIM) { ok = false; break; }
                    }
                    if (!ok) continue;
                    vector<int> c(k + 1);
                    c[0] = c0;
                    long long t = xcode[x];
                    for (int i = 0; i < k1; i++) { c[1 + i] = vals[t % NV]; t /= NV; }
                    t = ycode[q];
                    for (int i = 0; i < k2; i++) { c[1 + k1 + i] = vals[t % NV]; t /= NV; }
                    surv[tid].push_back(c);
                }
            }
        }
    };
    {
        vector<thread> th;
        for (int t = 0; t < nthreads; t++) th.emplace_back(worker, t);
        for (auto& t : th) t.join();
    }
    vector<vector<int>> S;
    unsigned long long ex = 0;
    for (int t = 0; t < nthreads; t++) {
        ex += examined[t];
        S.insert(S.end(), surv[t].begin(), surv[t].end());
    }
    sort(S.begin(), S.end());
    printf("examined (Parseval-feasible) c vectors: %llu, PSD survivors: %zu\n", ex, S.size());
    // exact PAF keys: (PAF(0), PAF(rep_1), ..., PAF(rep_F))
    map<vector<int>, vector<int>> bykey;  // key -> indices
    vector<vector<int>> keys(S.size());
    for (size_t i = 0; i < S.size(); i++) {
        vector<int> full(P);
        full[0] = S[i][0];
        for (int r = 1; r < P; r++) full[r] = S[i][1 + cos_of[r]];
        int sumc = 0;
        for (int r = 0; r < P; r++) sumc += full[r];
        if (sumc != 1) { fprintf(stderr, "sum check failed\n"); return 3; }
        vector<int> key(F + 1);
        for (int f = 0; f <= F; f++) {
            int s = f == 0 ? 0 : rep[f - 1], acc = 0;
            for (int r = 0; r < P; r++) acc += full[r] * full[(r + s) % P];
            key[f] = acc;
        }
        keys[i] = key;
        bykey[key].push_back((int)i);
    }
    printf("distinct PAF keys: %zu\n", bykey.size());
    size_t pairs = 0;
    set<int> adm;
    for (size_t i = 0; i < S.size(); i++) {
        vector<int> w(F + 1);
        w[0] = PARS - keys[i][0];
        for (int f = 1; f <= F; f++) w[f] = LAM - keys[i][f];
        auto it = bykey.find(w);
        if (it == bykey.end()) continue;
        pairs += it->second.size();
        adm.insert((int)i);
    }
    printf("ordered compressed pairs (c,d): %zu, admissible c vectors: %zu\n", pairs, adm.size());
    FILE* fo = outpath ? fopen(outpath, "w") : nullptr;
    for (int i : adm) {
        if (fo) {
            for (int j = 0; j <= k; j++) fprintf(fo, "%d%c", S[i][j], j == k ? '\n' : ' ');
        }
    }
    if (fo) fclose(fo);
    // print cosets (so the coset order of the output is reproducible)
    printf("coset order:");
    for (auto& c : cosets) printf(" {%d..}", c[0]);
    printf("\nRESULT P=%d Q=%d m=%d survivors=%zu pairs=%zu admissible=%zu\n", P, Q, m, S.size(), pairs,
           adm.size());
    return 0;
}
