// lp_comp111.cpp -- exhaustive search for H-invariant 3-compressed Legendre pairs (implementation 1).
//
// Let (A, B) be a Legendre pair of length L = 9P (here L = 333, P = 37) with sum(A) = sum(B) = 1,
// both constant on the orbits of a multiplier group H <= (Z/LZ)^*.  With M = L/3 the
// 3-compressions A'(y) = A(y) + A(y+M) + A(y+2M) (y in Z/M) satisfy exactly
//   PAF_A'(s) + PAF_B'(s) = -6 (s != 0 mod M),  PAF_A'(0) + PAF_B'(0) = 2L - 4,
// because PAF_A'(s) is the sum of PAF_A(t) over the three t = s (mod M).  Moreover
//   * A' is invariant under H mod M, and A'(y) can only take the values sum_i +-|f_i|, where
//     f_1, f_2, ... are the parts of the fibre {y, y+M, y+2M} cut out by the H-orbits of Z/L
//     (if H permutes the fibre transitively, A'(y) = +-3);
//   * the P-compression of A' equals the P-compression c of A, which must be one of the
//     admissible compressions in c_file (lists produced and cross-checked by comp_pairs.cpp and
//     comp37_exact.py);
//   * sum A'^2 <= 2L - 4 - M (every B'(y) is odd, so sum B'^2 >= M);
//   * the 3-compression (u, v, w) of A' has Eisenstein norm n with 2L + 2 - n also the norm of
//     an admissible triple (the Legendre identity at frequency L/3);
//   * PSD_A'(k) = PSD_A(3k) <= 2L + 2 for k != 0 (mod M) (floating-point filter with
//     tolerance 1e-6; the rounding error is below 1e-9, so it never rejects a valid A').
// Every A' passing these filters is kept; exact integer PAF vectors at ALL M shifts are then
// matched (key_A' + key_B' = (2L - 4, -6, ..., -6)).  A' is "admissible" if it has a partner.
// An empty admissible set excludes every Legendre pair with both members H-invariant.
//
// Usage: lp_comp111 L gens c_file [admissible_out]
//   gens: comma-separated generators of H (mod L); c_file: one P-compression per line in the
//   format "c_0 x_1 ... x_k" (x_i = value on the i-th (H mod P)-orbit of (Z/P)^*, orbits ordered
//   by least element).
// Build: g++ -O2 -std=c++17 -o lp_comp111 lp_comp111.cpp
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;

static const long double PI_L = 3.14159265358979323846264338327950288L;

int main(int argc, char** argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: %s L gens c_file [admissible_out]\n", argv[0]);
        return 2;
    }
    const int L = atoi(argv[1]);
    if (L % 9 != 0 || L % 2 == 0) { fprintf(stderr, "L must be odd and divisible by 9\n"); return 2; }
    const int M = L / 3, P = L / 9;
    vector<long long> gens;
    {
        stringstream ss(argv[2]);
        string t;
        while (getline(ss, t, ',')) gens.push_back(((stoll(t) % L) + L) % L);
    }
    // ---- H as a set of residues mod L ----
    vector<char> inH(L, 0);
    vector<int> H = {1};
    inH[1] = 1;
    for (size_t i = 0; i < H.size(); i++)
        for (long long g : gens) {
            if (std::gcd((long long)L, g) != 1) { fprintf(stderr, "non-unit generator\n"); return 2; }
            int y = (int)(H[i] * g % L);
            if (!inH[y]) { inH[y] = 1; H.push_back(y); }
        }
    // ---- H-orbit labels on Z/L ----
    vector<int> orbL(L, -1);
    int nL = 0;
    for (int x = 0; x < L; x++)
        if (orbL[x] < 0) {
            for (int h : H) orbL[(int)((long long)h * x % L)] = nL;
            nL++;
        }
    // ---- orbits of H mod M on Z/M, allowed values from the fibre partition ----
    vector<int> orbM(M, -1);
    vector<vector<int>> orbs;
    for (int y = 0; y < M; y++)
        if (orbM[y] < 0) {
            set<int> o;
            for (int h : H) o.insert((int)((long long)h * y % M));
            for (int z : o) orbM[z] = (int)orbs.size();
            orbs.push_back(vector<int>(o.begin(), o.end()));
        }
    const int n = (int)orbs.size();
    vector<vector<int>> vals(n);
    for (int k = 0; k < n; k++) {
        int y = orbs[k][0];
        map<int, int> part;  // H-orbit label -> number of fibre points in it
        for (int i = 0; i < 3; i++) part[orbL[y + i * M]]++;
        set<int> v = {0};
        for (auto& pr : part) {
            set<int> nv;
            for (int a : v) { nv.insert(a + pr.second); nv.insert(a - pr.second); }
            v = nv;
        }
        vals[k] = vector<int>(v.begin(), v.end());
    }
    // ---- column classes: orbits of H mod P on Z/P, ordered by least element ----
    vector<int> colOf(P, -1);
    vector<int> colSize;
    for (int r = 0; r < P; r++)
        if (colOf[r] < 0) {
            set<int> c;
            for (int h : H) c.insert((int)((long long)h * r % P));
            for (int z : c) colOf[z] = (int)colSize.size();
            colSize.push_back((int)c.size());
        }
    const int NC = (int)colSize.size();
    vector<vector<int>> colOrbs(NC);
    vector<int> wcol(n);
    for (int k = 0; k < n; k++) {
        int j = colOf[orbs[k][0] % P];
        colOrbs[j].push_back(k);
        wcol[k] = (int)orbs[k].size() / colSize[j];  // points of the orbit over each residue
    }
    // ---- admissible P-compressions ----
    vector<vector<int>> ctargets;
    {
        ifstream in(argv[3]);
        string line;
        while (getline(in, line)) {
            stringstream ss(line);
            vector<int> c;
            int v;
            while (ss >> v) c.push_back(v);
            if (c.empty()) continue;
            if ((int)c.size() != NC) { fprintf(stderr, "c target length %zu != %d\n", c.size(), NC); return 2; }
            ctargets.push_back(c);
        }
    }
    // ---- exact filters ----
    const int PARS = 2 * L - 4, LAM = -6, SQMAX = PARS - M;
    auto Nrm = [](long long a, long long b, long long c) { return a * a + b * b + c * c - a * b - b * c - c * a; };
    vector<char> allowedNorm(4 * (size_t)L * L + 1, 0);
    {
        const int m = L / 3;
        vector<char> isnorm(4 * (size_t)L * L + 1, 0);
        for (int pass = 0; pass < 2; pass++)
            for (int u = -m; u <= m; u += 2)
                for (int v = -m; v <= m; v += 2) {
                    int w = 1 - u - v;
                    if (w < -m || w > m || ((w - m) % 2) != 0) continue;
                    long long nn = Nrm(u, v, w);
                    if (pass == 0) { isnorm[nn] = 1; continue; }
                    long long co = 2LL * L + 2 - nn;
                    if (co >= 0 && isnorm[co]) allowedNorm[nn] = 1;
                }
    }
    // ---- frequency representatives (orbits of <H,-1> on nonzero residues mod M) ----
    vector<int> fr;
    {
        vector<char> seen(M, 0);
        for (int k = 1; k < M; k++)
            if (!seen[k]) {
                fr.push_back(k);
                for (int h : H) {
                    int y = (int)((long long)h * k % M);
                    seen[y] = seen[(M - y) % M] = 1;
                }
            }
    }
    const int F = (int)fr.size();
    const double LIM = 2.0 * L + 2.0 + 1e-6;
    vector<double> Gr((size_t)n * F), Gi((size_t)n * F);
    for (int k = 0; k < n; k++)
        for (int f = 0; f < F; f++) {
            long double re = 0, im = 0;
            for (int y : orbs[k]) {
                long double a = 2.0L * PI_L * (long double)((long long)fr[f] * y % M) / M;
                re += cosl(a);
                im += sinl(a);
            }
            Gr[(size_t)k * F + f] = (double)re;
            Gi[(size_t)k * F + f] = (double)im;
        }
    printf("L=%d gens=%s |H|=%zu M=%d orbits(H mod M)=%d columns=%d freq_reps=%d c_targets=%zu\n", L, argv[2],
           H.size(), M, n, NC, F, ctargets.size());
    {
        map<vector<int>, int> vc;
        for (int k = 0; k < n; k++) vc[vals[k]]++;
        printf("allowed value sets:");
        for (auto& pr : vc) {
            printf(" {");
            for (size_t i = 0; i < pr.first.size(); i++) printf(i ? ",%d" : "%d", pr.first[i]);
            printf("}x%d", pr.second);
        }
        printf("\n");
    }
    // ---- enumerate candidates column by column ----
    unsigned long long cand = 0, afterExact = 0;
    vector<vector<int>> surv;  // surviving A' as full sequences of length M
    for (auto& c : ctargets) {
        // per column: all value combos with the right weighted column sum
        vector<vector<vector<int>>> combos(NC);
        for (int j = 0; j < NC; j++) {
            const vector<int>& ks = colOrbs[j];
            vector<int> cur(ks.size());
            vector<size_t> idx(ks.size(), 0);
            for (;;) {
                int s = 0;
                for (size_t i = 0; i < ks.size(); i++) { cur[i] = vals[ks[i]][idx[i]]; s += wcol[ks[i]] * cur[i]; }
                if (s == c[j]) combos[j].push_back(cur);
                size_t i = 0;
                while (i < ks.size() && ++idx[i] == vals[ks[i]].size()) idx[i++] = 0;
                if (i == ks.size()) break;
            }
        }
        // per column combo: partial DFT, partial square sum, partial 3-compression
        struct Part { vector<double> d; int sq; int t[3]; };
        vector<vector<Part>> parts(NC);
        for (int j = 0; j < NC; j++)
            for (auto& cb : combos[j]) {
                Part p;
                p.d.assign(2 * F, 0.0);
                p.sq = 0;
                p.t[0] = p.t[1] = p.t[2] = 0;
                for (size_t i = 0; i < cb.size(); i++) {
                    int k = colOrbs[j][i];
                    for (int f = 0; f < F; f++) {
                        p.d[2 * f] += cb[i] * Gr[(size_t)k * F + f];
                        p.d[2 * f + 1] += cb[i] * Gi[(size_t)k * F + f];
                    }
                    for (int y : orbs[k]) { p.sq += cb[i] * cb[i]; p.t[y % 3] += cb[i]; }
                }
                parts[j].push_back(p);
            }
        unsigned long long tot = 1;
        for (int j = 0; j < NC; j++) tot *= parts[j].size();
        cand += tot;
        // odometer over the columns
        vector<size_t> ix(NC, 0);
        if (tot == 0) continue;
        vector<double> acc(2 * F);
        for (;;) {
            int sq = 0, t0 = 0, t1 = 0, t2 = 0;
            for (int j = 0; j < NC; j++) {
                const Part& p = parts[j][ix[j]];
                sq += p.sq; t0 += p.t[0]; t1 += p.t[1]; t2 += p.t[2];
            }
            if (sq <= SQMAX && allowedNorm[Nrm(t0, t1, t2)]) {
                afterExact++;
                for (int f = 0; f < 2 * F; f++) acc[f] = 0;
                for (int j = 0; j < NC; j++) {
                    const double* d = parts[j][ix[j]].d.data();
                    for (int f = 0; f < 2 * F; f++) acc[f] += d[f];
                }
                bool ok = true;
                for (int f = 0; f < F && ok; f++)
                    if (acc[2 * f] * acc[2 * f] + acc[2 * f + 1] * acc[2 * f + 1] > LIM) ok = false;
                if (ok) {
                    vector<int> seq(M);
                    for (int j = 0; j < NC; j++)
                        for (size_t i = 0; i < colOrbs[j].size(); i++)
                            for (int y : orbs[colOrbs[j][i]]) seq[y] = combos[j][ix[j]][i];
                    surv.push_back(seq);
                }
            }
            int j = 0;
            while (j < NC && ++ix[j] == parts[j].size()) ix[j++] = 0;
            if (j == NC) break;
        }
    }
    printf("candidates (column sums in c_file)=%llu  after Parseval+3-compression filters=%llu  PSD survivors=%zu\n",
           cand, afterExact, surv.size());
    // ---- exact PAF matching ----
    map<vector<int>, vector<int>> bykey;
    for (size_t i = 0; i < surv.size(); i++) {
        const vector<int>& a = surv[i];
        int s0 = 0;
        for (int y = 0; y < M; y++) s0 += a[y];
        if (s0 != 1) { fprintf(stderr, "sum error\n"); return 3; }
        vector<int> key(M);
        for (int s = 0; s < M; s++) {
            int acc = 0;
            for (int y = 0; y < M; y++) acc += a[y] * a[(y + s) % M];
            key[s] = acc;
        }
        bykey[key].push_back((int)i);
    }
    unsigned long long pairs = 0;
    set<int> adm;
    for (auto& kv : bykey) {
        vector<int> w(M);
        w[0] = PARS - kv.first[0];
        for (int s = 1; s < M; s++) w[s] = LAM - kv.first[s];
        auto it = bykey.find(w);
        if (it == bykey.end()) continue;
        pairs += (unsigned long long)kv.second.size() * it->second.size();
        for (int i : kv.second) adm.insert(i);
    }
    printf("distinct PAF vectors=%zu  ordered compressed pairs=%llu  admissible A'=%zu\n", bykey.size(), pairs,
           adm.size());
    if (argc > 4) {
        FILE* fo = fopen(argv[4], "w");
        vector<vector<int>> out;
        for (int i : adm) out.push_back(surv[i]);
        sort(out.begin(), out.end());
        for (auto& a : out) {
            for (int y = 0; y < M; y++) fprintf(fo, y ? " %d" : "%d", a[y]);
            fprintf(fo, "\n");
        }
        fclose(fo);
    }
    printf("RESULT L=%d gens=%s candidates=%llu psd_survivors=%zu ordered_pairs=%llu admissible=%zu\n", L, argv[2],
           cand, surv.size(), pairs, adm.size());
    return 0;
}
