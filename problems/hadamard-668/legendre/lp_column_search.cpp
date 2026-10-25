// lp_column_search.cpp -- implementation 2: column-decomposition search for multiplier-
// invariant Legendre pairs of length L = 9 P (P an odd prime > 3; the target is P = 37).
//
// Coordinates: x in Z/LZ <-> (x mod 9, x mod P).  For a subgroup H of (Z/LZ)^* let H9, HP be
// its images mod 9 and mod P.  Every H-orbit lies in one "cell" (R, C), where R is an
// H9-orbit on Z/9 (a row class) and C is an HP-orbit on Z/P (a column class: {0} or a coset of
// HP in (Z/PZ)^*).  For an H-invariant sequence A:
//   * the P-compression c_beta = sum_{x = beta mod P} A(x) equals the weighted column sum
//     s_C = sum_{O in column C} eps_O |O| / |C|  (beta in C);
//   * the 9-compression a_alpha = sum_{x = alpha mod 9} A(x) equals the weighted row sum
//     r_R = sum_{O in row R} eps_O |O| / |R|  (alpha in R).
// For a Legendre pair (A, B) the compressions satisfy exact equations, so c must be an
// admissible P-compression (listed in c_file, produced by comp_pairs) and either
//   mode a9: a must be an admissible 9-compression (listed in a_file), or
//   mode u3: the 3-compression (u, v, w) must satisfy u + v + w = 1 and
//            N(u + v w3 + w w3^2) + N(u' + v' w3 + w' w3^2) = 2L + 2 for attainable (u',v',w')
//            (targets recomputed here independently of lp_orbit_search), or
//   mode a111: the 3-compression A'(y) = A(y) + A(y+L/3) + A(y+2L/3) (length L/3) must be one of
//            the admissible compressions in a_file (output of lp_comp111); the key is the vector of
//            A'-values on the orbits of H mod L/3 (each such orbit lies over a single column).
// Search: for each admissible c, enumerate per column the sign patterns with the required
// column sum, split the columns into two groups, and meet in the middle keyed by the exact
// row-sum data.  Then the floating-point PSD filter (reject only if PSD > 2L+2+1e-6) at one
// frequency per <H,-1>-orbit, exact integer PAF keys for survivors (direct int arithmetic),
// and an exact hash-based complement search over the survivors of all c targets.
//
// Usage: lp_column_search P gens c_file mode(a9|u3|a111) a_file|- [threads] [surv_out|-] [pairs_out]
// Build: g++ -O3 -std=c++17 -pthread -o lp_column_search lp_column_search.cpp
#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>
using namespace std;

static const long double PI_L = 3.14159265358979323846264338327950288L;

struct Pattern {
    uint64_t mask;      // global orbit bits set to 1 = sign -1
    vector<int> rows;   // contribution to each row-class sum
};

static vector<vector<int>> read_rows(const string& path) {
    vector<vector<int>> out;
    ifstream in(path);
    string line;
    while (getline(in, line)) {
        stringstream ss(line);
        vector<int> v;
        int t;
        while (ss >> t) v.push_back(t);
        if (!v.empty()) out.push_back(v);
    }
    return out;
}

int main(int argc, char** argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s P gens c_file a9|u3|a111 a_file|- [threads] [surv_out|-] [pairs_out]\n", argv[0]);
        return 2;
    }
    const int P = atoi(argv[1]);
    const int L = 9 * P;
    const string mode = argv[4];
    const int nthreads = argc > 6 ? atoi(argv[6]) : 3;
    const string surv_out = argc > 7 ? argv[7] : "-";
    const char* pairs_out = argc > 8 ? argv[8] : nullptr;
    if (mode != "a9" && mode != "u3" && mode != "a111") { fprintf(stderr, "mode must be a9, u3 or a111\n"); return 2; }

    // ---- subgroup ----
    vector<long long> gens;
    {
        stringstream ss(argv[2]);
        string t;
        while (getline(ss, t, ',')) gens.push_back(((stoll(t) % L) + L) % L);
    }
    set<int> Hs = {1};
    {
        vector<int> todo = {1};
        while (!todo.empty()) {
            int x = todo.back();
            todo.pop_back();
            for (long long g : gens) {
                if (std::gcd((long long)L, g) != 1) { fprintf(stderr, "non-unit generator\n"); return 2; }
                int y = (int)(x * g % L);
                if (!Hs.count(y)) { Hs.insert(y); todo.push_back(y); }
            }
        }
    }
    vector<int> H(Hs.begin(), Hs.end());
    // ---- orbits (computed by BFS, independent of lp_orbit_search) ----
    vector<int> orbit_of(L, -1);
    vector<vector<int>> orbits;
    for (int x = 0; x < L; x++) {
        if (orbit_of[x] >= 0) continue;
        set<int> o;
        for (int h : H) o.insert((int)((long long)h * x % L));
        for (int y : o) orbit_of[y] = (int)orbits.size();
        orbits.push_back(vector<int>(o.begin(), o.end()));
    }
    const int n = (int)orbits.size();
    if (n > 64) { fprintf(stderr, "n=%d > 64 orbits not supported\n", n); return 2; }
    // ---- row classes (H9-orbits on Z/9) and column classes (HP-orbits on Z/P) ----
    vector<int> row_of(9, -1);
    vector<vector<int>> rowcls;
    for (int a = 0; a < 9; a++)
        if (row_of[a] < 0) {
            set<int> r;
            for (int h : H) r.insert(h % 9 * a % 9);
            for (int y : r) row_of[y] = (int)rowcls.size();
            rowcls.push_back(vector<int>(r.begin(), r.end()));
        }
    vector<int> col_of(P, -1);
    vector<vector<int>> colcls;  // colcls[0] = {0}, then cosets ordered by minimal element
    for (int b = 0; b < P; b++)
        if (col_of[b] < 0) {
            set<int> c;
            for (int h : H) c.insert(h % P * b % P);
            for (int y : c) col_of[y] = (int)colcls.size();
            colcls.push_back(vector<int>(c.begin(), c.end()));
        }
    const int NR = (int)rowcls.size(), NC = (int)colcls.size();
    // ---- cells and weights ----
    vector<int> orow(n), ocol(n), wrow(n), wcol(n);
    for (int j = 0; j < n; j++) {
        orow[j] = row_of[orbits[j][0] % 9];
        ocol[j] = col_of[orbits[j][0] % P];
        for (int x : orbits[j])
            if (row_of[x % 9] != orow[j] || col_of[x % P] != ocol[j]) { fprintf(stderr, "cell error\n"); return 3; }
        int sz = (int)orbits[j].size();
        if (sz % rowcls[orow[j]].size() || sz % colcls[ocol[j]].size()) { fprintf(stderr, "weight error\n"); return 3; }
        wrow[j] = sz / (int)rowcls[orow[j]].size();
        wcol[j] = sz / (int)colcls[ocol[j]].size();
    }
    // ---- orbits of H mod M (M = L/3) on Z/M, for mode a111 ----
    const int M = L / 3;
    vector<int> orbM(M, -1), mo(n), wmo(n);
    vector<int> mrep;
    for (int y = 0; y < M; y++)
        if (orbM[y] < 0) {
            for (int h : H) orbM[(int)((long long)h * y % M)] = (int)mrep.size();
            mrep.push_back(y);
        }
    const int nM = (int)mrep.size();
    {
        vector<int> msize(nM, 0);
        for (int y = 0; y < M; y++) msize[orbM[y]]++;
        for (int j = 0; j < n; j++) {
            mo[j] = orbM[orbits[j][0] % M];
            for (int x : orbits[j])
                if (orbM[x % M] != mo[j]) { fprintf(stderr, "M-orbit error\n"); return 3; }
            wmo[j] = (int)orbits[j].size() / msize[mo[j]];
        }
    }
    const int NK = mode == "a111" ? nM : NR;  // length of the per-pattern key data
    if (mode == "a111" && nM > 21) { fprintf(stderr, "a111 mode supports at most 21 orbits mod L/3\n"); return 2; }
    // ---- frequency reps (orbits of <H,-1> on nonzero residues) and orbit Gauss sums ----
    vector<int> freqs;
    {
        vector<char> seen(L, 0);
        for (int k = 1; k < L; k++) {
            if (seen[k]) continue;
            freqs.push_back(k);
            for (int h : H) {
                int y = (int)((long long)h * k % L);
                seen[y] = seen[L - y] = 1;
            }
        }
    }
    const int F = (int)freqs.size();
    const double LIM = 2.0 * L + 2 + 1e-6;
    vector<double> Gr((size_t)n * F), Gi((size_t)n * F);
    for (int j = 0; j < n; j++)
        for (int f = 0; f < F; f++) {
            long double re = 0, im = 0;
            for (int x : orbits[j]) {
                long double ang = 2 * PI_L * (long double)((long long)freqs[f] * x % L) / L;
                re += cosl(ang);
                im += sinl(ang);
            }
            Gr[(size_t)j * F + f] = (double)re;
            Gi[(size_t)j * F + f] = (double)im;
        }
    {  // check the most selective frequencies first: sort by decreasing sum_j |G_j(f)|^2
        vector<pair<double, int>> var(F);
        for (int f = 0; f < F; f++) {
            double v = 0;
            for (int j = 0; j < n; j++)
                v += Gr[(size_t)j * F + f] * Gr[(size_t)j * F + f] + Gi[(size_t)j * F + f] * Gi[(size_t)j * F + f];
            var[f] = {-v, f};
        }
        sort(var.begin(), var.end());
        vector<double> r2(Gr.size()), i2(Gi.size());
        for (int j = 0; j < n; j++)
            for (int f = 0; f < F; f++) {
                r2[(size_t)j * F + f] = Gr[(size_t)j * F + var[f].second];
                i2[(size_t)j * F + f] = Gi[(size_t)j * F + var[f].second];
            }
        Gr.swap(r2);
        Gi.swap(i2);
    }
    // ---- key targets ----
    // key = row-sum vector (a9) or 3-compression (u3); packed with offset 128, 8 bits each
    auto rows_to_key = [&](const vector<int>& r) -> vector<int> {
        if (mode == "a9" || mode == "a111") return r;
        int u = 0, v = 0, w = 0;
        for (int R = 0; R < NR; R++)
            for (int a : rowcls[R]) {
                if (a % 3 == 0) u += r[R];
                else if (a % 3 == 1) v += r[R];
                else w += r[R];
            }
        return {u, v, w};
    };
    auto packk = [&](const vector<int>& k) -> uint64_t {
        uint64_t z = 0;
        if (mode == "a111") {  // 3 bits per component, values -3..3; UINT64_MAX = unrealizable
            for (int t : k) {
                if (t < -3 || t > 3) return UINT64_MAX;
                z = (z << 3) | (uint64_t)(t + 3);
            }
            return z;
        }
        for (int t : k) z = (z << 9) | (uint64_t)(t + 256);
        return z;
    };
    vector<vector<int>> targets;
    if (mode == "a9") {
        for (auto& a : read_rows(argv[5])) {
            if ((int)a.size() != 9) { fprintf(stderr, "a_file lines need 9 entries\n"); return 2; }
            vector<int> r(NR);
            bool ok = true;
            for (int R = 0; R < NR; R++) {
                r[R] = a[rowcls[R][0]];
                for (int al : rowcls[R]) ok = ok && a[al] == r[R];
            }
            if (ok) targets.push_back(r);  // targets not constant on row classes are unrealizable
        }
    } else if (mode == "a111") {
        for (auto& a : read_rows(argv[5])) {
            if ((int)a.size() != M) { fprintf(stderr, "a_file lines need %d entries\n", M); return 2; }
            vector<int> r(nM);
            for (int k = 0; k < nM; k++) r[k] = a[mrep[k]];
            for (int y = 0; y < M; y++)
                if (a[y] != r[orbM[y]]) { fprintf(stderr, "a_file entry not invariant\n"); return 2; }
            targets.push_back(r);
        }
    } else {
        // u, v, w: sums of P*3 = L/3 signs each; norms attainable with u+v+w=1
        const int m3 = L / 3;
        set<long long> norms;
        vector<array<int, 3>> trip;
        for (int u = -m3; u <= m3; u += 2)
            for (int v = -m3; v <= m3; v += 2) {
                int w = 1 - u - v;
                if (abs(w) > m3 || (abs(w) % 2) != (m3 % 2)) continue;
                norms.insert((long long)u * u + (long long)v * v + (long long)w * w - (long long)u * v -
                             (long long)v * w - (long long)w * u);
                trip.push_back({u, v, w});
            }
        for (auto& t : trip) {
            long long N = (long long)t[0] * t[0] + (long long)t[1] * t[1] + (long long)t[2] * t[2] -
                          (long long)t[0] * t[1] - (long long)t[1] * t[2] - (long long)t[2] * t[0];
            if (norms.count(2LL * L + 2 - N)) targets.push_back({t[0], t[1], t[2]});
        }
    }
    vector<vector<int>> ctargets = read_rows(argv[3]);
    printf("L=%d gens=%s |H|=%zu n=%d rows=%d cols=%d F=%d mode=%s key_targets=%zu c_targets=%zu\n", L,
           argv[2], H.size(), n, NR, NC, F, mode.c_str(), targets.size(), ctargets.size());
    fflush(stdout);

    // ---- per-c-target search ----
    vector<uint64_t> allsurv;
    unsigned long long tot_examined = 0;
    for (size_t ci = 0; ci < ctargets.size(); ci++) {
        const vector<int>& c = ctargets[ci];
        if ((int)c.size() != NC) { fprintf(stderr, "c target has %zu entries, expected %d\n", c.size(), NC); return 2; }
        // column patterns
        vector<vector<Pattern>> colpat(NC);
        for (int C = 0; C < NC; C++) {
            vector<int> js;
            for (int j = 0; j < n; j++)
                if (ocol[j] == C) js.push_back(j);
            for (uint32_t s = 0; s < (1u << js.size()); s++) {
                int sum = 0;
                for (size_t i = 0; i < js.size(); i++) sum += ((s >> i) & 1 ? -1 : 1) * wcol[js[i]];
                if (sum != c[C]) continue;
                Pattern p;
                p.mask = 0;
                p.rows.assign(NK, 0);
                for (size_t i = 0; i < js.size(); i++) {
                    int sg = (s >> i) & 1 ? -1 : 1;
                    if (sg < 0) p.mask |= 1ULL << js[i];
                    if (mode == "a111") p.rows[mo[js[i]]] += sg * wmo[js[i]];
                    else p.rows[orow[js[i]]] += sg * wrow[js[i]];
                }
                colpat[C].push_back(p);
            }
        }
        // split columns into two groups with balanced pattern-count products
        vector<int> order(NC);
        iota(order.begin(), order.end(), 0);
        sort(order.begin(), order.end(), [&](int a, int b) { return colpat[a].size() > colpat[b].size(); });
        vector<int> G1, G2;
        double l1 = 0, l2 = 0;
        for (int C : order) {
            double lg = log((double)max<size_t>(1, colpat[C].size()));
            if (l1 <= l2) { G1.push_back(C); l1 += lg; } else { G2.push_back(C); l2 += lg; }
        }
        // X = smaller product, Y = larger product
        if (l1 > l2) swap(G1, G2);
        auto build = [&](const vector<int>& G, vector<uint64_t>& masks, vector<vector<int>>& rows) {
            masks.assign(1, 0);
            rows.assign(1, vector<int>(NK, 0));
            for (int C : G) {
                vector<uint64_t> nm;
                vector<vector<int>> nr;
                for (size_t q = 0; q < masks.size(); q++)
                    for (auto& p : colpat[C]) {
                        nm.push_back(masks[q] | p.mask);
                        vector<int> r = rows[q];
                        for (int R = 0; R < NK; R++) r[R] += p.rows[R];
                        nr.push_back(r);
                    }
                masks.swap(nm);
                rows.swap(nr);
            }
        };
        vector<uint64_t> xm, ym;
        vector<vector<int>> xr, yr;
        build(G1, xm, xr);
        build(G2, ym, yr);
        if (xm.empty() || ym.empty()) {
            printf("c#%zu: no column patterns\n", ci);
            continue;
        }
        // partial DFT of a configuration: only orbits in the group's columns contribute
        vector<char> in1(n, 0), in2(n, 0);
        for (int j = 0; j < n; j++) {
            in1[j] = find(G1.begin(), G1.end(), ocol[j]) != G1.end();
            in2[j] = find(G2.begin(), G2.end(), ocol[j]) != G2.end();
        }
        auto group_dft = [&](uint64_t mask, const vector<char>& inG, double* d) {
            for (int f = 0; f < 2 * F; f++) d[f] = 0;
            for (int j = 0; j < n; j++) {
                if (!inG[j]) continue;
                double s = (mask >> j & 1) ? -1.0 : 1.0;
                for (int f = 0; f < F; f++) {
                    d[2 * f] += s * Gr[(size_t)j * F + f];
                    d[2 * f + 1] += s * Gi[(size_t)j * F + f];
                }
            }
        };
        // Y configurations sorted by key, stored contiguously (masks + DFT at all F freqs)
        const size_t NYc = ym.size();
        vector<uint64_t> ykeys(NYc);
        for (size_t q = 0; q < NYc; q++) ykeys[q] = packk(rows_to_key(yr[q]));
        vector<uint32_t> yord(NYc);
        iota(yord.begin(), yord.end(), 0);
        sort(yord.begin(), yord.end(), [&](uint32_t a, uint32_t b) {
            return ykeys[a] != ykeys[b] ? ykeys[a] < ykeys[b] : a < b;
        });
        vector<uint64_t> ymS(NYc);
        vector<double> yD(NYc * 2 * F);
        unordered_map<uint64_t, pair<size_t, size_t>> yrange;
        for (size_t q = 0; q < NYc; q++) {
            ymS[q] = ym[yord[q]];
            group_dft(ymS[q], in2, &yD[q * 2 * F]);
            uint64_t kq = ykeys[yord[q]];
            auto it = yrange.find(kq);
            if (it == yrange.end()) yrange[kq] = {q, q + 1};
            else it->second.second = q + 1;
        }
        // group X configurations by key
        map<uint64_t, vector<uint32_t>> xgroups;
        for (size_t q = 0; q < xm.size(); q++) xgroups[packk(rows_to_key(xr[q]))].push_back((uint32_t)q);
        vector<pair<uint64_t, vector<uint32_t>*>> xg;
        for (auto& kv : xgroups) xg.push_back({kv.first, &kv.second});
        atomic<size_t> next(0);
        vector<unsigned long long> exam(nthreads, 0);
        vector<vector<uint64_t>> surv(nthreads);
        auto worker = [&](int tid) {
            vector<double> dx(2 * F);
            vector<pair<size_t, size_t>> ranges;
            for (;;) {
                size_t g = next.fetch_add(1);
                if (g >= xg.size()) break;
                const vector<int> kx = rows_to_key(xr[(*xg[g].second)[0]]);
                ranges.clear();
                for (auto& t : targets) {
                    vector<int> ky(t.size());
                    bool ok = true;
                    for (size_t i = 0; i < t.size(); i++) {
                        ky[i] = t[i] - kx[i];
                        if (ky[i] < -255 || ky[i] > 255) ok = false;
                    }
                    if (!ok) continue;
                    auto it = yrange.find(packk(ky));
                    if (it != yrange.end()) ranges.push_back(it->second);
                }
                if (ranges.empty()) continue;
                for (uint32_t xq : *xg[g].second) {
                    group_dft(xm[xq], in1, dx.data());
                    for (auto& rg : ranges) {
                        exam[tid] += rg.second - rg.first;
                        for (size_t yq = rg.first; yq < rg.second; yq++) {
                            const double* d = &yD[yq * 2 * F];
                            int f = 0;
                            for (; f < F; f++) {
                                double re = dx[2 * f] + d[2 * f], im = dx[2 * f + 1] + d[2 * f + 1];
                                if (re * re + im * im > LIM) break;
                            }
                            if (f == F) surv[tid].push_back(xm[xq] | ymS[yq]);
                        }
                    }
                }
            }
        };
        vector<thread> th;
        for (int t = 0; t < nthreads; t++) th.emplace_back(worker, t);
        for (auto& t : th) t.join();
        unsigned long long ex = 0;
        size_t sv = 0;
        for (int t = 0; t < nthreads; t++) {
            ex += exam[t];
            sv += surv[t].size();
            allsurv.insert(allsurv.end(), surv[t].begin(), surv[t].end());
        }
        tot_examined += ex;
        printf("c#%zu [", ci);
        for (int v : c) printf(" %d", v);
        printf(" ] X=%zu Y=%zu examined=%llu survivors=%zu\n", xm.size(), ym.size(), ex, sv);
        fflush(stdout);
    }
    sort(allsurv.begin(), allsurv.end());
    size_t before = allsurv.size();
    allsurv.erase(unique(allsurv.begin(), allsurv.end()), allsurv.end());
    if (allsurv.size() != before) { fprintf(stderr, "duplicate survivors?!\n"); return 3; }
    printf("total examined=%llu survivors=%zu\n", tot_examined, allsurv.size());
    if (surv_out != "-") {
        FILE* fs = fopen(surv_out.c_str(), "w");
        for (uint64_t s : allsurv) fprintf(fs, "%llu\n", (unsigned long long)s);
        fclose(fs);
    }
    // ---- exact PAF keys (direct integer arithmetic) and hash complement search ----
    vector<int> sreps = freqs;  // shift reps: same <H,-1>-orbit representatives
    auto seq_of = [&](uint64_t mask, vector<int>& A) {
        for (int x = 0; x < L; x++) A[x] = (mask >> orbit_of[x] & 1) ? -1 : 1;
    };
    unordered_map<string, vector<uint32_t>> bykey;
    vector<string> keys(allsurv.size());
    {
        vector<int> A(L);
        for (size_t i = 0; i < allsurv.size(); i++) {
            seq_of(allsurv[i], A);
            string k;
            for (int s : sreps) {
                int p = 0;
                for (int x = 0; x < L; x++) p += A[x] * A[(x + s) % L];
                k += to_string(p) + ",";
            }
            keys[i] = k;
            bykey[k].push_back((uint32_t)i);
        }
    }
    printf("distinct PAF keys=%zu\n", bykey.size());
    size_t pairs = 0;
    FILE* pf = pairs_out ? fopen(pairs_out, "w") : nullptr;
    {
        vector<int> A(L), B(L);
        for (size_t i = 0; i < allsurv.size(); i++) {
            // complement key: PAF_B(s) = -2 - PAF_A(s)
            string want;
            stringstream ss(keys[i]);
            string tok;
            while (getline(ss, tok, ',')) want += to_string(-2 - stoi(tok)) + ",";
            auto it = bykey.find(want);
            if (it == bykey.end()) continue;
            for (uint32_t j : it->second) {
                seq_of(allsurv[i], A);
                seq_of(allsurv[j], B);
                for (int s = 1; s < L; s++) {
                    int p = 0;
                    for (int x = 0; x < L; x++) p += A[x] * A[(x + s) % L] + B[x] * B[(x + s) % L];
                    if (p != -2) { fprintf(stderr, "verification failed?!\n"); return 4; }
                }
                pairs++;
                if (pf) {
                    for (int x = 0; x < L; x++) fputc(A[x] > 0 ? '+' : '-', pf);
                    fputc(' ', pf);
                    for (int x = 0; x < L; x++) fputc(B[x] > 0 ? '+' : '-', pf);
                    fputc('\n', pf);
                }
            }
        }
    }
    if (pf) fclose(pf);
    printf("RESULT L=%d gens=%s n=%d mode=%s c_targets=%zu examined=%llu survivors=%zu distinct_keys=%zu "
           "pairs=%zu\n",
           L, argv[2], n, mode.c_str(), ctargets.size(), tot_examined, allsurv.size(), bykey.size(), pairs);
    return 0;
}
