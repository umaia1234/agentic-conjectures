/* graph6 filter: "line" -> line graph, "prism" -> G x K2 (Cartesian), "k3" -> G x K3 (Cartesian).
   Input graphs n <= 62; output graphs must have <= 62 vertices (larger ones are skipped). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, A[64][64], N, B[64][64];
static int parse(const char *s) {
    if (*s == '>') return 0;
    n = s[0] - 63; if (n < 1 || n > 62) return 0;
    memset(A, 0, sizeof A);
    int k = 0, len = strlen(s);
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, k++) {
        int byte = 1 + k / 6, bit = 5 - k % 6; if (byte >= len) return 0;
        if (((s[byte] - 63) >> bit) & 1) A[i][j] = A[j][i] = 1;
    }
    return 1;
}
static void emit(void) {
    char out[4096]; int p = 0, k = 0, x = 0;
    out[p++] = 63 + N;
    for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
        x = (x << 1) | B[i][j]; k++;
        if (k == 6) { out[p++] = 63 + x; x = 0; k = 0; }
    }
    if (k) { x <<= (6 - k); out[p++] = 63 + x; }
    out[p] = 0; puts(out);
}
int main(int argc, char **argv) {
    char line[4096]; const char *mode = argv[1];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!parse(line)) continue;
        memset(B, 0, sizeof B);
        if (!strcmp(mode, "line")) {
            int eu[2048], ev[2048], m = 0;
            for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (A[i][j]) { eu[m] = i; ev[m] = j; m++; }
            if (m > 62) continue;
            N = m;
            for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++)
                if (eu[a] == eu[b] || eu[a] == ev[b] || ev[a] == eu[b] || ev[a] == ev[b]) B[a][b] = B[b][a] = 1;
        } else {
            int t = !strcmp(mode, "prism") ? 2 : 3;
            if (n * t > 62) continue;
            N = n * t;
            for (int a = 0; a < t; a++) for (int i = 0; i < n; i++) for (int j = 0; j < n; j++)
                if (A[i][j]) B[a * n + i][a * n + j] = 1;
            for (int i = 0; i < n; i++) for (int a = 0; a < t; a++) for (int b = a + 1; b < t; b++)
                B[a * n + i][b * n + i] = B[b * n + i][a * n + i] = 1;
        }
        emit();
    }
    return 0;
}
