def bits(n, L):
    return [(n >> i) & 1 for i in range(L)]


def occurrences(n):
    L = n.bit_length()
    z = n*n
    return [s for s in range(z.bit_length()-L+1)
            if ((z >> s) & ((1 << L)-1)) == n]


def periodic(n, L, d):
    b = bits(n, L)
    return all(b[i] == b[i+d] for i in range(L-d))


def generated(L, d):
    r = L % d
    q = L // d
    required = 1 | (1 << ((L-1) % d))
    out = set()
    for u in range(1 << d):
        if (u & required) != required:
            continue
        n = sum(u << (j*d) for j in range(q))
        if r:
            n += (u & ((1 << r)-1)) << (q*d)
        out.add(n)
    return out


for L in range(5, 15):
    odd_words = range((1 << (L-1)) | 1, 1 << L, 2)
    for d in range(1, L-3):
        brute = {n for n in odd_words if periodic(n, L, d)}
        assert brute == generated(L, d), (L, d, brute ^ generated(L, d))

for n in range(1, 1_000_000):
    os = occurrences(n)
    assert len(os) <= 1, (n, os)
    v = (n & -n).bit_length()-1
    m = n >> v
    if v and os:
        mos = occurrences(m)
        assert all(s-v in mos for s in os), (n, os, m, mos)

print("audit ok: generator equality for L<=14; direct/even reduction for n<1,000,000")
