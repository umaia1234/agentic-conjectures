#!/usr/bin/env python3
"""Independent checker for the certified OEIS A297707 previous-prime gaps.

For every record of a297707_gaps.jsonl with n in the requested range this
script re-derives, without trusting the generator:

1. a(n) = prod_{k=1}^{n-1} prod_{0 <= j <= (n-1)//k} (n - j*k), compared with
   the stored SHA-256 of its decimal expansion;
2. compositeness of every a(n) - h with 1 <= h < g(n):
   * h with a prime factor p <= n: p divides a(n) (p | n!), hence a(n) - h;
   * otherwise the stored witness: a factor q with 1 < q < a(n) - h and
     q | a(n) - h, or a Fermat base b with 1 < b < N = a(n) - h and
     b^(N-1) mod N != 1 (impossible for prime N by Fermat's little theorem);
   the witness lists must cover exactly these h;
3. primality of N = a(n) - g(n), by at least one of:
   * N < 3.3e24: deterministic Miller-Rabin with the 13 prime bases 2..41
     (Sorenson-Webster 2015: the least strong pseudoprime to all of them is
     3317044064679887385961981);
   * with --certs DIR: the PARI/GP ECPP certificate DIR/n<n>.gp (normally the
     one whose SHA-256 is recorded; a regenerated certificate is accepted
     if valid and reported as such) is checked by this script's own affine
     elliptic-curve arithmetic: for every step i, gcd(N_i, 6) = 1,
     t_i^2 < 4 N_i, m_i = N_i + 1 - t_i = s_i q_i, q_i > (N_i^(1/4) + 1)^2,
     gcd(4a^3 + 27b^2, N_i) = 1, [s_i]P_i is an affine point and
     [q_i]([s_i]P_i) = O, every inversion modulo N_i being valid (so the
     computation is the group law modulo each prime factor r of N_i, and
     [s_i]P_i mod r has order q_i <= #E(F_r) <= (r^(1/2) + 1)^2, which is
     impossible for a prime r <= N_i^(1/2)); q_i = N_{i+1}, and the last
     q_l < 2^64 is proved by the Miller-Rabin test above;
   * with --pari GP in addition: PARI's own primecertisvalid;
4. g(n) is 1 or prime (trial division), i.e. never composite.

A record counts as fully certified when steps 1-4 pass with a primality
proof in step 3; otherwise the endpoint is only re-tested as a base-2 strong
probable prime and reported as BPSW-only/unchecked.

Only the Python standard library is needed (gmpy2 is used for speed if it
is importable and --no-gmpy2 is not given).
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import math
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MPZ = int
POWMOD = pow
GCD = math.gcd


def a297707(n: int) -> int:
    terms = [n - j * k for k in range(1, n) for j in range((n - 1) // k + 1)]
    while len(terms) > 1:  # balanced product tree
        terms = [
            terms[i] * terms[i + 1] if i + 1 < len(terms) else terms[i]
            for i in range(0, len(terms), 2)
        ]
    return terms[0] if terms else 1


def primes_upto(m: int) -> list[int]:
    return [p for p in range(2, m + 1) if all(p % d for d in range(2, math.isqrt(p) + 1))]


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("ascii")).hexdigest()


MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
MR_LIMIT = 3_317_044_064_679_887_385_961_981


def strong_prp(m: int, b: int) -> bool:
    """Miller-Rabin round: m odd > b is a strong probable prime to base b."""
    d, s = m - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = POWMOD(b, d, m)
    if x == 1 or x == m - 1:
        return True
    for _ in range(s - 1):
        x = x * x % m
        if x == m - 1:
            return True
    return False


def is_prime_small(m: int) -> bool:
    """Deterministic for m < MR_LIMIT (Sorenson-Webster)."""
    assert m < MR_LIMIT
    if m < 2:
        return False
    for p in MR_BASES:
        if m % p == 0:
            return m == p
    return all(strong_prp(m, b) for b in MR_BASES)


def inv(x: int, mod: int) -> int:
    if GCD(x, mod) != 1:
        raise ValueError("non-invertible denominator")
    return POWMOD(x % mod, -1, mod)


def ec_add(p1, p2, a4: int, mod: int):
    """Affine group law modulo mod; raises if a case is not decided mod N."""
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if (x1 - x2) % mod == 0:
        if (y1 + y2) % mod == 0:
            return None
        if (y1 - y2) % mod != 0:
            raise ValueError("equal x, unrelated y")
        lam = (3 * x1 * x1 + a4) * inv(2 * y1, mod) % mod
    else:
        lam = (y2 - y1) * inv(x2 - x1, mod) % mod
    x3 = (lam * lam - x1 - x2) % mod
    return x3, (lam * (x1 - x3) - y1) % mod


def ec_mul(k: int, point, a4: int, mod: int):
    result = None
    for bit in bin(k)[2:]:
        result = ec_add(result, result, a4, mod)
        if bit == "1":
            result = ec_add(result, point, a4, mod)
    return result


def quartic_bound_ok(q: int, big_n: int) -> bool:
    """q > (N^(1/4) + 1)^2, using an upper bound for N^(1/4) to 2^-64."""
    k = 64
    x_hi = math.isqrt(math.isqrt(big_n << (4 * k))) + 1  # > N^(1/4) * 2^k
    return q << (2 * k) > (x_hi + (1 << k)) ** 2


def check_ecpp(cert, prime: int) -> int:
    if isinstance(cert, int):
        assert cert == prime and is_prime_small(prime)
        return 0
    expected = prime
    for entry in cert:
        big_n, t, s, a4 = (MPZ(v) for v in entry[:4])
        point = [MPZ(v) for v in entry[4]]
        assert big_n == expected and big_n > 1 and GCD(big_n, 6) == 1
        assert t * t < 4 * big_n and s > 0
        m = big_n + 1 - t
        assert m % s == 0
        q = m // s
        assert quartic_bound_ok(q, big_n), "q too small"
        x, y = point[0] % big_n, point[1] % big_n
        b4 = (y * y - x * x * x - a4 * x) % big_n
        assert GCD(4 * a4**3 + 27 * b4 * b4, big_n) == 1, "singular curve"
        sp = ec_mul(s, (x, y), a4, big_n)
        assert sp is not None, "[s]P = O"
        assert ec_mul(q, sp, a4, big_n) is None, "[m]P != O"
        expected = q
    assert expected < 2**64 and is_prime_small(int(expected))
    return len(cert)


def load_cert(path: Path):
    text = path.read_text().strip()
    return ast.literal_eval(text)


def gp_check(gp: str, path: Path, prime: int) -> None:
    script = (
        f'default(nbthreads, 1); C = read("{path}"); N = {prime};\n'
        'print(primecertisvalid(C) && if (type(C) == "t_INT", C == N, C[1][1] == N));\n'
    )
    out = subprocess.run(
        [gp, "-q", "-f", "-s", "1G"], input=script, capture_output=True, text=True, check=True
    ).stdout.strip()
    assert out == "1", f"primecertisvalid rejected {path}: {out}"


def verify_record(record: dict, certs: Path | None, gp: str | None) -> str:
    n, g = record["n"], record["g"]
    value = MPZ(a297707(n))
    assert sha256_text(str(value)) == record["a_sha256"], "a(n) hash mismatch"
    assert len(str(value)) == record["digits"]
    assert 1 <= g < value - 1
    prime = value - g
    assert sha256_text(str(prime)) == record["endpoint_sha256"]

    small = primes_upto(n)
    factor = {h: q for h, q in record["factor"]}
    fermat = {h: 2 for h in record["fermat2"]}
    for h, b in record["fermat_other"]:
        fermat[h] = b
    assert len(factor) + len(fermat) == record["admissible_below_g"]
    assert not set(factor) & set(fermat)
    for h in range(1, g):
        cand = value - h
        p = next((p for p in small if h % p == 0), None)
        if p is not None:
            assert cand % p == 0 and cand > p
            assert h not in factor and h not in fermat
        elif h in factor:
            q = factor.pop(h)
            assert 1 < q < cand and cand % q == 0, f"bad factor witness h={h}"
        else:
            b = fermat.pop(h)  # KeyError = missing witness
            assert 1 < b < cand and POWMOD(b, cand - 1, cand) != 1, f"bad Fermat h={h}"
    assert not factor and not fermat, "witnesses outside the gap"
    if g > 1:  # p | g with p <= n would put p | a(n) - g
        assert all(g % p for p in small)

    endpoint = record["endpoint"]
    proofs = []
    if prime < MR_LIMIT:
        assert is_prime_small(prime)
        proofs.append("miller-rabin")
    if endpoint["method"] == "ecpp-pari" and certs is not None:
        path = certs / Path(endpoint["cert_file"]).name
        same = hashlib.sha256(path.read_bytes()).hexdigest() == endpoint["cert_sha256"]
        steps = check_ecpp(load_cert(path), prime)
        assert steps == endpoint["cert_steps"] or not same
        # A regenerated certificate may differ byte-wise; it is checked all the same.
        proofs.append("ecpp" if same else "ecpp(regenerated certificate)")
        if gp:
            gp_check(gp, path, prime)
            proofs.append("primecertisvalid")
    if not proofs:  # unproved endpoint: only re-check that it is a probable prime
        assert strong_prp(prime, 2), "endpoint is not even a base-2 strong probable prime"
        return "ecpp-unchecked" if endpoint["method"] == "ecpp-pari" else "bpsw-only"
    assert g == 1 or all(g % d for d in range(2, math.isqrt(g) + 1)), "g composite"
    return "+".join(proofs)


def main() -> int:
    global MPZ, POWMOD, GCD
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--data", type=Path, default=HERE / "a297707_gaps.jsonl")
    parser.add_argument("--certs", type=Path, default=None, help="directory of n<n>.gp files")
    parser.add_argument("--pari", default=None, help="gp executable: also run primecertisvalid")
    parser.add_argument("--min-n", type=int, default=3)
    parser.add_argument("--max-n", type=int, default=10**9)
    parser.add_argument(
        "--require-certified-through",
        type=int,
        default=None,
        help="fail unless every 2 < n <= this bound is present and fully proved",
    )
    parser.add_argument("--no-gmpy2", action="store_true")
    args = parser.parse_args()
    sys.set_int_max_str_digits(0)
    if not args.no_gmpy2:
        try:
            import gmpy2

            MPZ, POWMOD, GCD = gmpy2.mpz, gmpy2.powmod, gmpy2.gcd
        except ImportError:
            pass

    proved: set[int] = set()
    unproved: list[int] = []
    for line in args.data.read_text().splitlines():
        record = json.loads(line)
        if not args.min_n <= record["n"] <= args.max_n:
            continue
        started = time.time()
        proof = verify_record(record, args.certs, args.pari)
        ok = proof not in ("bpsw-only", "ecpp-unchecked")
        (proved.add if ok else unproved.append)(record["n"])
        print(f"n={record['n']} g={record['g']} digits={record['digits']} {proof} "
              f"{time.time() - started:.1f}s", flush=True)
    bound = args.require_certified_through
    if bound is not None:
        missing = [n for n in range(max(3, args.min_n), bound + 1) if n not in proved]
        assert not missing, f"not certified: {missing}"
    print(f"OK: {len(proved)} records fully certified, {len(unproved)} with unproved endpoint"
          + (f" {unproved}" if unproved else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
