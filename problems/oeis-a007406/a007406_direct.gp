\\ OEIS A007406: direct check of the Eldar-Ordowski conjecture with exact
\\ rationals in PARI/GP (independent of the Python checker).
\\   gcd(n, a(n-1)) = n if n is prime, 1 otherwise, for 3 < n <= N,
\\ where a(m) = |numerator(sum_{k=1}^m 1/k^2)|.
\\ Usage:  echo 'check(10^5)' | gp -q -D parisizemax=2G a007406_direct.gp
check(N) =
{
  my(H = 0, bad = 0, t0 = getabstime());
  for (m = 1, N - 1,
    H += 1/m^2;
    my(n = m + 1);
    if (n > 3,
      my(g = gcd(numerator(H), n));
      if (g != if (isprime(n), n, 1),
        bad++;
        print("MISMATCH n=", n, " gcd=", g))));
  print("direct-gp: 3 < n <= ", N, ", mismatches=", bad,
        ", time=", getabstime() - t0, " ms");
  bad
}
