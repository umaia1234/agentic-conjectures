\\ OEIS A007406: independent PARI/GP recomputation of the Boyd-tree children of
\\ a root s (1 <= s < q) with v_q(H2(s)) = 2, for a prime q >= 5.
\\   H2(q s + r) = U(q s) + sum_{rho=1}^{r} (q s + rho)^-2 + H2(s) / q^2,
\\   U(q s) = sum_{j<P} (-1)^j (j+1) q^j F_j(s) A_{j+2}  (mod q^P),
\\ with A_t = sum_{rho=1}^{q-1} rho^-t and the power sums F_j(s) = sum_{i<s} i^j
\\ taken from Bernoulli polynomials (the Python checker uses Stirling numbers).
\\ Prints how many children have v_q = 0, 1 and >= 2 (the latter listed).
\\ Usage:  echo 'children(16843, 16842, 8)' | gp -q a007406_children.gp
children(q, s, P) =
{
  my(M = q^P, h, A, U, c, v, cnt = [0, 0, 0], deep = List(), t0 = getabstime());
  if (!isprime(q) || q < 5 || s < 1 || s >= q || P < 3, error("bad arguments"));
  h = lift(sum(k = 1, s, Mod(k, q^(P + 2))^-2));
  if (h % q^2 || !(h % q^3), error("v_q(H2(s)) is not 2"));
  A = vector(P + 1, t, Mod(0, M));
  for (rho = 1, q - 1,
    my(inv = Mod(rho, M)^-1, pw = inv^2);
    for (t = 2, P + 1, A[t] += pw; pw *= inv));
  U = sum(j = 0, P - 1,
    my(B = bernpol(j + 1), F = (subst(B, 'x, s) - subst(B, 'x, 0)) / (j + 1));
    (-1)^j * (j + 1) * q^j * F * A[j + 2]);
  c = U + Mod(h / q^2, M);
  for (r = 0, q - 1,
    if (r, c += Mod(q * s + r, M)^-2);
    v = if (lift(c), valuation(lift(c), q), P);
    if (v >= 2, listput(deep, [q * s + r, v]));
    cnt[min(v, 2) + 1]++);
  print("children-gp q=", q, " s=", s, " P=", P, ": v=0: ", cnt[1], ", v=1: ", cnt[2],
        ", v>=2: ", Vec(deep), " (", getabstime() - t0, " ms)");
}
