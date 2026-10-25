\\ Independent PARI/GP re-check of the main steps of analyze_z_poly_y.py.
\\ Run from this directory:  gp -q crosscheck_z_poly_y.gp
\\ Needs PARI/GP (ellrank: version 2.15 or later); not run in CI.
\\
\\ Different normalisation from the Python script: Q = q*W with W monic and
\\ t = 1/q^2, so  y^4 - 4b - Q^2 = -q^2 (y-s)^m H^3  becomes
\\     W^2 - (y-s)^m H^3 = t*(y^4 - 4b),   t a nonzero rational square.
\\ The systems are rebuilt from scratch here and eliminated with PARI.

default(parisizemax, 2000000000);
NOK = 0; NEXPECTED = 38;
chk(c, msg) = if (c, NOK++; print("ok   ", msg), error(Str("FAIL: ", msg)));
isconst(f) = my(u = type(simplify(f))); f != 0 && (u == "t_INT" || u == "t_FRAC");
samefac(g, L) =
{
  my(F = factor(g)[, 1]);
  #F == #L && vecmin(vector(#L, i, vecmax(vector(#F, j, isconst(F[j] / L[i]))))) == 1;
}
\\ coefficients [y^4, y^3, y^2, y^1, y^0] of W^2 - (y-s)^m H^3 after the
\\ coefficients of y^(2d-1) .. y^5 have been used to fix W
resid(d, hv, m, s, W0) =
{
  my(h = #hv, H = y^h + sum(i = 1, h, hv[i] * y^(i - 1)), G = (y - s)^m * H^3);
  my(W = y^d + W0, c);
  forstep (k = 2*d - 1, 5, -1, c = polcoef(W^2 - G, k, y); W -= c / 2 * y^(k - d));
  c = W^2 - G;
  vector(5, i, polcoef(c, 5 - i, y));
}
ratroots(P) = Vec(nfroots(, P));   \\ rational roots, as a row vector
nocommon(L) = my(g = L[1]); for (i = 2, #L, g = gcd(g, L[i])); poldegree(g) == 0;

print("== deg A = 4 (a = 0): W^2 - (y-s)^2 H^3 = t(y^4-4b), H = y^2 + h1*y + h0");
{
  my(e, al, be, R2, R3, g, U, br);
  e = resid(4, [h0, h1], 2, 1, w0);
  chk(polcoef(e[1], 1, w0) == 2, "s=1: y^4 coefficient is 2*w0 + (...); trade w0 for t");
  e = apply(f -> subst(f, w0, (t - polcoef(e[1], 0, w0)) / 2), e);
  al = vector(3, i, polcoef(e[i + 1], 1, t)); be = vector(3, i, polcoef(e[i + 1], 0, t));
  chk(vecmax(vector(3, i, poldegree(e[i + 1], t))) == 1, "s=1: y^3, y^2, y^1 equations linear in t");
  R2 = al[1] * be[2] - al[2] * be[1]; R3 = al[1] * be[3] - al[3] * be[1];
  g = gcd(R2, R3);
  chk(samefac(g, [4*h0 - h1^2]), "s=1: gcd of the t-eliminants is c*(4h0-h1^2)^j");
  U = polresultant(R2 / g, R3 / g, h0);
  chk(U != 0 && ratroots(U) == [-2], "s=1: off that curve, the only rational h1 is -2");
  chk(isconst(subst(e[2], h1, -2) / t), "s=1, h1=-2: y^3 equation is (nonzero const)*t, so t=0");
  br = vector(3, i, subst(e[i + 1], h0, h1^2 / 4));
  chk(vecmax(vector(3, i, polcoef(br[i], 0, t) != 0)) == 0
      && nocommon(vector(3, i, polcoef(br[i], 1, t))),
      "s=1, on 4h0=h1^2: equations are t*gamma_i(h1) with no common root of the gamma_i");
  e = resid(4, [h0, h1], 2, 0, w0);
  e = apply(f -> subst(f, w0, (t - polcoef(e[1], 0, w0)) / 2), e);
  chk(isconst(e[2] / (h1 * ((4*h0 - h1^2)^2 + 64*t))),
      "s=0: y^3 equation = c*h1*((4h0-h1^2)^2 + 64t) with t > 0, so h1 = 0");
  chk(isconst(subst(e[3], h1, 0) / (h0 * (h0^2 + 12*t))),
      "s=0, h1=0: y^2 equation = c*h0*(h0^2 + 12t), so h0 = 0");
  chk(substvec(e[4], [h0, h1], [0, 0]) == 0
      && substvec(e[5], [h0, h1], [0, 0]) == t^2 / 4,
      "s=0, H=y^2: y^1 equation holds and y^0 coefficient is t^2/4 = -4bt, so t = -16b");
  foreach([-2, -3, 3], bv, chk(!issquare(-16 * bv), Str("s=0: t = -16b is not a square for b=", bv)));
}

print("== deg A = 5 (a = 0): W^2 - (y-s) H^3 = t(y^4-4b), H = y^3 + h2*y^2 + h1*y + h0");
{
  my(e, c, R12, R13, g, U, P3, r12, r13, sub, fac, Pb, cm, red, rr12, rr13);
  foreach([1, 0], s,
    e = resid(5, [h0, h1, h2], 1, s, 0);   \\ e[1] = t, e[2..4] must vanish
    c = vector(3, i, e[i + 1]);
    R12 = polresultant(c[1], c[2], h0); R13 = polresultant(c[1], c[3], h0);
    g = gcd(R12, R13);
    U = polresultant(R12 / g, R13 / g, h1);
    if (s == 1,
      chk(samefac(g, [4*h1 - h2^2 + 2*h2 + 3]), "s=1: gcd of h0-resultants is c*(4h1-h2^2+2h2+3)^j");
      chk(U != 0 && ratroots(U) == [-3], "s=1: off that curve, the only rational h2 is -3");
      P3 = apply(f -> subst(f, h2, -3), c);
      r12 = polresultant(P3[1], P3[2], h0); r13 = polresultant(P3[1], P3[3], h0);
      chk(r12 != 0 && r13 != 0 && ratroots(gcd(r12, r13)) == [3], "s=1, h2=-3: h1 = 3");
      chk(ratroots(gcd(gcd(subst(P3[1], h1, 3), subst(P3[2], h1, 3)), subst(P3[3], h1, 3))) == [-1],
          "s=1, (h1,h2)=(3,-3): h0 = -1");
      chk(substvec(e[1], [h0, h1, h2], [-1, 3, -3]) == 0, "s=1, H=(y-1)^3: t = 0, excluded");
      sub = (h2^2 - 2*h2 - 3) / 4; fac = 4*h0 + (h2 + 1)^2,
    \\ s = 0
      chk(samefac(g, [4*h1 - h2^2, 48*h1^2 - 72*h1*h2^2 + 23*h2^4]),
          "s=0: gcd of h0-resultants has factors 4h1-h2^2, 48h1^2-72h1h2^2+23h2^4");
      chk(!issquare(72^2 - 4*48*23), "s=0: second factor has only the rational point h1=h2=0");
      chk(U != 0 && ratroots(U) == [0], "s=0: off those curves, the only rational h2 is 0");
      P3 = apply(f -> subst(f, h2, 0), c);
      chk(isconst(P3[1] / (h0 * h1^2)) && isconst(subst(P3[2], h0, 0) / h1^4)
          && isconst(subst(P3[3], h1, 0) / h0^3), "s=0, h2=0: forces h0 = h1 = 0");
      chk(substvec(e[1], [h0, h1, h2], [0, 0, 0]) == 0, "s=0, H=y^3: t = 0, excluded");
      sub = h2^2 / 4; fac = h0);
    Pb = apply(f -> subst(f, h1, sub), c);
    cm = gcd(gcd(Pb[1], Pb[2]), Pb[3]);
    chk(samefac(cm, [fac]), Str("s=", s, ": on 4h1 = ", 4*sub, " the common factor is ", fac));
    red = apply(f -> f / cm, Pb);
    rr12 = polresultant(red[1], red[2], h0); rr13 = polresultant(red[1], red[3], h0);
    chk(rr12 != 0 && rr13 != 0 && poldegree(gcd(rr12, rr13)) == 0, "   off it: no common zero");
    chk(subst(subst(e[1], h1, sub), h0, polcoef(fac, 0, h0) / -polcoef(fac, 1, h0)) == 0,
        "   on it: t = 0, excluded");
  );
}

print("== deg A = 2 (a = 0): curves of C_b : k^2 = r^4 - 4b");
{
  my(E);
  E = ellinit([0, 0, 0, -48, 0]);
  chk(ellrank(E)[1..2] == [0, 0] && elltors(E)[1] == 2, "b=-3: E: Y^2=X^3-48X has rank 0, torsion Z/2");
  foreach([-2, 3], bv, E = ellinit([0, 0, 0, 16 * bv, 0]);
    chk(ellrank(E)[1] >= 1, Str("b=", bv, ": E: Y^2=X^3+(", 16 * bv, ")X has rank >= 1")));
}
{
  my(k2, Qs, P, lam, s, V, Vp, cubes, sq, n);
  k2 = r^4 - 4*b;
  \\ Q^2 for Q = k + (2r^3/k)(y-r) + (r^2(r^4-12b)/k^3)(y-r)^2, written with k^2 = k2
  Qs = k2 * (1 + 2*r^3 / k2 * (y - r) + r^2 * (r^4 - 12*b) / k2^2 * (y - r)^2)^2;
  P = y^4 - 4*b - Qs;
  chk(subst(P, y, r) == 0 && subst(deriv(P, y), y, r) == 0 && subst(deriv(deriv(P, y), y), y, r) == 0,
      "y^4-4b-Q^2 has a triple root at y = r");
  lam = polcoef(P, 4, y);
  s = -polcoef(P / (lam * (y - r)^3), 0, y);
  chk(P == lam * (y - r)^3 * (y - s), "y^4-4b-Q^2 = lam*(y-r)^3*(y-s)");
  V = substvec(T^9 * k2^3 * lam / 4 * (y - s), [r], [R / T]);
  chk(type(V) == "t_POL" && denominator(content(V)) == 1,
      "V = T^9 k^6 (lam/4)(y-s) is an integer polynomial in R, T, y, b");
  foreach([[-2, 13], [3, 9]], bm,
    n = 0; Vp = subst(V, b, bm[1]);
    cubes = Set(vector(bm[2], c, (c^3) % bm[2]));
    sq = Set(vector(bm[2], c, (c^2) % bm[2]));
    for (RR = 0, bm[2] - 1, for (TT = 0, bm[2] - 1,
      if ((bm[2] == 13 && RR == 0 && TT == 0) || (bm[2] == 9 && RR % 3 == 0 && TT % 3 == 0), next);
      if (!setsearch(sq, (RR^4 - 4 * bm[1] * TT^4) % bm[2]), next);
      for (YY = 0, bm[2] - 1, n++;
        if (setsearch(cubes, substvec(Vp, [R, T, y], [RR, TT, YY]) % bm[2]),
          error(Str("FAIL: residue case ", [bm[1], RR, TT, YY]))))));
    chk(n > 0, Str("b=", bm[1], ": V is never a cube mod ", bm[2], " (", n, " residue cases)")));
}
{
  my(U = 'U, X, Y, A);
  X = 729*U^4/26 + 252*U/13; Y = 729*U^3/26 + 239/13; A = -(Y^2 - 16*Y - 44)/27;
  chk(A^2 + Y^2*A + X^3 - 2 == 0, "b=-2 family satisfies the equation identically");
  X = -4*U^4/99 + 56*U/33; Y = 122/33 - 4*U^3/99; A = -(11*Y^2 - 48*Y + 54)/2;
  chk(A^2 + Y^2*A + X^3 + 3 == 0, "b=3 family satisfies the equation identically");
}
{
  if (NOK == NEXPECTED, print("ALL CROSS-CHECKS PASSED (", NOK, " checks)"); quit(0),
    print("CROSS-CHECK FAILED: ", NOK, " of ", NEXPECTED, " checks passed"); quit(1));
}
