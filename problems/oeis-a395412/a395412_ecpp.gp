\\ PARI/GP helper for problems/oeis-a395412 (driven by ecpp_certify.py).
\\
\\ a395412_witness(n, certfile): scan squarefree d = 1, 2, ... < p_n in
\\ increasing order and stop at the first d for which C = P_n/d + d passes
\\ PARI's BPSW test ispseudoprime.  Then prove C prime with an Atkin-Morain
\\ ECPP certificate (primecert), write that certificate to certfile with one
\\ step [N_i, t_i, s_i, a_i, [x_i, y_i]] per line, read the file back with
\\ readvec and accept it only if primecertisvalid succeeds on what was read.
\\ The BPSW test only selects d; the certificate is the primality proof.
\\
\\ Output: one line "A395412 n p_n d bits steps primecert_ms check_ms skipped",
\\ times being CPU milliseconds (getabstime) and skipped the number of BPSW
\\ probable primes rejected by primecert (none expected).  If no d works,
\\ "A395412-ZERO n p_n" is printed instead; that would only be a lead, since
\\ refuting the conjecture also needs compositeness proofs for every d.

a395412_witness(n, certfile) =
{
  my(p = prime(n), P = vecprod(primes(n)), skipped = 0);
  for (d = 1, p - 1,
    my(N, C, R, t0, t1, t2);
    if (!issquarefree(d), next);
    N = P / d + d;
    if (!ispseudoprime(N), next);
    t0 = getabstime();
    C = primecert(N);
    t1 = getabstime();
    if (C === 0, skipped++; next);
    for (i = 1, #C, write(certfile, C[i]));
    R = readvec(certfile);
    if (R != C || R[1][1] != N || !primecertisvalid(R),
      error("A395412: certificate check failed for n = ", n, ", d = ", d));
    t2 = getabstime();
    print("A395412 ", n, " ", p, " ", d, " ", #binary(N), " ", #C, " ",
          t1 - t0, " ", t2 - t1, " ", skipped);
    return(d));
  print("A395412-ZERO ", n, " ", p);
  return(0);
}
