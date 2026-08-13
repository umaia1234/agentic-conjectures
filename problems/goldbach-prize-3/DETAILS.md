**English** | [한국어](DETAILS.ko.md)

# Mathematical details for prize problem 3

Fix \(q>0\), set \(M=n_2\cdots n_k\), and let
\(\rho(q)=1+((q-1)\bmod M)\). The division algorithm gives
\(1\leq\rho(q)\leq M\) and \(q\equiv\rho(q)\pmod M\). For each
\(j\geq2\), transitivity through \(n_j\mid M\) gives
\(q\equiv\rho(q)\pmod{n_j}\). Multiplication by \(n_1\) and subtraction
of one preserve this congruence. Hence

\[
 n_j\mid n_1q-1\iff n_j\mid n_1\rho(q)-1.
\]

This is the only periodicity fact used by the construction.

For the forward inclusion, take \(y\in S\). Since \(n_1\mid y+1\), write
\(y+1=n_1q\). Positivity of \(y\) implies \(q>0\), and then
\(y=f(q)=n_1q-1\). The avoidance conditions on \(y\), transported through
the displayed equivalence, put \(\rho(q)\) in \(I_2\); hence \(g(q)\) lies
in the chosen finite sumset.

For the reverse inclusion, membership supplies some \(r\in I_2\) with
\(n_2\rho(q)+C=n_2r+C\). Cancellation is valid because \(n_2>1\), so
\(\rho(q)=r\). Periodicity gives avoidance of all \(n_j\), \(j\geq2\).
Moreover \(f(q)+1=n_1q\), and if \(n_1\) divided \(f(q)\), it would divide
the difference 1, contradicting \(n_1>1\). Thus \(f(q)\in S\).

The Lean theorem uses `List.prod` and `List.sum` only to represent the fixed
finite product and sum. `residueSet_finite` bounds \(I_2\) by
`{r : ℕ | r ≤ M}`. The congruence step uses mathlib's `Nat.ModEq`; no finite
instances are enumerated.

The trust boundary is Lean's kernel plus mathlib. There is no `sorry`, added
axiom, `native_decide`, computational search, external solver, or unverified
certificate.
