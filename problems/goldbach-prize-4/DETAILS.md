**English** | [한국어](DETAILS.ko.md)

# Mathematical details for prize problem 4

Let (P) denote the advertised universal proposition. Assuming (P),
specialize it to the primes (2<3<5) and (n=5). A supplied witness must
satisfy (h,k>0) and (h+k=5), so elementary order arithmetic gives exactly

\[
  (h,k)\in\{(1,4),(2,3),(3,2),(4,1)\}.
\]

The four branches contradict, respectively, the claimed facts
(3\nmid2k+1), (3\nmid2h-1), (5\nmid2h-1), and
(3\nmid2k+1). The quotients are (3,1,1,1), so no primality or modular
computation is hidden in the argument.

In Lean, `omega` derives only the exhaustive four-way split from linear
natural-number constraints. Each contradiction is then proved by `norm_num`,
which constructs and checks the corresponding small divisibility witness.
The theorem proves `¬ statement`; it does not merely exhibit a failed search.

The complete trust boundary is Lean's kernel plus mathlib. There is no
`sorry`, added axiom, `native_decide`, external solver certificate, or
numerical search artifact.
