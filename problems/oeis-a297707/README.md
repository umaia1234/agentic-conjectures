**English** | [한국어](README.ko.md)

# OEIS A297707

Experimental code that searches for gaps to the previous prime. It requires
`gmpy2` and `sympy`, and since the output endpoints are Baillie–PSW
probable primes, a separate primality certification is needed to use them
as a final proof.

```bash
python3 problems/oeis-a297707/oeis_a297707_search.py N
```

## Upstream Lean formalization

The FormalConjectures [original snapshot and provenance record](upstream/README.md)
is preserved in [`297707_fd3973db.lean`](upstream/297707_fd3973db.lean).
The theorem stating that the counterexample index is greater than `250` is
a `by sorry` **conjecture statement**, not a formal proof. The search in
this folder is likewise a probable-prime experiment and does not certify
that statement.
