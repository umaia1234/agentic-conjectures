import Mathlib

/-!
# OEIS A072780 — refutation of the Goldbach-like equivalence

The canonical OEIS entry defines

`a(n) = sigma_2(n) + phi(n) * sigma(n) - 2*n^2`

and states that, when `n = m^2-r^2` with `m > r`, one has `a(n)=2` if and
only if `m-r` and `m+r` are prime. The definitions below are copied verbatim
(modulo namespace) from
`problems/oeis-a072780/upstream/72780_30fabef9.lean`, the Formal Conjectures
snapshot at commit `67338a157bbb8d87e9a349d662f82a868bda6327`.

We refute exactly the universally quantified upstream proposition. At
`m=8`, `r=7`, natural subtraction is ordinary subtraction because `8>7`,
and `8^2-7^2=15`. Exact kernel computation gives `a(15)=2`, while the
corresponding factors are `1` and `15`, neither prime.

Faithfulness notes: OEIS has offset 1, but the counterexample uses the
positive input 15. The upstream definition performs the potentially signed
outer subtraction in `Int` and then applies `Int.toNat`; this file preserves
that convention exactly. The powers and the inner differences in the
Goldbach-like statement use `Nat`, also exactly as upstream. The hypothesis
`m > r` prevents truncation in `m-r` and `m^2-r^2` for this statement.
-/

namespace AgenticConjectures.OeisA072780

open Nat Finset

/-- Upstream definition, verbatim: `sigma_2(n) + phi(n)*sigma(n) - 2*n^2`,
computed in `Int` and converted back to `Nat`. -/
def a (n : ℕ) : ℕ :=
  let sigma2_n : ℕ := n.divisors.sum fun d => d ^ 2
  let sigma1_n : ℕ := n.divisors.sum fun d => d
  let phi_n : ℕ := n.totient
  let two_n_sq : ℕ := 2 * n ^ 2
  ((sigma2_n : ℤ) + (phi_n * sigma1_n : ℤ) - (two_n_sq : ℤ)).toNat

/-- The exact universally quantified proposition expressed by upstream
`oeis_72780_goldbach_conjecture`. -/
def goldbachStatement : Prop :=
  ∀ (m r : ℕ), m > r →
    (a (m ^ 2 - r ^ 2) = 2 ↔ (m - r).Prime ∧ (m + r).Prime)

/-- Exact evaluation of the counterexample's sequence value. -/
theorem counterexample_value : a 15 = 2 := by
  decide

/-- The factors selected by `(m,r)=(8,7)` are not prime even though the
sequence value at their difference of squares is 2. -/
theorem counterexample :
    a (8 ^ 2 - 7 ^ 2) = 2 ∧
      ¬ ((8 - 7).Prime ∧ (8 + 7).Prime) := by
  norm_num [counterexample_value]

/-- **Refutation of the exact A072780 Goldbach-like conjecture.** -/
theorem goldbach_conjecture_false : ¬ goldbachStatement := by
  intro h
  have h87 := h 8 7 (by norm_num)
  exact counterexample.2 (h87.mp counterexample.1)

end AgenticConjectures.OeisA072780
