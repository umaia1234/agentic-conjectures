import Mathlib

/-!
# OEIS A319197 — refutation of the stated `I(n; 1) = 1` normalization

OEIS A319197 (offset 3) defines

`I(n; m) = F(2^(n-2) * 3 * m) / (2^n * Product_{j=3..n} a(j))`

and its Formula section states that there are no further common factors because
`I(n; 1) = 1`.  The published data begin

`a(3), ..., a(7) = 1, 9, 161, 51841, 6989569`.

At `n = 7` and `m = 1`, those exact values give `I(7; 1) = 769`, not `1`.
This module proves both the exact evaluation and the negation of that specific
normalization claim.

This does **not** refute the entry's separate conjecture that `I(n; m)` is a
nonnegative integer for every `n >= 3` and `m >= 0`: the counterexample value
`769` is itself a positive integer.

Faithfulness notes (there is no upstream Lean snapshot for this entry):
- `factorProductAtSeven` transcribes precisely the five source terms with
  indices 3 through 7; no values outside the published counterexample are
  assigned or assumed.
- The source index `2^(n-2) * 3 * m` becomes `2^(7-2) * 3 * 1 = 96`.
- Lean natural-number subtraction matches ordinary subtraction because `7 >= 2`.
- `Nat.div` does not hide rounding here: the exact computation also verifies
  that the denominator divides `F(96)`, with quotient `769`.
- The theorem is scoped only to the explicit `I(n; 1) = 1` subclaim; it makes
  no novelty claim and no assertion about the unresolved all-`m` conjecture.
-/

namespace AgenticConjectures.OeisA319197

/-- Product of the published terms `a(3)` through `a(7)`. -/
def factorProductAtSeven : ℕ :=
  1 * 9 * 161 * 51841 * 6989569

/-- The denominator in the source's definition of `I(7; 1)`. -/
def sourceDenominatorAtSeven : ℕ :=
  2 ^ 7 * factorProductAtSeven

/-- The exact `n = 7`, `m = 1` instance of the source's `I(n; m)`. -/
def sourceIAtSeven : ℕ :=
  Nat.fib (2 ^ (7 - 2) * 3 * 1) / sourceDenominatorAtSeven

/-- The A319197 Formula-section subclaim instantiated at `n = 7`. -/
def statement : Prop :=
  sourceIAtSeven = 1

/-- Exact evaluation of the published `n = 7` denominator. -/
theorem source_denominator_at_seven_value :
    sourceDenominatorAtSeven = 67205083036226688 := by
  norm_num [sourceDenominatorAtSeven, factorProductAtSeven]

/-- Exact counterexample value: the source's own data give `I(7; 1) = 769`. -/
theorem source_I_at_seven_value : sourceIAtSeven = 769 := by
  norm_num [sourceIAtSeven, sourceDenominatorAtSeven, factorProductAtSeven,
    Nat.fib, Function.iterate_succ_apply]

/-- **Refutation of the A319197 `I(n; 1) = 1` normalization claim** at `n = 7`. -/
theorem oeis_a319197_normalization_false : ¬ statement := by
  norm_num [statement, source_I_at_seven_value]

end AgenticConjectures.OeisA319197
