import Mathlib

/-!
# OEIS A286185 / A286183 — connected induced subgraphs of Möbius ladders and antiprisms

Giovanni Resta's 2017 family of OEIS entries counts the connected induced
(non-null) subgraphs of the standard `2n`-vertex "width-two cyclic strip" graphs:

* [A286182](https://oeis.org/A286182) — the prism graph (circular ladder) `C n □ K₂`;
* [A286185](https://oeis.org/A286185) — the Möbius ladder on `2n` vertices;
* [A286183](https://oeis.org/A286183) — the antiprism on `2n` vertices.

Each entry carries a conjectured closed form, a conjectured order-6 linear
recurrence and a conjectured generating function.  For the **prism** these were
proved by A. Vince, *The average size of a connected vertex set of a graph —
explicit formulas and open problems*, J. Graph Theory **97** (2021) 82–103,
Lemma 7.2 (the OEIS entry has not been updated).  For the **Möbius ladder** and
the **antiprism** we found no proof in the literature;
`problems/oeis-a286185-a286183/PROOF.md` gives one, by a uniform column
transfer-matrix argument that also re-derives the prism case.

This module contributes the machine-checked parts:

* `prism`, `moebius`, `antiprism` — the three graphs, and `connectedInducedCount`;
* `statementMoebius`, `statementAntiprism`, `statementPrism` — faithful
  formalisations of the three conjectured closed forms;
* `aMoebius_linear_recurrence`, `aAntiprism_linear_recurrence`,
  `aPrism_linear_recurrence` — each closed form satisfies the order-6 recurrence
  conjectured on its OEIS entry, for **every** `n` (proved, no `sorry`);
* `statement*_imp_*_linear_recurrence` — hence each closed form implies the
  corresponding recurrence for the graph counts themselves.

The graph-theoretic identities `connectedInducedCount _ n = a n` are proved in
`PROOF.md`, not in Lean; they are re-verified numerically (exhaustively for small
`n`, and by an independent generic algorithm up to `n = 200`) by
`problems/oeis-a286185-a286183/certificate.py`.

## Faithfulness notes

* Vertices are `ZMod n × Bool`; `(i, r)` is row `r` of column `i`.  All three
  graphs share the *rungs* `(i, 0) ~ (i, 1)` and differ only in how consecutive
  columns are joined:
  - `prism`: rails `(i, r) ~ (i + 1, r)` in both rows;
  - `moebius`: the same, except that the rails leaving the last column are
    *twisted*, `(n - 1, r) ~ (0, !r)`.  The rails then form a single `2n`-cycle
    and the rungs are its `n` main diagonals, which is the usual definition of
    the Möbius ladder;
  - `antiprism`: both rails plus the diagonal `(i, 1) ~ (i + 1, 0)`.
* The side condition `u.1 ≠ v.1` on every inter-column edge keeps the graph
  simple in the degenerate cases `n = 1, 2`, which OEIS includes: all three
  families then give `K₂` at `n = 1`, and at `n = 2` the prism gives `C₄` while
  the Möbius ladder and the antiprism both give `K₄`.  That reproduces the OEIS
  terms `3, 13` and `3, 15, …` exactly.
* OEIS uses offset 1 for all three entries and the `statement`s are quantified
  over `1 ≤ n`, so indices agree with the OEIS entries with no shift.
* A286185 states its closed form as `Lucas(n, 2) + 3 n · Fibonacci(n, 2) - n - 1`
  with `Lucas(n, 2) = A002203 n` and `Fibonacci(n, 2) = A000129 n`; A286183 states
  `A005248 n - 2 n + 2 n · A001906 n`.  Below, `Q`/`P` are A002203/A000129 (defined
  by their own recurrences) and `H`/`G` are A005248/A001906, i.e. `L (2n)` and
  `F (2n)`, likewise defined by the recurrence `x (n+2) = 3 x (n+1) - x n` that
  those even-index bisections satisfy.
* There is no `upstream/` Lean snapshot: none of these entries is among the
  sequences formalised in google-deepmind/formal-conjectures.  The canonical
  source is the OEIS entry itself, quoted in the problem README.
-/

namespace AgenticConjectures.OeisA286185A286183

/-! ### The four integer sequences appearing in the closed forms -/

/-- Pell numbers, [A000129](https://oeis.org/A000129): `0, 1, 2, 5, 12, 29, 70, …` -/
def P : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * P (n + 1) + P n

/-- Companion Pell (Pell–Lucas) numbers, [A002203](https://oeis.org/A002203):
`2, 2, 6, 14, 34, 82, 198, …` -/
def Q : ℕ → ℤ
  | 0 => 2
  | 1 => 2
  | n + 2 => 2 * Q (n + 1) + Q n

/-- [A001906](https://oeis.org/A001906), the even-index Fibonacci bisection
`F (2n)`: `0, 1, 3, 8, 21, 55, 144, …` -/
def G : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 3 * G (n + 1) - G n

/-- [A005248](https://oeis.org/A005248), the even-index Lucas bisection `L (2n)`:
`2, 3, 7, 18, 47, 123, 322, …` -/
def H : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 3 * H (n + 1) - H n

/-! ### The three graphs -/

/-- The prism graph (circular ladder) `C n □ K₂` on `2 n` vertices. -/
def prism (n : ℕ) : SimpleGraph (ZMod n × Bool) where
  Adj u v :=
    (u.1 = v.1 ∧ u.2 ≠ v.2) ∨ (u.2 = v.2 ∧ u.1 ≠ v.1 ∧ (v.1 = u.1 + 1 ∨ u.1 = v.1 + 1))
  symm := by
    rintro u v (⟨h1, h2⟩ | ⟨h1, h2, h3 | h3⟩)
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, h2.symm, Or.inr h3⟩
    · exact Or.inr ⟨h1.symm, h2.symm, Or.inl h3⟩
  loopless := ⟨by rintro u (⟨-, h⟩ | ⟨-, h, -⟩) <;> exact h rfl⟩

/-- The Möbius ladder on `2 n` vertices: the prism with the rails out of the last
column twisted, `(n - 1, r) ~ (0, !r)`.  Equivalently a `2n`-cycle plus its `n`
main diagonals. -/
def moebius (n : ℕ) : SimpleGraph (ZMod n × Bool) where
  Adj u v :=
    (u.1 = v.1 ∧ u.2 ≠ v.2) ∨
      (u.1 ≠ v.1 ∧
        ((v.1 = u.1 + 1 ∧ (if u.1 = (n : ZMod n) - 1 then u.2 ≠ v.2 else u.2 = v.2)) ∨
         (u.1 = v.1 + 1 ∧ (if v.1 = (n : ZMod n) - 1 then u.2 ≠ v.2 else u.2 = v.2))))
  symm := by
    rintro u v (⟨h1, h2⟩ | ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩)
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, Or.inr ⟨h2, by split at h3 <;> simp_all [ne_comm]⟩⟩
    · exact Or.inr ⟨h1.symm, Or.inl ⟨h2, by split at h3 <;> simp_all [ne_comm]⟩⟩
  loopless := ⟨by rintro u (⟨-, h⟩ | ⟨h, -⟩) <;> exact h rfl⟩

/-- The antiprism on `2 n` vertices: the prism together with the diagonals
`(i, 1) ~ (i + 1, 0)`. -/
def antiprism (n : ℕ) : SimpleGraph (ZMod n × Bool) where
  Adj u v :=
    (u.1 = v.1 ∧ u.2 ≠ v.2) ∨
      (u.1 ≠ v.1 ∧
        ((v.1 = u.1 + 1 ∧ (u.2 = v.2 ∨ (u.2 = true ∧ v.2 = false))) ∨
         (u.1 = v.1 + 1 ∧ (u.2 = v.2 ∨ (v.2 = true ∧ u.2 = false)))))
  symm := by
    rintro u v (⟨h1, h2⟩ | ⟨h1, ⟨h2, h3⟩ | ⟨h2, h3⟩⟩)
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h1.symm, Or.inr ⟨h2, h3.imp Eq.symm id⟩⟩
    · exact Or.inr ⟨h1.symm, Or.inl ⟨h2, h3.imp Eq.symm id⟩⟩
  loopless := ⟨by rintro u (⟨-, h⟩ | ⟨h, -⟩) <;> exact h rfl⟩

/-- The number of non-null induced subgraphs of `Γ` that are connected — the
quantity tabulated by A286182 / A286185 / A286183. -/
noncomputable def connectedInducedCount {V : Type*} [DecidableEq V] (Γ : SimpleGraph V) : ℕ :=
  {S : Finset V | S.Nonempty ∧ (Γ.induce (S : Set V)).Connected}.ncard

/-! ### The conjectured closed forms -/

/-- A286182 (prism), Eric W. Weisstein 2017: `A002203 n + 3 n · A000129 n - 3 n + 1`. -/
def aPrism (n : ℕ) : ℤ := Q n + 3 * (n : ℤ) * P n - 3 * (n : ℤ) + 1

/-- A286185 (Möbius ladder), Eric W. Weisstein 2017:
`A002203 n + 3 n · A000129 n - n - 1`. -/
def aMoebius (n : ℕ) : ℤ := Q n + 3 * (n : ℤ) * P n - (n : ℤ) - 1

/-- A286183 (antiprism), Eric W. Weisstein 2017:
`A005248 n - 2 n + 2 n · A001906 n`. -/
def aAntiprism (n : ℕ) : ℤ := H n - 2 * (n : ℤ) + 2 * (n : ℤ) * G n

/-- **A286182 closed-form conjecture.**  Proved by Vince (2021), Lemma 7.2, and
re-proved in `PROOF.md`; not formalised here. -/
def statementPrism : Prop :=
  ∀ n : ℕ, 1 ≤ n → (connectedInducedCount (prism n) : ℤ) = aPrism n

/-- **A286185 closed-form conjecture** (Eric W. Weisstein, OEIS A286185): the
number of connected induced non-null subgraphs of the `2n`-vertex Möbius ladder
is `A002203 n + 3 n · A000129 n - n - 1`, for every `n ≥ 1`.  A complete
elementary proof is given in `PROOF.md`; it is not formalised here. -/
def statementMoebius : Prop :=
  ∀ n : ℕ, 1 ≤ n → (connectedInducedCount (moebius n) : ℤ) = aMoebius n

/-- **A286183 closed-form conjecture** (Eric W. Weisstein, OEIS A286183): the
number of connected induced non-null subgraphs of the `2n`-vertex antiprism is
`A005248 n - 2 n + 2 n · A001906 n`, for every `n ≥ 1`.  A complete elementary
proof is given in `PROOF.md`; it is not formalised here. -/
def statementAntiprism : Prop :=
  ∀ n : ℕ, 1 ≤ n → (connectedInducedCount (antiprism n) : ℤ) = aAntiprism n

/-! ### The conjectured linear recurrences follow from the closed forms -/

section Recurrence

private lemma P_step (n : ℕ) : P (n + 2) = 2 * P (n + 1) + P n := rfl
private lemma Q_step (n : ℕ) : Q (n + 2) = 2 * Q (n + 1) + Q n := rfl
private lemma G_step (n : ℕ) : G (n + 2) = 3 * G (n + 1) - G n := rfl
private lemma H_step (n : ℕ) : H (n + 2) = 3 * H (n + 1) - H n := rfl

/-- `aPrism` satisfies the order-6 recurrence conjectured for A286182, whose
characteristic polynomial is `(x - 1)² (x² - 2x - 1)²`. -/
theorem aPrism_linear_recurrence (n : ℕ) :
    aPrism (n + 6) = 6 * aPrism (n + 5) - 11 * aPrism (n + 4) + 4 * aPrism (n + 3)
      + 5 * aPrism (n + 2) - 2 * aPrism (n + 1) - aPrism n := by
  have hp2 : P (n + 2) = 2 * P (n + 1) + P n := P_step n
  have hp3 : P (n + 3) = 2 * P (n + 2) + P (n + 1) := P_step (n + 1)
  have hp4 : P (n + 4) = 2 * P (n + 3) + P (n + 2) := P_step (n + 2)
  have hp5 : P (n + 5) = 2 * P (n + 4) + P (n + 3) := P_step (n + 3)
  have hp6 : P (n + 6) = 2 * P (n + 5) + P (n + 4) := P_step (n + 4)
  have hq2 : Q (n + 2) = 2 * Q (n + 1) + Q n := Q_step n
  have hq3 : Q (n + 3) = 2 * Q (n + 2) + Q (n + 1) := Q_step (n + 1)
  have hq4 : Q (n + 4) = 2 * Q (n + 3) + Q (n + 2) := Q_step (n + 2)
  have hq5 : Q (n + 5) = 2 * Q (n + 4) + Q (n + 3) := Q_step (n + 3)
  have hq6 : Q (n + 6) = 2 * Q (n + 5) + Q (n + 4) := Q_step (n + 4)
  simp only [aPrism]
  push_cast
  rw [hp6, hp5, hp4, hp3, hp2, hq6, hq5, hq4, hq3, hq2]
  ring

/-- `aMoebius` satisfies the order-6 recurrence conjectured for A286185 — the same
characteristic polynomial `(x - 1)² (x² - 2x - 1)²` as the prism. -/
theorem aMoebius_linear_recurrence (n : ℕ) :
    aMoebius (n + 6) = 6 * aMoebius (n + 5) - 11 * aMoebius (n + 4) + 4 * aMoebius (n + 3)
      + 5 * aMoebius (n + 2) - 2 * aMoebius (n + 1) - aMoebius n := by
  have hp2 : P (n + 2) = 2 * P (n + 1) + P n := P_step n
  have hp3 : P (n + 3) = 2 * P (n + 2) + P (n + 1) := P_step (n + 1)
  have hp4 : P (n + 4) = 2 * P (n + 3) + P (n + 2) := P_step (n + 2)
  have hp5 : P (n + 5) = 2 * P (n + 4) + P (n + 3) := P_step (n + 3)
  have hp6 : P (n + 6) = 2 * P (n + 5) + P (n + 4) := P_step (n + 4)
  have hq2 : Q (n + 2) = 2 * Q (n + 1) + Q n := Q_step n
  have hq3 : Q (n + 3) = 2 * Q (n + 2) + Q (n + 1) := Q_step (n + 1)
  have hq4 : Q (n + 4) = 2 * Q (n + 3) + Q (n + 2) := Q_step (n + 2)
  have hq5 : Q (n + 5) = 2 * Q (n + 4) + Q (n + 3) := Q_step (n + 3)
  have hq6 : Q (n + 6) = 2 * Q (n + 5) + Q (n + 4) := Q_step (n + 4)
  simp only [aMoebius]
  push_cast
  rw [hp6, hp5, hp4, hp3, hp2, hq6, hq5, hq4, hq3, hq2]
  ring

/-- `aAntiprism` satisfies the order-6 recurrence conjectured for A286183, whose
characteristic polynomial is `(x - 1)² (x² - 3x + 1)²`. -/
theorem aAntiprism_linear_recurrence (n : ℕ) :
    aAntiprism (n + 6) = 8 * aAntiprism (n + 5) - 24 * aAntiprism (n + 4)
      + 34 * aAntiprism (n + 3) - 24 * aAntiprism (n + 2) + 8 * aAntiprism (n + 1)
      - aAntiprism n := by
  have hg2 : G (n + 2) = 3 * G (n + 1) - G n := G_step n
  have hg3 : G (n + 3) = 3 * G (n + 2) - G (n + 1) := G_step (n + 1)
  have hg4 : G (n + 4) = 3 * G (n + 3) - G (n + 2) := G_step (n + 2)
  have hg5 : G (n + 5) = 3 * G (n + 4) - G (n + 3) := G_step (n + 3)
  have hg6 : G (n + 6) = 3 * G (n + 5) - G (n + 4) := G_step (n + 4)
  have hh2 : H (n + 2) = 3 * H (n + 1) - H n := H_step n
  have hh3 : H (n + 3) = 3 * H (n + 2) - H (n + 1) := H_step (n + 1)
  have hh4 : H (n + 4) = 3 * H (n + 3) - H (n + 2) := H_step (n + 2)
  have hh5 : H (n + 5) = 3 * H (n + 4) - H (n + 3) := H_step (n + 3)
  have hh6 : H (n + 6) = 3 * H (n + 5) - H (n + 4) := H_step (n + 4)
  simp only [aAntiprism]
  push_cast
  rw [hg6, hg5, hg4, hg3, hg2, hh6, hh5, hh4, hh3, hh2]
  ring

/-- If the A286185 closed form holds, so does the linear recurrence conjectured
on the same entry. -/
theorem statementMoebius_imp_linear_recurrence (h : statementMoebius) (n : ℕ) (hn : 1 ≤ n) :
    (connectedInducedCount (moebius (n + 6)) : ℤ) =
      6 * connectedInducedCount (moebius (n + 5)) - 11 * connectedInducedCount (moebius (n + 4))
        + 4 * connectedInducedCount (moebius (n + 3)) + 5 * connectedInducedCount (moebius (n + 2))
        - 2 * connectedInducedCount (moebius (n + 1)) - connectedInducedCount (moebius n) := by
  rw [h (n + 6) (by omega), h (n + 5) (by omega), h (n + 4) (by omega),
    h (n + 3) (by omega), h (n + 2) (by omega), h (n + 1) (by omega), h n hn]
  exact aMoebius_linear_recurrence n

/-- If the A286183 closed form holds, so does the linear recurrence conjectured
on the same entry. -/
theorem statementAntiprism_imp_linear_recurrence (h : statementAntiprism) (n : ℕ) (hn : 1 ≤ n) :
    (connectedInducedCount (antiprism (n + 6)) : ℤ) =
      8 * connectedInducedCount (antiprism (n + 5))
        - 24 * connectedInducedCount (antiprism (n + 4))
        + 34 * connectedInducedCount (antiprism (n + 3))
        - 24 * connectedInducedCount (antiprism (n + 2))
        + 8 * connectedInducedCount (antiprism (n + 1))
        - connectedInducedCount (antiprism n) := by
  rw [h (n + 6) (by omega), h (n + 5) (by omega), h (n + 4) (by omega),
    h (n + 3) (by omega), h (n + 2) (by omega), h (n + 1) (by omega), h n hn]
  exact aAntiprism_linear_recurrence n

/-- If the A286182 closed form holds, so does the linear recurrence conjectured
on the same entry. -/
theorem statementPrism_imp_linear_recurrence (h : statementPrism) (n : ℕ) (hn : 1 ≤ n) :
    (connectedInducedCount (prism (n + 6)) : ℤ) =
      6 * connectedInducedCount (prism (n + 5)) - 11 * connectedInducedCount (prism (n + 4))
        + 4 * connectedInducedCount (prism (n + 3)) + 5 * connectedInducedCount (prism (n + 2))
        - 2 * connectedInducedCount (prism (n + 1)) - connectedInducedCount (prism n) := by
  rw [h (n + 6) (by omega), h (n + 5) (by omega), h (n + 4) (by omega),
    h (n + 3) (by omega), h (n + 2) (by omega), h (n + 1) (by omega), h n hn]
  exact aPrism_linear_recurrence n

end Recurrence

/-! ### The closed forms reproduce the OEIS data terms -/

/-- A286182 begins `3, 13, 51, 167, 503, 1441`. -/
theorem aPrism_initial_values :
    aPrism 1 = 3 ∧ aPrism 2 = 13 ∧ aPrism 3 = 51 ∧ aPrism 4 = 167 ∧ aPrism 5 = 503 ∧
      aPrism 6 = 1441 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [aPrism, P, Q]

/-- A286185 begins `3, 15, 55, 173, 511, 1451`. -/
theorem aMoebius_initial_values :
    aMoebius 1 = 3 ∧ aMoebius 2 = 15 ∧ aMoebius 3 = 55 ∧ aMoebius 4 = 173 ∧
      aMoebius 5 = 511 ∧ aMoebius 6 = 1451 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [aMoebius, P, Q]

/-- A286183 begins `3, 15, 60, 207, 663, 2038`. -/
theorem aAntiprism_initial_values :
    aAntiprism 1 = 3 ∧ aAntiprism 2 = 15 ∧ aAntiprism 3 = 60 ∧ aAntiprism 4 = 207 ∧
      aAntiprism 5 = 663 ∧ aAntiprism 6 = 2038 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [aAntiprism, G, H]

end AgenticConjectures.OeisA286185A286183
