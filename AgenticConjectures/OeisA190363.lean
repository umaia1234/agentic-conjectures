import Mathlib

/-!
# OEIS A190363 — refutation of the conjectured order-21 linear recurrence

The OEIS entry for A190363 (`a(n) = 2n + ⌊n·√(5/4)⌋ + ⌊n/4⌋`) conjectures the
constant-coefficient recurrence `a(n+21) = a(n+17) + a(n+4) - a(n)`.

The definitions `a`, `A190363_coeffs`, `A190363_LR` below are copied **verbatim**
(modulo namespace) from the upstream statement snapshot
`problems/oeis-a190363/upstream/190363_e4edee15.lean`
(google-deepmind/formal-conjectures, commit `e4edee15…`, Apache-2.0), which
formalizes the conjecture as `A190363_LR.IsSolution (fun n => (a (n + 1) : ℤ))`.

We prove the **negation** of that exact statement: the recurrence first fails at
solution index `n = 139`, i.e. `a(161) = 542 ≠ 541 = a(157) + a(144) - a(140)`.
This matches the informal disproof in `problems/oeis-a190363/PROOF.md` and the
certificate `a190363_certificate.py`.

Faithfulness notes: the sequence is indexed through `fun n => a (n + 1)` (OEIS
offset 1), so `IsSolution` failing at `n = 139` is the OEIS-level failure at
base index 140; `mathlib`'s `LinearRecurrence.IsSolution` is the forward form
`u (n + 21) = ∑ i, coeffs i · u (n + i)`.
-/

namespace AgenticConjectures.OeisA190363

open Real

/-- Upstream definition, verbatim: `a(n) = 2n + ⌊n·√(5/4)⌋ + ⌊n/4⌋`. -/
noncomputable def a (n : ℕ) : ℕ :=
  let n_R : ℝ := n
  let sqrt_expr : ℝ := sqrt (5 / 4)
  let floor_term_sqrt : ℕ := (Int.floor (n_R * sqrt_expr)).toNat
  let floor_term_div : ℕ := n / 4
  2 * n + floor_term_sqrt + floor_term_div

/-- Upstream definition, verbatim: coefficients of the conjectured recurrence
`u(n+21) = ∑ c̃ᵢ u(n+i)` with `c̃₀ = -1, c̃₄ = 1, c̃₁₇ = 1`. -/
noncomputable def A190363_coeffs : Fin 21 → ℤ :=
  fun i =>
    match i.val with
    | 0 => -1
    | 4 => 1
    | 17 => 1
    | _ => 0

/-- Upstream definition, verbatim. -/
noncomputable def A190363_LR : LinearRecurrence ℤ :=
  LinearRecurrence.mk 21 A190363_coeffs

/-- Exact evaluation of `⌊m·√(5/4)⌋` from an integer square sandwich
`4k² ≤ 5m² < 4(k+1)²`. -/
private lemma floor_toNat_eval (m k : ℕ)
    (h1 : 4 * k ^ 2 ≤ 5 * m ^ 2) (h2 : 5 * m ^ 2 < 4 * (k + 1) ^ 2) :
    (Int.floor ((m : ℝ) * Real.sqrt (5 / 4))).toNat = k := by
  have hs : Real.sqrt (5 / 4) ^ 2 = 5 / 4 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt (5 / 4) := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hms : ((m : ℝ) * Real.sqrt (5 / 4)) ^ 2 = (m : ℝ) ^ 2 * (5 / 4) := by
    rw [mul_pow, hs]
  have h1' : 4 * (k : ℝ) ^ 2 ≤ 5 * (m : ℝ) ^ 2 := by exact_mod_cast h1
  have h2' : 5 * (m : ℝ) ^ 2 < 4 * ((k : ℝ) + 1) ^ 2 := by exact_mod_cast h2
  have hprod0 : (0 : ℝ) ≤ (m : ℝ) * Real.sqrt (5 / 4) := mul_nonneg hm0 hs0
  have hfloor : Int.floor ((m : ℝ) * Real.sqrt (5 / 4)) = (k : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast
      nlinarith [hms, hprod0, h1']
    · push_cast
      nlinarith [hms, hprod0, h2']
  rw [hfloor]
  exact Int.toNat_natCast k

private lemma a_140 : a 140 = 471 := by
  simp only [a]
  rw [floor_toNat_eval 140 156 (by norm_num) (by norm_num)]

private lemma a_144 : a 144 = 484 := by
  simp only [a]
  rw [floor_toNat_eval 144 160 (by norm_num) (by norm_num)]

private lemma a_157 : a 157 = 528 := by
  simp only [a]
  rw [floor_toNat_eval 157 175 (by norm_num) (by norm_num)]

private lemma a_161 : a 161 = 542 := by
  simp only [a]
  rw [floor_toNat_eval 161 180 (by norm_num) (by norm_num)]

/-- **Refutation of the A190363 recurrence conjecture** (the exact negation of
upstream `oeis_190363_conjecture_0`): the sequence `n ↦ a (n + 1)` is *not* a
solution of the order-21 recurrence with coefficients `A190363_coeffs`. -/
theorem oeis_190363_conjecture_0_false :
    ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  -- `h 139` states the recurrence at solution index 139; restating it with the
  -- literal type `Fin 21` (definitionally equal) lets the sum lemmas fire.
  have h161 : (a 161 : ℤ) =
      ∑ x : Fin 21, A190363_coeffs x * (a (139 + (x : ℕ) + 1) : ℤ) := h 139
  rw [Finset.sum_fin_eq_sum_range] at h161
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h161
  norm_num [A190363_coeffs, a_140, a_144, a_157, a_161] at h161

end AgenticConjectures.OeisA190363
