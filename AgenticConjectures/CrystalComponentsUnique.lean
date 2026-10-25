import Mathlib

/-!
# Uniqueness of crystal components (arXiv:1601.03081)

Abrate, Barbero, Cerruti and Murru, *The Biharmonic mean* (arXiv:1601.03081), call an odd
`n = ab` with `a, b > 1` a *crystal* when `2 (a + 1)(b + 1)` divides `(a + b)^2 + (ab + 1)^2`.
They conjecture that the components of a crystal are unique: no other pair `c, d > 1` with
`n = cd` has the same property.  The conjecture is open; this file does not prove it.

What is proved here:

* `isCrystal_iff_dvd_sq_add`, `isCrystal_iff_dvd_succ_sq`, `isCrystal_iff_uv`: equivalent
  divisibility conditions.  Proposition 1 of the paper; the first two are also in the (open)
  Formal Conjectures PR #7051.
* `sq_eq_mul_iff_seqU`, `isCrystal_iff_seqU`: the paper's Theorems 4 and 5, the recurrent
  sequence classification of all crystals, stated with both orders of the pair (the paper
  writes `(u_n, u_{n-1})` only) and with the index range made exact.  The paper takes
  Theorem 4 from its reference [1] (Abrate, Barbero, Cerruti, Murru, *Polynomial sequences on
  quadratic curves*, Integers 2015); here it is proved by Vieta descent.
* `isCrystal_iff_kpr`: the same classification in closed form, `{a + 1, b + 1} =
  {2 k p^2, 2 (p + r)^2}` with `(p + r)^2 = k p r + 1`, through the Lucas sequence
  `lucas (k - 2)` (`seqU_lucas`); `isCrystal_iff_pronic`: `n + 1 = k q (q + 1)` and
  `a + b = k (q + 1)`.
* `statement_iff_crystalK_eq`: the conjecture is equivalent to "`n` determines
  `k = (a + b)^2 / ((a + 1)(b + 1))`", because `eq_of_crystalK_eq` shows that two crystal
  factorizations of the same `n` with the same `k` coincide.
* Cases of the conjecture: `eq_of_crystalK_eq_three` (`k = 3` occurs only for `35 = 5 · 7`),
  `eq_of_j1` (two crystals of the `j = 1` family `a + 1 = 2k` never share `n`), and the
  description `IsCrystalWithComponents.crystalK_eq_four_iff` of the `k = 4` family.
* `eq_of_crystalK_eq_four_of_j1`: the `k = 4` family against the `j = 1` family, **assuming**
  `EllipticCurveIntegralPoints`, the list of integral points of an elliptic curve computed in
  Sage/PARI.  That list is a hypothesis of this one theorem, not an axiom, and is not proved
  here.

## Upstream correspondence

The upstream statement is `Arxiv.«1601.03081».crystals_components_unique` of
google-deepmind/formal-conjectures at commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`
(snapshot `problems/crystal-components-unique/upstream/UniqueCrystalComponents.lean`).

* `IsCrystalWithComponents` and `isCrystalWithComponents_35_5_7` are copied term for term.
* `statement` is the upstream theorem with its arguments and hypotheses universally
  quantified; its conclusion `({a, b} : Finset ℕ) = {c, d}` is unchanged.
* Only what is needed outside the formal-conjectures project changes: `import Mathlib`
  replaces `public import FormalConjecturesUtil`; the `module` keyword, `@[expose] public
  section` and the `@[category ...]`/`@[AMS ...]` attributes are dropped; the namespace
  `Arxiv.«1601.03081»` becomes `AgenticConjectures.CrystalComponentsUnique`.
* This repository builds against mathlib `v4.30.0`, formal-conjectures at `c094b97` against
  `v4.33.1`.  The definitions use only `Odd`, `∣`, `*`, `^` on `ℕ` and `Finset` insertion,
  whose meaning is the same in both.
-/

namespace AgenticConjectures.CrystalComponentsUnique

/-! ## Upstream definitions and the open statement -/

/-- An odd number `n` is called a crystal if `n = ab`, with `a, b > 1` and `B(a, b) ∈ ℕ`, where
`B(a, b) := ((a + b)^2 + (a b + 1)^2) / (2 (a + 1) (b + 1))`.  Term for term the Formal
Conjectures definition `Arxiv.«1601.03081».IsCrystalWithComponents`. -/
def IsCrystalWithComponents (n a b : ℕ) : Prop :=
  Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ 2 * (a + 1) * (b + 1) ∣ (a + b)^2 + (a * b + 1)^2

/-- The upstream test case `isCrystalWithComponents_35_5_7`. -/
theorem isCrystalWithComponents_35_5_7 : IsCrystalWithComponents 35 5 7 := by
  norm_num [IsCrystalWithComponents]

/-- The open conjecture `crystals_components_unique`: the components of a crystal are unique. -/
def statement : Prop :=
  ∀ n a b c d : ℕ, IsCrystalWithComponents n a b → IsCrystalWithComponents n c d →
    ({a, b} : Finset ℕ) = {c, d}

/-! ## Proposition 1 of the paper (also in Formal Conjectures PR #7051) -/

theorem IsCrystalWithComponents.symm {n a b : ℕ} (h : IsCrystalWithComponents n a b) :
    IsCrystalWithComponents n b a := by
  obtain ⟨hn, ha, hb, rfl, hd⟩ := h
  refine ⟨mul_comm a b ▸ hn, hb, ha, mul_comm a b, ?_⟩
  rw [show 2 * (b + 1) * (a + 1) = 2 * (a + 1) * (b + 1) by ring,
    show (b + a) ^ 2 + (b * a + 1) ^ 2 = (a + b) ^ 2 + (a * b + 1) ^ 2 by ring]
  exact hd

theorem IsCrystalWithComponents.odd_left {n a b : ℕ} (h : IsCrystalWithComponents n a b) :
    Odd a := by
  obtain ⟨hn, -, -, rfl, -⟩ := h
  exact (Nat.odd_mul.mp hn).1

theorem IsCrystalWithComponents.odd_right {n a b : ℕ} (h : IsCrystalWithComponents n a b) :
    Odd b :=
  h.symm.odd_left

/-- `B(a, b) ∈ ℕ ↔ Q(a, b) = (a + b)^2 / ((a + 1)(b + 1)) ∈ ℕ` for odd `a`. -/
theorem dvd_biharmonic_iff (a b : ℕ) (ha : Odd a) :
    2 * (a + 1) * (b + 1) ∣ (a + b) ^ 2 + (a * b + 1) ^ 2 ↔
      (a + 1) * (b + 1) ∣ (a + b) ^ 2 := by
  obtain ⟨u, rfl⟩ := ha
  rw [← Int.natCast_dvd_natCast, ← Int.natCast_dvd_natCast]
  push_cast
  rw [show ((2 * u + 1 : ℤ) + b) ^ 2 + ((2 * u + 1 : ℤ) * b + 1) ^ 2 =
      2 * (((2 * u + 1 : ℤ) + b) ^ 2 + (2 * u + 1 + 1) * (b + 1) * (u * (b - 1))) by ring,
    show (2 : ℤ) * (2 * u + 1 + 1) * (b + 1) = 2 * ((2 * u + 1 + 1) * (b + 1)) by ring,
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]
  exact dvd_add_left (dvd_mul_right _ _)

/-- `Q(a, b) ∈ ℕ ↔ F(a, b) = (a b + 1)^2 / ((a + 1)(b + 1)) ∈ ℕ`. -/
theorem dvd_sq_add_iff_dvd_mul_add_one_sq (a b : ℕ) :
    (a + 1) * (b + 1) ∣ (a + b) ^ 2 ↔ (a + 1) * (b + 1) ∣ (a * b + 1) ^ 2 := by
  rw [← Int.natCast_dvd_natCast, ← Int.natCast_dvd_natCast]
  push_cast
  rw [show ((a : ℤ) * b + 1) ^ 2 =
      (a + b) ^ 2 + (a + 1) * (b + 1) * ((a + 1) * (b + 1) - 2 * (a + b)) by ring]
  exact (dvd_add_left (dvd_mul_right _ _)).symm

/-- Proposition 1, `Q` form: a crystal is a pair of odd numbers `a, b > 1` with
`(a + 1)(b + 1) ∣ (a + b)^2`. -/
theorem isCrystal_iff_dvd_sq_add {n a b : ℕ} :
    IsCrystalWithComponents n a b ↔
      Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ (a + 1) * (b + 1) ∣ (a + b) ^ 2 := by
  constructor
  · intro h
    have hodd := h.odd_left
    obtain ⟨hn, ha, hb, hab, hd⟩ := h
    exact ⟨hn, ha, hb, hab, (dvd_biharmonic_iff a b hodd).mp hd⟩
  · rintro ⟨hn, ha, hb, rfl, hd⟩
    exact ⟨hn, ha, hb, rfl, (dvd_biharmonic_iff a b (Nat.odd_mul.mp hn).1).mpr hd⟩

/-- Proposition 1, `F` form, written with `n`: `(a + 1)(b + 1) ∣ (n + 1)^2`. -/
theorem isCrystal_iff_dvd_succ_sq {n a b : ℕ} :
    IsCrystalWithComponents n a b ↔
      Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ (a + 1) * (b + 1) ∣ (n + 1) ^ 2 := by
  rw [isCrystal_iff_dvd_sq_add]
  constructor
  · rintro ⟨hn, ha, hb, rfl, hd⟩
    exact ⟨hn, ha, hb, rfl, (dvd_sq_add_iff_dvd_mul_add_one_sq a b).mp hd⟩
  · rintro ⟨hn, ha, hb, rfl, hd⟩
    exact ⟨hn, ha, hb, rfl, (dvd_sq_add_iff_dvd_mul_add_one_sq a b).mpr hd⟩

/-! ## The `(u, v)` form -/

private theorem int_uv (u v : ℤ) :
    u * v ∣ (u + v - 1) ^ 2 ↔ u ∣ (v - 1) ^ 2 ∧ v ∣ (u - 1) ^ 2 := by
  constructor
  · intro h
    constructor
    · rw [show (v - 1) ^ 2 = (u + v - 1) ^ 2 - u * (u + 2 * v - 2) by ring]
      exact dvd_sub (dvd_trans (dvd_mul_right u v) h) (dvd_mul_right _ _)
    · rw [show (u - 1) ^ 2 = (u + v - 1) ^ 2 - v * (v + 2 * u - 2) by ring]
      exact dvd_sub (dvd_trans (dvd_mul_left v u) h) (dvd_mul_right _ _)
  · rintro ⟨⟨x, hx⟩, hv⟩
    have hcop : IsCoprime u v := ⟨x, 2 - v, by linear_combination -hx⟩
    refine hcop.mul_dvd ?_ ?_
    · rw [show (u + v - 1) ^ 2 = (v - 1) ^ 2 + u * (u + 2 * v - 2) by ring]
      exact dvd_add ⟨x, hx⟩ (dvd_mul_right _ _)
    · rw [show (u + v - 1) ^ 2 = (u - 1) ^ 2 + v * (v + 2 * u - 2) by ring]
      exact dvd_add hv (dvd_mul_right _ _)

/-- With `a + 1 = 2u` and `b + 1 = 2v`, `(a + 1)(b + 1) ∣ (a + b)^2` is `uv ∣ (u + v - 1)^2`. -/
private theorem dvd_sq_add_iff_uv {a b u v : ℕ} (hu : a + 1 = 2 * u) (hv : b + 1 = 2 * v) :
    (a + 1) * (b + 1) ∣ (a + b) ^ 2 ↔ (u * v : ℤ) ∣ ((u : ℤ) + v - 1) ^ 2 := by
  rw [← Int.natCast_dvd_natCast]
  have hu' : (a : ℤ) = 2 * u - 1 := by omega
  have hv' : (b : ℤ) = 2 * v - 1 := by omega
  push_cast
  rw [hu', hv', show (2 * (u : ℤ) - 1 + 1) * (2 * v - 1 + 1) = 4 * (u * v) by ring,
    show (2 * (u : ℤ) - 1 + (2 * v - 1)) ^ 2 = 4 * ((u + v - 1) ^ 2) by ring,
    mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)]

/-- The `(u, v)` form with an integer divisibility: `uv ∣ (u + v - 1)^2`. -/
theorem isCrystal_iff_uv_dvd {n a b u v : ℕ} (hu : a + 1 = 2 * u) (hv : b + 1 = 2 * v) :
    IsCrystalWithComponents n a b ↔
      n = a * b ∧ 1 < u ∧ 1 < v ∧ (u * v : ℤ) ∣ ((u : ℤ) + v - 1) ^ 2 := by
  rw [isCrystal_iff_dvd_sq_add, dvd_sq_add_iff_uv hu hv]
  constructor
  · rintro ⟨-, ha, hb, rfl, hd⟩
    exact ⟨rfl, by omega, by omega, hd⟩
  · rintro ⟨rfl, h1, h2, hd⟩
    refine ⟨?_, by omega, by omega, rfl, hd⟩
    exact Nat.odd_mul.mpr ⟨⟨u - 1, by omega⟩, ⟨v - 1, by omega⟩⟩

/-- The `(u, v)` form: with `a + 1 = 2u` and `b + 1 = 2v`, `n = ab` is a crystal exactly when
`u, v > 1`, `u ∣ (v - 1)^2` and `v ∣ (u - 1)^2`.  (Then `gcd(u, v) = 1`.) -/
theorem isCrystal_iff_uv {n a b u v : ℕ} (hu : a + 1 = 2 * u) (hv : b + 1 = 2 * v) :
    IsCrystalWithComponents n a b ↔
      n = a * b ∧ 1 < u ∧ 1 < v ∧ u ∣ (v - 1) ^ 2 ∧ v ∣ (u - 1) ^ 2 := by
  rw [isCrystal_iff_uv_dvd hu hv]
  have h1 : 1 ≤ u := by omega
  have h2 : 1 ≤ v := by omega
  have key : (u ∣ (v - 1) ^ 2 ∧ v ∣ (u - 1) ^ 2) ↔ (u * v : ℤ) ∣ ((u : ℤ) + v - 1) ^ 2 := by
    rw [int_uv, ← Int.natCast_dvd_natCast, ← Int.natCast_dvd_natCast]
    push_cast [h1, h2]
    rfl
  rw [← key]

/-! ## The invariant `k = Q(a, b)` and the reduction to "`n` determines `k`" -/

/-- `Q(a, b) = (a + b)^2 / ((a + 1)(b + 1))`; for a crystal this is the paper's parameter `w`. -/
def crystalK (a b : ℕ) : ℕ := (a + b) ^ 2 / ((a + 1) * (b + 1))

theorem crystalK_comm (a b : ℕ) : crystalK a b = crystalK b a := by
  unfold crystalK
  rw [add_comm a b, mul_comm (a + 1)]

theorem IsCrystalWithComponents.sq_add_eq {n a b : ℕ} (h : IsCrystalWithComponents n a b) :
    (a + b) ^ 2 = crystalK a b * ((a + 1) * (b + 1)) :=
  (Nat.div_mul_cancel (isCrystal_iff_dvd_sq_add.mp h).2.2.2.2).symm

/-- With `s = a + b` and `k = Q(a, b)`: `s^2 = k (n + 1 + s)`. -/
theorem IsCrystalWithComponents.sq_add_eq_mul {n a b : ℕ} (h : IsCrystalWithComponents n a b) :
    (a + b) ^ 2 = crystalK a b * (n + 1 + (a + b)) := by
  rw [h.sq_add_eq, h.2.2.2.1]
  ring

theorem IsCrystalWithComponents.three_le_left {n a b : ℕ} (h : IsCrystalWithComponents n a b) :
    3 ≤ a := by
  obtain ⟨u, hu⟩ := h.odd_left
  have := h.2.1
  omega

theorem IsCrystalWithComponents.three_le_crystalK {n a b : ℕ}
    (h : IsCrystalWithComponents n a b) : 3 ≤ crystalK a b := by
  have e := h.sq_add_eq
  have ha := h.three_le_left
  have hb := h.symm.three_le_left
  by_contra hk
  have hk2 : crystalK a b ≤ 2 := by omega
  have : (a + b) ^ 2 ≤ 2 * ((a + 1) * (b + 1)) := by
    rw [e]
    exact Nat.mul_le_mul_right _ hk2
  nlinarith

/-- **Two crystal factorizations of the same `n` with the same `k` coincide.**  Both sums
`s = a + b` are the positive root of `s^2 = k (n + 1 + s)`, and `{a, b}` is fixed by `a + b` and
`ab`. -/
theorem eq_of_crystalK_eq {n a b c d : ℕ} (h1 : IsCrystalWithComponents n a b)
    (h2 : IsCrystalWithComponents n c d) (hk : crystalK a b = crystalK c d) :
    ({a, b} : Finset ℕ) = {c, d} := by
  have e1 := h1.sq_add_eq_mul
  have e2 := h2.sq_add_eq_mul
  rw [hk] at e1
  have hab := h1.2.2.2.1
  have hcd := h2.2.2.2.1
  have ha := h1.2.1
  have hb := h1.2.2.1
  have hc := h2.2.1
  have hd := h2.2.2.1
  have e1' : ((a : ℤ) + b) ^ 2 = crystalK c d * (n + 1 + (a + b)) := by exact_mod_cast e1
  have e2' : ((c : ℤ) + d) ^ 2 = crystalK c d * (n + 1 + (c + d)) := by exact_mod_cast e2
  have hs : (a : ℤ) + b = c + d := by
    have key : ((a : ℤ) + b - (c + d)) * ((a + b) + (c + d) - crystalK c d) = 0 := by
      linear_combination e1' - e2'
    rcases mul_eq_zero.mp key with h | h
    · linarith
    · exfalso
      have hk' : (crystalK c d : ℤ) = (a + b) + (c + d) := by linarith
      rw [hk'] at e2'
      have hpos : (0 : ℤ) < ((a : ℤ) + b) * ((n : ℤ) + 1) := by
        apply mul_pos <;> positivity
      have hnn : (0 : ℤ) ≤ ((a : ℤ) + b) * ((c : ℤ) + d) := by positivity
      have hnn' : (0 : ℤ) ≤ ((c : ℤ) + d) * ((n : ℤ) + 1) := by positivity
      nlinarith
  have hp : (a : ℤ) * b = c * d := by exact_mod_cast hab.symm.trans hcd
  have key : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by
    linear_combination (a : ℤ) * hs - hp
  rcases mul_eq_zero.mp key with h | h
  · have hac : a = c := by omega
    have hbd : b = d := by omega
    rw [hac, hbd]
  · have had : a = d := by omega
    have hbc : b = c := by omega
    rw [had, hbc, Finset.pair_comm]

/-- **The conjecture is equivalent to "`n` determines `k`"**: all crystal factorizations of the
same `n` have the same `k = Q(a, b) = (a + b)^2 / ((a + 1)(b + 1))`. -/
theorem statement_iff_crystalK_eq :
    statement ↔ ∀ n a b c d : ℕ, IsCrystalWithComponents n a b →
      IsCrystalWithComponents n c d → crystalK a b = crystalK c d := by
  constructor
  · intro hst n a b c d h1 h2
    have he := hst n a b c d h1 h2
    have hmem : a ∈ ({c, d} : Finset ℕ) := he ▸ Finset.mem_insert_self a {b}
    have hab := h1.2.2.2.1
    have hcd := h2.2.2.2.1
    have hc := h2.2.1
    have hd := h2.2.2.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · have hbd : b = d := by
        rw [h] at hab
        exact Nat.eq_of_mul_eq_mul_left (by omega) (hab.symm.trans hcd)
      rw [h, hbd]
    · have hbc : b = c := by
        rw [h] at hab
        exact Nat.eq_of_mul_eq_mul_left (by omega) (hab.symm.trans (hcd.trans (mul_comm c d)))
      rw [h, hbc, crystalK_comm]
  · intro hk n a b c d h1 h2
    exact eq_of_crystalK_eq h1 h2 (hk n a b c d h1 h2)

/-! ## Small `k` -/

/-- `k = 3` occurs only for `35 = 5 · 7`. -/
theorem IsCrystalWithComponents.eq_five_seven_of_crystalK_eq_three {n a b : ℕ}
    (h : IsCrystalWithComponents n a b) (hk : crystalK a b = 3) :
    (a = 5 ∧ b = 7) ∨ (a = 7 ∧ b = 5) := by
  have e := h.sq_add_eq
  rw [hk] at e
  have ha := h.2.1
  have hb := h.2.2.1
  have e' : ((a : ℤ) + b) ^ 2 = 3 * ((a + 1) * (b + 1)) := by exact_mod_cast e
  have hsum : (a : ℤ) + b ≤ 12 := by nlinarith [sq_nonneg ((a : ℤ) - b)]
  have ha' : a ≤ 12 := by omega
  have hb' : b ≤ 12 := by omega
  interval_cases a <;> interval_cases b <;> omega

/-- `35 = 5 · 7` is the only crystal factorization of `35`. -/
theorem IsCrystalWithComponents.eq_five_seven_of_eq_35 {a b : ℕ}
    (h : IsCrystalWithComponents 35 a b) : (a = 5 ∧ b = 7) ∨ (a = 7 ∧ b = 5) := by
  have hab := h.2.2.2.1
  have ha := h.2.1
  have hb := h.2.2.1
  have ha' : a ≤ 35 := by nlinarith
  interval_cases a <;> omega

/-- No other crystal shares `n` with a crystal of `k = 3`. -/
theorem eq_of_crystalK_eq_three {n a b c d : ℕ} (h1 : IsCrystalWithComponents n a b)
    (h2 : IsCrystalWithComponents n c d) (hk : crystalK a b = 3) :
    ({a, b} : Finset ℕ) = {c, d} := by
  have hab := h1.eq_five_seven_of_crystalK_eq_three hk
  have hn : n = 35 := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact h1.2.2.2.1
  subst hn
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h2.eq_five_seven_of_eq_35 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first | rfl | exact Finset.pair_comm _ _

/-! ## The recurrent-sequence classification (Theorems 4 and 5 of the paper) -/

/-- The paper's sequence `u_n(w)`: `u_0 = 0`, `u_1 = 1`, `u_{n+1} = (w - 2) u_n - u_{n-1} + 2`. -/
def seqU (w : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => (w - 2) * seqU w (n + 1) - seqU w n + 2

theorem seqU_add_two (w : ℤ) (n : ℕ) :
    seqU w (n + 2) = (w - 2) * seqU w (n + 1) - seqU w n + 2 := rfl

/-- Consecutive terms lie on the conic `(x + y - 1)^2 = w x y`. -/
theorem seqU_invariant (w : ℤ) (n : ℕ) :
    (seqU w (n + 1) + seqU w n - 1) ^ 2 = w * seqU w (n + 1) * seqU w n := by
  induction n with
  | zero => simp [seqU]
  | succ n ih =>
    rw [seqU_add_two]
    linear_combination ih

/-- Vieta descent: every positive solution of `(x + y - 1)^2 = w x y` is a pair of consecutive
terms of `u(w)` (Theorem 4 of the paper, up to order). -/
private theorem seqU_descent (w : ℤ) (s : ℕ) : ∀ x y : ℕ, x + y ≤ s → 0 < x → 0 < y →
    ((x : ℤ) + y - 1) ^ 2 = w * x * y →
    ∃ m : ℕ, ((x : ℤ) = seqU w (m + 2) ∧ (y : ℤ) = seqU w (m + 1)) ∨
      ((x : ℤ) = seqU w (m + 1) ∧ (y : ℤ) = seqU w (m + 2)) := by
  induction s with
  | zero => intro x y hs hx; omega
  | succ s ih =>
    intro x y hs hx hy he
    wlog hxy : x ≤ y generalizing x y
    · obtain ⟨m, hm⟩ := this y x (by omega) hy hx (by linear_combination he) (by omega)
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      exacts [⟨m, Or.inr ⟨h2, h1⟩⟩, ⟨m, Or.inl ⟨h2, h1⟩⟩]
    rcases Nat.lt_or_ge x 2 with hx1 | hx2
    · have hx1 : x = 1 := by omega
      subst hx1
      have hyw : (y : ℤ) = w := by
        have hy0 : (y : ℤ) ≠ 0 := by exact_mod_cast hy.ne'
        have : (y : ℤ) * y = w * y := by push_cast at he; linear_combination he
        exact mul_right_cancel₀ hy0 this
      exact ⟨0, Or.inr ⟨by simp [seqU], by simp [seqU, hyw]⟩⟩
    · have hprod : (y : ℤ) * ((w - 2) * x + 2 - y) = ((x : ℤ) - 1) ^ 2 := by
        linear_combination -he
      have hx2' : (2 : ℤ) ≤ x := by exact_mod_cast hx2
      have hy' : (0 : ℤ) < y := by exact_mod_cast hy
      have hxy' : (x : ℤ) ≤ y := by exact_mod_cast hxy
      have hpos : 0 < (w - 2) * x + 2 - y := by
        have h1 : (0 : ℤ) < ((x : ℤ) - 1) ^ 2 := by nlinarith
        nlinarith
      have hlt : (w - 2) * x + 2 - y < x := by nlinarith
      obtain ⟨y', hy'eq⟩ : ∃ y' : ℕ, (y' : ℤ) = (w - 2) * x + 2 - y :=
        ⟨((w - 2) * x + 2 - y).toNat, Int.toNat_of_nonneg hpos.le⟩
      have hy'lt : y' < x := by
        have : (y' : ℤ) < x := hy'eq ▸ hlt
        exact_mod_cast this
      have hy'pos : 0 < y' := by
        have : (0 : ℤ) < y' := hy'eq ▸ hpos
        exact_mod_cast this
      have he' : ((x : ℤ) + y' - 1) ^ 2 = w * x * y' := by
        rw [hy'eq]
        linear_combination he
      obtain ⟨m, hm⟩ := ih x y' (by omega) hx hy'pos he'
      rcases hm with ⟨hmx, hmy⟩ | ⟨hmx, hmy⟩
      · refine ⟨m + 1, Or.inr ⟨hmx, ?_⟩⟩
        have h2 : seqU w (m + 3) = (w - 2) * seqU w (m + 2) - seqU w (m + 1) + 2 :=
          seqU_add_two w (m + 1)
        show (y : ℤ) = seqU w (m + 3)
        linear_combination hy'eq + (w - 2) * hmx - hmy - h2
      · rcases m with _ | m
        · have h1 : seqU w (0 + 1) = 1 := rfl
          rw [h1] at hmx
          omega
        · have hmx' : (x : ℤ) = seqU w (m + 2) := hmx
          have hmy' : (y' : ℤ) = seqU w (m + 3) := hmy
          have h2 : seqU w (m + 3) = (w - 2) * seqU w (m + 2) - seqU w (m + 1) + 2 :=
            seqU_add_two w (m + 1)
          refine ⟨m, Or.inl ⟨hmx', ?_⟩⟩
          linear_combination hy'eq + (w - 2) * hmx' - hmy' - h2

/-- **Theorem 4 of the paper** (up to the order of the pair): the positive solutions of
`(x + y - 1)^2 = w x y` are exactly the pairs of consecutive terms of `u(w)`. -/
theorem sq_eq_mul_iff_seqU (w : ℤ) {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    ((x : ℤ) + y - 1) ^ 2 = w * x * y ↔
      ∃ m : ℕ, ((x : ℤ) = seqU w (m + 2) ∧ (y : ℤ) = seqU w (m + 1)) ∨
        ((x : ℤ) = seqU w (m + 1) ∧ (y : ℤ) = seqU w (m + 2)) := by
  refine ⟨seqU_descent w (x + y) x y le_rfl hx hy, ?_⟩
  rintro ⟨m, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> rw [h1, h2] <;>
    linear_combination seqU_invariant w (m + 1)

/-- Every crystal pair comes from the recurrence with `w = Q(a, b)`: `a + 1 = 2 u_{m+1}` and
`b + 1 = 2 u_{m+2}`, or the other way round. -/
theorem IsCrystalWithComponents.exists_seqU {n a b : ℕ} (h : IsCrystalWithComponents n a b) :
    ∃ m : ℕ, ((a : ℤ) + 1 = 2 * seqU (crystalK a b) (m + 1) ∧
        (b : ℤ) + 1 = 2 * seqU (crystalK a b) (m + 2)) ∨
      ((a : ℤ) + 1 = 2 * seqU (crystalK a b) (m + 2) ∧
        (b : ℤ) + 1 = 2 * seqU (crystalK a b) (m + 1)) := by
  obtain ⟨u, hu⟩ := h.odd_left
  obtain ⟨v, hv⟩ := h.odd_right
  have hu' : (a : ℤ) = 2 * u + 1 := by exact_mod_cast hu
  have hv' : (b : ℤ) = 2 * v + 1 := by exact_mod_cast hv
  have e : ((a : ℤ) + b) ^ 2 = crystalK a b * ((a + 1) * (b + 1)) := by exact_mod_cast h.sq_add_eq
  rw [hu', hv'] at e
  have he : (((u + 1 : ℕ) : ℤ) + (v + 1 : ℕ) - 1) ^ 2 =
      (crystalK a b : ℤ) * (u + 1 : ℕ) * (v + 1 : ℕ) := by
    push_cast
    have h4 : (4 : ℤ) * ((u + 1 + (v + 1) - 1) ^ 2) =
        4 * (crystalK a b * (u + 1) * (v + 1)) := by linear_combination e
    exact mul_left_cancel₀ (by norm_num) h4
  obtain ⟨m, hm⟩ := seqU_descent _ _ (u + 1) (v + 1) le_rfl (by omega) (by omega) he
  refine ⟨m, ?_⟩
  push_cast at hm
  rw [hu', hv']
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨by linear_combination 2 * h1, by linear_combination 2 * h2⟩
  · exact Or.inl ⟨by linear_combination 2 * h1, by linear_combination 2 * h2⟩

/-- **The classification of crystals** (Theorem 5 of the paper, up to the order of the pair):
`n = ab` is a crystal exactly when `(a + 1) / 2` and `(b + 1) / 2` are two consecutive terms, both
at least `2`, of `u(w)` for some integer `w`.  One can take `w = Q(a, b)`
(`IsCrystalWithComponents.exists_seqU`). -/
theorem isCrystal_iff_seqU {n a b : ℕ} :
    IsCrystalWithComponents n a b ↔ n = a * b ∧ ∃ (w : ℤ) (m : ℕ),
      2 ≤ seqU w (m + 1) ∧ 2 ≤ seqU w (m + 2) ∧
      (((a : ℤ) + 1 = 2 * seqU w (m + 1) ∧ (b : ℤ) + 1 = 2 * seqU w (m + 2)) ∨
        ((a : ℤ) + 1 = 2 * seqU w (m + 2) ∧ (b : ℤ) + 1 = 2 * seqU w (m + 1))) := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_seqU
    have ha := h.three_le_left
    have hb := h.symm.three_le_left
    refine ⟨h.2.2.2.1, crystalK a b, m, ?_, ?_, hm⟩ <;>
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  · rintro ⟨rfl, w, m, h1, h2, hab⟩
    have hu : a + 1 = 2 * ((a + 1) / 2) := by rcases hab with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    have hv : b + 1 = 2 * ((b + 1) / 2) := by rcases hab with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    rw [isCrystal_iff_uv_dvd hu hv]
    have inv := seqU_invariant w (m + 1)
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rcases hab with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    · rcases hab with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    · rcases hab with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · have e1 : (((a + 1) / 2 : ℕ) : ℤ) = seqU w (m + 1) := by omega
        have e2 : (((b + 1) / 2 : ℕ) : ℤ) = seqU w (m + 2) := by omega
        rw [e1, e2]
        exact ⟨w, by linear_combination inv⟩
      · have e1 : (((a + 1) / 2 : ℕ) : ℤ) = seqU w (m + 2) := by omega
        have e2 : (((b + 1) / 2 : ℕ) : ℤ) = seqU w (m + 1) := by omega
        rw [e1, e2]
        exact ⟨w, by linear_combination inv⟩

/-! ## Closed form through a Lucas sequence -/

/-- The Lucas sequence `L_0 = 0`, `L_1 = 1`, `L_{i+2} = c L_{i+1} - L_i`. -/
def lucas (c : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (i + 2) => c * lucas c (i + 1) - lucas c i

theorem lucas_add_two (c : ℤ) (i : ℕ) : lucas c (i + 2) = c * lucas c (i + 1) - lucas c i := rfl

/-- Consecutive terms satisfy `L_{i+1}^2 - c L_i L_{i+1} + L_i^2 = 1`. -/
theorem lucas_cassini (c : ℤ) (i : ℕ) :
    lucas c (i + 1) ^ 2 - c * lucas c i * lucas c (i + 1) + lucas c i ^ 2 = 1 := by
  induction i with
  | zero => simp [lucas]
  | succ i ih =>
    have h2 : lucas c (i + 1 + 1) = c * lucas c (i + 1) - lucas c i := lucas_add_two c i
    rw [h2]
    linear_combination ih

/-- For `c ≥ 2` the sequence is nonnegative and strictly increasing. -/
theorem lucas_nonneg_lt {c : ℤ} (hc : 2 ≤ c) (i : ℕ) :
    0 ≤ lucas c i ∧ lucas c i < lucas c (i + 1) := by
  induction i with
  | zero => simp [lucas]
  | succ i ih =>
    obtain ⟨h0, h1⟩ := ih
    have h2 : lucas c (i + 1 + 1) = c * lucas c (i + 1) - lucas c i := lucas_add_two c i
    refine ⟨by linarith, ?_⟩
    rw [h2]
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ c - 2) (by linarith : (0 : ℤ) ≤ lucas c (i + 1))]

/-- `u_{2i}(w) = w L_i^2` and `u_{2i+1}(w) = (L_i + L_{i+1})^2` with `L = lucas (w - 2)`. -/
theorem seqU_lucas (w : ℤ) (i : ℕ) :
    seqU w (2 * i) = w * lucas (w - 2) i ^ 2 ∧
      seqU w (2 * i + 1) = (lucas (w - 2) i + lucas (w - 2) (i + 1)) ^ 2 := by
  induction i with
  | zero => simp [seqU, lucas]
  | succ i ih =>
    obtain ⟨h0, h1⟩ := ih
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, show 2 * i + 2 + 1 = 2 * i + 3 by ring]
    have e2 : seqU w (2 * i + 2) = (w - 2) * seqU w (2 * i + 1) - seqU w (2 * i) + 2 :=
      seqU_add_two w (2 * i)
    have e3 : seqU w (2 * i + 3) = (w - 2) * seqU w (2 * i + 2) - seqU w (2 * i + 1) + 2 :=
      seqU_add_two w (2 * i + 1)
    have hl : lucas (w - 2) (i + 1 + 1) = (w - 2) * lucas (w - 2) (i + 1) - lucas (w - 2) i :=
      lucas_add_two (w - 2) i
    have hc := lucas_cassini (w - 2) i
    have h2 : seqU w (2 * i + 2) = w * lucas (w - 2) (i + 1) ^ 2 := by
      rw [e2, h0, h1]
      linear_combination (-2) * hc
    refine ⟨h2, ?_⟩
    rw [e3, h2, h1, hl]
    linear_combination (-2) * hc

/-- For `w ≥ 4`, a term `u_{m+1}(w) ≥ 2` and its successor are `w p^2` and `(p + r)^2`, in some
order, for positive `p, r` with `(p + r)^2 = w p r + 1`. -/
private theorem seqU_kpr {k : ℕ} (hk : 4 ≤ k) (m : ℕ) (h1 : 2 ≤ seqU k (m + 1)) :
    ∃ p r : ℕ, 0 < p ∧ 0 < r ∧ (p + r) ^ 2 = k * p * r + 1 ∧
      ((seqU k (m + 1) = k * (p : ℤ) ^ 2 ∧ seqU k (m + 2) = ((p : ℤ) + r) ^ 2) ∨
        (seqU k (m + 1) = ((p : ℤ) + r) ^ 2 ∧ seqU k (m + 2) = k * (p : ℤ) ^ 2)) := by
  have hc : (2 : ℤ) ≤ (k : ℤ) - 2 := by omega
  obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' (m + 1)
  · obtain ⟨hA, hB⟩ := seqU_lucas k i
    obtain ⟨hA0, hAB⟩ := lucas_nonneg_lt hc i
    have hcas := lucas_cassini ((k : ℤ) - 2) i
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = lucas ((k : ℤ) - 2) i := ⟨_, Int.toNat_of_nonneg hA0⟩
    obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = lucas ((k : ℤ) - 2) (i + 1) :=
      ⟨_, Int.toNat_of_nonneg (by linarith)⟩
    simp only [← hp, ← hr] at hA hB hcas hAB
    have hm1 : m + 1 = 2 * i := hi
    have hm2 : m + 2 = 2 * i + 1 := by omega
    rw [hm1, hA] at h1
    have hp0 : 0 < p := by
      rcases Nat.eq_zero_or_pos p with h0 | h0
      · subst h0; push_cast at h1; linarith
      · exact h0
    refine ⟨p, r, hp0, by omega, ?_, Or.inl ⟨by rw [hm1, hA], by rw [hm2, hB]⟩⟩
    have : ((p : ℤ) + r) ^ 2 = k * p * r + 1 := by linear_combination hcas
    exact_mod_cast this
  · obtain ⟨hA, hB⟩ := seqU_lucas k i
    have hC := (seqU_lucas k (i + 1)).1
    obtain ⟨hA0, hAB⟩ := lucas_nonneg_lt hc i
    have hcas := lucas_cassini ((k : ℤ) - 2) i
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = lucas ((k : ℤ) - 2) (i + 1) :=
      ⟨_, Int.toNat_of_nonneg (by linarith)⟩
    obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = lucas ((k : ℤ) - 2) i := ⟨_, Int.toNat_of_nonneg hA0⟩
    simp only [← hp, ← hr] at hA hB hcas hAB
    simp only [← hp] at hC
    have hm1 : m + 1 = 2 * i + 1 := hi
    have hm2 : m + 2 = 2 * (i + 1) := by omega
    rw [hm1, hB] at h1
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        push_cast at h1 hcas
        nlinarith
      · exact h0
    refine ⟨p, r, by omega, hr0, ?_, Or.inr ⟨by rw [hm1, hB]; ring, by rw [hm2, hC]⟩⟩
    have : ((p : ℤ) + r) ^ 2 = k * p * r + 1 := by linear_combination hcas
    exact_mod_cast this

/-- **Closed form of the classification.**  `n = ab` is a crystal exactly when
`{a + 1, b + 1} = {2 k p^2, 2 (p + r)^2}` for some `k` and positive `p, r` with
`(p + r)^2 = k p r + 1`.  (The solutions `(p, r)` are consecutive terms of `lucas (k - 2)`, and
`k = Q(a, b)` by `crystalK_eq_of_kpr`.) -/
theorem isCrystal_iff_kpr {n a b : ℕ} :
    IsCrystalWithComponents n a b ↔ n = a * b ∧ ∃ k p r : ℕ, 0 < p ∧ 0 < r ∧
      (p + r) ^ 2 = k * p * r + 1 ∧
      ((a + 1 = 2 * k * p ^ 2 ∧ b + 1 = 2 * (p + r) ^ 2) ∨
        (a + 1 = 2 * (p + r) ^ 2 ∧ b + 1 = 2 * k * p ^ 2)) := by
  constructor
  · intro h
    refine ⟨h.2.2.2.1, ?_⟩
    have hk3 := h.three_le_crystalK
    rcases Nat.lt_or_ge (crystalK a b) 4 with hk | hk
    · rcases h.eq_five_seven_of_crystalK_eq_three (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨3, 1, 1, by norm_num, by norm_num, by norm_num, Or.inl ⟨by norm_num, by norm_num⟩⟩
      · exact ⟨3, 1, 1, by norm_num, by norm_num, by norm_num, Or.inr ⟨by norm_num, by norm_num⟩⟩
    · obtain ⟨m, hm⟩ := h.exists_seqU
      have ha := h.three_le_left
      have hb := h.symm.three_le_left
      have h1 : 2 ≤ seqU (crystalK a b) (m + 1) := by
        rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      obtain ⟨p, r, hp, hr, hpr, hs⟩ := seqU_kpr hk m h1
      refine ⟨crystalK a b, p, r, hp, hr, hpr, ?_⟩
      rcases hm with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases hs with ⟨h5, h6⟩ | ⟨h5, h6⟩
      · exact Or.inl ⟨by zify; linear_combination h3 + 2 * h5,
          by zify; linear_combination h4 + 2 * h6⟩
      · exact Or.inr ⟨by zify; linear_combination h3 + 2 * h5,
          by zify; linear_combination h4 + 2 * h6⟩
      · exact Or.inr ⟨by zify; linear_combination h3 + 2 * h6,
          by zify; linear_combination h4 + 2 * h5⟩
      · exact Or.inl ⟨by zify; linear_combination h3 + 2 * h6,
          by zify; linear_combination h4 + 2 * h5⟩
  · rintro ⟨rfl, k, p, r, hp, hr, hpr, hab⟩
    have hk : 3 ≤ k := by
      by_contra hk
      have := Nat.mul_le_mul_right (p * r) (show k ≤ 2 by omega)
      nlinarith
    have hpr' : ((p : ℤ) + r) ^ 2 = k * p * r + 1 := by exact_mod_cast hpr
    have hu : 1 < k * p ^ 2 := by nlinarith
    have hv : 1 < (p + r) ^ 2 := by nlinarith
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [isCrystal_iff_uv_dvd (u := k * p ^ 2) (v := (p + r) ^ 2) (by rw [h1]; ring) h2]
      refine ⟨rfl, hu, hv, k, ?_⟩
      push_cast
      linear_combination (2 * k * p ^ 2 + ((p + r) ^ 2 - 1) + k * p * r) * hpr'
    · rw [isCrystal_iff_uv_dvd (u := (p + r) ^ 2) (v := k * p ^ 2) h1 (by rw [h2]; ring)]
      refine ⟨rfl, hv, hu, k, ?_⟩
      push_cast
      linear_combination (2 * k * p ^ 2 + ((p + r) ^ 2 - 1) + k * p * r) * hpr'

theorem crystalK_eq_of_sq_eq {a b k : ℕ} (h : (a + b) ^ 2 = k * ((a + 1) * (b + 1))) :
    crystalK a b = k := by
  unfold crystalK
  rw [h, Nat.mul_div_cancel _ (by positivity)]

/-- In the closed form, `k` is the invariant `Q(a, b)`. -/
theorem crystalK_eq_of_kpr {a b k p r : ℕ} (hpr : (p + r) ^ 2 = k * p * r + 1)
    (ha : a + 1 = 2 * k * p ^ 2) (hb : b + 1 = 2 * (p + r) ^ 2) : crystalK a b = k := by
  have hpr' : ((p : ℤ) + r) ^ 2 = k * p * r + 1 := by exact_mod_cast hpr
  have ha' : (a : ℤ) = 2 * k * p ^ 2 - 1 := by
    have : (a : ℤ) + 1 = 2 * k * p ^ 2 := by exact_mod_cast ha
    linarith
  have hb' : (b : ℤ) = 2 * (p + r) ^ 2 - 1 := by
    have : (b : ℤ) + 1 = 2 * (p + r) ^ 2 := by exact_mod_cast hb
    linarith
  apply crystalK_eq_of_sq_eq
  zify
  rw [ha', hb']
  linear_combination (4 * (2 * k * p ^ 2 + k * p * r + (p + r) ^ 2 - 1)) * hpr'

/-- Another reformulation: `n = ab` is a crystal exactly when `n + 1 = k q (q + 1)` and
`a + b = k (q + 1)` for some `k, q`.  (Then `a + b ∣ n + 1`, `q = (n + 1) / (a + b)` and
`k = Q(a, b)`.) -/
theorem isCrystal_iff_pronic {n a b : ℕ} :
    IsCrystalWithComponents n a b ↔ Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧
      ∃ k q : ℕ, n + 1 = k * q * (q + 1) ∧ a + b = k * (q + 1) := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    obtain ⟨hn, k, p, r, hp, hr, hpr, hab⟩ := isCrystal_iff_kpr.mp h
    obtain ⟨q, hq⟩ : ∃ q : ℕ, q + 1 = 2 * p * (p + r) :=
      ⟨2 * p * (p + r) - 1, by have : 0 < 2 * p * (p + r) := by positivity
                               omega⟩
    have hpr' : ((p : ℤ) + r) ^ 2 = k * p * r + 1 := by exact_mod_cast hpr
    have hq' : (q : ℤ) = 2 * p * (p + r) - 1 := by
      have : (q : ℤ) + 1 = 2 * p * (p + r) := by exact_mod_cast hq
      linarith
    have hab' : ((a : ℤ) = 2 * k * p ^ 2 - 1 ∧ (b : ℤ) = 2 * (p + r) ^ 2 - 1) ∨
        ((a : ℤ) = 2 * (p + r) ^ 2 - 1 ∧ (b : ℤ) = 2 * k * p ^ 2 - 1) := by
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; constructor <;> [zify at h1; zify at h2] <;> linarith
      · right; constructor <;> [zify at h1; zify at h2] <;> linarith
    refine ⟨k, q, ?_, ?_⟩
    · rw [hn]
      zify
      rw [hq']
      rcases hab' with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> rw [ha', hb'] <;>
        linear_combination (-2) * hpr'
    · zify
      rw [hq']
      rcases hab' with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ <;> rw [ha', hb'] <;>
        linear_combination 2 * hpr'
  · rintro ⟨hodd, ha, hb, hn, k, q, h1, h2⟩
    refine isCrystal_iff_dvd_sq_add.mpr ⟨hodd, ha, hb, hn, k, ?_⟩
    have e : (a + 1) * (b + 1) = k * (q + 1) ^ 2 := by
      have : (a + 1) * (b + 1) = (a * b + 1) + (a + b) := by ring
      rw [this, ← hn, h1, h2]
      ring
    rw [e, h2]
    ring

/-! ## Families, and the cases in which `n` determines `k` -/

/-- `k = 4` exactly for the consecutive squares: `{(a + 1)/2, (b + 1)/2} = {t^2, (t + 1)^2}`. -/
theorem IsCrystalWithComponents.crystalK_eq_four_iff {n a b : ℕ}
    (h : IsCrystalWithComponents n a b) :
    crystalK a b = 4 ↔ ∃ t : ℕ, 2 ≤ t ∧ ((a + 1 = 2 * t ^ 2 ∧ b + 1 = 2 * (t + 1) ^ 2) ∨
      (a + 1 = 2 * (t + 1) ^ 2 ∧ b + 1 = 2 * t ^ 2)) := by
  constructor
  · intro hk
    obtain ⟨-, k, p, r, hp, hr, hpr, hab⟩ := isCrystal_iff_kpr.mp h
    have hk' : k = 4 := by
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← crystalK_eq_of_kpr hpr h1 h2, hk]
      · rw [← crystalK_eq_of_kpr hpr h2 h1, crystalK_comm, hk]
    subst hk'
    have hd : ((p : ℤ) - r - 1) * ((p : ℤ) - r + 1) = 0 := by
      have : ((p : ℤ) + r) ^ 2 = 4 * p * r + 1 := by exact_mod_cast hpr
      linear_combination this
    rcases mul_eq_zero.mp hd with hd | hd
    · obtain rfl : p = r + 1 := by omega
      refine ⟨2 * r + 1, by omega, ?_⟩
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨by rw [h1]; ring, by rw [h2]; ring⟩
      · exact Or.inl ⟨by rw [h1]; ring, by rw [h2]; ring⟩
    · obtain rfl : r = p + 1 := by omega
      refine ⟨2 * p, by omega, ?_⟩
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [h1]; ring, by rw [h2]; ring⟩
      · exact Or.inr ⟨by rw [h1]; ring, by rw [h2]; ring⟩
  · rintro ⟨t, -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> apply crystalK_eq_of_sq_eq
    · have ha' : (a : ℤ) = 2 * t ^ 2 - 1 := by
        have : (a : ℤ) + 1 = 2 * t ^ 2 := by exact_mod_cast h1
        linarith
      have hb' : (b : ℤ) = 2 * (t + 1) ^ 2 - 1 := by
        have : (b : ℤ) + 1 = 2 * (t + 1) ^ 2 := by exact_mod_cast h2
        linarith
      zify
      rw [ha', hb']
      ring
    · have ha' : (a : ℤ) = 2 * (t + 1) ^ 2 - 1 := by
        have : (a : ℤ) + 1 = 2 * (t + 1) ^ 2 := by exact_mod_cast h1
        linarith
      have hb' : (b : ℤ) = 2 * t ^ 2 - 1 := by
        have : (b : ℤ) + 1 = 2 * t ^ 2 := by exact_mod_cast h2
        linarith
      zify
      rw [ha', hb']
      ring

/-- The `j = 1` crystals: if `a + 1 = 2k` with `k = Q(a, b)`, then `b + 1 = 2 (k - 1)^2`. -/
theorem IsCrystalWithComponents.j1 {n a b : ℕ} (h : IsCrystalWithComponents n a b)
    (ha : a + 1 = 2 * crystalK a b) : b + 1 = 2 * (crystalK a b - 1) ^ 2 := by
  have hk := h.three_le_crystalK
  have hb := h.2.2.1
  have e : ((a : ℤ) + b) ^ 2 = crystalK a b * ((a + 1) * (b + 1)) := by
    exact_mod_cast h.sq_add_eq
  have ha' : (a : ℤ) = 2 * crystalK a b - 1 := by
    have : (a : ℤ) + 1 = 2 * crystalK a b := by exact_mod_cast ha
    linarith
  rw [ha'] at e
  have key : ((b : ℤ) - 1) * (b + 1 - 2 * ((crystalK a b : ℤ) - 1) ^ 2) = 0 := by
    linear_combination e
  rcases mul_eq_zero.mp key with h1 | h1
  · omega
  · have : ((b + 1 : ℕ) : ℤ) = ((2 * (crystalK a b - 1) ^ 2 : ℕ) : ℤ) := by
      push_cast [show 1 ≤ crystalK a b by omega]
      linarith
    exact_mod_cast this

/-- **Two `j = 1` crystals of the same `n` coincide**: on this family
`n = (2k - 1)(2(k - 1)^2 - 1)` is strictly increasing in `k`. -/
theorem eq_of_j1 {n a b c d : ℕ} (h1 : IsCrystalWithComponents n a b)
    (h2 : IsCrystalWithComponents n c d) (ha : a + 1 = 2 * crystalK a b)
    (hc : c + 1 = 2 * crystalK c d) : ({a, b} : Finset ℕ) = {c, d} := by
  apply eq_of_crystalK_eq h1 h2
  have hb := h1.j1 ha
  have hd := h2.j1 hc
  have hab := h1.2.2.2.1
  have hcd := h2.2.2.2.1
  have hk1 := h1.three_le_crystalK
  have hk2 := h2.three_le_crystalK
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hac : a < c := by omega
    have hbd : b < d := by
      have := Nat.pow_lt_pow_left (show crystalK a b - 1 < crystalK c d - 1 by omega)
        (two_ne_zero)
      omega
    have : a * b < c * d := Nat.mul_lt_mul'' hac hbd
    omega
  · have hac : c < a := by omega
    have hbd : d < b := by
      have := Nat.pow_lt_pow_left (show crystalK c d - 1 < crystalK a b - 1 by omega)
        (two_ne_zero)
      omega
    have : c * d < a * b := Nat.mul_lt_mul'' hac hbd
    omega

/-! ## `k = 4` against `j = 1`, conditional on an elliptic curve -/

/-- Every integral point of the elliptic curve `y^2 = x^3 - 10 x^2 + 24 x + 16` (conductor
`2432`) has `x ∈ {0, 3, 4, 6, 10, 16, 19, 84, 1200}`.  This is the output of a Sage/PARI
computation (`problems/crystal-components-unique/ec_k4_j1.py`: rank 2, generators by
saturation, integral points by elliptic logarithms).  It is **not** proved in Lean and is used
only as the hypothesis of `eq_of_crystalK_eq_four_of_j1`. -/
def EllipticCurveIntegralPoints : Prop :=
  ∀ x y : ℤ, y ^ 2 = x ^ 3 - 10 * x ^ 2 + 24 * x + 16 →
    x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 6 ∨ x = 10 ∨ x = 16 ∨ x = 19 ∨ x = 84 ∨ x = 1200

/-- **`k = 4` against `j = 1`, assuming `EllipticCurveIntegralPoints`**: a crystal of the `k = 4`
family and a `j = 1` crystal with the same `n` coincide (both are `119 = 7 · 17`).  With
`X = t (t + 1)` and `K = Q(c, d)`, the equation `(2t^2 - 1)(2(t + 1)^2 - 1) =
(2K - 1)(2(K - 1)^2 - 1)` reads `(2X - 1)^2 = 4K^3 - 10K^2 + 6K + 1`, so `(4K, 4(2X - 1))` is
an integral point of the curve; `K = 21` and `K = 300` give `X = 91` and `X = 5175`, which are
not of the form `t (t + 1)`. -/
theorem eq_of_crystalK_eq_four_of_j1 (hE : EllipticCurveIntegralPoints) {n a b c d : ℕ}
    (h1 : IsCrystalWithComponents n a b) (h2 : IsCrystalWithComponents n c d)
    (hk : crystalK a b = 4) (hc : c + 1 = 2 * crystalK c d) :
    ({a, b} : Finset ℕ) = {c, d} := by
  apply eq_of_crystalK_eq h1 h2
  rw [hk]
  obtain ⟨t, -, hab⟩ := h1.crystalK_eq_four_iff.mp hk
  have hd := h2.j1 hc
  have hK := h2.three_le_crystalK
  have hn : (a : ℤ) * b = c * d := by
    have e1 := h1.2.2.2.1
    have e2 := h2.2.2.2.1
    exact_mod_cast e1.symm.trans e2
  have hab' : (a : ℤ) * b = (2 * (t : ℤ) ^ 2 - 1) * (2 * ((t : ℤ) + 1) ^ 2 - 1) := by
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ha' : (a : ℤ) + 1 = 2 * (t : ℤ) ^ 2 := by exact_mod_cast ha
      have hb' : (b : ℤ) + 1 = 2 * ((t : ℤ) + 1) ^ 2 := by exact_mod_cast hb
      linear_combination (2 * ((t : ℤ) + 1) ^ 2 - 1) * ha' + (a : ℤ) * hb'
    · have ha' : (a : ℤ) + 1 = 2 * ((t : ℤ) + 1) ^ 2 := by exact_mod_cast ha
      have hb' : (b : ℤ) + 1 = 2 * (t : ℤ) ^ 2 := by exact_mod_cast hb
      linear_combination (2 * (t : ℤ) ^ 2 - 1) * ha' + (a : ℤ) * hb'
  have hcd' : (c : ℤ) * d =
      (2 * (crystalK c d : ℤ) - 1) * (2 * ((crystalK c d : ℤ) - 1) ^ 2 - 1) := by
    have hc' : (c : ℤ) + 1 = 2 * (crystalK c d : ℤ) := by exact_mod_cast hc
    have hd' : (d : ℤ) + 1 = 2 * ((crystalK c d - 1 : ℕ) : ℤ) ^ 2 := by exact_mod_cast hd
    push_cast [show 1 ≤ crystalK c d by omega] at hd'
    linear_combination (2 * ((crystalK c d : ℤ) - 1) ^ 2 - 1) * hc' + (c : ℤ) * hd'
  have heq : (2 * ((t : ℤ) * (t + 1)) - 1) ^ 2 =
      4 * (crystalK c d : ℤ) ^ 3 - 10 * (crystalK c d : ℤ) ^ 2 + 6 * crystalK c d + 1 := by
    linear_combination hn - hab' + hcd'
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have hX : 0 ≤ (t : ℤ) * (t + 1) := by positivity
  rcases hE (4 * crystalK c d) (4 * (2 * ((t : ℤ) * (t + 1)) - 1)) (by linear_combination 16 * heq)
    with h | h | h | h | h | h | h | h | h <;> try omega
  · -- `K = 21`: `X = 91`
    rw [show (crystalK c d : ℤ) = 21 by omega] at heq
    have hm : (2 * ((t : ℤ) * (t + 1)) - 1 - 181) * (2 * ((t : ℤ) * (t + 1)) - 1 + 181) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hm with hm | hm
    · rcases le_or_gt (t : ℤ) 9 with ht | ht <;> nlinarith
    · linarith
  · -- `K = 300`: `X = 5175`
    rw [show (crystalK c d : ℤ) = 300 by omega] at heq
    have hm :
        (2 * ((t : ℤ) * (t + 1)) - 1 - 10349) * (2 * ((t : ℤ) * (t + 1)) - 1 + 10349) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hm with hm | hm
    · rcases le_or_gt (t : ℤ) 71 with ht | ht <;> nlinarith
    · linarith

end AgenticConjectures.CrystalComponentsUnique
