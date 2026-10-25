import AgenticConjectures.AdditiveSinkWallDuality.Games

/-!
# Additive sink–wall duality: the explicit wall `𝒫`-set and its two gaps

Fix `1 ≤ a < b`. Write every integer as `y = 2a·Y + ρ` with `0 ≤ ρ < 2a`, and put

* `E = {y : ρ < a}` (the residues `0, …, a - 1` modulo `2a`),
* `κ(y) = a·Y + min(a, ρ)` (for `y ≥ 0`, the number of elements of `E` in `[0, y)`),
* `N = κ(b)`, `φ(y) = ⌊κ(y) / N⌋` and `Φ(y) = y + b·φ(y)`,
* `W = Φ(E) = {x : ∃ j, x - j·b ∈ E ∧ φ(x - j·b) = j}`.

For `n ≥ 0` the `n`-th element of `E` is `n + a⌊n/a⌋`, so `W ∩ ℕ` is the set of the numbers
`n + a⌊n/a⌋ + b⌊n/N⌋`: the classical bracket formula for the `𝒫`-positions of additive wall
subtraction. This file does not use that formula's known proofs. It proves the facts about `W`
that the main proof needs:

* `W_indep`: no two elements of `W` differ by `a`, `b` or `a + b`;
* `W_cover`: for every `x`, one of `x`, `x - a`, `x - b`, `x - (a + b)` lies in `W`;
* `W_neg_gap`, `W_top_gap`: `W` misses `[-(a + b), -1]` and `[p - (a + b), p - 1]`, where `p` is
  the period of Bhagat–Larsson–Manabe–Yamashita (`period`, defined by their formula);
* `period_gt`: `a + b < p`.

Both gaps come from `Explicit.not_W_of_gap`: no element of `E` lies strictly between
`2aM - a - 1` and `2aM`, and `Φ` is strictly increasing. For the lower gap `M = 0`, with
`Φ(-a - 1) = -(a + b) - 1` and `Φ(0) = 0`. For the upper gap, `Explicit.period_spec` writes
`p = 2Q + k·b` with `Q = a·ℓ = k·N` and `ℓ, k ≥ 1` (the proof takes `g = gcd(a, N)`,
`Q = a·N/g` and `k = a/g`); then `M = ℓ`, `Φ(2Q - a - 1) = p - (a + b) - 1` and `Φ(2Q) = p`.
-/

namespace AgenticConjectures.AdditiveSinkWallDuality

namespace Explicit

/-- `E a y`: the residue of `y` modulo `2a` is less than `a`. -/
def E (a : ℕ) (y : ℤ) : Prop :=
  y % (2 * (a : ℤ)) < a

/-- `κ(y) = a⌊y / 2a⌋ + min(a, y mod 2a)`. -/
def kappa (a : ℕ) (y : ℤ) : ℤ :=
  a * (y / (2 * (a : ℤ))) + min (a : ℤ) (y % (2 * (a : ℤ)))

/-- `N = κ(b) = a⌊b / 2a⌋ + min(a, b mod 2a)`. -/
def N (a b : ℕ) : ℤ :=
  kappa a b

/-- `φ(y) = ⌊κ(y) / N⌋`. -/
def phi (a b : ℕ) (y : ℤ) : ℤ :=
  kappa a y / N a b

/-- `Φ(y) = y + b·φ(y)`. -/
def Phi (a b : ℕ) (y : ℤ) : ℤ :=
  y + b * phi a b y

end Explicit

open Explicit

/-- The explicit set `W = Φ(E)`. -/
def W (a b : ℕ) (x : ℤ) : Prop :=
  ∃ j : ℤ, E a (x - j * b) ∧ phi a b (x - j * b) = j

namespace Explicit

variable {a b : ℕ}

/-! ### Arithmetic helpers -/

private theorem no_mult {A Z m : ℤ} (hA : 0 < A) (h1 : A * Z < A * m) (h2 : A * m < A * Z + A) :
    False := by
  have h3 := Int.lt_of_mul_lt_mul_left h1 hA.le
  have h4 : A * (Z + 1) ≤ A * m := Int.mul_le_mul_of_nonneg_left (by omega) hA.le
  rw [mul_add, mul_one] at h4
  omega

private theorem mult_eq {A Z m : ℤ} (hA : 0 < A) (h1 : A * Z < A * m) (h2 : A * m ≤ A * Z + A) :
    A * m = A * Z + A := by
  have h3 := Int.lt_of_mul_lt_mul_left h1 hA.le
  have h4 : A * (Z + 1) ≤ A * m := Int.mul_le_mul_of_nonneg_left (by omega) hA.le
  rw [mul_add, mul_one] at h4
  omega

/-! ### Decompositions modulo `2a` -/

theorem decomp (ha : 1 ≤ a) (y : ℤ) :
    ∃ Y ρ : ℤ, y = 2 * (a * Y) + ρ ∧ 0 ≤ ρ ∧ ρ < 2 * a := by
  refine ⟨y / (2 * a), y % (2 * a), ?_, Int.emod_nonneg _ (by omega),
    Int.emod_lt_of_pos _ (by omega)⟩
  have := Int.mul_ediv_add_emod y (2 * (a : ℤ))
  linear_combination -this

theorem kappa_eq (ha : 1 ≤ a) {y Y ρ : ℤ} (h : y = 2 * (a * Y) + ρ) (h0 : 0 ≤ ρ)
    (h1 : ρ < 2 * a) : kappa a y = a * Y + min (a : ℤ) ρ := by
  obtain ⟨hq, hr⟩ := (Int.ediv_emod_unique (a := y) (q := Y) (r := ρ)
    (by omega : (0 : ℤ) < 2 * a)).2 ⟨by linear_combination -h, h0, h1⟩
  simp only [kappa, hq, hr]

theorem E_iff (ha : 1 ≤ a) {y Y ρ : ℤ} (h : y = 2 * (a * Y) + ρ) (h0 : 0 ≤ ρ)
    (h1 : ρ < 2 * a) : E a y ↔ ρ < a := by
  obtain ⟨-, hr⟩ := (Int.ediv_emod_unique (a := y) (q := Y) (r := ρ)
    (by omega : (0 : ℤ) < 2 * a)).2 ⟨by linear_combination -h, h0, h1⟩
  simp only [E, hr]

/-- The decomposition `b = 2a·q + r` and what it says about `N` (fact F0 and its relatives). -/
theorem b_decomp (ha : 1 ≤ a) (hab : a < b) :
    ∃ q r : ℤ, (b : ℤ) = 2 * (a * q) + r ∧ 0 ≤ r ∧ r < 2 * a ∧
      N a b = a * q + min (a : ℤ) r ∧ 0 ≤ a * q ∧ (r < a → a ≤ a * q) := by
  obtain ⟨q, r, hb, hr0, hr1⟩ := decomp ha b
  refine ⟨q, r, hb, hr0, hr1, kappa_eq ha hb hr0 hr1, ?_⟩
  have hA : (0 : ℤ) < a := by omega
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · have : (a : ℤ) * q ≤ a * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) hA.le
    omega
  · simp only [mul_zero]
    omega
  · have : (a : ℤ) * 1 ≤ a * q := Int.mul_le_mul_of_nonneg_left (by omega) hA.le
    omega

theorem N_ge (ha : 1 ≤ a) (hab : a < b) : (a : ℤ) ≤ N a b := by
  obtain ⟨q, r, -, hr0, hr1, hN, hq0, hq1⟩ := b_decomp ha hab
  omega

theorem N_pos (ha : 1 ≤ a) (hab : a < b) : 0 < N a b := by
  have := N_ge ha hab
  omega

/-! ### `φ` as a floor -/

theorem le_phi_iff (ha : 1 ≤ a) (hab : a < b) {y j : ℤ} :
    j ≤ phi a b y ↔ j * N a b ≤ kappa a y :=
  Int.le_ediv_iff_mul_le (N_pos ha hab)

theorem phi_lt_iff (ha : 1 ≤ a) (hab : a < b) {y j : ℤ} :
    phi a b y < j ↔ kappa a y < j * N a b :=
  Int.ediv_lt_iff_lt_mul (N_pos ha hab)

theorem phi_eq_iff (ha : 1 ≤ a) (hab : a < b) {y j : ℤ} :
    phi a b y = j ↔ j * N a b ≤ kappa a y ∧ kappa a y < j * N a b + N a b := by
  have h1 := le_phi_iff ha hab (y := y) (j := j)
  have h2 := phi_lt_iff ha hab (y := y) (j := j + 1)
  rw [show (j + 1) * N a b = j * N a b + N a b by ring] at h2
  constructor
  · intro h
    exact ⟨h1.1 h.ge, h2.1 (by omega)⟩
  · rintro ⟨hl, hr⟩
    have := h1.2 hl
    have := h2.2 hr
    omega

/-- If `κ` grows by at least `N`, then `φ` grows. -/
theorem phi_lt_of_kappa (ha : 1 ≤ a) (hab : a < b) {u v : ℤ}
    (h : kappa a v + N a b ≤ kappa a u) : phi a b v < phi a b u := by
  obtain ⟨h1, -⟩ := (phi_eq_iff ha hab (y := v)).1 rfl
  have : (phi a b v + 1) * N a b ≤ kappa a u := by linarith
  have := (le_phi_iff ha hab).2 this
  omega

/-- F5: if `κ` grows by between `0` and `N`, then `φ` grows by `0` or `1`. -/
theorem phi_step (ha : 1 ≤ a) (hab : a < b) {u v : ℤ} (h0 : kappa a v ≤ kappa a u)
    (h1 : kappa a u ≤ kappa a v + N a b) :
    phi a b v ≤ phi a b u ∧ phi a b u ≤ phi a b v + 1 := by
  obtain ⟨h2, h3⟩ := (phi_eq_iff ha hab (y := v)).1 rfl
  constructor
  · exact (le_phi_iff ha hab).2 (by omega)
  · have : kappa a u < (phi a b v + 2) * N a b := by linarith
    have := (phi_lt_iff ha hab).2 this
    omega

/-! ### Elementary facts F1–F4 -/

/-- F1: `κ` never decreases. -/
theorem kappa_le_succ (ha : 1 ≤ a) (y : ℤ) : kappa a y ≤ kappa a (y + 1) := by
  obtain ⟨Y, ρ, hy, h0, h1⟩ := decomp ha y
  rw [kappa_eq ha hy h0 h1]
  by_cases hρ : ρ + 1 < 2 * a
  · rw [kappa_eq ha (Y := Y) (ρ := ρ + 1) (by rw [hy]; ring) (by omega) hρ]
    omega
  · have hρ' : ρ = 2 * a - 1 := by omega
    rw [kappa_eq ha (Y := Y + 1) (ρ := 0) (by rw [hy, hρ']; ring) le_rfl (by omega), mul_add,
      mul_one]
    omega

theorem kappa_mono (ha : 1 ≤ a) : Monotone (kappa a) :=
  monotone_int_of_le_succ (kappa_le_succ ha)

theorem phi_mono (ha : 1 ≤ a) (hab : a < b) {y y' : ℤ} (h : y ≤ y') :
    phi a b y ≤ phi a b y' :=
  Int.ediv_le_ediv (N_pos ha hab) (kappa_mono ha h)

theorem Phi_strictMono (ha : 1 ≤ a) (hab : a < b) : StrictMono (Phi a b) := by
  intro y y' h
  have := phi_mono ha hab h.le
  have : (b : ℤ) * phi a b y ≤ b * phi a b y' := Int.mul_le_mul_of_nonneg_left this (by omega)
  simp only [Phi]
  omega

/-- F2: exactly one of `y` and `y - a` lies in `E`. -/
theorem E_sub_a (ha : 1 ≤ a) (y : ℤ) : E a (y - a) ↔ ¬ E a y := by
  obtain ⟨Y, ρ, hy, h0, h1⟩ := decomp ha y
  rw [E_iff ha hy h0 h1]
  by_cases hρ : ρ < a
  · rw [E_iff ha (Y := Y - 1) (ρ := ρ + a) (by rw [hy]; ring) (by omega) (by omega)]
    omega
  · rw [E_iff ha (Y := Y) (ρ := ρ - a) (by rw [hy]; ring) (by omega) (by omega)]
    omega

theorem not_E_add_a (ha : 1 ≤ a) {e : ℤ} (h : E a e) : ¬ E a (e + a) := by
  have := E_sub_a ha (e + a)
  rw [add_sub_cancel_right] at this
  tauto

/-- F3: `0 ≤ κ(y) - κ(y - a) ≤ a`. -/
theorem kappa_sub_a (ha : 1 ≤ a) (y : ℤ) :
    kappa a (y - a) ≤ kappa a y ∧ kappa a y ≤ kappa a (y - a) + a := by
  obtain ⟨Y, ρ, hy, h0, h1⟩ := decomp ha y
  rw [kappa_eq ha hy h0 h1]
  by_cases hρ : ρ < a
  · rw [kappa_eq ha (Y := Y - 1) (ρ := ρ + a) (by rw [hy]; ring) (by omega) (by omega),
      mul_sub, mul_one]
    omega
  · rw [kappa_eq ha (Y := Y) (ρ := ρ - a) (by rw [hy]; ring) (by omega) (by omega)]
    omega

/-- F4: `0 ≤ κ(y) - κ(y - b) ≤ N`. -/
theorem kappa_sub_b (ha : 1 ≤ a) (hab : a < b) (y : ℤ) :
    kappa a (y - b) ≤ kappa a y ∧ kappa a y ≤ kappa a (y - b) + N a b := by
  obtain ⟨q, r, hb, hr0, hr1, hN, hq0, hq1⟩ := b_decomp ha hab
  obtain ⟨Y, ρ, hy, h0, h1⟩ := decomp ha y
  rw [kappa_eq ha hy h0 h1, hN]
  by_cases hρ : r ≤ ρ
  · rw [kappa_eq ha (Y := Y - q) (ρ := ρ - r) (by rw [hy, hb]; ring) (by omega) (by omega),
      mul_sub]
    omega
  · rw [kappa_eq ha (Y := Y - q - 1) (ρ := 2 * a + ρ - r) (by rw [hy, hb]; ring) (by omega)
      (by omega), mul_sub, mul_sub, mul_one]
    omega

theorem phi_sub_a (ha : 1 ≤ a) (hab : a < b) (y : ℤ) :
    phi a b (y - a) ≤ phi a b y ∧ phi a b y ≤ phi a b (y - a) + 1 := by
  obtain ⟨h0, h1⟩ := kappa_sub_a ha y
  have := N_ge ha hab
  exact phi_step ha hab h0 (by omega)

theorem phi_sub_b (ha : 1 ≤ a) (hab : a < b) (y : ℤ) :
    phi a b (y - b) ≤ phi a b y ∧ phi a b y ≤ phi a b (y - b) + 1 := by
  obtain ⟨h0, h1⟩ := kappa_sub_b ha hab y
  exact phi_step ha hab h0 h1

/-! ### Facts F6–F8 -/

/-- F6: if `y` and `y - b` both lie in `E`, then `φ(y - b) < φ(y)`. -/
theorem phi_sub_b_lt (ha : 1 ≤ a) (hab : a < b) {y : ℤ} (hy : E a y) (hyb : E a (y - b)) :
    phi a b (y - b) < phi a b y := by
  obtain ⟨q, r, hb, hr0, hr1, hN, hq0, hq1⟩ := b_decomp ha hab
  obtain ⟨Z, τ, hz, hτ0, hτ1⟩ := decomp ha (y - b)
  have hτ : τ < a := (E_iff ha hz hτ0 hτ1).1 hyb
  have hκz := kappa_eq ha hz hτ0 hτ1
  by_cases hc : τ + r < 2 * a
  · have hy' : y = 2 * (a * (Z + q)) + (τ + r) := by linear_combination hz + hb
    have hσ : τ + r < a := (E_iff ha hy' (by omega) hc).1 hy
    have hκy := kappa_eq ha hy' (by omega) hc
    rw [mul_add] at hκy
    exact phi_lt_of_kappa ha hab (by rw [hκy, hκz, hN]; omega)
  · have hy' : y = 2 * (a * (Z + q + 1)) + (τ + r - 2 * a) := by linear_combination hz + hb
    have hκy := kappa_eq ha hy' (by omega) (by omega)
    rw [mul_add, mul_add, mul_one] at hκy
    have hN' : N a b = a * (q + 1) := by rw [hN, mul_add, mul_one]; omega
    have hm : phi a b y * N a b = a * (phi a b y * (q + 1)) := by rw [hN']; ring
    have hN'' : N a b = a * q + a := by rw [hN']; ring
    by_contra hlt
    have hle := phi_mono ha hab (show y - b ≤ y by omega)
    obtain ⟨h1, -⟩ := (phi_eq_iff ha hab (y := y - b)).1 rfl
    obtain ⟨-, h2⟩ := (phi_eq_iff ha hab (y := y)).1 rfl
    have heq : phi a b (y - b) = phi a b y := by omega
    rw [heq] at h1
    exact no_mult (A := a) (Z := Z) (m := phi a b y * (q + 1)) (by omega) (by omega) (by omega)

/-- F7: if `y` and `y - (a + b)` both lie in `E`, then `φ(y - (a + b)) < φ(y)`. -/
theorem phi_sub_c_lt (ha : 1 ≤ a) (hab : a < b) {y : ℤ} (hy : E a y)
    (hyc : E a (y - (a + b))) : phi a b (y - (a + b)) < phi a b y := by
  obtain ⟨q, r, hb, hr0, hr1, hN, hq0, hq1⟩ := b_decomp ha hab
  obtain ⟨Z, τ, hz, hτ0, hτ1⟩ := decomp ha (y - (a + b))
  have hτ : τ < a := (E_iff ha hz hτ0 hτ1).1 hyc
  have hκz := kappa_eq ha hz hτ0 hτ1
  by_cases hc : τ + a + r < 2 * a
  · have hy' : y = 2 * (a * (Z + q)) + (τ + a + r) := by linear_combination hz + hb
    have := (E_iff ha hy' (by omega) hc).1 hy
    omega
  · have hy' : y = 2 * (a * (Z + q + 1)) + (τ + r - a) := by linear_combination hz + hb
    have hσ : τ + r - a < a := (E_iff ha hy' (by omega) (by omega)).1 hy
    have hκy := kappa_eq ha hy' (by omega) (by omega)
    rw [mul_add, mul_add, mul_one] at hκy
    exact phi_lt_of_kappa ha hab (by rw [hκy, hκz, hN]; omega)

/-- F8: if `y ∉ E` and `φ(y - a) < φ(y) < φ(y + b)`, then `y + b - a ∈ E` and
`φ(y + b - a) = φ(y)`. -/
theorem phi_shift (ha : 1 ≤ a) (hab : a < b) {y : ℤ} (hy : ¬ E a y)
    (h1 : phi a b (y - a) < phi a b y) (h2 : phi a b y < phi a b (y + b)) :
    E a (y + b - a) ∧ phi a b (y + b - a) = phi a b y := by
  obtain ⟨q, r, hb, hr0, hr1, hN, hq0, hq1⟩ := b_decomp ha hab
  obtain ⟨U, ρ, hu, hρ0, hρ1⟩ := decomp ha y
  have hρ : a ≤ ρ := by have := (E_iff ha hu hρ0 hρ1).not.1 hy; omega
  have hκy := kappa_eq ha hu hρ0 hρ1
  have hκa := kappa_eq ha (y := y - a) (Y := U) (ρ := ρ - a) (by rw [hu]; ring) (by omega)
    (by omega)
  obtain ⟨hj1, hj2⟩ := (phi_eq_iff ha hab (y := y)).1 rfl
  have hA := (phi_lt_iff ha hab).1 h1
  have hB := (le_phi_iff ha hab).1 (show phi a b y + 1 ≤ phi a b (y + b) by omega)
  rw [show (phi a b y + 1) * N a b = phi a b y * N a b + N a b by ring] at hB
  rw [phi_eq_iff ha hab]
  by_cases hc1 : ρ + r < 2 * a
  · have hv : y + b - a = 2 * (a * (U + q)) + (ρ - a + r) := by linear_combination hu + hb
    have hκv := kappa_eq ha hv (by omega) (by omega)
    rw [mul_add] at hκv
    have := hq1 (by omega)
    refine ⟨(E_iff ha hv (by omega) (by omega)).2 (by omega), ?_, ?_⟩
    · rw [hκv]; omega
    · rw [hκv]; omega
  · have hw : y + b = 2 * (a * (U + q + 1)) + (ρ + r - 2 * a) := by
      linear_combination hu + hb
    have hκw := kappa_eq ha hw (by omega) (by omega)
    rw [mul_add, mul_add, mul_one] at hκw
    by_cases hc2 : ρ + r < 3 * a
    · exfalso
      by_cases hra : a < r
      · have hN' : N a b = a * (q + 1) := by rw [hN, mul_add, mul_one]; omega
        have hm : phi a b y * N a b = a * (phi a b y * (q + 1)) := by rw [hN']; ring
        have hN'' : N a b = a * q + a := by rw [hN']; ring
        exact no_mult (A := a) (Z := U) (m := phi a b y * (q + 1)) (by omega) (by omega)
          (by omega)
      · omega
    · have hv : y + b - a = 2 * (a * (U + q + 1)) + (ρ + r - 3 * a) := by
        linear_combination hu + hb
      have hκv := kappa_eq ha hv (by omega) (by omega)
      rw [mul_add, mul_add, mul_one] at hκv
      have hN' : N a b = a * (q + 1) := by rw [hN, mul_add, mul_one]; omega
      have hm : phi a b y * N a b = a * (phi a b y * (q + 1)) := by rw [hN']; ring
      have hN'' : N a b = a * q + a := by rw [hN']; ring
      have hjN := mult_eq (A := a) (Z := U) (m := phi a b y * (q + 1)) (by omega) (by omega)
        (by omega)
      refine ⟨(E_iff ha hv (by omega) (by omega)).2 (by omega), ?_, ?_⟩
      · rw [hκv]; omega
      · rw [hκv]; omega

/-! ### Membership in `W` and the gap lemma -/

theorem W_of {x e j : ℤ} (he : E a e) (hj : phi a b e = j) (hx : x = e + j * b) : W a b x :=
  ⟨j, by rwa [hx, add_sub_cancel_right], by rw [hx, add_sub_cancel_right]; exact hj⟩

/-- No element of `W` lies strictly between `Φ(2aM - a - 1)` and `Φ(2aM)`, because no element
of `E` lies strictly between `2aM - a - 1` and `2aM`. -/
theorem not_W_of_gap (ha : 1 ≤ a) (hab : a < b) (M : ℤ) {x : ℤ}
    (h1 : Phi a b (2 * (a * M) - a - 1) < x) (h2 : x < Phi a b (2 * (a * M))) :
    ¬ W a b x := by
  rintro ⟨j, he, hj⟩
  have hx : Phi a b (x - j * b) = x := by
    rw [Phi, hj]
    ring
  have h3 : 2 * (a * M) - a - 1 < x - j * b :=
    (Phi_strictMono ha hab).lt_iff_lt.1 (by rw [hx]; exact h1)
  have h4 : x - j * b < 2 * (a * M) := (Phi_strictMono ha hab).lt_iff_lt.1 (by rw [hx]; exact h2)
  rw [E_iff ha (Y := M - 1) (ρ := x - j * b - 2 * (a * M) + 2 * a) (by ring) (by omega)
    (by omega)] at he
  omega

/-! ### The period formula -/

/-- The period `p` of Bhagat–Larsson–Manabe–Yamashita is `p = 2·a·ℓ + k·b` with
`a·ℓ = k·N` and `ℓ, k ≥ 1`. In the proof `g = gcd(a, N)`, `k = a/g` and `ℓ = N/g`. -/
theorem period_spec (ha : 1 ≤ a) (hab : a < b) :
    ∃ ℓ k : ℤ, 1 ≤ ℓ ∧ 1 ≤ k ∧ a * ℓ = k * N a b ∧ (period a b : ℤ) = 2 * (a * ℓ) + k * b := by
  obtain ⟨q, r, hqr, hr⟩ : ∃ q r : ℕ, b = 2 * a * q + r ∧ r < 2 * a :=
    ⟨b / (2 * a), b % (2 * a), (Nat.div_add_mod b (2 * a)).symm, Nat.mod_lt _ (by omega)⟩
  have hN : N a b = a * q + min (a : ℤ) r :=
    kappa_eq ha (y := b) (Y := q) (ρ := r) (by rw [hqr]; push_cast; ring) (by omega) (by omega)
  have hP : period a b = if (b - a) % (2 * a) ≤ a then 3 * a + 2 * (b - a) - (b - a) % (2 * a)
      else a * (a + 2 * (b - a) + (b - a) % (2 * a)) / Nat.gcd a ((b - a) % (2 * a)) := rfl
  rcases (show a ≤ r ∨ r < a by omega) with hra | hra
  · -- `d = r - a`; `k = 1`, `ℓ = q + 1`
    have hd : (b - a) % (2 * a) = r - a := by
      rw [show b - a = r - a + 2 * a * q by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (show r - a < 2 * a by omega)]
    rw [hd, if_pos (show r - a ≤ a by omega)] at hP
    refine ⟨q + 1, 1, by omega, le_rfl, ?_, ?_⟩
    · rw [hN, min_eq_left (show (a : ℤ) ≤ r by omega)]
      ring
    · rw [show period a b = 2 * a * q + 2 * a + b by omega]
      push_cast
      ring
  · have hq : q ≠ 0 := by
      rintro rfl
      omega
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Nat.mul_add, Nat.mul_one] at hqr
    rw [min_eq_right (show (r : ℤ) ≤ a by omega)] at hN
    push_cast at hN
    have hbZ : (b : ℤ) = 2 * a * q + 2 * a + r := by exact_mod_cast hqr
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · -- `r = 0`: `d = a`; `k = 1`, `ℓ = q + 1`
      subst hr0
      simp only [Nat.cast_zero, add_zero] at hN hbZ
      have hd : (b - a) % (2 * a) = a := by
        rw [show b - a = a + 2 * a * q by omega, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show a < 2 * a by omega)]
      rw [hd, if_pos (le_refl a)] at hP
      refine ⟨q + 1, 1, by omega, le_rfl, by rw [hN]; ring, ?_⟩
      rw [show period a b = 2 * b by omega]
      push_cast
      linear_combination hbZ
    · -- `0 < r < a`: `d = a + r`; `k = a/g`, `ℓ = N/g` with `g = gcd(a, r) = gcd(a, N)`
      have hd : (b - a) % (2 * a) = a + r := by
        rw [show b - a = a + r + 2 * a * q by omega, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show a + r < 2 * a by omega)]
      rw [hd, if_neg (show ¬ a + r ≤ a by omega), Nat.gcd_self_add_right,
        show a + 2 * (b - a) + (a + r) = 2 * b + r by omega] at hP
      have hG := Nat.gcd_pos_of_pos_left r (show 0 < a by omega)
      obtain ⟨k, hk⟩ := Nat.gcd_dvd_left a r
      obtain ⟨s, hs⟩ := Nat.gcd_dvd_right a r
      generalize Nat.gcd a r = g at hG hk hs hP
      have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hP' : period a b = k * (2 * b + r) := by
        rw [hP, hk, Nat.mul_assoc, Nat.mul_div_cancel_left _ hG]
      have hkZ : (a : ℤ) = g * k := by exact_mod_cast hk
      have hsZ : (r : ℤ) = g * s := by exact_mod_cast hs
      have hm : (k : ℤ) * 1 ≤ k * (q + 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      refine ⟨k * (q + 1) + s, k, by omega, by omega, ?_, ?_⟩
      · rw [hN]
        linear_combination (s : ℤ) * hkZ - (k : ℤ) * hsZ
      · rw [hP']
        push_cast
        linear_combination (k : ℤ) * hbZ + 2 * (k : ℤ) * hsZ - 2 * (s : ℤ) * hkZ

end Explicit

/-! ### The interface -/

/-- (B1) No two elements of `W` differ by `a`, `b` or `a + b`. -/
theorem W_indep {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) {u v : ℤ} (hu : W a b u) (hv : W a b v)
    (h : v = u + a ∨ v = u + b ∨ v = u + (a + b)) : False := by
  obtain ⟨j, he, hj⟩ := hu
  obtain ⟨j', he', hj'⟩ := hv
  have hb0 : (0 : ℤ) ≤ b := by omega
  rcases lt_trichotomy j' j with hlt | heq | hgt
  · -- the preimage of `v` lies above that of `u`, so `j ≤ j'`
    have h1 : (j' + 1) * (b : ℤ) ≤ j * b := Int.mul_le_mul_of_nonneg_right (by omega) hb0
    have h2 : (j' + 1) * (b : ℤ) = j' * b + b := by ring
    have := phi_mono ha hab (show u - j * b ≤ v - j' * b by omega)
    omega
  · rw [heq] at he' hj'
    rcases h with rfl | rfl | rfl
    · rw [show u + a - j * b = u - j * b + a by ring] at he'
      exact not_E_add_a ha he he'
    · have h1 : u + b - j * b - b = u - j * b := by ring
      have := phi_sub_b_lt ha hab he' (by rw [h1]; exact he)
      rw [h1] at this
      omega
    · have h1 : u + (a + b) - j * b - (a + b) = u - j * b := by ring
      have := phi_sub_c_lt ha hab he' (by rw [h1]; exact he)
      rw [h1] at this
      omega
  · rcases (show j' = j + 1 ∨ j + 2 ≤ j' by omega) with heq | hge
    · rw [heq] at he' hj'
      have h1 : (j + 1) * (b : ℤ) = j * b + b := by ring
      rcases h with rfl | rfl | rfl
      · have := phi_mono ha hab (show u + a - (j + 1) * b ≤ u - j * b by omega)
        omega
      · rw [show u + b - (j + 1) * b = u - j * b by ring] at hj'
        omega
      · rw [show u + (a + b) - (j + 1) * b = u - j * b + a by ring] at he'
        exact not_E_add_a ha he he'
    · -- the preimage of `v` lies below that of `u`, so `j' ≤ j`
      have h1 : (j + 2) * (b : ℤ) ≤ j' * b := Int.mul_le_mul_of_nonneg_right (by omega) hb0
      have h2 : (j + 2) * (b : ℤ) = j * b + 2 * b := by ring
      have := phi_mono ha hab (show v - j' * b ≤ u - j * b by omega)
      omega

/-- (B2) For every `x`, one of `x`, `x - a`, `x - b`, `x - (a + b)` lies in `W`. -/
theorem W_cover {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (x : ℤ) :
    W a b x ∨ W a b (x - a) ∨ W a b (x - b) ∨ W a b (x - (a + b)) := by
  have hb0 : (0 : ℤ) ≤ b := by omega
  -- the largest `j` with `j ≤ φ(x - j·b)`
  obtain ⟨j, hP, hmax⟩ : ∃ j : ℤ, j ≤ phi a b (x - j * b) ∧
      ∀ z : ℤ, z ≤ phi a b (x - z * b) → z ≤ j := by
    refine Int.exists_greatest_of_bdd ⟨max 0 (phi a b x), fun z hz => ?_⟩
      ⟨min 0 (phi a b x), ?_⟩
    · rcases le_or_gt z 0 with h | h
      · exact le_trans h (le_max_left _ _)
      · have : 0 ≤ z * (b : ℤ) := mul_nonneg h.le hb0
        have := phi_mono ha hab (show x - z * b ≤ x by omega)
        exact le_trans (le_trans hz this) (le_max_right _ _)
    · have : min 0 (phi a b x) * (b : ℤ) ≤ 0 * b :=
        Int.mul_le_mul_of_nonneg_right (min_le_left _ _) hb0
      have := phi_mono ha hab (show x ≤ x - min 0 (phi a b x) * b by omega)
      exact le_trans (min_le_right _ _) this
  have hn : ¬ j + 1 ≤ phi a b (x - (j + 1) * b) := fun h' => by
    have := hmax _ h'
    omega
  obtain ⟨y, hy⟩ : ∃ y, x - j * b = y := ⟨_, rfl⟩
  have hxy : x = y + j * b := by omega
  rw [hy] at hP
  rw [show x - (j + 1) * b = y - b by linear_combination hy] at hn
  obtain ⟨hb1, hb2⟩ := phi_sub_b ha hab y
  obtain ⟨ha1, ha2⟩ := phi_sub_a ha hab y
  by_cases hφ : phi a b y = j
  · by_cases hE : E a y
    · exact Or.inl (W_of hE hφ hxy)
    · have hEa := (E_sub_a ha y).2 hE
      by_cases hφa : phi a b (y - a) = j
      · exact Or.inr (Or.inl (W_of hEa hφa (by linear_combination hxy)))
      · exact Or.inr (Or.inr (Or.inr
          (W_of hEa (show phi a b (y - a) = j - 1 by omega) (by linear_combination hxy))))
  · have hφb : phi a b (y - b) = j := by omega
    by_cases hE : E a (y - b)
    · exact Or.inr (Or.inr (Or.inl (W_of hE hφb (by linear_combination hxy))))
    · have hEa := (E_sub_a ha (y - b)).2 hE
      obtain ⟨hc1, hc2⟩ := phi_sub_a ha hab (y - b)
      by_cases hφa : phi a b (y - b - a) = j
      · exact Or.inr (Or.inr (Or.inr (W_of hEa hφa (by linear_combination hxy))))
      · -- F8 at `y - b`
        obtain ⟨hE', hφ'⟩ := phi_shift ha hab hE (by omega) (by rw [sub_add_cancel]; omega)
        rw [sub_add_cancel] at hE' hφ'
        exact Or.inr (Or.inl (W_of (j := j) hE' (by omega) (by linear_combination hxy)))

/-- (B3) The lower gap: `W` misses `[-(a + b), -1]`. -/
theorem W_neg_gap {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) {x : ℤ} (h1 : -((a : ℤ) + b) ≤ x)
    (h2 : x < 0) : ¬ W a b x := by
  have hN := N_pos ha hab
  have hk0 : kappa a 0 = 0 := by
    rw [kappa_eq ha (y := 0) (Y := 0) (ρ := 0) (by ring) le_rfl (by omega)]
    omega
  have hk1 : kappa a (-(a : ℤ) - 1) = -1 := by
    rw [kappa_eq ha (y := -(a : ℤ) - 1) (Y := -1) (ρ := a - 1) (by ring) (by omega) (by omega)]
    omega
  have hp0 : phi a b 0 = 0 := by
    rw [phi_eq_iff ha hab, hk0]
    omega
  have hp1 : phi a b (-(a : ℤ) - 1) = -1 := by
    rw [phi_eq_iff ha hab, hk1]
    omega
  apply not_W_of_gap ha hab 0
  · rw [show 2 * ((a : ℤ) * 0) - a - 1 = -(a : ℤ) - 1 by ring, Phi, hp1]
    omega
  · rw [show 2 * ((a : ℤ) * 0) = 0 by ring, Phi, hp0]
    omega

/-- (B3) The upper gap: `W` misses `[p - (a + b), p - 1]`, where `p = period a b`. -/
theorem W_top_gap {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) {x : ℤ}
    (h1 : (period a b : ℤ) - (a + b) ≤ x) (h2 : x < period a b) : ¬ W a b x := by
  obtain ⟨ℓ, k, -, -, hQ, hp⟩ := period_spec ha hab
  have hN := N_pos ha hab
  have hk0 : kappa a (2 * (a * ℓ)) = a * ℓ := by
    rw [kappa_eq ha (y := 2 * (a * ℓ)) (Y := ℓ) (ρ := 0) (by ring) le_rfl (by omega)]
    omega
  have hk1 : kappa a (2 * (a * ℓ) - a - 1) = a * ℓ - 1 := by
    rw [kappa_eq ha (y := 2 * (a * ℓ) - a - 1) (Y := ℓ - 1) (ρ := a - 1) (by ring) (by omega)
      (by omega), mul_sub, mul_one]
    omega
  have hp0 : phi a b (2 * (a * ℓ)) = k := by
    rw [phi_eq_iff ha hab, hk0, hQ]
    omega
  have hp1 : phi a b (2 * (a * ℓ) - a - 1) = k - 1 := by
    rw [phi_eq_iff ha hab, hk1, hQ, show (k - 1) * N a b = k * N a b - N a b by ring]
    omega
  apply not_W_of_gap ha hab ℓ
  · rw [Phi, hp1, show (b : ℤ) * (k - 1) = k * b - b by ring]
    omega
  · rw [Phi, hp0, show (b : ℤ) * k = k * b by ring]
    omega

/-- The period exceeds `a + b`. -/
theorem period_gt {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) : a + b < period a b := by
  obtain ⟨ℓ, k, hℓ, hk, -, hp⟩ := period_spec ha hab
  have h1 : (a : ℤ) * 1 ≤ a * ℓ := Int.mul_le_mul_of_nonneg_left hℓ (by omega)
  have h2 : 1 * (b : ℤ) ≤ k * b := Int.mul_le_mul_of_nonneg_right hk (by omega)
  omega

end AgenticConjectures.AdditiveSinkWallDuality
