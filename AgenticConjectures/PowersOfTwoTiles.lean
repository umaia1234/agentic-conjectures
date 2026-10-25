import Mathlib

/-!
# Powers-of-two translational tiles (Benjamini–Kozma–Tzalik, Question 9)

Question 9 of Benjamini–Kozma–Tzalik, *The number of tiles of `ℤ^d`*
(<https://arxiv.org/abs/2303.07956v2>), first asks how many tiles are
contained in the set `{1,2,4,…,2^n}`, and then:

> Are the only such tiles the sets of size `1` and `2`?

The paper's definition (Section 1): a set `S ⊆ ℤ^d` tiles `ℤ^d` by
translations if there is a set `T ⊆ ℤ^d` such that `ℤ^d` is the disjoint union
of the translates `S + z`, `z ∈ T`.  `Tiles` below is that definition for
`d = 1`, written as "the translates cover `ℤ` and are pairwise disjoint".

`statement` is the yes/no clause only: every finite set of integers contained
in `{2^i : i ≤ n}` that tiles `ℤ` has one or two elements.  Subsets of a
finite set are finite, so quantifying over `Finset ℤ` loses nothing.  The
first sentence of Question 9 (the exact count of such tiles) is not
formalized and not addressed.

We prove `¬ statement` (`refuted`) with `A = {1,4,16}` and
`B = {b : b mod 9 < 3} = {0,1,2} + 9ℤ` (`isTiling_one_four_sixteen`), and the
README's general family (`exists_tile_of_odd`): for every odd `t` there is a
tile of exactly `t` elements inside some `{1,2,…,2^n}`.  The family uses any
`r ≥ 1` with `t ∣ 2^r - 1` (the README takes `r = ord_t 2`; we take
`r = φ(t)`), `A = {2^(r i) : i < t}`, and `B = {b : b mod t(2^r-1) < 2^r-1}`.
The README's shifted family `A_{t,s}` is not formalized.
-/

namespace AgenticConjectures.PowersOfTwoTiles

/-- The paper's definition for `d = 1`: some family of translates `A + b`,
`b ∈ B`, covers `ℤ` and is pairwise disjoint. -/
def Tiles (A : Set ℤ) : Prop :=
  ∃ B : Set ℤ, (⋃ b ∈ B, (· + b) '' A) = Set.univ ∧
    B.PairwiseDisjoint fun b => (· + b) '' A

/-- `{1, 2, 4, …, 2^n}` as a set of integers. -/
def powersUpTo (n : ℕ) : Set ℤ := {x | ∃ i ≤ n, x = 2 ^ i}

/-- The yes/no clause of Question 9: every tile contained in
`{1, 2, 4, …, 2^n}` has one or two elements. -/
def statement : Prop :=
  ∀ n : ℕ, ∀ A : Finset ℤ, (A : Set ℤ) ⊆ powersUpTo n → Tiles A →
    A.card = 1 ∨ A.card = 2

/-- Every integer is uniquely `a + b` with `a ∈ A`, `b ∈ B`. -/
def IsTiling (A B : Set ℤ) : Prop :=
  ∀ z : ℤ, ∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = z

/-- Unique representation gives the paper's disjoint union of translates. -/
theorem IsTiling.tiles {A B : Set ℤ} (h : IsTiling A B) : Tiles A := by
  refine ⟨B, ?_, ?_⟩
  · ext z
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_univ, iff_true]
    obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, -⟩ := h z
    exact ⟨b, hb, a, ha, hab⟩
  · intro b hb b' hb' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨a', ha', hx⟩
    obtain ⟨p, -, huniq⟩ := h (a + b)
    have h1 := huniq (a, b) ⟨ha, hb, rfl⟩
    have h2 := huniq (a', b') ⟨ha', hb', hx⟩
    exact hne (congrArg Prod.snd (h1.trans h2.symm))

/-- `(1 + q)^i ≡ 1 + i q (mod t q)` whenever `t ∣ q`. -/
theorem one_add_pow_modEq {t q : ℤ} (htq : t ∣ q) (i : ℕ) :
    (1 + q) ^ i ≡ 1 + i * q [ZMOD t * q] := by
  obtain ⟨k, rfl⟩ := htq
  induction i with
  | zero => simp
  | succ i ih =>
    refine ((pow_succ (1 + t * k) i ▸ ih.mul_right (1 + t * k))).trans ?_
    rw [Int.modEq_iff_dvd]
    exact ⟨-(i * k), by push_cast; ring⟩

/-- For `0 ≤ w < M`, `0 ≤ I` and `I + q ≤ M`, the residue of `w - I` lies
below `q` exactly when `w ∈ [I, I + q)`. -/
theorem sub_emod_lt_iff {w I q M : ℤ} (hw0 : 0 ≤ w) (hwM : w < M) (hI : 0 ≤ I)
    (hIq : I + q ≤ M) (hq : 0 < q) :
    (w - I) % M < q ↔ I ≤ w ∧ w < I + q := by
  rcases le_or_gt I w with h | h
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · have : (w - I) % M = w - I + M := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [this]
    omega

/-- The tile `{2^(r i) : i < t}`. -/
def tileA (t r : ℕ) : Finset ℤ :=
  (Finset.range t).image fun i => (2 : ℤ) ^ (r * i)

/-- The complement `{b : b mod t q < q} = {0, …, q-1} + t q ℤ`. -/
def tileB (t q : ℤ) : Set ℤ := {b | b % (t * q) < q}

/-- If `t ∣ 2^r - 1`, then `{2^(r i) : i < t}` tiles `ℤ` with complement
`{0, …, q-1} + t q ℤ`, where `q = 2^r - 1`. -/
theorem isTiling_tileA (t r : ℕ) (ht : 0 < t) (hr : 0 < r)
    (hdiv : (t : ℤ) ∣ 2 ^ r - 1) :
    IsTiling (tileA t r) (tileB t (2 ^ r - 1)) := by
  set q : ℤ := 2 ^ r - 1 with hq_def
  have hq : 0 < q := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
    omega
  set M : ℤ := t * q with hM_def
  have hM : 0 < M := mul_pos (by exact_mod_cast ht) hq
  have hcong : ∀ i : ℕ, (2 : ℤ) ^ (r * i) ≡ 1 + i * q [ZMOD M] := by
    intro i
    rw [pow_mul, show (2 : ℤ) ^ r = 1 + q by rw [hq_def]; ring]
    exact one_add_pow_modEq hdiv i
  -- `z - 2^(r i)` lies in `B` exactly when `(z - 1) mod M ∈ [i q, i q + q)`.
  have hkey : ∀ (z : ℤ) (i : ℕ), i < t →
      ((z - 2 ^ (r * i)) % M < q ↔
        i * q ≤ (z - 1) % M ∧ (z - 1) % M < i * q + q) := by
    intro z i hi
    have e1 : z - 2 ^ (r * i) ≡ (z - 1) - i * q [ZMOD M] := by
      have := (hcong i).sub_left z
      rwa [show z - (1 + i * q) = z - 1 - i * q by ring] at this
    have e2 : (z - 1) % M - i * q ≡ (z - 1) - i * q [ZMOD M] :=
      (Int.mod_modEq _ _).sub_right _
    have h1 : (z - 2 ^ (r * i)) % M = ((z - 1) % M - i * q) % M :=
      e1.trans e2.symm
    have hit : (i : ℤ) + 1 ≤ t := by exact_mod_cast hi
    rw [h1]
    refine sub_emod_lt_iff (Int.emod_nonneg _ hM.ne') (Int.emod_lt_of_pos _ hM)
      (mul_nonneg (by positivity) hq.le) ?_ hq
    calc (i : ℤ) * q + q = ((i : ℤ) + 1) * q := by ring
      _ ≤ t * q := mul_le_mul_of_nonneg_right hit hq.le
  intro z
  set w := (z - 1) % M with hw_def
  have hw0 : 0 ≤ w := Int.emod_nonneg _ hM.ne'
  have hwM : w < M := Int.emod_lt_of_pos _ hM
  have hd0 : 0 ≤ w / q := Int.ediv_nonneg hw0 hq.le
  set i := (w / q).toNat with hi_def
  have hiw : (i : ℤ) = w / q := Int.toNat_of_nonneg hd0
  have hit : i < t := by
    have : w / q < t := Int.ediv_lt_of_lt_mul hq (by rw [← hM_def]; exact hwM)
    omega
  have hlo : (i : ℤ) * q ≤ w := hiw ▸ Int.ediv_mul_le w hq.ne'
  have hhi : w < (i : ℤ) * q + q := by
    have := Int.lt_ediv_add_one_mul_self w hq
    rw [hiw]; linarith
  refine ⟨(2 ^ (r * i), z - 2 ^ (r * i)), ⟨?_, ?_, by ring⟩, ?_⟩
  · simp only [tileA, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨i, hit, rfl⟩
  · exact (hkey z i hit).2 ⟨hlo, hhi⟩
  · rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    simp only [tileA, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio] at ha
    obtain ⟨j, hjt, rfl⟩ := ha
    have hb' : b = z - 2 ^ (r * j) := by simp only at hab; linarith
    subst hb'
    obtain ⟨hlo', hhi'⟩ := (hkey z j hjt).1 hb
    have hij : (i : ℤ) = j := by
      have h1 : (i : ℤ) < j + 1 := lt_of_mul_lt_mul_right (by linarith) hq.le
      have h2 : (j : ℤ) < i + 1 := lt_of_mul_lt_mul_right (by linarith) hq.le
      omega
    have : i = j := by exact_mod_cast hij
    subst this
    rfl

theorem card_tileA (t r : ℕ) (hr : 0 < r) : (tileA t r).card = t := by
  rw [tileA, Finset.card_image_of_injective _ ?_, Finset.card_range]
  exact ((pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 2)).comp
    (strictMono_mul_left_of_pos hr)).injective

theorem tileA_subset (t r : ℕ) : (tileA t r : Set ℤ) ⊆ powersUpTo (r * (t - 1)) := by
  intro x hx
  simp only [tileA, Finset.coe_image, Finset.coe_range, Set.mem_image,
    Set.mem_Iio] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨r * i, Nat.mul_le_mul_left r (by omega), rfl⟩

/-- `A = {1, 4, 16}` tiles `ℤ` with `B = {0, 1, 2} + 9ℤ`. -/
theorem isTiling_one_four_sixteen :
    IsTiling ({1, 4, 16} : Set ℤ) {b | b % 9 < 3} := by
  have h := isTiling_tileA 3 2 (by norm_num) (by norm_num) (by norm_num)
  have hA : (tileA 3 2 : Set ℤ) = {1, 4, 16} := by
    ext x
    simp only [tileA, Finset.coe_image, Finset.coe_range, Set.mem_image,
      Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i <;> norm_num
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, by norm_num⟩
      · exact ⟨2, by norm_num, by norm_num⟩
  have hB : tileB ((3 : ℕ) : ℤ) (2 ^ 2 - 1) = {b | b % 9 < 3} := by
    ext b
    simp only [tileB, Set.mem_setOf_eq]
    norm_num
  rwa [hA, hB] at h

/-- The yes/no clause of Question 9 is false: `{1, 4, 16} ⊆ {1, 2, …, 2^4}`
tiles `ℤ` and has three elements. -/
theorem refuted : ¬ statement := by
  intro h
  have hsub : (({1, 4, 16} : Finset ℤ) : Set ℤ) ⊆ powersUpTo 4 := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact ⟨4, by norm_num, by norm_num⟩
  have htiles : Tiles (({1, 4, 16} : Finset ℤ) : Set ℤ) := by
    simpa using isTiling_one_four_sixteen.tiles
  have := h 4 {1, 4, 16} hsub htiles
  simp at this

/-- For every odd `t` there is a tile of exactly `t` elements contained in
some `{1, 2, 4, …, 2^n}`. -/
theorem exists_tile_of_odd (t : ℕ) (ht : Odd t) :
    ∃ n : ℕ, ∃ A : Finset ℤ, (A : Set ℤ) ⊆ powersUpTo n ∧ A.card = t ∧ Tiles A := by
  have ht0 : 0 < t := ht.pos
  have hr : 0 < Nat.totient t := Nat.totient_pos.2 ht0
  have hcop : Nat.Coprime 2 t := Nat.coprime_two_left.2 ht
  have hdiv : (t : ℤ) ∣ 2 ^ Nat.totient t - 1 := by
    have := Nat.modEq_iff_dvd.1 (Nat.ModEq.pow_totient hcop).symm
    simpa using this
  exact ⟨_, tileA t (Nat.totient t), tileA_subset _ _, card_tileA _ _ hr,
    (isTiling_tileA t _ ht0 hr hdiv).tiles⟩

end AgenticConjectures.PowersOfTwoTiles
