import Mathlib

/-!
# Erdős problem 424 — residue obstruction and polynomial bounds for the generated set

Start from `2` and `3` and repeatedly add `x * y - 1` for distinct members `x ≠ y`
(Hofstadter's sequence, OEIS A005244).  Erdős problem 424 (= Ben Green's open problem 63)
asks whether the resulting set of integers has positive density.  That question remains
open; this module does **not** settle it.

The three definitions below are copied verbatim from the FormalConjectures file
`FormalConjectures/ErdosProblems/424.lean` at commit
`9118d083ffca1536f521f9a7d103201f537ea670` (local snapshot:
`problems/erdos-424/upstream/424.lean`), only moved into this namespace.  The upstream research
statement `erdos_424 : answer(sorry) ↔ generatedSet.HasPosDensity` is not restated: its
`Set.HasPosDensity` lives in `FormalConjecturesForMathlib`, which this repository does not
import.  Instead we use the explicit counting function
`countingFn N = #(generatedSet ∩ [0, N])` (a `Set.ncard`).

Proved here, for the upstream `generatedSet`:

* `mem_generatedSet_iff`, `lt_mul_sub_one`: the members are exactly `2`, `3` and the numbers
  `x * y - 1` with distinct members `x, y`, and both factors are smaller than the product.
  This is the recursion used by the exact sieves in `problems/erdos-424/`.
* `mod_three_ne_one`: no member is `≡ 1 (mod 3)`.
* `three_mul_countingFn_le`: `3 * A(N) ≤ 2 * N` for all `N`; hence
  `le_two_thirds_of_tendsto`: if `A(N) / N` converges, its limit is at most `2/3`.
* `pow_two_add_one_mem`, `generatedSet_infinite`: `2^k + 1` is a member for every `k ≥ 1`.
* `le_sixteen_mul_countingFn_sq`: `N ≤ 16 * A(N)^2` for `N ≥ 5`, i.e. `A(N) ≥ √N / 4`.
* `not_mem_of_prime_succ`, `three_mul_prime_sub_one_not_mem`,
  `infinite_nonmembers_zero_mod_three`, `infinite_nonmembers_two_mod_three`: `p - 1` and
  `3p - 1` are non-members for suitable primes `p`, so both admissible classes `0` and `2`
  modulo `3` contain infinitely many non-members.

Natural-number subtraction: every member is at least `2` (`two_le_of_mem`), so `x * y ≥ 6`
for distinct members and `x * y - 1` never truncates.  The lower bound `√N / 4` is far below
the linear growth seen numerically and is not a step towards positive density.
-/

namespace AgenticConjectures.Erdos424

open Filter Set Topology

/-- Upstream `Erdos424.nextGeneration`, copied verbatim. -/
def nextGeneration (A : Set ℕ) : Set ℕ :=
  { z : ℕ | ∃ x y, x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ z = x * y - 1 }

/-- Upstream `Erdos424.sequenceSet`, copied verbatim. -/
def sequenceSet : ℕ → Set ℕ
  | 0 => {2, 3}
  | n + 1 => (sequenceSet n) ∪ (nextGeneration (sequenceSet n))

/-- Upstream `Erdos424.generatedSet`, copied verbatim. -/
def generatedSet : Set ℕ := ⋃ n : ℕ, sequenceSet n

theorem sequenceSet_mono : Monotone sequenceSet :=
  monotone_nat_of_le_succ fun _ => subset_union_left

theorem two_mem : 2 ∈ generatedSet := mem_iUnion.2 ⟨0, by simp [sequenceSet]⟩

theorem three_mem : 3 ∈ generatedSet := mem_iUnion.2 ⟨0, by simp [sequenceSet]⟩

/-- The generated set is closed under `x, y ↦ x * y - 1` for distinct members. -/
theorem mul_sub_one_mem {x y : ℕ} (hx : x ∈ generatedSet) (hy : y ∈ generatedSet)
    (hxy : x ≠ y) : x * y - 1 ∈ generatedSet := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  obtain ⟨j, hj⟩ := mem_iUnion.1 hy
  refine mem_iUnion.2 ⟨max i j + 1, Or.inr ⟨x, y, ?_, ?_, hxy, rfl⟩⟩
  · exact sequenceSet_mono (le_max_left i j) hi
  · exact sequenceSet_mono (le_max_right i j) hj

/-- Induction over the generated set: a property of `2` and `3` that passes from distinct
members `x, y` to `x * y - 1` holds for every member. -/
theorem induction_on {P : ℕ → Prop} (h2 : P 2) (h3 : P 3)
    (hstep : ∀ x y, x ∈ generatedSet → y ∈ generatedSet → x ≠ y → P x → P y →
      P (x * y - 1))
    {n : ℕ} (hn : n ∈ generatedSet) : P n := by
  suffices h : ∀ k, ∀ m ∈ sequenceSet k, m ∈ generatedSet ∧ P m by
    obtain ⟨k, hk⟩ := mem_iUnion.1 hn
    exact (h k n hk).2
  intro k
  induction k with
  | zero =>
    intro m hm
    simp only [sequenceSet, mem_insert_iff, mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · exact ⟨two_mem, h2⟩
    · exact ⟨three_mem, h3⟩
  | succ k ih =>
    intro m hm
    rcases hm with hm | ⟨x, y, hx, hy, hxy, rfl⟩
    · exact ih m hm
    · obtain ⟨hxG, hPx⟩ := ih x hx
      obtain ⟨hyG, hPy⟩ := ih y hy
      exact ⟨mul_sub_one_mem hxG hyG hxy, hstep x y hxG hyG hxy hPx hPy⟩

/-- Fixed-point description: the members are `2`, `3`, and the numbers `x * y - 1` with
distinct members `x, y`. -/
theorem mem_generatedSet_iff {n : ℕ} :
    n ∈ generatedSet ↔ n = 2 ∨ n = 3 ∨
      ∃ x y, x ∈ generatedSet ∧ y ∈ generatedSet ∧ x ≠ y ∧ n = x * y - 1 := by
  constructor
  · intro hn
    exact induction_on (P := fun n => n = 2 ∨ n = 3 ∨
        ∃ x y, x ∈ generatedSet ∧ y ∈ generatedSet ∧ x ≠ y ∧ n = x * y - 1)
      (Or.inl rfl) (Or.inr (Or.inl rfl))
      (fun x y hx hy hxy _ _ => Or.inr (Or.inr ⟨x, y, hx, hy, hxy, rfl⟩)) hn
  · rintro (rfl | rfl | ⟨x, y, hx, hy, hxy, rfl⟩)
    · exact two_mem
    · exact three_mem
    · exact mul_sub_one_mem hx hy hxy

theorem two_le_of_mem {n : ℕ} (hn : n ∈ generatedSet) : 2 ≤ n := by
  refine induction_on (P := fun n => 2 ≤ n) le_rfl (by norm_num) ?_ hn
  intro x y _ _ _ hx hy
  have : 4 ≤ x * y := by nlinarith
  omega

/-- Both factors are smaller than the product: `x < x * y - 1` and `y < x * y - 1`. -/
theorem lt_mul_sub_one {x y : ℕ} (hx : x ∈ generatedSet) (hy : y ∈ generatedSet)
    (hxy : x ≠ y) : x < x * y - 1 ∧ y < x * y - 1 := by
  have h2x := two_le_of_mem hx
  have h2y := two_le_of_mem hy
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · constructor <;> nlinarith [Nat.sub_add_cancel (show 1 ≤ x * y by nlinarith)]
  · constructor <;> nlinarith [Nat.sub_add_cancel (show 1 ≤ x * y by nlinarith)]

/-- **Residue obstruction.** No member is congruent to `1` modulo `3`. -/
theorem mod_three_ne_one {n : ℕ} (hn : n ∈ generatedSet) : n % 3 ≠ 1 := by
  refine induction_on (P := fun n => n % 3 ≠ 1) (by norm_num) (by norm_num) ?_ hn
  intro x y hx hy _ hx3 hy3
  have h2x := two_le_of_mem hx
  have h2y := two_le_of_mem hy
  have hpos : 4 ≤ x * y := by nlinarith
  have hmod := Nat.mul_mod x y 3
  have hx' : x % 3 = 0 ∨ x % 3 = 2 := by omega
  have hy' : y % 3 = 0 ∨ y % 3 = 2 := by omega
  generalize x * y = p at hpos hmod ⊢
  rcases hx' with h | h <;> rcases hy' with h' | h' <;> simp only [h, h'] at hmod <;> omega

/-! ### Counting function and the upper bound `A(N) ≤ 2N/3` -/

/-- The counting function `A(N) = #{n ≤ N : n ∈ generatedSet}`. -/
noncomputable def countingFn (N : ℕ) : ℕ := (generatedSet ∩ Iic N).ncard

/-- Exact number of `n ≤ N` with `2 ≤ n` and `n % 3 ≠ 1`. -/
theorem card_filter_admissible (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun n => 2 ≤ n ∧ n % 3 ≠ 1)).card =
      N / 3 + (N + 1) / 3 := by
  induction N with
  | zero => decide
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]
      omega
    · rw [ih]
      omega

/-- **Upper bound.** `3 · A(N) ≤ 2 · N` for every `N`. -/
theorem three_mul_countingFn_le (N : ℕ) : 3 * countingFn N ≤ 2 * N := by
  have hsub : generatedSet ∩ Iic N ⊆
      ↑((Finset.range (N + 1)).filter (fun n => 2 ≤ n ∧ n % 3 ≠ 1)) := by
    intro n ⟨hn, hnN⟩
    simp only [Finset.coe_filter, Finset.mem_range, mem_setOf_eq]
    exact ⟨Nat.lt_succ_of_le hnN, two_le_of_mem hn, mod_three_ne_one hn⟩
  have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, card_filter_admissible] at h
  unfold countingFn
  omega

/-- If `A(N)/N` converges, its limit is at most `2/3`. -/
theorem le_two_thirds_of_tendsto {α : ℝ}
    (h : Tendsto (fun N : ℕ => (countingFn N : ℝ) / N) atTop (𝓝 α)) : α ≤ 2 / 3 := by
  refine le_of_tendsto h (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ hN']
  have : ((3 * countingFn N : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
    exact_mod_cast three_mul_countingFn_le N
  push_cast at this
  linarith

/-! ### An explicit infinite family -/

/-- `2 ^ k + 1` is generated for every `k ≥ 1` (`3, 5, 9, 17, …`). -/
theorem pow_two_add_one_mem : ∀ k, 1 ≤ k → 2 ^ k + 1 ∈ generatedSet
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simpa using three_mem
  | k + 2, _ => by
    have ih := pow_two_add_one_mem (k + 1) (by omega)
    have hpow : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hne : (2 : ℕ) ≠ 2 ^ (k + 1) + 1 := by omega
    have hmem := mul_sub_one_mem two_mem ih hne
    have heq : 2 * (2 ^ (k + 1) + 1) - 1 = 2 ^ (k + 2) + 1 := by
      rw [pow_succ 2 (k + 1)]
      omega
    rwa [heq] at hmem

theorem generatedSet_infinite : generatedSet.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ (k + 1) + 1) ?_ ?_
  · intro a b hab
    have : 2 ^ (a + 1) = 2 ^ (b + 1) := by simpa using hab
    have := Nat.pow_right_injective (le_refl 2) this
    omega
  · intro k
    exact pow_two_add_one_mem (k + 1) (by omega)

/-! ### The lower bound `A(N) ≥ √N / 4`

For odd members `y ≥ 5` both `2y - 1` and `2(3y - 1) - 1 = 6y - 3` are odd members.  The
first is `1 (mod 4)` and the second `3 (mod 4)`, so the two maps have disjoint images, which
gives the recursion `c(N) ≥ 1 + c((N+1)/2) + c((N+3)/6)` for the number `c(N)` of odd
members in `[5, N]`, and hence `N ≤ 16 c(N)^2`. -/

/-- Odd members `y` of the generated set with `5 ≤ y ≤ N` (auxiliary). -/
noncomputable def oddMembers (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 5 N).filter fun y => y ∈ generatedSet ∧ y % 2 = 1

theorem mem_oddMembers {N y : ℕ} :
    y ∈ oddMembers N ↔ (5 ≤ y ∧ y ≤ N) ∧ y ∈ generatedSet ∧ y % 2 = 1 := by
  classical
  simp [oddMembers, Finset.mem_filter, Finset.mem_Icc]

theorem five_mem : 5 ∈ generatedSet := by
  simpa using mul_sub_one_mem two_mem three_mem (by norm_num)

theorem nine_mem : 9 ∈ generatedSet := by
  simpa using mul_sub_one_mem two_mem five_mem (by norm_num)

theorem card_oddMembers_rec {N : ℕ} (hN : 5 ≤ N) :
    1 + (oddMembers ((N + 1) / 2)).card + (oddMembers ((N + 3) / 6)).card ≤
      (oddMembers N).card := by
  classical
  set A := oddMembers ((N + 1) / 2) with hA
  set B := oddMembers ((N + 3) / 6) with hB
  have hf : ∀ y ∈ A, 2 * y - 1 ∈ oddMembers N ∧ (2 * y - 1) % 4 = 1 ∧ 9 ≤ 2 * y - 1 := by
    intro y hy
    rw [hA, mem_oddMembers] at hy
    obtain ⟨⟨h5, hyN⟩, hyG, hodd⟩ := hy
    have hmem := mul_sub_one_mem two_mem hyG (by omega)
    refine ⟨mem_oddMembers.2 ⟨⟨by omega, by omega⟩, hmem, by omega⟩, by omega, by omega⟩
  have hg : ∀ y ∈ B, 6 * y - 3 ∈ oddMembers N ∧ (6 * y - 3) % 4 = 3 := by
    intro y hy
    rw [hB, mem_oddMembers] at hy
    obtain ⟨⟨h5, hyN⟩, hyG, hodd⟩ := hy
    have h1 := mul_sub_one_mem three_mem hyG (by omega)
    have h2 := mul_sub_one_mem two_mem h1 (by omega)
    have heq : 2 * (3 * y - 1) - 1 = 6 * y - 3 := by omega
    rw [heq] at h2
    exact ⟨mem_oddMembers.2 ⟨⟨by omega, by omega⟩, h2, by omega⟩, by omega⟩
  have hdisj : Disjoint (A.image fun y => 2 * y - 1) (B.image fun y => 6 * y - 3) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨y', hy', hyy⟩ := Finset.mem_image.1 hz'
    have h1 := (hf y hy).2.1
    have h2 := (hg y' hy').2
    omega
  have h5 : 5 ∉ (A.image fun y => 2 * y - 1) ∪ (B.image fun y => 6 * y - 3) := by
    intro h
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨y, hy, hy5⟩ := Finset.mem_image.1 h
      have := (hf y hy).2.2
      omega
    · obtain ⟨y, hy, hy5⟩ := Finset.mem_image.1 h
      have := (hg y hy).2
      omega
  have hinjA : Set.InjOn (fun y => 2 * y - 1) A := by
    intro a ha b hb hab
    have := (hf a ha).2.2
    have := (hf b hb).2.2
    simp only at hab
    omega
  have hinjB : Set.InjOn (fun y => 6 * y - 3) B := by
    intro a ha b hb hab
    have := (hg a ha).2
    have := (hg b hb).2
    simp only at hab
    omega
  have hsub : insert 5 ((A.image fun y => 2 * y - 1) ∪ (B.image fun y => 6 * y - 3)) ⊆
      oddMembers N := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact mem_oddMembers.2 ⟨⟨le_rfl, hN⟩, five_mem, by norm_num⟩
    rcases Finset.mem_union.1 hz with h | h
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact (hf y hy).1
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
      exact (hg y hy).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem h5, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hinjA, Finset.card_image_of_injOn hinjB] at hcard
  omega

theorem le_sixteen_mul_card_oddMembers_sq (N : ℕ) (hN : 5 ≤ N) :
    N ≤ 16 * (oddMembers N).card ^ 2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  have h5 : 5 ∈ oddMembers N := mem_oddMembers.2 ⟨⟨le_rfl, hN⟩, five_mem, by norm_num⟩
  by_cases hN9 : N < 9
  · have : 1 ≤ (oddMembers N).card := Finset.card_pos.2 ⟨5, h5⟩
    nlinarith
  by_cases hN27 : N < 27
  · have h9 : 9 ∈ oddMembers N := mem_oddMembers.2 ⟨⟨by norm_num, by omega⟩, nine_mem, by norm_num⟩
    have hsub : ({5, 9} : Finset ℕ) ⊆ oddMembers N := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact h5
      · exact h9
    have : 2 ≤ (oddMembers N).card := by simpa using Finset.card_le_card hsub
    nlinarith
  push Not at hN9 hN27
  set a := (N + 1) / 2 with ha_def
  set b := (N + 3) / 6 with hb_def
  have ha := ih a (by omega) (by omega)
  have hb := ih b (by omega) (by omega)
  have hrec := card_oddMembers_rec hN
  rw [← ha_def, ← hb_def] at hrec
  set ca := (oddMembers a).card
  set cb := (oddMembers b).card
  set c := (oddMembers N).card
  obtain ⟨s, hs⟩ : ∃ s, N = a + b + s := ⟨N - a - b, by omega⟩
  have h2a : N ≤ 2 * a := by omega
  have h6b : N ≤ 6 * b + 2 := by omega
  have h4a : 2 * a ≤ N + 1 := by omega
  have h3s : 3 * s ≤ N + 1 := by omega
  have hs2 : s * s ≤ 4 * a * b := by
    have e1 : (3 * s) * (3 * s) ≤ (N + 1) * (N + 1) := Nat.mul_le_mul h3s h3s
    have e2 : N * N ≤ (2 * a) * (6 * b + 2) := Nat.mul_le_mul h2a h6b
    nlinarith
  have hab : 4 * a * b ≤ (32 * ca * cb) * (32 * ca * cb) := by
    have := Nat.mul_le_mul ha hb
    nlinarith
  have hkey : s ≤ 32 * ca * cb := Nat.mul_self_le_mul_self_iff.1 (hs2.trans hab)
  have hsq : (1 + ca + cb) ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hrec 2
  nlinarith

/-- **Lower bound.** `N ≤ 16 · A(N)²`, i.e. `A(N) ≥ √N / 4`, for every `N ≥ 5`. -/
theorem le_sixteen_mul_countingFn_sq {N : ℕ} (hN : 5 ≤ N) : N ≤ 16 * countingFn N ^ 2 := by
  have hle : (oddMembers N).card ≤ countingFn N := by
    rw [countingFn, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ ((Set.finite_Iic N).subset inter_subset_right)
    intro y hy
    rw [Finset.mem_coe, mem_oddMembers] at hy
    exact ⟨hy.2.1, hy.1.2⟩
  calc N ≤ 16 * (oddMembers N).card ^ 2 := le_sixteen_mul_card_oddMembers_sq N hN
    _ ≤ 16 * countingFn N ^ 2 := by gcongr

/-! ### Infinitely many non-members in each admissible class -/

/-- If `n + 1` is prime and `n ≥ 4`, then `n` is not generated. -/
theorem not_mem_of_prime_succ {n : ℕ} (hp : (n + 1).Prime) (hn : 4 ≤ n) :
    n ∉ generatedSet := by
  intro h
  rcases mem_generatedSet_iff.1 h with rfl | rfl | ⟨x, y, hx, hy, _, rfl⟩
  · omega
  · omega
  have h2x := two_le_of_mem hx
  have h2y := two_le_of_mem hy
  have hxy : x * y - 1 + 1 = x * y := Nat.sub_add_cancel (by nlinarith)
  rw [hxy] at hp
  rcases hp.eq_one_or_self_of_dvd x (dvd_mul_right x y) with h1 | h1
  · omega
  · have : x * y = x * 1 := by rw [mul_one]; exact h1.symm
    have := Nat.eq_of_mul_eq_mul_left (by omega) this
    omega

/-- If `p` is a prime with `p % 3 = 1`, then `3p - 1` is not generated. -/
theorem three_mul_prime_sub_one_not_mem {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 1) :
    3 * p - 1 ∉ generatedSet := by
  intro h
  have hp7 : 7 ≤ p := by
    have := hp.two_le
    rcases (show p = 4 ∨ 7 ≤ p by omega) with h4 | h7
    · exact absurd (h4 ▸ hp) (by decide)
    · exact h7
  rcases mem_generatedSet_iff.1 h with h' | h' | ⟨x, y, hx, hy, _, hxy⟩
  · omega
  · omega
  have h2x := two_le_of_mem hx
  have h2y := two_le_of_mem hy
  have hprod : x * y = 3 * p := by
    have : 1 ≤ x * y := by nlinarith
    omega
  have hdvd : p ∣ x * y := ⟨3, by rw [hprod]; ring⟩
  rcases hp.dvd_mul.1 hdvd with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · -- x = p * t, so t * y = 3 and y ∈ {1, 3}; y ≥ 2 forces t = 1 and x = p
    have hty : t * y = 3 := by
      have : p * (t * y) = p * 3 := by rw [← mul_assoc, hprod]; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    have ht : t = 1 := by
      have : t ∣ 3 := ⟨y, hty.symm⟩
      rcases (Nat.dvd_prime Nat.prime_three).1 this with h | h
      · exact h
      · subst h; omega
    subst ht
    exact mod_three_ne_one hx (by simpa using hp3)
  · have hty : x * t = 3 := by
      have : p * (x * t) = p * 3 := by rw [mul_left_comm, hprod]; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    have ht : t = 1 := by
      have : t ∣ 3 := ⟨x, by rw [← hty]; ring⟩
      rcases (Nat.dvd_prime Nat.prime_three).1 this with h | h
      · exact h
      · subst h; omega
    subst ht
    exact mod_three_ne_one hy (by simpa using hp3)

/-- Infinitely many multiples of `3` are not generated (e.g. `p - 1` for primes `p ≡ 1 mod 3`). -/
theorem infinite_nonmembers_zero_mod_three :
    {n : ℕ | n % 3 = 0 ∧ n ∉ generatedSet}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun m => ?_
  obtain ⟨p, hp, hpm, hp1⟩ := Nat.exists_prime_gt_modEq_one (k := 3) (m + 7) (by norm_num)
  have hp3 : p % 3 = 1 := hp1
  refine ⟨p - 1, ⟨by omega, not_mem_of_prime_succ ?_ (by omega)⟩, by omega⟩
  rwa [Nat.sub_add_cancel hp.one_le]

/-- Infinitely many `n ≡ 2 (mod 3)` are not generated (e.g. `3p - 1` for primes
`p ≡ 1 mod 3`). -/
theorem infinite_nonmembers_two_mod_three :
    {n : ℕ | n % 3 = 2 ∧ n ∉ generatedSet}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun m => ?_
  obtain ⟨p, hp, hpm, hp1⟩ := Nat.exists_prime_gt_modEq_one (k := 3) m (by norm_num)
  have hp3 : p % 3 = 1 := hp1
  exact ⟨3 * p - 1, ⟨by omega, three_mul_prime_sub_one_not_mem hp hp3⟩, by omega⟩

end AgenticConjectures.Erdos424
