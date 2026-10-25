import Mathlib

/-!
# Minimum modulus for the unique multiset-sum problem

J. A. R. Fonollosa, *Minimum modulus for the unique multiset-sum problem*
(arXiv:2607.08366), calls a finite set `A ⊆ ℤ/Nℤ` *valid* when the all-ones
multiplicity vector is the only size-`#A` multiset on `A` with sum `∑ A`, and
conjectures (Conjecture 1) that a valid `n`-set needs
`N ≥ 2^n - 2^⌊log₂ n⌋` for `n ≥ 2`.

`IsValidMod` and `minModulus` are copied term for term from the upstream Formal
Conjectures file `FormalConjectures/Arxiv/2607.08366/MinModulus.lean` (commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d`, snapshot in
`problems/min-modulus-multiset-sum/upstream/`), and `statement` is the
proposition of the upstream theorem `min_modulus` word for word.  As upstream,
`0 < N` excludes `ZMod 0 = ℤ`.  Adaptations, all forced by building without
`FormalConjecturesUtil`: `import Mathlib` replaces the `module` header and
`public import FormalConjecturesUtil`; there is no `@[expose] public section`;
the `category`/`AMS` attributes are dropped; the namespace is
`AgenticConjectures.MinModulusMultisetSum` instead of `Arxiv.«2607.08366»`;
the sorry-backed theorem `min_modulus` becomes `def statement : Prop`; the
docstrings are shortened.  The upstream API lemmas and the solved upper bound
`exists_isValidMod_minModulus` are not copied.

Proved here, for every valid `A ⊆ ZMod N` with `0 < N`:

* `IsValidMod.two_pow_le`: `2 ^ (#A - 1) ≤ N`.  The translated subset sums
  `∑_{x ∈ S} (x - a₀)` over `S ⊆ A \ {a₀}` are pairwise distinct.  This is
  the cyclic case of Inal's lower bound for finite abelian groups, recorded in
  the problem README.
* `IsValidMod.card_mul_card_sub_one_le`: `#A * (#A - 1) ≤ N`.  Valid sets are
  Sidon-like (`IsValidMod.add_eq_add`), so the ordered differences `x - y`,
  `x ≠ y`, are distinct, except that the element of order two may occur twice.
* `IsValidMod.two_pow_add_le`: `2 ^ (#A - 1) + (#A - 2) ≤ N` for `#A ≥ 2`.
  The doubled differences `2 (b - a₀)` avoid every nonempty translated subset
  sum, and at most two of them coincide.
* `statement_of_le_four`: the conjecture for `n ≤ 4`, where
  `minModulus n = n * (n - 1)`.

The conjecture itself remains open; `statement` is not proved.  The
exhaustive search for `n ≤ 9` lives in the problem directory, not in Lean.
-/

namespace AgenticConjectures.MinModulusMultisetSum

open Finset

variable {N : ℕ}

/-- `A ⊆ ZMod N` is valid if the all-ones multiplicity function is the only
`m : ZMod N → ℕ` with total weight `#A` on `A` and weighted sum `∑ A`.
(Upstream `IsValidMod`.) -/
def IsValidMod (A : Finset (ZMod N)) : Prop :=
  ∀ m : ZMod N → ℕ, ∑ a ∈ A, m a = #A → ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a →
    ∀ a ∈ A, m a = 1

/-- The conjectured minimum modulus `2^n - 2^⌊log₂ n⌋`.  (Upstream `minModulus`.) -/
def minModulus (n : ℕ) : ℕ := 2 ^ n - 2 ^ (Nat.log 2 n)

/-- Conjecture 1 of Fonollosa (upstream `min_modulus`): for `n ≥ 2`, no
`n`-subset of `ZMod N` is valid when `0 < N < minModulus n`. -/
def statement : Prop :=
  ∀ n N : ℕ, 2 ≤ n → 0 < N → N < minModulus n →
    ∀ A : Finset (ZMod N), #A = n → ¬ IsValidMod A

/-- A rival multiplicity function `1 + p - q` (with `q ≤ 1 + p` on `A`) of the
same total weight and weighted sum as the all-ones function forces `p = q`
on `A`. -/
theorem IsValidMod.eq_of_rival {A : Finset (ZMod N)} (hA : IsValidMod A)
    (p q : ZMod N → ℕ) (hle : ∀ a ∈ A, q a ≤ 1 + p a)
    (hcard : ∑ a ∈ A, p a = ∑ a ∈ A, q a)
    (hsum : ∑ a ∈ A, (p a : ZMod N) * a = ∑ a ∈ A, (q a : ZMod N) * a) :
    ∀ a ∈ A, p a = q a := by
  have h1 : ∑ a ∈ A, (1 + p a - q a) = #A := by
    have h : ∑ a ∈ A, (1 + p a - q a) + ∑ a ∈ A, q a = ∑ a ∈ A, (1 + p a) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a ha => Nat.sub_add_cancel (hle a ha)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, hcard] at h
    omega
  have h2 : ∑ a ∈ A, ((1 + p a - q a : ℕ) : ZMod N) * a = ∑ a ∈ A, a := by
    have h : ∀ a ∈ A, ((1 + p a - q a : ℕ) : ZMod N) * a
        = a + (p a : ZMod N) * a - (q a : ZMod N) * a := by
      intro a ha
      rw [Nat.cast_sub (hle a ha)]
      push_cast
      ring
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum]
    ring
  intro a ha
  have h3 : 1 + p a - q a = 1 := hA (fun a => 1 + p a - q a) h1 h2 a ha
  have h4 := hle a ha
  omega

/-- Translated subset sums `∑_{x ∈ S} (x - a₀)`. -/
def ssum (a₀ : ZMod N) (S : Finset (ZMod N)) : ZMod N := ∑ x ∈ S, (x - a₀)

theorem ssum_eq (a₀ : ZMod N) (S : Finset (ZMod N)) :
    ssum a₀ S = ∑ x ∈ S, x - (#S : ZMod N) * a₀ := by
  rw [ssum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

/-- Disjoint subsets of `A \ {a₀}` with `#S ≤ #T` and equal translated sums
coincide. -/
theorem IsValidMod.ssum_ne {A : Finset (ZMod N)} (hA : IsValidMod A) {a₀ : ZMod N}
    (ha₀ : a₀ ∈ A) {S T : Finset (ZMod N)} (hS : S ⊆ A.erase a₀) (hT : T ⊆ A.erase a₀)
    (hdisj : Disjoint S T) (hcard : #S ≤ #T) (hne : S ≠ T) : ssum a₀ S ≠ ssum a₀ T := by
  classical
  intro hcol
  have hSA : S ⊆ A := hS.trans (Finset.erase_subset _ _)
  have hTA : T ⊆ A := hT.trans (Finset.erase_subset _ _)
  have hSa₀ : a₀ ∉ S := fun h => (Finset.mem_erase.1 (hS h)).1 rfl
  have hTa₀ : a₀ ∉ T := fun h => (Finset.mem_erase.1 (hT h)).1 rfl
  let p : ZMod N → ℕ := fun a => (if a ∈ S then 1 else 0) + (if a = a₀ then #T - #S else 0)
  let q : ZMod N → ℕ := fun a => if a ∈ T then 1 else 0
  have key := hA.eq_of_rival p q
    (by intro a _; simp only [p, q]; split_ifs <;> omega)
    (by
      simp only [p, q, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_ite_eq',
        if_pos ha₀, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hSA,
        Finset.inter_eq_right.2 hTA, Nat.cast_id]
      omega)
    (by
      have hc : ((#T - #S : ℕ) : ZMod N) = (#T : ZMod N) - #S := Nat.cast_sub hcard
      simp only [p, q, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul,
        ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_mem,
        Finset.inter_eq_right.2 hSA, Finset.inter_eq_right.2 hTA, Finset.sum_ite_eq',
        if_pos ha₀, hc]
      rw [ssum_eq, ssum_eq] at hcol
      linear_combination hcol)
  have hST : S.Nonempty ∨ T.Nonempty := by
    by_contra h
    simp only [not_or, Finset.not_nonempty_iff_eq_empty] at h
    exact hne (h.1.trans h.2.symm)
  rcases hST with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hxT : x ∉ T := Finset.disjoint_left.1 hdisj hx
    have hxa : x ≠ a₀ := fun h => hSa₀ (h ▸ hx)
    have := key x (hSA hx)
    simp [p, q, hx, hxT, hxa] at this
  · have hxS : x ∉ S := Finset.disjoint_right.1 hdisj hx
    have hxa : x ≠ a₀ := fun h => hTa₀ (h ▸ hx)
    have := key x (hTA hx)
    simp [p, q, hx, hxS, hxa] at this

/-- Validity makes the translated subset sums of `A \ {a₀}` pairwise distinct. -/
theorem IsValidMod.ssum_injOn {A : Finset (ZMod N)} (hA : IsValidMod A) {a₀ : ZMod N}
    (ha₀ : a₀ ∈ A) :
    Set.InjOn (ssum a₀) ((A.erase a₀).powerset : Set (Finset (ZMod N))) := by
  classical
  intro S hS T hT hcol
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset] at hS hT
  by_contra hne
  have hcol' : ssum a₀ (S \ T) = ssum a₀ (T \ S) := by
    unfold ssum at hcol ⊢
    exact Finset.sum_sdiff_eq_sum_sdiff_iff.2 hcol
  have hdisj : Disjoint (S \ T) (T \ S) :=
    Finset.disjoint_left.2 fun _ ha hb => (Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1
  have hne' : S \ T ≠ T \ S := by
    intro h
    apply hne
    have h1 : S \ T = ∅ := by
      have hd := hdisj
      rw [← h] at hd
      exact Finset.disjoint_self_iff_empty _ |>.1 hd
    have h2 : T \ S = ∅ := h ▸ h1
    exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.1 h1)
      (Finset.sdiff_eq_empty_iff_subset.1 h2)
  have hS' : S \ T ⊆ A.erase a₀ := Finset.sdiff_subset.trans hS
  have hT' : T \ S ⊆ A.erase a₀ := Finset.sdiff_subset.trans hT
  rcases le_total #(S \ T) #(T \ S) with hle | hle
  · exact hA.ssum_ne ha₀ hS' hT' hdisj hle hne' hcol'
  · exact hA.ssum_ne ha₀ hT' hS' hdisj.symm hle (Ne.symm hne') hcol'.symm

/-- **Lower bound `2^(n-1)`.**  A valid nonempty `A ⊆ ZMod N` has
`2 ^ (#A - 1) ≤ N`. -/
theorem IsValidMod.two_pow_le [NeZero N] {A : Finset (ZMod N)} (hA : IsValidMod A)
    (hne : A.Nonempty) : 2 ^ (#A - 1) ≤ N := by
  obtain ⟨a₀, ha₀⟩ := hne
  have h := Finset.card_le_card_of_injOn (ssum a₀) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (hA.ssum_injOn ha₀)
  rwa [Finset.card_powerset, Finset.card_erase_of_mem ha₀, Finset.card_univ,
    ZMod.card] at h

/-- **Sidon-type property.**  In a valid set, `x + w = y + z` with `x ≠ w` forces
`{x, w} = {y, z}`. -/
theorem IsValidMod.add_eq_add {A : Finset (ZMod N)} (hA : IsValidMod A)
    {x y z w : ZMod N} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hw : w ∈ A)
    (hxw : x ≠ w) (h : x + w = y + z) : (x = y ∧ w = z) ∨ (x = z ∧ w = y) := by
  classical
  by_contra hcon
  simp only [not_or, not_and] at hcon
  have hxy : x ≠ y := fun e => hcon.1 e (by subst e; exact add_left_cancel h)
  have hxz : x ≠ z := fun e => hcon.2 e (by subst e; rw [add_comm y x] at h; exact add_left_cancel h)
  let p : ZMod N → ℕ := fun a => (if a = y then 1 else 0) + (if a = z then 1 else 0)
  let q : ZMod N → ℕ := fun a => (if a = x then 1 else 0) + (if a = w then 1 else 0)
  have key := hA.eq_of_rival p q
    (by
      intro a _
      simp only [p, q]
      by_cases hax : a = x
      · subst hax
        simp [hxw]
      · simp only [hax, if_false, zero_add]
        split_ifs <;> omega)
    (by
      simp only [p, q, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hx, if_pos hy,
        if_pos hz, if_pos hw])
    (by
      simp only [p, q, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul,
        ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hx,
        if_pos hy, if_pos hz, if_pos hw]
      rw [h])
  have := key x hx
  simp [p, q, hxy, hxz, hxw] at this

/-- The Sidon-type property including the degenerate case `x = w`. -/
theorem IsValidMod.add_eq_add' {A : Finset (ZMod N)} (hA : IsValidMod A)
    {x y z w : ZMod N} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hw : w ∈ A)
    (h : x + w = y + z) : (x = y ∧ w = z) ∨ (x = z ∧ w = y) ∨ (x = w ∧ y = z) := by
  by_cases hxw : x = w
  · by_cases hyz : y = z
    · exact Or.inr (Or.inr ⟨hxw, hyz⟩)
    · rcases hA.add_eq_add hy hx hw hz hyz h.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (h1.trans (hxw.trans h2.symm)) hyz
      · exact absurd (h1.trans (hxw.symm.trans h2.symm)) hyz
  · exact (hA.add_eq_add hx hy hz hw hxw h).elim Or.inl (fun h' => Or.inr (Or.inl h'))

/-- In `ZMod N` (`N > 0`) there is at most one nonzero `h` with `2 * h = 0`. -/
theorem eq_of_two_mul_eq_zero [NeZero N] {h h' : ZMod N} (hh : 2 * h = 0) (hh' : 2 * h' = 0)
    (h0 : h ≠ 0) (h0' : h' ≠ 0) : h = h' := by
  have key : ∀ g : ZMod N, 2 * g = 0 → g ≠ 0 → 2 * g.val = N := by
    intro g hg hg0
    have hlt := ZMod.val_lt g
    have hpos : 0 < g.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero g).2 hg0)
    have hdvd : N ∣ 2 * g.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hg
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have hk2 : k < 2 := by
      by_contra hk2
      have := Nat.mul_le_mul_left N (not_lt.1 hk2)
      omega
    have hk1 : k = 1 := by omega
    subst hk1
    omega
  apply ZMod.val_injective N
  have := key h hh h0
  have := key h' hh' h0'
  omega

/-- A valid set contains at most one pair `{p, q}` whose difference has order two. -/
theorem IsValidMod.half_pair_unique [NeZero N] {A : Finset (ZMod N)} (hA : IsValidMod A)
    {p q r s : ZMod N} (hp : p ∈ A) (hq : q ∈ A) (hr : r ∈ A) (hs : s ∈ A)
    (hpq : p ≠ q) (hrs : r ≠ s) (h1 : 2 * (p - q) = 0) (h2 : 2 * (r - s) = 0) :
    (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  have e : p - q = r - s :=
    eq_of_two_mul_eq_zero h1 h2 (sub_ne_zero.2 hpq) (sub_ne_zero.2 hrs)
  have h : p + s = q + r := by linear_combination e
  rcases hA.add_eq_add' hp hq hr hs h with ⟨h3, _⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact absurd h3 hpq
  · exact Or.inl ⟨h3, h4.symm⟩
  · exact Or.inr ⟨h3, h4⟩

/-- **Lower bound `n (n - 1)`.**  A valid `A ⊆ ZMod N` has `#A * (#A - 1) ≤ N`. -/
theorem IsValidMod.card_mul_card_sub_one_le [NeZero N] {A : Finset (ZMod N)}
    (hA : IsValidMod A) : #A * (#A - 1) ≤ N := by
  classical
  -- pairs whose difference has order two, oriented by `val`
  let bad : ZMod N × ZMod N → Prop := fun xy => 2 * (xy.1 - xy.2) = 0 ∧ xy.1.val < xy.2.val
  have hgood : #(A.offDiag.filter fun xy => ¬ bad xy) ≤ N - 1 := by
    have h := Finset.card_le_card_of_injOn (fun xy : ZMod N × ZMod N => xy.1 - xy.2)
      (s := A.offDiag.filter fun xy => ¬ bad xy) (t := Finset.univ.erase 0)
      (by
        intro xy hxy
        simp only [Finset.coe_filter, Finset.mem_offDiag, Set.mem_setOf_eq] at hxy
        simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
          Set.mem_singleton_iff, true_and]
        exact sub_ne_zero.2 hxy.1.2.2)
      (by
        rintro ⟨x, y⟩ hxy ⟨z, w⟩ hzw (e : x - y = z - w)
        simp only [Finset.coe_filter, Finset.mem_offDiag, Set.mem_setOf_eq, bad] at hxy hzw
        have h : x + w = y + z := by linear_combination e
        rcases hA.add_eq_add' hxy.1.1 hxy.1.2.1 hzw.1.1 hzw.1.2.1 h with
          ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 hxy.1.2.2
        · rw [h1, h2]
        · subst h1 h2
          have h3 : 2 * (x - y) = 0 := by linear_combination e
          have h4 : 2 * (y - x) = 0 := by linear_combination -e
          have h5 := hxy.2
          have h6 := hzw.2
          simp only [h3, h4, true_and, not_lt] at h5 h6
          exact absurd (ZMod.val_injective N (le_antisymm h6 h5)) hxy.1.2.2)
    rwa [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at h
  have hbad : #(A.offDiag.filter bad) ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨p, q⟩ hpq ⟨r, s⟩ hrs
    simp only [Finset.mem_filter, Finset.mem_offDiag, bad] at hpq hrs
    rcases hA.half_pair_unique hpq.1.1 hpq.1.2.1 hrs.1.1 hrs.1.2.1 hpq.1.2.2 hrs.1.2.2
      hpq.2.1 hrs.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · subst h1 h2
      omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := A.offDiag) bad
  rw [Finset.offDiag_card] at hsplit
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hmul : #A * (#A - 1) = #A * #A - #A := by
    rw [Nat.mul_sub, mul_one]
  omega

/-- For `b ∈ A \ {a₀}`, the doubled difference `2 (b - a₀)` is not a translated
subset sum of a nonempty `T ⊆ A \ {a₀}`. -/
theorem IsValidMod.two_mul_ne_ssum {A : Finset (ZMod N)} (hA : IsValidMod A) {a₀ b : ZMod N}
    (ha₀ : a₀ ∈ A) (hb : b ∈ A.erase a₀) {T : Finset (ZMod N)} (hT : T ⊆ A.erase a₀)
    (hTne : T.Nonempty) : 2 * (b - a₀) ≠ ssum a₀ T := by
  classical
  intro hcol
  have hbA : b ∈ A := Finset.mem_of_mem_erase hb
  have hba : b ≠ a₀ := Finset.ne_of_mem_erase hb
  have hTA : T ⊆ A := hT.trans (Finset.erase_subset _ _)
  have hTa₀ : a₀ ∉ T := fun h => (Finset.mem_erase.1 (hT h)).1 rfl
  by_cases hbT : b ∈ T
  · -- then `b - a₀` is the translated sum of `T \ {b}`, contradicting injectivity
    have h1 : ssum a₀ T = (b - a₀) + ssum a₀ (T.erase b) :=
      (Finset.add_sum_erase T (fun x => x - a₀) hbT).symm
    have h2 : ssum a₀ {b} = ssum a₀ (T.erase b) := by
      have h3 : ssum a₀ {b} = b - a₀ := by simp [ssum]
      rw [h3]
      rw [h1] at hcol
      linear_combination hcol
    have h4 := hA.ssum_injOn ha₀
      (Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hb)))
      (Finset.mem_coe.2 (Finset.mem_powerset.2 ((Finset.erase_subset b T).trans hT))) h2
    have h5 : b ∈ T.erase b := h4 ▸ Finset.mem_singleton_self b
    simp at h5
  · have ht := Finset.card_pos.2 hTne
    let p : ZMod N → ℕ := fun a => (if a = b then 2 else 0) + (if a = a₀ then #T - 2 else 0)
    let q : ZMod N → ℕ := fun a => (if a ∈ T then 1 else 0) + (if a = a₀ then 2 - #T else 0)
    have key := hA.eq_of_rival p q
      (by
        intro a _
        simp only [p, q]
        by_cases haa : a = a₀
        · subst haa
          simp only [hTa₀, if_false, if_true, zero_add, hba.symm]
          omega
        · simp only [haa, if_false, add_zero]
          split_ifs <;> omega)
      (by
        simp only [p, q, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hbA, if_pos ha₀,
          Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hTA, Nat.cast_id]
        omega)
      (by
        simp only [p, q, Nat.cast_add, Nat.cast_ite, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
          add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
          if_pos hbA, if_pos ha₀, Finset.sum_ite_mem, Finset.inter_eq_right.2 hTA]
        rw [ssum_eq] at hcol
        rcases Nat.lt_or_ge #T 2 with hlt | hge
        · have h1 : #T = 1 := by omega
          rw [h1] at hcol ⊢
          norm_num
          linear_combination hcol
        · rw [Nat.cast_sub hge, Nat.sub_eq_zero_of_le hge]
          push_cast
          linear_combination hcol)
    have := key b hbA
    simp [p, q, hbT, hba] at this

/-- **Lower bound `2^(n-1) + n - 2`.**  A valid `A ⊆ ZMod N` with `#A ≥ 2` has
`2 ^ (#A - 1) + (#A - 2) ≤ N`: besides the `2^(n-1)` translated subset sums,
`ZMod N` contains `n - 2` distinct doubled differences `2 (b - a₀)`. -/
theorem IsValidMod.two_pow_add_le [NeZero N] {A : Finset (ZMod N)} (hA : IsValidMod A)
    (h2 : 2 ≤ #A) : 2 ^ (#A - 1) + (#A - 2) ≤ N := by
  classical
  -- `a₀, b₁` cover every pair of `A` whose difference has order two
  obtain ⟨a₀, b₁, ha₀, hb₁, hab, hsel⟩ : ∃ a₀ b₁, a₀ ∈ A ∧ b₁ ∈ A ∧ a₀ ≠ b₁ ∧
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 2 * (x - y) = 0 → x = a₀ ∨ x = b₁ := by
    by_cases hpair : ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ 2 * (p - q) = 0
    · obtain ⟨p, hp, q, hq, hpq, h2pq⟩ := hpair
      refine ⟨p, q, hp, hq, hpq, fun x hx y hy hxy h2xy => ?_⟩
      rcases hA.half_pair_unique hx hy hp hq hxy hpq h2xy h2pq with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    · simp only [not_exists, not_and] at hpair
      obtain ⟨a₀, ha₀, b₁, hb₁, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < #A)
      exact ⟨a₀, b₁, ha₀, hb₁, hne, fun x hx y hy hxy h2 => absurd h2 (hpair x hx y hy hxy)⟩
  have hb₁B : b₁ ∈ A.erase a₀ := Finset.mem_erase.2 ⟨hab.symm, hb₁⟩
  set X1 := (A.erase a₀).powerset.image (ssum a₀) with hX1def
  set X2 := ((A.erase a₀).erase b₁).image (fun b => 2 * (b - a₀)) with hX2def
  have hmem : ∀ b ∈ (A.erase a₀).erase b₁, b ∈ A ∧ b ≠ a₀ ∧ b ≠ b₁ := by
    intro b hb
    have h1 := Finset.mem_erase.1 hb
    have h2 := Finset.mem_erase.1 h1.2
    exact ⟨h2.2, h2.1, h1.1⟩
  have hX1 : #X1 = 2 ^ (#A - 1) := by
    rw [hX1def, Finset.card_image_of_injOn (hA.ssum_injOn ha₀), Finset.card_powerset,
      Finset.card_erase_of_mem ha₀]
  have hX2 : #X2 = #A - 2 := by
    rw [hX2def, Finset.card_image_of_injOn, Finset.card_erase_of_mem hb₁B,
      Finset.card_erase_of_mem ha₀]
    · omega
    · intro b hb b' hb' e
      by_contra hne
      have hb2 := hmem b (Finset.mem_coe.1 hb)
      have hb2' := hmem b' (Finset.mem_coe.1 hb')
      have e' : 2 * (b - b') = 0 := by linear_combination e
      rcases hsel b hb2.1 b' hb2'.1 hne e' with h | h
      · exact hb2.2.1 h
      · exact hb2.2.2 h
  have hdisj : Disjoint X1 X2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hX1def, Finset.mem_image] at hx1
    rw [hX2def, Finset.mem_image] at hx2
    obtain ⟨T, hT, rfl⟩ := hx1
    obtain ⟨b, hb, e⟩ := hx2
    have hb2 := hmem b hb
    rw [Finset.mem_powerset] at hT
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · subst hTe
      have e' : 2 * (b - a₀) = 0 := by simpa [ssum] using e
      rcases hsel b hb2.1 a₀ ha₀ hb2.2.1 e' with h | h
      · exact hb2.2.1 h
      · exact hb2.2.2 h
    · exact hA.two_mul_ne_ssum ha₀ (Finset.mem_erase.2 ⟨hb2.2.1, hb2.1⟩) hT hTne e
  have hunion := Finset.card_union_eq_card_add_card.2 hdisj
  have hle : #(X1 ∪ X2) ≤ N := (Finset.card_le_univ _).trans (by rw [ZMod.card])
  omega

/-- **Conjecture 1 for `n ≤ 4`.**  Here `minModulus n = n * (n - 1)`, so the
bound `IsValidMod.card_mul_card_sub_one_le` is exactly the conjectured one. -/
theorem statement_of_le_four : ∀ n N : ℕ, 2 ≤ n → n ≤ 4 → 0 < N → N < minModulus n →
    ∀ A : Finset (ZMod N), #A = n → ¬ IsValidMod A := by
  intro n N h2 h4 hN hlt A hA hvalid
  haveI : NeZero N := ⟨by omega⟩
  have hbound := hvalid.card_mul_card_sub_one_le
  rw [hA] at hbound
  have hlog2 : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hlog3 : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have hlog4 : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  interval_cases n <;> simp only [minModulus, hlog2, hlog3, hlog4] at hlt <;> omega

end AgenticConjectures.MinModulusMultisetSum
