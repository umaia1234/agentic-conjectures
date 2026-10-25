import Mathlib

/-!
# Frankl's union-closed sets conjecture — classical special cases

Frankl's conjecture asserts that every finite union-closed family of finite sets other than
`{∅}` has an element lying in at least half of its members. It is open; this module records it
as `statement` (a `Prop`, never proved here) and Lean-verifies classical special cases against a
term-for-term copy of the upstream definition `IsUnionClosed`:

* `singleton_mem` (Sarvate–Renaud): if `{a} ∈ A`, then `a` lies in at least half of the members
  (`half_le_card_filter_mem_of_singleton_mem`). The members avoiding `a` inject into the members
  containing `a` via `x ↦ x ∪ {a}`.
* `pair_mem` (Sarvate–Renaud): if `{a, b} ∈ A`, then `a` or `b` lies in at least half of the
  members. The members avoiding both inject into the members containing both via
  `x ↦ x ∪ {a, b}`, whence `#A ≤ #{x ∈ A | a ∈ x} + #{x ∈ A | b ∈ x}`.
* `sum_card_filter_mem_eq_sum_card` and `exists_card_le_two_mul_card_filter_mem_of_average`:
  double counting `∑ i ∈ U, #{x ∈ A | i ∈ x} = ∑ x ∈ A, #x` over the union `U = A.sup id`, and the
  averaging lemma: if the average member size is at least `#U / 2`, some element of `U` lies in
  at least half of the members.
* `union_closed_of_card_sup_le_six`: the conjecture for families whose union has at most six
  elements, with the corollaries `univ_card_le_six` (ground type of size at most six) and
  `univ_card_two`. A member of size one or two is handled by the two cases above; otherwise every
  nonempty member has at least `3 ≥ #U / 2` elements, the union `U` is itself a member and makes
  up for a possible member `∅`, and the averaging lemma applies.

All of this is classical: the 1-set and 2-set cases are due to Sarvate and Renaud (Ars Combin. 27
(1989), 149–153), the averaging lemma is standard double counting, and the conjecture is known
for ground sets of up to 12 elements (Vučković–Živković 2017). No novelty is claimed, and the
general conjecture remains open.

## Correspondence with the upstream snapshot

Upstream is `problems/frankl-union-closed/upstream/UnionClosed.lean`
(google-deepmind/formal-conjectures, `FormalConjectures/Wikipedia/UnionClosed.lean`).

* `IsUnionClosed` is upstream `UnionClosed.IsUnionClosed`, copied term for term: an `abbrev` for
  `∀ᵉ (X ∈ A) (Y ∈ A), X ∪ Y ∈ A` on `A : Finset (Finset n)` with `[DecidableEq n]`.
* `statement` is upstream `UnionClosed.union_closed` with its section variables bound
  explicitly. Families are `Finset`s of `Finset`s over an arbitrary ground type, hence finite
  families of finite sets; "at least half" is the rational inequality
  `(1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}`, so neither division nor truncated subtraction occurs.
  The family `{∅}` is excluded by `A ≠ {∅}`; otherwise `∅` may be a member. The empty family is
  allowed and satisfies the conclusion trivially for any `i`, which is why upstream assumes
  `[Nonempty n]`. Upstream's `Type*` makes `union_closed` universe polymorphic; `statement`
  takes the universe as a parameter, `statement.{u}`.
* `singleton_mem` has exactly the hypotheses and conclusion of upstream
  `union_closed.variants.singleton_mem` (upstream already proves it; it is re-proved here against
  the copied definition). `univ_card_two` is upstream `union_closed.variants.univ_card_two`
  verbatim (upstream proves it by `decide +revert +kernel`; here it is a corollary of
  `univ_card_le_six`). `univ_card_le_six` has the hypotheses and conclusion of upstream
  `union_closed.variants.univ_card` with `Fintype.card n ≤ 12` strengthened to
  `Fintype.card n ≤ 6`, so it is a weaker theorem than the sorry-backed upstream variant.
* `pair_mem`, the counting forms and the averaging lemmas have no upstream counterpart. The
  special cases need neither `A ≠ {∅}` nor `[Nonempty n]`: the member `{a}` or `{a, b}` excludes
  `A = {∅}` and supplies the witness. `pair_mem` does not assume `a ≠ b` (for `a = b` it is the
  singleton case).
-/

namespace AgenticConjectures.FranklUnionClosed

open Finset

universe u

variable {n : Type*} [DecidableEq n] {A : Finset (Finset n)}

/-- A family is union-closed if the union of any two members is a member
(upstream `UnionClosed.IsUnionClosed`, term for term). -/
abbrev IsUnionClosed (A : Finset (Finset n)) : Prop :=
  ∀ᵉ (X ∈ A) (Y ∈ A), X ∪ Y ∈ A

/-- **Frankl's union-closed sets conjecture** (open; recorded as a `Prop`, not proved here):
every finite union-closed family other than `{∅}` has an element in at least half of its members.
This is upstream `UnionClosed.union_closed` with its section variables bound explicitly. -/
def statement : Prop :=
  ∀ (n : Type u) [DecidableEq n] [Nonempty n] (A : Finset (Finset n)),
    A ≠ {∅} → IsUnionClosed A → ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x}

/-! ### Singletons -/

/-- If `{a} ∈ A`, then `x ↦ x ∪ {a}` (written `insert a x`) injects the members avoiding `a` into
the members containing `a`. -/
theorem card_filter_notMem_le_of_singleton_mem (h_union_closed : IsUnionClosed A)
    {a : n} (ha : {a} ∈ A) : #{x ∈ A | a ∉ x} ≤ #{x ∈ A | a ∈ x} := by
  refine card_le_card_of_injOn (insert a) ?_ ?_
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq] at hx ⊢
    refine ⟨?_, mem_insert_self a x⟩
    rw [insert_eq]
    exact h_union_closed _ ha _ hx.1
  · intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq] at hx hy
    have := congrArg (·.erase a) hxy
    simp only at this
    rwa [erase_insert hx.2, erase_insert hy.2] at this

/-- **Singleton case** (Sarvate–Renaud), counting form: if `{a} ∈ A`, then
`#A ≤ 2 * #{x ∈ A | a ∈ x}`. -/
theorem card_le_two_mul_card_filter_mem_of_singleton_mem (h_union_closed : IsUnionClosed A)
    {a : n} (ha : {a} ∈ A) : #A ≤ 2 * #{x ∈ A | a ∈ x} := by
  have h₁ := card_filter_notMem_le_of_singleton_mem h_union_closed ha
  have h₂ := card_filter_add_card_filter_not (s := A) (fun x => a ∈ x)
  omega

/-- **Singleton case** (Sarvate–Renaud): if `{a} ∈ A`, then `a` lies in at least half of the
members, in the upstream form `(1 / 2 : ℚ) * #A ≤ #{x ∈ A | a ∈ x}`. -/
theorem half_le_card_filter_mem_of_singleton_mem (h_union_closed : IsUnionClosed A)
    {a : n} (ha : {a} ∈ A) : (1 / 2 : ℚ) * #A ≤ #{x ∈ A | a ∈ x} := by
  have h : ((#A : ℕ) : ℚ) ≤ 2 * (#{x ∈ A | a ∈ x} : ℕ) := by
    exact_mod_cast card_le_two_mul_card_filter_mem_of_singleton_mem h_union_closed ha
  linarith

/-- Upstream `union_closed.variants.singleton_mem`, with the same hypotheses and conclusion. -/
theorem singleton_mem (h_union_closed : IsUnionClosed A) (i : n) (hi : {i} ∈ A) :
    ∃ i, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x} :=
  ⟨i, half_le_card_filter_mem_of_singleton_mem h_union_closed hi⟩

/-! ### Two-element sets -/

/-- If `{a, b} ∈ A`, then `x ↦ {a, b} ∪ x` injects the members avoiding both `a` and `b` into the
members containing both. -/
theorem card_filter_not_or_le_of_pair_mem (h_union_closed : IsUnionClosed A) {a b : n}
    (hab : {a, b} ∈ A) : #{x ∈ A | ¬(a ∈ x ∨ b ∈ x)} ≤ #{x ∈ A | a ∈ x ∧ b ∈ x} := by
  refine card_le_card_of_injOn ({a, b} ∪ ·) ?_ ?_
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq] at hx ⊢
    exact ⟨h_union_closed _ hab _ hx.1, by simp, by simp⟩
  · intro x hx y hy hxy
    simp only [coe_filter, Set.mem_setOf_eq, not_or] at hx hy
    have hdx : Disjoint ({a, b} : Finset n) x := by simp [hx.2.1, hx.2.2]
    have hdy : Disjoint ({a, b} : Finset n) y := by simp [hy.2.1, hy.2.2]
    have := congrArg (· \ ({a, b} : Finset n)) hxy
    simp only at this
    rwa [union_sdiff_cancel_left hdx, union_sdiff_cancel_left hdy] at this

/-- **Two-element case** (Sarvate–Renaud), counting form: if `{a, b} ∈ A`, then
`#A ≤ #{x ∈ A | a ∈ x} + #{x ∈ A | b ∈ x}`. -/
theorem card_le_card_filter_mem_add_card_filter_mem_of_pair_mem
    (h_union_closed : IsUnionClosed A) {a b : n} (hab : {a, b} ∈ A) :
    #A ≤ #{x ∈ A | a ∈ x} + #{x ∈ A | b ∈ x} := by
  have h₁ := card_filter_not_or_le_of_pair_mem h_union_closed hab
  have h₂ := card_filter_add_card_filter_not (s := A) (fun x => a ∈ x ∨ b ∈ x)
  have h₃ := card_union_add_card_inter {x ∈ A | a ∈ x} {x ∈ A | b ∈ x}
  rw [← filter_or, ← filter_and] at h₃
  omega

/-- **Two-element case** (Sarvate–Renaud): if `{a, b} ∈ A`, then `a` or `b` lies in at least
half of the members. No `a ≠ b` is needed. -/
theorem pair_mem (h_union_closed : IsUnionClosed A) {a b : n} (hab : {a, b} ∈ A) :
    (1 / 2 : ℚ) * #A ≤ #{x ∈ A | a ∈ x} ∨ (1 / 2 : ℚ) * #A ≤ #{x ∈ A | b ∈ x} := by
  have h : ((#A : ℕ) : ℚ) ≤ (#{x ∈ A | a ∈ x} : ℕ) + (#{x ∈ A | b ∈ x} : ℕ) := by
    exact_mod_cast card_le_card_filter_mem_add_card_filter_mem_of_pair_mem h_union_closed hab
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  linarith [hc.1, hc.2]

/-- The two-element case in the existential form of the upstream variants. -/
theorem exists_of_pair_mem (h_union_closed : IsUnionClosed A) {a b : n} (hab : {a, b} ∈ A) :
    ∃ i, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x} :=
  (pair_mem h_union_closed hab).elim (⟨a, ·⟩) (⟨b, ·⟩)

/-! ### Averaging -/

/-- Double counting over the union `A.sup id`: the element frequencies add up to the total size
of the members. -/
theorem sum_card_filter_mem_eq_sum_card (A : Finset (Finset n)) :
    ∑ i ∈ A.sup id, #{x ∈ A | i ∈ x} = ∑ x ∈ A, #x := by
  have h : ∀ x ∈ A, #x = #(A.sup id ∩ x) := by
    intro x hx
    have hsub : x ⊆ A.sup id := le_sup (f := id) hx
    rw [inter_eq_right.mpr hsub]
  rw [sum_congr rfl h]
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- **Averaging lemma**: if the average member size is at least half the size of the union
`A.sup id` (multiplied out: `#(A.sup id) * #A ≤ 2 * ∑ x ∈ A, #x`), then some element of the
union lies in at least half of the members. Union-closedness is not needed. -/
theorem exists_card_le_two_mul_card_filter_mem_of_average (hU : (A.sup id).Nonempty)
    (h : #(A.sup id) * #A ≤ 2 * ∑ x ∈ A, #x) :
    ∃ i ∈ A.sup id, #A ≤ 2 * #{x ∈ A | i ∈ x} := by
  apply exists_le_of_sum_le hU
  rw [sum_const, smul_eq_mul, ← mul_sum, sum_card_filter_mem_eq_sum_card]
  exact h

/-! ### Families with a small union -/

/-- A nonempty union-closed family contains the union of all its members. -/
theorem sup_mem_of_nonempty (h_union_closed : IsUnionClosed A) (hA : A.Nonempty) :
    A.sup id ∈ A := by
  have hsc : SupClosed (A : Set (Finset n)) := fun x hx y hy => h_union_closed x hx y hy
  exact hsc.finsetSup_mem hA fun x hx => hx

/-- **Frankl's conjecture for families whose union has at most six elements**, with the
hypotheses of upstream `union_closed` plus `#(A.sup id) ≤ 6`. -/
theorem union_closed_of_card_sup_le_six [Nonempty n] (h_ne_singleton_empty : A ≠ {∅})
    (h_union_closed : IsUnionClosed A) (h_card : #(A.sup id) ≤ 6) :
    ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x} := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨Classical.arbitrary n, by simp⟩
  by_cases h1 : ∃ x ∈ A, #x = 1
  · obtain ⟨x, hx, hx1⟩ := h1
    obtain ⟨a, rfl⟩ := card_eq_one.mp hx1
    exact singleton_mem h_union_closed a hx
  by_cases h2 : ∃ x ∈ A, #x = 2
  · obtain ⟨x, hx, hx2⟩ := h2
    obtain ⟨a, b, -, rfl⟩ := card_eq_two.mp hx2
    exact exists_of_pair_mem h_union_closed hx
  push Not at h1 h2
  set U := A.sup id
  have hUA : U ∈ A := sup_mem_of_nonempty h_union_closed hA
  have hUne : U.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hU
    apply h_ne_singleton_empty
    refine eq_singleton_iff_unique_mem.mpr ⟨hU ▸ hUA, fun x hx => ?_⟩
    exact subset_empty.mp (hU ▸ le_sup (f := id) hx)
  -- Every nonempty member has at least three elements, hence at least half of `#U ≤ 6`.
  have h3 : ∀ x ∈ A, x ≠ ∅ → 3 ≤ #x := by
    intro x hx hne
    have := card_pos.mpr (nonempty_iff_ne_empty.mpr hne)
    have := h1 x hx
    have := h2 x hx
    omega
  -- `U` contributes `#U = #U / 2 + #U / 2`, making up for a possible member `∅`.
  have hsum : #U + ∑ x ∈ A.erase U, #x = ∑ x ∈ A, #x := add_sum_erase A card hUA
  have hsum' : ∑ x ∈ (A.erase U).erase ∅, #x = ∑ x ∈ A.erase U, #x :=
    sum_erase _ card_empty
  have hlow : #U * #((A.erase U).erase ∅) ≤ 2 * ∑ x ∈ (A.erase U).erase ∅, #x := by
    rw [card_eq_sum_ones ((A.erase U).erase ∅), mul_sum, mul_sum]
    apply sum_le_sum
    intro x hx
    simp only [mem_erase] at hx
    have := h3 x hx.2.2 hx.1
    omega
  have hcard : #A - 2 ≤ #((A.erase U).erase ∅) := by
    have := pred_card_le_card_erase (s := A) (a := U)
    have := pred_card_le_card_erase (s := A.erase U) (a := ∅)
    omega
  have hmul : #U * #A ≤ #U * (#A - 2) + #U * 2 := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  have hmono : #U * (#A - 2) ≤ #U * #((A.erase U).erase ∅) := Nat.mul_le_mul_left _ hcard
  have havg : #U * #A ≤ 2 * ∑ x ∈ A, #x := by omega
  obtain ⟨i, -, hi⟩ := exists_card_le_two_mul_card_filter_mem_of_average hUne havg
  refine ⟨i, ?_⟩
  have h' : ((#A : ℕ) : ℚ) ≤ 2 * (#{x ∈ A | i ∈ x} : ℕ) := by exact_mod_cast hi
  linarith

/-- Upstream `union_closed.variants.univ_card` with `Fintype.card n ≤ 12` strengthened to
`Fintype.card n ≤ 6` (all other hypotheses and the conclusion unchanged). -/
theorem univ_card_le_six [Fintype n] [Nonempty n] (h_ne_singleton_empty : A ≠ {∅})
    (h_union_closed : IsUnionClosed A) (h_card : Fintype.card n ≤ 6) :
    ∃ i : n, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x} :=
  union_closed_of_card_sup_le_six h_ne_singleton_empty h_union_closed
    ((card_le_univ _).trans h_card)

/-- Upstream `union_closed.variants.univ_card_two`, verbatim. -/
theorem univ_card_two (A : Finset (Finset (Fin 2)))
    (h_ne_singleton_empty : A ≠ {∅})
    (h_union_closed : IsUnionClosed A) :
    ∃ i, (1 / 2 : ℚ) * #A ≤ #{x ∈ A | i ∈ x} :=
  univ_card_le_six h_ne_singleton_empty h_union_closed (by simp)

end AgenticConjectures.FranklUnionClosed
