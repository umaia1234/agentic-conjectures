import Mathlib

/-!
# CRIM: stacking a losing partition under a losing hook

Source: Ina Bašić, Eric Gottlieb, Matjaž Krnc, *CRIM: A Natural Game on Integer Partitions*,
arXiv:2606.16828v1 (2026). `statement` is the paper's Conjecture `conj:bloby`:

> Let `λ` and `Γ_{r,c}` be losing and suppose `λ* = Γ_{r,c} ◁ λ` is defined. Then `λ* ∈ P`.

`mainConjecture` is the paper's Conjecture `conj:main`: every P-position has even rank.
There is no Formal Conjectures statement of either; both formal statements are ours.

## Readings (checked against the TeX)

* A partition is a weakly decreasing list of positive naturals (`IsPartition`); `[]` is the
  empty partition. `part l i` is `λ_i` (1-indexed, `0` past the end; `part l 0` is unused).
* A CRIM move removes one row or one column of the Young diagram and reattaches the pieces:
  deleting row `i` is `List.eraseIdx`; deleting column `j` (`1 ≤ j ≤ λ₁`) is `delCol`, which
  lowers every part `≥ j` by one and drops the parts that become `0`.
* Normal play: `isP` is defined by well-founded recursion on `|λ| + ℓ(λ)`, so `[]` is P.
  "Losing" means P-position (`IsP`).
* `rank l = |ℓ(λ) − λ₁|`, Dyson's rank as defined in the paper's §2.1.
* `durfee l` is the greatest `d` with `d ≤ λ_d`, searched in `0 ≤ d ≤ ℓ(λ)` (larger `d` fail
  because `λ_d = 0`).
* `stack l m` is the paper's stack `λ ◁ μ`, term for term: with `d = d(λ)` and `k = ℓ(μ)` it is
  defined iff `λ_{d+i} = d` for `1 ≤ i ≤ k` and `λ_d ≥ d + μ₁` (with `μ₁ = 0` for `μ = []`),
  and then it is `[λ₁, …, λ_d, λ_{d+1} + μ₁, …, λ_{d+k} + μ_k, λ_{d+k+1}, …, λ_r]`.
* `hook r c = [c, 1^{r-1}] = Γ_{r,c}` with `r, c ≥ 1`. Rows (`r = 1`) and columns (`c = 1`)
  count as hooks; they are never P (`isP_hook_iff`), and for them the stack is defined only
  when `μ = []`.
* `λ = []` is allowed and trivial: `Γ_{r,c} ◁ [] = Γ_{r,c}`.

## Results

* `statement_holds : statement` and `mainConjecture_holds : mainConjecture`: both conjectures
  hold. conj:main follows from `isP_ofPairs_iff`, and conj:bloby from conj:main by
  `statement_of_mainConjecture`.
* `isP_ofPairs_iff` (the classification in Zijian Zeng, *A Boundary-Word Classification of
  Losing Positions in CRIM*, an unrefereed 2026 preprint; formalized here): write a
  partition through its run pairs `p = [(a₁, b₁), …, (a_k, b_k)]` (`ofPairs`, `exists_ofPairs`).
  It is a P-position iff the boundary length `plen p = ℓ(λ) + λ₁` and the end-peeling
  statistic `endM p` are both even.
* `stack_hook` (hook-stack reduction): for `c ≥ 1`, `Γ_{r,c} ◁ μ` is defined iff
  `ℓ(μ) ≤ r − 1` and `μ₁ ≤ c − 1`, and then it is `hookStack r c μ =
  [c, 1 + μ₁, …, 1 + μ_k, 1^{r−1−k}]`.
* `isP_hook_iff` (the paper's `lem:hook`), `isP_pair_iff` (`thm:2parts`) and
  `isP_twoCol_iff` (two columns, the conjugate statement).
* `isP_stack_of_localEvenRank` (sharp local form): conj:bloby holds for a losing `λ` as soon
  as every position reached from `λ` by repeating "a move, then a move onto a P-position"
  (`PChain`) has even rank.
* `statement_of_mainConjecture : mainConjecture → statement`.
* `statement_of_mainConjecture_le`: conj:main for partitions of size `≤ N` implies conj:bloby
  for every `λ` of size `≤ N` and every hook.
* `statement_of_length_le_two`, `statement_of_part_one_le_two`: conj:bloby holds
  unconditionally when `λ` has at most two rows or at most two columns.

## Proof idea

The second player answers on `X = Γ_{r,c} ◁ μ` (induction on `r + c`): row 1 with column 1
and vice versa (both reach `μ`); a move inside `μ` with `μ`'s own winning answer, played in
the shifted rows or columns (special replies `[c − 1, a]` when `r = 3` and `[2^a, 1^{r−1−a}]`
when `c = 3`); a leg row with another leg row or the last arm column, and an arm column with
another arm column or a leg row. The answer fails to exist only for
`(r, c) = (ℓ(μ) + 2, μ₁ + 1)` or `(ℓ(μ) + 1, μ₁ + 2)`, and with `r ≡ c (mod 2)` both force
`rank μ` to be odd.

For conj:main, a CRIM move deletes one letter of the boundary word `0^{a₁}1^{b₁}⋯0^{a_k}1^{b_k}`
and then strips leading `1`s and trailing `0`s (`mem_moves_ofPairs`, the six cases of `PMove`).
Zeng's lemmas show that "even length and even `M`" satisfies the P-recursion of this game
(`pairs_classification`). The argument is Zeng's; the Lean proof is ours.
-/

namespace AgenticConjectures.CrimHookStacks

/-! ## The game -/

/-- A partition: a weakly decreasing list of positive integers (its parts, i.e. rows). -/
def IsPartition (l : List ℕ) : Prop := l.Pairwise (· ≥ ·) ∧ ∀ x ∈ l, 0 < x

/-- The `i`-th part `λ_i` (1-indexed), and `0` past the last part. -/
def part (l : List ℕ) (i : ℕ) : ℕ := l.getD (i - 1) 0

/-- Delete column `j`: every part `≥ j` drops by one, and parts that become `0` vanish. -/
def delCol (l : List ℕ) (j : ℕ) : List ℕ :=
  (l.map fun x => if j ≤ x then x - 1 else x).filter (· ≠ 0)

/-- The CRIM moves: delete one row, or delete one column `j` with `1 ≤ j ≤ λ₁`. -/
def moves (l : List ℕ) : List (List ℕ) :=
  (List.range l.length).map l.eraseIdx ++ (List.range' 1 (part l 1)).map (delCol l)

theorem delCol_nil (j : ℕ) : delCol [] j = [] := rfl

theorem delCol_cons (x : ℕ) (t : List ℕ) (j : ℕ) :
    delCol (x :: t) j =
      if (if j ≤ x then x - 1 else x) = 0 then delCol t j
      else (if j ≤ x then x - 1 else x) :: delCol t j := by
  simp only [delCol, List.map_cons, List.filter_cons]
  split_ifs <;> simp_all

theorem sum_add_length_eraseIdx_lt :
    ∀ {l : List ℕ} {i : ℕ}, i < l.length →
      (l.eraseIdx i).sum + (l.eraseIdx i).length < l.sum + l.length
  | [], _, h => by simp at h
  | x :: t, 0, _ => by simp; omega
  | x :: t, i + 1, h => by
    have := sum_add_length_eraseIdx_lt (l := t) (i := i) (by simpa using h)
    simp; omega

theorem sum_add_length_delCol_le (j : ℕ) :
    ∀ l : List ℕ, (delCol l j).sum + (delCol l j).length ≤ l.sum + l.length
  | [] => by simp [delCol_nil]
  | x :: t => by
    have := sum_add_length_delCol_le j t
    rw [delCol_cons]; split_ifs <;> simp <;> omega

theorem sum_add_length_delCol_lt {l : List ℕ} {j : ℕ} (hj : 1 ≤ j) (hj' : j ≤ part l 1) :
    (delCol l j).sum + (delCol l j).length < l.sum + l.length := by
  cases l with
  | nil => simp [part] at hj'; omega
  | cons x t =>
    have := sum_add_length_delCol_le j t
    simp [part] at hj'
    rw [delCol_cons]; split_ifs <;> simp <;> omega

theorem mem_moves {l m : List ℕ} :
    m ∈ moves l ↔ (∃ i < l.length, l.eraseIdx i = m) ∨
      (∃ j, 1 ≤ j ∧ j ≤ part l 1 ∧ delCol l j = m) := by
  simp only [moves, List.mem_append, List.mem_map, List.mem_range, List.mem_range'_1]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, ⟨hj, hj'⟩, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨j, hj, by omega, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, hj', rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨j, ⟨hj, by omega⟩, rfl⟩

theorem lt_of_mem_moves {l m : List ℕ} (h : m ∈ moves l) :
    m.sum + m.length < l.sum + l.length := by
  rcases mem_moves.1 h with ⟨i, hi, rfl⟩ | ⟨j, hj, hj', rfl⟩
  · exact sum_add_length_eraseIdx_lt hi
  · exact sum_add_length_delCol_lt hj hj'

/-- `isP l`: the player to move from `l` loses (normal play: `[]` is losing), by
well-founded recursion on `|λ| + ℓ(λ)`, which every move decreases. -/
def isP (l : List ℕ) : Bool :=
  (moves l).attach.all fun ⟨m, _⟩ => !isP m
termination_by l.sum + l.length
decreasing_by exact lt_of_mem_moves ‹_›

/-- `λ` is a P-position ("losing"). -/
def IsP (l : List ℕ) : Prop := isP l = true

theorem isP_iff (l : List ℕ) : IsP l ↔ ∀ m ∈ moves l, ¬ IsP m := by
  unfold IsP
  rw [isP]
  simp [List.all_eq_true]

theorem isP_nil : IsP [] := (isP_iff []).2 (by simp [moves, part])

/-- To show `l` is P, answer every move with a move onto a P-position. -/
theorem isP_of_forall {l : List ℕ} (h : ∀ m ∈ moves l, ∃ m' ∈ moves m, IsP m') : IsP l :=
  (isP_iff l).2 fun m hm hP => by
    obtain ⟨m', hm', hP'⟩ := h m hm
    exact (isP_iff m).1 hP m' hm' hP'

theorem not_isP_of_mem {l m : List ℕ} (hm : m ∈ moves l) (hP : IsP m) : ¬ IsP l :=
  fun hl => (isP_iff l).1 hl m hm hP

theorem eraseIdx_mem_moves {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l.eraseIdx i ∈ moves l := mem_moves.2 (Or.inl ⟨i, h, rfl⟩)

theorem delCol_mem_moves {l : List ℕ} {j : ℕ} (h : 1 ≤ j) (h' : j ≤ part l 1) :
    delCol l j ∈ moves l := mem_moves.2 (Or.inr ⟨j, h, h', rfl⟩)

/-! ## Partitions are closed under moves -/

theorem part_one_cons (x : ℕ) (t : List ℕ) : part (x :: t) 1 = x := rfl

theorem part_one_nil : part [] 1 = 0 := rfl

theorem part_one_le {m : List ℕ} {B : ℕ} (h : ∀ z ∈ m, z ≤ B) : part m 1 ≤ B := by
  cases m with
  | nil => simp [part_one_nil]
  | cons x t => exact h x (by simp)

theorem le_part_one {l : List ℕ} (hl : IsPartition l) {x : ℕ} (hx : x ∈ l) :
    x ≤ part l 1 := by
  cases l with
  | nil => simp at hx
  | cons y t =>
    rw [part_one_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · exact List.rel_of_pairwise_cons hl.1 hx

theorem IsPartition.eraseIdx {l : List ℕ} (h : IsPartition l) (i : ℕ) :
    IsPartition (l.eraseIdx i) :=
  ⟨h.1.sublist (List.eraseIdx_sublist l i), fun x hx => h.2 x (List.mem_of_mem_eraseIdx hx)⟩

theorem colMap_mono (j : ℕ) {x y : ℕ} (h : x ≤ y) :
    (if j ≤ x then x - 1 else x) ≤ (if j ≤ y then y - 1 else y) := by
  split_ifs <;> omega

theorem mem_delCol {l : List ℕ} {j z : ℕ} :
    z ∈ delCol l j ↔ z ≠ 0 ∧ ∃ x ∈ l, (if j ≤ x then x - 1 else x) = z := by
  simp only [delCol, List.mem_filter, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h0⟩
    exact ⟨h0, x, hx, rfl⟩
  · rintro ⟨h0, x, hx, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, h0⟩

theorem IsPartition.delCol {l : List ℕ} (h : IsPartition l) (j : ℕ) :
    IsPartition (delCol l j) := by
  refine ⟨?_, fun z hz => Nat.pos_of_ne_zero (mem_delCol.1 hz).1⟩
  have hmap : (l.map fun x => if j ≤ x then x - 1 else x).Pairwise (· ≥ ·) :=
    List.Pairwise.map _ (fun a b (hab : a ≥ b) => colMap_mono j hab) h.1
  exact hmap.filter _

theorem IsPartition.of_mem_moves {l m : List ℕ} (h : IsPartition l) (hm : m ∈ moves l) :
    IsPartition m := by
  rcases mem_moves.1 hm with ⟨i, _, rfl⟩ | ⟨j, _, _, rfl⟩
  · exact h.eraseIdx i
  · exact h.delCol j

theorem part_one_eraseIdx_le {l : List ℕ} (hl : IsPartition l) (i : ℕ) :
    part (l.eraseIdx i) 1 ≤ part l 1 :=
  part_one_le fun _ hz => le_part_one hl (List.mem_of_mem_eraseIdx hz)

/-- Deleting a column `j ≤ λ₁` shortens the first row. -/
theorem part_one_delCol_lt {l : List ℕ} (hl : IsPartition l) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ part l 1) : part (delCol l j) 1 + 1 ≤ part l 1 := by
  have hpos : 0 < part l 1 := by
    cases l with
    | nil => simp [part_one_nil] at hj; omega
    | cons x t => exact hl.2 x (by simp)
  have := part_one_le (m := delCol l j) (B := part l 1 - 1) fun z hz => by
    obtain ⟨-, x, hx, rfl⟩ := mem_delCol.1 hz
    have := le_part_one hl hx
    split_ifs <;> omega
  omega

theorem part_one_delCol_le {l : List ℕ} (hl : IsPartition l) (j : ℕ) :
    part (delCol l j) 1 ≤ part l 1 :=
  part_one_le fun z hz => by
    obtain ⟨-, x, hx, rfl⟩ := mem_delCol.1 hz
    have := le_part_one hl hx
    split_ifs <;> omega

theorem length_delCol_le (l : List ℕ) (j : ℕ) : (delCol l j).length ≤ l.length := by
  unfold delCol
  exact (List.length_filter_le _ _).trans (by simp)

/-! ## Rows and columns are N-positions -/

theorem not_isP_single (x : ℕ) : ¬ IsP [x] :=
  not_isP_of_mem (eraseIdx_mem_moves (l := [x]) (i := 0) (by simp)) isP_nil

theorem delCol_one_eq_nil : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ 1) → delCol l 1 = []
  | [], _ => rfl
  | x :: t, h => by
    rw [delCol_cons, delCol_one_eq_nil fun y hy => h y (by simp [hy])]
    have := h x (by simp)
    split_ifs <;> simp_all

theorem not_isP_of_part_one_le_one {l : List ℕ} (hl : IsPartition l) (hne : l ≠ [])
    (h1 : part l 1 ≤ 1) : ¬ IsP l := by
  have hpos : 1 ≤ part l 1 := by
    cases l with
    | nil => exact absurd rfl hne
    | cons x t => exact hl.2 x (by simp)
  refine not_isP_of_mem (delCol_mem_moves (j := 1) le_rfl hpos) ?_
  rw [delCol_one_eq_nil fun x hx => (le_part_one hl hx).trans h1]
  exact isP_nil

/-- A nonempty P-position has at least two rows and at least two columns. -/
theorem two_le_of_isP {l : List ℕ} (hl : IsPartition l) (hP : IsP l) (hne : l ≠ []) :
    2 ≤ l.length ∧ 2 ≤ part l 1 := by
  refine ⟨?_, ?_⟩
  · match l, hne, hP with
    | [x], _, hP => exact absurd hP (not_isP_single x)
    | _ :: _ :: _, _, _ => simp
  · by_contra h
    exact not_isP_of_part_one_le_one hl hne (by omega) hP

/-! ## Rank, Durfee length, stacks, hooks, and the two conjectures -/

/-- Dyson's rank `|r − λ₁|`, where `r = ℓ(λ)` is the number of rows. -/
def rank (l : List ℕ) : ℕ := Int.natAbs ((l.length : ℤ) - (part l 1 : ℤ))

/-- The Durfee length: the greatest `d` with `d ≤ λ_d` (searched in `0 ≤ d ≤ ℓ(λ)`;
no larger `d` qualifies since `λ_d = 0` there). -/
def durfee (l : List ℕ) : ℕ := Nat.findGreatest (fun d => d ≤ part l d) l.length

/-- The stack `λ ◁ μ` of the paper, `none` when undefined: with `d = d(λ)` and `k = ℓ(μ)`
it is defined iff `λ_{d+i} = d` for all `1 ≤ i ≤ k` and `λ_d ≥ d + μ₁`, and then it is
`[λ_1, …, λ_d, λ_{d+1} + μ_1, …, λ_{d+k} + μ_k, λ_{d+k+1}, …, λ_r]`. -/
def stack (l m : List ℕ) : Option (List ℕ) :=
  if (∀ i ∈ Finset.Icc 1 m.length, part l (durfee l + i) = durfee l) ∧
      durfee l + part m 1 ≤ part l (durfee l) then
    some (l.take (durfee l) ++
      (List.range' 1 m.length).map (fun i => part l (durfee l + i) + part m i) ++
      l.drop (durfee l + m.length))
  else none

/-- The hook `Γ_{r,c} = [c, 1^{r-1}]` (`r` rows, `c` columns). -/
def hook (r c : ℕ) : List ℕ := c :: List.replicate (r - 1) 1

/-- **conj:main** of arXiv:2606.16828: every P-position has even rank. -/
def mainConjecture : Prop := ∀ l : List ℕ, IsPartition l → IsP l → Even (rank l)

/-- **conj:bloby** of arXiv:2606.16828: if `λ` and the hook `Γ_{r,c}` are losing and
`λ* = Γ_{r,c} ◁ λ` is defined, then `λ*` is losing. -/
def statement : Prop :=
  ∀ (lam : List ℕ) (r c : ℕ), IsPartition lam → 1 ≤ r → 1 ≤ c → IsP lam → IsP (hook r c) →
    ∀ s, stack (hook r c) lam = some s → IsP s

/-- `μ` padded with zeros to length `n`. -/
def pad (μ : List ℕ) (n : ℕ) : List ℕ := μ ++ List.replicate (n - μ.length) 0

/-- `[c, 1 + μ₁, …, 1 + μ_k, 1^{r-1-k}]`; `stack_hook` shows it is `Γ_{r,c} ◁ μ`. -/
def hookStack (r c : ℕ) (μ : List ℕ) : List ℕ := c :: (pad μ (r - 1)).map (· + 1)

/-! ## The moves of `hookStack r c μ` -/

theorem eraseIdx_map (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (i : ℕ), (l.map f).eraseIdx i = (l.eraseIdx i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: t, i + 1 => by simp [eraseIdx_map f t i]

theorem length_pad {μ : List ℕ} {n : ℕ} (h : μ.length ≤ n) : (pad μ n).length = n := by
  simp [pad]; omega

theorem pad_eraseIdx {μ : List ℕ} {n i : ℕ} (h : μ.length ≤ n) (hi : i < n) :
    (pad μ n).eraseIdx i = pad (μ.eraseIdx i) (n - 1) := by
  unfold pad
  rcases lt_or_ge i μ.length with hik | hik
  · rw [List.eraseIdx_append_of_lt_length hik, List.length_eraseIdx_of_lt hik]
    congr 2; omega
  · rw [List.eraseIdx_append_of_length_le hik, List.eraseIdx_of_length_le hik,
      List.eraseIdx_replicate, if_pos (by omega)]
    congr 2; omega

theorem map_pad {g : ℕ → ℕ} (hg : g 0 = 0) (μ : List ℕ) (n : ℕ) :
    (pad μ n).map g = pad (μ.map g) n := by
  simp [pad, hg]

theorem pad_filter_ne_zero : ∀ {L : List ℕ} {n : ℕ}, L.Pairwise (· ≥ ·) → L.length ≤ n →
    pad (L.filter (· ≠ 0)) n = pad L n
  | [], _, _, _ => rfl
  | x :: t, n, h, hn => by
    have ht := List.pairwise_cons.1 h
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · have hz : ∀ y ∈ t, y = 0 := fun y hy => by have := ht.1 y hy; omega
      have h2 : t = List.replicate t.length 0 := List.eq_replicate_iff.2 ⟨rfl, hz⟩
      have h1 : t.filter (· ≠ 0) = [] := List.filter_eq_nil_iff.2 fun a ha => by simp [hz a ha]
      simp only [List.length_cons] at hn
      simp only [pad, List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, h1, List.nil_append, List.length_nil, Nat.sub_zero, List.length_cons]
      rw [h2, List.length_replicate, ← List.replicate_succ, List.replicate_append_replicate]
      congr 1; omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
      have ih := pad_filter_ne_zero (n := m) ht.2 (by simp at hn; omega)
      simp only [pad] at ih ⊢
      simp only [List.filter_cons, ne_eq, hx.ne', not_false_eq_true, decide_true, if_true,
        List.cons_append, List.length_cons, Nat.add_sub_add_right, ih]

theorem pad_delCol {μ : List ℕ} (hμ : IsPartition μ) (j : ℕ) {n : ℕ} (hn : μ.length ≤ n) :
    pad (delCol μ j) n = pad (μ.map fun x => if j ≤ x then x - 1 else x) n :=
  pad_filter_ne_zero (List.Pairwise.map _ (fun a b (hab : a ≥ b) => colMap_mono j hab) hμ.1)
    (by simpa using hn)

theorem filter_pad {μ : List ℕ} (hμ : ∀ x ∈ μ, 0 < x) (n : ℕ) :
    (pad μ n).filter (· ≠ 0) = μ := by
  unfold pad
  rw [List.filter_append, List.filter_replicate_of_neg (by simp), List.append_nil,
    List.filter_eq_self.2 fun x hx => by simpa using (hμ x hx).ne']

theorem delCol_map_succ_one : ∀ L : List ℕ, delCol (L.map (· + 1)) 1 = L.filter (· ≠ 0)
  | [] => rfl
  | x :: t => by
    rw [List.map_cons, delCol_cons, delCol_map_succ_one t, List.filter_cons]
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · simp [hx.ne']

theorem delCol_map_succ_succ {j : ℕ} (hj : 1 ≤ j) : ∀ L : List ℕ,
    delCol (L.map (· + 1)) (j + 1) = (L.map fun x => if j ≤ x then x - 1 else x).map (· + 1)
  | [] => rfl
  | x :: t => by
    rw [List.map_cons, delCol_cons, delCol_map_succ_succ hj t]
    by_cases h : j ≤ x
    · rw [if_pos (show j + 1 ≤ x + 1 by omega), if_neg (show x + 1 - 1 ≠ 0 by omega)]
      simp [h]; omega
    · rw [if_neg (show ¬ j + 1 ≤ x + 1 by omega), if_neg (show x + 1 ≠ 0 by omega)]
      simp [h]

theorem delCol_eq_self {μ : List ℕ} (hμ : IsPartition μ) {j : ℕ} (hj : part μ 1 < j) :
    delCol μ j = μ := by
  unfold delCol
  rw [List.map_congr_left (g := id) fun x hx => by
      have := le_part_one hμ hx; simp; omega, List.map_id]
  exact List.filter_eq_self.2 fun x hx => by simpa using (hμ.2 x hx).ne'

theorem length_hookStack {r c : ℕ} {μ : List ℕ} (hr : 1 ≤ r) (hk : μ.length ≤ r - 1) :
    (hookStack r c μ).length = r := by
  simp [hookStack, length_pad hk]; omega

theorem part_one_hookStack (r c : ℕ) (μ : List ℕ) : part (hookStack r c μ) 1 = c := rfl

theorem hookStack_nil (r c : ℕ) : hookStack r c [] = hook r c := by
  simp [hookStack, pad, hook]

/-- Deleting the first row of `hookStack r c μ`. -/
theorem eraseIdx_hookStack_zero (r c : ℕ) (μ : List ℕ) :
    (hookStack r c μ).eraseIdx 0 = (pad μ (r - 1)).map (· + 1) := rfl

/-- Deleting row `i + 2` of `hookStack r c μ`: the row `1 + μ_{i+1}` if `i < ℓ(μ)`, and
a leg row `1` otherwise (then `μ.eraseIdx i = μ`). -/
theorem eraseIdx_hookStack_succ {r c i : ℕ} {μ : List ℕ} (hk : μ.length ≤ r - 1)
    (hi : i < r - 1) :
    (hookStack r c μ).eraseIdx (i + 1) = hookStack (r - 1) c (μ.eraseIdx i) := by
  simp only [hookStack, List.eraseIdx_cons_succ, eraseIdx_map, pad_eraseIdx hk hi]

/-- Deleting the first column of `hookStack r c μ`. -/
theorem delCol_hookStack_one {r c : ℕ} {μ : List ℕ} (hc : 2 ≤ c) (hμ : ∀ x ∈ μ, 0 < x) :
    delCol (hookStack r c μ) 1 = (c - 1) :: μ := by
  rw [hookStack, delCol_cons, if_pos (show 1 ≤ c by omega), if_neg (show c - 1 ≠ 0 by omega),
    delCol_map_succ_one, filter_pad hμ]

/-- Deleting column `j + 1` (`1 ≤ j < c`) of `hookStack r c μ`: an inner column of `μ` if
`j ≤ μ₁`, and an arm column otherwise (then `delCol μ j = μ`). -/
theorem delCol_hookStack_succ {r c j : ℕ} {μ : List ℕ} (hμ : IsPartition μ)
    (hk : μ.length ≤ r - 1) (hj : 1 ≤ j) (hjc : j + 1 ≤ c) :
    delCol (hookStack r c μ) (j + 1) = hookStack r (c - 1) (delCol μ j) := by
  rw [hookStack, delCol_cons, if_pos hjc, if_neg (by omega), delCol_map_succ_succ hj,
    map_pad (by simp), ← pad_delCol hμ j hk]
  rfl

/-! ## The general stack under a hook (the hook-stack reduction) -/

theorem part_hook_add_two (r c i : ℕ) :
    part (hook r c) (i + 2) = if i < r - 1 then 1 else 0 := by
  simp only [part, hook, show i + 2 - 1 = i + 1 by omega, List.getD_cons_succ]
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> simp

theorem durfee_hook {r c : ℕ} (hc : 1 ≤ c) : durfee (hook r c) = 1 := by
  unfold durfee
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by simp only [hook, List.length_cons, List.length_replicate]; omega, fun _ => hc,
    fun k hk hkr => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
  rw [part_hook_add_two]
  split_ifs <;> omega

theorem map_range'_part (μ : List ℕ) (f : ℕ → ℕ) :
    (List.range' 1 μ.length).map (fun i => f (part μ i)) = μ.map f := by
  apply List.ext_getElem (by simp)
  intro t h1 h2
  simp only [List.length_map] at h2
  simp [part, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **Hook-stack reduction.** For a hook `Γ_{r,c}` (`r, c ≥ 1`, rows and columns included)
the paper's general stack `Γ_{r,c} ◁ μ` is defined iff `ℓ(μ) ≤ r - 1` and `μ₁ ≤ c - 1`,
and then it is `[c, 1 + μ₁, …, 1 + μ_k, 1^{r-1-k}] = hookStack r c μ`. -/
theorem stack_hook {r c : ℕ} (μ : List ℕ) (hc : 1 ≤ c) :
    stack (hook r c) μ =
      if μ.length ≤ r - 1 ∧ part μ 1 + 1 ≤ c then some (hookStack r c μ) else none := by
  have hcond : (∀ i ∈ Finset.Icc 1 μ.length, part (hook r c) (1 + i) = 1) ↔
      μ.length ≤ r - 1 := by
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos μ.length with h0 | hpos
      · omega
      · have := h μ.length (Finset.mem_Icc.2 ⟨hpos, le_rfl⟩)
        obtain ⟨i, hi⟩ : ∃ i, μ.length = i + 1 := ⟨μ.length - 1, by omega⟩
        rw [hi, show 1 + (i + 1) = i + 2 by omega, part_hook_add_two] at this
        split_ifs at this; omega
    · intro h i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
      obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
      rw [show 1 + (t + 1) = t + 2 by omega, part_hook_add_two, if_pos (by omega)]
  have hval (h : μ.length ≤ r - 1) :
      (hook r c).take 1 ++
        (List.range' 1 μ.length).map (fun i => part (hook r c) (1 + i) + part μ i) ++
        (hook r c).drop (1 + μ.length) = hookStack r c μ := by
    have hmap : (List.range' 1 μ.length).map (fun i => part (hook r c) (1 + i) + part μ i) =
        μ.map (· + 1) := by
      rw [← map_range'_part μ (· + 1)]
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range'_1] at hi
      obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
      rw [show 1 + (t + 1) = t + 2 by omega, part_hook_add_two, if_pos (by omega)]
      ring
    rw [hmap, Nat.add_comm 1]
    simp [hook, hookStack, pad]
  unfold stack
  rw [durfee_hook hc]
  split_ifs with h1 h2 h2
  · rw [hval h2.1]
  · exact absurd ⟨hcond.1 h1.1, by have := h1.2; change 1 + part μ 1 ≤ c at this; omega⟩ h2
  · exact absurd ⟨hcond.2 h2.1, by change 1 + part μ 1 ≤ c; omega⟩ h1
  · rfl

/-! ## Moves of `hookStack`, packaged -/

theorem isPartition_pad {μ : List ℕ} (hμ : IsPartition μ) (n : ℕ) :
    (pad μ n).Pairwise (· ≥ ·) := by
  unfold pad
  rw [List.pairwise_append]
  exact ⟨hμ.1, List.pairwise_replicate.2 (Or.inr le_rfl), fun a _ b hb => by
    rw [List.eq_of_mem_replicate hb]; exact Nat.zero_le a⟩

theorem isPartition_hookStack {r c : ℕ} {μ : List ℕ} (hμ : IsPartition μ)
    (hc : part μ 1 + 1 ≤ c) : IsPartition (hookStack r c μ) := by
  have hle : ∀ x ∈ pad μ (r - 1), x ≤ part μ 1 := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · exact le_part_one hμ hx
    · rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _
  refine ⟨List.pairwise_cons.2 ⟨fun y hy => ?_, ?_⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have := hle x hx; omega
  · exact List.Pairwise.map _ (fun a b (hab : a ≥ b) => by omega) (isPartition_pad hμ _)
  · rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; omega

theorem isPartition_hook {r c : ℕ} (hc : 1 ≤ c) : IsPartition (hook r c) := by
  rw [← hookStack_nil]
  exact isPartition_hookStack ⟨List.Pairwise.nil, by simp⟩ (by simpa [part_one_nil])

theorem delCol_pad_one {μ : List ℕ} (hμ : ∀ x ∈ μ, 0 < x) (n : ℕ) :
    delCol ((pad μ n).map (· + 1)) 1 = μ := by
  rw [delCol_map_succ_one, filter_pad hμ]

theorem part_one_pad_map {μ : List ℕ} {n : ℕ} (hn : 1 ≤ n) :
    part ((pad μ n).map (· + 1)) 1 = part μ 1 + 1 := by
  cases μ with
  | nil =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pad, List.replicate_succ, part_one_cons, part_one_nil]
  | cons x t => simp [pad, part_one_cons]

theorem pad_map_mem_moves {r c : ℕ} {μ : List ℕ} :
    (pad μ (r - 1)).map (· + 1) ∈ moves (hookStack r c μ) :=
  eraseIdx_hookStack_zero r c μ ▸ eraseIdx_mem_moves (by simp [hookStack])

theorem mem_moves_pad_map {μ : List ℕ} (hμ : ∀ x ∈ μ, 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    μ ∈ moves ((pad μ n).map (· + 1)) := by
  have := delCol_mem_moves (l := (pad μ n).map (· + 1)) (j := 1) le_rfl
    (by rw [part_one_pad_map hn]; omega)
  rwa [delCol_pad_one hμ n] at this

theorem cons_mem_moves {r c : ℕ} {μ : List ℕ} (hμ : ∀ x ∈ μ, 0 < x) (hc : 2 ≤ c) :
    (c - 1) :: μ ∈ moves (hookStack r c μ) :=
  delCol_hookStack_one hc hμ ▸ delCol_mem_moves le_rfl (by rw [part_one_hookStack]; omega)

theorem mem_moves_cons (x : ℕ) (μ : List ℕ) : μ ∈ moves (x :: μ) :=
  eraseIdx_mem_moves (l := x :: μ) (i := 0) (by simp)

theorem hookStack_eraseIdx_mem_moves {r c i : ℕ} {μ : List ℕ} (hr : 1 ≤ r)
    (hk : μ.length ≤ r - 1) (hi : i < r - 1) :
    hookStack (r - 1) c (μ.eraseIdx i) ∈ moves (hookStack r c μ) :=
  eraseIdx_hookStack_succ hk hi ▸ eraseIdx_mem_moves (by rw [length_hookStack hr hk]; omega)

theorem hookStack_delCol_mem_moves {r c j : ℕ} {μ : List ℕ} (hμ : IsPartition μ)
    (hk : μ.length ≤ r - 1) (hj : 1 ≤ j) (hjc : j + 1 ≤ c) :
    hookStack r (c - 1) (delCol μ j) ∈ moves (hookStack r c μ) :=
  delCol_hookStack_succ hμ hk hj hjc ▸
    delCol_mem_moves (by omega) (by rw [part_one_hookStack]; exact hjc)

/-- Every move from `hookStack r c μ`. -/
theorem mem_moves_hookStack {r c : ℕ} {μ m : List ℕ} (hμ : IsPartition μ) (hr : 1 ≤ r)
    (hc : 2 ≤ c) (hk : μ.length ≤ r - 1) (hm : m ∈ moves (hookStack r c μ)) :
    m = (pad μ (r - 1)).map (· + 1) ∨
      (∃ i < r - 1, m = hookStack (r - 1) c (μ.eraseIdx i)) ∨
      m = (c - 1) :: μ ∨
      (∃ j, 1 ≤ j ∧ j + 1 ≤ c ∧ m = hookStack r (c - 1) (delCol μ j)) := by
  rcases mem_moves.1 hm with ⟨i, hi, rfl⟩ | ⟨j, hj1, hj2, rfl⟩
  · rw [length_hookStack hr hk] at hi
    rcases i with _ | i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨i, by omega, eraseIdx_hookStack_succ hk (by omega)⟩)
  · rw [part_one_hookStack] at hj2
    rcases j with _ | _ | j
    · omega
    · exact Or.inr (Or.inr (Or.inl (delCol_hookStack_one hc hμ.2)))
    · exact Or.inr (Or.inr (Or.inr
        ⟨j + 1, by omega, by omega, delCol_hookStack_succ hμ hk (by omega) (by omega)⟩))

theorem exists_isP_of_not_isP {l : List ℕ} (h : ¬ IsP l) : ∃ m ∈ moves l, IsP m := by
  by_contra h'
  exact h ((isP_iff l).2 fun m hm hP => h' ⟨m, hm, hP⟩)

/-! ## Hooks, two rows and two columns -/

theorem isPartition_nil : IsPartition [] := ⟨List.Pairwise.nil, by simp⟩

/-- The paper's lem:hook (its P-part): `Γ_{r,c}` is P iff `r, c ≥ 2` and `r ≡ c (mod 2)`. -/
theorem isP_hook_iff_aux (n : ℕ) : ∀ r c, r + c ≤ n → 1 ≤ r → 1 ≤ c →
    (IsP (hook r c) ↔ 2 ≤ r ∧ 2 ≤ c ∧ r % 2 = c % 2) := by
  induction n with
  | zero => intro r c h hr; omega
  | succ n ih =>
  intro r c hn hr hc
  have IH : ∀ r' c', r' + c' < r + c → 1 ≤ r' → 1 ≤ c' →
      (IsP (hook r' c') ↔ 2 ≤ r' ∧ 2 ≤ c' ∧ r' % 2 = c' % 2) :=
    fun r' c' hlt => ih r' c' (by omega)
  constructor
  · intro hP
    by_contra hcon
    rcases Nat.lt_or_ge r 2 with hr1 | hr2
    · obtain rfl : r = 1 := by omega
      exact not_isP_single c hP
    rcases Nat.lt_or_ge c 2 with hc1 | hc2
    · obtain rfl : c = 1 := by omega
      exact not_isP_of_part_one_le_one (isPartition_hook le_rfl) (by simp [hook]) le_rfl hP
    rw [← hookStack_nil] at hP
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    · obtain rfl : r = 2 := by omega
      have hm := hookStack_delCol_mem_moves (r := 2) (c := c) (j := c - 1) isPartition_nil
        (by simp) (by omega) (by omega)
      rw [delCol_nil, hookStack_nil 2 (c - 1)] at hm
      exact not_isP_of_mem hm
        ((IH 2 (c - 1) (by omega) (by omega) (by omega)).2 ⟨le_rfl, by omega, by omega⟩) hP
    · have hm := hookStack_eraseIdx_mem_moves (r := r) (c := c) (μ := []) (i := 0) (by omega)
        (by simp) (by omega)
      rw [List.eraseIdx_nil, hookStack_nil (r - 1) c] at hm
      exact not_isP_of_mem hm
        ((IH (r - 1) c (by omega) (by omega) (by omega)).2 ⟨by omega, hc2, by omega⟩) hP
  · rintro ⟨hr2, hc2, hpar⟩
    rw [← hookStack_nil]
    refine (isP_iff _).2 fun m hm => ?_
    rcases mem_moves_hookStack isPartition_nil (by omega) hc2 (by simp) hm with
      rfl | ⟨i, hi, rfl⟩ | rfl | ⟨j, hj1, hj2, rfl⟩
    · exact not_isP_of_mem (mem_moves_pad_map (by simp) (by omega)) isP_nil
    · rw [List.eraseIdx_nil, hookStack_nil, IH (r - 1) c (by omega) (by omega) (by omega)]
      omega
    · exact not_isP_single (c - 1)
    · rw [delCol_nil, hookStack_nil, IH r (c - 1) (by omega) (by omega) (by omega)]
      omega

theorem isP_hook_iff {r c : ℕ} (hr : 1 ≤ r) (hc : 1 ≤ c) :
    IsP (hook r c) ↔ 2 ≤ r ∧ 2 ≤ c ∧ r % 2 = c % 2 :=
  isP_hook_iff_aux (r + c) r c le_rfl hr hc

theorem delCol_pair {a b j : ℕ} (ha : 2 ≤ a) (hj : j ≤ a) :
    delCol [a, b] j = (a - 1) :: delCol [b] j := by
  rw [delCol_cons, if_pos hj, if_neg (show a - 1 ≠ 0 by omega)]

/-- The paper's thm:2parts: for `a ≥ b ≥ 1`, `[a, b]` is P iff `a` is even. -/
theorem isP_pair_iff_aux (n : ℕ) : ∀ a b, a + b ≤ n → 1 ≤ b → b ≤ a →
    (IsP [a, b] ↔ a % 2 = 0) := by
  induction n with
  | zero => intro a b h hb; omega
  | succ n ih =>
  intro a b hn hb hba
  have IH : ∀ a' b', a' + b' < a + b → 1 ≤ b' → b' ≤ a' → (IsP [a', b'] ↔ a' % 2 = 0) :=
    fun a' b' hlt => ih a' b' (by omega)
  constructor
  · intro hP
    by_contra hodd
    rcases Nat.lt_or_ge b a with hlt | hge
    · have hm := delCol_mem_moves (l := [a, b]) (j := a) (by omega) le_rfl
      rw [delCol_pair (by omega) le_rfl, delCol_cons, if_neg (show ¬ a ≤ b by omega),
        if_neg (show b ≠ 0 by omega), delCol_nil] at hm
      exact not_isP_of_mem hm ((IH (a - 1) b (by omega) hb (by omega)).2 (by omega)) hP
    · obtain rfl : b = a := le_antisymm hba hge
      have hm := delCol_mem_moves (l := [b, b]) (j := 1) le_rfl hb
      rcases Nat.lt_or_ge b 2 with hb2 | hb2
      · obtain rfl : b = 1 := by omega
        exact not_isP_of_mem hm isP_nil hP
      · rw [delCol_pair hb2 hb, delCol_cons, if_pos hb, if_neg (show b - 1 ≠ 0 by omega),
          delCol_nil] at hm
        exact not_isP_of_mem hm ((IH (b - 1) (b - 1) (by omega) (by omega) le_rfl).2
          (by omega)) hP
  · intro heven
    refine (isP_iff _).2 fun m hm => ?_
    rcases mem_moves.1 hm with ⟨i, hi, rfl⟩ | ⟨j, hj1, hj2, rfl⟩
    · simp only [List.length_cons, List.length_nil] at hi
      rcases i with _ | _ | i
      · exact not_isP_single b
      · exact not_isP_single a
      · omega
    · rw [part_one_cons] at hj2
      rw [delCol_pair (by omega) hj2, delCol_cons, delCol_nil]
      by_cases hjb : j ≤ b
      · rw [if_pos hjb]
        by_cases hb1 : b - 1 = 0
        · rw [if_pos hb1]; exact not_isP_single (a - 1)
        · rw [if_neg hb1, IH (a - 1) (b - 1) (by omega) (by omega) (by omega)]; omega
      · rw [if_neg hjb, if_neg (show b ≠ 0 by omega), IH (a - 1) b (by omega) hb (by omega)]
        omega

theorem isP_pair_iff {a b : ℕ} (hb : 1 ≤ b) (hba : b ≤ a) : IsP [a, b] ↔ a % 2 = 0 :=
  isP_pair_iff_aux (a + b) a b le_rfl hb hba

theorem eraseIdx_twoCol_lt {a b i : ℕ} (hi : i < a) :
    (List.replicate a 2 ++ List.replicate b 1).eraseIdx i =
      List.replicate (a - 1) 2 ++ List.replicate b 1 := by
  rw [List.eraseIdx_append_of_lt_length (by simpa using hi), List.eraseIdx_replicate, if_pos hi]

theorem eraseIdx_twoCol_ge {a b i : ℕ} (hi : a ≤ i) (hib : i < a + b) :
    (List.replicate a 2 ++ List.replicate b 1).eraseIdx i =
      List.replicate a 2 ++ List.replicate (b - 1) 1 := by
  rw [List.eraseIdx_append_of_length_le (by simpa using hi), List.length_replicate,
    List.eraseIdx_replicate, if_pos (by omega)]

theorem delCol_twoCol_one (a b : ℕ) :
    delCol (List.replicate a 2 ++ List.replicate b 1) 1 = List.replicate a 1 := by
  simp [delCol]

theorem delCol_twoCol_two (a b : ℕ) :
    delCol (List.replicate a 2 ++ List.replicate b 1) 2 = List.replicate (a + b) 1 := by
  simp [delCol]

theorem not_isP_replicate_one {r : ℕ} (hr : 1 ≤ r) : ¬ IsP (List.replicate r 1) := by
  apply not_isP_of_part_one_le_one
  · exact ⟨List.pairwise_replicate.2 (Or.inr le_rfl), fun x hx => by
      rw [List.eq_of_mem_replicate hx]; omega⟩
  · simp; omega
  · exact part_one_le fun z hz => by rw [List.eq_of_mem_replicate hz]

/-- Two columns (the conjugate of thm:2parts): for `a ≥ 1`, `[2^a, 1^b]` is P iff
`a + b` is even. -/
theorem isP_twoCol_iff_aux (n : ℕ) : ∀ a b, a + b ≤ n → 1 ≤ a →
    (IsP (List.replicate a 2 ++ List.replicate b 1) ↔ (a + b) % 2 = 0) := by
  induction n with
  | zero => intro a b h ha; omega
  | succ n ih =>
  intro a b hn ha
  have IH : ∀ a' b', a' + b' < a + b → 1 ≤ a' →
      (IsP (List.replicate a' 2 ++ List.replicate b' 1) ↔ (a' + b') % 2 = 0) :=
    fun a' b' hlt => ih a' b' (by omega)
  have hlen : (List.replicate a 2 ++ List.replicate b 1).length = a + b := by simp
  have hhead : part (List.replicate a 2 ++ List.replicate b 1) 1 = 2 := by
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rfl
  constructor
  · intro hP
    by_contra hodd
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have hm := eraseIdx_mem_moves (l := List.replicate a 2 ++ List.replicate 0 1) (i := 0)
        (by rw [hlen]; omega)
      rw [eraseIdx_twoCol_lt ha] at hm
      rcases Nat.lt_or_ge a 2 with ha2 | ha2
      · obtain rfl : a = 1 := by omega
        exact not_isP_of_mem hm isP_nil hP
      · exact not_isP_of_mem hm ((IH (a - 1) 0 (by omega) (by omega)).2 (by omega)) hP
    · have hm := eraseIdx_mem_moves (l := List.replicate a 2 ++ List.replicate b 1) (i := a)
        (by rw [hlen]; omega)
      rw [eraseIdx_twoCol_ge le_rfl (by omega)] at hm
      exact not_isP_of_mem hm ((IH a (b - 1) (by omega) ha).2 (by omega)) hP
  · intro heven
    refine (isP_iff _).2 fun m hm => ?_
    rcases mem_moves.1 hm with ⟨i, hi, rfl⟩ | ⟨j, hj1, hj2, rfl⟩
    · rw [hlen] at hi
      rcases Nat.lt_or_ge i a with hia | hia
      · rw [eraseIdx_twoCol_lt hia]
        rcases Nat.lt_or_ge a 2 with ha2 | ha2
        · obtain rfl : a = 1 := by omega
          simp only [Nat.sub_self, List.replicate_zero, List.nil_append]
          exact not_isP_replicate_one (by omega)
        · rw [IH (a - 1) b (by omega) (by omega)]; omega
      · rw [eraseIdx_twoCol_ge hia hi, IH a (b - 1) (by omega) ha]; omega
    · rw [hhead] at hj2
      rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
      · rw [delCol_twoCol_one]; exact not_isP_replicate_one ha
      · rw [delCol_twoCol_two]; exact not_isP_replicate_one (by omega)

theorem isP_twoCol_iff {a b : ℕ} (ha : 1 ≤ a) :
    IsP (List.replicate a 2 ++ List.replicate b 1) ↔ (a + b) % 2 = 0 :=
  isP_twoCol_iff_aux (a + b) a b le_rfl ha

/-! ## conj:main implies conj:bloby -/

/-- `PChain μ ω`: `ω` arises from `μ` by repeating "make a move, then a move onto a
P-position" zero or more times. -/
inductive PChain : List ℕ → List ℕ → Prop
  | refl (μ : List ℕ) : PChain μ μ
  | step {μ ν ν' ω : List ℕ} : ν ∈ moves μ → ν' ∈ moves ν → IsP ν' → PChain ν' ω →
      PChain μ ω

/-- The local hypothesis: every position that a `PChain` from `μ` reaches (`μ` itself
included) has even rank. -/
def LocalEvenRank (μ : List ℕ) : Prop := ∀ ω, PChain μ ω → Even (rank ω)

theorem LocalEvenRank.step {μ ν ν' : List ℕ} (h : LocalEvenRank μ) (hν : ν ∈ moves μ)
    (hν' : ν' ∈ moves ν) (hP : IsP ν') : LocalEvenRank ν' :=
  fun ω hω => h ω (PChain.step hν hν' hP hω)

theorem rank_even_iff {μ : List ℕ} : Even (rank μ) ↔ μ.length % 2 = part μ 1 % 2 := by
  unfold rank
  rw [Int.natAbs_even, Int.even_sub, Int.even_coe_nat, Int.even_coe_nat, Nat.even_iff,
    Nat.even_iff]
  omega

theorem part_one_delCol_eq {l : List ℕ} {j : ℕ} (hj : j ≤ part l 1) (h2 : 2 ≤ part l 1) :
    part (delCol l j) 1 = part l 1 - 1 := by
  cases l with
  | nil => simp [part_one_nil] at h2
  | cons x t =>
    rw [part_one_cons] at hj h2 ⊢
    rw [delCol_cons, if_pos hj, if_neg (show x - 1 ≠ 0 by omega), part_one_cons]

/-- **Main local theorem.** Let `μ` be a P-position such that every position reached
from `μ` by `PChain` has even rank. If `r, c ≥ 2`, `r ≡ c (mod 2)` (i.e. `Γ_{r,c}` is P),
`ℓ(μ) ≤ r - 1` and `μ₁ ≤ c - 1`, then `Γ_{r,c} ◁ μ` is P. -/
theorem isP_hookStack_aux (n : ℕ) : ∀ (r c : ℕ) (μ : List ℕ), r + c ≤ n →
    IsPartition μ → IsP μ → LocalEvenRank μ → 2 ≤ r → 2 ≤ c → r % 2 = c % 2 →
    μ.length + 1 ≤ r → part μ 1 + 1 ≤ c → IsP (hookStack r c μ) := by
  induction n with
  | zero => intro r c μ h; omega
  | succ n ih =>
  intro r c μ hn hμ hP hloc hr hc hpar hk h1
  have IH : ∀ (r' c' : ℕ) (μ' : List ℕ), r' + c' < r + c → IsPartition μ' → IsP μ' →
      LocalEvenRank μ' → 2 ≤ r' → 2 ≤ c' → r' % 2 = c' % 2 → μ'.length + 1 ≤ r' →
      part μ' 1 + 1 ≤ c' → IsP (hookStack r' c' μ') :=
    fun r' c' μ' hlt => ih r' c' μ' (by omega)
  rcases eq_or_ne μ [] with rfl | hne
  · rw [hookStack_nil]
    exact (isP_hook_iff (by omega) (by omega)).2 ⟨hr, hc, hpar⟩
  obtain ⟨hk2, hμ2⟩ := two_le_of_isP hμ hP hne
  have hrank : μ.length % 2 = part μ 1 % 2 := rank_even_iff.1 (hloc μ (PChain.refl μ))
  refine (isP_iff _).2 fun m hm => ?_
  rcases mem_moves_hookStack hμ (by omega) hc (by omega) hm with
    rfl | ⟨i, hi, rfl⟩ | rfl | ⟨j, hj1, hj2, rfl⟩
  · -- (R1) the first row: answer with the first column, back to `μ`
    exact not_isP_of_mem (mem_moves_pad_map hμ.2 (by omega)) hP
  · rcases Nat.lt_or_ge i μ.length with hik | hik
    · -- (Rin) the row `1 + μ_{i+1}`: the position is `hookStack (r - 1) c ν`
      have hνmem : μ.eraseIdx i ∈ moves μ := eraseIdx_mem_moves hik
      have hνpart : IsPartition (μ.eraseIdx i) := hμ.eraseIdx i
      have hνlen : (μ.eraseIdx i).length = μ.length - 1 := List.length_eraseIdx_of_lt hik
      have hν1 : part (μ.eraseIdx i) 1 ≤ part μ 1 := part_one_eraseIdx_le hμ i
      rcases Nat.lt_or_ge r 4 with hr4 | hr4
      · -- `r = 3`: `ν = [x]`; answer with the first column, reaching `[c - 1, x]`
        obtain ⟨x, hx⟩ : ∃ x, μ.eraseIdx i = [x] := List.length_eq_one_iff.1 (by omega)
        have hx1 : 0 < x := hνpart.2 x (by simp [hx])
        have hxc : x ≤ part μ 1 := by
          have := hν1; rw [hx, part_one_cons] at this; exact this
        refine not_isP_of_mem (cons_mem_moves hνpart.2 hc) ?_
        rw [hx]
        exact (isP_pair_iff hx1 (by omega)).2 (by omega)
      · obtain ⟨ν', hν'mem, hν'P⟩ := exists_isP_of_not_isP ((isP_iff μ).1 hP _ hνmem)
        have hloc' := hloc.step hνmem hν'mem hν'P
        rcases mem_moves.1 hν'mem with ⟨i', hi', rfl⟩ | ⟨j', hj'1, hj'2, rfl⟩
        · -- `ν' = ν` minus a row: answer with the matching row of the position
          refine not_isP_of_mem (hookStack_eraseIdx_mem_moves (c := c) (i := i') (by omega)
            (by omega) (by omega)) ?_
          have := part_one_eraseIdx_le hνpart i'
          have := List.length_eraseIdx_of_lt hi'
          exact IH _ _ _ (by omega) (hνpart.eraseIdx i') hν'P hloc' (by omega) hc
            (by omega) (by omega) (by omega)
        · -- `ν' = ν` minus a column: answer with the matching column of the position
          refine not_isP_of_mem (hookStack_delCol_mem_moves hνpart (by omega) hj'1
            (by omega)) ?_
          have := part_one_delCol_lt hνpart hj'1 hj'2
          have := length_delCol_le (μ.eraseIdx i) j'
          exact IH _ _ _ (by omega) (hνpart.delCol j') hν'P hloc' (by omega) (by omega)
            (by omega) (by omega) (by omega)
    · -- (Rleg) a leg row: the position is `hookStack (r - 1) c μ`
      rw [List.eraseIdx_of_length_le hik]
      rcases Nat.lt_or_ge r (μ.length + 3) with hr3 | hr3
      · rcases Nat.lt_or_ge c (part μ 1 + 2) with hc2 | hc2
        · -- `r = ℓ(μ) + 2` and `c = μ₁ + 1` would force odd rank
          exfalso; omega
        · -- answer with the last column: `hookStack (r - 1) (c - 1) μ`
          refine not_isP_of_mem (hookStack_delCol_mem_moves (j := c - 1) hμ (by omega)
            (by omega) (by omega)) ?_
          rw [delCol_eq_self hμ (by omega)]
          exact IH _ _ _ (by omega) hμ hP hloc (by omega) (by omega) (by omega) (by omega)
            (by omega)
      · -- answer with another leg row: `hookStack (r - 2) c μ`
        refine not_isP_of_mem (hookStack_eraseIdx_mem_moves (c := c) (i := μ.length)
          (by omega) (by omega) (by omega)) ?_
        rw [List.eraseIdx_of_length_le le_rfl]
        exact IH _ _ _ (by omega) hμ hP hloc (by omega) hc (by omega) (by omega) h1
  · -- (C1) the first column: answer with the first row, back to `μ`
    exact not_isP_of_mem (mem_moves_cons (c - 1) μ) hP
  · rcases Nat.lt_or_ge (part μ 1) j with hjμ | hjμ
    · -- (Carm) an arm column: the position is `hookStack r (c - 1) μ`
      rw [delCol_eq_self hμ hjμ]
      rcases Nat.lt_or_ge c (part μ 1 + 3) with hc3 | hc3
      · rcases Nat.lt_or_ge r (μ.length + 2) with hr2 | hr2
        · -- `c = μ₁ + 2` and `r = ℓ(μ) + 1` would force odd rank
          exfalso; omega
        · -- answer with a leg row: `hookStack (r - 1) (c - 1) μ`
          refine not_isP_of_mem (hookStack_eraseIdx_mem_moves (c := c - 1) (i := μ.length)
            (by omega) (by omega) (by omega)) ?_
          rw [List.eraseIdx_of_length_le le_rfl]
          exact IH _ _ _ (by omega) hμ hP hloc (by omega) (by omega) (by omega) (by omega)
            (by omega)
      · -- answer with another arm column: `hookStack r (c - 2) μ`
        refine not_isP_of_mem (hookStack_delCol_mem_moves (j := c - 2) hμ (by omega)
          (by omega) (by omega)) ?_
        rw [delCol_eq_self hμ (by omega)]
        exact IH _ _ _ (by omega) hμ hP hloc hr (by omega) (by omega) hk (by omega)
    · -- (Cin) the column `j + 1` through `μ`: the position is `hookStack r (c - 1) ν`
      have hνmem : delCol μ j ∈ moves μ := delCol_mem_moves hj1 hjμ
      have hνpart : IsPartition (delCol μ j) := hμ.delCol j
      have hνlen : (delCol μ j).length ≤ μ.length := length_delCol_le μ j
      have hν1 : part (delCol μ j) 1 + 1 ≤ part μ 1 := part_one_delCol_lt hμ hj1 hjμ
      rcases Nat.lt_or_ge c 4 with hc4 | hc4
      · -- `c = 3`: `μ₁ = 2` and `ν = [1^a]`; answer with the first row, `[2^a, 1^{r-1-a}]`
        have hνeq : part (delCol μ j) 1 = 1 := by
          rw [part_one_delCol_eq hjμ hμ2]; omega
        have hνrep : delCol μ j = List.replicate (delCol μ j).length 1 :=
          List.eq_replicate_iff.2 ⟨rfl, fun x hx => by
            have := le_part_one hνpart hx; have := hνpart.2 x hx; omega⟩
        have hνne : 1 ≤ (delCol μ j).length := by
          rcases Nat.eq_zero_or_pos (delCol μ j).length with h0 | h0
          · rw [List.length_eq_zero_iff.1 h0, part_one_nil] at hνeq; omega
          · exact h0
        refine not_isP_of_mem pad_map_mem_moves ?_
        generalize ha : (delCol μ j).length = a at hνrep hνne hνlen
        rw [hνrep]
        have : (pad (List.replicate a 1) (r - 1)).map (· + 1) =
            List.replicate a 2 ++ List.replicate (r - 1 - a) 1 := by
          simp [pad]
        rw [this]
        exact (isP_twoCol_iff hνne).2 (by omega)
      · obtain ⟨ν', hν'mem, hν'P⟩ := exists_isP_of_not_isP ((isP_iff μ).1 hP _ hνmem)
        have hloc' := hloc.step hνmem hν'mem hν'P
        rcases mem_moves.1 hν'mem with ⟨i', hi', rfl⟩ | ⟨j', hj'1, hj'2, rfl⟩
        · -- `ν' = ν` minus a row: answer with the matching row of the position
          refine not_isP_of_mem (hookStack_eraseIdx_mem_moves (c := c - 1) (i := i')
            (by omega) (by omega) (by omega)) ?_
          have := part_one_eraseIdx_le hνpart i'
          have := List.length_eraseIdx_of_lt hi'
          exact IH _ _ _ (by omega) (hνpart.eraseIdx i') hν'P hloc' (by omega) (by omega)
            (by omega) (by omega) (by omega)
        · -- `ν' = ν` minus a column: answer with the matching column of the position
          refine not_isP_of_mem (hookStack_delCol_mem_moves hνpart (by omega) hj'1
            (by omega)) ?_
          have := part_one_delCol_lt hνpart hj'1 hj'2
          have := length_delCol_le (delCol μ j) j'
          exact IH _ _ _ (by omega) (hνpart.delCol j') hν'P hloc' hr (by omega)
            (by omega) (by omega) (by omega)

theorem isP_hookStack {r c : ℕ} {μ : List ℕ} (hμ : IsPartition μ) (hP : IsP μ)
    (hloc : LocalEvenRank μ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hpar : r % 2 = c % 2)
    (hk : μ.length + 1 ≤ r) (h1 : part μ 1 + 1 ≤ c) : IsP (hookStack r c μ) :=
  isP_hookStack_aux (r + c) r c μ le_rfl hμ hP hloc hr hc hpar hk h1

/-- **conj:bloby for one losing `λ` under the local hypothesis** (the sharp form). -/
theorem isP_stack_of_localEvenRank {lam : List ℕ} {r c : ℕ} (hlam : IsPartition lam)
    (hr : 1 ≤ r) (hc : 1 ≤ c) (hP : IsP lam) (hloc : LocalEvenRank lam)
    (hH : IsP (hook r c)) {s : List ℕ} (hs : stack (hook r c) lam = some s) : IsP s := by
  obtain ⟨hr2, hc2, hpar⟩ := (isP_hook_iff hr hc).1 hH
  rw [stack_hook lam hc] at hs
  by_cases h : lam.length ≤ r - 1 ∧ part lam 1 + 1 ≤ c
  · rw [if_pos h, Option.some.injEq] at hs
    subst hs
    exact isP_hookStack hlam hP hloc hr2 hc2 hpar (by omega) h.2
  · rw [if_neg h] at hs
    cases hs

theorem PChain.isP {μ ω : List ℕ} (h : PChain μ ω) (hP : IsP μ) : IsP ω := by
  induction h with
  | refl => exact hP
  | step _ _ hP' _ ih => exact ih hP'

theorem PChain.isPartition {μ ω : List ℕ} (h : PChain μ ω) (hμ : IsPartition μ) :
    IsPartition ω := by
  induction h with
  | refl => exact hμ
  | step hν hν' _ _ ih => exact ih ((hμ.of_mem_moves hν).of_mem_moves hν')

/-- A `PChain` never increases a quantity that no move increases. -/
theorem PChain.le_of_moves {μ ω : List ℕ} (f : List ℕ → ℕ)
    (hf : ∀ l m, IsPartition l → m ∈ moves l → f m ≤ f l) (h : PChain μ ω)
    (hμ : IsPartition μ) : f ω ≤ f μ := by
  induction h with
  | refl => exact le_rfl
  | step hν hν' _ _ ih =>
    have h1 := hμ.of_mem_moves hν
    exact (ih (h1.of_mem_moves hν')).trans ((hf _ _ h1 hν').trans (hf _ _ hμ hν))

theorem sum_eraseIdx_le : ∀ (l : List ℕ) (i : ℕ), (l.eraseIdx i).sum ≤ l.sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: t, i + 1 => by simp [sum_eraseIdx_le t i]

theorem sum_delCol_le (j : ℕ) : ∀ l : List ℕ, (delCol l j).sum ≤ l.sum
  | [] => by simp [delCol_nil]
  | x :: t => by
    have := sum_delCol_le j t
    rw [delCol_cons]; split_ifs <;> simp <;> omega

theorem sum_le_of_mem_moves {l m : List ℕ} (hm : m ∈ moves l) : m.sum ≤ l.sum := by
  rcases mem_moves.1 hm with ⟨i, _, rfl⟩ | ⟨j, _, _, rfl⟩
  · exact sum_eraseIdx_le l i
  · exact sum_delCol_le j l

theorem localEvenRank_of_mainConjecture (h : mainConjecture) {μ : List ℕ}
    (hμ : IsPartition μ) (hP : IsP μ) : LocalEvenRank μ :=
  fun ω hω => h ω (hω.isPartition hμ) (hω.isP hP)

/-- **Headline: conj:main implies conj:bloby.** -/
theorem statement_of_mainConjecture : mainConjecture → statement :=
  fun h _ _ _ hlam hr hc hP hH _ hs =>
    isP_stack_of_localEvenRank hlam hr hc hP (localEvenRank_of_mainConjecture h hlam hP) hH hs

/-- **Size-bounded form.** conj:main for all partitions of size at most `N` implies
conj:bloby for every `λ` of size at most `N` (and every hook, of any size). -/
theorem statement_of_mainConjecture_le (N : ℕ)
    (h : ∀ ω, IsPartition ω → ω.sum ≤ N → IsP ω → Even (rank ω)) :
    ∀ (lam : List ℕ) (r c : ℕ), IsPartition lam → lam.sum ≤ N → 1 ≤ r → 1 ≤ c →
      IsP lam → IsP (hook r c) → ∀ s, stack (hook r c) lam = some s → IsP s :=
  fun _ _ _ hlam hN hr hc hP hH _ hs =>
    isP_stack_of_localEvenRank hlam hr hc hP
      (fun ω hω => h ω (hω.isPartition hlam)
        ((hω.le_of_moves List.sum (fun _ _ _ hm => sum_le_of_mem_moves hm) hlam).trans hN)
        (hω.isP hP)) hH hs

/-! ## Unconditional instances: at most two rows, or at most two columns -/

theorem length_le_of_mem_moves {l m : List ℕ} (hm : m ∈ moves l) : m.length ≤ l.length := by
  rcases mem_moves.1 hm with ⟨i, _, rfl⟩ | ⟨j, _, _, rfl⟩
  · exact List.length_eraseIdx_le l i
  · exact length_delCol_le l j

theorem part_one_le_of_mem_moves {l m : List ℕ} (hl : IsPartition l) (hm : m ∈ moves l) :
    part m 1 ≤ part l 1 := by
  rcases mem_moves.1 hm with ⟨i, _, rfl⟩ | ⟨j, _, _, rfl⟩
  · exact part_one_eraseIdx_le hl i
  · exact part_one_delCol_le hl j

/-- Every P-position with at most two rows has even rank (via thm:2parts). -/
theorem even_rank_of_length_le_two {ω : List ℕ} (hω : IsPartition ω) (hP : IsP ω)
    (h2 : ω.length ≤ 2) : Even (rank ω) := by
  rw [rank_even_iff]
  match ω, hω, hP, h2 with
  | [], _, _, _ => rfl
  | [x], _, hP, _ => exact absurd hP (not_isP_single x)
  | [a, b], hω, hP, _ =>
    have hb : 0 < b := hω.2 b (by simp)
    have hba : b ≤ a := le_part_one hω (by simp)
    have := (isP_pair_iff hb hba).1 hP
    simp [part_one_cons]; omega

theorem eq_twoCol : ∀ {ω : List ℕ}, IsPartition ω → part ω 1 ≤ 2 →
    ∃ a b, ω = List.replicate a 2 ++ List.replicate b 1
  | [], _, _ => ⟨0, 0, rfl⟩
  | x :: t, hω, h2 => by
    rw [part_one_cons] at h2
    have hx : 0 < x := hω.2 x (by simp)
    have ht : IsPartition t :=
      ⟨(List.pairwise_cons.1 hω.1).2, fun y hy => hω.2 y (by simp [hy])⟩
    have htx : part t 1 ≤ x := part_one_le fun y hy => List.rel_of_pairwise_cons hω.1 hy
    obtain ⟨a, b, rfl⟩ := eq_twoCol ht (by omega)
    rcases (show x = 1 ∨ x = 2 by omega) with rfl | rfl
    · rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact ⟨0, b + 1, by simp [List.replicate_succ]⟩
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        simp [List.replicate_succ, part_one_cons] at htx
    · exact ⟨a + 1, b, by simp [List.replicate_succ]⟩

/-- Every P-position with at most two columns has even rank. -/
theorem even_rank_of_part_one_le_two {ω : List ℕ} (hω : IsPartition ω) (hP : IsP ω)
    (h2 : part ω 1 ≤ 2) : Even (rank ω) := by
  obtain ⟨a, b, rfl⟩ := eq_twoCol hω h2
  rw [rank_even_iff]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · rfl
    · exact absurd hP (by simpa using not_isP_replicate_one hb)
  · have := (isP_twoCol_iff (b := b) ha).1 hP
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    simp [List.replicate_succ, part_one_cons]; omega

/-- conj:bloby holds unconditionally when `λ` has at most two rows. -/
theorem statement_of_length_le_two :
    ∀ (lam : List ℕ) (r c : ℕ), IsPartition lam → lam.length ≤ 2 → 1 ≤ r → 1 ≤ c →
      IsP lam → IsP (hook r c) → ∀ s, stack (hook r c) lam = some s → IsP s :=
  fun _ _ _ hlam h2 hr hc hP hH _ hs =>
    isP_stack_of_localEvenRank hlam hr hc hP
      (fun _ hω => even_rank_of_length_le_two (hω.isPartition hlam) (hω.isP hP)
        ((hω.le_of_moves List.length (fun _ _ _ hm => length_le_of_mem_moves hm) hlam).trans
          h2)) hH hs

/-- conj:bloby holds unconditionally when `λ` has at most two columns (`λ₁ ≤ 2`). -/
theorem statement_of_part_one_le_two :
    ∀ (lam : List ℕ) (r c : ℕ), IsPartition lam → part lam 1 ≤ 2 → 1 ≤ r → 1 ≤ c →
      IsP lam → IsP (hook r c) → ∀ s, stack (hook r c) lam = some s → IsP s :=
  fun _ _ _ hlam h2 hr hc hP hH _ hs =>
    isP_stack_of_localEvenRank hlam hr hc hP
      (fun _ hω => even_rank_of_part_one_le_two (hω.isPartition hlam) (hω.isP hP)
        ((hω.le_of_moves (part · 1) (fun _ _ hl hm => part_one_le_of_mem_moves hl hm)
          hlam).trans h2)) hH hs

/-! ## Boundary-word classification: definitions -/

/-- Run pairs: `(a, b)` stands for the boundary-word block `0^a 1^b`. A nonempty partition
with distinct part sizes `v₁ > ⋯ > v_k` of multiplicities `a_i` has run pairs
`[(a₁, b₁), …, (a_k, b_k)]` with `b_i = v_i - v_{i+1}` (`v_{k+1} = 0`). -/
def ValidPairs (p : List (ℕ × ℕ)) : Prop := ∀ x ∈ p, 1 ≤ x.1 ∧ 1 ≤ x.2

/-- Boundary length `∑ (a_i + b_i)`, which equals (number of rows) + (largest part). -/
def plen (p : List (ℕ × ℕ)) : ℕ := (p.map fun x => x.1 + x.2).sum

/-- One CRIM move in run-pair language: delete one letter of the boundary word
`0^{a₁}1^{b₁}⋯0^{a_k}1^{b_k}`, then strip leading `1`s and trailing `0`s. -/
inductive PMove : List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  /-- delete a `0` from a `0`-run of length `≥ 2` (a row of a repeated size) -/
  | zeroDec (A B : List (ℕ × ℕ)) (a b : ℕ) (ha : 2 ≤ a) :
      PMove (A ++ (a, b) :: B) (A ++ (a - 1, b) :: B)
  /-- delete the only `0` of the first run; the following `1`s are stripped -/
  | zeroFirst (B : List (ℕ × ℕ)) (b : ℕ) : PMove ((1, b) :: B) B
  /-- delete the only `0` of a later run; the two neighbouring `1`-runs merge -/
  | zeroMerge (A B : List (ℕ × ℕ)) (a b b' : ℕ) :
      PMove (A ++ (a, b) :: (1, b') :: B) (A ++ (a, b + b') :: B)
  /-- delete a `1` from a `1`-run of length `≥ 2` -/
  | oneDec (A B : List (ℕ × ℕ)) (a b : ℕ) (hb : 2 ≤ b) :
      PMove (A ++ (a, b) :: B) (A ++ (a, b - 1) :: B)
  /-- delete the only `1` of the last run; the preceding `0`s are stripped -/
  | oneLast (A : List (ℕ × ℕ)) (a : ℕ) : PMove (A ++ [(a, 1)]) A
  /-- delete the only `1` of an earlier run; the two neighbouring `0`-runs merge -/
  | oneMerge (A B : List (ℕ × ℕ)) (a a' b : ℕ) :
      PMove (A ++ (a, 1) :: (a', b) :: B) (A ++ (a + a', b) :: B)

/-- A run pair is A-good if `a = 1` and `b` is odd. -/
def AGood (x : ℕ × ℕ) : Bool := x.1 == 1 && x.2 % 2 == 1

/-- A run pair is B-good if `a` is odd and `b = 1`. -/
def BGood (x : ℕ × ℕ) : Bool := x.1 % 2 == 1 && x.2 == 1

/-- `L`: the number of pairs in the maximal A-good prefix. -/
def endL (p : List (ℕ × ℕ)) : ℕ := (p.takeWhile AGood).length

/-- `R`: the number of pairs in the maximal B-good suffix. -/
def endR (p : List (ℕ × ℕ)) : ℕ := (p.reverse.takeWhile BGood).length

/-- The end-peeling statistic `M = min(k, L + R)`. -/
def endM (p : List (ℕ × ℕ)) : ℕ := min p.length (endL p + endR p)

/-- The partition with run pairs `p`. -/
def ofPairs : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (a, b) :: p => List.replicate a (b + (p.map Prod.snd).sum) ++ ofPairs p

/-!
## Boundary-word classification for the run-pair game (after Zeng)

`pairs_classification`: in the game whose moves are `PMove`, a valid position `p` is a
P-position iff `plen p` and `endM p` are both even. The proof is a strong induction on `plen`
with three lemmas:

* **E** (`RunPairs.endM_eq_of_even`): a move between two even positions lowers `M` by exactly 1;
* **E2** (`RunPairs.goodMove_of_even`): an even position with odd `M` has an end-peel to an even
  position with even `M`;
* **O** (`RunPairs.goodMove_of_odd`): an odd position has a move to an even position with
  even `M`. Write it as `P ++ C ++ S` (A-good prefix, core, B-good suffix, so `M = |P| + |S|`)
  and change the core or the last prefix pair, case by case; half of the cases are the duals
  (reverse the list, swap the pairs) of the other half.

The helper lemmas live in the namespace `RunPairs` to keep their names apart from the module.
-/

namespace RunPairs

theorem aGood_iff (x : ℕ × ℕ) : AGood x = true ↔ x.1 = 1 ∧ x.2 % 2 = 1 := by
  simp [AGood]

theorem bGood_iff (x : ℕ × ℕ) : BGood x = true ↔ x.1 % 2 = 1 ∧ x.2 = 1 := by
  simp [BGood]

theorem aGood_swap (x : ℕ × ℕ) : AGood x.swap = BGood x := by
  simp [AGood, BGood, Bool.and_comm]

theorem bGood_swap (x : ℕ × ℕ) : BGood x.swap = AGood x := by
  simp [AGood, BGood, Bool.and_comm]

theorem plen_nil : plen [] = 0 := rfl

theorem plen_cons (x : ℕ × ℕ) (l : List (ℕ × ℕ)) : plen (x :: l) = x.1 + x.2 + plen l := by
  simp [plen]

theorem plen_append (l l' : List (ℕ × ℕ)) : plen (l ++ l') = plen l + plen l' := by
  simp [plen]

theorem validPairs_nil : ValidPairs [] := by simp [ValidPairs]

theorem validPairs_append {l l' : List (ℕ × ℕ)} :
    ValidPairs (l ++ l') ↔ ValidPairs l ∧ ValidPairs l' := by
  simp only [ValidPairs, List.mem_append]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · exact h2 x hx

theorem validPairs_cons {x : ℕ × ℕ} {l : List (ℕ × ℕ)} :
    ValidPairs (x :: l) ↔ (1 ≤ x.1 ∧ 1 ≤ x.2) ∧ ValidPairs l := by
  simp [ValidPairs]

theorem PMove.of_eq {p p' q q' : List (ℕ × ℕ)} (h : PMove p' q') (hp : p = p') (hq : q = q') :
    PMove p q := hp ▸ hq ▸ h

/-! ### Duality: reverse the word and swap the letters -/

/-- The dual position: reverse the boundary word and exchange `0` and `1`
(the conjugate partition). -/
def pdual (p : List (ℕ × ℕ)) : List (ℕ × ℕ) := (p.map Prod.swap).reverse

theorem pdual_nil : pdual [] = [] := rfl

theorem pdual_cons (x : ℕ × ℕ) (l : List (ℕ × ℕ)) : pdual (x :: l) = pdual l ++ [x.swap] := by
  simp [pdual]

theorem pdual_append (l l' : List (ℕ × ℕ)) : pdual (l ++ l') = pdual l' ++ pdual l := by
  simp [pdual]

theorem pdual_pdual (l : List (ℕ × ℕ)) : pdual (pdual l) = l := by
  simp [pdual, List.map_reverse]

theorem length_pdual (l : List (ℕ × ℕ)) : (pdual l).length = l.length := by
  simp [pdual]

theorem plen_pdual (l : List (ℕ × ℕ)) : plen (pdual l) = plen l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [pdual_cons, plen_append, ih, plen_cons, plen_cons, plen_nil]; simp; omega

theorem mem_pdual {x : ℕ × ℕ} {l : List (ℕ × ℕ)} : x ∈ pdual l ↔ x.swap ∈ l := by
  simp only [pdual, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨x.swap, h, by simp⟩

theorem validPairs_pdual {l : List (ℕ × ℕ)} (h : ValidPairs l) : ValidPairs (pdual l) := by
  intro x hx
  have := h _ (mem_pdual.1 hx)
  simp at this
  exact ⟨this.2, this.1⟩

theorem endL_pdual (l : List (ℕ × ℕ)) : endL (pdual l) = endR l := by
  have h : (AGood ∘ Prod.swap) = BGood := by
    funext x
    simp [aGood_swap]
  simp only [endL, endR, pdual, ← List.map_reverse, List.takeWhile_map, h, List.length_map]

theorem endR_pdual (l : List (ℕ × ℕ)) : endR (pdual l) = endL l := by
  have h : (BGood ∘ Prod.swap) = AGood := by
    funext x
    simp [bGood_swap]
  simp only [endL, endR, pdual, List.reverse_reverse, List.takeWhile_map, h, List.length_map]

theorem endM_pdual (l : List (ℕ × ℕ)) : endM (pdual l) = endM l := by
  simp only [endM, endL_pdual, endR_pdual, length_pdual]
  omega

theorem PMove.pdual {p q : List (ℕ × ℕ)} (h : PMove p q) :
    PMove (RunPairs.pdual p) (RunPairs.pdual q) := by
  cases h with
  | zeroDec A B a b ha =>
    exact PMove.of_eq (PMove.oneDec (RunPairs.pdual B) (RunPairs.pdual A) b a ha)
      (by simp [RunPairs.pdual]) (by simp [RunPairs.pdual])
  | zeroFirst _ b =>
    exact PMove.of_eq (PMove.oneLast (RunPairs.pdual q) b)
      (by simp [RunPairs.pdual]) rfl
  | zeroMerge A B a b b' =>
    exact PMove.of_eq (PMove.oneMerge (RunPairs.pdual B) (RunPairs.pdual A) b' b a)
      (by simp [RunPairs.pdual]) (by simp [RunPairs.pdual, Nat.add_comm])
  | oneDec A B a b hb =>
    exact PMove.of_eq (PMove.zeroDec (RunPairs.pdual B) (RunPairs.pdual A) b a hb)
      (by simp [RunPairs.pdual]) (by simp [RunPairs.pdual])
  | oneLast _ a =>
    exact PMove.of_eq (PMove.zeroFirst (RunPairs.pdual q) a)
      (by simp [RunPairs.pdual]) rfl
  | oneMerge A B a a' b =>
    exact PMove.of_eq (PMove.zeroMerge (RunPairs.pdual B) (RunPairs.pdual A) b a' a)
      (by simp [RunPairs.pdual]) (by simp [RunPairs.pdual, Nat.add_comm])

/-! ### The end statistics -/

theorem endL_nil : endL [] = 0 := rfl

theorem endR_nil : endR [] = 0 := rfl

theorem endL_cons (x : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    endL (x :: l) = if AGood x = true then endL l + 1 else 0 := by
  unfold endL
  rw [List.takeWhile_cons]
  split_ifs <;> simp

theorem endR_append_single (l : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    endR (l ++ [x]) = if BGood x = true then endR l + 1 else 0 := by
  unfold endR
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.takeWhile_cons]
  split_ifs <;> simp

theorem endL_le_length (l : List (ℕ × ℕ)) : endL l ≤ l.length :=
  (List.takeWhile_prefix _).length_le

theorem endR_le_length (l : List (ℕ × ℕ)) : endR l ≤ l.length := by
  have := (List.takeWhile_prefix BGood (l := l.reverse)).length_le
  simpa [endR] using this

theorem endL_append_of_forall {P : List (ℕ × ℕ)} (hP : ∀ x ∈ P, AGood x = true)
    (l : List (ℕ × ℕ)) : endL (P ++ l) = P.length + endL l := by
  unfold endL
  rw [List.takeWhile_append_of_pos hP]
  simp

theorem endR_append_of_forall {S : List (ℕ × ℕ)} (hS : ∀ x ∈ S, BGood x = true)
    (l : List (ℕ × ℕ)) : endR (l ++ S) = endR l + S.length := by
  unfold endR
  rw [List.reverse_append, List.takeWhile_append_of_pos (by simpa using hS)]
  simp
  omega

theorem endR_append_of_lt {l : List (ℕ × ℕ)} (h : endR l < l.length) (l0 : List (ℕ × ℕ)) :
    endR (l0 ++ l) = endR l := by
  unfold endR at *
  rw [List.reverse_append, List.takeWhile_append, if_neg (by simpa using h.ne)]

theorem le_endR_append (l0 l : List (ℕ × ℕ)) : endR l ≤ endR (l0 ++ l) := by
  unfold endR
  rw [List.reverse_append, List.takeWhile_append]
  split_ifs with h
  · rw [h]
    simp
  · exact le_rfl

theorem endR_of_forall {S : List (ℕ × ℕ)} (hS : ∀ x ∈ S, BGood x = true) :
    endR S = S.length := by
  simpa [endR_nil] using endR_append_of_forall hS []

/-- A list made of an A-good part followed by a B-good part has `M = k`. -/
theorem endM_of_good {P S : List (ℕ × ℕ)} (hP : ∀ x ∈ P, AGood x = true)
    (hS : ∀ x ∈ S, BGood x = true) : endM (P ++ S) = P.length + S.length := by
  unfold endM
  rw [endL_append_of_forall hP]
  have h1 := le_endR_append P S
  have h2 := endR_of_forall hS
  have h3 := endR_le_length (P ++ S)
  simp only [List.length_append] at h3 ⊢
  omega

theorem even_plen_of_forall {l : List (ℕ × ℕ)}
    (h : ∀ x ∈ l, AGood x = true ∨ BGood x = true) : Even (plen l) := by
  induction l with
  | nil => exact ⟨0, rfl⟩
  | cons x l ih =>
    have hx := h x (by simp)
    have ih := ih (fun y hy => h y (by simp [hy]))
    rw [aGood_iff, bGood_iff] at hx
    rw [plen_cons, Nat.even_iff]
    rw [Nat.even_iff] at ih
    omega

/-! ### Splitting an odd position into prefix, core and suffix -/

/-- `P ++ C ++ S` with `P` A-good, `S` B-good, and a core `C` that starts with a pair that is
not A-good and ends with a pair that is not B-good. -/
structure Split (P C S : List (ℕ × ℕ)) : Prop where
  prefix_good : ∀ x ∈ P, AGood x = true
  suffix_good : ∀ x ∈ S, BGood x = true
  core_head : ∃ c C', C = c :: C' ∧ AGood c = false
  core_last : ∃ C' c, C = C' ++ [c] ∧ BGood c = false

theorem Split.endL_eq {P C S : List (ℕ × ℕ)} (h : Split P C S) :
    endL (P ++ C ++ S) = P.length := by
  obtain ⟨c, C', rfl, hc⟩ := h.core_head
  rw [List.append_assoc, endL_append_of_forall h.prefix_good, List.cons_append, endL_cons,
    if_neg (by simp [hc])]
  simp

theorem Split.endR_eq {P C S : List (ℕ × ℕ)} (h : Split P C S) :
    endR (P ++ C ++ S) = S.length := by
  obtain ⟨C', c, rfl, hc⟩ := h.core_last
  rw [endR_append_of_forall h.suffix_good, ← List.append_assoc, endR_append_single,
    if_neg (by simp [hc])]
  simp

theorem Split.endM_eq {P C S : List (ℕ × ℕ)} (h : Split P C S) :
    endM (P ++ C ++ S) = P.length + S.length := by
  have hC : 1 ≤ C.length := by
    obtain ⟨c, C', rfl, _⟩ := h.core_head
    simp
  unfold endM
  rw [h.endL_eq, h.endR_eq]
  simp only [List.length_append]
  omega

theorem endM_eq_of_split {q P C S : List (ℕ × ℕ)} (hq : q = P ++ C ++ S) (h : Split P C S) :
    endM q = P.length + S.length := hq ▸ h.endM_eq

theorem Split.pdual {P C S : List (ℕ × ℕ)} (h : Split P C S) :
    Split (RunPairs.pdual S) (RunPairs.pdual C) (RunPairs.pdual P) where
  prefix_good x hx := by
    rw [mem_pdual] at hx
    rw [← bGood_swap]
    exact h.suffix_good _ hx
  suffix_good x hx := by
    rw [mem_pdual] at hx
    rw [← aGood_swap]
    exact h.prefix_good _ hx
  core_head := by
    obtain ⟨C', c, rfl, hc⟩ := h.core_last
    exact ⟨c.swap, RunPairs.pdual C', by simp [pdual_append, pdual_cons, pdual_nil],
      by rw [aGood_swap, hc]⟩
  core_last := by
    obtain ⟨c, C', rfl, hc⟩ := h.core_head
    exact ⟨RunPairs.pdual C', c.swap, pdual_cons c C', by rw [bGood_swap, hc]⟩

theorem dropWhile_eq_cons_imp {α : Type*} {f : α → Bool} :
    ∀ {l : List α} {c : α} {rest : List α}, l.dropWhile f = c :: rest → f c = false
  | [], _, _, h => by simp at h
  | x :: l, c, rest, h => by
    rw [List.dropWhile_cons] at h
    split_ifs at h with hx
    · exact dropWhile_eq_cons_imp h
    · simp only [List.cons.injEq] at h
      rw [← h.1]
      simpa using hx

theorem exists_split {p : List (ℕ × ℕ)} (hodd : ¬ Even (plen p)) :
    ∃ P C S, p = P ++ C ++ S ∧ Split P C S := by
  obtain ⟨D, hD⟩ : ∃ D, D = p.dropWhile AGood := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = D.reverse.dropWhile BGood := ⟨_, rfl⟩
  have hPD : p = p.takeWhile AGood ++ D := by rw [hD, List.takeWhile_append_dropWhile]
  have hDE : D = E.reverse ++ (D.reverse.takeWhile BGood).reverse := by
    rw [hE, ← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]
  have hPg : ∀ x ∈ p.takeWhile AGood, AGood x = true := fun x hx => List.mem_takeWhile_imp hx
  have hSg : ∀ x ∈ (D.reverse.takeWhile BGood).reverse, BGood x = true :=
    fun x hx => List.mem_takeWhile_imp (List.mem_reverse.1 hx)
  have hE0 : E ≠ [] := by
    rintro rfl
    apply hodd
    rw [hPD, hDE]
    apply even_plen_of_forall
    intro x hx
    simp only [List.reverse_nil, List.nil_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl (hPg x hx)
    · exact Or.inr (hSg x hx)
  refine ⟨p.takeWhile AGood, E.reverse, (D.reverse.takeWhile BGood).reverse,
    by rw [List.append_assoc, ← hDE, ← hPD], hPg, hSg, ?_, ?_⟩
  · -- the first element of the core is the first element of `D`
    obtain ⟨c, C', hc⟩ : ∃ c C', E.reverse = c :: C' := by
      refine List.exists_cons_of_ne_nil ?_
      simpa using hE0
    refine ⟨c, C', hc, ?_⟩
    have : D = c :: (C' ++ (D.reverse.takeWhile BGood).reverse) :=
      hDE.trans (by rw [hc, List.cons_append])
    rw [hD] at this
    exact dropWhile_eq_cons_imp this
  · obtain ⟨e, E', hE'⟩ := List.exists_cons_of_ne_nil hE0
    refine ⟨E'.reverse, e, by rw [hE']; simp, ?_⟩
    rw [hE] at hE'
    exact dropWhile_eq_cons_imp hE'

/-! ### Even positions: only the two end-peels keep the parity -/

theorem endM_cons_aGood {x : ℕ × ℕ} (hx : AGood x = true) (B : List (ℕ × ℕ)) :
    endM (x :: B) = endM B + 1 := by
  unfold endM
  rw [endL_cons, if_pos hx]
  have h1 := le_endR_append [x] B
  have h2 := endR_le_length (x :: B)
  have h3 := endR_le_length B
  simp only [List.singleton_append] at h1
  by_cases hR : endR B < B.length
  · have h4 := endR_append_of_lt hR [x]
    simp only [List.singleton_append] at h4
    rw [h4]
    simp only [List.length_cons]
    omega
  · simp only [List.length_cons] at h2 ⊢
    omega

theorem endM_append_bGood {x : ℕ × ℕ} (hx : BGood x = true) (A : List (ℕ × ℕ)) :
    endM (A ++ [x]) = endM A + 1 := by
  rw [← endM_pdual, ← endM_pdual A, pdual_append, pdual_cons, pdual_nil, List.nil_append,
    List.singleton_append]
  exact endM_cons_aGood (by rw [aGood_swap]; exact hx) _

/-- Lemma E: from an even position, a move to an even position lowers `M` by exactly one. -/
theorem endM_eq_of_even {p q : List (ℕ × ℕ)} (h : PMove p q) (hp : Even (plen p))
    (hq : Even (plen q)) : endM p = endM q + 1 := by
  rw [Nat.even_iff] at hp hq
  cases h with
  | zeroDec A B a b ha =>
    simp only [plen_append, plen_cons] at hp hq
    omega
  | zeroFirst _ b =>
    rw [plen_cons] at hp
    dsimp only at hp
    exact endM_cons_aGood (by rw [aGood_iff]; exact ⟨rfl, by dsimp only; omega⟩) _
  | zeroMerge A B a b b' =>
    simp only [plen_append, plen_cons] at hp hq
    omega
  | oneDec A B a b hb =>
    simp only [plen_append, plen_cons] at hp hq
    omega
  | oneLast _ a =>
    rw [plen_append, plen_cons, plen_nil] at hp
    dsimp only at hp
    exact endM_append_bGood (by rw [bGood_iff]; exact ⟨by dsimp only; omega, rfl⟩) _
  | oneMerge A B a a' b =>
    simp only [plen_append, plen_cons] at hp hq
    omega

/-- A move to a position with even length and even `M` (a P-position, a posteriori). -/
def GoodMove (p : List (ℕ × ℕ)) : Prop := ∃ q, PMove p q ∧ Even (plen q) ∧ Even (endM q)

theorem GoodMove.of_pdual {p : List (ℕ × ℕ)} (h : GoodMove (pdual p)) : GoodMove p := by
  obtain ⟨q, hq, h1, h2⟩ := h
  refine ⟨pdual q, ?_, by rwa [plen_pdual], by rwa [endM_pdual]⟩
  simpa [pdual_pdual] using PMove.pdual hq

theorem goodMove_of_endL {p : List (ℕ × ℕ)} (hp : Even (plen p)) (hM : ¬ Even (endM p))
    (hL : 1 ≤ endL p) : GoodMove p := by
  obtain _ | ⟨x, B⟩ := p
  · simp [endL_nil] at hL
  rw [endL_cons] at hL
  have hx : AGood x = true := by
    by_contra hx
    rw [if_neg hx] at hL
    omega
  obtain ⟨a, b⟩ := x
  obtain ⟨rfl, hb⟩ := (aGood_iff _).1 hx
  have hM' := endM_cons_aGood hx B
  refine ⟨B, PMove.zeroFirst B b, ?_, ?_⟩
  · rw [Nat.even_iff] at hp ⊢
    rw [plen_cons] at hp
    simp only at hp hb
    omega
  · rw [hM'] at hM
    rw [Nat.even_iff] at hM ⊢
    omega

/-- Lemma E2: an even position with odd `M` has an end-peel to an even position with even `M`. -/
theorem goodMove_of_even {p : List (ℕ × ℕ)} (hp : Even (plen p)) (hM : ¬ Even (endM p)) :
    GoodMove p := by
  have h0 : 1 ≤ endM p := by
    rcases Nat.eq_zero_or_pos (endM p) with h | h
    · exact absurd (h ▸ ⟨0, rfl⟩) hM
    · exact h
  have h1 : 1 ≤ endL p ∨ 1 ≤ endR p := by
    unfold endM at h0
    omega
  rcases h1 with h1 | h1
  · exact goodMove_of_endL hp hM h1
  · apply GoodMove.of_pdual
    refine goodMove_of_endL (by rwa [plen_pdual]) (by rwa [endM_pdual]) ?_
    rwa [endL_pdual]

/-! ### Odd positions: a move to an even position with even `M` -/

theorem exists_last_aGood {P : List (ℕ × ℕ)} (hP : ∀ x ∈ P, AGood x = true) (h : P ≠ []) :
    ∃ P₀ b', P = P₀ ++ [(1, b')] ∧ b' % 2 = 1 ∧ ∀ x ∈ P₀, AGood x = true := by
  rcases List.eq_nil_or_concat P with rfl | ⟨P₀, ⟨a, b⟩, rfl⟩
  · exact absurd rfl h
  · have hx := (aGood_iff _).1 (hP (a, b) (by simp))
    simp only at hx
    obtain ⟨rfl, hb⟩ := hx
    exact ⟨P₀, b, by simp, hb, fun x hx => hP x (by simp [hx])⟩

theorem exists_eq_append_single {α : Type*} {x y : α} {l l₁ : List α} (h : x :: l = l₁ ++ [y])
    (hl : l ≠ []) : ∃ l₂, l = l₂ ++ [y] := by
  rcases l₁ with _ | ⟨z, l₁⟩
  · simp only [List.nil_append, List.cons.injEq] at h
    exact absurd h.2 hl
  · simp only [List.cons_append, List.cons.injEq] at h
    exact ⟨l₁, h.2⟩

/-- Replacing the first pair of a core of length `≥ 2` keeps its last pair. -/
theorem core_last_cons {c c' : ℕ × ℕ} {C' : List (ℕ × ℕ)} (hC' : C' ≠ [])
    (h : ∃ C'' d, c :: C' = C'' ++ [d] ∧ BGood d = false) :
    ∃ C'' d, c' :: C' = C'' ++ [d] ∧ BGood d = false := by
  obtain ⟨C'', d, hC'', hd⟩ := h
  obtain ⟨l₂, hl₂⟩ := exists_eq_append_single hC'' hC'
  exact ⟨c' :: l₂, d, by rw [hl₂]; rfl, hd⟩

theorem not_aGood_of {x : ℕ × ℕ} (h : x.1 ≠ 1 ∨ x.2 % 2 = 0) : AGood x = false := by
  rw [Bool.eq_false_iff, ne_eq, aGood_iff]
  omega

theorem not_bGood_of {x : ℕ × ℕ} (h : x.1 % 2 = 0 ∨ x.2 ≠ 1) : BGood x = false := by
  rw [Bool.eq_false_iff, ne_eq, bGood_iff]
  omega

theorem plen_even_of_split {P C S : List (ℕ × ℕ)} (h : Split P C S) :
    plen P % 2 = 0 ∧ plen S % 2 = 0 := by
  have h1 := even_plen_of_forall (fun x hx => Or.inl (h.prefix_good x hx))
  have h2 := even_plen_of_forall (fun x hx => Or.inr (h.suffix_good x hx))
  rw [Nat.even_iff] at h1 h2
  exact ⟨h1, h2⟩

/-- "Reduce A": delete a `1` from the last pair of the A-good prefix. -/
theorem goodMove_reduceA {P C S : List (ℕ × ℕ)} (h : Split P C S)
    (hv : ValidPairs (P ++ C ++ S)) (hodd : plen (P ++ C ++ S) % 2 = 1)
    (hLR : (P.length + S.length) % 2 = 1) (hP : P ≠ [])
    (hC : ∀ a, C = [(a, 1)] → a % 2 = 1) : GoodMove (P ++ C ++ S) := by
  obtain ⟨P₀, b', rfl, hb', hP₀⟩ := exists_last_aGood h.prefix_good hP
  obtain ⟨⟨a, b⟩, C', rfl, hc⟩ := h.core_head
  have hab := hv (a, b) (by simp)
  simp only at hab
  simp only [List.length_append, List.length_singleton] at hLR
  rcases Nat.lt_or_ge b' 2 with hb1 | hb2
  · -- `b' = 1`: the pair `(1, 1)` merges into the first core pair
    obtain rfl : b' = 1 := by omega
    refine ⟨P₀ ++ (1 + a, b) :: (C' ++ S),
      PMove.of_eq (PMove.oneMerge P₀ (C' ++ S) 1 a b) (by simp) rfl, ?_, ?_⟩
    · rw [Nat.even_iff]
      simp only [plen_append, plen_cons, plen_nil] at hodd ⊢
      omega
    · have hs : Split P₀ ((1 + a, b) :: C') S := by
        refine ⟨hP₀, h.suffix_good, ⟨_, _, rfl, not_aGood_of (by simp only; omega)⟩, ?_⟩
        rcases eq_or_ne C' [] with rfl | hC'
        · refine ⟨[], (1 + a, b), rfl, not_bGood_of ?_⟩
          simp only
          rcases eq_or_ne b 1 with rfl | hb
          · have := hC a rfl
            omega
          · exact Or.inr hb
        · exact core_last_cons hC' h.core_last
      rw [endM_eq_of_split (by simp) hs, Nat.even_iff]
      omega
  · -- `b' ≥ 3`: the pair `(1, b')` becomes `(1, b' - 1)`, which is neither A- nor B-good
    refine ⟨P₀ ++ (1, b' - 1) :: ((a, b) :: C' ++ S),
      PMove.of_eq (PMove.oneDec P₀ ((a, b) :: C' ++ S) 1 b' hb2) (by simp) rfl, ?_, ?_⟩
    · rw [Nat.even_iff]
      simp only [plen_append, plen_cons, plen_nil] at hodd ⊢
      omega
    · have hs : Split P₀ ((1, b' - 1) :: (a, b) :: C') S := by
        refine ⟨hP₀, h.suffix_good, ⟨_, _, rfl, not_aGood_of (by simp only; omega)⟩, ?_⟩
        obtain ⟨C'', d, hC'', hd⟩ := h.core_last
        exact ⟨(1, b' - 1) :: C'', d, by rw [hC'']; rfl, hd⟩
      rw [endM_eq_of_split (by simp) hs, Nat.even_iff]
      omega

/-- Core `(1, b)` with `b` even and `L + R` odd: turn it into the A-good pair `(1, b - 1)`. -/
theorem goodMove_core_one_odd {P S : List (ℕ × ℕ)} {b : ℕ} (h : Split P [(1, b)] S)
    (hv : ValidPairs (P ++ [(1, b)] ++ S)) (hodd : plen (P ++ [(1, b)] ++ S) % 2 = 1)
    (hLR : (P.length + S.length) % 2 = 1) (hb : b % 2 = 0) :
    GoodMove (P ++ [(1, b)] ++ S) := by
  have hb1 := (hv (1, b) (by simp)).2
  simp only at hb1
  refine ⟨P ++ (1, b - 1) :: S,
    PMove.of_eq (PMove.oneDec P S 1 b (by omega)) (by simp) rfl, ?_, ?_⟩
  · rw [Nat.even_iff]
    simp only [plen_append, plen_cons, plen_nil] at hodd ⊢
    omega
  · have hg : ∀ x ∈ P ++ [(1, b - 1)], AGood x = true := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h.prefix_good x hx
      · rw [List.mem_singleton.1 hx, aGood_iff]
        exact ⟨rfl, by simp only; omega⟩
    rw [show P ++ (1, b - 1) :: S = P ++ [(1, b - 1)] ++ S by simp,
      endM_of_good hg h.suffix_good, Nat.even_iff]
    simp only [List.length_append, List.length_singleton]
    omega

/-- Core `(1, b)` with `b` even and `L + R` even: delete its `0`. -/
theorem goodMove_core_one_even {P S : List (ℕ × ℕ)} {b : ℕ} (h : Split P [(1, b)] S)
    (hodd : plen (P ++ [(1, b)] ++ S) % 2 = 1)
    (hLR : (P.length + S.length) % 2 = 0) (hb : b % 2 = 0) :
    GoodMove (P ++ [(1, b)] ++ S) := by
  rcases eq_or_ne P [] with rfl | hP
  · refine ⟨S, PMove.of_eq (PMove.zeroFirst S b) (by simp) rfl, ?_, ?_⟩
    · rw [Nat.even_iff]
      simp only [plen_append, plen_cons, plen_nil] at hodd
      omega
    · have := endM_of_good (P := []) (fun x hx => by simp at hx) h.suffix_good
      rw [List.nil_append] at this
      rw [this, Nat.even_iff]
      simpa using hLR
  · obtain ⟨P₀, b', rfl, hb', hP₀⟩ := exists_last_aGood h.prefix_good hP
    refine ⟨P₀ ++ (1, b' + b) :: S,
      PMove.of_eq (PMove.zeroMerge P₀ S 1 b' b) (by simp) rfl, ?_, ?_⟩
    · rw [Nat.even_iff]
      simp only [plen_append, plen_cons, plen_nil] at hodd ⊢
      omega
    · have hg : ∀ x ∈ P₀ ++ [(1, b' + b)], AGood x = true := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hP₀ x hx
        · rw [List.mem_singleton.1 hx, aGood_iff]
          exact ⟨rfl, by simp only; omega⟩
      rw [show P₀ ++ (1, b' + b) :: S = P₀ ++ [(1, b' + b)] ++ S by simp,
        endM_of_good hg h.suffix_good, Nat.even_iff]
      simp only [List.length_append, List.length_singleton] at hLR ⊢
      omega

/-- Core `(a, b)` with `a ≥ 3` odd and `b` even (`L + R` even): delete a `0`. -/
theorem goodMove_core_odd_even {P S : List (ℕ × ℕ)} {a b : ℕ} (h : Split P [(a, b)] S)
    (hodd : plen (P ++ [(a, b)] ++ S) % 2 = 1)
    (hLR : (P.length + S.length) % 2 = 0) (ha : 3 ≤ a) (ha2 : a % 2 = 1) :
    GoodMove (P ++ [(a, b)] ++ S) := by
  refine ⟨P ++ (a - 1, b) :: S,
    PMove.of_eq (PMove.zeroDec P S a b (by omega)) (by simp) rfl, ?_, ?_⟩
  · rw [Nat.even_iff]
    simp only [plen_append, plen_cons, plen_nil] at hodd ⊢
    omega
  · have hs : Split P [(a - 1, b)] S :=
      ⟨h.prefix_good, h.suffix_good, ⟨_, _, rfl, not_aGood_of (by simp only; omega)⟩,
        ⟨[], _, rfl, not_bGood_of (by simp only; omega)⟩⟩
    rw [endM_eq_of_split (by simp) hs, Nat.even_iff]
    exact hLR

theorem endR_barrier {X S : List (ℕ × ℕ)} {d : ℕ × ℕ} (hS : ∀ x ∈ S, BGood x = true)
    (hd : BGood d = false) : endR (X ++ [d] ++ S) = S.length := by
  rw [endR_append_of_forall hS, endR_append_single, if_neg (by simp [hd])]
  simp

theorem endM_prefix_barrier {X Y S : List (ℕ × ℕ)} {d : ℕ × ℕ}
    (hX : ∀ x ∈ X, AGood x = true) (hS : ∀ x ∈ S, BGood x = true) (hd : BGood d = false) :
    endM (X ++ (Y ++ [d] ++ S)) = min (X.length + (Y.length + 1 + S.length))
      (X.length + endL (Y ++ [d] ++ S) + S.length) := by
  unfold endM
  rw [endL_append_of_forall hX]
  have : endR (X ++ (Y ++ [d] ++ S)) = S.length := by
    rw [show X ++ (Y ++ [d] ++ S) = X ++ Y ++ [d] ++ S by simp]
    exact endR_barrier hS hd
  rw [this]
  simp only [List.length_append, List.length_singleton]

/-- A core of length `≥ 2` with `L + R` even: change its first pair. -/
theorem goodMove_core_long {P C₁ S : List (ℕ × ℕ)} {a b : ℕ}
    (h : Split P ((a, b) :: C₁) S) (hv : ValidPairs (P ++ (a, b) :: C₁ ++ S))
    (hodd : plen (P ++ (a, b) :: C₁ ++ S) % 2 = 1)
    (hLR : (P.length + S.length) % 2 = 0) (hC₁ : C₁ ≠ []) :
    GoodMove (P ++ (a, b) :: C₁ ++ S) := by
  have hab := hv (a, b) (by simp)
  simp only at hab
  have hcA : AGood (a, b) = false := by
    obtain ⟨c, C', hc, hcA⟩ := h.core_head
    simp only [List.cons.injEq] at hc
    rw [hc.1]
    exact hcA
  rw [Bool.eq_false_iff, ne_eq, aGood_iff] at hcA
  simp only at hcA
  obtain ⟨C₁', d, hC₁e, hd⟩ : ∃ C₁' d, C₁ = C₁' ++ [d] ∧ BGood d = false := by
    obtain ⟨C'', d, hC'', hd⟩ := h.core_last
    obtain ⟨l₂, hl₂⟩ := exists_eq_append_single hC'' hC₁
    exact ⟨l₂, d, hl₂, hd⟩
  have keep : ∀ c' : ℕ × ℕ, AGood c' = false →
      endM (P ++ c' :: (C₁ ++ S)) = P.length + S.length := fun c' hc' =>
    endM_eq_of_split (by simp)
      ⟨h.prefix_good, h.suffix_good, ⟨c', C₁, rfl, hc'⟩, core_last_cons hC₁ h.core_last⟩
  have hplen : ∀ q, plen q + 1 = plen (P ++ (a, b) :: C₁ ++ S) → Even (plen q) := by
    intro q hq
    rw [Nat.even_iff]
    omega
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · -- `a = 1` and `b` even: deleting the `0` or a `1` gives consecutive values of `M`
    obtain rfl : a = 1 := by omega
    have hb : b % 2 = 0 := by omega
    obtain ⟨q0, hq0, hq0e, hq0M⟩ : ∃ q0, PMove (P ++ (1, b) :: C₁ ++ S) q0 ∧
        plen q0 % 2 = 0 ∧ endM q0 = min (P.length + (C₁'.length + 1 + S.length))
          (P.length + endL (C₁' ++ [d] ++ S) + S.length) := by
      rcases eq_or_ne P [] with rfl | hP
      · refine ⟨C₁ ++ S, PMove.of_eq (PMove.zeroFirst (C₁ ++ S) b) (by simp) rfl, ?_, ?_⟩
        · simp only [plen_append, plen_cons, List.nil_append] at hodd ⊢
          omega
        · have := endM_prefix_barrier (X := []) (Y := C₁') (fun x hx => by simp at hx)
            h.suffix_good hd
          rw [hC₁e]
          simpa using this
      · obtain ⟨P₀, b', rfl, hb', hP₀⟩ := exists_last_aGood h.prefix_good hP
        refine ⟨P₀ ++ (1, b' + b) :: (C₁ ++ S),
          PMove.of_eq (PMove.zeroMerge P₀ (C₁ ++ S) 1 b' b) (by simp) rfl, ?_, ?_⟩
        · simp only [plen_append, plen_cons, plen_nil] at hodd ⊢
          omega
        · have hg : ∀ x ∈ P₀ ++ [(1, b' + b)], AGood x = true := by
            intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact hP₀ x hx
            · rw [List.mem_singleton.1 hx, aGood_iff]
              exact ⟨rfl, by simp only; omega⟩
          have := endM_prefix_barrier (Y := C₁') hg h.suffix_good hd
          rw [show P₀ ++ (1, b' + b) :: (C₁ ++ S) = P₀ ++ [(1, b' + b)] ++ (C₁' ++ [d] ++ S) by
            rw [hC₁e]; simp, this]
          simp only [List.length_append, List.length_singleton]
    by_cases he : endM q0 % 2 = 0
    · exact ⟨q0, hq0, Nat.even_iff.2 hq0e, Nat.even_iff.2 he⟩
    · have hg : ∀ x ∈ P ++ [(1, b - 1)], AGood x = true := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h.prefix_good x hx
        · rw [List.mem_singleton.1 hx, aGood_iff]
          exact ⟨rfl, by simp only; omega⟩
      have hq1M := endM_prefix_barrier (Y := C₁') hg h.suffix_good hd
      refine ⟨P ++ (1, b - 1) :: (C₁ ++ S),
        PMove.of_eq (PMove.oneDec P (C₁ ++ S) 1 b (by omega)) (by simp) rfl,
        hplen _ (by simp only [plen_append, plen_cons]; omega), ?_⟩
      rw [show P ++ (1, b - 1) :: (C₁ ++ S) = P ++ [(1, b - 1)] ++ (C₁' ++ [d] ++ S) by
        rw [hC₁e]; simp, hq1M, Nat.even_iff]
      simp only [List.length_append, List.length_singleton]
      rw [hq0M] at he
      omega
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · obtain rfl : a = 2 := by omega
    rcases Nat.lt_or_ge b 2 with hb1 | hb2
    · -- the pair `(2, 1)`: delete its `1`, merging it into the next core pair
      obtain rfl : b = 1 := by omega
      obtain ⟨⟨a', b'⟩, C₂, rfl⟩ := List.exists_cons_of_ne_nil hC₁
      refine ⟨P ++ (2 + a', b') :: (C₂ ++ S),
        PMove.of_eq (PMove.oneMerge P (C₂ ++ S) 2 a' b') (by simp) rfl,
        hplen _ (by simp only [plen_append, plen_cons]; omega), ?_⟩
      have hs : Split P ((2 + a', b') :: C₂) S := by
        refine ⟨h.prefix_good, h.suffix_good, ⟨_, _, rfl, not_aGood_of (by simp only; omega)⟩, ?_⟩
        rcases eq_or_ne C₂ [] with rfl | hC₂
        · have : d = (a', b') := by
            have := congrArg List.getLast? hC₁e
            simpa using this.symm
          subst this
          refine ⟨[], _, rfl, not_bGood_of ?_⟩
          rw [Bool.eq_false_iff, ne_eq, bGood_iff] at hd
          simp only at hd ⊢
          omega
        · obtain ⟨C'', e, hC'', he⟩ := h.core_last
          obtain ⟨l₂, hl₂⟩ := exists_eq_append_single hC'' hC₁
          exact core_last_cons hC₂ ⟨l₂, e, hl₂, he⟩
      rw [endM_eq_of_split (by simp) hs, Nat.even_iff]
      exact hLR
    · rcases Nat.even_or_odd b with hb | hb
      · -- `(2, b)` with `b` even: delete a `0`
        rw [Nat.even_iff] at hb
        refine ⟨P ++ (2 - 1, b) :: (C₁ ++ S),
          PMove.of_eq (PMove.zeroDec P (C₁ ++ S) 2 b le_rfl) (by simp) rfl,
          hplen _ (by simp only [plen_append, plen_cons]; omega), ?_⟩
        rw [keep _ (not_aGood_of (by simp only; omega)), Nat.even_iff]
        exact hLR
      · -- `(2, b)` with `b ≥ 3` odd: delete a `1`
        refine ⟨P ++ (2, b - 1) :: (C₁ ++ S),
          PMove.of_eq (PMove.oneDec P (C₁ ++ S) 2 b hb2) (by simp) rfl,
          hplen _ (by simp only [plen_append, plen_cons]; omega), ?_⟩
        rw [keep _ (not_aGood_of (by simp only; omega)), Nat.even_iff]
        exact hLR
  · -- `a ≥ 3`: delete a `0`
    refine ⟨P ++ (a - 1, b) :: (C₁ ++ S),
      PMove.of_eq (PMove.zeroDec P (C₁ ++ S) a b (by omega)) (by simp) rfl,
      hplen _ (by simp only [plen_append, plen_cons]; omega), ?_⟩
    rw [keep _ (not_aGood_of (by simp only; omega)), Nat.even_iff]
    exact hLR

theorem pdual_single (a b : ℕ) : pdual [(a, b)] = [(b, a)] := by
  simp [pdual]

theorem pdual_cons_eq_single {a b a' b' : ℕ} {C₁ : List (ℕ × ℕ)}
    (h : pdual ((a, b) :: C₁) = [(a', b')]) : C₁ = [] ∧ b = a' ∧ a = b' := by
  have hl := congrArg List.length h
  rw [length_pdual] at hl
  simp only [List.length_cons, List.length_nil] at hl
  obtain rfl : C₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [pdual_single] at h
  simp only [List.cons.injEq, Prod.mk.injEq] at h
  exact ⟨rfl, h.1.1, h.1.2⟩

/-- Lemma O: every odd position has a move to an even position with even `M`. -/
theorem goodMove_of_odd {p : List (ℕ × ℕ)} (hv : ValidPairs p) (hodd : ¬ Even (plen p)) :
    GoodMove p := by
  obtain ⟨P, C, S, rfl, h⟩ := exists_split hodd
  rw [Nat.not_even_iff] at hodd
  have hd : pdual (P ++ C ++ S) = pdual S ++ pdual C ++ pdual P := by
    simp only [pdual_append, List.append_assoc]
  have hvd : ValidPairs (pdual S ++ pdual C ++ pdual P) := hd ▸ validPairs_pdual hv
  have hoddd : plen (pdual S ++ pdual C ++ pdual P) % 2 = 1 := by
    rw [← hd, plen_pdual]
    exact hodd
  have hsd := h.pdual
  have dual : GoodMove (pdual S ++ pdual C ++ pdual P) → GoodMove (P ++ C ++ S) :=
    fun g => GoodMove.of_pdual (hd ▸ g)
  have hlen : (pdual S).length + (pdual P).length = P.length + S.length := by
    rw [length_pdual, length_pdual]
    omega
  obtain ⟨hPe, hSe⟩ := plen_even_of_split h
  have hCo : plen C % 2 = 1 := by
    rw [plen_append, plen_append] at hodd
    omega
  obtain ⟨⟨a, b⟩, C₁, rfl, hcA⟩ := h.core_head
  have hab := hv (a, b) (by simp)
  simp only at hab
  rcases Nat.mod_two_eq_zero_or_one (P.length + S.length) with hLR | hLR
  · -- `L + R` even
    rcases eq_or_ne C₁ [] with rfl | hC₁
    · have hcB : BGood (a, b) = false := by
        obtain ⟨C', c, hc, hcB⟩ := h.core_last
        have : c = (a, b) := by
          have := congrArg List.getLast? hc
          simpa using this.symm
        rwa [this] at hcB
      rw [Bool.eq_false_iff, ne_eq, aGood_iff] at hcA
      rw [Bool.eq_false_iff, ne_eq, bGood_iff] at hcB
      simp only [plen_cons, plen_nil] at hCo hcA hcB
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · -- `a` even and `b` odd: the dual of the two cases below
        apply dual
        rw [pdual_single] at hsd hvd hoddd ⊢
        rcases Nat.lt_or_ge b 2 with hb1 | hb3
        · obtain rfl : b = 1 := by omega
          exact goodMove_core_one_even hsd hoddd (by omega) ha
        · exact goodMove_core_odd_even hsd hoddd (by omega) (by omega) (by omega)
      · rcases Nat.lt_or_ge a 2 with ha1 | ha3
        · obtain rfl : a = 1 := by omega
          exact goodMove_core_one_even h hodd hLR (by omega)
        · exact goodMove_core_odd_even h hodd hLR (by omega) ha
    · exact goodMove_core_long h hv hodd hLR hC₁
  · -- `L + R` odd
    by_cases hA : P ≠ [] ∧ ∀ a', (a, b) :: C₁ = [(a', 1)] → a' % 2 = 1
    · exact goodMove_reduceA h hv hodd hLR hA.1 hA.2
    by_cases hB : S ≠ [] ∧ ∀ a', pdual ((a, b) :: C₁) = [(a', 1)] → a' % 2 = 1
    · apply dual
      refine goodMove_reduceA hsd hvd hoddd (by omega) ?_ hB.2
      intro hS
      apply hB.1
      simpa [pdual] using hS
    -- the remaining cases: a single core pair `(1, even)` or `(even, 1)`
    rcases eq_or_ne P [] with rfl | hP
    · have hS : S ≠ [] := by
        rintro rfl
        simp at hLR
      push Not at hB
      obtain ⟨a', ha'1, ha'2⟩ := hB hS
      obtain ⟨rfl, rfl, rfl⟩ := pdual_cons_eq_single ha'1
      exact goodMove_core_one_odd h hv hodd hLR (by omega)
    · push Not at hA
      obtain ⟨a', ha'1, ha'2⟩ := hA hP
      simp only [List.cons.injEq, Prod.mk.injEq] at ha'1
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ha'1
      apply dual
      rw [pdual_single] at hsd hvd hoddd ⊢
      exact goodMove_core_one_odd hsd hvd hoddd (by omega) (by omega)

end RunPairs

/-! ## The classification -/

/-- Every move shortens the boundary word. -/
theorem PMove.plen_lt {p q : List (ℕ × ℕ)} (h : PMove p q) : plen q < plen p := by
  cases h <;> simp [RunPairs.plen_append, RunPairs.plen_cons, RunPairs.plen_nil] <;> omega

/-- Moves keep positions valid. -/
theorem PMove.validPairs {p q : List (ℕ × ℕ)} (h : PMove p q) (hp : ValidPairs p) :
    ValidPairs q := by
  cases h with
  | zeroDec A B a b ha =>
    simp only [RunPairs.validPairs_append, RunPairs.validPairs_cons] at hp ⊢
    exact ⟨hp.1, ⟨⟨by omega, hp.2.1.2⟩, hp.2.2⟩⟩
  | zeroFirst B b =>
    exact (RunPairs.validPairs_cons.1 hp).2
  | zeroMerge A B a b b' =>
    simp only [RunPairs.validPairs_append, RunPairs.validPairs_cons] at hp ⊢
    exact ⟨hp.1, ⟨⟨hp.2.1.1, by omega⟩, hp.2.2.2⟩⟩
  | oneDec A B a b hb =>
    simp only [RunPairs.validPairs_append, RunPairs.validPairs_cons] at hp ⊢
    exact ⟨hp.1, ⟨⟨hp.2.1.1, by omega⟩, hp.2.2⟩⟩
  | oneLast A a =>
    exact (RunPairs.validPairs_append.1 hp).1
  | oneMerge A B a a' b =>
    simp only [RunPairs.validPairs_append, RunPairs.validPairs_cons] at hp ⊢
    exact ⟨hp.1, ⟨⟨by omega, hp.2.2.1.2⟩, hp.2.2.2⟩⟩

/-- **Boundary-word classification** (Zeng), for the run-pair game: in any game whose moves are
`PMove`, the P-positions are exactly those with even boundary length and even `M`. -/
theorem pairs_classification (G : List (ℕ × ℕ) → Prop)
    (hG : ∀ p, ValidPairs p → (G p ↔ ∀ q, PMove p q → ¬ G q)) :
    ∀ p, ValidPairs p → (G p ↔ Even (plen p) ∧ Even (endM p)) := by
  suffices H : ∀ n, ∀ p, plen p = n → ValidPairs p →
      (G p ↔ Even (plen p) ∧ Even (endM p)) from fun p hp => H _ p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn hp
    have ih' : ∀ q, PMove p q → (G q ↔ Even (plen q) ∧ Even (endM q)) := fun q hq =>
      ih (plen q) (hn ▸ hq.plen_lt) q rfl (hq.validPairs hp)
    rw [hG p hp]
    constructor
    · intro hall
      by_contra hcon
      by_cases he : Even (plen p)
      · obtain ⟨q, hq, hq1, hq2⟩ := RunPairs.goodMove_of_even he (fun hm => hcon ⟨he, hm⟩)
        exact hall q hq ((ih' q hq).2 ⟨hq1, hq2⟩)
      · obtain ⟨q, hq, hq1, hq2⟩ := RunPairs.goodMove_of_odd hp he
        exact hall q hq ((ih' q hq).2 ⟨hq1, hq2⟩)
    · rintro ⟨he, hm⟩ q hq hGq
      obtain ⟨hq1, hq2⟩ := (ih' q hq).1 hGq
      have := RunPairs.endM_eq_of_even hq he hq1
      rw [Nat.even_iff] at hm hq2
      omega

/-! ## CRIM is the run-pair game (Zeng's move correspondence) -/

/-- Sum of the `b`-components: the largest part of `ofPairs p`. -/
def pairsBSum (p : List (ℕ × ℕ)) : ℕ := (p.map Prod.snd).sum

/-- Sum of the `a`-components: the number of rows of `ofPairs p`. -/
def pairsASum (p : List (ℕ × ℕ)) : ℕ := (p.map Prod.fst).sum

@[simp] theorem pairsBSum_nil : pairsBSum [] = 0 := rfl

@[simp] theorem pairsBSum_cons (a b : ℕ) (p : List (ℕ × ℕ)) :
    pairsBSum ((a, b) :: p) = b + pairsBSum p := by simp [pairsBSum]

@[simp] theorem pairsBSum_append (A B : List (ℕ × ℕ)) :
    pairsBSum (A ++ B) = pairsBSum A + pairsBSum B := by simp [pairsBSum]

@[simp] theorem pairsASum_nil : pairsASum [] = 0 := rfl

@[simp] theorem pairsASum_cons (a b : ℕ) (p : List (ℕ × ℕ)) :
    pairsASum ((a, b) :: p) = a + pairsASum p := by simp [pairsASum]

@[simp] theorem pairsASum_append (A B : List (ℕ × ℕ)) :
    pairsASum (A ++ B) = pairsASum A + pairsASum B := by simp [pairsASum]

theorem ofPairs_nil : ofPairs [] = [] := rfl

theorem ofPairs_cons (a b : ℕ) (p : List (ℕ × ℕ)) :
    ofPairs ((a, b) :: p) = List.replicate a (b + pairsBSum p) ++ ofPairs p := rfl

theorem ofPairs_append : ∀ (A B : List (ℕ × ℕ)),
    ofPairs (A ++ B) = (ofPairs A).map (· + pairsBSum B) ++ ofPairs B
  | [], B => by simp [ofPairs_nil]
  | (a, b) :: A, B => by
    rw [List.cons_append, ofPairs_cons, ofPairs_append A B, ofPairs_cons, List.map_append,
      List.map_replicate, pairsBSum_append, List.append_assoc, Nat.add_assoc]

theorem length_ofPairs : ∀ p : List (ℕ × ℕ), (ofPairs p).length = pairsASum p
  | [] => rfl
  | (a, b) :: p => by simp [ofPairs_cons, length_ofPairs p]

theorem le_of_mem_ofPairs : ∀ {p : List (ℕ × ℕ)} {x : ℕ}, x ∈ ofPairs p → x ≤ pairsBSum p
  | [], _, h => by simp [ofPairs_nil] at h
  | (a, b) :: p, x, h => by
    rw [ofPairs_cons, List.mem_append] at h
    rcases h with h | h
    · rw [List.eq_of_mem_replicate h, pairsBSum_cons]
    · have := le_of_mem_ofPairs h
      rw [pairsBSum_cons]; omega

theorem validPairs_cons {a b : ℕ} {p : List (ℕ × ℕ)} :
    ValidPairs ((a, b) :: p) ↔ (1 ≤ a ∧ 1 ≤ b) ∧ ValidPairs p := by
  simp [ValidPairs]

theorem validPairs_append {A B : List (ℕ × ℕ)} :
    ValidPairs (A ++ B) ↔ ValidPairs A ∧ ValidPairs B := by
  simp only [ValidPairs, List.mem_append]
  constructor
  · intro h; exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · exact h2 x hx

theorem pos_of_mem_ofPairs : ∀ {p : List (ℕ × ℕ)}, ValidPairs p → ∀ x ∈ ofPairs p, 0 < x
  | [], _, _, h => by simp [ofPairs_nil] at h
  | (a, b) :: p, hp, x, h => by
    rw [validPairs_cons] at hp
    rw [ofPairs_cons, List.mem_append] at h
    rcases h with h | h
    · rw [List.eq_of_mem_replicate h]; omega
    · exact pos_of_mem_ofPairs hp.2 x h

theorem isPartition_ofPairs {p : List (ℕ × ℕ)} (hp : ValidPairs p) : IsPartition (ofPairs p) := by
  refine ⟨?_, pos_of_mem_ofPairs hp⟩
  induction p with
  | nil => exact List.Pairwise.nil
  | cons x p ih =>
    obtain ⟨a, b⟩ := x
    have hp' := validPairs_cons.1 hp
    rw [ofPairs_cons, List.pairwise_append]
    refine ⟨List.pairwise_replicate.2 (Or.inr le_rfl), ih hp'.2, ?_⟩
    intro u hu v hv
    rw [List.eq_of_mem_replicate hu]
    have := le_of_mem_ofPairs hv
    show v ≤ b + pairsBSum p
    omega

theorem part_one_ofPairs : ∀ {p : List (ℕ × ℕ)}, ValidPairs p → part (ofPairs p) 1 = pairsBSum p
  | [], _ => rfl
  | (a, b) :: p, hp => by
    have hp' := validPairs_cons.1 hp
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [ofPairs_cons, List.replicate_succ, List.cons_append, part_one_cons, pairsBSum_cons]

theorem plen_eq : ∀ p : List (ℕ × ℕ), plen p = pairsASum p + pairsBSum p
  | [] => rfl
  | (a, b) :: p => by
    have := plen_eq p
    simp only [plen, List.map_cons, List.sum_cons] at this ⊢
    rw [this, pairsASum_cons, pairsBSum_cons]; omega

theorem length_add_part_one_ofPairs {p : List (ℕ × ℕ)} (hp : ValidPairs p) :
    (ofPairs p).length + part (ofPairs p) 1 = plen p := by
  rw [length_ofPairs, part_one_ofPairs hp, plen_eq]

theorem exists_ofPairs : ∀ {l : List ℕ}, IsPartition l → ∃ p, ValidPairs p ∧ ofPairs p = l
  | [], _ => ⟨[], by simp [ValidPairs], rfl⟩
  | x :: rest, hl => by
    have hrest : IsPartition rest :=
      ⟨(List.pairwise_cons.1 hl.1).2, fun y hy => hl.2 y (List.mem_cons_of_mem _ hy)⟩
    obtain ⟨p', hp', hrest'⟩ := exists_ofPairs hrest
    have hx : 0 < x := hl.2 x (by simp)
    have hge : ∀ y ∈ rest, x ≥ y := fun y hy => (List.pairwise_cons.1 hl.1).1 y hy
    cases p' with
    | nil =>
      rw [ofPairs_nil] at hrest'
      subst hrest'
      exact ⟨[(1, x)], by simp [ValidPairs]; omega, by simp [ofPairs_cons, ofPairs_nil]⟩
    | cons y p'' =>
      obtain ⟨a', b'⟩ := y
      have hv := validPairs_cons.1 hp'
      obtain ⟨a'', rfl⟩ : ∃ a'', a' = a'' + 1 := ⟨a' - 1, by omega⟩
      have hhead : b' + pairsBSum p'' ≤ x := by
        apply hge
        rw [← hrest', ofPairs_cons]
        simp [List.replicate_succ]
      rcases Nat.eq_or_lt_of_le hhead with h | h
      · refine ⟨(a'' + 2, b') :: p'', validPairs_cons.2 ⟨⟨by omega, hv.1.2⟩, hv.2⟩, ?_⟩
        rw [← hrest', ofPairs_cons, ofPairs_cons, h, List.replicate_succ, List.cons_append]
      · refine ⟨(1, x - (b' + pairsBSum p'')) :: (a'' + 1, b') :: p'',
          validPairs_cons.2 ⟨⟨le_rfl, by omega⟩, hp'⟩, ?_⟩
        rw [ofPairs_cons, hrest', pairsBSum_cons]
        simp only [List.replicate_one, List.singleton_append, List.cons.injEq, and_true]
        omega

/-! ### Rows: deleting a `0` -/

theorem ofPairs_block (A B : List (ℕ × ℕ)) (a b : ℕ) :
    ofPairs (A ++ (a, b) :: B) =
      (ofPairs A).map (· + (b + pairsBSum B)) ++
        (List.replicate a (b + pairsBSum B) ++ ofPairs B) := by
  rw [ofPairs_append, ofPairs_cons, pairsBSum_cons]

theorem ofPairs_concat_map (A : List (ℕ × ℕ)) (a b c : ℕ) :
    (ofPairs (A ++ [(a, b)])).map (· + c) =
      (ofPairs A).map (· + (b + c)) ++ List.replicate a (b + c) := by
  rw [ofPairs_append, ofPairs_cons, ofPairs_nil]
  simp [List.map_map, Function.comp_def, Nat.add_assoc]

theorem length_ofPairs_block (A B : List (ℕ × ℕ)) (a b : ℕ) :
    (ofPairs (A ++ (a, b) :: B)).length = (ofPairs A).length + a + (ofPairs B).length := by
  rw [ofPairs_block]; simp; omega

theorem eraseIdx_ofPairs_block {A B : List (ℕ × ℕ)} {a b k : ℕ} (hk : k < a) :
    (ofPairs (A ++ (a, b) :: B)).eraseIdx ((ofPairs A).length + k) =
      (ofPairs A).map (· + (b + pairsBSum B)) ++
        (List.replicate (a - 1) (b + pairsBSum B) ++ ofPairs B) := by
  rw [ofPairs_block, List.eraseIdx_append_of_length_le (by simp), List.length_map,
    Nat.add_sub_cancel_left, List.eraseIdx_append_of_lt_length (by simpa using hk),
    List.eraseIdx_replicate, if_pos hk]

/-- Deleting the only `0` of a later run merges two `1`-runs. -/
theorem eraseIdx_ofPairs_merge (A B : List (ℕ × ℕ)) (a b b' : ℕ) :
    (ofPairs (A ++ (a, b) :: (1, b') :: B)).eraseIdx ((ofPairs A).length + a) =
      ofPairs (A ++ (a, b + b') :: B) := by
  have h1 : A ++ (a, b) :: (1, b') :: B = (A ++ [(a, b)]) ++ (1, b') :: B := by simp
  have h2 : (ofPairs A).length + a = (ofPairs (A ++ [(a, b)])).length + 0 := by
    rw [length_ofPairs, length_ofPairs, pairsASum_append]; simp
  rw [h1, h2, eraseIdx_ofPairs_block (Nat.zero_lt_one), ofPairs_concat_map, ofPairs_block]
  simp [Nat.add_assoc]

/-! ### Columns: deleting a `1` -/

theorem delCol_append_eq (L1 L2 : List ℕ) (j : ℕ) :
    delCol (L1 ++ L2) j = delCol L1 j ++ delCol L2 j := by
  simp [delCol, List.map_append, List.filter_append]

theorem delCol_eq_self_of_lt {L : List ℕ} {j : ℕ} (h : ∀ y ∈ L, y < j ∧ 0 < y) :
    delCol L j = L := by
  unfold delCol
  rw [List.map_congr_left (g := id) fun y hy => by have := h y hy; simp; omega, List.map_id]
  exact List.filter_eq_self.2 fun y hy => by simpa using (h y hy).2.ne'

theorem delCol_map_add_eq {L : List ℕ} {j c : ℕ} (hL : ∀ y ∈ L, 0 < y) (hj1 : 1 ≤ j)
    (hj : j ≤ c) : delCol (L.map (· + c)) j = L.map (· + (c - 1)) := by
  unfold delCol
  rw [List.map_map, List.map_congr_left (g := (· + (c - 1))) fun y hy => by
    have := hL y hy
    simp only [Function.comp_apply]
    rw [if_pos (by omega)]; omega]
  exact List.filter_eq_self.2 fun y hy => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    have := hL z hz
    simp; omega

theorem delCol_replicate_eq {a v j : ℕ} (hj : j ≤ v) (hv : 2 ≤ v) :
    delCol (List.replicate a v) j = List.replicate a (v - 1) := by
  unfold delCol
  rw [List.map_replicate, if_pos hj]
  exact List.filter_eq_self.2 fun y hy => by rw [List.eq_of_mem_replicate hy]; simp; omega

theorem delCol_ofPairs_block {A B : List (ℕ × ℕ)} {a b j : ℕ} (hA : ValidPairs A)
    (hB : ValidPairs B) (hj1 : pairsBSum B < j) (hj2 : j ≤ pairsBSum B + b) :
    delCol (ofPairs (A ++ (a, b) :: B)) j =
      (ofPairs A).map (· + (b + pairsBSum B - 1)) ++
        (delCol (List.replicate a (b + pairsBSum B)) j ++ ofPairs B) := by
  rw [ofPairs_block, delCol_append_eq, delCol_append_eq,
    delCol_map_add_eq (pos_of_mem_ofPairs hA) (by omega) (by omega),
    delCol_eq_self_of_lt (L := ofPairs B) fun y hy =>
      ⟨by have := le_of_mem_ofPairs hy; omega, pos_of_mem_ofPairs hB y hy⟩]

/-! ### Decomposition at a row index or a column index -/

theorem exists_block_of_lt_length : ∀ {p : List (ℕ × ℕ)} {i : ℕ}, i < (ofPairs p).length →
    ∃ A a b B k, p = A ++ (a, b) :: B ∧ k < a ∧ i = (ofPairs A).length + k
  | [], i, h => by simp [ofPairs_nil] at h
  | (a, b) :: p, i, h => by
    rw [ofPairs_cons, List.length_append, List.length_replicate] at h
    by_cases hi : i < a
    · exact ⟨[], a, b, p, i, rfl, hi, by simp [ofPairs_nil]⟩
    · obtain ⟨A, a', b', B, k, rfl, hk, hik⟩ :=
        exists_block_of_lt_length (p := p) (i := i - a) (by omega)
      refine ⟨(a, b) :: A, a', b', B, k, rfl, hk, ?_⟩
      rw [ofPairs_cons, List.length_append, List.length_replicate]; omega

theorem exists_block_of_le_bsum : ∀ {p : List (ℕ × ℕ)} {j : ℕ}, 1 ≤ j → j ≤ pairsBSum p →
    ∃ A a b B, p = A ++ (a, b) :: B ∧ pairsBSum B < j ∧ j ≤ pairsBSum B + b
  | [], j, h1, h2 => by simp at h2; omega
  | (a, b) :: p, j, h1, h2 => by
    rw [pairsBSum_cons] at h2
    by_cases hj : pairsBSum p < j
    · exact ⟨[], a, b, p, rfl, hj, by omega⟩
    · obtain ⟨A, a', b', B, rfl, hj1, hj2⟩ := exists_block_of_le_bsum (p := p) h1 (by omega)
      exact ⟨(a, b) :: A, a', b', B, rfl, hj1, hj2⟩

/-! ### The correspondence -/

theorem mem_moves_ofPairs {p : List (ℕ × ℕ)} (hp : ValidPairs p) {m : List ℕ} :
    m ∈ moves (ofPairs p) ↔ ∃ q, PMove p q ∧ ofPairs q = m := by
  constructor
  · intro hm
    rcases mem_moves.1 hm with ⟨i, hi, rfl⟩ | ⟨j, hj1, hj2, rfl⟩
    · obtain ⟨A, a, b, B, k, rfl, hk, rfl⟩ := exists_block_of_lt_length hi
      rw [eraseIdx_ofPairs_block hk]
      have hv := (validPairs_cons.1 (validPairs_append.1 hp).2).1
      by_cases ha : 2 ≤ a
      · exact ⟨_, PMove.zeroDec A B a b ha, ofPairs_block A B (a - 1) b⟩
      · obtain rfl : a = 1 := by omega
        rcases List.eq_nil_or_concat A with rfl | ⟨A', y, rfl⟩
        · exact ⟨B, by simpa using PMove.zeroFirst B b, by simp [ofPairs_nil]⟩
        · obtain ⟨a0, b0⟩ := y
          refine ⟨A' ++ (a0, b0 + b) :: B, ?_, ?_⟩
          · simpa using PMove.zeroMerge A' B a0 b0 b
          · rw [List.concat_eq_append, ofPairs_concat_map, ofPairs_block]
            simp [Nat.add_assoc]
    · rw [part_one_ofPairs hp] at hj2
      obtain ⟨A, a, b, B, rfl, hjB, hjb⟩ := exists_block_of_le_bsum hj1 hj2
      have hA := (validPairs_append.1 hp).1
      have hB := (validPairs_cons.1 (validPairs_append.1 hp).2).2
      have hv := (validPairs_cons.1 (validPairs_append.1 hp).2).1
      rw [delCol_ofPairs_block hA hB hjB hjb]
      by_cases hb : 2 ≤ b
      · refine ⟨_, PMove.oneDec A B a b hb, ?_⟩
        rw [delCol_replicate_eq (by omega) (by omega), ofPairs_block]
        have : b + pairsBSum B - 1 = b - 1 + pairsBSum B := by omega
        rw [this]
      · obtain rfl : b = 1 := by omega
        cases B with
        | nil =>
          obtain rfl : j = 1 := by simp at hjB hjb; omega
          refine ⟨A, PMove.oneLast A a, ?_⟩
          rw [pairsBSum_nil, delCol_one_eq_nil (by simp), ofPairs_nil]
          simp
        | cons z B' =>
          obtain ⟨a', b'⟩ := z
          have hz := (validPairs_cons.1 hB).1
          refine ⟨_, PMove.oneMerge A B' a a' b', ?_⟩
          rw [pairsBSum_cons] at hjB hjb ⊢
          rw [delCol_replicate_eq (by omega) (by omega), ofPairs_cons, ofPairs_block,
            show 1 + (b' + pairsBSum B') - 1 = b' + pairsBSum B' by omega,
            ← List.append_assoc (List.replicate a _), List.replicate_append_replicate]
  · rintro ⟨q, hq, rfl⟩
    cases hq with
    | zeroDec A B a b ha =>
      have hlt : (ofPairs A).length + 0 < (ofPairs (A ++ (a, b) :: B)).length := by
        rw [length_ofPairs_block]; omega
      have := eraseIdx_mem_moves hlt
      rwa [eraseIdx_ofPairs_block (by omega), ← ofPairs_block] at this
    | zeroFirst B b =>
      have hlt : 0 < (ofPairs ((1, b) :: q)).length := by rw [ofPairs_cons]; simp
      have := eraseIdx_mem_moves hlt
      rwa [ofPairs_cons, List.replicate_one, List.singleton_append,
        List.eraseIdx_cons_zero] at this
    | zeroMerge A B a b b' =>
      have hlt : (ofPairs A).length + a < (ofPairs (A ++ (a, b) :: (1, b') :: B)).length := by
        rw [length_ofPairs_block, ofPairs_cons]; simp
      have := eraseIdx_mem_moves hlt
      rwa [eraseIdx_ofPairs_merge] at this
    | oneDec A B a b hb =>
      have hA := (validPairs_append.1 hp).1
      have hB := (validPairs_cons.1 (validPairs_append.1 hp).2).2
      have hj2 : pairsBSum B + 1 ≤ part (ofPairs (A ++ (a, b) :: B)) 1 := by
        rw [part_one_ofPairs hp, pairsBSum_append, pairsBSum_cons]; omega
      have := delCol_mem_moves (by omega) hj2
      rwa [delCol_ofPairs_block hA hB (by omega) (by omega),
        delCol_replicate_eq (by omega) (by omega),
        show b + pairsBSum B - 1 = b - 1 + pairsBSum B by omega, ← ofPairs_block] at this
    | oneLast A a =>
      have hA := (validPairs_append.1 hp).1
      have hv := (validPairs_cons.1 (validPairs_append.1 hp).2).1
      have hj2 : 1 ≤ part (ofPairs (q ++ (a, 1) :: [])) 1 := by
        rw [part_one_ofPairs hp, pairsBSum_append, pairsBSum_cons]; omega
      have := delCol_mem_moves le_rfl hj2
      rw [delCol_ofPairs_block hA (by simp [ValidPairs]) (by simp) (by simp),
        pairsBSum_nil, delCol_one_eq_nil (by simp), ofPairs_nil] at this
      simpa using this
    | oneMerge A B a a' b =>
      have hA := (validPairs_append.1 hp).1
      have hB := (validPairs_cons.1 (validPairs_append.1 hp).2).2
      have hz := (validPairs_cons.1 hB).1
      have hj2 : b + pairsBSum B + 1 ≤ part (ofPairs (A ++ (a, 1) :: (a', b) :: B)) 1 := by
        rw [part_one_ofPairs hp, pairsBSum_append, pairsBSum_cons, pairsBSum_cons]; omega
      have := delCol_mem_moves (by omega) hj2
      have e := pairsBSum_cons a' b B
      rw [delCol_ofPairs_block hA hB (by omega) (by omega), pairsBSum_cons,
        delCol_replicate_eq (by omega) (by omega), ofPairs_cons,
        show 1 + (b + pairsBSum B) - 1 = b + pairsBSum B by omega,
        ← List.append_assoc (List.replicate a _), List.replicate_append_replicate] at this
      rwa [ofPairs_block A B (a + a') b]

/-- CRIM P-positions, read through `ofPairs`, satisfy the run-pair game recursion. -/
theorem isP_ofPairs_iff_forall {p : List (ℕ × ℕ)} (hp : ValidPairs p) :
    IsP (ofPairs p) ↔ ∀ q, PMove p q → ¬ IsP (ofPairs q) := by
  rw [isP_iff]
  constructor
  · intro h q hq
    exact h _ ((mem_moves_ofPairs hp).2 ⟨q, hq, rfl⟩)
  · intro h m hm
    obtain ⟨q, hq, rfl⟩ := (mem_moves_ofPairs hp).1 hm
    exact h q hq

/-! ## Conclusions -/

/-- **Zeng's boundary-word classification**, for CRIM: `ofPairs p` is a P-position iff its
boundary word has even length and even end-peeling statistic `M`. -/
theorem isP_ofPairs_iff {p : List (ℕ × ℕ)} (hp : ValidPairs p) :
    IsP (ofPairs p) ↔ Even (plen p) ∧ Even (endM p) :=
  pairs_classification (fun p => IsP (ofPairs p)) (fun _ hp => isP_ofPairs_iff_forall hp) p hp

/-- **conj:main holds**: every P-position has even rank. -/
theorem mainConjecture_holds : mainConjecture := by
  intro l hl hP
  obtain ⟨p, hp, rfl⟩ := exists_ofPairs hl
  obtain ⟨⟨k, hk⟩, -⟩ := (isP_ofPairs_iff hp).1 hP
  have h := length_add_part_one_ofPairs hp
  rw [rank_even_iff]
  omega

/-- **conj:bloby holds.** -/
theorem statement_holds : statement := statement_of_mainConjecture mainConjecture_holds

end AgenticConjectures.CrimHookStacks
