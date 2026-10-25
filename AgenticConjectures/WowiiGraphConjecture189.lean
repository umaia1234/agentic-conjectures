import Mathlib

/-!
# Written on the Wall II, Conjecture 189

*Conjecture (DeLaViña, Graffiti.pc, WOWII 189).*  If `G` is a connected graph on `n > 1`
vertices with `distEven(v) ≤ 1 + σ(G)` for every vertex `v`, then `G` has a Hamiltonian path.
Here `distEven(v)` counts the vertices at even distance from `v`, `v` included, and `σ(G)` is
the second entry of the nondecreasing degree sequence.

## Correspondence with the upstream snapshot

`statement` is the universal closure of `conjecture189` in Formal Conjectures
(`FormalConjectures/WrittenOnTheWallII/GraphConjecture189.lean`, commit `c094b97`, snapshot in
`problems/wowii-graph-conjecture-189/upstream/`).  Upstream binds
`{α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]` as section variables of the theorem;
here they are quantified inside the proposition, at a fixed universe `u`.  The hypotheses
(`G.Connected` and the `max'` inequality, with the same `by simp` nonemptiness proof) and the
conclusion are unchanged.  `distEven`, `degreeSequence` and `secondSmallestDegree` are copied
term for term from `FormalConjecturesForMathlib` (`SimpleGraph/VertexDistance.lean` and
`SimpleGraph/Degrees.lean`) because this repository depends on Mathlib only.

## What is proved

The conjecture itself is not proved here.  Under its hypothesis (H):

* `conjecture189_of_diam_le_two`: the conclusion holds when `G.diam ≤ 2`.  Then
  `distEven v = n - deg v` and (H) gives Ore's condition for Hamiltonian paths
  (`exists_isHamiltonian_of_ore`, proved from scratch by the rotation argument).  This
  reproduces case (1) of Theorem B of Easwar and Johari (arXiv 2609.11719).
* `card_dist_eq_two_le`: every vertex has at most `σ(G)` vertices at distance exactly two.
* `card_le_distEven_add_degree`, `card_le_degree_add` and `card_le_sq`: for every vertex `x`,
  `n ≤ distEven x + deg x + (distEven x - 1) σ(G)`; hence `deg x ≥ n - σ² - σ - 1` and
  `n ≤ (σ(G) + 1)²`.
* `search_reduction`: if moreover `σ(G) ≤ 3`, then `n ≤ 16`, every vertex has degree at least
  `n - 13`, every vertex has at most three vertices at distance two, and at least two vertices
  have degree at most three.  These facts make the case `σ(G) ≤ 3` a finite search, which is
  carried out (outside Lean) by the scripts in `problems/wowii-graph-conjecture-189/`.
* `exists_card_add_mul_self_le`, `four_mul_card_le` and `four_mul_card_le_sq`: for every vertex
  `x` some `s` satisfies `n + s² ≤ distEven x + deg x + s (σ(G) + 1)`, where `s` is the size of
  a minimum transversal of sets of neighbours of `x` that lie on geodesics towards the vertices
  at odd distance at least three.  Hence `4n ≤ 4 (σ + 1) + 4 deg x + (σ + 1)²` and
  `n ≤ 2σ + 1 + ⌊(σ + 1)² / 4⌋`.
* `search_reduction_four`: if `σ(G) ≤ 4`, then `n ≤ 15`, every vertex has degree at least
  `n - 11`, every vertex has at most four vertices at distance two, and at least two vertices
  have degree at most four.  This makes the case `σ(G) ≤ 4` a finite search, carried out by the
  same scripts.
-/

namespace AgenticConjectures.WowiiGraphConjecture189

open Finset

universe u

section Definitions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Number of vertices at even distance from `v`, `v` itself included.  Copied term for
term from Formal Conjectures, `SimpleGraph.distEven`. -/
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter fun w => Even (G.dist v w)).card

/-- The degree sequence of a graph, sorted in nondecreasing order.  Copied term for term
from Formal Conjectures, `SimpleGraph.degreeSequence`. -/
noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

/-- The second-smallest degree `σ(G)` (`0` when there are fewer than two vertices).
Copied term for term from Formal Conjectures, `SimpleGraph.secondSmallestDegree`. -/
noncomputable def secondSmallestDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (degreeSequence G).getD 1 0

end Definitions

/-- **WOWII Conjecture 189**, as stated by Formal Conjectures (`conjecture189`). -/
def statement : Prop :=
  ∀ (α : Type u) [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj], G.Connected →
    (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G →
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

section Ore

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

omit [Fintype α] [DecidableEq α] [DecidableRel G.Adj] in
/-- A nonempty list whose consecutive entries are adjacent is the support of a walk. -/
theorem exists_walk_support_eq :
    ∀ (l : List α) (a : α), (a :: l).IsChain G.Adj →
      ∃ b, ∃ p : G.Walk a b, p.support = a :: l
  | [], a, _ => ⟨a, .nil, rfl⟩
  | b :: l, a, h => by
    obtain ⟨c, p, hp⟩ := exists_walk_support_eq l b (List.isChain_cons_cons.1 h).2
    exact ⟨c, .cons (List.isChain_cons_cons.1 h).1 p, by simp [hp]⟩

omit [Fintype α] [DecidableRel G.Adj] in
/-- A duplicate-free chain through every vertex is a Hamiltonian path. -/
theorem exists_isHamiltonian_of_list {l : List α} (hnd : l.Nodup) (hc : l.IsChain G.Adj)
    (hall : ∀ v, v ∈ l) (hne : l ≠ []) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨b, p, hp⟩ := exists_walk_support_eq G t a hc
  exact ⟨a, b, p, fun v => by rw [hp]; exact List.count_eq_one_of_mem hnd (hall v)⟩

/-- **Ore's condition for Hamiltonian paths.**  If any two distinct non-adjacent vertices
have degree sum at least `n - 1`, the graph has a Hamiltonian path. -/
theorem exists_isHamiltonian_of_ore [Nonempty α]
    (hore : ∀ u v, u ≠ v → ¬ G.Adj u v → Fintype.card α ≤ G.degree u + G.degree v + 1) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  -- a longest duplicate-free chain `l`
  let P : ℕ → Prop := fun m => ∃ l : List α, l.Nodup ∧ l.IsChain G.Adj ∧ l.length = m
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hP1 : P 1 := ⟨[a₀], List.nodup_singleton _, List.isChain_singleton _, rfl⟩
  have hn1 : 1 ≤ Fintype.card α := Fintype.card_pos
  obtain ⟨l, hnd, hc, hlen⟩ := Nat.findGreatest_spec hn1 hP1
  have hmax : ∀ l' : List α, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ l.length := by
    intro l' hnd' hc'
    rw [hlen]
    exact Nat.le_findGreatest hnd'.length_le_card ⟨l', hnd', hc', rfl⟩
  have hL : 0 < l.length := by
    have := Nat.le_findGreatest hn1 hP1
    omega
  refine exists_isHamiltonian_of_list G hnd hc ?_ (List.ne_nil_of_length_pos hL)
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw⟩ := hcon
  -- the first vertex of a longest chain has all its neighbours on the chain
  have hend : ∀ l' : List α, l'.Nodup → l'.IsChain G.Adj → l'.length = l.length →
      ∀ (h : 0 < l'.length) (v : α), G.Adj (l'[0]'h) v → v ∈ l' := by
    intro l' hnd' hc' hlen' h v hv
    by_contra hvl
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_length_pos h
    have := hmax (v :: a :: t) (List.nodup_cons.2 ⟨hvl, hnd'⟩)
      (List.isChain_cons_cons.2 ⟨G.symm hv, hc'⟩)
    simp only [List.length_cons] at this hlen'
    omega
  set x := l[0]'hL with hx
  set z := l[l.length - 1]'(by omega) with hz
  have hxN : ∀ v, G.Adj x v → v ∈ l := hend l hnd hc rfl hL
  have hzN : ∀ v, G.Adj z v → v ∈ l := by
    intro v hv
    have hr : 0 < l.reverse.length := by simpa using hL
    have := hend l.reverse (List.nodup_reverse.2 hnd)
      (List.isChain_reverse.2 (hc.imp fun a b h => G.symm h)) (by simp) hr v
      (by simpa [List.getElem_reverse] using hv)
    simpa using this
  have hLn : l.length + 1 ≤ Fintype.card α := by
    have h1 : l.toFinset ⊆ univ.erase w := fun v hv =>
      mem_erase.2 ⟨fun h => hw (h ▸ List.mem_toFinset.1 hv), mem_univ _⟩
    have h2 := card_le_card h1
    rw [List.toFinset_card_of_nodup hnd, card_erase_of_mem (mem_univ _), card_univ] at h2
    omega
  -- `w` has a neighbour `y` on the chain: a common neighbour of `x` and `w`
  have hxl : x ∈ l := List.getElem_mem hL
  have hxw : x ≠ w := fun h => hw (h ▸ hxl)
  have hxw' : ¬ G.Adj x w := fun h => hw (hxN w h)
  obtain ⟨y, hy⟩ : (G.neighborFinset x ∩ G.neighborFinset w).Nonempty := by
    have h1 := hore x w hxw hxw'
    refine inter_nonempty_of_card_lt_card_add_card (s := (univ.erase x).erase w) ?_ ?_ ?_
    · intro v hv
      rw [SimpleGraph.mem_neighborFinset] at hv
      simp only [mem_erase, mem_univ, and_true]
      exact ⟨fun h => hw (h ▸ hxN v hv), (G.ne_of_adj hv).symm⟩
    · intro v hv
      rw [SimpleGraph.mem_neighborFinset] at hv
      simp only [mem_erase, mem_univ, and_true]
      exact ⟨(G.ne_of_adj hv).symm, fun h => hxw' (h ▸ G.symm hv)⟩
    · rw [card_erase_of_mem (by simp [Ne.symm hxw]), card_erase_of_mem (mem_univ _),
        card_univ, SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree]
      omega
  rw [mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hy
  have hyl : y ∈ l := hxN y hy.1
  obtain ⟨jy, hjy, hjy'⟩ := List.mem_iff_getElem.1 hyl
  have hL2 : 2 ≤ l.length := by
    rcases Nat.lt_or_ge jy 1 with h | h
    · have : jy = 0 := by omega
      subst this
      exact absurd hjy' (G.ne_of_adj hy.1)
    · omega
  -- a position `i` with `x ~ l[i+1]` and `l[i] ~ z`
  obtain ⟨i, hi, hxi, hiz⟩ :
      ∃ i, ∃ hi : i + 1 < l.length, G.Adj x (l[i + 1]'hi) ∧ G.Adj (l[i]'(by omega)) z := by
    by_cases hxz : G.Adj x z
    · have e : l.length - 2 + 1 = l.length - 1 := by omega
      refine ⟨l.length - 2, by omega, ?_, ?_⟩
      · rw [getElem_congr_idx e]
        exact hxz
      · have := List.isChain_iff_getElem.1 hc (l.length - 2) (by omega)
        rw [getElem_congr_idx e] at this
        exact this
    · have hxz' : x ≠ z := by
        intro h
        have := (hnd.getElem_inj_iff).1 h
        omega
      have hore' := hore x z hxz' hxz
      let f : ℕ → α := fun i => l.getD i x
      have hf : ∀ i (hi : i < l.length), f i = l[i] := fun i hi => List.getD_eq_getElem l x hi
      let A := (range (l.length - 1)).filter fun i => G.Adj x (f (i + 1))
      let B := (range (l.length - 1)).filter fun i => G.Adj (f i) z
      have hA : G.degree x ≤ A.card := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        refine (card_le_card ?_).trans (card_image_le (f := fun i => f (i + 1)))
        intro v hv
        rw [SimpleGraph.mem_neighborFinset] at hv
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 (hxN v hv)
        have hj0 : j ≠ 0 := by
          rintro rfl
          exact G.irrefl hv
        refine mem_image.2 ⟨j - 1, mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩, ?_⟩
        · rw [show j - 1 + 1 = j by omega, hf j hj]
          exact hv
        · show f (j - 1 + 1) = l[j]
          rw [show j - 1 + 1 = j by omega, hf j hj]
      have hB : G.degree z ≤ B.card := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        refine (card_le_card ?_).trans (card_image_le (f := f))
        intro v hv
        rw [SimpleGraph.mem_neighborFinset] at hv
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 (hzN v hv)
        have hj1 : j ≠ l.length - 1 := by
          rintro rfl
          exact G.irrefl hv
        refine mem_image.2 ⟨j, mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩, hf j hj⟩
        rw [hf j hj]
        exact G.symm hv
      obtain ⟨i, hi⟩ := inter_nonempty_of_card_lt_card_add_card (t := A) (u := B)
        (filter_subset _ _) (filter_subset _ _) (by rw [card_range]; omega)
      rw [mem_inter, mem_filter, mem_filter, mem_range] at hi
      refine ⟨i, by omega, ?_, ?_⟩
      · rw [← hf (i + 1) (by omega)]
        exact hi.1.2
      · rw [← hf i (by omega)]
        exact hi.2.2
  -- the chain closes up into a cycle `c` through the same vertices
  set c := l.take (i + 1) ++ (l.drop (i + 1)).reverse with hcdef
  have hcp : c.Perm l := by
    have := (List.reverse_perm (l.drop (i + 1))).append_left (l.take (i + 1))
    rwa [List.take_append_drop] at this
  have hcc : c.IsChain G.Adj := by
    refine List.IsChain.append (hc.take _)
      (List.isChain_reverse.2 ((hc.drop _).imp fun a b h => G.symm h)) ?_
    intro a ha b hb
    rw [List.getLast?_take] at ha
    rw [List.head?_reverse, List.getLast?_drop] at hb
    simp [List.getElem?_eq_getElem (show i < l.length by omega)] at ha
    simp [show ¬ l.length ≤ i + 1 by omega, List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show l.length - 1 < l.length by omega)] at hb
    subst ha
    subst hb
    exact hiz
  have hchead : c.head? = some x := by
    rw [hcdef, List.head?_append, List.head?_take, if_neg (by omega)]
    obtain ⟨a, t, ht⟩ := List.exists_cons_of_length_pos hL
    simp [ht, hx]
  have hclast : c.getLast? = some (l[i + 1]'hi) := by
    simp [hcdef, List.head?_drop, List.getElem?_eq_getElem hi]
  -- rotate the cycle to start at `y` and put `w` in front
  have hyc : y ∈ c := hcp.mem_iff.2 hyl
  obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.1 hyc
  set c' := c.drop j ++ c.take j with hc'def
  have hc'p : c'.Perm l := List.perm_append_comm.trans (by rw [List.take_append_drop]; exact hcp)
  have hc'c : c'.IsChain G.Adj := by
    refine List.IsChain.append (hcc.drop _) (hcc.take _) ?_
    intro a ha b hb
    rw [List.getLast?_drop, if_neg (by omega), hclast] at ha
    rw [List.head?_take] at hb
    split_ifs at hb with hj0
    · simp at hb
    rw [hchead] at hb
    simp at ha hb
    subst ha
    subst hb
    exact G.symm hxi
  have hc'h : c'.head? = some y := by
    simp [hc'def, List.head?_drop, List.getElem?_eq_getElem hj, hjy]
  have hlong := hmax (w :: c')
    (List.nodup_cons.2 ⟨fun h => hw (hc'p.mem_iff.1 h), hc'p.nodup_iff.2 hnd⟩)
    (List.isChain_cons.2 ⟨fun b hb => by
      rw [hc'h] at hb
      simp at hb
      subst hb
      exact hy.2, hc'c⟩)
  simp [hc'p.length_eq] at hlong

end Ore

section Hypothesis

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

/-- In a nondecreasing list whose second entry exceeds `M`, at most one entry is `≤ M`. -/
private lemma countP_le_one_of_lt_getD {s : List ℕ} (hs : s.Pairwise (· ≤ ·)) {M : ℕ}
    (hM : M < s.getD 1 0) : s.countP (fun d => decide (d ≤ M)) ≤ 1 := by
  match s, hs, hM with
  | [], _, _ => simp
  | [_], _, _ => exact List.countP_le_length.trans (by simp)
  | a :: b :: t, hs, hM =>
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hM
    have ht : ∀ d ∈ t, b ≤ d := (List.pairwise_cons.1 (List.pairwise_cons.1 hs).2).1
    have h0 : t.countP (fun d => decide (d ≤ M)) = 0 :=
      List.countP_eq_zero.2 fun d hd => by
        have := ht d hd
        simp only [decide_eq_true_eq]
        omega
    have hb : ¬ b ≤ M := by omega
    rw [List.countP_cons, List.countP_cons, h0]
    by_cases ha : a ≤ M <;> simp [ha, hb]

/-- At most one vertex has degree below `σ(G)`: any two distinct vertices have the larger
of their degrees at least `σ(G)`. -/
theorem secondSmallestDegree_le_max {u v : α} (huv : u ≠ v) :
    secondSmallestDegree G ≤ max (G.degree u) (G.degree v) := by
  set M := max (G.degree u) (G.degree v)
  by_contra hlt
  push Not at hlt
  have hle := countP_le_one_of_lt_getD (s := degreeSequence G) (Multiset.pairwise_sort _ _) hlt
  have h2 : 2 ≤ (univ.filter fun w => G.degree w ≤ M).card := by
    have hsub : ({u, v} : Finset α) ⊆ univ.filter fun w => G.degree w ≤ M := by
      intro w hw
      rw [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp [M]
    simpa [card_pair huv] using card_le_card hsub
  have h3 : (degreeSequence G).countP (fun d => decide (d ≤ M)) =
      (univ.filter fun w => G.degree w ≤ M).card := by
    rw [← Multiset.coe_countP, degreeSequence, Multiset.sort_eq, Multiset.countP_map]
    rfl
  omega

omit [DecidableEq α] in
/-- Some vertex has degree exactly `σ(G)`. -/
theorem exists_degree_eq_secondSmallestDegree [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj] : ∃ x, G.degree x = secondSmallestDegree G := by
  have hlen : 1 < (degreeSequence G).length := by
    rw [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hmem := (Multiset.mem_sort (r := (· ≤ ·))).1 (List.getElem_mem hlen)
  obtain ⟨v, -, hv⟩ := Multiset.mem_map.1 hmem
  exact ⟨v, by rw [hv, secondSmallestDegree, List.getD_eq_getElem _ _ hlen]⟩

omit [DecidableEq α] in
/-- At least two vertices have degree at most `σ(G)`. -/
theorem two_le_card_degree_le [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    2 ≤ (univ.filter fun w => G.degree w ≤ secondSmallestDegree G).card := by
  have h3 : (degreeSequence G).countP (fun d => decide (d ≤ secondSmallestDegree G)) =
      (univ.filter fun w => G.degree w ≤ secondSmallestDegree G).card := by
    rw [← Multiset.coe_countP, degreeSequence, Multiset.sort_eq, Multiset.countP_map]
    rfl
  have hlen : 1 < (degreeSequence G).length := by
    rw [degreeSequence, Multiset.length_sort, Multiset.card_map, Finset.card_val,
      Finset.card_univ]
    exact Fintype.one_lt_card
  have hs : (degreeSequence G).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  rw [← h3, secondSmallestDegree]
  match degreeSequence G, hs, hlen with
  | a :: b :: t, hs, _ =>
    have hab : a ≤ b := List.rel_of_pairwise_cons hs (by simp)
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [List.countP_cons, List.countP_cons]
    simp [hab]

/-- In a connected graph of diameter at most two, `distEven v = n - deg v`. -/
theorem distEven_eq_card_sub_degree (hconn : G.Connected) (hdiam : G.diam ≤ 2) (v : α) :
    distEven G v = Fintype.card α - G.degree v := by
  have : Nonempty α := hconn.nonempty
  have hne : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hconn
  have heq : (univ.filter fun w => Even (G.dist v w)) = univ.filter fun w => ¬ G.Adj v w := by
    ext w
    simp only [mem_filter, mem_univ, true_and]
    rw [← SimpleGraph.dist_eq_one_iff_adj]
    have := (SimpleGraph.dist_le_diam hne (u := v) (v := w)).trans hdiam
    rcases (by omega : G.dist v w = 0 ∨ G.dist v w = 1 ∨ G.dist v w = 2) with h | h | h <;>
      simp [h]
  rw [distEven, heq, filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ,
    ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]

/-- **WOWII Conjecture 189 for graphs of diameter at most two** (Easwar–Johari,
Theorem B(1)).  The hypothesis gives `deg v ≥ n - 1 - σ` for every `v`, and the larger degree
of two distinct vertices is at least `σ`, so Ore's condition holds. -/
theorem conjecture189_of_diam_le_two [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hdiam : G.diam ≤ 2)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hdeg : ∀ v, Fintype.card α ≤ G.degree v + 1 + secondSmallestDegree G := by
    intro v
    have h1 := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans hσ
    rw [distEven_eq_card_sub_degree h hdiam] at h1
    omega
  refine exists_isHamiltonian_of_ore G fun u v huv _ => ?_
  have hm := secondSmallestDegree_le_max (G := G) huv
  have hu := hdeg u
  have hv := hdeg v
  rcases le_max_iff.1 hm with hm | hm <;> omega

/-- Under the hypothesis of Conjecture 189 every vertex has at most `σ(G)` vertices at
distance exactly two (they are at even distance and differ from the vertex itself). -/
theorem card_dist_eq_two_le [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (v : α) : (Finset.univ.filter fun w => G.dist v w = 2).card ≤ secondSmallestDegree G := by
  have h1 : distEven G v ≤ _ := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans hσ
  have h2 : (univ.filter fun w => G.dist v w = 2) ⊆
      (univ.filter fun w => Even (G.dist v w)).erase v := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and, mem_erase] at hw ⊢
    refine ⟨fun h => ?_, by rw [hw]; decide⟩
    rw [h, SimpleGraph.dist_self] at hw
    exact absurd hw (by decide)
  have h3 := card_le_card h2
  rw [card_erase_of_mem (by simp)] at h3
  unfold distEven at h1
  omega

omit [Fintype α] [DecidableEq α] [DecidableRel G.Adj] in
/-- In a connected graph every vertex `w ≠ x` has a neighbour one step closer to `x`. -/
private lemma exists_adj_dist_add_one (hconn : G.Connected) {x w : α} (hw : w ≠ x) :
    ∃ y, G.Adj w y ∧ G.dist x y + 1 = G.dist x w := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist w x
  cases p with
  | nil => exact absurd rfl hw
  | @cons _ y _ h q =>
    refine ⟨y, h, ?_⟩
    rw [SimpleGraph.Walk.length_cons, SimpleGraph.dist_comm] at hp
    have h2 : G.dist x y ≤ q.length := by
      rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_le q
    have h3 := (G.symm h).diff_dist_adj (u := x)
    omega

/-- **Vertex bound.**  Under the hypothesis of Conjecture 189, every vertex `x` of a
connected graph satisfies `n ≤ distEven x + deg x + (distEven x - 1) σ(G)`.  A vertex `w` at
odd distance at least three from `x` has a neighbour `y` one step closer to `x`, which is at
even distance from `x`, and `w` lies at distance two from a fixed neighbour `q y` of `y` one
step closer still; by `card_dist_eq_two_le` each `y` accounts for at most `σ` such `w`. -/
theorem card_le_distEven_add_degree [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (x : α) :
    Fintype.card α ≤
      distEven G x + G.degree x + (distEven G x - 1) * secondSmallestDegree G := by
  classical
  set σ := secondSmallestDegree G with hσdef
  have h2 := card_dist_eq_two_le G hσ
  -- a parent `q y` of every vertex `y ≠ x`
  have hpar : ∀ y : α, ∃ p, y ≠ x → G.Adj y p ∧ G.dist x p + 1 = G.dist x y := by
    intro y
    by_cases hy : y = x
    · exact ⟨y, fun h => absurd hy h⟩
    · obtain ⟨p, hp⟩ := exists_adj_dist_add_one hconn hy
      exact ⟨p, fun _ => hp⟩
  choose q hq using hpar
  set D := univ.filter fun w => Even (G.dist x w) with hD
  set R := univ.filter fun w => ¬ Even (G.dist x w) ∧ ¬ G.Adj x w with hR
  have hcover : (univ : Finset α) ⊆ D ∪ G.neighborFinset x ∪ R := by
    intro w _
    by_cases he : Even (G.dist x w)
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨mem_univ _, he⟩))
    · by_cases ha : G.Adj x w
      · exact mem_union_left _ (mem_union_right _ ((G.mem_neighborFinset x w).2 ha))
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, he, ha⟩)
  have hRsub : R ⊆ (D.erase x).biUnion fun y => univ.filter fun w => G.dist (q y) w = 2 := by
    intro w hw
    simp only [hR, mem_filter, mem_univ, true_and] at hw
    obtain ⟨hodd, hna⟩ := hw
    have hwx : w ≠ x := by
      intro h
      rw [h, SimpleGraph.dist_self] at hodd
      exact hodd (by decide)
    have hd1 : G.dist x w ≠ 1 := fun h => hna (SimpleGraph.dist_eq_one_iff_adj.1 h)
    obtain ⟨y, hwy, hy⟩ := exists_adj_dist_add_one hconn hwx
    have hyx : y ≠ x := by
      intro h
      rw [h, SimpleGraph.dist_self] at hy
      omega
    obtain ⟨hyp, hpy⟩ := hq y hyx
    rw [mem_biUnion]
    refine ⟨y, mem_erase.2 ⟨hyx, ?_⟩, ?_⟩
    · simp only [hD, mem_filter, mem_univ, true_and]
      rw [Nat.even_iff] at hodd ⊢
      omega
    · simp only [mem_filter, mem_univ, true_and]
      have hle : G.dist (q y) w ≤ 2 :=
        SimpleGraph.dist_le (.cons (G.symm hyp) (.cons (G.symm hwy) .nil))
      have hge : G.dist x w ≤ G.dist x (q y) + G.dist (q y) w := hconn.dist_triangle
      omega
  have hRcard : R.card ≤ (D.card - 1) * σ := by
    refine (card_le_card hRsub).trans (card_biUnion_le.trans ?_)
    calc ∑ y ∈ D.erase x, (univ.filter fun w => G.dist (q y) w = 2).card
        ≤ ∑ _y ∈ D.erase x, σ := sum_le_sum fun y _ => h2 (q y)
      _ = (D.erase x).card * σ := by rw [sum_const, smul_eq_mul]
      _ = (D.card - 1) * σ := by rw [card_erase_of_mem (by simp [hD])]
  have hDcard : D.card = distEven G x := rfl
  have hN : (G.neighborFinset x).card = G.degree x := G.card_neighborFinset_eq_degree x
  have hn := card_le_card hcover
  rw [card_univ] at hn
  have hu := (card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le D (G.neighborFinset x)) R.card)
  rw [← hDcard]
  omega

/-- **Degree bound.**  Under the hypothesis of Conjecture 189 every vertex of a connected graph
has degree at least `n - σ(G)² - σ(G) - 1`. -/
theorem card_le_degree_add [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (x : α) :
    Fintype.card α ≤ G.degree x + secondSmallestDegree G ^ 2 + secondSmallestDegree G + 1 := by
  have h := card_le_distEven_add_degree G hconn hσ x
  have hde : distEven G x ≤ secondSmallestDegree G + 1 :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ x))).trans (by omega)
  have h5 : (distEven G x - 1) * secondSmallestDegree G ≤
      secondSmallestDegree G * secondSmallestDegree G :=
    Nat.mul_le_mul_right _ (by omega)
  have hsq : secondSmallestDegree G ^ 2 = secondSmallestDegree G * secondSmallestDegree G :=
    sq _
  omega

/-- **Order bound.**  Under the hypothesis of Conjecture 189 a connected graph has at most
`(σ(G) + 1)²` vertices: apply `card_le_degree_add` to a vertex of degree `σ(G)`. -/
theorem card_le_sq [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    Fintype.card α ≤ (secondSmallestDegree G + 1) ^ 2 := by
  obtain ⟨x, hx⟩ := exists_degree_eq_secondSmallestDegree G
  have h := card_le_degree_add G hconn hσ x
  rw [hx] at h
  have hsq : (secondSmallestDegree G + 1) ^ 2 =
      secondSmallestDegree G ^ 2 + 2 * secondSmallestDegree G + 1 := by ring
  omega

/-- **Search reduction.**  A connected graph satisfying the hypothesis of Conjecture 189 with
`σ(G) ≤ 3` has at most `16` vertices, minimum degree at least `n - 13`, at most three vertices
at distance two from any vertex, and at least two vertices of degree at most three.  These are
the facts the computer search for the case `σ(G) ≤ 3` relies on. -/
theorem search_reduction [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (h3 : secondSmallestDegree G ≤ 3) :
    Fintype.card α ≤ 16 ∧ (∀ x, Fintype.card α ≤ G.degree x + 13) ∧
      (∀ v, (Finset.univ.filter fun w => G.dist v w = 2).card ≤ 3) ∧
      2 ≤ (Finset.univ.filter fun w => G.degree w ≤ 3).card := by
  have hsq : secondSmallestDegree G ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left h3 2
  refine ⟨?_, fun x => ?_, fun v => (card_dist_eq_two_le G hσ v).trans h3, ?_⟩
  · have h := card_le_sq G hconn hσ
    have h4 : (secondSmallestDegree G + 1) ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  · have h := card_le_degree_add G hconn hσ x
    omega
  · exact (two_le_card_degree_le G).trans
      (card_le_card fun w hw => by
        simp only [mem_filter, mem_univ, true_and] at hw ⊢; omega)

/-- **Transversal bound.**  Under the hypothesis of Conjecture 189, for every vertex `x` of a
connected graph there is an `s` with `n + s² ≤ distEven x + deg x + s (σ(G) + 1)`.

Let `O` be the set of vertices at odd distance at least three from `x`, give each `z ∈ O` a
neighbour `q z` one step closer to `x`, and let `Dn p` be the set of neighbours of `x` one step
closer to `p` than `x` is.  Every `y ∈ Dn (q z)` is at even distance `dist x z - 1` from `z`.
Take `Y` of minimum size `s` meeting every `Dn (q z)`.  Each `y ∈ Y` has a private `z`, with
`y` the only element of `Y` in `Dn (q z)`.  For `y' ∈ Y`, every other `y ∈ Y` gives a vertex at
even distance from `y'` outside `O`: `y` itself if `y` and `y'` are not adjacent, and the
private parent `q z` of `y` if they are.  So `y'` has at most `σ + 1 - s` vertices of `O` at
even distance, and these sets cover `O`. -/
theorem exists_card_add_mul_self_le [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (x : α) :
    ∃ s, Fintype.card α + s * s ≤
      distEven G x + G.degree x + s * (secondSmallestDegree G + 1) := by
  classical
  set σ := secondSmallestDegree G with hσdef
  have hDle : ∀ v, distEven G v ≤ σ + 1 := fun v =>
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans (by omega)
  -- a parent `q w` of every vertex `w ≠ x`
  have hpar : ∀ w : α, ∃ p, w ≠ x → G.Adj w p ∧ G.dist x p + 1 = G.dist x w := by
    intro w
    by_cases hw : w = x
    · exact ⟨w, fun h => absurd hw h⟩
    · obtain ⟨p, hp⟩ := exists_adj_dist_add_one hconn hw
      exact ⟨p, fun _ => hp⟩
  choose q hq using hpar
  set N := G.neighborFinset x with hN
  -- `Dn p`: the neighbours of `x` one step closer to `p` than `x` is
  set Dn : α → Finset α := fun p => N.filter fun y => G.dist y p + 1 = G.dist x p with hDn
  -- `O`: the vertices at odd distance at least three from `x`
  set O := univ.filter fun w => ¬ Even (G.dist x w) ∧ ¬ G.Adj x w with hO
  set E : α → Finset α := fun v => univ.filter fun w => Even (G.dist v w) with hE
  have hOx : ∀ z ∈ O, z ≠ x := by
    intro z hz h
    simp only [hO, mem_filter, mem_univ, true_and] at hz
    rw [h, SimpleGraph.dist_self] at hz
    exact hz.1 (by decide)
  have hOd : ∀ z ∈ O, 3 ≤ G.dist x z ∧ ¬ Even (G.dist x z) := by
    intro z hz
    simp only [hO, mem_filter, mem_univ, true_and] at hz
    refine ⟨?_, hz.1⟩
    have h0 : G.dist x z ≠ 0 := fun h => hz.1 (by rw [h]; decide)
    have h1 : G.dist x z ≠ 1 := fun h => hz.2 (SimpleGraph.dist_eq_one_iff_adj.1 h)
    have h2 : G.dist x z ≠ 2 := fun h => hz.1 (by rw [h]; decide)
    omega
  have hqd : ∀ z ∈ O, G.dist x (q z) + 1 = G.dist x z := fun z hz => (hq z (hOx z hz)).2
  have hqadj : ∀ z ∈ O, G.Adj z (q z) := fun z hz => (hq z (hOx z hz)).1
  -- `Dn (q z)` is nonempty: a geodesic from `x` to `q z` starts with such a neighbour
  have hDnne : ∀ z ∈ O, (Dn (q z)).Nonempty := by
    intro z hz
    have hqx : x ≠ q z := by
      intro h
      have h1 := hqd z hz
      rw [← h, SimpleGraph.dist_self] at h1
      have h2 := (hOd z hz).1
      omega
    obtain ⟨y, hxy, hy⟩ := exists_adj_dist_add_one hconn hqx
    refine ⟨y, ?_⟩
    simp only [hDn, mem_filter, hN, SimpleGraph.mem_neighborFinset]
    refine ⟨hxy, ?_⟩
    rw [SimpleGraph.dist_comm (u := y), SimpleGraph.dist_comm (u := x)]
    exact hy
  -- a vertex `y ∈ Dn (q z)` is at even distance `dist x z - 1` from `z`
  have hcov : ∀ z ∈ O, ∀ y ∈ Dn (q z), Even (G.dist y z) := by
    intro z hz y hy
    simp only [hDn, mem_filter, hN, SimpleGraph.mem_neighborFinset] at hy
    obtain ⟨hxy, hyd⟩ := hy
    have h1 : G.dist y z ≤ G.dist y (q z) + G.dist (q z) z := hconn.dist_triangle
    have h2 : G.dist (q z) z = 1 := SimpleGraph.dist_eq_one_iff_adj.2 (G.symm (hqadj z hz))
    have h3 : G.dist x z ≤ G.dist x y + G.dist y z := hconn.dist_triangle
    have h4 : G.dist x y = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hxy
    have h5 := hqd z hz
    have h6 := (hOd z hz).2
    rw [Nat.even_iff] at h6 ⊢
    omega
  -- a minimum transversal `Y` of the sets `Dn (q z)`
  set T := N.powerset.filter fun Y => ∀ z ∈ O, (Y ∩ Dn (q z)).Nonempty with hT
  have hNT : N ∈ T := by
    simp only [hT, mem_filter, mem_powerset]
    refine ⟨subset_refl _, fun z hz => ?_⟩
    obtain ⟨y, hy⟩ := hDnne z hz
    have hyN : y ∈ N := by
      simp only [hDn, mem_filter] at hy
      exact hy.1
    exact ⟨y, mem_inter.2 ⟨hyN, hy⟩⟩
  obtain ⟨Y, hYT, hYmin⟩ := T.exists_min_image card ⟨N, hNT⟩
  simp only [hT, mem_filter, mem_powerset] at hYT
  obtain ⟨hYN, hYcov⟩ := hYT
  refine ⟨Y.card, ?_⟩
  -- every `y ∈ Y` has a private `z`: `y` is the only element of `Y` in `Dn (q z)`
  have hpriv : ∀ y ∈ Y, ∃ z ∈ O, y ∈ Dn (q z) ∧ ∀ y' ∈ Y, y' ≠ y → y' ∉ Dn (q z) := by
    intro y hy
    by_contra hcon
    push Not at hcon
    have hmem : Y.erase y ∈ T := by
      simp only [hT, mem_filter, mem_powerset]
      refine ⟨(erase_subset _ _).trans hYN, fun z hz => ?_⟩
      obtain ⟨y'', hy''⟩ := hYcov z hz
      rw [mem_inter] at hy''
      by_cases hyy : y'' = y
      · rw [hyy] at hy''
        obtain ⟨y', hy'Y, hy'ne, hy'Dn⟩ := hcon z hz hy''.2
        exact ⟨y', mem_inter.2 ⟨mem_erase.2 ⟨hy'ne, hy'Y⟩, hy'Dn⟩⟩
      · exact ⟨y'', mem_inter.2 ⟨mem_erase.2 ⟨hyy, hy''.1⟩, hy''.2⟩⟩
    have h1 := hYmin _ hmem
    rw [card_erase_of_mem hy] at h1
    have h2 : 0 < Y.card := card_pos.2 ⟨y, hy⟩
    omega
  choose! zz hzzO hzzDn hzzpriv using hpriv
  -- facts about the private parents `q (zz y)`
  have hpp : ∀ y ∈ Y, G.Adj x y ∧ G.dist y (q (zz y)) + 1 = G.dist x (q (zz y)) ∧
      Even (G.dist x (q (zz y))) := by
    intro y hy
    have h1 := hzzDn y hy
    simp only [hDn, mem_filter, hN, SimpleGraph.mem_neighborFinset] at h1
    refine ⟨h1.1, h1.2, ?_⟩
    have h2 := hqd _ (hzzO y hy)
    have h3 := (hOd _ (hzzO y hy)).2
    rw [Nat.even_iff] at h3 ⊢
    omega
  have hYadj : ∀ y ∈ Y, G.Adj x y := fun y hy => (hpp y hy).1
  -- `Y.card + |E y' ∩ O| ≤ distEven y'` for every `y' ∈ Y`
  have hkey : ∀ y' ∈ Y, Y.card + (E y' ∩ O).card ≤ distEven G y' := by
    intro y' hy'
    have hy'x := hYadj y' hy'
    set f : α → α := fun y => if G.Adj y' y then q (zz y) else y with hf
    have hfE : ∀ y ∈ Y.erase y', f y ∈ E y' := by
      intro y hy
      obtain ⟨hne, hyY⟩ := mem_erase.1 hy
      obtain ⟨hxy, hyd, hev⟩ := hpp y hyY
      simp only [hE, mem_filter, mem_univ, true_and, hf]
      by_cases hadj : G.Adj y' y
      · rw [if_pos hadj]
        have h1 : G.dist y' (q (zz y)) ≤ G.dist y' y + G.dist y (q (zz y)) :=
          hconn.dist_triangle
        have h2 : G.dist y' y = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hadj
        have h3 : G.dist x (q (zz y)) ≤ G.dist x y' + G.dist y' (q (zz y)) :=
          hconn.dist_triangle
        have h4 : G.dist x y' = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hy'x
        have h5 : ¬ (G.dist y' (q (zz y)) + 1 = G.dist x (q (zz y))) := by
          intro h
          apply hzzpriv y hyY y' hy' (Ne.symm hne)
          simp only [hDn, mem_filter, hN, SimpleGraph.mem_neighborFinset]
          exact ⟨hy'x, h⟩
        rw [Nat.even_iff] at hev ⊢
        omega
      · rw [if_neg hadj]
        have h1 : G.dist y' y ≤ 2 :=
          SimpleGraph.dist_le (.cons (G.symm hy'x) (.cons hxy .nil))
        have h2 : 0 < G.dist y' y := hconn.pos_dist_of_ne (Ne.symm hne)
        have h3 : G.dist y' y ≠ 1 := fun h => hadj (SimpleGraph.dist_eq_one_iff_adj.1 h)
        have h4 : G.dist y' y = 2 := by omega
        rw [h4]
        decide
    have hfO : ∀ y ∈ Y.erase y', f y ∉ O := by
      intro y hy hO'
      obtain ⟨-, hyY⟩ := mem_erase.1 hy
      obtain ⟨hxy, -, hev⟩ := hpp y hyY
      simp only [hO, mem_filter, mem_univ, true_and, hf] at hO'
      by_cases hadj : G.Adj y' y
      · rw [if_pos hadj] at hO'
        exact hO'.1 hev
      · rw [if_neg hadj] at hO'
        exact hO'.2 hxy
    have hfne : ∀ y ∈ Y.erase y', f y ≠ y' := by
      intro y hy hfy
      obtain ⟨hne, hyY⟩ := mem_erase.1 hy
      obtain ⟨-, -, hev⟩ := hpp y hyY
      simp only [hf] at hfy
      by_cases hadj : G.Adj y' y
      · rw [if_pos hadj] at hfy
        rw [hfy, SimpleGraph.dist_eq_one_iff_adj.2 hy'x] at hev
        exact absurd hev (by decide)
      · rw [if_neg hadj] at hfy
        exact hne hfy
    have hfinj : Set.InjOn f (Y.erase y') := by
      intro a ha b hb hab
      obtain ⟨-, haY⟩ := mem_erase.1 (mem_coe.1 ha)
      obtain ⟨-, hbY⟩ := mem_erase.1 (mem_coe.1 hb)
      simp only [hf] at hab
      by_cases hadja : G.Adj y' a <;> by_cases hadjb : G.Adj y' b
      · rw [if_pos hadja, if_pos hadjb] at hab
        by_contra hne
        have h1 := hzzDn b hbY
        rw [← hab] at h1
        exact hzzpriv a haY b hbY (Ne.symm hne) h1
      · rw [if_pos hadja, if_neg hadjb] at hab
        have hev := (hpp a haY).2.2
        rw [hab, SimpleGraph.dist_eq_one_iff_adj.2 (hYadj b hbY)] at hev
        exact absurd hev (by decide)
      · rw [if_neg hadja, if_pos hadjb] at hab
        have hev := (hpp b hbY).2.2
        rw [← hab, SimpleGraph.dist_eq_one_iff_adj.2 (hYadj a haY)] at hev
        exact absurd hev (by decide)
      · rw [if_neg hadja, if_neg hadjb] at hab
        exact hab
    have hy'O : y' ∉ O := by
      intro h
      simp only [hO, mem_filter, mem_univ, true_and] at h
      exact h.2 hy'x
    have hdisj : Disjoint ((Y.erase y').image f) (E y' ∩ O) := by
      rw [disjoint_left]
      intro w hw hw'
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hw
      exact hfO y hy (mem_inter.1 hw').2
    have hnotin : y' ∉ (Y.erase y').image f ∪ (E y' ∩ O) := by
      rw [mem_union, not_or]
      refine ⟨fun h => ?_, fun h => hy'O (mem_inter.1 h).2⟩
      obtain ⟨y, hy, hfy⟩ := mem_image.1 h
      exact hfne y hy hfy
    have hsub : insert y' ((Y.erase y').image f ∪ (E y' ∩ O)) ⊆ E y' := by
      intro w hw
      rw [mem_insert, mem_union] at hw
      rcases hw with rfl | hw | hw
      · simp only [hE, mem_filter, mem_univ, true_and, SimpleGraph.dist_self]
        decide
      · obtain ⟨y, hy, rfl⟩ := mem_image.1 hw
        exact hfE y hy
      · exact (mem_inter.1 hw).1
    have h1 := card_le_card hsub
    rw [card_insert_of_notMem hnotin, card_union_of_disjoint hdisj,
      card_image_of_injOn hfinj, card_erase_of_mem hy'] at h1
    have h2 : 0 < Y.card := card_pos.2 ⟨y', hy'⟩
    have h3 : (E y').card = distEven G y' := rfl
    omega
  -- `O` is covered by the sets `E y ∩ O`, `y ∈ Y`
  have hOsub : O ⊆ Y.biUnion fun y => E y ∩ O := by
    intro z hz
    obtain ⟨y, hy⟩ := hYcov z hz
    rw [mem_inter] at hy
    rw [mem_biUnion]
    refine ⟨y, hy.1, mem_inter.2 ⟨?_, hz⟩⟩
    simp only [hE, mem_filter, mem_univ, true_and]
    exact hcov z hz y hy.2
  have hOcard : O.card + Y.card * Y.card ≤ Y.card * (σ + 1) := by
    have h1 := (card_le_card hOsub).trans card_biUnion_le
    have h2 : ∑ y ∈ Y, (Y.card + (E y ∩ O).card) ≤ ∑ _y ∈ Y, (σ + 1) :=
      sum_le_sum fun y hy => (hkey y hy).trans (hDle y)
    rw [sum_add_distrib, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at h2
    omega
  -- `V = E x ∪ N(x) ∪ O`
  have hcover : (univ : Finset α) ⊆ E x ∪ N ∪ O := by
    intro w _
    by_cases he : Even (G.dist x w)
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨mem_univ _, he⟩))
    · by_cases ha : G.Adj x w
      · exact mem_union_left _ (mem_union_right _ ((G.mem_neighborFinset x w).2 ha))
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, he, ha⟩)
  have hn := card_le_card hcover
  rw [card_univ] at hn
  have hu := (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le (E x) N) O.card)
  have hEx : (E x).card = distEven G x := rfl
  have hNc : N.card = G.degree x := G.card_neighborFinset_eq_degree x
  omega

/-- **Order bound from any vertex.**  Under the hypothesis of Conjecture 189, every vertex `x`
of a connected graph satisfies `4n ≤ 4 (σ(G) + 1) + 4 deg x + (σ(G) + 1)²`, because
`4 s (σ + 1) ≤ (σ + 1)² + 4 s²`. -/
theorem four_mul_card_le [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (x : α) :
    4 * Fintype.card α ≤
      4 * (secondSmallestDegree G + 1) + 4 * G.degree x + (secondSmallestDegree G + 1) ^ 2 := by
  obtain ⟨s, hs⟩ := exists_card_add_mul_self_le G hconn hσ x
  have hde : distEven G x ≤ secondSmallestDegree G + 1 :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ x))).trans (by omega)
  have hsq : 4 * (s * (secondSmallestDegree G + 1)) ≤
      (secondSmallestDegree G + 1) ^ 2 + 4 * (s * s) := by
    zify
    nlinarith [sq_nonneg ((secondSmallestDegree G : ℤ) + 1 - 2 * s)]
  omega

/-- **Order bound.**  Under the hypothesis of Conjecture 189 a connected graph has
`4n ≤ 4 (2σ(G) + 1) + (σ(G) + 1)²`, that is `n ≤ 2σ + 1 + ⌊(σ + 1)² / 4⌋`: apply
`four_mul_card_le` to a vertex of degree `σ(G)`.  This gives `n ≤ 11` for `σ(G) = 3` and
`n ≤ 15` for `σ(G) = 4`. -/
theorem four_mul_card_le_sq [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    4 * Fintype.card α ≤
      4 * (2 * secondSmallestDegree G + 1) + (secondSmallestDegree G + 1) ^ 2 := by
  obtain ⟨x, hx⟩ := exists_degree_eq_secondSmallestDegree G
  have h := four_mul_card_le G hconn hσ x
  rw [hx] at h
  omega

/-- **Search reduction for `σ(G) ≤ 4`.**  A connected graph satisfying the hypothesis of
Conjecture 189 with `σ(G) ≤ 4` has at most `15` vertices, minimum degree at least `n - 11`, at
most four vertices at distance two from any vertex, and at least two vertices of degree at most
four.  These are the facts the computer search for the case `σ(G) ≤ 4` relies on. -/
theorem search_reduction_four [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G)
    (h4 : secondSmallestDegree G ≤ 4) :
    Fintype.card α ≤ 15 ∧ (∀ x, Fintype.card α ≤ G.degree x + 11) ∧
      (∀ v, (Finset.univ.filter fun w => G.dist v w = 2).card ≤ 4) ∧
      2 ≤ (Finset.univ.filter fun w => G.degree w ≤ 4).card := by
  have hsq : (secondSmallestDegree G + 1) ^ 2 ≤ 5 ^ 2 := Nat.pow_le_pow_left (by omega) 2
  refine ⟨?_, fun x => ?_, fun v => (card_dist_eq_two_le G hσ v).trans h4, ?_⟩
  · have h := four_mul_card_le_sq G hconn hσ
    omega
  · have h := four_mul_card_le G hconn hσ x
    omega
  · exact (two_le_card_degree_le G).trans
      (card_le_card fun w hw => by
        simp only [mem_filter, mem_univ, true_and] at hw ⊢; omega)

end Hypothesis

end AgenticConjectures.WowiiGraphConjecture189
