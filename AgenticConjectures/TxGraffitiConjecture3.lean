import Mathlib

/-!
# TxGraffiti Conjecture 3: independent domination versus saturation for regular graphs

*Reference:* [arXiv:2507.17780](https://arxiv.org/abs/2507.17780), Conjecture 3 (TxGraffiti):
every `r`-regular graph `G` with `r ≥ 1` satisfies `i(G) ≤ μ*(G)`, where `i` is the independent
domination number and `μ*` the saturation number (the minimum size of a maximal matching).

## Upstream correspondence

`statement` is the universal closure of `Arxiv.«2507.17780».tx_graffiti_conjecture_3` in
formal-conjectures c094b97 (snapshot: `problems/txgraffiti-conjecture-3/upstream/3.lean`), with the
same binders, the same hypotheses `∀ v, G.degree v = r` and `1 ≤ r`, and the same conclusion.
`statementGeFour` replaces `1 ≤ r` by `4 ≤ r`, and `statementDeg r` fixes the degree.

The definitions are copied term for term from formal-conjectures c094b97 (Apache-2.0),
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/{Domination,Matching,Saturation}.lean`,
with these adaptations:
* they are plain definitions in this namespace (`IsDominating G D` rather than
  `G.IsDominating D`), so they cannot clash with Mathlib or with other modules;
* `IsNIndepDominatingSet` takes `G` explicitly (upstream it is an implicit section variable);
* the upstream attributes, `IsIndepDominating` and `computableSaturationNumber` are not copied,
  since nothing here uses them.

Both invariants are infima over `ℕ`, and `sInf ∅ = 0`. `exists_isNIndepDominatingSet` and
`exists_isMaximalEdgeMatching` show that both sets are nonempty, so the infima are attained.

## Results

* `G48` is the 48-vertex cubic graph of the public release `txgraffiti-order48-successor`, with the
  vertex labels of its `counterexample.g6`. Lean proves `μ*(G48) = 15` (`saturationNumber_G48`,
  from the maximal matching `M48` and the bound `|E| ≤ (2r - 1) μ*`) and checks the independent
  dominating set `D48` of size 16.
* `G48LowerBound` (every independent dominating set of `G48` has at least 16 vertices) is **not
  proved in Lean**. It is certified by a DRAT proof that `drat-trim` checks in CI
  (`problems/txgraffiti-conjecture-3/certificates/`), so the refutations take it as a hypothesis.
* `blowup G t` is `G[K̄_t]`: each vertex is replaced by `t` pairwise non-adjacent twins. It is
  `(t·r)`-regular (`degree_blowup`), with `i(G[K̄_t]) = t·i(G)` (`indepDominationNumber_blowup`)
  and `μ*(G[K̄_t]) ≤ t·μ*(G)` (`saturationNumber_blowup_le`).
* Hence, given `G48LowerBound`, the conjecture fails in every degree divisible by 3
  (`not_statementDeg`). In particular `not_statement` refutes the upstream statement (the known
  cubic case), and `not_statementGeFour` refutes the `r ≥ 4` restriction through the 6-regular
  graph `G48[K̄_2]` on 96 vertices.
-/

namespace AgenticConjectures.TxGraffitiConjecture3

open Finset

section Definitions

variable {α : Type*} [Fintype α] [DecidableEq α]

def IsDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

@[mk_iff]
structure IsNIndepDominatingSet (G : SimpleGraph α) (n : ℕ) (D : Finset α) : Prop where
  isIndep : G.IsIndepSet D
  isDominating : IsDominating G D
  card_eq : D.card = n

noncomputable def indepDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, IsNIndepDominatingSet G n D}

def IsEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ = e₂ ∨ ∀ v : α, ¬ (v ∈ e₁ ∧ v ∈ e₂)

instance (G : SimpleGraph α) [DecidableRel G.Adj] (M : Finset (Sym2 α)) :
    Decidable (IsEdgeMatching G M) := by
  unfold IsEdgeMatching; infer_instance

def IsMaximalEdgeMatching (G : SimpleGraph α) (M : Finset (Sym2 α)) : Prop :=
  IsEdgeMatching G M ∧
    ∀ e ∈ G.edgeSet, e ∉ M → ¬ IsEdgeMatching G (insert e M)

instance (G : SimpleGraph α) [DecidableRel G.Adj] (M : Finset (Sym2 α)) :
    Decidable (IsMaximalEdgeMatching G M) := by
  unfold IsMaximalEdgeMatching; infer_instance

noncomputable def saturationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ M : Finset (Sym2 α), IsMaximalEdgeMatching G M ∧ M.card = n}

end Definitions

section Statements

def statement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), (∀ v, G.degree v = r) → 1 ≤ r →
    indepDominationNumber G ≤ saturationNumber G

def statementGeFour : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), (∀ v, G.degree v = r) → 4 ≤ r →
    indepDominationNumber G ≤ saturationNumber G

def statementDeg (r : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v = r) → indepDominationNumber G ≤ saturationNumber G

theorem statement_iff : statement ↔ ∀ r, 1 ≤ r → statementDeg r :=
  ⟨fun h r hr V _ _ G _ hG => h V G r hG hr, fun h V _ _ G _ r hG hr => h r hr V G hG⟩

theorem statementGeFour_iff : statementGeFour ↔ ∀ r, 4 ≤ r → statementDeg r :=
  ⟨fun h r hr V _ _ G _ hG => h V G r hG hr, fun h V _ _ G _ r hG hr => h r hr V G hG⟩

end Statements

section Matchings

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

omit [Fintype α] in
/-- A matching is maximal iff every edge of `G` has an endpoint covered by it. -/
theorem isMaximalEdgeMatching_iff (M : Finset (Sym2 α)) :
    IsMaximalEdgeMatching G M ↔ IsEdgeMatching G M ∧
      ∀ u v, G.Adj u v → (∃ e ∈ M, u ∈ e) ∨ ∃ e ∈ M, v ∈ e := by
  constructor
  · rintro ⟨hM, hmax⟩
    refine ⟨hM, fun u v huv => ?_⟩
    by_cases hin : s(u, v) ∈ M
    · exact Or.inl ⟨_, hin, Sym2.mem_mk_left u v⟩
    by_contra hcov
    push Not at hcov
    apply hmax s(u, v) huv hin
    refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ => ?_⟩
    · rcases mem_insert.1 he with rfl | he
      · exact huv
      · exact hM.1 e he
    have key : ∀ e ∈ M, ∀ w : α, ¬ (w ∈ s(u, v) ∧ w ∈ e) := by
      rintro e he w ⟨hw, hwe⟩
      rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact hcov.1 e he hwe
      · exact hcov.2 e he hwe
    rcases mem_insert.1 he₁ with rfl | he₁ <;> rcases mem_insert.1 he₂ with rfl | he₂
    · exact Or.inl rfl
    · exact Or.inr (key e₂ he₂)
    · exact Or.inr fun w hw => key e₁ he₁ w ⟨hw.2, hw.1⟩
    · exact hM.2 e₁ he₁ e₂ he₂
  · rintro ⟨hM, hcov⟩
    refine ⟨hM, fun e he hnot hmat => ?_⟩
    induction e using Sym2.ind with
    | h u v =>
      have huv : G.Adj u v := he
      have hcases : ∃ e' ∈ M, ∃ w, w ∈ s(u, v) ∧ w ∈ e' := by
        rcases hcov u v huv with ⟨e', he', hu⟩ | ⟨e', he', hv⟩
        · exact ⟨e', he', u, Sym2.mem_mk_left u v, hu⟩
        · exact ⟨e', he', v, Sym2.mem_mk_right u v, hv⟩
      obtain ⟨e', he', w, hw, hw'⟩ := hcases
      rcases hmat.2 _ (mem_insert_self _ _) e' (mem_insert_of_mem he') with h | h
      · exact hnot (h ▸ he')
      · exact h w ⟨hw, hw'⟩

/-- Every finite graph has a maximal matching (a matching of maximum cardinality). -/
theorem exists_isMaximalEdgeMatching [DecidableRel G.Adj] :
    ∃ M : Finset (Sym2 α), IsMaximalEdgeMatching G M := by
  obtain ⟨M, hM, hmax⟩ := (G.edgeFinset.powerset.filter (IsEdgeMatching G)).exists_max_image
    Finset.card ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp [IsEdgeMatching]⟩⟩
  rw [mem_filter, mem_powerset] at hM
  refine ⟨M, hM.2, fun e he hnot hmat => ?_⟩
  have := hmax (insert e M) (mem_filter.2 ⟨mem_powerset.2 (insert_subset
    (SimpleGraph.mem_edgeFinset.2 he) hM.1), hmat⟩)
  rw [card_insert_of_notMem hnot] at this
  omega

/-- If every vertex has degree at most `r` (with `r ≥ 1`), every maximal matching `M`
satisfies `|E(G)| ≤ (2r - 1) |M|`. -/
theorem card_edgeFinset_le_of_isMaximalEdgeMatching [DecidableRel G.Adj] {r : ℕ} (hr : 1 ≤ r)
    (hdeg : ∀ v, G.degree v ≤ r) {M : Finset (Sym2 α)} (hM : IsMaximalEdgeMatching G M) :
    G.edgeFinset.card ≤ (2 * r - 1) * M.card := by
  rw [isMaximalEdgeMatching_iff] at hM
  obtain ⟨hM, hcov⟩ := hM
  -- each edge meets an edge of `M`
  let near : Sym2 α → Finset (Sym2 α) := fun e => G.edgeFinset.filter fun f => ∃ w ∈ e, w ∈ f
  have hsub : G.edgeFinset ⊆ M.biUnion near := by
    intro f hf
    induction f using Sym2.ind with
    | h u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.1 hf
      rw [mem_biUnion]
      rcases hcov u v huv with ⟨e, he, hu⟩ | ⟨e, he, hv⟩
      · exact ⟨e, he, mem_filter.2 ⟨hf, u, hu, Sym2.mem_mk_left u v⟩⟩
      · exact ⟨e, he, mem_filter.2 ⟨hf, v, hv, Sym2.mem_mk_right u v⟩⟩
  have hnear : ∀ e ∈ M, (near e).card ≤ 2 * r - 1 := by
    intro e he
    have heG : e ∈ G.edgeSet := hM.1 e he
    induction e using Sym2.ind with
    | h u v =>
      have huv : G.Adj u v := heG
      have hsub' : near s(u, v) ⊆ G.incidenceFinset u ∪ G.incidenceFinset v := by
        intro f hf
        obtain ⟨hfE, w, hw, hwf⟩ := mem_filter.1 hf
        have hfE' : f ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.1 hfE
        rcases Sym2.mem_iff.1 hw with rfl | rfl
        · exact mem_union_left _ ((G.mem_incidenceFinset _ _).2 ⟨hfE', hwf⟩)
        · exact mem_union_right _ ((G.mem_incidenceFinset _ _).2 ⟨hfE', hwf⟩)
      have hinter : s(u, v) ∈ G.incidenceFinset u ∩ G.incidenceFinset v :=
        mem_inter.2 ⟨(G.mem_incidenceFinset _ _).2 ⟨huv, Sym2.mem_mk_left u v⟩,
          (G.mem_incidenceFinset _ _).2 ⟨huv, Sym2.mem_mk_right u v⟩⟩
      have h1 := card_union_add_card_inter (G.incidenceFinset u) (G.incidenceFinset v)
      have h2 : 1 ≤ (G.incidenceFinset u ∩ G.incidenceFinset v).card :=
        card_pos.2 ⟨_, hinter⟩
      rw [G.card_incidenceFinset_eq_degree, G.card_incidenceFinset_eq_degree] at h1
      have := card_le_card hsub'
      have := hdeg u
      have := hdeg v
      omega
  calc G.edgeFinset.card ≤ (M.biUnion near).card := card_le_card hsub
    _ ≤ ∑ e ∈ M, (near e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ M, (2 * r - 1) := sum_le_sum hnear
    _ = (2 * r - 1) * M.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- The bound `|E(G)| ≤ (2r - 1) μ*(G)` for graphs of maximum degree at most `r ≥ 1`. -/
theorem card_edgeFinset_le_mul_saturationNumber [DecidableRel G.Adj] {r : ℕ} (hr : 1 ≤ r)
    (hdeg : ∀ v, G.degree v ≤ r) :
    G.edgeFinset.card ≤ (2 * r - 1) * saturationNumber G := by
  obtain ⟨M, hM⟩ := exists_isMaximalEdgeMatching G
  obtain ⟨M', hM', hcard⟩ : saturationNumber G ∈
      {n | ∃ M : Finset (Sym2 α), IsMaximalEdgeMatching G M ∧ M.card = n} :=
    Nat.sInf_mem ⟨_, M, hM, rfl⟩
  rw [← hcard]
  exact card_edgeFinset_le_of_isMaximalEdgeMatching G hr hdeg hM'

end Matchings

section IndepDomination

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)

/-- Every finite graph has an independent dominating set (an independent set of maximum
cardinality). -/
theorem exists_isNIndepDominatingSet [DecidableRel G.Adj] :
    ∃ n, ∃ D : Finset α, IsNIndepDominatingSet G n D := by
  obtain ⟨S, hS, hmax⟩ := (univ.powerset.filter fun S : Finset α =>
    ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v).exists_max_image Finset.card
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  have hI : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v := (mem_filter.1 hS).2
  refine ⟨S.card, S, fun u hu v hv _ => hI u hu v hv, fun v => ?_, rfl⟩
  by_contra hv
  simp only [not_or, not_exists, not_and, Finset.mem_coe] at hv
  have hins : insert v S ∈ univ.powerset.filter fun S : Finset α =>
      ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v := by
    refine mem_filter.2 ⟨mem_powerset.2 (subset_univ _), ?_⟩
    intro a ha b hb hab
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact G.irrefl hab
      · exact hv.2 b hb hab
    · rcases hb with rfl | hb
      · exact hv.2 a ha hab.symm
      · exact hI a ha b hb hab
  have := hmax _ hins
  rw [card_insert_of_notMem hv.1] at this
  omega

end IndepDomination

section Blowup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The lexicographic product `G[K̄_t]`: every vertex of `G` is replaced by `t` pairwise
non-adjacent twins, and two copies are adjacent iff the original vertices are. -/
def blowup (G : SimpleGraph V) (t : ℕ) : SimpleGraph (V × Fin t) where
  Adj p q := G.Adj p.1 q.1
  symm _ _ h := G.symm h
  loopless := ⟨fun _ h => G.irrefl h⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : DecidableRel (blowup G t).Adj :=
  fun p q => inferInstanceAs (Decidable (G.Adj p.1 q.1))

variable {G : SimpleGraph V} {t : ℕ}

omit [Fintype V] [DecidableEq V] in
@[simp] theorem blowup_adj {p q : V × Fin t} : (blowup G t).Adj p q ↔ G.Adj p.1 q.1 := Iff.rfl

omit [DecidableEq V] in
/-- `G[K̄_t]` is `(t · r)`-regular when `G` is `r`-regular. -/
theorem degree_blowup [DecidableRel G.Adj] (p : V × Fin t) :
    (blowup G t).degree p = G.degree p.1 * t := by
  have h : (blowup G t).neighborFinset p = G.neighborFinset p.1 ×ˢ univ := by
    ext q; simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, h, card_product,
    SimpleGraph.card_neighborFinset_eq_degree, card_univ, Fintype.card_fin]

omit [Fintype V] in
/-- Twins force full fibres: an independent dominating set `D` of `G[K̄_t]` (`t > 0`) is
`S ×ˢ univ` for the independent dominating set `S = D.image Prod.fst` of `G`. -/
theorem isNIndepDominatingSet_of_blowup (ht : 0 < t) {n : ℕ} {D : Finset (V × Fin t)}
    (hD : IsNIndepDominatingSet (blowup G t) n D) :
    IsNIndepDominatingSet G (D.image Prod.fst).card (D.image Prod.fst) ∧
      n = (D.image Prod.fst).card * t := by
  obtain ⟨hI, hDom, hcard⟩ := hD
  have hfull : D = D.image Prod.fst ×ˢ univ := by
    ext ⟨v, a⟩
    simp only [mem_product, mem_image, mem_univ, and_true]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨⟨w, b⟩, hwb, rfl⟩
    rcases hDom (w, a) with h | ⟨q, hq, hadj⟩
    · exact h
    · have hadj' : G.Adj w q.1 := hadj
      exact absurd hadj' (hI hwb hq fun h => G.ne_of_adj hadj' (congrArg Prod.fst h))
  refine ⟨⟨?_, ?_, rfl⟩, ?_⟩
  · rintro u hu v hv huv hadj
    obtain ⟨⟨u, a⟩, hua, rfl⟩ := mem_image.1 (Finset.mem_coe.1 hu)
    obtain ⟨⟨v, b⟩, hvb, rfl⟩ := mem_image.1 (Finset.mem_coe.1 hv)
    exact hI hua hvb (fun h => huv (congrArg Prod.fst h)) hadj
  · intro v
    rcases hDom (v, ⟨0, ht⟩) with h | ⟨q, hq, hadj⟩
    · exact Or.inl (Finset.mem_coe.2 (mem_image_of_mem Prod.fst h))
    · exact Or.inr ⟨q.1, Finset.mem_coe.2 (mem_image_of_mem Prod.fst hq), hadj⟩
  · rw [← hcard]
    conv_lhs => rw [hfull]
    rw [card_product, card_univ, Fintype.card_fin]

omit [Fintype V] [DecidableEq V] in
/-- Conversely, `S ×ˢ univ` is an independent dominating set of `G[K̄_t]` for every independent
dominating set `S` of `G`. -/
theorem isNIndepDominatingSet_blowup {n : ℕ} {S : Finset V}
    (hS : IsNIndepDominatingSet G n S) :
    IsNIndepDominatingSet (blowup G t) (n * t) (S ×ˢ (univ : Finset (Fin t))) := by
  obtain ⟨hI, hDom, hcard⟩ := hS
  refine ⟨?_, ?_, by rw [card_product, card_univ, Fintype.card_fin, hcard]⟩
  · rintro ⟨u, a⟩ hu ⟨v, b⟩ hv _ hadj
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hu hv
    exact hI (Finset.mem_coe.2 hu.1) (Finset.mem_coe.2 hv.1) (G.ne_of_adj hadj) hadj
  · rintro ⟨v, a⟩
    rcases hDom v with h | ⟨w, hw, hadj⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr ⟨(w, a), by simpa using hw, hadj⟩

/-- `i(G[K̄_t]) = t · i(G)` for `t > 0`. -/
theorem indepDominationNumber_blowup [DecidableRel G.Adj] (ht : 0 < t) :
    indepDominationNumber (blowup G t) = indepDominationNumber G * t := by
  obtain ⟨n₀, D₀, hD₀⟩ := exists_isNIndepDominatingSet G
  obtain ⟨S, hS⟩ : indepDominationNumber G ∈ {n | ∃ D : Finset V, IsNIndepDominatingSet G n D} :=
    Nat.sInf_mem ⟨n₀, D₀, hD₀⟩
  apply le_antisymm
  · exact Nat.sInf_le ⟨_, isNIndepDominatingSet_blowup hS⟩
  · refine le_csInf ⟨_, _, isNIndepDominatingSet_blowup (t := t) hS⟩ ?_
    rintro n ⟨D, hD⟩
    obtain ⟨hS', rfl⟩ := isNIndepDominatingSet_of_blowup ht hD
    exact Nat.mul_le_mul_right t (Nat.sInf_le ⟨_, hS'⟩)

/-- The blow-up `{e.map (·, a) | e ∈ M, a : Fin t}` of a set of edges. -/
def blowupMatching (M : Finset (Sym2 V)) (t : ℕ) : Finset (Sym2 (V × Fin t)) :=
  (M ×ˢ univ).image fun x => x.1.map fun v => (v, x.2)

omit [Fintype V] in
theorem card_blowupMatching (M : Finset (Sym2 V)) :
    (blowupMatching M t).card = M.card * t := by
  rw [blowupMatching, card_image_of_injective, card_product, card_univ, Fintype.card_fin]
  rintro ⟨e, a⟩ ⟨f, b⟩ h
  simp only at h
  have hab : a = b := by
    induction e using Sym2.ind with
    | h x y =>
      have hx : (x, a) ∈ f.map fun v => (v, b) := h ▸ Sym2.mem_map.2 ⟨x, Sym2.mem_mk_left x y, rfl⟩
      obtain ⟨_, _, hz⟩ := Sym2.mem_map.1 hx
      exact (congrArg Prod.snd hz).symm
  subst hab
  have hinj : Function.Injective fun v : V => (v, a) := fun _ _ h => congrArg Prod.fst h
  rw [Sym2.map.injective hinj h]

/-- The blow-up of a maximal matching of `G` is a maximal matching of `G[K̄_t]`. -/
theorem isMaximalEdgeMatching_blowupMatching {M : Finset (Sym2 V)}
    (hM : IsMaximalEdgeMatching G M) : IsMaximalEdgeMatching (blowup G t) (blowupMatching M t) := by
  rw [isMaximalEdgeMatching_iff] at hM ⊢
  obtain ⟨⟨hE, hdisj⟩, hcov⟩ := hM
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e' he'
    obtain ⟨⟨e, a⟩, he, rfl⟩ := mem_image.1 he'
    have heG := hE e (mem_product.1 he).1
    induction e using Sym2.ind with
    | h x y => simpa [Sym2.map_mk] using heG
  · intro e₁' he₁' e₂' he₂'
    obtain ⟨⟨e₁, a⟩, he₁, rfl⟩ := mem_image.1 he₁'
    obtain ⟨⟨e₂, b⟩, he₂, rfl⟩ := mem_image.1 he₂'
    by_cases hcommon : ∃ w : V × Fin t, w ∈ e₁.map (fun v => (v, a)) ∧ w ∈ e₂.map (fun v => (v, b))
    · obtain ⟨w, hw₁, hw₂⟩ := hcommon
      obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.1 hw₁
      obtain ⟨y, hy, hxy⟩ := Sym2.mem_map.1 hw₂
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hxy
      rcases hdisj e₁ (mem_product.1 he₁).1 e₂ (mem_product.1 he₂).1 with h | h
      · exact Or.inl (by rw [h])
      · exact absurd ⟨hx, hy⟩ (h y)
    · push Not at hcommon
      exact Or.inr fun w hw => hcommon w hw.1 hw.2
  · rintro ⟨u, a⟩ ⟨v, b⟩ hadj
    have hmem : ∀ (x : V) (c : Fin t) (e : Sym2 V), e ∈ M → x ∈ e →
        ∃ e' ∈ blowupMatching M t, (x, c) ∈ e' := fun x c e he hx =>
      ⟨e.map fun v => (v, c), mem_image.2 ⟨(e, c), mem_product.2 ⟨he, mem_univ _⟩, rfl⟩,
        Sym2.mem_map.2 ⟨x, hx, rfl⟩⟩
    rcases hcov u v hadj with ⟨e, he, hu⟩ | ⟨e, he, hv⟩
    · exact Or.inl (hmem u a e he hu)
    · exact Or.inr (hmem v b e he hv)

/-- `μ*(G[K̄_t]) ≤ t · μ*(G)`. -/
theorem saturationNumber_blowup_le [DecidableRel G.Adj] :
    saturationNumber (blowup G t) ≤ saturationNumber G * t := by
  obtain ⟨M₀, hM₀⟩ := exists_isMaximalEdgeMatching G
  obtain ⟨M, hM, hcard⟩ : saturationNumber G ∈
      {n | ∃ M : Finset (Sym2 V), IsMaximalEdgeMatching G M ∧ M.card = n} :=
    Nat.sInf_mem ⟨_, M₀, hM₀, rfl⟩
  rw [← hcard, ← card_blowupMatching]
  exact Nat.sInf_le ⟨_, isMaximalEdgeMatching_blowupMatching hM, rfl⟩

end Blowup

section G48

/-- Neighbour lists of a 48-vertex cubic graph with `i = 16 > 15 = μ*`: the graph of
`counterexample.g6` in the public release `txgraffiti-order48-successor`, with the same vertex
labels. The edges `{0,1}, {2,3}, …, {28,29}` form a maximal matching. -/
def nbrs48 : List (List ℕ) :=
  [[1, 31, 40], [0, 32, 39], [3, 25, 46], [2, 36, 44], [5, 38, 42], [4, 6, 43], [5, 7, 42],
   [6, 35, 38], [9, 13, 32], [8, 35, 38], [11, 43, 47], [10, 34, 37], [13, 32, 35], [8, 12, 39],
   [15, 44, 46], [14, 33, 37], [17, 40, 41], [16, 31, 36], [19, 41, 45], [18, 40, 44],
   [21, 31, 39], [20, 34, 47], [23, 36, 41], [22, 30, 45], [25, 30, 33], [2, 24, 45],
   [27, 37, 46], [26, 30, 34], [29, 42, 43], [28, 33, 47], [23, 24, 27], [0, 17, 20],
   [1, 8, 12], [15, 24, 29], [11, 21, 27], [7, 9, 12], [3, 17, 22], [11, 15, 26], [4, 7, 9],
   [1, 13, 20], [0, 16, 19], [16, 18, 22], [4, 6, 28], [5, 10, 28], [3, 14, 19], [18, 23, 25],
   [2, 14, 26], [10, 21, 29]]

/-- Adjacency of `G48`, read off `nbrs48`. -/
def adj48 (u v : Fin 48) : Bool := (nbrs48.getD u.val []).contains v.val

theorem adj48_symm : ∀ u v : Fin 48, adj48 u v = true → adj48 v u = true := by decide

theorem adj48_irrefl : ∀ u : Fin 48, adj48 u u = false := by decide

/-- The 48-vertex cubic counterexample. -/
def G48 : SimpleGraph (Fin 48) where
  Adj u v := adj48 u v = true
  symm u v h := adj48_symm u v h
  loopless := ⟨fun u h => by rw [adj48_irrefl u] at h; exact Bool.false_ne_true h⟩

instance : DecidableRel G48.Adj := fun u v => inferInstanceAs (Decidable (adj48 u v = true))

set_option maxRecDepth 100000 in
theorem G48_degree : ∀ v : Fin 48, G48.degree v = 3 := by decide

theorem card_edgeFinset_G48 : G48.edgeFinset.card = 72 := by
  have h := G48.sum_degrees_eq_twice_card_edges
  simp only [G48_degree, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

/-- The variable edges `{0,1}, {2,3}, …, {28,29}`. -/
def M48 : Finset (Sym2 (Fin 48)) :=
  {s(0, 1), s(2, 3), s(4, 5), s(6, 7), s(8, 9), s(10, 11), s(12, 13), s(14, 15), s(16, 17),
   s(18, 19), s(20, 21), s(22, 23), s(24, 25), s(26, 27), s(28, 29)}

theorem card_M48 : M48.card = 15 := by decide

set_option maxRecDepth 100000 in
theorem isMaximalEdgeMatching_M48 : IsMaximalEdgeMatching G48 M48 := by
  rw [isMaximalEdgeMatching_iff]
  exact ⟨by decide, by decide⟩

/-- `μ*(G48) = 15`: `M48` is a maximal matching, and `|E| = 72 ≤ 5 μ*`. -/
theorem saturationNumber_G48 : saturationNumber G48 = 15 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨M48, isMaximalEdgeMatching_M48, card_M48⟩
  · have h := card_edgeFinset_le_mul_saturationNumber G48 (r := 3) (by norm_num)
      fun v => (G48_degree v).le
    rw [card_edgeFinset_G48] at h
    omega

/-- An independent dominating set of `G48` with 16 vertices. -/
def D48 : Finset (Fin 48) := {0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 34}

set_option maxRecDepth 100000 in
theorem isNIndepDominatingSet_D48 : IsNIndepDominatingSet G48 16 D48 := by
  have hI : ∀ u ∈ D48, ∀ v ∈ D48, ¬ G48.Adj u v := by decide
  have hD : ∀ v : Fin 48, v ∈ D48 ∨ ∃ w ∈ D48, G48.Adj v w := by decide
  exact ⟨fun u hu v hv _ => hI u hu v hv, hD, by decide⟩

/-- The lower bound `i(G48) ≥ 16`. It is not proved in Lean: it is the statement certified by
the DRAT proof shipped with this problem (`certificates/`), whose CNF encodes "an independent
dominating set of `G48` with at most 15 vertices". -/
def G48LowerBound : Prop :=
  ∀ D : Finset (Fin 48), G48.IsIndepSet D → IsDominating G48 D → 16 ≤ D.card

theorem indepDominationNumber_G48 (h : G48LowerBound) : indepDominationNumber G48 = 16 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨D48, isNIndepDominatingSet_D48⟩
  · refine le_csInf ⟨16, D48, isNIndepDominatingSet_D48⟩ ?_
    rintro n ⟨D, hI, hD, rfl⟩
    exact h D hI hD

end G48

section Refutation

/-- Given `i(G48) ≥ 16`, the blow-up `G48[K̄_t]` is a `3t`-regular graph with
`i = 16 t > 15 t ≥ μ*`. -/
theorem not_statementDeg (h : G48LowerBound) {r : ℕ} (hr : 3 ∣ r) (hr0 : 0 < r) :
    ¬ statementDeg r := by
  obtain ⟨t, rfl⟩ := hr
  have ht : 0 < t := by omega
  intro hs
  have hreg : ∀ p, (blowup G48 t).degree p = 3 * t := fun p => by
    rw [degree_blowup, G48_degree]
  have hle := hs (Fin 48 × Fin t) (blowup G48 t) hreg
  rw [indepDominationNumber_blowup ht, indepDominationNumber_G48 h] at hle
  have hmu := saturationNumber_blowup_le (G := G48) (t := t)
  rw [saturationNumber_G48] at hmu
  have : 16 * t ≤ 15 * t := hle.trans hmu
  omega

/-- TxGraffiti Conjecture 3 fails (cubic case, `G48`), given the DRAT-certified `i(G48) ≥ 16`. -/
theorem not_statement (h : G48LowerBound) : ¬ statement := fun hs =>
  not_statementDeg h (r := 3) ⟨1, rfl⟩ (by norm_num) (statement_iff.1 hs 3 (by norm_num))

/-- The restriction to `r ≥ 4` fails too: `G48[K̄_2]` is a 6-regular graph on 96 vertices with
`i = 32 > 30 ≥ μ*` (given the DRAT-certified `i(G48) ≥ 16`). -/
theorem not_statementGeFour (h : G48LowerBound) : ¬ statementGeFour := fun hs =>
  not_statementDeg h (r := 6) ⟨2, rfl⟩ (by norm_num) (statementGeFour_iff.1 hs 6 (by norm_num))

end Refutation

end AgenticConjectures.TxGraffitiConjecture3
