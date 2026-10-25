import AgenticConjectures.CrimHookStacks

/-!
# CRIM: melds of losing thick hooks, parity self-conjugate partitions, and misère play

Source: Ina Bašić, Eric Gottlieb, Matjaž Krnc, *CRIM: A Natural Game on Integer Partitions*,
arXiv:2606.16828v1 (2026). Two conjectures from the paper's §5 (Future Work), both stated here by
us (there is no Formal Conjectures statement):

* the thick-hook meld conjecture: "A meld of losing thick hooks is losing";
* `conj:pself`: "A parity self-conjugate partition is in N if and only if it is the stack of
  odd self-conjugate hooks and [1]".

It also classifies the misère P-positions (`misereP_iff`). We found no prior statement of this
classification; the paper asks only about misère-related Conway pairs. Finally, it states the
paper's `conj:hookswap` for nonempty partitions and proves one direction; the other is open.

Both are corollaries of Zijian Zeng's boundary-word classification of the CRIM P-positions
(an unrefereed 2026 preprint), formalized as `isP_ofPairs_iff` in `CrimHookStacks`; this module
reuses that file's definitions (`IsPartition`, `part`, `IsP`, `stack`, `hook`, `ofPairs`).

## Readings (checked against the TeX)

* `meld μ lam` is the paper's meld `μ ◇ λ = [μ₁ + λ₁, …, μ₁ + λ_m, μ₁, …, μ_k]` (§2.1).
  It is associative with unit `[]` (`meld_assoc`, `meld_nil_left`, `meld_nil_right`).
* `thickHook r c a b = [c^a, b^{r-a}] = Γ^{a,b}_{r,c}` with the paper's side conditions
  `r > a ≥ 2` and `c > b ≥ 2` (`ThickParams`, §2.2); "losing" means P-position (`IsP`).
* "A meld of losing thick hooks" is any member of `Melds S` for `S t := IsThickHook t ∧ IsP t`:
  the closure of `S` under the binary meld, in any bracketing, together with the empty meld
  `[]` (which is P). By associativity this is the set of right-nested melds
  `H₁ ◇ (H₂ ◇ (⋯ ◇ Hₙ))` of lists of losing thick hooks, `n ≥ 0` (`melds_iff`).
* `ParitySelfConj l`: `λ_k ≡ λ'_k (mod 2)` for every `k ≥ 1`, where `λ'_k = conjPart l k` is
  the number of parts `≥ k`, and parts past the end are `0` on both sides.
* "Odd self-conjugate hooks" are the hooks `Γ_{r,r} = hook r r` with `r` odd (`Γ_{r,c}` has
  conjugate `Γ_{c,r}`; "odd hooks" in the paper's Observation have an odd number of rows and of
  columns). "The stack of odd self-conjugate hooks and `[1]`" is read as
  `Γ_{r₁,r₁} ◁ (Γ_{r₂,r₂} ◁ (⋯ ◁ (Γ_{r_j,r_j} ◁ [1])))` with `j ≥ 0` and every `r_i` odd,
  where `◁` is the general Durfee-length stack `stack` of `CrimHookStacks` and every
  intermediate stack must be defined (`OddHookStack`; `j = 0` gives `[1]`). The paper writes
  such stacks without brackets ("the stack operation is associative") and puts `[1]` last
  ("a stack of odd hooks, with last hook being `[1]`"). Every other bracketing gives the same
  partitions, with the same intermediate stacks defined (`exists_hookTree_iff`).
* Misère play: "a player who reaches a terminal position wins" (§2), that is, the player to
  move at `[]` wins, so `[]` is a misère N-position. `IsMP` is defined by the recursion of `IsP`
  with `[]` excluded (`isMP_iff`).
* Conway pairs (§2): `cp(λ) = (sg(λ), G⁻(λ))`, where the misère Grundy value `G⁻` is the mex of
  the options' values, and `1` at the terminal position `[]`. Conway pair `(0, 1)` is
  `IsP l ∧ IsMV1 l` (`isMV1_iff`). The paper's own `cp([]) = (0, 1)` makes `conj:hookswap`
  fail at `[]` as written, so `hookswapConjecture` is the nonempty version (`nil_conwayPair`).
  An even-by-even hook is `hook r c` with `r, c ≥ 2` even (`EEHook`).

## Results

* `meldConjecture_holds`: every meld of losing thick hooks is a P-position.
  `isP_meldAll` is the same for right-nested melds of a list.
* `isP_thickHook_iff`: a thick hook is a P-position iff `r ≡ c (mod 2)` (the P-part of the
  paper's `thm:thick-hook`).
* `pselfConjecture_holds`: conj:pself. `paritySelfConj_and_not_isP_iff` is the slightly
  stronger form "`λ` is parity self-conjugate and in N iff `λ` is such a stack" (so every such
  stack is parity self-conjugate, in fact self-conjugate).
* `oddHookStack_iff`: the stacks are exactly the partitions with run pairs
  `[(1, o₁), …, (1, o_j), (1, 1), (o_j, 1), …, (o₁, 1)]` with every `o_i` odd.
* `pselfConjecture_anyBracketing`: conj:pself with the stack bracketed in any way. It rests on
  `stack_hook_assoc`: `(Γ_{r,c} ◁ μ) ◁ ν = Γ_{r,c} ◁ (μ ◁ ν)` for a nonempty partition `μ`,
  with either side defined iff the other is.
* `misereP_iff`: `ofPairs p` is a misère P-position iff exactly one of Zeng's normal-play
  condition (`plen p` and `endM p` even) and the cover condition `k ≤ L + R` holds;
  `misereP_iff_isP` is the same with `IsP (ofPairs p)` for Zeng's condition.
* `hookswapConjecture` is stated but not proved. `conwayPair_of_eeHook` proves its `(⇐)`
  direction from `misere_hook` (the misère part of the paper's `thm:cgpairshooks`),
  `hookswapConjecture_iff` reduces it to its `(⇒)` direction, and `covered_of_conwayPair`
  shows that Conway pair `(0, 1)` forces `k ≤ L + R` with `k` even.

## Proof idea

By `isP_ofPairs_iff`, `λ = ofPairs p` is P iff `plen p = ℓ(λ) + λ₁` and `endM p` are both even.
A meld is concatenation of run pairs (`meld_ofPairs`); a thick hook has run pairs
`[(a, c - b), (r - a, b)]` with `a, b ≥ 2`, so in a meld of thick hooks the first pair is not
A-good and the last is not B-good, whence `endM = 0`, while `plen` adds up.

For conj:pself, `λ'_k` is `part (ofPairs (pdual p)) k` (`countP_ofPairs`), so parity
self-conjugacy says that `λ` and `λ'` have the same parity sequence. `endL p` is the number of
leading rows whose drop `λ_i - λ_{i+1}` is odd (`endL_drops`), so
`endL p = endL (pdual p) = endR p`, and `plen p` is even. If `λ` is in N, then `endM p` is odd,
which forces `endL p + endR p ≥ k`. Then every run pair is A-good or B-good, all run-pair
entries are odd, and the parity sequences determine the `a`-entries, so `pdual p = p`. Peeling
the first and last pairs then gives the pairs above, which are exactly the run pairs of the
stacks (`stack_hook`).

For misère play, call `p` covered if `k ≤ L + R`. A covered position has even `plen`, and a move
between positions of even `plen` peels an end pair, so it lowers both `endM` and `k` by one: it
flips Zeng's condition and keeps coverage. Hence no move stays inside `Z xor C`, and from a
position of even `plen` outside it, peeling a good end pair enters it. From a position of odd
`plen`, the move is the one of Zeng's proof of the classification (`RunPairs.goodMove_of_odd`),
changed in three cases (`mgood_of_odd`).

The arguments follow routes found by an earlier scouting run of this project, which also found
the misère hypothesis; its Lean draft of the meld argument supplied `meld`, `thickHook`,
`ThickParams`, `thickPairs` and `meld_ofPairs`. The classification is Zeng's.
-/

namespace AgenticConjectures.CrimPselfMeld

open AgenticConjectures.CrimHookStacks

/-! ## Melds -/

/-- The meld `μ ◇ λ = [μ₁ + λ₁, …, μ₁ + λ_m, μ₁, …, μ_k]` (arXiv:2606.16828, §2.1). -/
def meld (μ lam : List ℕ) : List ℕ := lam.map (· + part μ 1) ++ μ

theorem part_one_meld (μ lam : List ℕ) : part (meld μ lam) 1 = part lam 1 + part μ 1 := by
  cases lam with
  | nil => simp [meld, part_one_nil]
  | cons x t => rfl

theorem meld_nil_left (lam : List ℕ) : meld [] lam = lam := by
  simp [meld, part_one_nil]

theorem meld_nil_right (μ : List ℕ) : meld μ [] = μ := rfl

/-- The meld is associative (the paper's remark after the definition). -/
theorem meld_assoc (μ ν lam : List ℕ) : meld (meld μ ν) lam = meld μ (meld ν lam) := by
  rw [show meld (meld μ ν) lam = lam.map (· + part (meld μ ν) 1) ++ meld μ ν from rfl,
    part_one_meld]
  simp only [meld, List.map_append, List.map_map, List.append_assoc]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  omega

/-- The right-nested meld `H₁ ◇ (H₂ ◇ (⋯ ◇ Hₙ))` of a list, `[]` for the empty list. -/
def meldAll (hs : List (List ℕ)) : List ℕ := hs.foldr meld []

theorem meldAll_append (xs ys : List (List ℕ)) :
    meldAll (xs ++ ys) = meld (meldAll xs) (meldAll ys) := by
  induction xs with
  | nil => simp [meldAll, meld_nil_left]
  | cons x xs ih =>
    simp only [meldAll, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, meld_assoc]

/-- The melds of members of `S`: any number of them (the empty meld is `[]`), in any
bracketing. -/
inductive Melds (S : List ℕ → Prop) : List ℕ → Prop
  | nil : Melds S []
  | piece {l : List ℕ} : S l → Melds S l
  | join {μ lam : List ℕ} : Melds S μ → Melds S lam → Melds S (meld μ lam)

/-- By associativity, the bracketing does not matter: `Melds S` is the set of right-nested
melds of finite lists of members of `S`. -/
theorem melds_iff {S : List ℕ → Prop} {l : List ℕ} :
    Melds S l ↔ ∃ hs : List (List ℕ), (∀ h ∈ hs, S h) ∧ meldAll hs = l := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], by simp, rfl⟩
    | @piece l hl => exact ⟨[l], by simpa using hl, meld_nil_right l⟩
    | join _ _ ih1 ih2 =>
      obtain ⟨xs, hxs, rfl⟩ := ih1
      obtain ⟨ys, hys, rfl⟩ := ih2
      refine ⟨xs ++ ys, fun h hh => ?_, meldAll_append xs ys⟩
      rcases List.mem_append.1 hh with hh | hh
      · exact hxs h hh
      · exact hys h hh
  · rintro ⟨hs, hhs, rfl⟩
    induction hs with
    | nil => exact Melds.nil
    | cons x xs ih =>
      exact Melds.join (Melds.piece (hhs x (by simp)))
        (ih fun h hh => hhs h (List.mem_cons_of_mem _ hh))

/-! ## Thick hooks -/

/-- The thick hook `Γ^{a,b}_{r,c} = [c^a, b^{r-a}]` (arXiv:2606.16828, §2.2). -/
def thickHook (r c a b : ℕ) : List ℕ := List.replicate a c ++ List.replicate (r - a) b

/-- The paper's side conditions on a thick hook: `r > a ≥ 2` and `c > b ≥ 2`. -/
def ThickParams (r c a b : ℕ) : Prop := a < r ∧ 2 ≤ a ∧ b < c ∧ 2 ≤ b

/-- `l` is a thick hook. -/
def IsThickHook (l : List ℕ) : Prop := ∃ r c a b, ThickParams r c a b ∧ thickHook r c a b = l

/-- **The thick-hook meld conjecture**: every meld of losing thick hooks is losing. -/
def meldConjecture : Prop := ∀ l : List ℕ, Melds (fun t => IsThickHook t ∧ IsP t) l → IsP l

/-- Run pairs of a thick hook. -/
def thickPairs (r c a b : ℕ) : List (ℕ × ℕ) := [(a, c - b), (r - a, b)]

theorem meld_ofPairs {A B : List (ℕ × ℕ)} (hB : ValidPairs B) :
    meld (ofPairs B) (ofPairs A) = ofPairs (A ++ B) := by
  rw [meld, ofPairs_append, part_one_ofPairs hB]

theorem validPairs_thickPairs {r c a b : ℕ} (h : ThickParams r c a b) :
    ValidPairs (thickPairs r c a b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  intro x hx
  simp only [thickPairs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> constructor <;> dsimp only <;> omega

theorem ofPairs_thickPairs {r c a b : ℕ} (h : ThickParams r c a b) :
    ofPairs (thickPairs r c a b) = thickHook r c a b := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [thickPairs, ofPairs_cons, ofPairs_cons, ofPairs_nil, thickHook]
  simp only [pairsBSum_cons, pairsBSum_nil, List.append_nil]
  rw [show c - b + (b + 0) = c by omega, show b + 0 = b by omega]

theorem plen_thickPairs {r c a b : ℕ} (h : ThickParams r c a b) :
    plen (thickPairs r c a b) = r + c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [thickPairs, plen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem endL_thickPairs {r c a b : ℕ} (h : ThickParams r c a b) :
    endL (thickPairs r c a b) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hA : AGood (a, c - b) = false := RunPairs.not_aGood_of (Or.inl (by dsimp only; omega))
  rw [thickPairs, RunPairs.endL_cons, if_neg (by simp [hA])]

theorem endR_thickPairs {r c a b : ℕ} (h : ThickParams r c a b) :
    endR (thickPairs r c a b) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hB : BGood (r - a, b) = false := RunPairs.not_bGood_of (Or.inr (by dsimp only; omega))
  rw [thickPairs, show [(a, c - b), (r - a, b)] = [(a, c - b)] ++ [(r - a, b)] from rfl,
    RunPairs.endR_append_single, if_neg (by simp [hB])]

/-- The P-part of the paper's `thm:thick-hook`: a thick hook is losing iff `r ≡ c (mod 2)`. -/
theorem isP_thickHook_iff {r c a b : ℕ} (h : ThickParams r c a b) :
    IsP (thickHook r c a b) ↔ Even (r + c) := by
  rw [← ofPairs_thickPairs h, isP_ofPairs_iff (validPairs_thickPairs h), plen_thickPairs h]
  simp [endM, endL_thickPairs h, endR_thickPairs h]

theorem endL_append_eq_zero {A B : List (ℕ × ℕ)} (hA : endL A = 0) (hB : endL B = 0) :
    endL (A ++ B) = 0 := by
  cases A with
  | nil => simpa using hB
  | cons x A =>
    rw [List.cons_append, RunPairs.endL_cons]
    rw [RunPairs.endL_cons] at hA
    by_cases hx : AGood x = true
    · rw [if_pos hx] at hA
      omega
    · rw [if_neg hx]

theorem endR_append_eq_zero {A B : List (ℕ × ℕ)} (hA : endR A = 0) (hB : endR B = 0) :
    endR (A ++ B) = 0 := by
  rw [← RunPairs.endL_pdual, RunPairs.pdual_append]
  exact endL_append_eq_zero (by rwa [RunPairs.endL_pdual]) (by rwa [RunPairs.endL_pdual])

/-- Invariant of melds of losing thick hooks: run pairs with even `plen` whose first pair is
not A-good and whose last pair is not B-good. -/
theorem exists_pairs_of_melds {l : List ℕ} (h : Melds (fun t => IsThickHook t ∧ IsP t) l) :
    ∃ p, ValidPairs p ∧ ofPairs p = l ∧ Even (plen p) ∧ endL p = 0 ∧ endR p = 0 := by
  induction h with
  | nil => exact ⟨[], RunPairs.validPairs_nil, rfl, ⟨0, rfl⟩, rfl, rfl⟩
  | piece hl =>
    obtain ⟨⟨r, c, a, b, hpar, rfl⟩, hP⟩ := hl
    have hv := validPairs_thickPairs hpar
    rw [← ofPairs_thickPairs hpar] at hP
    exact ⟨_, hv, ofPairs_thickPairs hpar, ((isP_ofPairs_iff hv).1 hP).1,
      endL_thickPairs hpar, endR_thickPairs hpar⟩
  | join _ _ ih1 ih2 =>
    obtain ⟨q, hq, rfl, hq1, hq2, hq3⟩ := ih1
    obtain ⟨p, hp, rfl, hp1, hp2, hp3⟩ := ih2
    refine ⟨p ++ q, RunPairs.validPairs_append.2 ⟨hp, hq⟩, (meld_ofPairs hq).symm, ?_,
      endL_append_eq_zero hp2 hq2, endR_append_eq_zero hp3 hq3⟩
    rw [RunPairs.plen_append]
    exact hp1.add hq1

/-- **The thick-hook meld conjecture holds.** -/
theorem meldConjecture_holds : meldConjecture := by
  intro l h
  obtain ⟨p, hp, rfl, hplen, hL, hR⟩ := exists_pairs_of_melds h
  rw [isP_ofPairs_iff hp]
  exact ⟨hplen, by simp [endM, hL, hR]⟩

/-- The meld conjecture for right-nested melds `H₁ ◇ (H₂ ◇ (⋯ ◇ Hₙ))`. -/
theorem isP_meldAll {hs : List (List ℕ)} (h : ∀ t ∈ hs, IsThickHook t ∧ IsP t) :
    IsP (meldAll hs) :=
  meldConjecture_holds _ (melds_iff.2 ⟨hs, h, rfl⟩)

/-! ## Parity self-conjugate partitions and stacks of odd hooks -/

/-- `λ'_k`, the `k`-th part of the conjugate partition: the number of parts `≥ k`. -/
def conjPart (l : List ℕ) (k : ℕ) : ℕ := l.countP (fun x => decide (k ≤ x))

/-- `λ` is parity self-conjugate: `λ_k ≡ λ'_k (mod 2)` for every `k ≥ 1` (parts past the end
are `0`). -/
def ParitySelfConj (l : List ℕ) : Prop := ∀ k, 1 ≤ k → part l k % 2 = conjPart l k % 2

/-- The stacks `Γ_{r₁,r₁} ◁ (Γ_{r₂,r₂} ◁ (⋯ ◁ (Γ_{r_j,r_j} ◁ [1])))` of odd self-conjugate
hooks and `[1]`: `j ≥ 0`, every `r_i` odd, and every intermediate stack defined (`stack` is
the paper's general Durfee-length stack). -/
inductive OddHookStack : List ℕ → Prop
  | base : OddHookStack [1]
  | step {r : ℕ} {m s : List ℕ} : Odd r → OddHookStack m → stack (hook r r) m = some s →
      OddHookStack s

/-- **conj:pself**: a parity self-conjugate partition is in N iff it is the stack of odd
self-conjugate hooks and `[1]`. -/
def pselfConjecture : Prop :=
  ∀ l : List ℕ, IsPartition l → ParitySelfConj l → (¬ IsP l ↔ OddHookStack l)

/-! ### Rows of `ofPairs p` and of its conjugate -/

theorem getD_ofPairs_cons (a b : ℕ) (p : List (ℕ × ℕ)) (j : ℕ) :
    (ofPairs ((a, b) :: p)).getD j 0 =
      if j < a then b + pairsBSum p else (ofPairs p).getD (j - a) 0 := by
  rw [ofPairs_cons]
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_replicate _ h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using h), List.length_replicate]

theorem getD_zero_ofPairs {p : List (ℕ × ℕ)} (hp : ValidPairs p) :
    (ofPairs p).getD 0 0 = pairsBSum p :=
  part_one_ofPairs hp

theorem getD_map_add {l : List ℕ} {c j : ℕ} (h : j < l.length) :
    (l.map (· + c)).getD j 0 = l.getD j 0 + c := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

theorem pairsBSum_pdual (p : List (ℕ × ℕ)) : pairsBSum (RunPairs.pdual p) = pairsASum p := by
  simp [RunPairs.pdual, pairsBSum, pairsASum, List.map_reverse, List.sum_reverse, List.map_map,
    Function.comp_def]

theorem pairsASum_pdual (p : List (ℕ × ℕ)) : pairsASum (RunPairs.pdual p) = pairsBSum p := by
  simp [RunPairs.pdual, pairsBSum, pairsASum, List.map_reverse, List.sum_reverse, List.map_map,
    Function.comp_def]

/-- The conjugate of `ofPairs p` is `ofPairs (pdual p)`: the number of parts `≥ j + 1` is row
`j` (0-indexed) of `ofPairs (pdual p)`. -/
theorem countP_ofPairs (p : List (ℕ × ℕ)) (j : ℕ) :
    (ofPairs p).countP (fun x => decide (j + 1 ≤ x)) =
      (ofPairs (RunPairs.pdual p)).getD j 0 := by
  induction p with
  | nil => simp [ofPairs_nil, RunPairs.pdual_nil]
  | cons x q ih =>
    obtain ⟨a, b⟩ := x
    have hlen : (ofPairs (RunPairs.pdual q)).length = pairsBSum q := by
      rw [length_ofPairs, pairsASum_pdual]
    rw [ofPairs_cons, List.countP_append, ih, RunPairs.pdual_cons, ofPairs_append,
      List.countP_replicate]
    simp only [Prod.swap_prod_mk, ofPairs_cons, ofPairs_nil, pairsBSum_cons, pairsBSum_nil,
      List.append_nil, Nat.add_zero, decide_eq_true_eq]
    by_cases h1 : j < pairsBSum q
    · rw [List.getD_append _ _ _ _ (by simpa [hlen] using h1), getD_map_add (by omega),
        if_pos (by omega)]
      omega
    · rw [List.getD_append_right _ _ _ _ (by simp [hlen]; omega), List.length_map, hlen,
        List.getD_eq_default _ _ (by omega)]
      by_cases h2 : j < pairsBSum q + b
      · rw [if_pos (by omega), List.getD_replicate _ (by omega)]
        omega
      · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Parity self-conjugacy, read through run pairs: `λ` and `λ'` have the same parity
sequence. -/
theorem parity_eq_of_paritySelfConj {p : List (ℕ × ℕ)} (h : ParitySelfConj (ofPairs p))
    (j : ℕ) : (ofPairs p).getD j 0 % 2 = (ofPairs (RunPairs.pdual p)).getD j 0 % 2 := by
  have := h (j + 1) (by omega)
  simp only [part, conjPart, Nat.add_sub_cancel, countP_ofPairs] at this
  exact this

/-! ### `L = R` and even boundary length -/

/-- `endL p` is the first row with an even drop: `λ_{i+1} - λ_{i+2}` is odd for `i < endL p`
and even for `i = endL p` (rows 0-indexed, parts past the end `0`). -/
theorem endL_drops {p : List (ℕ × ℕ)} (hp : ValidPairs p) :
    (∀ j < endL p, (ofPairs p).getD j 0 % 2 ≠ (ofPairs p).getD (j + 1) 0 % 2) ∧
      (ofPairs p).getD (endL p) 0 % 2 = (ofPairs p).getD (endL p + 1) 0 % 2 := by
  induction p with
  | nil => simp [ofPairs_nil, RunPairs.endL_nil]
  | cons x q ih =>
    obtain ⟨a, b⟩ := x
    have hv := validPairs_cons.1 hp
    obtain ⟨ih1, ih2⟩ := ih hv.2
    have h0 := getD_zero_ofPairs hv.2
    rw [RunPairs.endL_cons]
    by_cases hx : AGood (a, b) = true
    · rw [if_pos hx]
      simp only [RunPairs.aGood_iff] at hx
      obtain ⟨rfl, hb⟩ := hx
      refine ⟨fun j hj => ?_, ?_⟩
      · rcases j with _ | j
        · rw [getD_ofPairs_cons, getD_ofPairs_cons, if_pos (by omega), if_neg (by omega),
            Nat.sub_self, h0]
          omega
        · rw [getD_ofPairs_cons, getD_ofPairs_cons, if_neg (by omega), if_neg (by omega),
            Nat.add_sub_cancel, Nat.add_sub_cancel]
          exact ih1 j (by omega)
      · rw [getD_ofPairs_cons, getD_ofPairs_cons, if_neg (by omega), if_neg (by omega),
          Nat.add_sub_cancel, Nat.add_sub_cancel]
        exact ih2
    · rw [if_neg hx]
      refine ⟨fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
      rw [getD_ofPairs_cons, getD_ofPairs_cons, if_pos (by omega)]
      by_cases ha : 0 + 1 < a
      · rw [if_pos ha]
      · rw [if_neg ha, show 0 + 1 - a = 0 by omega, h0]
        have ha1 : a = 1 := by omega
        subst ha1
        have hb : b % 2 ≠ 1 := fun hb => hx ((RunPairs.aGood_iff _).2 ⟨rfl, hb⟩)
        omega

theorem endL_le_of_parity {p q : List (ℕ × ℕ)} (hp : ValidPairs p) (hq : ValidPairs q)
    (h : ∀ j, (ofPairs p).getD j 0 % 2 = (ofPairs q).getD j 0 % 2) : endL p ≤ endL q := by
  by_contra hlt
  apply (endL_drops hp).1 (endL q) (by omega)
  rw [h, h]
  exact (endL_drops hq).2

/-- For a parity self-conjugate partition, `L = R`. -/
theorem endL_eq_endR_of_paritySelfConj {p : List (ℕ × ℕ)} (hp : ValidPairs p)
    (h : ParitySelfConj (ofPairs p)) : endL p = endR p := by
  have hpar := parity_eq_of_paritySelfConj h
  have hd := RunPairs.validPairs_pdual hp
  rw [← RunPairs.endL_pdual]
  exact le_antisymm (endL_le_of_parity hp hd hpar)
    (endL_le_of_parity hd hp fun j => (hpar j).symm)

/-- For a parity self-conjugate partition, `ℓ(λ) + λ₁` is even (the case `k = 1`). -/
theorem even_plen_of_paritySelfConj {p : List (ℕ × ℕ)} (hp : ValidPairs p)
    (h : ParitySelfConj (ofPairs p)) : Even (plen p) := by
  have h0 := parity_eq_of_paritySelfConj h 0
  rw [getD_zero_ofPairs hp, getD_zero_ofPairs (RunPairs.validPairs_pdual hp),
    pairsBSum_pdual] at h0
  rw [plen_eq, Nat.even_iff]
  omega

/-! ### When `L + R ≥ k`: self-conjugacy -/

theorem forall_bGood_of_endR_eq {S : List (ℕ × ℕ)} (h : endR S = S.length) :
    ∀ x ∈ S, BGood x = true := by
  have h1 : S.reverse.takeWhile BGood = S.reverse :=
    (List.takeWhile_prefix _).eq_of_length (by rw [List.length_reverse]; exact h)
  intro x hx
  exact List.mem_takeWhile_imp (h1 ▸ List.mem_reverse.2 hx)

/-- If `L + R ≥ k`, every run pair is A-good or B-good. -/
theorem forall_good_of_le {p : List (ℕ × ℕ)} (h : p.length ≤ endL p + endR p) :
    ∀ x ∈ p, AGood x = true ∨ BGood x = true := by
  have hsplit : p.takeWhile AGood ++ p.dropWhile AGood = p := List.takeWhile_append_dropWhile
  have hL : endL p = (p.takeWhile AGood).length := rfl
  have hlen : p.length = (p.takeWhile AGood).length + (p.dropWhile AGood).length := by
    conv_lhs => rw [← hsplit]
    rw [List.length_append]
  have hRD : endR (p.dropWhile AGood) = (p.dropWhile AGood).length := by
    by_contra hne
    have hlt := lt_of_le_of_ne (RunPairs.endR_le_length _) hne
    have := RunPairs.endR_append_of_lt hlt (p.takeWhile AGood)
    rw [hsplit] at this
    omega
  intro x hx
  rw [← hsplit, List.mem_append] at hx
  rcases hx with hx | hx
  · exact Or.inl (List.mem_takeWhile_imp hx)
  · exact Or.inr (forall_bGood_of_endR_eq hRD x hx)

/-- With every `b`-entry odd, the parity sequence of `ofPairs p` determines the `a`-entries:
the parity changes exactly at the ends of the blocks. -/
theorem map_fst_eq_of_parity : ∀ {p q : List (ℕ × ℕ)}, ValidPairs p → ValidPairs q →
    (∀ x ∈ p, x.2 % 2 = 1) → (∀ x ∈ q, x.2 % 2 = 1) →
    (∀ j, (ofPairs p).getD j 0 % 2 = (ofPairs q).getD j 0 % 2) →
    p.map Prod.fst = q.map Prod.fst
  | [], [], _, _, _, _, _ => rfl
  | [], (a, b) :: q, _, hq, _, hqo, h => by
    have hv := validPairs_cons.1 hq
    have hb : b % 2 = 1 := hqo (a, b) (by simp)
    have h1 := h (a - 1)
    have h2 := h a
    rw [getD_ofPairs_cons, if_pos (by omega)] at h1
    rw [getD_ofPairs_cons, if_neg (by omega), Nat.sub_self, getD_zero_ofPairs hv.2] at h2
    simp only [ofPairs_nil, List.getD_nil] at h1 h2
    omega
  | (a, b) :: p, [], hp, _, hpo, _, h => by
    have hv := validPairs_cons.1 hp
    have hb : b % 2 = 1 := hpo (a, b) (by simp)
    have h1 := h (a - 1)
    have h2 := h a
    rw [getD_ofPairs_cons, if_pos (by omega)] at h1
    rw [getD_ofPairs_cons, if_neg (by omega), Nat.sub_self, getD_zero_ofPairs hv.2] at h2
    simp only [ofPairs_nil, List.getD_nil] at h1 h2
    omega
  | (a, b) :: p, (a', b') :: q, hp, hq, hpo, hqo, h => by
    have hv := validPairs_cons.1 hp
    have hv' := validPairs_cons.1 hq
    have hb : b % 2 = 1 := hpo (a, b) (by simp)
    have hb' : b' % 2 = 1 := hqo (a', b') (by simp)
    have haa : a = a' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have h1 := h (a - 1)
        have h2 := h a
        rw [getD_ofPairs_cons, getD_ofPairs_cons, if_pos (by omega), if_pos (by omega)] at h1
        rw [getD_ofPairs_cons, getD_ofPairs_cons, if_neg (by omega), if_pos hlt, Nat.sub_self,
          getD_zero_ofPairs hv.2] at h2
        omega
      · have h1 := h (a' - 1)
        have h2 := h a'
        rw [getD_ofPairs_cons, getD_ofPairs_cons, if_pos (by omega), if_pos (by omega)] at h1
        rw [getD_ofPairs_cons, getD_ofPairs_cons, if_pos hlt, if_neg (by omega), Nat.sub_self,
          getD_zero_ofPairs hv'.2] at h2
        omega
    subst haa
    have ih := map_fst_eq_of_parity hv.2 hv'.2 (fun x hx => hpo x (List.mem_cons_of_mem _ hx))
      (fun x hx => hqo x (List.mem_cons_of_mem _ hx)) (fun j => by
        have := h (j + a)
        rwa [getD_ofPairs_cons, getD_ofPairs_cons, if_neg (by omega), if_neg (by omega),
          Nat.add_sub_cancel] at this)
    simp [ih]

/-- With all run-pair entries odd, a parity self-conjugate partition is self-conjugate. -/
theorem pdual_eq_self_of_parity {p : List (ℕ × ℕ)} (hp : ValidPairs p)
    (hodd : ∀ x ∈ p, x.1 % 2 = 1 ∧ x.2 % 2 = 1)
    (h : ∀ j, (ofPairs p).getD j 0 % 2 = (ofPairs (RunPairs.pdual p)).getD j 0 % 2) :
    RunPairs.pdual p = p := by
  have hfst := map_fst_eq_of_parity hp (RunPairs.validPairs_pdual hp)
    (fun x hx => (hodd x hx).2)
    (fun x hx => (hodd _ (RunPairs.mem_pdual.1 hx)).1) h
  have e1 : (RunPairs.pdual p).map Prod.fst = (p.map Prod.snd).reverse := by
    simp [RunPairs.pdual, List.map_reverse, List.map_map]
  have e2 : (RunPairs.pdual p).map Prod.snd = (p.map Prod.fst).reverse := by
    simp [RunPairs.pdual, List.map_reverse, List.map_map]
  have hsnd : (RunPairs.pdual p).map Prod.snd = p.map Prod.snd := by
    rw [e2, hfst, e1, List.reverse_reverse]
  have key : ∀ l : List (ℕ × ℕ), (l.map Prod.fst).zip (l.map Prod.snd) = l := fun l => by
    have := List.zip_unzip l
    rwa [List.unzip_fst, List.unzip_snd] at this
  calc RunPairs.pdual p
      = ((RunPairs.pdual p).map Prod.fst).zip ((RunPairs.pdual p).map Prod.snd) := (key _).symm
    _ = (p.map Prod.fst).zip (p.map Prod.snd) := by rw [← hfst, hsnd]
    _ = p := key p

/-! ### The run pairs of the stacks -/

/-- Run pairs `[(1, o₁), …, (1, o_j), (1, 1), (o_j, 1), …, (o₁, 1)]`. -/
def spPairs (os : List ℕ) : List (ℕ × ℕ) :=
  os.map (fun o => (1, o)) ++ (1, 1) :: os.reverse.map (fun o => (o, 1))

theorem spPairs_cons (o : ℕ) (os : List ℕ) :
    spPairs (o :: os) = (1, o) :: (spPairs os ++ [(o, 1)]) := by
  simp [spPairs]

theorem pdual_spPairs (os : List ℕ) : RunPairs.pdual (spPairs os) = spPairs os := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    rw [spPairs_cons, RunPairs.pdual_cons, RunPairs.pdual_append, ih, RunPairs.pdual_single]
    simp

theorem validPairs_spPairs {os : List ℕ} (h : ∀ o ∈ os, Odd o) : ValidPairs (spPairs os) := by
  intro x hx
  simp only [spPairs, List.mem_append, List.mem_map, List.mem_cons, List.mem_reverse] at hx
  rcases hx with ⟨o, ho, rfl⟩ | rfl | ⟨o, ho, rfl⟩
  · exact ⟨le_rfl, (h o ho).pos⟩
  · exact ⟨le_rfl, le_rfl⟩
  · exact ⟨(h o ho).pos, le_rfl⟩

theorem endM_spPairs {os : List ℕ} (h : ∀ o ∈ os, Odd o) :
    endM (spPairs os) = 2 * os.length + 1 := by
  have hA : ∀ x ∈ os.map (fun o => (1, o)) ++ [(1, 1)], AGood x = true := by
    intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨o, ho, rfl⟩ | rfl
    · exact (RunPairs.aGood_iff _).2 ⟨rfl, Nat.odd_iff.1 (h o ho)⟩
    · rfl
  have hB : ∀ x ∈ os.reverse.map (fun o => (o, 1)), BGood x = true := by
    intro x hx
    simp only [List.mem_map, List.mem_reverse] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    exact (RunPairs.bGood_iff _).2 ⟨Nat.odd_iff.1 (h o ho), rfl⟩
  have := RunPairs.endM_of_good hA hB
  rw [List.append_assoc, List.singleton_append] at this
  rw [spPairs, this]
  simp
  omega

theorem pairsBSum_spPairs_cons (o : ℕ) (os : List ℕ) :
    pairsBSum (spPairs (o :: os)) = pairsBSum (spPairs os) + o + 1 := by
  rw [spPairs_cons]
  simp
  omega

theorem odd_pairsBSum_spPairs {os : List ℕ} (h : ∀ o ∈ os, Odd o) :
    Odd (pairsBSum (spPairs os)) := by
  induction os with
  | nil => exact ⟨0, rfl⟩
  | cons o os ih =>
    rw [pairsBSum_spPairs_cons, Nat.odd_iff]
    have h1 := Nat.odd_iff.1 (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 := Nat.odd_iff.1 (h o List.mem_cons_self)
    omega

theorem ofPairs_spPairs_cons (o : ℕ) (os : List ℕ) :
    ofPairs (spPairs (o :: os)) =
      (o + (pairsBSum (spPairs os) + 1)) ::
        ((ofPairs (spPairs os)).map (· + 1) ++ List.replicate o 1) := by
  rw [spPairs_cons, ofPairs_cons, ofPairs_append]
  simp [ofPairs_cons, ofPairs_nil]

/-- The stacks of odd self-conjugate hooks and `[1]` are exactly the partitions with run pairs
`[(1, o₁), …, (1, o_j), (1, 1), (o_j, 1), …, (o₁, 1)]`, every `o_i` odd. -/
theorem oddHookStack_iff {l : List ℕ} :
    OddHookStack l ↔ ∃ os : List ℕ, (∀ o ∈ os, Odd o) ∧ l = ofPairs (spPairs os) := by
  constructor
  · intro h
    induction h with
    | base => exact ⟨[], by simp, rfl⟩
    | @step r m s hr _ hs ih =>
      obtain ⟨os, hos, rfl⟩ := ih
      have hv := validPairs_spPairs hos
      have hlen : (ofPairs (spPairs os)).length = pairsBSum (spPairs os) := by
        rw [length_ofPairs, ← pairsBSum_pdual, pdual_spPairs]
      have hpart := part_one_ofPairs hv
      have hN := Nat.odd_iff.1 (odd_pairsBSum_spPairs hos)
      have hr2 := Nat.odd_iff.1 hr
      rw [stack_hook _ hr.pos] at hs
      split_ifs at hs with hcond
      obtain rfl := Option.some.inj hs
      rw [hlen, hpart] at hcond
      refine ⟨(r - 1 - pairsBSum (spPairs os)) :: os, ?_, ?_⟩
      · intro o ho
        rcases List.mem_cons.1 ho with rfl | ho
        · exact Nat.odd_iff.2 (by omega)
        · exact hos o ho
      · rw [ofPairs_spPairs_cons, hookStack, pad, hlen, List.map_append, List.map_replicate]
        congr 1
        omega
  · rintro ⟨os, hos, rfl⟩
    induction os with
    | nil => exact OddHookStack.base
    | cons o os ih =>
      have ho := Nat.odd_iff.1 (hos o List.mem_cons_self)
      have hos' : ∀ x ∈ os, Odd x := fun x hx => hos x (List.mem_cons_of_mem _ hx)
      have hv := validPairs_spPairs hos'
      have hN := Nat.odd_iff.1 (odd_pairsBSum_spPairs hos')
      have hlen : (ofPairs (spPairs os)).length = pairsBSum (spPairs os) := by
        rw [length_ofPairs, ← pairsBSum_pdual, pdual_spPairs]
      have hpart := part_one_ofPairs hv
      refine OddHookStack.step (r := o + (pairsBSum (spPairs os) + 1))
        (Nat.odd_iff.2 (by omega)) (ih hos') ?_
      rw [stack_hook _ (by omega), if_pos (by rw [hlen, hpart]; omega), ofPairs_spPairs_cons,
        hookStack, pad, hlen, List.map_append, List.map_replicate,
        show o + (pairsBSum (spPairs os) + 1) - 1 - pairsBSum (spPairs os) = o by omega]

/-! ### conj:pself -/

/-- Every stack of odd self-conjugate hooks and `[1]` is self-conjugate. -/
theorem conjPart_of_oddHookStack {l : List ℕ} (h : OddHookStack l) {k : ℕ} (hk : 1 ≤ k) :
    conjPart l k = part l k := by
  obtain ⟨os, -, rfl⟩ := oddHookStack_iff.1 h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [conjPart, countP_ofPairs, pdual_spPairs]
  rfl

theorem not_isP_ofPairs_spPairs {os : List ℕ} (h : ∀ o ∈ os, Odd o) :
    ¬ IsP (ofPairs (spPairs os)) := by
  rw [isP_ofPairs_iff (validPairs_spPairs h), endM_spPairs h]
  rintro ⟨-, hM⟩
  rw [Nat.even_iff] at hM
  omega

theorem aGood_of_mem_take {p : List (ℕ × ℕ)} {m : ℕ} (hm : m ≤ endL p) {x : ℕ × ℕ}
    (hx : x ∈ p.take m) : AGood x = true := by
  have hpre : p.takeWhile AGood = p.take (endL p) :=
    List.prefix_iff_eq_take.1 (List.takeWhile_prefix _)
  have : p.take m = (p.takeWhile AGood).take m := by
    rw [hpre, List.take_take, min_eq_left hm]
  rw [this] at hx
  exact List.mem_takeWhile_imp (List.mem_of_mem_take hx)

/-- A self-conjugate list of `2n + 1` run pairs whose first `n + 1` pairs are A-good has the
form `spPairs os` with every `o_i` odd. -/
theorem eq_spPairs : ∀ (n : ℕ) (p : List (ℕ × ℕ)), p.length = 2 * n + 1 →
    RunPairs.pdual p = p → (∀ x ∈ p.take (n + 1), AGood x = true) →
    ∃ os : List ℕ, (∀ o ∈ os, Odd o) ∧ p = spPairs os
  | 0, p, hlen, hd, hA => by
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hlen
    have hx := (RunPairs.aGood_iff _).1 (hA x (by simp))
    have hs : x.swap = x := by
      rw [RunPairs.pdual_cons, RunPairs.pdual_nil, List.nil_append] at hd
      exact List.singleton_injective hd
    obtain ⟨a, b⟩ := x
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hs hx
    refine ⟨[], by simp, ?_⟩
    rw [show a = 1 by omega, show b = 1 by omega]
    rfl
  | n + 1, p, hlen, hd, hA => by
    obtain ⟨x, t, rfl⟩ : ∃ x t, p = x :: t := List.exists_cons_of_ne_nil (by
      rintro rfl; simp at hlen)
    have ht : t ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨q, y, rfl⟩ : ∃ q y, t = q ++ [y] :=
      ⟨t.dropLast, t.getLast ht, (List.dropLast_append_getLast ht).symm⟩
    simp only [List.length_cons, List.length_append, List.length_nil] at hlen
    rw [RunPairs.pdual_cons, RunPairs.pdual_append, RunPairs.pdual_cons y [],
      RunPairs.pdual_nil, List.nil_append, List.singleton_append, List.cons_append,
      List.cons.injEq] at hd
    obtain ⟨hyx, hd⟩ := hd
    obtain ⟨hq, -⟩ := List.append_inj' hd rfl
    rw [List.take_succ_cons, List.take_append_of_le_length (by omega)] at hA
    have hx := (RunPairs.aGood_iff _).1 (hA x List.mem_cons_self)
    obtain ⟨os, hos, rfl⟩ := eq_spPairs n q (by omega) hq
      (fun z hz => hA z (List.mem_cons_of_mem _ hz))
    obtain ⟨a, o⟩ := x
    simp only at hx
    obtain ⟨rfl, ho⟩ := hx
    have hy : y = (o, 1) := by rw [← Prod.swap_swap y, hyx]; rfl
    subst hy
    refine ⟨o :: os, ?_, by rw [spPairs_cons]⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact Nat.odd_iff.2 ho
    · exact hos z hz

/-- A parity self-conjugate N-position is a stack of odd self-conjugate hooks and `[1]`. -/
theorem oddHookStack_of_paritySelfConj {l : List ℕ} (hl : IsPartition l)
    (hps : ParitySelfConj l) (hN : ¬ IsP l) : OddHookStack l := by
  obtain ⟨p, hp, rfl⟩ := exists_ofPairs hl
  have hLR := endL_eq_endR_of_paritySelfConj hp hps
  have hplen := even_plen_of_paritySelfConj hp hps
  rw [isP_ofPairs_iff hp] at hN
  have hM : ¬ Even (endM p) := fun hM => hN ⟨hplen, hM⟩
  have hk : p.length ≤ endL p + endR p := by
    by_contra hlt
    apply hM
    rw [endM, min_eq_right (by omega), ← hLR]
    exact ⟨endL p, rfl⟩
  rw [endM, min_eq_left hk, Nat.even_iff] at hM
  have hodd : ∀ x ∈ p, x.1 % 2 = 1 ∧ x.2 % 2 = 1 := fun x hx => by
    rcases forall_good_of_le hk x hx with h | h
    · rw [RunPairs.aGood_iff] at h
      omega
    · rw [RunPairs.bGood_iff] at h
      omega
  have hself := pdual_eq_self_of_parity hp hodd (parity_eq_of_paritySelfConj hps)
  obtain ⟨os, hos, rfl⟩ := eq_spPairs (p.length / 2) p (by omega) hself
    (fun x hx => aGood_of_mem_take (by omega) hx)
  exact oddHookStack_iff.2 ⟨os, hos, rfl⟩

/-- **conj:pself**, in a slightly stronger form: a partition is parity self-conjugate and in N
iff it is a stack of odd self-conjugate hooks and `[1]`. -/
theorem paritySelfConj_and_not_isP_iff {l : List ℕ} (hl : IsPartition l) :
    ParitySelfConj l ∧ ¬ IsP l ↔ OddHookStack l := by
  constructor
  · rintro ⟨hps, hN⟩
    exact oddHookStack_of_paritySelfConj hl hps hN
  · intro h
    refine ⟨fun k hk => by rw [conjPart_of_oddHookStack h hk], ?_⟩
    obtain ⟨os, hos, rfl⟩ := oddHookStack_iff.1 h
    exact not_isP_ofPairs_spPairs hos

/-- **conj:pself holds.** -/
theorem pselfConjecture_holds : pselfConjecture := fun _ hl hps =>
  ⟨fun hN => (paritySelfConj_and_not_isP_iff hl).1 ⟨hps, hN⟩,
    fun h => ((paritySelfConj_and_not_isP_iff hl).2 h).2⟩

/-! ## Every bracketing of a stack of hooks

The paper writes stacks of hooks without brackets. `stack_hook_assoc` shows that
`(Γ_{r,c} ◁ μ) ◁ ν = Γ_{r,c} ◁ (μ ◁ ν)` as partial operations, so every bracketing of a stack of
hooks `Γ_{r,r}` gives the right-nested stack (`HookTree.eval_eq_nest`), and conj:pself holds in
every bracketing (`pselfConjecture_anyBracketing`). -/

/-! ### Stacks under a hook associate -/

theorem getD_pad (μ : List ℕ) (n i : ℕ) : (pad μ n).getD i 0 = μ.getD i 0 := by
  unfold pad
  by_cases h : i < μ.length
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default μ 0 (by omega)]
    by_cases h' : i - μ.length < n - μ.length
    · exact List.getD_replicate _ h'
    · exact List.getD_eq_default _ _ (by simp; omega)

theorem part_hookStack_add_two {r c : ℕ} {μ : List ℕ} (h : μ.length ≤ r - 1) (n : ℕ) :
    part (hookStack r c μ) (n + 2) = if n < r - 1 then part μ (n + 1) + 1 else 0 := by
  simp only [part, hookStack, show n + 2 - 1 = n + 1 by omega, List.getD_cons_succ,
    Nat.add_sub_cancel]
  split_ifs with hn
  · rw [getD_map_add (by rw [length_pad h]; exact hn), getD_pad]
  · exact List.getD_eq_default _ _ (by simp [length_pad h]; omega)

theorem one_le_durfee {m : List ℕ} (hm : IsPartition m) (hne : m ≠ []) : 1 ≤ durfee m := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact Nat.le_findGreatest (by simp) (hm.2 x (by simp))

theorem durfee_hookStack {r c : ℕ} {μ : List ℕ} (hc : 1 ≤ c) (h : μ.length ≤ r - 1) :
    durfee (hookStack r c μ) = durfee μ + 1 := by
  obtain ⟨-, he2, he3⟩ := (Nat.findGreatest_eq_iff (P := fun d => d ≤ part μ d)
    (k := μ.length) (m := durfee μ)).1 rfl
  have hdm : durfee μ ≤ μ.length := Nat.findGreatest_le _
  have hlen : (hookStack r c μ).length = r - 1 + 1 := by simp [hookStack, length_pad h]
  show Nat.findGreatest (fun d => d ≤ part (hookStack r c μ) d) (hookStack r c μ).length =
    durfee μ + 1
  rw [Nat.findGreatest_eq_iff, hlen]
  refine ⟨by omega, fun _ => ?_, fun n hn hle => ?_⟩
  · rcases Nat.eq_zero_or_pos (durfee μ) with h0 | hpos
    · simpa [h0, part_one_hookStack] using hc
    · obtain ⟨e, he⟩ : ∃ e, durfee μ = e + 1 := ⟨durfee μ - 1, by omega⟩
      rw [he, part_hookStack_add_two h, if_pos (by omega)]
      have := he2 (by omega)
      rw [he] at this
      omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [part_hookStack_add_two h]
    split_ifs with hk
    · intro hcon
      by_cases hk' : k + 1 ≤ μ.length
      · exact he3 (by omega) hk' (by omega)
      · rw [part, List.getD_eq_default _ _ (by omega)] at hcon
        omega
    · omega

/-- When `d(m) ≥ 1`, a defined stack `m ◁ s` keeps the number of rows and the first row. -/
theorem stack_facts {m s w : List ℕ} (he : 1 ≤ durfee m) (h : stack m s = some w) :
    durfee m + s.length ≤ m.length ∧ w.length = m.length ∧ part w 1 = part m 1 := by
  have hdm : durfee m ≤ m.length := Nat.findGreatest_le _
  unfold stack at h
  split_ifs at h with hcond
  obtain rfl := Option.some.inj h
  have hks : durfee m + s.length ≤ m.length := by
    rcases Nat.eq_zero_or_pos s.length with h0 | hpos
    · omega
    · have := hcond.1 s.length (Finset.mem_Icc.2 ⟨hpos, le_rfl⟩)
      by_contra hlt
      rw [part, List.getD_eq_default _ _ (by omega)] at this
      omega
  refine ⟨hks, by simp; omega, ?_⟩
  obtain ⟨x, t, rfl⟩ : ∃ x t, m = x :: t := List.exists_cons_of_ne_nil (by
    rintro rfl; simp at hdm; omega)
  obtain ⟨e, he'⟩ : ∃ e, durfee (x :: t) = e + 1 := ⟨durfee (x :: t) - 1, by omega⟩
  rw [he']
  rfl

/-- The list identity behind `stack_hook_assoc`. -/
theorem hookStack_stack_eq {r c e : ℕ} {m s : List ℕ} (hlen : m.length ≤ r - 1)
    (hks : e + s.length ≤ m.length) :
    (hookStack r c m).take (e + 1) ++ (List.range' 1 s.length).map
        (fun i => part (hookStack r c m) (e + 1 + i) + part s i) ++
      (hookStack r c m).drop (e + 1 + s.length) =
    hookStack r c (m.take e ++ (List.range' 1 s.length).map
        (fun i => part m (e + i) + part s i) ++ m.drop (e + s.length)) := by
  have hw : (m.take e ++ (List.range' 1 s.length).map (fun i => part m (e + i) + part s i) ++
      m.drop (e + s.length)).length = m.length := by
    simp; omega
  have hmid : ∀ i ∈ List.range' 1 s.length,
      part (hookStack r c m) (e + 1 + i) + part s i = (part m (e + i) + part s i) + 1 := by
    intro i hi
    rw [List.mem_range'_1] at hi
    rw [show e + 1 + i = (e + i - 1) + 2 by omega, part_hookStack_add_two hlen,
      if_pos (by omega), show e + i - 1 + 1 = e + i by omega]
    omega
  rw [List.map_congr_left hmid]
  unfold hookStack pad
  rw [hw, show e + 1 + s.length = (e + s.length) + 1 by omega, List.take_succ_cons,
    List.drop_succ_cons, List.cons_append, List.cons_append]
  congr 1
  have hle : e ≤ (List.map (fun x => x + 1) m).length := by simp; omega
  have hle' : e + s.length ≤ (List.map (fun x => x + 1) m).length := by simp; omega
  rw [List.map_append, List.take_append_of_le_length hle, List.drop_append_of_le_length hle',
    List.map_append, List.map_append, List.map_append, List.map_take, List.map_drop,
    List.map_map]
  simp only [List.append_assoc]
  rfl

/-- **Stacks under a hook associate**: `(Γ_{r,c} ◁ m) ◁ s = Γ_{r,c} ◁ (m ◁ s)` for a nonempty
partition `m`, and either side is defined iff the other is. -/
theorem stack_hook_assoc {r c : ℕ} (hc : 1 ≤ c) {m : List ℕ} (hm : IsPartition m)
    (hne : m ≠ []) (s : List ℕ) :
    (stack (hook r c) m).bind (fun x => stack x s) = (stack m s).bind (stack (hook r c)) := by
  have he := one_le_durfee hm hne
  have hdm : durfee m ≤ m.length := Nat.findGreatest_le _
  rw [stack_hook m hc]
  by_cases hcond : m.length ≤ r - 1 ∧ part m 1 + 1 ≤ c
  · rw [if_pos hcond, Option.bind_some]
    have hdx := durfee_hookStack (r := r) hc hcond.1
    -- the rows of `Γ_{r,c} ◁ m` below its Durfee square
    have hrow : ∀ i, 1 ≤ i → part (hookStack r c m) (durfee m + 1 + i) =
        if durfee m + i ≤ r - 1 then part m (durfee m + i) + 1 else 0 := by
      intro i hi
      rw [show durfee m + 1 + i = (durfee m + i - 1) + 2 by omega,
        part_hookStack_add_two hcond.1, show durfee m + i - 1 + 1 = durfee m + i by omega]
      split_ifs <;> first | rfl | omega
    have hrow0 : part (hookStack r c m) (durfee m + 1) = part m (durfee m) + 1 := by
      rw [show durfee m + 1 = (durfee m - 1) + 2 by omega, part_hookStack_add_two hcond.1,
        if_pos (by omega), show durfee m - 1 + 1 = durfee m by omega]
    have hiff : ∀ i, 1 ≤ i → (part (hookStack r c m) (durfee m + 1 + i) = durfee m + 1 ↔
        part m (durfee m + i) = durfee m) := by
      intro i hi
      rw [hrow i hi]
      split_ifs with hle
      · omega
      · have : part m (durfee m + i) = 0 := by
          rw [part]; exact List.getD_eq_default _ _ (by omega)
        rw [this]
        exact ⟨False.elim, fun h => by omega⟩
    cases hs : stack m s with
    | none =>
      rw [Option.bind_none]
      unfold stack at hs ⊢
      rw [hdx]
      split_ifs at hs with h1
      split_ifs with h2
      · exfalso
        apply h1
        refine ⟨fun i hi => (hiff i (Finset.mem_Icc.1 hi).1).1 (h2.1 i hi), ?_⟩
        have := h2.2
        rw [hrow0] at this
        omega
      · rfl
    | some w =>
      obtain ⟨hks, hlw, hpw⟩ := stack_facts he hs
      rw [Option.bind_some, stack_hook w hc, if_pos ⟨by omega, by omega⟩]
      unfold stack at hs ⊢
      rw [hdx]
      split_ifs at hs with h1
      obtain rfl := Option.some.inj hs
      rw [if_pos ⟨fun i hi => (hiff i (Finset.mem_Icc.1 hi).1).2 (h1.1 i hi),
        by rw [hrow0]; have := h1.2; omega⟩]
      exact congrArg some (hookStack_stack_eq hcond.1 hks)
  · rw [if_neg hcond, Option.bind_none]
    cases hs : stack m s with
    | none => rfl
    | some w =>
      obtain ⟨-, hlw, hpw⟩ := stack_facts he hs
      rw [Option.bind_some, stack_hook w hc, if_neg (by rw [hlw, hpw]; exact hcond)]

/-! ### Bracketings -/

/-- `nest [r₁, …, r_j] p = Γ_{r₁,r₁} ◁ (Γ_{r₂,r₂} ◁ (⋯ ◁ (Γ_{r_j,r_j} ◁ p)))`, or `none` if some
stack is undefined. -/
def nest : List ℕ → List ℕ → Option (List ℕ)
  | [], p => some p
  | r :: rs, p => (nest rs p).bind (stack (hook r r))

theorem nest_append (A B p : List ℕ) : nest (A ++ B) p = (nest B p).bind (nest A) := by
  induction A with
  | nil => rw [List.nil_append]; cases nest B p <;> rfl
  | cons r A ih => simp only [List.cons_append, nest, ih, Option.bind_assoc]

theorem nest_isPartition {p : List ℕ} (hp : IsPartition p) (hne : p ≠ []) :
    ∀ {rs l : List ℕ}, (∀ r ∈ rs, 1 ≤ r) → nest rs p = some l → IsPartition l ∧ l ≠ []
  | [], l, _, h => by
    simp only [nest, Option.some.injEq] at h
    exact h ▸ ⟨hp, hne⟩
  | r :: rs, l, hr, h => by
    simp only [nest] at h
    obtain ⟨y, hy, hyl⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hyp, -⟩ := nest_isPartition hp hne (fun r' h' => hr r' (by simp [h'])) hy
    rw [stack_hook y (hr r (by simp))] at hyl
    split_ifs at hyl with hc
    obtain rfl := Option.some.inj hyl
    exact ⟨isPartition_hookStack hyp hc.2, by simp [hookStack]⟩

/-- Moving a stack on the inside out of a nest of hooks. -/
theorem nest_assoc : ∀ {rs : List ℕ}, (∀ r ∈ rs, 1 ≤ r) → ∀ {p : List ℕ}, IsPartition p →
    p ≠ [] → ∀ s : List ℕ, (nest rs p).bind (fun x => stack x s) = (stack p s).bind (nest rs)
  | [], _, p, _, _, s => by simp only [nest, Option.bind_some]; cases stack p s <;> rfl
  | r :: rs, hr, p, hp, hne, s => by
    have hr' : ∀ r' ∈ rs, 1 ≤ r' := fun r' h' => hr r' (by simp [h'])
    calc ((nest rs p).bind (stack (hook r r))).bind (fun x => stack x s)
        = (nest rs p).bind (fun y => (stack (hook r r) y).bind (fun x => stack x s)) :=
          Option.bind_assoc _ _ _
      _ = (nest rs p).bind (fun y => (stack y s).bind (stack (hook r r))) := by
          cases hy : nest rs p with
          | none => rfl
          | some y =>
            obtain ⟨hyp, hyne⟩ := nest_isPartition hp hne hr' hy
            simp only [Option.bind_some]
            exact stack_hook_assoc (hr r (by simp)) hyp hyne s
      _ = ((nest rs p).bind (fun x => stack x s)).bind (stack (hook r r)) :=
          (Option.bind_assoc _ _ _).symm
      _ = ((stack p s).bind (nest rs)).bind (stack (hook r r)) := by
          rw [nest_assoc hr' hp hne s]
      _ = (stack p s).bind (nest (r :: rs)) := Option.bind_assoc _ _ _

/-- A bracketing of a stack of hooks `Γ_{r,r}`; the leaves, read from left to right, are the
hooks from the outside in, and `node t u` is the stack `t ◁ u`. -/
inductive HookTree
  | leaf (r : ℕ)
  | node (t u : HookTree)

namespace HookTree

/-- The stack that a bracketing denotes, or `none` if some stack in it is undefined. -/
def eval : HookTree → Option (List ℕ)
  | leaf r => some (hook r r)
  | node t u => t.eval.bind fun x => u.eval.bind (stack x)

/-- The last (innermost) leaf. -/
def last : HookTree → ℕ
  | leaf r => r
  | node _ u => u.last

/-- The leaves before the last one, from left to right. -/
def init : HookTree → List ℕ
  | leaf _ => []
  | node t u => t.init ++ t.last :: u.init

/-- Every leaf satisfies `P`. -/
def All (P : ℕ → Prop) : HookTree → Prop
  | leaf r => P r
  | node t u => t.All P ∧ u.All P

theorem all_iff {P : ℕ → Prop} : ∀ {T : HookTree}, T.All P ↔ (∀ r ∈ T.init, P r) ∧ P T.last
  | leaf r => by simp [All, init, last]
  | node t u => by
    simp only [All, init, last, all_iff (T := t), all_iff (T := u), List.mem_append,
      List.mem_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨fun r hr => by rcases hr with hr | rfl | hr <;> solve_by_elim, h4⟩
    · rintro ⟨h, h4⟩
      exact ⟨⟨fun r hr => h r (Or.inl hr), h _ (Or.inr (Or.inl rfl))⟩,
        fun r hr => h r (Or.inr (Or.inr hr)), h4⟩

/-- Every bracketing gives the right-nested stack. -/
theorem eval_eq_nest : ∀ {T : HookTree}, T.All (1 ≤ ·) →
    T.eval = nest T.init (hook T.last T.last)
  | leaf _, _ => rfl
  | node t u, ⟨ht, hu⟩ => by
    have htl : 1 ≤ t.last := (all_iff.1 ht).2
    simp only [eval, init, last, eval_eq_nest ht, eval_eq_nest hu, nest_append, nest]
    rw [Option.bind_comm]
    simp only [nest_assoc (all_iff.1 ht).1 (isPartition_hook htl) (by simp [hook])]
    rw [Option.bind_assoc]

end HookTree

theorem oddHookStack_iff_nest {l : List ℕ} :
    OddHookStack l ↔ ∃ rs : List ℕ, (∀ r ∈ rs, Odd r) ∧ nest rs [1] = some l := by
  constructor
  · intro h
    induction h with
    | base => exact ⟨[], by simp, rfl⟩
    | @step r m s hr _ hs ih =>
      obtain ⟨rs, hrs, hn⟩ := ih
      exact ⟨r :: rs, List.forall_mem_cons.2 ⟨hr, hrs⟩, by simp [nest, hn, hs]⟩
  · rintro ⟨rs, hrs, hn⟩
    induction rs generalizing l with
    | nil =>
      simp only [nest, Option.some.injEq] at hn
      exact hn ▸ OddHookStack.base
    | cons r rs ih =>
      simp only [nest] at hn
      obtain ⟨m, hm, hml⟩ := Option.bind_eq_some_iff.1 hn
      exact OddHookStack.step (hrs r (by simp)) (ih (fun r' h' => hrs r' (by simp [h'])) hm) hml

theorem exists_comb : ∀ rs : List ℕ, (∀ r ∈ rs, Odd r) →
    ∃ T : HookTree, T.init = rs ∧ T.last = 1 ∧ T.All Odd
  | [], _ => ⟨.leaf 1, rfl, rfl, odd_one⟩
  | r :: rs, h => by
    obtain ⟨T, h1, h2, h3⟩ := exists_comb rs (fun r' h' => h r' (by simp [h']))
    exact ⟨.node (.leaf r) T, by simp [HookTree.init, HookTree.last, h1], h2, h r (by simp), h3⟩

/-- **Any bracketing**: a partition is a stack of odd self-conjugate hooks and `[1]`, bracketed
in some way with every intermediate stack defined, iff it is one in the right-nested reading. -/
theorem exists_hookTree_iff {l : List ℕ} :
    (∃ T : HookTree, T.All Odd ∧ T.last = 1 ∧ T.eval = some l) ↔ OddHookStack l := by
  rw [oddHookStack_iff_nest]
  have hpos : ∀ {T : HookTree}, T.All Odd → T.All (1 ≤ ·) := fun hT =>
    HookTree.all_iff.2 ⟨fun r hr => (HookTree.all_iff.1 hT).1 r hr |>.pos,
      (HookTree.all_iff.1 hT).2.pos⟩
  constructor
  · rintro ⟨T, hT, hl, he⟩
    rw [HookTree.eval_eq_nest (hpos hT), hl] at he
    exact ⟨T.init, (HookTree.all_iff.1 hT).1, he⟩
  · rintro ⟨rs, hrs, hn⟩
    obtain ⟨T, hTi, hTl, hTa⟩ := exists_comb rs hrs
    refine ⟨T, hTa, hTl, ?_⟩
    rw [HookTree.eval_eq_nest (hpos hTa), hTi, hTl]
    exact hn

/-- conj:pself with the stack in any bracketing. -/
theorem pselfConjecture_anyBracketing {l : List ℕ} (hl : IsPartition l)
    (hp : ParitySelfConj l) :
    ¬ IsP l ↔ ∃ T : HookTree, T.All Odd ∧ T.last = 1 ∧ T.eval = some l := by
  rw [exists_hookTree_iff]
  exact pselfConjecture_holds l hl hp

/-! ## Misère play

Under misère play the player who cannot move wins, so `[]` is an N-position. Write `Z` for
Zeng's normal-play P-condition `Even (plen p) ∧ Even (endM p)` and `C` for the cover condition
`k ≤ L + R` (the A-good prefix and the B-good suffix cover all `k` run pairs). The misère
P-positions are `Z xor C` (`misere_classification`, `misereP_iff`). -/

/-- Misère P-positions of CRIM: `[]` is not one (the player to move cannot move, and wins), and
a nonempty position is one iff no move reaches one. -/
def isMP (l : List ℕ) : Bool :=
  !l.isEmpty && (moves l).attach.all fun ⟨m, _⟩ => !isMP m
termination_by l.sum + l.length
decreasing_by exact lt_of_mem_moves ‹_›

/-- `l` is a misère P-position. -/
def IsMP (l : List ℕ) : Prop := isMP l = true

theorem isMP_iff (l : List ℕ) : IsMP l ↔ l ≠ [] ∧ ∀ m ∈ moves l, ¬ IsMP m := by
  unfold IsMP
  rw [isMP]
  simp [List.all_eq_true]

/-- The misère P-condition on run pairs: `Z xor C`. -/
def MisP (p : List (ℕ × ℕ)) : Prop :=
  Xor (Even (plen p) ∧ Even (endM p)) (p.length ≤ endL p + endR p)

theorem cover_iff (p : List (ℕ × ℕ)) : p.length ≤ endL p + endR p ↔ endM p = p.length := by
  unfold endM
  omega

/-- A covered position has even `plen`: an odd one splits with a nonempty core. -/
theorem even_plen_of_cover {p : List (ℕ × ℕ)} (h : p.length ≤ endL p + endR p) :
    Even (plen p) := by
  by_contra hodd
  obtain ⟨P, C, S, rfl, hs⟩ := RunPairs.exists_split hodd
  rw [hs.endL_eq, hs.endR_eq] at h
  obtain ⟨c, C', rfl, -⟩ := hs.core_head
  simp only [List.length_append, List.length_cons] at h
  omega

theorem even_plen_of_misP {p : List (ℕ × ℕ)} (h : MisP p) : Even (plen p) := by
  rcases h with ⟨⟨h, -⟩, -⟩ | ⟨h, -⟩
  · exact h
  · exact even_plen_of_cover h

theorem ne_nil_of_misP {p : List (ℕ × ℕ)} (h : MisP p) : p ≠ [] := by
  rintro rfl
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact h (Nat.zero_le _)
  · exact h ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩

/-- A move between even positions is an end-peel, so it shortens the list by one. -/
theorem length_eq_of_even {p q : List (ℕ × ℕ)} (h : PMove p q) (hp : Even (plen p))
    (hq : Even (plen q)) : p.length = q.length + 1 := by
  rw [Nat.even_iff] at hp hq
  cases h <;> simp only [RunPairs.plen_append, RunPairs.plen_cons, RunPairs.plen_nil,
    List.length_append, List.length_cons, List.length_nil] at hp hq ⊢ <;> omega

/-- Along an end-peel `Z` flips and `C` is kept, so `Z xor C` flips. -/
theorem misP_iff_of_succ {q q' : List (ℕ × ℕ)} (he : Even (plen q)) (he' : Even (plen q'))
    (hM : endM q' = endM q + 1) (hl : q'.length = q.length + 1) : MisP q' ↔ ¬ MisP q := by
  unfold MisP
  rw [cover_iff, cover_iff, hM, hl, Nat.add_right_cancel_iff]
  simp only [he, he', true_and, Nat.even_add_one]
  unfold Xor
  tauto

theorem misP_iff_of_move {p q : List (ℕ × ℕ)} (h : PMove p q) (hp : Even (plen p))
    (hq : Even (plen q)) : MisP p ↔ ¬ MisP q :=
  misP_iff_of_succ hq hp (RunPairs.endM_eq_of_even h hp hq) (length_eq_of_even h hp hq)

theorem misP_pdual (l : List (ℕ × ℕ)) : MisP (RunPairs.pdual l) ↔ MisP l := by
  unfold MisP
  rw [RunPairs.plen_pdual, RunPairs.endM_pdual, RunPairs.length_pdual, RunPairs.endL_pdual,
    RunPairs.endR_pdual, Nat.add_comm (endR l)]

/-- A move to a predicted misère P-position. -/
def MGood (p : List (ℕ × ℕ)) : Prop := ∃ q, PMove p q ∧ MisP q

theorem MGood.of_pdual {p : List (ℕ × ℕ)} (h : MGood (RunPairs.pdual p)) : MGood p := by
  obtain ⟨q, hq, hM⟩ := h
  refine ⟨RunPairs.pdual q, ?_, (misP_pdual q).2 hM⟩
  simpa [RunPairs.pdual_pdual] using RunPairs.PMove.pdual hq

theorem exists_peel_of_endL {p : List (ℕ × ℕ)} (hp : Even (plen p)) (hL : 1 ≤ endL p) :
    ∃ q, PMove p q ∧ Even (plen q) := by
  obtain _ | ⟨x, B⟩ := p
  · simp [RunPairs.endL_nil] at hL
  rw [RunPairs.endL_cons] at hL
  have hx : AGood x = true := by
    by_contra hx
    rw [if_neg hx] at hL
    omega
  obtain ⟨a, b⟩ := x
  obtain ⟨rfl, hb⟩ := (RunPairs.aGood_iff _).1 hx
  refine ⟨B, PMove.zeroFirst B b, ?_⟩
  rw [Nat.even_iff] at hp ⊢
  rw [RunPairs.plen_cons] at hp
  simp only at hp hb
  omega

/-- An even position with `M ≥ 1` has an end-peel to an even position. -/
theorem exists_peel {p : List (ℕ × ℕ)} (hp : Even (plen p)) (hM : 1 ≤ endM p) :
    ∃ q, PMove p q ∧ Even (plen q) := by
  have h1 : 1 ≤ endL p ∨ 1 ≤ endR p := by
    unfold endM at hM
    omega
  rcases h1 with h1 | h1
  · exact exists_peel_of_endL hp h1
  · obtain ⟨q, hq, he⟩ := exists_peel_of_endL (p := RunPairs.pdual p)
      (by rwa [RunPairs.plen_pdual]) (by rwa [RunPairs.endL_pdual])
    refine ⟨RunPairs.pdual q, ?_, by rwa [RunPairs.plen_pdual]⟩
    simpa [RunPairs.pdual_pdual] using RunPairs.PMove.pdual hq

/-- An even split position with `L + R` even satisfies `Z` and, having a core, not `C`. -/
theorem misP_of_split {q P C S : List (ℕ × ℕ)} (hq : q = P ++ C ++ S)
    (h : RunPairs.Split P C S) (he : plen q % 2 = 0) (hLR : (P.length + S.length) % 2 = 0) :
    MisP q := by
  subst hq
  refine Or.inl ⟨⟨Nat.even_iff.2 he, ?_⟩, ?_⟩
  · rw [h.endM_eq, Nat.even_iff]
    exact hLR
  · rw [h.endL_eq, h.endR_eq]
    obtain ⟨c, C', rfl, -⟩ := h.core_head
    simp only [List.length_append, List.length_cons]
    omega

/-- A covered position with an odd number of pairs satisfies `C` and not `Z`. -/
theorem misP_of_good {P S : List (ℕ × ℕ)} (hP : ∀ x ∈ P, AGood x = true)
    (hS : ∀ x ∈ S, BGood x = true) (hk : (P.length + S.length) % 2 = 1) : MisP (P ++ S) := by
  have hM := RunPairs.endM_of_good hP hS
  refine Or.inr ⟨(cover_iff _).2 (by rw [hM, List.length_append]), fun hZ => ?_⟩
  obtain ⟨-, hZ⟩ := hZ
  rw [hM, Nat.even_iff] at hZ
  omega

/-! ### Odd positions: a move into `Z xor C`

This follows `RunPairs.goodMove_of_odd` (Zeng's Lemma 7.4). Every move there reaches `Z`; it
also avoids `C` except in three cases, changed below (`mgood_core_one_odd`,
`mgood_core_one_even`, and the case `a = 1` of `mgood_core_long`). -/

/-- "Reduce A" (`L + R` odd): delete a `1` from the last pair of the A-good prefix. -/
theorem mgood_reduceA {P C S : List (ℕ × ℕ)} (h : RunPairs.Split P C S)
    (hv : ValidPairs (P ++ C ++ S)) (hodd : plen (P ++ C ++ S) % 2 = 1)
    (hLR : (P.length + S.length) % 2 = 1) (hP : P ≠ [])
    (hC : ∀ a, C = [(a, 1)] → a % 2 = 1) : MGood (P ++ C ++ S) := by
  obtain ⟨P₀, b', rfl, hb', hP₀⟩ := RunPairs.exists_last_aGood h.prefix_good hP
  obtain ⟨⟨a, b⟩, C', rfl, hc⟩ := h.core_head
  have hab := hv (a, b) (by simp)
  simp only at hab
  simp only [List.length_append, List.length_singleton] at hLR
  rcases Nat.lt_or_ge b' 2 with hb1 | hb2
  · -- `b' = 1`: the pair `(1, 1)` merges into the first core pair
    obtain rfl : b' = 1 := by omega
    have hs : RunPairs.Split P₀ ((1 + a, b) :: C') S := by
      refine ⟨hP₀, h.suffix_good, ⟨_, _, rfl, RunPairs.not_aGood_of (by simp only; omega)⟩,
        ?_⟩
      rcases eq_or_ne C' [] with rfl | hC'
      · refine ⟨[], (1 + a, b), rfl, RunPairs.not_bGood_of ?_⟩
        simp only
        rcases eq_or_ne b 1 with rfl | hb
        · have := hC a rfl
          omega
        · exact Or.inr hb
      · exact RunPairs.core_last_cons hC' h.core_last
    refine ⟨P₀ ++ (1 + a, b) :: (C' ++ S),
      RunPairs.PMove.of_eq (PMove.oneMerge P₀ (C' ++ S) 1 a b) (by simp) rfl,
      misP_of_split (by simp) hs ?_ (by omega)⟩
    simp only [RunPairs.plen_append, RunPairs.plen_cons, RunPairs.plen_nil] at hodd ⊢
    omega
  · -- `b' ≥ 3`: the pair `(1, b')` becomes `(1, b' - 1)`, which is neither A- nor B-good
    have hs : RunPairs.Split P₀ ((1, b' - 1) :: (a, b) :: C') S := by
      refine ⟨hP₀, h.suffix_good, ⟨_, _, rfl, RunPairs.not_aGood_of (by simp only; omega)⟩,
        ?_⟩
      obtain ⟨C'', d, hC'', hd⟩ := h.core_last
      exact ⟨(1, b' - 1) :: C'', d, by rw [hC'']; rfl, hd⟩
    refine ⟨P₀ ++ (1, b' - 1) :: ((a, b) :: C' ++ S),
      RunPairs.PMove.of_eq (PMove.oneDec P₀ ((a, b) :: C' ++ S) 1 b' hb2) (by simp) rfl,
      misP_of_split (by simp) hs ?_ (by omega)⟩
    simp only [RunPairs.plen_append, RunPairs.plen_cons, RunPairs.plen_nil] at hodd ⊢
    omega

/-- Core `(1, b)`, empty A-good prefix and `R` odd: delete the core's `0`, leaving the B-good
suffix (changed: normal play deletes a `1`). -/
theorem mgood_core_one_odd {S : List (ℕ × ℕ)} {b : ℕ} (h : RunPairs.Split [] [(1, b)] S)
    (hS : S.length % 2 = 1) : MGood ([] ++ [(1, b)] ++ S) := by
  refine ⟨S, RunPairs.PMove.of_eq (PMove.zeroFirst S b) (by simp) rfl, ?_⟩
  simpa using misP_of_good (P := []) (fun x hx => by simp at hx) h.suffix_good
    (by simpa using hS)

/-- Core `(1, b)` with `b` even and `L + R` even: delete a `1`, which makes the core A-good
(changed: normal play deletes the `0`). -/
theorem mgood_core_one_even {P S : List (ℕ × ℕ)} {b : ℕ} (h : RunPairs.Split P [(1, b)] S)
    (hv : ValidPairs (P ++ [(1, b)] ++ S)) (hLR : (P.length + S.length) % 2 = 0)
    (hb : b % 2 = 0) : MGood (P ++ [(1, b)] ++ S) := by
  have hb1 := (hv (1, b) (by simp)).2
  simp only at hb1
  have hg : ∀ x ∈ P ++ [(1, b - 1)], AGood x = true := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h.prefix_good x hx
    · rw [List.mem_singleton.1 hx, RunPairs.aGood_iff]
      exact ⟨rfl, by simp only; omega⟩
  refine ⟨P ++ [(1, b - 1)] ++ S,
    RunPairs.PMove.of_eq (PMove.oneDec P S 1 b (by omega)) (by simp) (by simp),
    misP_of_good hg h.suffix_good ?_⟩
  simp only [List.length_append, List.length_singleton]
  omega

/-- Core `(a, b)` with `a ≥ 3` odd and `b` even (`L + R` even): delete a `0`. -/
theorem mgood_core_odd_even {P S : List (ℕ × ℕ)} {a b : ℕ} (h : RunPairs.Split P [(a, b)] S)
    (hodd : plen (P ++ [(a, b)] ++ S) % 2 = 1)
    (hLR : (P.length + S.length) % 2 = 0) (ha : 3 ≤ a) (ha2 : a % 2 = 1) :
    MGood (P ++ [(a, b)] ++ S) := by
  have hs : RunPairs.Split P [(a - 1, b)] S :=
    ⟨h.prefix_good, h.suffix_good, ⟨_, _, rfl, RunPairs.not_aGood_of (by simp only; omega)⟩,
      ⟨[], _, rfl, RunPairs.not_bGood_of (by simp only; omega)⟩⟩
  refine ⟨P ++ [(a - 1, b)] ++ S,
    RunPairs.PMove.of_eq (PMove.zeroDec P S a b (by omega)) (by simp) (by simp),
    misP_of_split rfl hs ?_ hLR⟩
  simp only [RunPairs.plen_append, RunPairs.plen_cons, RunPairs.plen_nil] at hodd ⊢
  omega

/-- A core of length `≥ 2` with `L + R` even: change its first pair. For a first pair `(1, b)`
(changed) the two moves "delete the `0`" and "delete a `1`" reach consecutive values of `M`
and of the length, so exactly one of them lands in `Z xor C`. -/
theorem mgood_core_long {P C₁ S : List (ℕ × ℕ)} {a b : ℕ}
    (h : RunPairs.Split P ((a, b) :: C₁) S) (hv : ValidPairs (P ++ (a, b) :: C₁ ++ S))
    (hodd : plen (P ++ (a, b) :: C₁ ++ S) % 2 = 1)
    (hLR : (P.length + S.length) % 2 = 0) (hC₁ : C₁ ≠ []) :
    MGood (P ++ (a, b) :: C₁ ++ S) := by
  have hab := hv (a, b) (by simp)
  simp only at hab
  have hcA : AGood (a, b) = false := by
    obtain ⟨c, C', hc, hcA⟩ := h.core_head
    simp only [List.cons.injEq] at hc
    rw [hc.1]
    exact hcA
  rw [Bool.eq_false_iff, ne_eq, RunPairs.aGood_iff] at hcA
  simp only at hcA
  obtain ⟨C₁', d, hC₁e, hd⟩ : ∃ C₁' d, C₁ = C₁' ++ [d] ∧ BGood d = false := by
    obtain ⟨C'', d, hC'', hd⟩ := h.core_last
    obtain ⟨l₂, hl₂⟩ := RunPairs.exists_eq_append_single hC'' hC₁
    exact ⟨l₂, d, hl₂, hd⟩
  have hplen : ∀ q, plen q + 1 = plen (P ++ (a, b) :: C₁ ++ S) → plen q % 2 = 0 := by
    intro q hq
    omega
  have keep : ∀ c' : ℕ × ℕ, AGood c' = false →
      plen (P ++ c' :: (C₁ ++ S)) + 1 = plen (P ++ (a, b) :: C₁ ++ S) →
      MisP (P ++ c' :: (C₁ ++ S)) := fun c' hc' hpl =>
    misP_of_split (by simp)
      ⟨h.prefix_good, h.suffix_good, ⟨c', C₁, rfl, hc'⟩, RunPairs.core_last_cons hC₁ h.core_last⟩
      (hplen _ hpl) hLR
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · -- `a = 1` and `b` even: deleting the `0` or a `1` gives consecutive values of `M`
    obtain rfl : a = 1 := by omega
    have hb : b % 2 = 0 := by omega
    obtain ⟨q0, hq0, hq0e, hq0M, hq0l⟩ : ∃ q0, PMove (P ++ (1, b) :: C₁ ++ S) q0 ∧
        Even (plen q0) ∧ endM q0 = min (P.length + (C₁'.length + 1 + S.length))
          (P.length + endL (C₁' ++ [d] ++ S) + S.length) ∧
        q0.length = P.length + (C₁'.length + 1 + S.length) := by
      rcases eq_or_ne P [] with rfl | hP
      · refine ⟨C₁ ++ S, RunPairs.PMove.of_eq (PMove.zeroFirst (C₁ ++ S) b) (by simp) rfl,
          ?_, ?_, ?_⟩
        · rw [Nat.even_iff]
          simp only [RunPairs.plen_append, RunPairs.plen_cons, List.nil_append] at hodd ⊢
          omega
        · have := RunPairs.endM_prefix_barrier (X := []) (Y := C₁') (fun x hx => by simp at hx)
            h.suffix_good hd
          rw [hC₁e]
          simpa using this
        · simp only [hC₁e, List.length_append, List.length_singleton, List.length_nil]
          omega
      · obtain ⟨P₀, b', rfl, hb', hP₀⟩ := RunPairs.exists_last_aGood h.prefix_good hP
        have hg : ∀ x ∈ P₀ ++ [(1, b' + b)], AGood x = true := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hP₀ x hx
          · rw [List.mem_singleton.1 hx, RunPairs.aGood_iff]
            exact ⟨rfl, by simp only; omega⟩
        have he : P₀ ++ (1, b' + b) :: (C₁ ++ S) = P₀ ++ [(1, b' + b)] ++ (C₁' ++ [d] ++ S) := by
          rw [hC₁e]
          simp
        refine ⟨P₀ ++ (1, b' + b) :: (C₁ ++ S),
          RunPairs.PMove.of_eq (PMove.zeroMerge P₀ (C₁ ++ S) 1 b' b) (by simp) rfl, ?_, ?_, ?_⟩
        · rw [Nat.even_iff]
          simp only [RunPairs.plen_append, RunPairs.plen_cons, RunPairs.plen_nil] at hodd ⊢
          omega
        · rw [he, RunPairs.endM_prefix_barrier hg h.suffix_good hd]
          simp only [List.length_append, List.length_singleton]
        · rw [he]
          simp only [List.length_append, List.length_singleton]
    have hg : ∀ x ∈ P ++ [(1, b - 1)], AGood x = true := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h.prefix_good x hx
      · rw [List.mem_singleton.1 hx, RunPairs.aGood_iff]
        exact ⟨rfl, by simp only; omega⟩
    have he : P ++ (1, b - 1) :: (C₁ ++ S) = P ++ [(1, b - 1)] ++ (C₁' ++ [d] ++ S) := by
      rw [hC₁e]
      simp
    have hq1 : PMove (P ++ (1, b) :: C₁ ++ S) (P ++ (1, b - 1) :: (C₁ ++ S)) :=
      RunPairs.PMove.of_eq (PMove.oneDec P (C₁ ++ S) 1 b (by omega)) (by simp) rfl
    have hq1e : Even (plen (P ++ (1, b - 1) :: (C₁ ++ S))) := by
      rw [Nat.even_iff]
      exact hplen _ (by simp only [RunPairs.plen_append, RunPairs.plen_cons]; omega)
    have hq1M : endM (P ++ (1, b - 1) :: (C₁ ++ S)) = endM q0 + 1 := by
      rw [he, RunPairs.endM_prefix_barrier hg h.suffix_good hd, hq0M]
      simp only [List.length_append, List.length_singleton]
      omega
    have hq1l : (P ++ (1, b - 1) :: (C₁ ++ S)).length = q0.length + 1 := by
      rw [he, hq0l]
      simp only [List.length_append, List.length_singleton]
      omega
    by_cases hm : MisP q0
    · exact ⟨q0, hq0, hm⟩
    · exact ⟨_, hq1, (misP_iff_of_succ hq0e hq1e hq1M hq1l).2 hm⟩
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · obtain rfl : a = 2 := by omega
    rcases Nat.lt_or_ge b 2 with hb1 | hb2
    · -- the pair `(2, 1)`: delete its `1`, merging it into the next core pair
      obtain rfl : b = 1 := by omega
      obtain ⟨⟨a', b'⟩, C₂, rfl⟩ := List.exists_cons_of_ne_nil hC₁
      have hs : RunPairs.Split P ((2 + a', b') :: C₂) S := by
        refine ⟨h.prefix_good, h.suffix_good,
          ⟨_, _, rfl, RunPairs.not_aGood_of (by simp only; omega)⟩, ?_⟩
        rcases eq_or_ne C₂ [] with rfl | hC₂
        · have : d = (a', b') := by
            have := congrArg List.getLast? hC₁e
            simpa using this.symm
          subst this
          refine ⟨[], _, rfl, RunPairs.not_bGood_of ?_⟩
          rw [Bool.eq_false_iff, ne_eq, RunPairs.bGood_iff] at hd
          simp only at hd ⊢
          omega
        · obtain ⟨C'', e, hC'', he⟩ := h.core_last
          obtain ⟨l₂, hl₂⟩ := RunPairs.exists_eq_append_single hC'' hC₁
          exact RunPairs.core_last_cons hC₂ ⟨l₂, e, hl₂, he⟩
      exact ⟨P ++ (2 + a', b') :: (C₂ ++ S),
        RunPairs.PMove.of_eq (PMove.oneMerge P (C₂ ++ S) 2 a' b') (by simp) rfl,
        misP_of_split (by simp) hs
          (hplen _ (by simp only [RunPairs.plen_append, RunPairs.plen_cons]; omega)) hLR⟩
    · rcases Nat.even_or_odd b with hb | hb
      · -- `(2, b)` with `b` even: delete a `0`
        rw [Nat.even_iff] at hb
        exact ⟨P ++ (2 - 1, b) :: (C₁ ++ S),
          RunPairs.PMove.of_eq (PMove.zeroDec P (C₁ ++ S) 2 b le_rfl) (by simp) rfl,
          keep _ (RunPairs.not_aGood_of (by simp only; omega))
            (by simp only [RunPairs.plen_append, RunPairs.plen_cons]; omega)⟩
      · -- `(2, b)` with `b ≥ 3` odd: delete a `1`
        exact ⟨P ++ (2, b - 1) :: (C₁ ++ S),
          RunPairs.PMove.of_eq (PMove.oneDec P (C₁ ++ S) 2 b hb2) (by simp) rfl,
          keep _ (RunPairs.not_aGood_of (by simp only; omega))
            (by simp only [RunPairs.plen_append, RunPairs.plen_cons]; omega)⟩
  · -- `a ≥ 3`: delete a `0`
    exact ⟨P ++ (a - 1, b) :: (C₁ ++ S),
      RunPairs.PMove.of_eq (PMove.zeroDec P (C₁ ++ S) a b (by omega)) (by simp) rfl,
      keep _ (RunPairs.not_aGood_of (by simp only; omega))
        (by simp only [RunPairs.plen_append, RunPairs.plen_cons]; omega)⟩

/-- Every odd position has a move into `Z xor C` (Zeng's Lemma 7.4, adapted). -/
theorem mgood_of_odd {p : List (ℕ × ℕ)} (hv : ValidPairs p) (hodd : ¬ Even (plen p)) :
    MGood p := by
  obtain ⟨P, C, S, rfl, h⟩ := RunPairs.exists_split hodd
  rw [Nat.not_even_iff] at hodd
  have hd : RunPairs.pdual (P ++ C ++ S) =
      RunPairs.pdual S ++ RunPairs.pdual C ++ RunPairs.pdual P := by
    simp only [RunPairs.pdual_append, List.append_assoc]
  have hvd : ValidPairs (RunPairs.pdual S ++ RunPairs.pdual C ++ RunPairs.pdual P) :=
    hd ▸ RunPairs.validPairs_pdual hv
  have hoddd : plen (RunPairs.pdual S ++ RunPairs.pdual C ++ RunPairs.pdual P) % 2 = 1 := by
    rw [← hd, RunPairs.plen_pdual]
    exact hodd
  have hsd := h.pdual
  have dual : MGood (RunPairs.pdual S ++ RunPairs.pdual C ++ RunPairs.pdual P) →
      MGood (P ++ C ++ S) :=
    fun g => MGood.of_pdual (hd ▸ g)
  have hlen : (RunPairs.pdual S).length + (RunPairs.pdual P).length = P.length + S.length := by
    rw [RunPairs.length_pdual, RunPairs.length_pdual]
    omega
  obtain ⟨hPe, hSe⟩ := RunPairs.plen_even_of_split h
  have hCo : plen C % 2 = 1 := by
    rw [RunPairs.plen_append, RunPairs.plen_append] at hodd
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
      rw [Bool.eq_false_iff, ne_eq, RunPairs.aGood_iff] at hcA
      rw [Bool.eq_false_iff, ne_eq, RunPairs.bGood_iff] at hcB
      simp only [RunPairs.plen_cons, RunPairs.plen_nil] at hCo hcA hcB
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · -- `a` even and `b` odd: the dual of the two cases below
        apply dual
        rw [RunPairs.pdual_single] at hsd hvd hoddd ⊢
        rcases Nat.lt_or_ge b 2 with hb1 | hb3
        · obtain rfl : b = 1 := by omega
          exact mgood_core_one_even hsd hvd (by omega) ha
        · exact mgood_core_odd_even hsd hoddd (by omega) (by omega) (by omega)
      · rcases Nat.lt_or_ge a 2 with ha1 | ha3
        · obtain rfl : a = 1 := by omega
          exact mgood_core_one_even h hv hLR (by omega)
        · exact mgood_core_odd_even h hodd hLR (by omega) ha
    · exact mgood_core_long h hv hodd hLR hC₁
  · -- `L + R` odd
    by_cases hA : P ≠ [] ∧ ∀ a', (a, b) :: C₁ = [(a', 1)] → a' % 2 = 1
    · exact mgood_reduceA h hv hodd hLR hA.1 hA.2
    by_cases hB : S ≠ [] ∧ ∀ a', RunPairs.pdual ((a, b) :: C₁) = [(a', 1)] → a' % 2 = 1
    · apply dual
      refine mgood_reduceA hsd hvd hoddd (by omega) ?_ hB.2
      intro hS
      apply hB.1
      simpa [RunPairs.pdual] using hS
    -- the remaining cases: a single core pair `(1, even)` first or `(even, 1)` last
    rcases eq_or_ne P [] with rfl | hP
    · have hS : S ≠ [] := by
        rintro rfl
        simp at hLR
      push Not at hB
      obtain ⟨a', ha'1, ha'2⟩ := hB hS
      obtain ⟨rfl, rfl, rfl⟩ := RunPairs.pdual_cons_eq_single ha'1
      exact mgood_core_one_odd h (by simpa using hLR)
    · push Not at hA
      obtain ⟨a', ha'1, ha'2⟩ := hA hP
      simp only [List.cons.injEq, Prod.mk.injEq] at ha'1
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ha'1
      have hS : S = [] := by
        by_contra hS
        refine hB ⟨hS, fun a'' h'' => ?_⟩
        simp [RunPairs.pdual_single] at h''
        omega
      subst hS
      apply dual
      simp only [RunPairs.pdual_single, RunPairs.pdual_nil] at hsd ⊢
      exact mgood_core_one_odd hsd (by rw [RunPairs.length_pdual]; simpa using hLR)

/-- From a nonempty position outside `Z xor C` there is a move into it. -/
theorem exists_misP_move {p : List (ℕ × ℕ)} (hv : ValidPairs p) (hne : p ≠ [])
    (h : ¬ MisP p) : MGood p := by
  by_cases he : Even (plen p)
  · have hM : 1 ≤ endM p := by
      by_contra hM
      apply h
      have h0 : endM p = 0 := by omega
      refine Or.inl ⟨⟨he, by rw [h0]; exact ⟨0, rfl⟩⟩, ?_⟩
      rw [cover_iff, h0]
      exact fun h1 => hne (List.eq_nil_of_length_eq_zero h1.symm)
    obtain ⟨q, hq, hqe⟩ := exists_peel he hM
    refine ⟨q, hq, ?_⟩
    by_contra hq'
    exact h ((misP_iff_of_move hq he hqe).2 hq')
  · exact mgood_of_odd hv he

/-- No move leads from `Z xor C` back into it. -/
theorem not_misP_move {p q : List (ℕ × ℕ)} (hM : MisP p) (hq : PMove p q) : ¬ MisP q :=
  fun hMq => (misP_iff_of_move hq (even_plen_of_misP hM) (even_plen_of_misP hMq)).1 hM hMq

/-- **Misère classification** on run pairs: any `G` satisfying the misère recursion is
`Z xor C`. -/
theorem misere_classification (G : List (ℕ × ℕ) → Prop)
    (hG : ∀ p, ValidPairs p → (G p ↔ p ≠ [] ∧ ∀ q, PMove p q → ¬ G q)) :
    ∀ p, ValidPairs p →
      (G p ↔ Xor (Even (plen p) ∧ Even (endM p)) (p.length ≤ endL p + endR p)) := by
  suffices H : ∀ n, ∀ p, plen p = n → ValidPairs p → (G p ↔ MisP p) from
    fun p hp => H _ p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn hp
    have ih' : ∀ q, PMove p q → (G q ↔ MisP q) := fun q hq =>
      ih (plen q) (hn ▸ hq.plen_lt) q rfl (hq.validPairs hp)
    rw [hG p hp]
    constructor
    · rintro ⟨hne, hall⟩
      by_contra hM
      obtain ⟨q, hq, hMq⟩ := exists_misP_move hp hne hM
      exact hall q hq ((ih' q hq).2 hMq)
    · intro hM
      exact ⟨ne_nil_of_misP hM, fun q hq hGq => not_misP_move hM hq ((ih' q hq).1 hGq)⟩

theorem ofPairs_ne_nil_iff {p : List (ℕ × ℕ)} (hp : ValidPairs p) :
    ofPairs p ≠ [] ↔ p ≠ [] := by
  cases p with
  | nil => simp [ofPairs_nil]
  | cons x l =>
    obtain ⟨a, b⟩ := x
    have ha : 1 ≤ a := (hp (a, b) List.mem_cons_self).1
    refine iff_of_true (fun h => ?_) (List.cons_ne_nil _ _)
    have := congrArg List.length h
    rw [ofPairs_cons, List.length_append, List.length_replicate] at this
    simp only [List.length_nil] at this
    omega

theorem isMP_ofPairs_iff_forall {p : List (ℕ × ℕ)} (hp : ValidPairs p) :
    IsMP (ofPairs p) ↔ p ≠ [] ∧ ∀ q, PMove p q → ¬ IsMP (ofPairs q) := by
  rw [isMP_iff, ofPairs_ne_nil_iff hp]
  refine and_congr_right fun _ => ⟨fun h q hq => h _ ((mem_moves_ofPairs hp).2 ⟨q, hq, rfl⟩),
    fun h m hm => ?_⟩
  obtain ⟨q, hq, rfl⟩ := (mem_moves_ofPairs hp).1 hm
  exact h q hq

/-- **Misère CRIM**: `ofPairs p` is a misère P-position iff exactly one of Zeng's normal-play
condition (`plen p` and `endM p` even) and the cover condition `k ≤ L + R` holds. -/
theorem misereP_iff {p : List (ℕ × ℕ)} (hp : ValidPairs p) :
    IsMP (ofPairs p) ↔
      Xor (Even (plen p) ∧ Even (endM p)) (p.length ≤ endL p + endR p) :=
  misere_classification (fun p => IsMP (ofPairs p)) (fun _ hp => isMP_ofPairs_iff_forall hp) p hp

/-- The misère P-positions are the normal-play P-positions with the covered positions
toggled. -/
theorem misereP_iff_isP {p : List (ℕ × ℕ)} (hp : ValidPairs p) :
    IsMP (ofPairs p) ↔ Xor (IsP (ofPairs p)) (p.length ≤ endL p + endR p) := by
  rw [misereP_iff hp, isP_ofPairs_iff hp]

/-! ## conj:hookswap

The paper's `conj:hookswap`: "A partition λ has Conway pair (0, 1) if and only if λ is an
even-by-even hook". The Conway pair is (normal Sprague-Grundy value, misère Grundy value), where
the misère value of the terminal position `[]` is `1` and otherwise the mex of the options'
values (§2). So Conway pair `(0, 1)` means `IsP l ∧ IsMV1 l`. The paper itself has
`cp([]) = (0, 1)` (proof of `thm:cgpairrow`), so the statement as written fails at `[]`
(`nil_conwayPair`), and `hookswapConjecture` is the nonempty version; this is a remark on the
edge case, not a refutation. We prove the `(⇐)` direction, which is the misère part of the
paper's `thm:cgpairshooks` (`misere_hook`, `conwayPair_of_eeHook`), and that a position with
Conway pair `(0, 1)` is covered with an even number of run pairs (`covered_of_conwayPair`). The
`(⇒)` direction is open here. -/

/-! ### Misère value 1 -/

/-- Misère SG value 1: `[]` (terminal) has value 1, and a nonempty position has value 1 iff some
option is misère P (value 0) and no option has value 1. -/
def isMV1 (l : List ℕ) : Bool :=
  l.isEmpty || ((moves l).any isMP && (moves l).attach.all fun ⟨m, _⟩ => !isMV1 m)
termination_by l.sum + l.length
decreasing_by exact lt_of_mem_moves ‹_›

/-- `l` has misère SG value 1. -/
def IsMV1 (l : List ℕ) : Prop := isMV1 l = true

theorem isMV1_iff (l : List ℕ) :
    IsMV1 l ↔ l = [] ∨ ((∃ m ∈ moves l, IsMP m) ∧ ∀ m ∈ moves l, ¬ IsMV1 m) := by
  unfold IsMV1
  rw [isMV1]
  simp [List.all_eq_true, List.any_eq_true, IsMP]

theorem not_isMP_nil : ¬ IsMP [] := fun h => ((isMP_iff []).1 h).1 rfl

theorem isMV1_nil : IsMV1 [] := (isMV1_iff []).2 (Or.inl rfl)

/-- An even-by-even hook `Γ_{r,c}`. -/
def EEHook (l : List ℕ) : Prop := ∃ r c, 2 ≤ r ∧ 2 ≤ c ∧ r % 2 = 0 ∧ c % 2 = 0 ∧ l = hook r c

/-- **conj:hookswap** of arXiv:2606.16828 for nonempty partitions: `λ ≠ []` has Conway pair
`(0, 1)` iff it is an even-by-even hook. Not proved here: only `(⇐)` is
(`conwayPair_of_eeHook`). -/
def hookswapConjecture : Prop :=
  ∀ l : List ℕ, IsPartition l → l ≠ [] → (IsP l ∧ IsMV1 l ↔ EEHook l)

/-- The literal conj:hookswap fails at `[]`: Conway pair `(0, 1)`, but not a hook. -/
theorem nil_conwayPair : IsP [] ∧ IsMV1 [] ∧ ¬ EEHook [] :=
  ⟨isP_nil, isMV1_nil, fun ⟨r, c, _, _, _, _, h⟩ => by simp [hook] at h⟩

/-! ### Columns and hooks -/

theorem delCol_replicate_one (n : ℕ) : delCol (List.replicate n 1) 1 = [] := by
  simp [delCol]

theorem pad_nil_map (n : ℕ) : (pad [] n).map (· + 1) = List.replicate n 1 := by
  simp [pad]

theorem hook_one {r : ℕ} (hr : 1 ≤ r) : hook r 1 = List.replicate r 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp [hook, List.replicate_succ]

theorem hook_one_left (c : ℕ) : hook 1 c = [c] := rfl

theorem mem_moves_column {n : ℕ} {m : List ℕ} (hm : m ∈ moves (List.replicate (n + 1) 1)) :
    m = [] ∨ m = List.replicate n 1 := by
  rcases mem_moves.1 hm with ⟨i, hi, rfl⟩ | ⟨j, hj1, hj2, rfl⟩
  · rw [List.length_replicate] at hi
    rw [List.eraseIdx_replicate, if_pos hi]
    simp
  · rw [List.replicate_succ, part_one_cons] at hj2
    obtain rfl : j = 1 := by omega
    exact Or.inl (delCol_replicate_one _)

/-- A column `1^n` is misère P iff `n` is odd, and has misère value 1 iff `n = 0`. -/
theorem misere_column (n : ℕ) :
    (IsMP (List.replicate n 1) ↔ n % 2 = 1) ∧ (IsMV1 (List.replicate n 1) ↔ n = 0) := by
  induction n with
  | zero => exact ⟨by simpa using not_isMP_nil, by simpa using isMV1_nil⟩
  | succ n ih =>
  have h0 : [] ∈ moves (List.replicate (n + 1) 1) := by
    have := delCol_mem_moves (l := List.replicate (n + 1) 1) (j := 1) le_rfl
      (by rw [List.replicate_succ, part_one_cons])
    rwa [delCol_replicate_one] at this
  have h1 : List.replicate n 1 ∈ moves (List.replicate (n + 1) 1) := by
    rw [List.replicate_succ]
    exact mem_moves_cons 1 _
  refine ⟨⟨fun h => ?_, fun hn => ?_⟩, ⟨fun h => ?_, fun h => by omega⟩⟩
  · have := ((isMP_iff _).1 h).2 _ h1
    rw [ih.1] at this
    omega
  · refine (isMP_iff _).2 ⟨by simp, fun m hm => ?_⟩
    rcases mem_moves_column hm with rfl | rfl
    · exact not_isMP_nil
    · rw [ih.1]
      omega
  · rcases (isMV1_iff _).1 h with h' | ⟨-, h'⟩
    · simp at h'
    · exact absurd isMV1_nil (h' _ h0)

/-- Hooks: `Γ_{r,c}` is misère P iff `r, c` are odd, and has misère value 1 iff `r, c` are
even. -/
theorem misere_hook_aux (n : ℕ) : ∀ r c, r + c ≤ n → 1 ≤ r → 1 ≤ c →
    (IsMP (hook r c) ↔ r % 2 = 1 ∧ c % 2 = 1) ∧ (IsMV1 (hook r c) ↔ r % 2 = 0 ∧ c % 2 = 0) := by
  induction n with
  | zero => intro r c h hr; omega
  | succ n ih =>
  intro r c hn hr hc
  have IH : ∀ r' c', r' + c' < r + c → 1 ≤ r' → 1 ≤ c' →
      (IsMP (hook r' c') ↔ r' % 2 = 1 ∧ c' % 2 = 1) ∧
        (IsMV1 (hook r' c') ↔ r' % 2 = 0 ∧ c' % 2 = 0) :=
    fun r' c' hlt => ih r' c' (by omega)
  rcases Nat.lt_or_ge c 2 with hc1 | hc2
  · obtain rfl : c = 1 := by omega
    rw [hook_one hr, (misere_column r).1, (misere_column r).2]
    exact ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩⟩
  rw [← hookStack_nil]
  have hopt : ∀ m ∈ moves (hookStack r c []), m = List.replicate (r - 1) 1 ∨
      (2 ≤ r ∧ m = hook (r - 1) c) ∨ m = hook 1 (c - 1) ∨ m = hook r (c - 1) := by
    intro m hm
    rcases mem_moves_hookStack isPartition_nil hr hc2 (by simp) hm with
      rfl | ⟨i, hi, rfl⟩ | rfl | ⟨j, -, -, rfl⟩
    · exact Or.inl (pad_nil_map _)
    · exact Or.inr (Or.inl ⟨by omega, by rw [List.eraseIdx_nil, hookStack_nil]⟩)
    · exact Or.inr (Or.inr (Or.inl (hook_one_left _).symm))
    · exact Or.inr (Or.inr (Or.inr (by rw [delCol_nil, hookStack_nil])))
  have hA : List.replicate (r - 1) 1 ∈ moves (hookStack r c []) := by
    rw [← pad_nil_map]
    exact pad_map_mem_moves
  have hB (h2 : 2 ≤ r) : hook (r - 1) c ∈ moves (hookStack r c []) := by
    have := hookStack_eraseIdx_mem_moves (c := c) (μ := []) (i := 0) hr (by simp) (by omega)
    rwa [List.eraseIdx_nil, hookStack_nil (r - 1) c] at this
  have hC : hook 1 (c - 1) ∈ moves (hookStack r c []) := by
    rw [hook_one_left]
    exact cons_mem_moves (μ := []) (by simp) hc2
  have hD : hook r (c - 1) ∈ moves (hookStack r c []) := by
    have := hookStack_delCol_mem_moves (r := r) (c := c) (j := 1) isPartition_nil (by simp)
      le_rfl (by omega)
    rwa [delCol_nil, hookStack_nil r (c - 1)] at this
  have hP1 := misere_column (r - 1)
  have hP3 := IH 1 (c - 1) (by omega) le_rfl (by omega)
  have hP4 := IH r (c - 1) (by omega) hr (by omega)
  have hne : hookStack r c [] ≠ [] := by simp [hookStack]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have nA := ((isMP_iff _).1 h).2 _ hA
    have nC := ((isMP_iff _).1 h).2 _ hC
    rw [hP1.1] at nA
    rw [hP3.1] at nC
    omega
  · refine (isMP_iff _).2 ⟨hne, fun m hm => ?_⟩
    rcases hopt m hm with rfl | ⟨h2, rfl⟩ | rfl | rfl
    · rw [hP1.1]; omega
    · rw [(IH (r - 1) c (by omega) (by omega) hc).1]; omega
    · rw [hP3.1]; omega
    · rw [hP4.1]; omega
  · rcases (isMV1_iff _).1 h with h0 | ⟨⟨m, hm, hmp⟩, hno⟩
    · exact absurd h0 hne
    have nA := hno _ hA
    rw [hP1.2] at nA
    have hP2 := IH (r - 1) c (by omega) (by omega) hc
    have nB := hno _ (hB (by omega))
    have nD := hno _ hD
    rw [hP2.2] at nB
    rw [hP4.2] at nD
    rcases hopt m hm with rfl | ⟨h2, rfl⟩ | rfl | rfl
    · rw [hP1.1] at hmp; omega
    · rw [hP2.1] at hmp; omega
    · rw [hP3.1] at hmp; omega
    · rw [hP4.1] at hmp; omega
  · refine (isMV1_iff _).2 (Or.inr ⟨⟨hook 1 (c - 1), hC, by rw [hP3.1]; omega⟩, fun m hm => ?_⟩)
    rcases hopt m hm with rfl | ⟨h2, rfl⟩ | rfl | rfl
    · rw [hP1.2]; omega
    · rw [(IH (r - 1) c (by omega) (by omega) hc).2]; omega
    · rw [hP3.2]; omega
    · rw [hP4.2]; omega

theorem misere_hook {r c : ℕ} (hr : 1 ≤ r) (hc : 1 ≤ c) :
    (IsMP (hook r c) ↔ r % 2 = 1 ∧ c % 2 = 1) ∧ (IsMV1 (hook r c) ↔ r % 2 = 0 ∧ c % 2 = 0) :=
  misere_hook_aux (r + c) r c le_rfl hr hc

/-! ### The `(⇐)` direction -/

/-- A hook has Conway pair `(0, 1)` iff it is even-by-even. -/
theorem conwayPair_hook_iff {r c : ℕ} (hr : 1 ≤ r) (hc : 1 ≤ c) :
    IsP (hook r c) ∧ IsMV1 (hook r c) ↔ r % 2 = 0 ∧ c % 2 = 0 := by
  rw [isP_hook_iff hr hc, (misere_hook hr hc).2]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨by omega, by omega, by omega⟩, h⟩

/-- `(⇐)` of conj:hookswap: every even-by-even hook has Conway pair `(0, 1)`. -/
theorem conwayPair_of_eeHook {l : List ℕ} (h : EEHook l) : IsP l ∧ IsMV1 l := by
  obtain ⟨r, c, hr, hc, hr2, hc2, rfl⟩ := h
  exact (conwayPair_hook_iff (by omega) (by omega)).2 ⟨hr2, hc2⟩

/-- conj:hookswap (nonempty) is equivalent to its `(⇒)` direction. -/
theorem hookswapConjecture_iff : hookswapConjecture ↔
    ∀ l : List ℕ, IsPartition l → l ≠ [] → IsP l → IsMV1 l → EEHook l :=
  ⟨fun h l hl hne hP hV => (h l hl hne).1 ⟨hP, hV⟩,
    fun h l hl hne => ⟨fun hcp => h l hl hne hcp.1 hcp.2, conwayPair_of_eeHook⟩⟩

/-! ### Towards `(⇒)` -/

theorem not_isMP_of_isMV1 {l : List ℕ} (h : IsMV1 l) : ¬ IsMP l := by
  rcases (isMV1_iff l).1 h with rfl | ⟨⟨m, hm, hmp⟩, -⟩
  · exact not_isMP_nil
  · exact fun hl => ((isMP_iff l).1 hl).2 m hm hmp

/-- A position with Conway pair `(0, 1)` is covered (`k ≤ L + R`) with `k` even. -/
theorem covered_of_conwayPair {p : List (ℕ × ℕ)} (hp : ValidPairs p) (hP : IsP (ofPairs p))
    (hV : IsMV1 (ofPairs p)) : p.length ≤ endL p + endR p ∧ Even p.length := by
  have hc : p.length ≤ endL p + endR p := by
    by_contra hc
    exact not_isMP_of_isMV1 hV ((misereP_iff_isP hp).2 (Or.inl ⟨hP, hc⟩))
  refine ⟨hc, ?_⟩
  have h := ((isP_ofPairs_iff hp).1 hP).2
  rwa [endM, min_eq_left hc] at h

end AgenticConjectures.CrimPselfMeld
