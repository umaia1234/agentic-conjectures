import Mathlib

/-!
# Catch-Up on `{1, …, N}`: the draw conjecture

Isaksen, Ismail, Brams and Nealen, *Catch-Up: A Game in Which the Lead Alternates*,
Game & Puzzle Design 1(2), 38–49 (2015), computed optimal play for `N ≤ 20` and
conjectured that Catch-Up on `{1, …, N}` is a draw whenever `T_N = N (N + 1) / 2` is even.

## Upstream correspondence

The definitions `Player`, `Player.other`, `Outcome`, `Outcome.neg`, `Outcome.best`,
`valueAux` and `value` below are copied term for term (docstrings and comments included)
from `FormalConjectures/Paper/CatchUpConjecture.lean` of google-deepmind/formal-conjectures at
commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d` (snapshot in
`problems/catch-up-game/upstream/`). The only adaptations:

* `module`, `public import FormalConjecturesUtil` and `@[expose] public section` are replaced
  by `import Mathlib`; the definitions use nothing from the FormalConjectures utilities.
* The upstream namespace `CatchUp` becomes `AgenticConjectures.CatchUpGame`.
* The open theorem `value_of_even_mul_succ_self_div_two` (attribute
  `@[category research open, AMS 11 91]`, proof `sorry`) becomes `def statement : Prop`
  with the same binder `N : ℕ`, the same hypothesis `Even (N * (N + 1) / 2)` and the same
  conclusion `value (.Icc 1 N) = .draw`. Note `N * (N + 1) / 2` is exact division, since
  `N * (N + 1)` is even.

## What is proved here

* `statement_of_le_ten`: the statement for every `N ≤ 10` (the even cases are
  `N = 0, 3, 4, 7, 8`), by kernel evaluation (`decide +kernel`) of a computable copy
  `valueList` of `valueAux`, proved equal to it in `valueAux_toFinset`.
* `value_Icc_ne_draw` and `statement_iff`: draws need an even total, so the conjecture says
  exactly that `value (.Icc 1 N) = .draw ↔ Even (N * (N + 1) / 2)`.
* `valueAux_add`, `gapValue_eq`, `value_eq_gapValue`, `value_eq_gapValue_zero`: `valueAux`
  only depends on the remaining set and the score gap, it satisfies the gap recursion that the
  independent C++ checker `problems/catch-up-game/catchup_pick.cpp` implements, and a fresh
  game is the position with gap `0`.

The exact values for `11 ≤ N ≤ 28` are computed outside Lean by two independent C++
programs; see `problems/catch-up-game/README.md`. The statement is open in general.
-/

namespace AgenticConjectures.CatchUpGame

/--
An arbitrary two elements type indexing the players in the Catch-Up game.
-/
inductive Player
  | p1
  | p2
deriving DecidableEq, Repr

/-- Returns the other player. -/
def Player.other : Player → Player
  | p1 => p2
  | p2 => p1

/-- The possible outcomes of a Catch-Up game. -/
inductive Outcome
  | win
  | loss
  | draw
deriving DecidableEq, Repr

/-- Negates an outcome, swapping win and loss. Used when switching player perspectives. -/
def Outcome.neg : Outcome → Outcome
  | win => loss
  | loss => win
  | draw => draw

/--
Computes the best outcome for the current player from a list of possible outcomes.
Win > Draw > Loss.
-/
def Outcome.best (os : List Outcome) : Outcome :=
  os.foldl (fun
    | .win,  _     => .win
    | _,     .win  => .win
    | .draw, _     => .draw
    | _,     .draw => .draw
    | _,     _     => .loss) .loss


/-
Define the recursive game value functions.
-/

/--
`value remaining s_me s_opp isFirstMove` evaluates the position where:

* `remaining` is the set `S'` of numbers not yet taken.
* `s_me` is the current score of the player who is about to act (the “current player”).
* `s_opp` is the opponent’s current score.
* `isFirstMove` indicates whether we are in the special very first move of the whole game,
  where the rules force exactly one pick and then the turn passes.

The result is the game-theoretic value from the current player’s point of view:
`.win` / `.loss` / `.draw`, assuming optimal play from both sides.

We model a single *turn* (which may consist of several picks `$x_1,...,x_k$`) by recursion:
the current player chooses one number `x`; if they are still strictly behind after taking it, they must
continue the same turn (so the recursive call keeps the same “current player”);
once they catch up (score ≥ opponent), the turn ends and we swap players.
-/
noncomputable def valueAux (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool) : Outcome :=
  -- If no numbers remain, the game is over. Compare final scores.
  if remaining = ∅ then
    if s_me > s_opp then
      -- Current player ends with strictly larger score.
      .win
    else if s_opp > s_me then
      -- Opponent ends with strictly larger score.
      .loss
    else
      -- Scores are equal.
      .draw
  else
    -- Terminal rule / pruning:
    -- If even taking *all* remaining numbers would still leave the current player behind,
    -- then there is no legal catch-up sequence (in the TeX: no `$x_1,...,x_k$` with final sum ≥ gap).
    -- By the rules, the current player takes everything and the game ends immediately,
    -- but under this inequality they must still lose.
    if s_me + remaining.sum (fun x => x) < s_opp then
      .loss
    else
      -- Otherwise, the current player can pick some `$x \in$ remaining`.
      -- We evaluate every possible next pick under optimal play, then take the best outcome.
      let moves := remaining.attach.toList
      let outcomes := moves.map (fun ⟨x, _⟩ =>
        -- Take `x`: update current player's score and remove `x` from the set.
        let s_me' := s_me + x
        let remaining' := remaining.erase x

        if isFirstMove then
          -- First move rule (TeX item (1)):
          -- On the first move, `p1` must take exactly one element and then the turn passes.
          -- We therefore swap roles, evaluate from the opponent’s perspective, and negate
          -- to convert back to the current player's perspective.
          (valueAux remaining' s_opp s_me' false).neg
        else
          -- Subsequent move rule (TeX item (2)):
          -- On a turn, the current player must keep taking numbers while strictly behind,
          -- and stops as soon as they reach or exceed the opponent.
          if s_me' ≥ s_opp then
            -- We have caught up (or overtaken) on this pick: the turn ends and the opponent moves next.
            -- Swap players and negate to return to the current player's perspective.
            (valueAux remaining' s_opp s_me' false).neg
          else
            -- Still strictly behind after taking `x`: rules force us to continue the same turn,
            -- so the same player remains “current” in the recursive call.
            valueAux remaining' s_me' s_opp false
      )
      -- Optimal play: choose the best outcome among all legal next picks.
      .best outcomes
termination_by remaining.card
decreasing_by
  all_goals
    simpa [remaining'] using Finset.card_erase_lt_of_mem ‹_›

/-- Public API: The game-theoretic value of Catch-Up on the set `S`, assuming optimal play.
Returns `.win` if player 1 wins, `.loss` if player 2 wins, `.draw` if the game is tied. -/
noncomputable def value (S : Finset ℕ) : Outcome :=
  valueAux S 0 0 true

/-! ## The open statement -/

/-- The Isaksen–Ismail–Brams–Nealen conjecture as stated upstream
(`value_of_even_mul_succ_self_div_two`): if `T_N = N (N + 1) / 2` is even, then
Catch-Up on `{1, …, N}` is a draw under optimal play. -/
def statement : Prop :=
  ∀ (N : ℕ), Even (N * (N + 1) / 2) → value (.Icc 1 N) = .draw

/-! ## `Outcome.best` only depends on which outcomes occur -/

/-- The step function of the fold in `Outcome.best`, as a named function. -/
def bestStep : Outcome → Outcome → Outcome
  | .win,  _     => .win
  | _,     .win  => .win
  | .draw, _     => .draw
  | _,     .draw => .draw
  | _,     _     => .loss

theorem best_eq_foldl (os : List Outcome) : Outcome.best os = os.foldl bestStep .loss := rfl

theorem foldl_bestStep (acc : Outcome) (os : List Outcome) :
    os.foldl bestStep acc =
      if acc = .win ∨ .win ∈ os then .win
      else if acc = .draw ∨ .draw ∈ os then .draw else .loss := by
  induction os generalizing acc with
  | nil => cases acc <;> simp
  | cons o os ih =>
    rw [List.foldl_cons, ih]
    cases acc <;> cases o <;> simp [bestStep]

/-- `Outcome.best` is the maximum for `loss < draw < win`. -/
theorem best_eq (os : List Outcome) :
    Outcome.best os = if .win ∈ os then .win else if .draw ∈ os then .draw else .loss := by
  rw [best_eq_foldl, foldl_bestStep]
  simp

theorem best_congr {os os' : List Outcome} (h : ∀ o, o ∈ os ↔ o ∈ os') :
    Outcome.best os = Outcome.best os' := by
  simp only [best_eq, h]

/-! ## A computable copy of `valueAux` -/

/-- The score comparison that `valueAux` makes once no numbers remain. -/
def finalOutcome (s_me s_opp : ℕ) : Outcome :=
  if s_me > s_opp then .win else if s_opp > s_me then .loss else .draw

/-- `valueAux` on a list instead of a finset, with a fuel argument `n` so that the recursion
is structural and the kernel can evaluate it. For a duplicate-free list `l` and any fuel
`n ≥ l.length` it agrees with `valueAux l.toFinset` (`valueAux_toFinset`). -/
def valueList : ℕ → List ℕ → ℕ → ℕ → Bool → Outcome
  | 0, _, s_me, s_opp, _ => finalOutcome s_me s_opp
  | _ + 1, [], s_me, s_opp, _ => finalOutcome s_me s_opp
  | n + 1, l@(_ :: _), s_me, s_opp, isFirstMove =>
    if s_me + l.sum < s_opp then .loss
    else Outcome.best (l.map fun x =>
      if isFirstMove then (valueList n (l.erase x) s_opp (s_me + x) false).neg
      else if s_me + x ≥ s_opp then (valueList n (l.erase x) s_opp (s_me + x) false).neg
      else valueList n (l.erase x) (s_me + x) s_opp false)

theorem toFinset_erase_of_nodup {l : List ℕ} (hl : l.Nodup) (x : ℕ) :
    (l.erase x).toFinset = l.toFinset.erase x := by
  ext y
  simp [hl.mem_erase_iff]

theorem valueAux_empty (s_me s_opp : ℕ) (isFirstMove : Bool) :
    valueAux ∅ s_me s_opp isFirstMove = finalOutcome s_me s_opp := by
  rw [valueAux]
  simp [finalOutcome]

theorem valueAux_toFinset (n : ℕ) :
    ∀ (l : List ℕ), l.Nodup → l.length ≤ n → ∀ (s_me s_opp : ℕ) (isFirstMove : Bool),
      valueAux l.toFinset s_me s_opp isFirstMove = valueList n l s_me s_opp isFirstMove := by
  induction n with
  | zero =>
    intro l _ hlen s_me s_opp isFirstMove
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [valueAux_empty, valueList]
  | succ n ih =>
    intro l hl hlen s_me s_opp isFirstMove
    rcases l with _ | ⟨y, ys⟩
    · simp [valueAux_empty, valueList]
    · have hne : (y :: ys).toFinset ≠ ∅ := by simp
      have hsum : (y :: ys).toFinset.sum (fun x => x) = (y :: ys).sum := by
        rw [List.sum_toFinset _ hl]
        simp
      rw [valueAux, valueList]
      simp only [hne, if_false, hsum]
      by_cases h : s_me + (y :: ys).sum < s_opp
      · simp only [h, if_true]
      · simp only [h, if_false]
        apply best_congr
        intro o
        simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and,
          Subtype.exists]
        have key : ∀ x ∈ y :: ys, ∀ a b f,
            valueAux ((y :: ys).toFinset.erase x) a b f =
              valueList n ((y :: ys).erase x) a b f := by
          intro x hx a b f
          rw [← toFinset_erase_of_nodup hl]
          apply ih _ (hl.erase x)
          rw [List.length_erase_of_mem hx]
          simp at hlen ⊢
          omega
        constructor
        · rintro ⟨x, hx, rfl⟩
          have hx' : x ∈ y :: ys := List.mem_toFinset.mp hx
          refine ⟨x, hx', ?_⟩
          simp only [key x hx']
        · rintro ⟨x, hx, rfl⟩
          refine ⟨x, List.mem_toFinset.mpr hx, ?_⟩
          simp only [key x hx]

/-! ## General lemmas about `valueAux` -/

theorem neg_eq_draw_iff (o : Outcome) : o.neg = .draw ↔ o = .draw := by
  cases o <;> simp [Outcome.neg]

theorem best_ne_draw {os : List Outcome} (h : Outcome.draw ∉ os) : Outcome.best os ≠ .draw := by
  rw [best_eq]
  split_ifs <;> simp_all

/-- With an odd total `s_me + s_opp + Σ remaining`, no position is drawn. -/
theorem valueAux_ne_draw (n : ℕ) :
    ∀ (remaining : Finset ℕ), remaining.card ≤ n →
      ∀ (s_me s_opp : ℕ) (isFirstMove : Bool),
      Odd (s_me + s_opp + remaining.sum (fun x => x)) →
        valueAux remaining s_me s_opp isFirstMove ≠ .draw := by
  induction n with
  | zero =>
    intro remaining hcard s_me s_opp isFirstMove hodd
    obtain rfl : remaining = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [valueAux_empty, finalOutcome]
    simp only [Finset.sum_empty, add_zero] at hodd
    obtain ⟨k, hk⟩ := hodd
    split_ifs <;> first | omega | simp
  | succ n ih =>
    intro remaining hcard s_me s_opp isFirstMove hodd
    by_cases hR : remaining = ∅
    · subst hR
      exact ih ∅ (by simp) s_me s_opp isFirstMove hodd
    rw [valueAux]
    by_cases hlt : s_me + remaining.sum (fun x => x) < s_opp
    · simp only [hR, hlt, if_false, if_true]
      simp
    simp only [hR, hlt, if_false]
    apply best_ne_draw
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and, Subtype.exists]
    rintro ⟨x, hx, hxo⟩
    have hcard' : (remaining.erase x).card ≤ n := by
      rw [Finset.card_erase_of_mem hx]
      omega
    have hs : (remaining.erase x).sum (fun y => y) + x = remaining.sum (fun y => y) :=
      Finset.sum_erase_add remaining (fun y => y) hx
    have hodd1 : Odd (s_opp + (s_me + x) + (remaining.erase x).sum (fun y => y)) := by
      have : s_opp + (s_me + x) + (remaining.erase x).sum (fun y => y) =
          s_me + s_opp + remaining.sum (fun y => y) := by omega
      rw [this]
      exact hodd
    have hodd2 : Odd (s_me + x + s_opp + (remaining.erase x).sum (fun y => y)) := by
      have : s_me + x + s_opp + (remaining.erase x).sum (fun y => y) =
          s_me + s_opp + remaining.sum (fun y => y) := by omega
      rw [this]
      exact hodd
    have h1 := ih _ hcard' s_opp (s_me + x) false hodd1
    have h2 := ih _ hcard' (s_me + x) s_opp false hodd2
    split_ifs at hxo
    · exact h1 ((neg_eq_draw_iff _).mp hxo)
    · exact h1 ((neg_eq_draw_iff _).mp hxo)
    · exact h2 hxo

theorem sum_Icc_id_mul_two (N : ℕ) : (Finset.Icc 1 N).sum (fun x => x) * 2 = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
    ring

theorem sum_Icc_id (N : ℕ) : (Finset.Icc 1 N).sum (fun x => x) = N * (N + 1) / 2 :=
  (Nat.div_eq_of_eq_mul_left (by norm_num) (sum_Icc_id_mul_two N).symm).symm

/-- Draws need an even total: if `T_N` is odd, `Catch-Up({1, …, N})` has a winner. -/
theorem value_Icc_ne_draw (N : ℕ) (h : ¬ Even (N * (N + 1) / 2)) :
    value (.Icc 1 N) ≠ .draw := by
  apply valueAux_ne_draw _ _ le_rfl
  rw [sum_Icc_id]
  simpa using Nat.not_even_iff_odd.mp h

/-- So the conjecture says exactly that the draws are the games with an even total. -/
theorem statement_iff :
    statement ↔ ∀ N : ℕ, value (.Icc 1 N) = .draw ↔ Even (N * (N + 1) / 2) := by
  constructor
  · intro hs N
    exact ⟨fun hd => by_contra fun h => value_Icc_ne_draw N h hd, hs N⟩
  · intro h N
    exact (h N).mpr

/-- Adding the same amount to both scores does not change the value. -/
theorem valueAux_add (n : ℕ) :
    ∀ (remaining : Finset ℕ), remaining.card ≤ n →
      ∀ (s_me s_opp k : ℕ) (isFirstMove : Bool),
      valueAux remaining (s_me + k) (s_opp + k) isFirstMove =
        valueAux remaining s_me s_opp isFirstMove := by
  induction n with
  | zero =>
    intro remaining hcard s_me s_opp k isFirstMove
    obtain rfl : remaining = ∅ := Finset.card_eq_zero.mp (by omega)
    simp only [valueAux_empty, finalOutcome]
    split_ifs <;> first | rfl | omega
  | succ n ih =>
    intro remaining hcard s_me s_opp k isFirstMove
    by_cases hR : remaining = ∅
    · subst hR
      simp only [valueAux_empty, finalOutcome]
      split_ifs <;> first | rfl | omega
    rw [valueAux, valueAux]
    have hlt : s_me + k + remaining.sum (fun x => x) < s_opp + k ↔
        s_me + remaining.sum (fun x => x) < s_opp := by omega
    by_cases h : s_me + remaining.sum (fun x => x) < s_opp
    · simp only [hR, hlt, h, if_false, if_true]
    simp only [hR, hlt, h, if_false]
    congr 1
    apply List.map_congr_left
    rintro ⟨x, hx⟩ -
    have hcard' : (remaining.erase x).card ≤ n := by
      rw [Finset.card_erase_of_mem hx]
      omega
    have e1 := ih _ hcard' s_opp (s_me + x) k false
    have e2 := ih _ hcard' (s_me + x) s_opp k false
    dsimp only
    rw [show s_me + k + x = s_me + x + k by omega, e1, e2]
    split_ifs <;> first | rfl | omega

/-- `valueAux` with `isFirstMove = false` only depends on the remaining set and on the gap
`D = s_opp - s_me` (the player to move is never ahead). This is the function `P(R, D)`
computed by the independent checker `problems/catch-up-game/catchup_pick.cpp`. -/
noncomputable def gapValue (remaining : Finset ℕ) (D : ℕ) : Outcome :=
  valueAux remaining 0 D false

theorem valueAux_eq_gapValue (remaining : Finset ℕ) (s_me D : ℕ) :
    valueAux remaining s_me (s_me + D) false = gapValue remaining D := by
  have := valueAux_add remaining.card remaining le_rfl 0 D s_me false
  simpa [gapValue, add_comm] using this

/-- The recursion implemented by `catchup_pick.cpp`, derived from the upstream definition. -/
theorem gapValue_eq (remaining : Finset ℕ) (D : ℕ) :
    gapValue remaining D =
      if remaining = ∅ then (if D = 0 then .draw else .loss)
      else if remaining.sum (fun x => x) < D then .loss
      else Outcome.best (remaining.attach.toList.map fun x =>
        if D ≤ x.1 then (gapValue (remaining.erase x.1) (x.1 - D)).neg
        else gapValue (remaining.erase x.1) (D - x.1)) := by
  by_cases hR : remaining = ∅
  · subst hR
    rw [gapValue, valueAux_empty, finalOutcome]
    simp only [if_true]
    split_ifs <;> first | rfl | omega
  rw [gapValue, valueAux]
  by_cases h : remaining.sum (fun x => x) < D
  · simp only [hR, h, zero_add, if_false, if_true]
  simp only [hR, h, zero_add, if_false]
  congr 1
  apply List.map_congr_left
  rintro ⟨x, hx⟩ -
  dsimp only
  by_cases hxD : D ≤ x
  · have := valueAux_eq_gapValue (remaining.erase x) D (x - D)
    rw [show D + (x - D) = x by omega] at this
    simp [hxD, this]
  · have := valueAux_eq_gapValue (remaining.erase x) x (D - x)
    rw [show x + (D - x) = D by omega] at this
    simp [hxD, this]

/-- The first move, in terms of `gapValue`. -/
theorem value_eq_gapValue (S : Finset ℕ) (hS : S ≠ ∅) :
    value S = Outcome.best (S.attach.toList.map fun x => (gapValue (S.erase x.1) x.1).neg) := by
  rw [value, valueAux]
  have h0 : ¬ (0 + S.sum (fun x => x) < 0) := by omega
  simp only [hS, h0, if_false, if_true]
  congr 1
  apply List.map_congr_left
  rintro ⟨x, hx⟩ -
  have := valueAux_eq_gapValue (S.erase x) 0 x
  simp only [zero_add] at this
  simp [this]

/-- A fresh game is the position with gap `0`: with level scores, the gap recursion also
takes exactly one number and then swaps roles, as the first-move rule demands. -/
theorem value_eq_gapValue_zero (S : Finset ℕ) : value S = gapValue S 0 := by
  by_cases hS : S = ∅
  · subst hS
    simp only [value, gapValue, valueAux_empty]
  rw [value_eq_gapValue S hS, gapValue_eq]
  simp [hS]

theorem toFinset_range' (N : ℕ) : (List.range' 1 N).toFinset = Finset.Icc 1 N := by
  ext x
  simp only [List.mem_toFinset, List.mem_range', Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hx
    exact ⟨x - 1, by omega, by omega⟩

theorem value_Icc_eq_valueList (N : ℕ) :
    value (.Icc 1 N) = valueList N (List.range' 1 N) 0 0 true := by
  rw [value, ← toFinset_range', valueAux_toFinset N _ List.nodup_range' (by simp)]

theorem value_Icc_three : value (.Icc 1 3) = .draw := by
  rw [value_Icc_eq_valueList]
  decide +kernel

theorem value_Icc_four : value (.Icc 1 4) = .draw := by
  rw [value_Icc_eq_valueList]
  decide +kernel

theorem value_Icc_seven : value (.Icc 1 7) = .draw := by
  rw [value_Icc_eq_valueList]
  decide +kernel

theorem value_Icc_eight : value (.Icc 1 8) = .draw := by
  rw [value_Icc_eq_valueList]
  decide +kernel

/-- The conjecture for every `N ≤ 10`. The even-`T_N` cases are `N = 0, 3, 4, 7, 8`. -/
theorem statement_of_le_ten (N : ℕ) (hN : N ≤ 10) (h_even : Even (N * (N + 1) / 2)) :
    value (.Icc 1 N) = .draw := by
  interval_cases N
  · rw [value_Icc_eq_valueList]
    decide
  all_goals first
    | exact value_Icc_three
    | exact value_Icc_four
    | exact value_Icc_seven
    | exact value_Icc_eight
    | exact absurd h_even (by decide)

end AgenticConjectures.CatchUpGame
