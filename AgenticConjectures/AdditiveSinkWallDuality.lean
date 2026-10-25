import AgenticConjectures.AdditiveSinkWallDuality.Classes
import AgenticConjectures.AdditiveSinkWallDuality.Explicit

/-!
# The sink–wall duality of additive subtraction games

Source: A. Bhagat, U. Larsson, H. Manabe and T. Yamashita, *Additive Sink Subtraction*,
arXiv:2601.18715v3, equation (3) (`eq:conj`), stated after Corollary 4 (`cor:add`). Let
`S = {s₁, s₂, s₁ + s₂}` with `1 ≤ s₁ < s₂`, let `p` be the period length of their Theorem 3
(`thm:main`), and let `σ` swap the nim-values `0` and `2` and fix `1` and `3`. The conjecture says
that for all `x`,

`v_wall([x]_p) = σ(v_sink([-s₂ - x]_p))`,

where `[x]_p` is the least nonnegative residue of `x` modulo `p`.

## The statement and its choices

* Both games are defined in `AdditiveSinkWallDuality/Games.lean` directly by their mex recursions:
  `wall s₁ s₂ x` for `x : ℕ` (only moves `s ≤ x`), and `sink s₁ s₂ y` for `y : ℤ`, where every
  `y ≤ 0` has value `0` and a position `y ≥ 1` may move to any `y - s`, including into the sink.
  Moves of size `0` are skipped to make the recursions total; for `1 ≤ s₁ < s₂` there are none.
* `period s₁ s₂` is the formula of `thm:main` with `m = s₁`, `δ = s₂ - s₁`, `d = δ mod 2m`:
  `3m + 2δ - d` if `d ≤ m`, else `m (m + 2δ + d) / gcd(m, d)`. The conjecture's `p` is this
  number: the paper calls it "the (outcome) period length", which is the period of `thm:main`
  and, by `cor:add`, of the wall outcomes. We use the formula itself. We prove here that it is a
  period of both nim-sequences (`wall_periodic`, `sink_periodic`), but not that it is the least
  one.
* `x` ranges over `ℤ`. Both sides depend only on `x mod p`, so this is the most general reading,
  and it contains the reading with `x : ℕ`.
* `[x]_p` is `x % p` (`Int.emod`, which lies in `[0, p)` since `p > 0`); on the wall side it is
  converted to `ℕ` with `Int.toNat`. On the sink side residue `0` is the sink position `0`, of
  value `0`; the paper's table for `S = {2, 5, 7}` (Example 5) uses the representative `p` instead,
  which has the same value (`sink_period_eq_zero`).
* `sigma` is `σ`, extended by the identity to values `≥ 4`, which never occur.
* There is no restriction on `gcd(s₁, s₂)` or on the regime (`d ≤ m` or not).

## Proof

* `Classes.lean` works from the mex recursions alone. With `P` the set of wall `𝒫`-positions it
  proves (T1) `wall_eq_wallClass`: the wall values `0, 1, 2, 3` sit on `P`, `P + s₁`, `P - s₂` and
  the rest; and (T2) `sink_eq_sinkClass`: the sink values `0, 1, 2, 3` sit on `P + s₃ + 1`,
  `P + 1`, `P + s₁ + 1` and the rest. If no element of `P` lies in `[p - s₃, p)`, then `P` is
  `p`-periodic and (T3) symmetric under `x ↦ p - s₃ - 1 - x` (`wall_zero_reflect`), and the
  conjecture follows (`conj_of_gap`).
* `Explicit.lean` proves that `P` is `W ∩ ℕ` for an explicit set `W ⊆ ℤ`, the image form of
  the classical bracket formula (`wall_zero_iff_W` below). It writes the formula of `thm:main` as
  `p = 2 s₁ ℓ + k s₂` with `s₁ ℓ = k N` and `ℓ, k ≥ 1`, where `N` is the bracket formula's
  second modulus (`Explicit.period_spec`), and from this proves the gap for the paper's `p`
  (`W_top_gap`).

The argument is uniform in `gcd(s₁, s₂)` and includes `s₁ = 1`, so no reduction to coprime
moves is needed. `problems/additive-sink-wall-duality/DETAILS.md` has the human-readable proof.
-/

namespace AgenticConjectures.AdditiveSinkWallDuality

/-- The sink–wall duality conjecture `eq:conj` of Bhagat, Larsson, Manabe and Yamashita
(arXiv:2601.18715v3). -/
def statement : Prop :=
  ∀ s₁ s₂ : ℕ, 1 ≤ s₁ → s₁ < s₂ → ∀ x : ℤ,
    wall s₁ s₂ (x % (period s₁ s₂ : ℤ)).toNat =
      sigma (sink s₁ s₂ ((-(s₂ : ℤ) - x) % (period s₁ s₂ : ℤ)))

section

variable {s₁ s₂ : ℕ} (h1 : 1 ≤ s₁) (h2 : s₁ < s₂)
include h1 h2

/-- (B4) The wall `𝒫`-positions are the natural numbers in the explicit set `W`. -/
theorem wall_zero_iff_W (n : ℕ) : wall s₁ s₂ n = 0 ↔ W s₁ s₂ n :=
  wall_zero_iff_of_kernel (by omega) h2 (W s₁ s₂) (fun _ _ hu hv h => W_indep h1 h2 hu hv h)
    (W_cover h1 h2) (fun _ hx1 hx2 => W_neg_gap h1 h2 hx1 hx2) n

/-- (Gap) No wall `𝒫`-position lies in `[p - s₃, p)`. -/
theorem wall_ne_zero_of_gap (n : ℕ) (hn1 : period s₁ s₂ - (s₁ + s₂) ≤ n)
    (hn2 : n < period s₁ s₂) : wall s₁ s₂ n ≠ 0 := by
  rw [Ne, wall_zero_iff_W h1 h2]
  have := period_gt h1 h2
  exact W_top_gap h1 h2 (by omega) (by omega)

/-- The wall nim-sequence is `p`-periodic. -/
theorem wall_periodic (x : ℕ) : wall s₁ s₂ (x + period s₁ s₂) = wall s₁ s₂ x :=
  wall_add_period (by omega) h2 (wall_ne_zero_of_gap h1 h2) (period_gt h1 h2) x

/-- The sink nim-sequence is purely `p`-periodic from position `1` on. -/
theorem sink_periodic {y : ℤ} (hy : 0 < y) : sink s₁ s₂ (y + period s₁ s₂) = sink s₁ s₂ y :=
  sink_add_period (by omega) h2 (wall_ne_zero_of_gap h1 h2) (period_gt h1 h2) hy

/-- (T3) The wall `𝒫`-positions in `[0, p - s₃ - 1]` are symmetric about its midpoint. -/
theorem wall_zero_reflect_period {x : ℕ} (hx : x ≤ period s₁ s₂ - (s₁ + s₂) - 1) :
    wall s₁ s₂ x = 0 ↔ wall s₁ s₂ (period s₁ s₂ - (s₁ + s₂) - 1 - x) = 0 :=
  wall_zero_reflect (by omega) h2 (wall_ne_zero_of_gap h1 h2)
    (by have := period_gt h1 h2; omega) hx

/-- The sink position `p` has value `0`, like the sink position `0`. -/
theorem sink_period_eq_zero : sink s₁ s₂ (period s₁ s₂) = 0 := by
  have hp := period_gt h1 h2
  rw [show ((period s₁ s₂ : ℕ) : ℤ) = ((period s₁ s₂ - 1 : ℕ) : ℤ) + 1 by omega,
    sink_eq_sinkClass (by omega) h2, sinkClass_eq_zero]
  refine ⟨by omega, ?_⟩
  have := (wall_zero_reflect_period h1 h2 (x := 0) (Nat.zero_le _)).1
    (wall_small (by omega) h2 (by omega))
  rwa [show period s₁ s₂ - (s₁ + s₂) - 1 - 0 = period s₁ s₂ - 1 - (s₁ + s₂) by omega] at this

end

/-- The sink–wall duality conjecture holds. -/
theorem statement_holds : statement := by
  intro s₁ s₂ h1 h2 x
  exact conj_of_gap (by omega) h2 (period_gt h1 h2) (wall_ne_zero_of_gap h1 h2) x

end AgenticConjectures.AdditiveSinkWallDuality
