import Mathlib

/-!
# Additive wall and sink subtraction: definitions

Both games use the subtraction set `S = {s₁, s₂, s₁ + s₂}` and are defined directly by their
mex recursions.

* `wall s₁ s₂ x` (`x : ℕ`): the options of `x` are the `x - s` with `s ∈ S` and `s ≤ x`.
* `sink s₁ s₂ y` (`y : ℤ`): every `y ≤ 0` is terminal with value `0`; the options of `y ≥ 1` are
  all `y - s` with `s ∈ S`, including those `≤ 0`.

Both definitions skip moves of size `0`, so that they terminate for every pair `s₁, s₂`. When
`1 ≤ s₁ < s₂`, the only case the conjecture concerns, every move is positive and the filter
changes nothing.

`period s₁ s₂` is the period length `p(m, δ)` of Theorem 3 (`thm:main`) of Bhagat, Larsson,
Manabe and Yamashita, with `m = s₁` and `δ = s₂ - s₁`.
-/

namespace AgenticConjectures.AdditiveSinkWallDuality

/-- The minimum excludant of a finite set of natural numbers. -/
def mex (T : Finset ℕ) : ℕ :=
  Nat.find (Infinite.exists_notMem_finset T)

theorem mex_eq_iff {T : Finset ℕ} {k : ℕ} : mex T = k ↔ k ∉ T ∧ ∀ j < k, j ∈ T := by
  unfold mex
  rw [Nat.find_eq_iff]
  simp

/-- The subtraction set `{s₁, s₂, s₁ + s₂}`. -/
def moves (s₁ s₂ : ℕ) : Finset ℕ :=
  {s₁, s₂, s₁ + s₂}

/-- Nim-values of additive wall subtraction. -/
def wall (s₁ s₂ : ℕ) (x : ℕ) : ℕ :=
  mex (((moves s₁ s₂).filter (fun s => 0 < s ∧ s ≤ x)).attach.image
    (fun s => wall s₁ s₂ (x - s.1)))
termination_by x
decreasing_by
  have := (Finset.mem_filter.1 s.2).2
  omega

/-- Nim-values of additive sink subtraction. -/
def sink (s₁ s₂ : ℕ) (y : ℤ) : ℕ :=
  if _h : y ≤ 0 then 0 else
    mex (((moves s₁ s₂).filter (fun s => 0 < s)).attach.image
      (fun s => sink s₁ s₂ (y - s.1)))
termination_by y.toNat
decreasing_by
  have := (Finset.mem_filter.1 s.2).2
  omega

/-- The period length of Theorem 3 of Bhagat–Larsson–Manabe–Yamashita: with `m = s₁`,
`δ = s₂ - s₁` and `d = δ mod 2m`, it is `3m + 2δ - d` if `d ≤ m` and
`m (m + 2δ + d) / gcd(m, d)` otherwise. -/
def period (s₁ s₂ : ℕ) : ℕ :=
  let m := s₁
  let δ := s₂ - s₁
  let d := δ % (2 * m)
  if d ≤ m then 3 * m + 2 * δ - d else m * (m + 2 * δ + d) / Nat.gcd m d

/-- The permutation `σ` of the conjecture: it swaps `0` and `2` and fixes every other value
(the values that occur are `0, 1, 2, 3`). -/
def sigma : ℕ → ℕ
  | 0 => 2
  | 2 => 0
  | n => n

section basic

variable {s₁ s₂ : ℕ}

theorem mem_moves {s : ℕ} : s ∈ moves s₁ s₂ ↔ s = s₁ ∨ s = s₂ ∨ s = s₁ + s₂ := by
  simp [moves]

/-- The mex recursion of the wall game, with the options listed by value. -/
theorem wall_eq_iff (h : 0 < s₁) (h' : s₁ < s₂) (x k : ℕ) :
    wall s₁ s₂ x = k ↔
      (∀ s ∈ moves s₁ s₂, s ≤ x → wall s₁ s₂ (x - s) ≠ k) ∧
        ∀ j < k, ∃ s ∈ moves s₁ s₂, s ≤ x ∧ wall s₁ s₂ (x - s) = j := by
  have hpos : ∀ s ∈ moves s₁ s₂, 0 < s := by
    intro s hs; rcases mem_moves.1 hs with rfl | rfl | rfl <;> omega
  rw [wall, mex_eq_iff]
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
    Finset.mem_filter, not_exists]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs hsx => h1 s ⟨hs, hpos s hs, hsx⟩, fun j hj => ?_⟩
    obtain ⟨s, ⟨hs, -, hsx⟩, rfl⟩ := h2 j hj
    exact ⟨s, hs, hsx, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs => h1 s hs.1 hs.2.2, fun j hj => ?_⟩
    obtain ⟨s, hs, hsx, rfl⟩ := h2 j hj
    exact ⟨s, ⟨hs, hpos s hs, hsx⟩, rfl⟩

theorem sink_of_nonpos {y : ℤ} (hy : y ≤ 0) : sink s₁ s₂ y = 0 := by
  rw [sink, dif_pos hy]

/-- The mex recursion of the sink game at a positive position. -/
theorem sink_eq_iff (h : 0 < s₁) (h' : s₁ < s₂) {y : ℤ} (hy : 0 < y) (k : ℕ) :
    sink s₁ s₂ y = k ↔
      (∀ s ∈ moves s₁ s₂, sink s₁ s₂ (y - s) ≠ k) ∧
        ∀ j < k, ∃ s ∈ moves s₁ s₂, sink s₁ s₂ (y - s) = j := by
  have hpos : ∀ s ∈ moves s₁ s₂, 0 < s := by
    intro s hs; rcases mem_moves.1 hs with rfl | rfl | rfl <;> omega
  rw [sink, dif_neg (by omega), mex_eq_iff]
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
    Finset.mem_filter, not_exists]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs => h1 s ⟨hs, hpos s hs⟩, fun j hj => ?_⟩
    obtain ⟨s, ⟨hs, -⟩, rfl⟩ := h2 j hj
    exact ⟨s, hs, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs => h1 s hs.1, fun j hj => ?_⟩
    obtain ⟨s, hs, rfl⟩ := h2 j hj
    exact ⟨s, ⟨hs, hpos s hs⟩, rfl⟩

end basic

end AgenticConjectures.AdditiveSinkWallDuality
