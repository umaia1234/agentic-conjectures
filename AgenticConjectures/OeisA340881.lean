import Mathlib

/-!
# OEIS A340881 — modular periodicity

[OEIS A340881](https://oeis.org/A340881) (row sums of A340880, offset 1) is

  `a(n) = ∑_{k=0}^{n-1} 2^(k(k+1)/2) * ∏_{j=k+1}^{n-1} (2^j - 1)`.

The entry records two conjectures: modulo a prime `p` the sequence is
"purely periodic with minimum period dividing 2*(p - 1)", and "for composite
n, the sequence taken modulo n is eventually periodic".  `statement1` and
`statement2` state them, and `statement1_holds` / `statement2_holds` prove
them, following `problems/oeis-a340881/PROOF.md`.

Correspondence with the upstream snapshot
`problems/oeis-a340881/upstream/340881_294a5574.lean`:

* `a` is the upstream `a`, term for term.  `Nat.choose (k + 1) 2 = k(k+1)/2`,
  and the natural subtraction `2 ^ j - 1` is exact because `2 ^ j ≥ 1`.
* `oeis_340881_conjecture_0` is the upstream theorem of the same name, with
  the same statement, now proved.  It asserts only that `2(p - 1)` is a
  period from `n = 1`; `statement1` adds the minimum-period clause.

Semantic choices:

* "Purely periodic" means periodic from the offset `n = 1` (`IsPeriodFrom p 1`).
  `a 0 = 0` is outside the sequence and never constrained.
* "Minimum period divides `2(p - 1)`" means: some positive period exists, and
  every positive period with no smaller positive period divides `2(p - 1)`.
* `statement2` keeps the OEIS restriction to composite moduli;
  `eventually_periodic` proves it for every modulus `m ≥ 1`.
* `ord_m(2)` is `orderOf (2 : ZMod m)`; `orderOf_two_pos` shows it is positive
  for odd `m`.  PROOF.md's explicit periods are `period_odd` (pure period
  `2 ord_m(2)` for odd `m`) and `modEq_two_pow_mul_odd` (period `2 ord_u(2)` for
  `n ≥ max(1, e)` when `m = 2^e u`, `u` odd; this is period 2 when `u = 1`).
-/

namespace AgenticConjectures.OeisA340881

open Finset

/-- Row sums of A340880 (the upstream definition, term for term). -/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))

/-- `T` is a period of `n ↦ a n % m` for all `n ≥ N`. -/
def IsPeriodFrom (m N T : ℕ) : Prop := ∀ n ≥ N, a (n + T) % m = a n % m

/-- OEIS conjecture 1: modulo every prime `p` the sequence is purely periodic,
with minimum period dividing `2(p - 1)`. -/
def statement1 : Prop :=
  ∀ p : ℕ, p.Prime →
    (∃ T, 0 < T ∧ IsPeriodFrom p 1 T) ∧
    ∀ d, 0 < d → IsPeriodFrom p 1 d → (∀ d', 0 < d' → d' < d → ¬ IsPeriodFrom p 1 d') →
      d ∣ 2 * (p - 1)

/-- OEIS conjecture 2: modulo every composite `m` the sequence is eventually
periodic. -/
def statement2 : Prop :=
  ∀ m : ℕ, 1 < m → ¬ m.Prime → ∃ N T, 0 < T ∧ IsPeriodFrom m N T

/-- The defining sum read in a commutative ring. -/
def A (R : Type*) [CommRing R] (n : ℕ) : R :=
  ∑ k ∈ range n, (2 : R) ^ Nat.choose (k + 1) 2 * ∏ j ∈ Ico (k + 1) n, ((2 : R) ^ j - 1)

theorem cast_a (R : Type*) [CommRing R] (n : ℕ) : ((a n : ℕ) : R) = A R n := by
  simp only [a, A, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_prod, Nat.cast_ofNat]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  refine prod_congr rfl fun j _ => ?_
  rw [Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  ring

theorem two_mul_choose_two (k : ℕ) : 2 * Nat.choose (k + 1) 2 = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right, mul_add, ih]
    ring

/-- PROOF.md (1.4) with `T = 2L`: `E(ℓ + 2L) = E(ℓ) + L(2ℓ + 2L + 1)`. -/
theorem choose_shift (L l : ℕ) :
    Nat.choose (2 * L + l + 1) 2 = Nat.choose (l + 1) 2 + L * (2 * l + 2 * L + 1) := by
  have h1 := two_mul_choose_two (2 * L + l)
  have h2 := two_mul_choose_two l
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
  linarith

/-- PROOF.md Lemma 1.4: `A(n+1) = (2^n - 1) A(n) + 2^E(n)`. -/
theorem A_succ (R : Type*) [CommRing R] (n : ℕ) :
    A R (n + 1) = ((2 : R) ^ n - 1) * A R n + 2 ^ Nat.choose (n + 1) 2 := by
  rw [A, sum_range_succ, Ico_self, prod_empty, mul_one, A, mul_sum]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [prod_Ico_succ_top (Nat.succ_le_of_lt (mem_range.1 hk))]
  ring

/-- PROOF.md Lemma 1.1: if `2^L = 1` in `R`, then `2L` is a period of `A R`
from `n = 1`. -/
theorem A_add_two_mul (R : Type*) [CommRing R] {L : ℕ} (hL : (2 : R) ^ L = 1) {n : ℕ}
    (hn : 1 ≤ n) : A R (n + 2 * L) = A R n := by
  have hT : (2 : R) ^ (2 * L) = 1 := by rw [pow_mul', hL, one_pow]
  rw [A, add_comm n, sum_range_add]
  -- Terms with `k < 2L` contain the factor `2^(2L) - 1 = 0`.
  have h1 : ∑ k ∈ range (2 * L),
      (2 : R) ^ Nat.choose (k + 1) 2 * ∏ j ∈ Ico (k + 1) (2 * L + n), ((2 : R) ^ j - 1) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    have hmem : 2 * L ∈ Ico (k + 1) (2 * L + n) := by
      have := mem_range.1 hk
      rw [mem_Ico]
      omega
    rw [prod_eq_zero hmem (by rw [hT, sub_self]), mul_zero]
  rw [h1, zero_add, A]
  -- The term `k = 2L + ℓ` agrees with the `ℓ`-th term of `A R n`.
  refine sum_congr rfl fun l _ => ?_
  congr 1
  · rw [choose_shift, pow_add, pow_mul, hL, one_pow, mul_one]
  · rw [show 2 * L + l + 1 = l + 1 + 2 * L by ring, show 2 * L + n = n + 2 * L by ring,
      ← prod_Ico_add' (fun j => (2 : R) ^ j - 1)]
    refine prod_congr rfl fun r _ => ?_
    rw [pow_add, hT, mul_one]

theorem two_pow_totient {m : ℕ} (hm : Odd m) : (2 : ZMod m) ^ Nat.totient m = 1 := by
  have := (ZMod.natCast_eq_natCast_iff _ _ _).2
    (Nat.ModEq.pow_totient (Nat.coprime_two_left.2 hm))
  simpa using this

theorem orderOf_two_pos {m : ℕ} (hm : Odd m) : 0 < orderOf (2 : ZMod m) :=
  (isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.totient_pos.2 hm.pos, two_pow_totient hm⟩).orderOf_pos

/-- `2 ord_m(2)` is a period of `a n mod m` from `n = 1` (trivially so when
`2` has no multiplicative order modulo `m`). -/
theorem modEq_add_two_mul_orderOf (m : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    a (n + 2 * orderOf (2 : ZMod m)) ≡ a n [MOD m] := by
  rw [← ZMod.natCast_eq_natCast_iff, cast_a, cast_a]
  exact A_add_two_mul _ (pow_orderOf_eq_one _) hn

/-- PROOF.md §1.2: for odd `m`, `2 ord_m(2)` is a positive pure period. -/
theorem period_odd {m : ℕ} (hm : Odd m) :
    0 < orderOf (2 : ZMod m) ∧ IsPeriodFrom m 1 (2 * orderOf (2 : ZMod m)) :=
  ⟨orderOf_two_pos hm, fun _ hn => modEq_add_two_mul_orderOf m hn⟩

/-- PROOF.md Lemma 1.5 (1.7): modulo `2^e`, `A(n+1) = -A(n)` for `n ≥ e ≥ 1`. -/
theorem A_succ_two_pow {e n : ℕ} (he : 1 ≤ e) (hn : e ≤ n) :
    A (ZMod (2 ^ e)) (n + 1) = -A (ZMod (2 ^ e)) n := by
  have h0 : ∀ k, e ≤ k → (2 : ZMod (2 ^ e)) ^ k = 0 := by
    intro k hk
    have he0 : (2 : ZMod (2 ^ e)) ^ e = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ e)
    rw [← Nat.add_sub_cancel' hk, pow_add, he0, zero_mul]
  have hc : n ≤ Nat.choose (n + 1) 2 := by
    have := two_mul_choose_two n
    nlinarith
  rw [A_succ, h0 n hn, h0 _ (hn.trans hc)]
  ring

/-- PROOF.md Lemma 1.5 (1.8), iterated: every even shift is a period modulo
`2^e` from `n = e`. -/
theorem modEq_two_pow (e : ℕ) {n : ℕ} (hn : e ≤ n) (j : ℕ) :
    a (n + 2 * j) ≡ a n [MOD 2 ^ e] := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [Nat.modEq_one]
  rw [← ZMod.natCast_eq_natCast_iff, cast_a, cast_a]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show n + 2 * (j + 1) = n + 2 * j + 1 + 1 by ring,
      A_succ_two_pow (n := n + 2 * j + 1) he (by omega),
      A_succ_two_pow (n := n + 2 * j) he (by omega), neg_neg, ih]

/-- PROOF.md Theorem 1.6: for `m = 2^e u` with `u` odd, `2 ord_u(2)` is a
period of `a n mod m` for `n ≥ max(1, e)`. -/
theorem modEq_two_pow_mul_odd (e : ℕ) {u : ℕ} (hu : Odd u) {n : ℕ} (hn : max 1 e ≤ n) :
    a (n + 2 * orderOf (2 : ZMod u)) ≡ a n [MOD 2 ^ e * u] := by
  have hcop : Nat.Coprime (2 ^ e) u := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hu)
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  exact ⟨modEq_two_pow e (le_of_max_le_right hn) _,
    modEq_add_two_mul_orderOf u (le_of_max_le_left hn)⟩

/-- Modulo every `m ≥ 1`, the sequence is eventually periodic. -/
theorem eventually_periodic (m : ℕ) (hm : 0 < m) : ∃ N T, 0 < T ∧ IsPeriodFrom m N T := by
  obtain ⟨e, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  exact ⟨max 1 e, 2 * orderOf (2 : ZMod u), by have := orderOf_two_pos hu; omega,
    fun n hn => modEq_two_pow_mul_odd e hu hn⟩

/-- The upstream `oeis_340881_conjecture_0`, verbatim: `2(p - 1)` is a period
modulo every prime `p` from `n = 1`. -/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
    ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  rcases hp.eq_two_or_odd' with rfl | hodd
  · simpa using modEq_two_pow 1 hn 1
  · have hL : (2 : ZMod p) ^ (p - 1) = 1 := by
      rw [← Nat.totient_prime hp]
      exact two_pow_totient hodd
    have := A_add_two_mul (ZMod p) hL hn
    rwa [← cast_a, ← cast_a, ZMod.natCast_eq_natCast_iff'] at this

theorem IsPeriodFrom.mul {m N d : ℕ} (h : IsPeriodFrom m N d) (q : ℕ) :
    IsPeriodFrom m N (q * d) := by
  induction q with
  | zero => intro n _; simp
  | succ q ih =>
    intro n hn
    rw [add_mul, one_mul, ← add_assoc, h (n + q * d) (by omega), ih n hn]

/-- PROOF.md Lemma 1.2: the remainder of one period by another is a period. -/
theorem IsPeriodFrom.mod {m N d T : ℕ} (hd : IsPeriodFrom m N d) (hT : IsPeriodFrom m N T) :
    IsPeriodFrom m N (T % d) := by
  intro n hn
  have h1 := hd.mul (T / d) (n + T % d) (by omega)
  rw [add_assoc, Nat.mod_add_div' T d] at h1
  rw [← h1]
  exact hT n hn

/-- PROOF.md Lemma 1.2: a minimal positive period divides every period. -/
theorem dvd_of_minimal {m N d T : ℕ} (hd0 : 0 < d) (hd : IsPeriodFrom m N d)
    (hmin : ∀ d', 0 < d' → d' < d → ¬ IsPeriodFrom m N d') (hT : IsPeriodFrom m N T) :
    d ∣ T := by
  by_contra hndvd
  exact hmin (T % d) (Nat.pos_of_ne_zero fun h => hndvd (Nat.dvd_of_mod_eq_zero h))
    (Nat.mod_lt _ hd0) (hd.mod hT)

/-- OEIS conjecture 1 holds. -/
theorem statement1_holds : statement1 := by
  intro p hp
  have hper : IsPeriodFrom p 1 (2 * (p - 1)) := oeis_340881_conjecture_0 p hp
  exact ⟨⟨2 * (p - 1), by have := hp.two_le; omega, hper⟩,
    fun d hd0 hd hmin => dvd_of_minimal hd0 hd hmin hper⟩

/-- OEIS conjecture 2 holds. -/
theorem statement2_holds : statement2 :=
  fun m hm _ => eventually_periodic m (by omega)

end AgenticConjectures.OeisA340881
