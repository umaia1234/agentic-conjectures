import Mathlib

/-!
# OEIS A398189 — the four-case 2-adic valuation conjecture, proved

OEIS A398187 (P. Luschny, Jul 23 2026) is the triangle of generalized
Schenker sums `T(n, k) = Σ_{j=0..n-k} ((n-k)!/j!) · n^j` (`0 ≤ k ≤ n`);
column `k = 0` is the classical Schenker sums A063170. OEIS A398189
(P. Luschny, Jul 27 2026) is `v2(T(n, k))`, its 2-adic valuation, and the
entry conjectures ("We conjecture that: T(n, k) ="):

  - `v2((n-k)!)`, if `n` is even;
  - `1`, if `n` is odd and `k = 0`;
  - `0`, if `n` is odd and `k` is odd;
  - `v2(k+2)`, if `n` is odd, `k` is even, and not `k ≡ 14 (mod 16)`.

This module proves all four cases (`valuation_even`, `valuation_odd_k0`,
`valuation_odd_odd`, `valuation_odd_even`) plus `sixteen_dvd_excluded`:
in the excluded class `k ≡ 14 (mod 16)` (odd `n`) the valuation is ≥ 4.

Faithfulness notes (there is no upstream Lean snapshot for this entry):
- `S n m` is `Σ_{j=0..m} (m!/j!) n^j` written with `Nat.descFactorial`
  (`m!/j! = m.descFactorial (m-j)`, exact — no ℕ-division pitfalls);
  `S_eq_sum_div`/`T_eq_oeis_form` prove it equals the literal OEIS
  expression with `m ! / j !`.
- `T n k := S n (n - k)` matches the OEIS triangle for `0 ≤ k ≤ n`
  (ℕ-truncation makes `T` total; theorems carry `k ≤ n` exactly where the
  OEIS index geometry requires it, and are stated without it where the
  claim holds for all `k`).
- "v2" is `padicValNat 2`. The even case is stated as `v2((n-k)!)` exactly
  as in OEIS; by `sub_one_mul_padicValNat_factorial` this equals
  `(n-k) - A000120(n-k)`, the form quoted in the A398189/A063170 comments.
- The odd `k = 0` case is stated separately (`valuation_odd_k0`) because
  OEIS lists it separately, but it is the `k = 0` instance of
  `valuation_odd_even` since `v2(0+2) = 1`.

Proof shape: `S n (m+1) = (m+1)·S n m + n^(m+1)` (`S_succ`). For even `n`
an ultrametric induction gives `v2(S n m) = v2(m!)` (each `n^j` term,
`j ≥ 1`, is 2-adically negligible against `m!` since `v2(m!) < m` by
Legendre). For odd `n` everything is decided mod 16: the recurrence pushed
to `ZMod 16` is periodic in `m` with period 16 (`V_add_sixteen`, using
`a^4 = 1` for odd `a`), so `S n m mod 16` is a function of
`(n mod 16, m mod 16)` and the remaining claims reduce to a finite `decide`
over the 64 odd residue pairs (`core`).
-/

namespace AgenticConjectures.OeisA398189

open Finset Nat

/-- Generalized Schenker sum `S n m = Σ_{j=0..m} (m!/j!) · n^j`, with
`m!/j! = m.descFactorial (m - j)` (exact, division-free). -/
def S (n m : ℕ) : ℕ := ∑ j ∈ range (m + 1), m.descFactorial (m - j) * n ^ j

/-- OEIS A398187: `T(n, k) = Σ_{j=0..n-k} ((n-k)!/j!) · n^j` for `0 ≤ k ≤ n`. -/
def T (n k : ℕ) : ℕ := S n (n - k)

@[simp] theorem S_zero (n : ℕ) : S n 0 = 1 := by simp [S]

/-- The literal OEIS closed form, with (exact) ℕ-division. -/
theorem S_eq_sum_div (n m : ℕ) : S n m = ∑ j ∈ range (m + 1), m ! / j ! * n ^ j := by
  unfold S
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [Nat.descFactorial_eq_div (show m - j ≤ m by omega), show m - (m - j) = j by omega]

/-- `T` written exactly as in the OEIS definition of A398187. -/
theorem T_eq_oeis_form (n k : ℕ) :
    T n k = ∑ j ∈ range (n - k + 1), (n - k)! / j ! * n ^ j :=
  S_eq_sum_div n (n - k)

/-- The basic recurrence `S n (m+1) = (m+1)·S n m + n^(m+1)`
(OEIS A398187: `T(n, k) = (n-k)·T(n, k+1) + n^(n-k)`). -/
theorem S_succ (n m : ℕ) : S n (m + 1) = (m + 1) * S n m + n ^ (m + 1) := by
  unfold S
  rw [Finset.sum_range_succ, Nat.sub_self, Nat.descFactorial_zero, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [show m + 1 - j = (m - j) + 1 by omega, Nat.succ_descFactorial_succ, mul_assoc]

/-! ## Even `n`: `v2(S n m) = v2(m!)` by an ultrametric induction -/

theorem exists_odd_eq_of_even (n : ℕ) (hn : Even n) (m : ℕ) :
    ∃ c, Odd c ∧ S n m = 2 ^ padicValNat 2 (m !) * c := by
  induction m with
  | zero => exact ⟨1, odd_one, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc, hSc⟩ := ih
    obtain ⟨w, d, hd, hwd⟩ :=
      Nat.exists_eq_two_pow_mul_odd (show m + 1 ≠ 0 by omega)
    obtain ⟨s, hs⟩ := hn
    have hd2 : ¬ 2 ∣ d := by obtain ⟨u, hu⟩ := hd; omega
    have hd0 : d ≠ 0 := by obtain ⟨u, hu⟩ := hd; omega
    have hv' : padicValNat 2 ((m + 1)!) = w + padicValNat 2 (m !) := by
      rw [Nat.factorial_succ,
        padicValNat.mul (show m + 1 ≠ 0 by omega) (Nat.factorial_ne_zero m), hwd,
        padicValNat.mul (pow_ne_zero w two_ne_zero) hd0,
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hd2, add_zero]
    have hvlt : padicValNat 2 ((m + 1)!) < m + 1 :=
      padicValNat_factorial_lt_of_ne_zero 2 (Nat.succ_ne_zero m)
    obtain ⟨e, he1, he2⟩ : ∃ e, 1 ≤ e ∧ w + padicValNat 2 (m !) + e = m + 1 :=
      ⟨m + 1 - (w + padicValNat 2 (m !)), by omega, by omega⟩
    have h2e : (2 : ℕ) ∣ 2 ^ e * s ^ (m + 1) :=
      (dvd_pow_self 2 (by omega : e ≠ 0)).mul_right _
    refine ⟨d * c + 2 ^ e * s ^ (m + 1),
      (hd.mul hc).add_even (even_iff_two_dvd.mpr h2e), ?_⟩
    rw [hv', S_succ, hSc]
    nth_rewrite 1 [hwd]
    rw [show n = 2 * s by omega, ← he2]
    ring

/-- **A398189 conjecture, case `n` even** (at the `S` level, for all `m`):
`v2(S n m) = v2(m!)`. -/
theorem padicValNat_S_of_even (n : ℕ) (hn : Even n) (m : ℕ) :
    padicValNat 2 (S n m) = padicValNat 2 (m !) := by
  obtain ⟨c, hc, h⟩ := exists_odd_eq_of_even n hn m
  have hc2 : ¬ 2 ∣ c := by obtain ⟨u, hu⟩ := hc; omega
  have hc0 : c ≠ 0 := by obtain ⟨u, hu⟩ := hc; omega
  rw [h, padicValNat.mul (pow_ne_zero _ two_ne_zero) hc0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hc2, add_zero]

/-! ## Odd `n`, even `m`: `S n m` is odd -/

theorem odd_S_of_odd_even (n m : ℕ) (hn : Odd n) (hm : Even m) : Odd (S n m) := by
  rcases m with - | m
  · simp
  · rw [S_succ]
    exact (hm.mul_right (S n m)).add_odd hn.pow

/-! ## Odd `n`, odd `m`: reduction mod 16 -/

/-- The Schenker recurrence transported to `ZMod 16`. -/
def V (a : ZMod 16) : ℕ → ZMod 16
  | 0 => 1
  | m + 1 => ((m + 1 : ℕ) : ZMod 16) * V a m + a ^ (m + 1)

@[simp] theorem V_zero (a : ZMod 16) : V a 0 = 1 := rfl

theorem V_succ (a : ZMod 16) (m : ℕ) :
    V a (m + 1) = ((m + 1 : ℕ) : ZMod 16) * V a m + a ^ (m + 1) := rfl

theorem S_cast (n m : ℕ) : ((S n m : ℕ) : ZMod 16) = V ((n : ℕ) : ZMod 16) m := by
  induction m with
  | zero => simp
  | succ m ih => rw [S_succ, V_succ, ← ih]; push_cast; ring

/-- Every odd residue in `ZMod 16` has fourth power 1. -/
theorem pow_four_of_odd (n : ℕ) (hn : Odd n) : ((n : ℕ) : ZMod 16) ^ 4 = 1 := by
  have key : ∀ a : ZMod 16, ¬ 2 ∣ a.val → a ^ 4 = 1 := by decide
  refine key _ ?_
  rw [ZMod.val_natCast]
  have h2 : n % 2 = 1 := Nat.odd_iff.mp hn
  omega

/-- Base case of the period-16 property, checked by `decide` over all residues. -/
theorem V_sixteen : ∀ a : ZMod 16, a ^ 4 = 1 → V a 16 = V a 0 := by decide

theorem V_add_sixteen (a : ZMod 16) (ha : a ^ 4 = 1) : ∀ m, V a (m + 16) = V a m := by
  have h16 : a ^ 16 = 1 := by
    have h44 : a ^ (4 * 4) = 1 := by rw [pow_mul, ha, one_pow]
    exact h44
  intro m
  induction m with
  | zero => exact V_sixteen a ha
  | succ m ih =>
    rw [show m + 1 + 16 = (m + 16) + 1 by omega, V_succ, ih, V_succ,
      show m + 16 + 1 = (m + 1) + 16 by omega, Nat.cast_add, ZMod.natCast_self,
      add_zero, pow_add, h16, mul_one]

theorem V_mod_sixteen (a : ZMod 16) (ha : a ^ 4 = 1) (m : ℕ) : V a m = V a (m % 16) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 16 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · rw [show m = (m - 16) + 16 by omega, V_add_sixteen a ha, ih (m - 16) (by omega),
        show (m - 16) % 16 = ((m - 16) + 16) % 16 by omega]

/-- The finite core: over the 64 odd residue pairs `(2i+1, 2j+1) = (n, m) mod 16`,
the table value `w = (V (2i+1) (2j+1)).val` lies in the same 2-adic residue
class as `d = (n - m + 2) % 16 = (2i+1 + 18 - (2j+1)) % 16`: both are 0, or
both are odd, or both are `2·odd`, `4·odd`, `8·odd` (mod 16). By `decide`. -/
theorem core : ∀ i : Fin 8, ∀ j : Fin 8,
    ((2 * (i : ℕ) + 1 + 18 - (2 * (j : ℕ) + 1)) % 16 = 0 ∧
      (V ((2 * (i : ℕ) + 1 : ℕ) : ZMod 16) (2 * (j : ℕ) + 1)).val % 16 = 0) ∨
    ((2 * (i : ℕ) + 1 + 18 - (2 * (j : ℕ) + 1)) % 16 % 2 = 1 ∧
      (V ((2 * (i : ℕ) + 1 : ℕ) : ZMod 16) (2 * (j : ℕ) + 1)).val % 2 = 1) ∨
    ((2 * (i : ℕ) + 1 + 18 - (2 * (j : ℕ) + 1)) % 16 % 4 = 2 ∧
      (V ((2 * (i : ℕ) + 1 : ℕ) : ZMod 16) (2 * (j : ℕ) + 1)).val % 4 = 2) ∨
    ((2 * (i : ℕ) + 1 + 18 - (2 * (j : ℕ) + 1)) % 16 % 8 = 4 ∧
      (V ((2 * (i : ℕ) + 1 : ℕ) : ZMod 16) (2 * (j : ℕ) + 1)).val % 8 = 4) ∨
    ((2 * (i : ℕ) + 1 + 18 - (2 * (j : ℕ) + 1)) % 16 % 16 = 8 ∧
      (V ((2 * (i : ℕ) + 1 : ℕ) : ZMod 16) (2 * (j : ℕ) + 1)).val % 16 = 8) := by
  decide

/-! ## Small `padicValNat 2` evaluators from residue classes -/

theorem pv_of_odd {x : ℕ} (h : x % 2 = 1) : padicValNat 2 x = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

theorem pv_of_two {x : ℕ} (h : x % 4 = 2) : padicValNat 2 x = 1 := by
  have hx : x = 2 * (x / 2) ∧ x / 2 % 2 = 1 := by omega
  rw [hx.1, padicValNat.mul two_ne_zero (by omega),
    padicValNat.self one_lt_two, padicValNat.eq_zero_of_not_dvd (by omega)]

theorem pv_of_four {x : ℕ} (h : x % 8 = 4) : padicValNat 2 x = 2 := by
  have hx : x = 2 ^ 2 * (x / 4) ∧ x / 4 % 2 = 1 := by omega
  rw [hx.1, padicValNat.mul (by norm_num) (by omega),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by omega)]

theorem pv_of_eight {x : ℕ} (h : x % 16 = 8) : padicValNat 2 x = 3 := by
  have hx : x = 2 ^ 3 * (x / 8) ∧ x / 8 % 2 = 1 := by omega
  rw [hx.1, padicValNat.mul (by norm_num) (by omega),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by omega)]

/-! ## The odd-`n` valuation theorem -/

/-- **A398189 conjecture, odd rows** (at the `S` level): for odd `n` and odd
`m ≤ n`, if `(n - m + 2) % 16 ≠ 0` then `v2(S n m) = v2(n - m + 2)`; in the
excluded class, `16 ∣ S n m`. -/
theorem padicValNat_S_of_odd_odd (n m : ℕ) (hn : Odd n) (hm : Odd m) (hmn : m ≤ n) :
    ((n - m + 2) % 16 ≠ 0 → padicValNat 2 (S n m) = padicValNat 2 (n - m + 2)) ∧
    ((n - m + 2) % 16 = 0 → 16 ∣ S n m) := by
  have ha4 : ((n : ℕ) : ZMod 16) ^ 4 = 1 := pow_four_of_odd n hn
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  have hval : S n m % 16 = (V ((n % 16 : ℕ) : ZMod 16) (m % 16)).val := by
    rw [← ZMod.val_natCast, S_cast, V_mod_sixteen _ ha4, ZMod.natCast_mod]
  have hwlt : (V ((n % 16 : ℕ) : ZMod 16) (m % 16)).val < 16 := ZMod.val_lt _
  obtain ⟨i, hi, hai⟩ : ∃ i, i < 8 ∧ n % 16 = 2 * i + 1 := ⟨n % 16 / 2, by omega, by omega⟩
  obtain ⟨j, hj, haj⟩ : ∃ j, j < 8 ∧ m % 16 = 2 * j + 1 := ⟨m % 16 / 2, by omega, by omega⟩
  have hcore :
      ((2 * i + 1 + 18 - (2 * j + 1)) % 16 = 0 ∧
        (V ((2 * i + 1 : ℕ) : ZMod 16) (2 * j + 1)).val % 16 = 0) ∨
      ((2 * i + 1 + 18 - (2 * j + 1)) % 16 % 2 = 1 ∧
        (V ((2 * i + 1 : ℕ) : ZMod 16) (2 * j + 1)).val % 2 = 1) ∨
      ((2 * i + 1 + 18 - (2 * j + 1)) % 16 % 4 = 2 ∧
        (V ((2 * i + 1 : ℕ) : ZMod 16) (2 * j + 1)).val % 4 = 2) ∨
      ((2 * i + 1 + 18 - (2 * j + 1)) % 16 % 8 = 4 ∧
        (V ((2 * i + 1 : ℕ) : ZMod 16) (2 * j + 1)).val % 8 = 4) ∨
      ((2 * i + 1 + 18 - (2 * j + 1)) % 16 % 16 = 8 ∧
        (V ((2 * i + 1 : ℕ) : ZMod 16) (2 * j + 1)).val % 16 = 8) :=
    core ⟨i, hi⟩ ⟨j, hj⟩
  rw [← hai, ← haj] at hcore
  have hd : (n % 16 + 18 - m % 16) % 16 = (n - m + 2) % 16 := by omega
  rw [hd] at hcore
  constructor
  · intro hne
    rcases hcore with ⟨hdc, hw⟩ | ⟨hdc, hw⟩ | ⟨hdc, hw⟩ | ⟨hdc, hw⟩ | ⟨hdc, hw⟩
    · exact absurd hdc hne
    · rw [pv_of_odd (show S n m % 2 = 1 by omega),
        pv_of_odd (show (n - m + 2) % 2 = 1 by omega)]
    · rw [pv_of_two (show S n m % 4 = 2 by omega),
        pv_of_two (show (n - m + 2) % 4 = 2 by omega)]
    · rw [pv_of_four (show S n m % 8 = 4 by omega),
        pv_of_four (show (n - m + 2) % 8 = 4 by omega)]
    · rw [pv_of_eight (show S n m % 16 = 8 by omega),
        pv_of_eight (show (n - m + 2) % 16 = 8 by omega)]
  · intro hz
    rcases hcore with ⟨hdc, hw⟩ | ⟨hdc, hw⟩ | ⟨hdc, hw⟩ | ⟨hdc, hw⟩ | ⟨hdc, hw⟩
    · exact Nat.dvd_of_mod_eq_zero (by omega)
    all_goals omega

/-! ## The A398189 conjecture, stated on the OEIS triangle -/

/-- **Case "n even"**: `A398189(n, k) = v2((n-k)!)` (all `k`, in particular
the triangle range `k ≤ n`). -/
theorem valuation_even (n k : ℕ) (hn : Even n) :
    padicValNat 2 (T n k) = padicValNat 2 ((n - k)!) :=
  padicValNat_S_of_even n hn (n - k)

/-- **Case "n odd, k odd"**: `A398189(n, k) = 0`. -/
theorem valuation_odd_odd (n k : ℕ) (hn : Odd n) (hk : Odd k) :
    padicValNat 2 (T n k) = 0 :=
  pv_of_odd (Nat.odd_iff.mp (odd_S_of_odd_even n (n - k) hn (Nat.Odd.sub_odd hn hk)))

/-- **Case "n odd, k even, k ≢ 14 (mod 16)"**: `A398189(n, k) = v2(k+2)`
for `0 ≤ k ≤ n`. Subsumes the OEIS "n odd, k = 0" case since `v2(2) = 1`. -/
theorem valuation_odd_even (n k : ℕ) (hn : Odd n) (hk : Even k) (hkn : k ≤ n)
    (h14 : k % 16 ≠ 14) : padicValNat 2 (T n k) = padicValNat 2 (k + 2) := by
  have hm : Odd (n - k) := Nat.Odd.sub_even hkn hn hk
  have h := (padicValNat_S_of_odd_odd n (n - k) hn hm (Nat.sub_le n k)).1
  rw [show n - (n - k) + 2 = k + 2 by omega] at h
  exact h (by omega)

/-- **Case "n odd, k = 0"**: `A398189(n, 0) = 1` — the McGarvey conjecture
for the classical Schenker sums A063170, proved by Amdeberhan–Callan–Moll
(2012); here it is the `k = 0` instance of `valuation_odd_even`. -/
theorem valuation_odd_k0 (n : ℕ) (hn : Odd n) : padicValNat 2 (T n 0) = 1 := by
  have h := valuation_odd_even n 0 hn ⟨0, rfl⟩ (Nat.zero_le n) (by norm_num)
  rwa [show (0 : ℕ) + 2 = 2 by norm_num, padicValNat.self one_lt_two] at h

/-- **The excluded class `k ≡ 14 (mod 16)`** (odd `n`), where OEIS
conjectures no simple formula: the valuation is at least 4, stated as
`16 ∣ A398187(n, k)`. -/
theorem sixteen_dvd_excluded (n k : ℕ) (hn : Odd n) (hkn : k ≤ n) (h14 : k % 16 = 14) :
    16 ∣ T n k := by
  have hk : Even k := Nat.even_iff.mpr (by omega)
  have hm : Odd (n - k) := Nat.Odd.sub_even hkn hn hk
  have h := (padicValNat_S_of_odd_odd n (n - k) hn hm (Nat.sub_le n k)).2
  rw [show n - (n - k) + 2 = k + 2 by omega] at h
  exact h (by omega)

end AgenticConjectures.OeisA398189
