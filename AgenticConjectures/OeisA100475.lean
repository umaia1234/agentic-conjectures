import Mathlib

/-!
# OEIS A100475 — no positive start gives an ultimately periodic orbit

OEIS A100475 iterates `k ↦ reversal(p_k)` from `1`, where `p_k` is the `k`-th
prime (`p_1 = 2`) and `reversal` reverses the decimal digits. Its comment asks
whether a start other than `1` ever goes into a loop. The definitions below are
copied term for term (modulo namespace) from
`problems/oeis-a100475/upstream/100475.lean`, the Formal Conjectures snapshot at
commit `c094b979118b89adb77cf5f8d923ac9dd2e51b1d`; the upstream open theorem
`conjecture` is recorded as `statement`.

We prove `not_isUltimatelyPeriodic`: for every `x > 0` (including `x = 1`) the
orbit `aStartAt x` is not ultimately periodic. Hence `not_statement`.

Proof outline:
1. A prime is not divisible by `10`, so reversing its digits keeps its number of
   decimal digits, and `k < p_k`. So the digit count never decreases along an
   orbit (orbits of positive starts never reach `0`).
2. In a periodic tail the digit count is therefore a constant `d`. A tail value
   `k` has `10 ^ (d - 1) ≤ k` and `p_k < 10 ^ d`, so `10 ^ (d - 1) ≤ π(10 ^ d)`.
3. `π(10 ^ d) < 10 ^ (d - 1)` for every `d ≥ 5`: an exact kernel count of the
   primes below `100112` (`d = 5`); the exact count below `509712` plus a
   dyadic bound from `centralBinom m ≤ 4 ^ m` (`d = 6`); four more dyadic
   blocks (`d = 7`); an induction based on `primorial n ≤ 4 ^ n` (`d ≥ 8`).
4. For `d ≤ 4` every tail value is at most `π(10 ^ 4) = 1229`, and a kernel
   check over all `k ≤ 1229` shows that each orbit leaves its digit band.

All finite checks are `decide +kernel` evaluations, with primality decided by
`Nat.gcd n B ! = 1` for `B < n < (B + 1) ^ 2` (`prime_iff_gcd_factorial`).

Adaptations from upstream: no `module` header, no `FormalConjecturesUtil`
import, no `@[expose] public section`, and no `category`/`AMS` attributes; the
open theorem `conjecture` becomes `def statement`; the upstream API and test
lemmas (`a_succ`, `a_0`–`a_4`, `aStartAt_zero`, `conjecture_with_zero`) are
not repeated.
-/

namespace AgenticConjectures.OeisA100475

open Nat Finset

/-! ## Upstream definitions (verbatim) -/

/-- Reverses the base 10 digits of a natural number. -/
def reverseDigits (k : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 k |>.reverse)

/-- The primary defining sequence `a`.
a n is the Prime-th recurrence with reversal at each step.
$a(n) = \operatorname{reversal}(p_{a(n-1)})$
with $a(0)=1$, where $p_k$ is the $k$-th prime number (i.e., $p_1=2, p_2=3, \dots$). -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    let k := a n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

/-- Definition of the generalized sequence starting at x. -/
noncomputable def aStartAt (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 =>
    let k := aStartAt x n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

/-- A sequence $f : \mathbb{N} \to \mathbb{N}$ is ultimately periodic if there exist
$N, P \in \mathbb{N}$, with $P>0$, such that for all $n \ge N$, $f(n+P) = f(n)$. -/
def IsUltimatelyPeriodic (f : ℕ → ℕ) : Prop :=
  ∃ N P, P > 0 ∧ ∀ n, n ≥ N → f (n + P) = f n

/-- The upstream open theorem `OeisA100475.conjecture`: starting at a positive value other
than $a(0) = 1$, the sequence goes into a loop. -/
def statement : Prop :=
  ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x)

/-! ## Digit reversal and primality helpers -/

lemma prime_mod_ten_ne_zero {p : ℕ} (hp : p.Prime) : p % 10 ≠ 0 := by
  intro h
  have h10 : 10 ∣ p := Nat.dvd_of_mod_eq_zero h
  have h2 : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (dvd_trans (by norm_num) h10)
  have h5 : 5 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 (dvd_trans (by norm_num) h10)
  omega

lemma length_digits_reverseDigits {p : ℕ} (hp : p % 10 ≠ 0) :
    (Nat.digits 10 (reverseDigits p)).length = (Nat.digits 10 p).length := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; simp at hp)
  unfold reverseDigits
  rw [Nat.digits_ofDigits 10 (by norm_num)]
  · simp
  · intro l hl
    exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.1 hl)
  · intro hne
    rw [List.getLast_reverse]
    simp [Nat.digits_def' (by norm_num : 1 < 10) hp0, hp]

/-- Kernel-friendly digit reversal with fuel: `revAux fuel n acc`. -/
def revAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, n, acc => cond (Nat.beq n 0) acc (revAux fuel (n / 10) (acc * 10 + n % 10))

lemma reverseDigits_zero : reverseDigits 0 = 0 := by simp [reverseDigits]

lemma reverseDigits_of_pos {n : ℕ} (hn : 0 < n) :
    reverseDigits n = reverseDigits (n / 10) + 10 ^ (Nat.digits 10 (n / 10)).length * (n % 10) := by
  unfold reverseDigits
  rw [Nat.digits_def' (by norm_num : 1 < 10) hn, List.reverse_cons, Nat.ofDigits_append,
    List.length_reverse, Nat.ofDigits_singleton]

lemma revAux_spec (fuel : ℕ) : ∀ n acc : ℕ, (Nat.digits 10 n).length ≤ fuel →
    revAux fuel n acc = acc * 10 ^ (Nat.digits 10 n).length + reverseDigits n := by
  induction fuel with
  | zero =>
    intro n acc h
    have hn : n = 0 := by simpa [Nat.digits_eq_nil_iff_eq_zero] using h
    subst hn
    simp [revAux, reverseDigits_zero]
  | succ fuel ih =>
    intro n acc h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [revAux, reverseDigits_zero]
    · have hlen : (Nat.digits 10 n).length = (Nat.digits 10 (n / 10)).length + 1 := by
        rw [Nat.digits_def' (by norm_num : 1 < 10) hn, List.length_cons]
      have hb : Nat.beq n 0 = false := Bool.eq_false_iff.2 (by simpa using hn.ne')
      simp only [revAux, hb, cond_false]
      rw [ih (n / 10) _ (by omega), reverseDigits_of_pos hn, hlen, pow_succ]
      ring

/-- Kernel-friendly reversal, correct below `10 ^ 10`. -/
def revB (n : ℕ) : ℕ := revAux 10 n 0

lemma revB_eq {n : ℕ} (hn : n < 10 ^ 10) : revB n = reverseDigits n := by
  rw [revB, revAux_spec 10 n 0 ((Nat.digits_length_le_iff (by norm_num) n).2 hn)]
  simp

theorem prime_iff_gcd_factorial {B n : ℕ} (hB : B < n) (hn : n < (B + 1) ^ 2) :
    n.Prime ↔ Nat.gcd n B ! = 1 := by
  constructor
  · intro hp
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 ?_
    rw [hp.dvd_factorial]
    omega
  · intro h
    by_contra hnp
    have hn1 : n ≠ 1 := by
      rintro rfl
      have : B = 0 := by omega
      subst this
      norm_num at hn
    have hq := Nat.minFac_prime hn1
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hle : n.minFac ≤ B := by
      by_contra hc
      have : (B + 1) ^ 2 ≤ n.minFac ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have h1 : n.minFac ∣ Nat.gcd n B ! :=
      Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial hq.pos hle)
    rw [h] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.1 h1)

/-- `15 !`, used by `isPrimeB`. -/
def F15 : ℕ := 15 !

/-- `255 !`, used by `isPrimeB`. -/
def F255 : ℕ := 255 !

/-- Kernel-friendly primality test, correct below `2 ^ 16` (`isPrimeB_iff`). -/
def isPrimeB (n : ℕ) : Bool :=
  cond (Nat.blt n 2) false <| cond (Nat.blt n 4) true <|
    cond (Nat.blt n 16) (Nat.beq (Nat.gcd n 6) 1) <|
      cond (Nat.blt n 256) (Nat.beq (Nat.gcd n F15) 1) (Nat.beq (Nat.gcd n F255) 1)

lemma isPrimeB_iff {n : ℕ} (hn : n < 65536) : isPrimeB n = true ↔ n.Prime := by
  unfold isPrimeB
  by_cases h1 : n < 2
  · rw [show Nat.blt n 2 = true by simpa using h1, cond_true]
    simp only [Bool.false_eq_true, false_iff]
    intro hp; have := hp.two_le; omega
  rw [show Nat.blt n 2 = false from Bool.eq_false_iff.2 (by simpa using h1), cond_false]
  by_cases h2 : n < 4
  · rw [show Nat.blt n 4 = true by simpa using h2, cond_true]
    simp only [true_iff]
    interval_cases n <;> norm_num
  rw [show Nat.blt n 4 = false from Bool.eq_false_iff.2 (by simpa using h2), cond_false]
  by_cases h3 : n < 16
  · rw [show Nat.blt n 16 = true by simpa using h3, cond_true, Nat.beq_eq,
      prime_iff_gcd_factorial (B := 3) (by omega) (by omega)]
    rfl
  rw [show Nat.blt n 16 = false from Bool.eq_false_iff.2 (by simpa using h3), cond_false]
  by_cases h4 : n < 256
  · rw [show Nat.blt n 256 = true by simpa using h4, cond_true, Nat.beq_eq,
      prime_iff_gcd_factorial (B := 15) (by omega) (by omega), F15]
  · rw [show Nat.blt n 256 = false from Bool.eq_false_iff.2 (by simpa using h4), cond_false,
      Nat.beq_eq, prime_iff_gcd_factorial (B := 255) (by omega) (by omega), F255]

theorem length_filter_range (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    ((List.range N).filter (fun n => decide (p n))).length = Nat.count p N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Nat.count_succ]
    by_cases h : p N <;> simp [h]

theorem nth_eq_getD_filter_range (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    ∀ i < Nat.count p N,
      Nat.nth p i = ((List.range N).filter (fun n => decide (p n))).getD i 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    intro i hi
    rw [List.range_succ, List.filter_append]
    rcases lt_or_ge i (Nat.count p N) with h | h
    · rw [List.getD_append _ _ _ _ (by rw [length_filter_range]; exact h)]
      exact ih i h
    · rw [Nat.count_succ] at hi
      by_cases hpN : p N
      · simp only [hpN, if_true] at hi
        have hieq : i = Nat.count p N := by omega
        subst hieq
        rw [List.getD_append_right _ _ _ _ (by rw [length_filter_range])]
        simp [hpN, length_filter_range, Nat.nth_count hpN]
      · simp only [hpN, if_false] at hi
        omega


/-! ## Counting primes -/

/-- `cntCop F k a` counts the `i < 2 ^ k` with `Nat.gcd (a + i) F = 1`. -/
def cntCop (F : ℕ) (k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun a => cond (Nat.beq (Nat.gcd a F) 1) 1 0)
    (fun k ih a => Nat.add (ih a) (ih (Nat.add a (Nat.pow 2 k)))) k

/-- `cntChunks F k c a` is the sum of `cntCop F k` over `c` consecutive blocks from `a`. -/
def cntChunks (F k : ℕ) (c : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih a => Nat.add (cntCop F k a) (ih (Nat.add a (Nat.pow 2 k)))) c

lemma cntCop_zero (F a : ℕ) : cntCop F 0 a = cond (Nat.beq (Nat.gcd a F) 1) 1 0 := rfl

lemma cntCop_succ (F k a : ℕ) :
    cntCop F (k + 1) a = cntCop F k a + cntCop F k (a + 2 ^ k) := rfl

lemma cntChunks_zero (F k a : ℕ) : cntChunks F k 0 a = 0 := rfl

lemma cntChunks_succ (F k c a : ℕ) :
    cntChunks F k (c + 1) a = cntCop F k a + cntChunks F k c (a + 2 ^ k) := rfl

lemma cntCop_eq (F k : ℕ) :
    ∀ a, cntCop F k a = Nat.count (fun i => Nat.gcd (a + i) F = 1) (2 ^ k) := by
  induction k with
  | zero =>
    intro a
    rw [cntCop_zero, pow_zero, Nat.count_one, add_zero]
    cases hb : Nat.beq (Nat.gcd a F) 1
    · simp [Nat.ne_of_beq_eq_false hb]
    · simp [Nat.eq_of_beq_eq_true hb]
  | succ k ih =>
    intro a
    rw [cntCop_succ, ih, ih, pow_succ, mul_two, Nat.count_add]
    simp only [add_assoc]

lemma count_prime_add_cntCop {B a k : ℕ} (h1 : B < a) (h2 : a + 2 ^ k ≤ (B + 1) ^ 2) :
    Nat.count Nat.Prime (a + 2 ^ k) = Nat.count Nat.Prime a + cntCop B ! k a := by
  rw [cntCop_eq, Nat.count_add]
  congr 1
  apply le_antisymm <;> apply Nat.count_mono_left <;> intro i hi h
  · exact (prime_iff_gcd_factorial (by omega) (by omega)).1 h
  · exact (prime_iff_gcd_factorial (by omega) (by omega)).2 h

lemma count_prime_add_cntChunks {B k : ℕ} (c : ℕ) : ∀ a, B < a →
    a + c * 2 ^ k ≤ (B + 1) ^ 2 →
    Nat.count Nat.Prime (a + c * 2 ^ k) = Nat.count Nat.Prime a + cntChunks B ! k c a := by
  induction c with
  | zero => intro a _ _; simp [cntChunks_zero]
  | succ c ih =>
    intro a h1 h2
    rw [cntChunks_succ]
    have e : a + (c + 1) * 2 ^ k = (a + 2 ^ k) + c * 2 ^ k := by ring
    have h3 : a + 2 ^ k + c * 2 ^ k ≤ (B + 1) ^ 2 := by rw [← e]; exact h2
    have h4 : a + 2 ^ k ≤ (B + 1) ^ 2 := le_trans (Nat.le_add_right _ _) h3
    rw [e, ih (a + 2 ^ k) (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _)) h3,
      count_prime_add_cntCop h1 h4]
    ring

lemma count_eq_add_card (p : ℕ → Prop) [DecidablePred p] {a b : ℕ} (h : a ≤ b) :
    Nat.count p b = Nat.count p a + #{x ∈ Ico a b | p x} := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  simp only [range_eq_Ico]
  rw [← Ico_union_Ico_eq_Ico (Nat.zero_le a) h, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (Ico_disjoint_Ico_consecutive 0 a b))]

/-- Chebyshev-type bound for a dyadic block `(m, 2m]`, via `centralBinom m ≤ 4 ^ m`. -/
lemma count_dyadic_le (m K : ℕ) (hK : 4 ^ m < (m + 1) ^ (K + 1)) :
    Nat.count Nat.Prime (2 * m + 1) ≤ Nat.count Nat.Prime (m + 1) + K := by
  have hsplit := count_eq_add_card Nat.Prime (a := m + 1) (b := m + m + 1) (by omega)
  have hprod : ∏ p ∈ Ico (m + 1) (m + m + 1) with p.Prime, p ≤ choose (m + m) m := by
    have h2 := primorial_add_le (le_refl m)
    rw [primorial_add m m] at h2
    exact Nat.le_of_mul_le_mul_left h2 (primorial_pos m)
  have hpow : (m + 1) ^ #{x ∈ Ico (m + 1) (m + m + 1) | x.Prime} ≤
      ∏ p ∈ Ico (m + 1) (m + m + 1) with p.Prime, p :=
    Finset.pow_card_le_prod _ _ _ (fun x hx => (mem_Ico.1 (mem_filter.1 hx).1).1)
  have hc : choose (m + m) m ≤ 4 ^ m := by
    rw [← two_mul, ← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.centralBinom_le_four_pow m
  have hm : 2 * m + 1 = m + m + 1 := by ring
  rw [hm, hsplit]
  by_contra hcon
  have h3 : (m + 1) ^ (K + 1) ≤ (m + 1) ^ #{x ∈ Ico (m + 1) (m + m + 1) | x.Prime} :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- `a ^ (number of primes in [a, b)) ≤ 4 ^ b`, from `primorial b ≤ 4 ^ b`. -/
lemma pow_card_primes_Ico_le (a b : ℕ) : a ^ #{x ∈ Ico a b | x.Prime} ≤ 4 ^ b := by
  calc a ^ #{x ∈ Ico a b | x.Prime}
      ≤ ∏ p ∈ Ico a b with p.Prime, p :=
        Finset.pow_card_le_prod _ _ _ (fun x hx => (mem_Ico.1 (mem_filter.1 hx).1).1)
    _ ≤ ∏ p ∈ range (b + 1) with p.Prime, p := by
        apply Finset.prod_le_prod_of_subset_of_one_le'
        · intro x hx
          simp only [mem_filter, mem_Ico, mem_range] at hx ⊢
          exact ⟨by omega, hx.2⟩
        · intro i hi _
          exact (mem_filter.1 hi).2.one_lt.le
    _ = primorial b := rfl
    _ ≤ 4 ^ b := primorial_le_four_pow b

/-- Induction step for `d ≥ 8`. -/
lemma count_step (e : ℕ) (ih : Nat.count Nat.Prime (10 ^ (e + 7)) < 10 ^ (e + 6)) :
    Nat.count Nat.Prime (10 ^ (e + 8)) < 10 ^ (e + 7) := by
  have hab : 10 ^ (e + 7) ≤ 10 ^ (e + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [count_eq_add_card Nat.Prime hab]
  have hpow := pow_card_primes_Ico_le (10 ^ (e + 7)) (10 ^ (e + 8))
  have e7 : 10 ^ (e + 7) = 10 * 10 ^ (e + 6) := by ring
  suffices hc : #{x ∈ Ico (10 ^ (e + 7)) (10 ^ (e + 8)) | x.Prime} < 9 * 10 ^ (e + 6) by
    omega
  by_contra hcon
  push Not at hcon
  have h1 : (10 ^ (e + 7)) ^ (9 * 10 ^ (e + 6)) ≤ 4 ^ (10 ^ (e + 8)) :=
    le_trans (Nat.pow_le_pow_right (by positivity) hcon) hpow
  have e1 : (10 ^ (e + 7)) ^ (9 * 10 ^ (e + 6)) = (10 ^ (9 * (e + 7))) ^ (10 ^ (e + 6)) := by
    rw [← pow_mul, ← pow_mul]; ring_nf
  have e2 : (4 : ℕ) ^ (10 ^ (e + 8)) = (4 ^ 100) ^ (10 ^ (e + 6)) := by
    rw [← pow_mul]; ring_nf
  rw [e1, e2] at h1
  have h2 : 10 ^ (9 * (e + 7)) ≤ 4 ^ 100 :=
    (Nat.pow_le_pow_iff_left (by positivity)).1 h1
  have h3 : (4 : ℕ) ^ 100 < 10 ^ 63 := by norm_num
  have h4 : (10 : ℕ) ^ 63 ≤ 10 ^ (9 * (e + 7)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## The primes below `10 ^ 4` -/

/-- The 1229 primes below `10 ^ 4`, in increasing order. -/
def primeTable : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
   197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
   311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
   431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
   557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
   661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
   809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
   937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039,
   1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153,
   1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279,
   1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
   1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499,
   1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613,
   1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741,
   1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873,
   1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999,
   2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113,
   2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251,
   2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371,
   2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477,
   2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647,
   2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731,
   2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857,
   2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001,
   3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163,
   3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299,
   3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407,
   3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539,
   3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659,
   3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793,
   3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919,
   3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051,
   4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201,
   4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327,
   4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463,
   4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603,
   4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733,
   4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903,
   4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009,
   5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153,
   5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303,
   5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441,
   5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569,
   5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701,
   5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843,
   5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987,
   6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131,
   6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269,
   6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373,
   6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553,
   6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691,
   6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829,
   6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967,
   6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109,
   7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247,
   7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451,
   7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559,
   7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687,
   7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841,
   7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993,
   8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147,
   8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287,
   8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431,
   8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599,
   8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719,
   8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849,
   8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007,
   9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157,
   9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293,
   9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431,
   9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551,
   9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721,
   9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851,
   9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]

/-- Kernel check: the table is exactly the list of `n < 10 ^ 4` passing `isPrimeB`. -/
theorem primeTable_eq_filter : primeTable = (List.range 10000).filter isPrimeB := by
  decide +kernel

theorem primeTable_length : primeTable.length = 1229 := by decide +kernel

theorem primeTable_eq_filter_prime :
    primeTable = (List.range 10000).filter (fun n => decide n.Prime) := by
  rw [primeTable_eq_filter]
  apply List.filter_congr
  intro n hn
  have hn' : n < 65536 := by simp at hn; omega
  rw [Bool.eq_iff_iff, isPrimeB_iff hn', decide_eq_true_iff]

theorem count_prime_10000 : Nat.count Nat.Prime 10000 = 1229 := by
  rw [← length_filter_range, ← primeTable_eq_filter_prime, primeTable_length]

theorem nth_prime_eq_table {i : ℕ} (hi : i < 1229) :
    Nat.nth Nat.Prime i = primeTable.getD i 0 := by
  rw [primeTable_eq_filter_prime]
  exact nth_eq_getD_filter_range Nat.Prime 10000 i (by rw [count_prime_10000]; exact hi)

/-! ## Packed table for fast kernel lookups -/

/-- Base-`2 ^ 14` packing of a list. -/
def enc : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 16384 * enc xs

/-- The `i`-th base-`2 ^ 14` digit. -/
def dec (E i : ℕ) : ℕ := E / 16384 ^ i % 16384

theorem dec_enc : ∀ L : List ℕ, (∀ x ∈ L, x < 16384) → ∀ i, dec (enc L) i = L.getD i 0
  | [], _, i => by simp [enc, dec]
  | x :: xs, h, i => by
    have hx : x < 16384 := h x (by simp)
    cases i with
    | zero => simp [enc, dec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ i =>
      have ih := dec_enc xs (fun y hy => h y (by simp [hy])) i
      simp only [dec] at ih ⊢
      rw [pow_succ', ← Nat.div_div_eq_div_mul, enc,
        Nat.add_mul_div_left _ _ (by norm_num : 0 < 16384), Nat.div_eq_of_lt hx, zero_add, ih]
      simp

/-- The packed prime table. -/
def tableEnc : ℕ := enc primeTable

theorem primeTable_lt : ∀ x ∈ primeTable, x < 16384 := by decide +kernel

/-! ## The map on small arguments -/

/-- Kernel-friendly version of `k ↦ reverseDigits (nth Prime (k - 1))` for `1 ≤ k ≤ 1229`. -/
def G (k : ℕ) : ℕ := revB (dec tableEnc (k - 1))

theorem step_eq_G {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 1229) :
    reverseDigits (Nat.nth Nat.Prime (k - 1)) = G k := by
  have hp : Nat.nth Nat.Prime (k - 1) < 10000 :=
    (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).1 (by rw [count_prime_10000]; omega)
  rw [G, tableEnc, dec_enc _ primeTable_lt, ← nth_prime_eq_table (by omega), revB_eq (by omega)]

/-- `inBand d k`: `k` has exactly `d` decimal digits and `k ≤ 1229`. -/
def inBand (d k : ℕ) : Bool :=
  Nat.ble (Nat.pow 10 (d - 1)) k && Nat.blt k (Nat.pow 10 d) && Nat.ble k 1229

/-- `escapes d fuel k`: iterating `G` from `k` leaves the band `d` within `fuel` steps. -/
def escapes (d : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, k => !(inBand d k) || escapes d fuel (G k)

theorem escapes_spec (d : ℕ) :
    ∀ fuel k, escapes d fuel k = true → ∃ j, inBand d (G^[j] k) = false
  | 0, k, h => by simp [escapes] at h
  | fuel + 1, k, h => by
    simp only [escapes, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨j, hj⟩ := escapes_spec d fuel (G k) h
      exact ⟨j + 1, by rwa [Function.iterate_succ_apply]⟩

/-- `allEsc d lo n`: every `k ∈ [lo, lo + n)` escapes the band `d` within `1230` steps. -/
def allEsc (d lo : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => escapes d 1230 (lo + n) && allEsc d lo n

theorem allEsc_spec {d lo : ℕ} :
    ∀ n, allEsc d lo n = true → ∀ k, lo ≤ k → k < lo + n → escapes d 1230 k = true
  | 0, _, k, h1, h2 => by omega
  | n + 1, h, k, h1, h2 => by
    simp only [allEsc, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge k (lo + n) with hk | hk
    · exact allEsc_spec n h.2 k h1 hk
    · rw [show k = lo + n by omega]
      exact h.1

/-- Kernel check: every `k ≤ 1229` with `d ≤ 4` digits leaves its digit band under `G`. -/
theorem escape_check :
    (allEsc 1 1 9 && allEsc 2 10 90 && allEsc 3 100 900 && allEsc 4 1000 230) = true := by
  decide +kernel

theorem escapes_of_band {d k : ℕ} (hd1 : 1 ≤ d) (hd4 : d ≤ 4) (hk1 : 10 ^ (d - 1) ≤ k)
    (hk2 : k < 10 ^ d) (hk3 : k ≤ 1229) : escapes d 1230 k = true := by
  have h := escape_check
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  interval_cases d
  · exact allEsc_spec 9 h1 k (by simpa using hk1) (by simpa using hk2)
  · exact allEsc_spec 90 h2 k (by simpa using hk1) (by simpa using hk2)
  · exact allEsc_spec 900 h3 k (by simpa using hk1) (by simpa using hk2)
  · exact allEsc_spec 230 h4 k (by simpa using hk1) (by omega)

theorem inBand_of {d k : ℕ} (hk1 : 10 ^ (d - 1) ≤ k) (hk2 : k < 10 ^ d) (hk3 : k ≤ 1229) :
    inBand d k = true := by
  simp [inBand, hk1, hk2, hk3]

/-! ## Prime counts at `10 ^ 5`, `10 ^ 6` and `10 ^ 7` -/

/-- Kernel computation: primes in `[10000, 91920)`. -/
theorem cnt_A : cntChunks 316 ! 14 5 10000 = 7649 := by decide +kernel

/-- Kernel computation: primes in `[91920, 100112)`. -/
theorem cnt_B : cntCop 316 ! 13 91920 = 722 := by decide +kernel

/-- Kernel computation: primes in `[100112, 509712)`. -/
theorem cnt_C : cntChunks 720 ! 14 25 100112 = 32669 := by decide +kernel

theorem count_prime_100112 : Nat.count Nat.Prime 100112 = 9600 := by
  have h1 := count_prime_add_cntChunks (B := 316) (k := 14) 5 10000 (by norm_num) (by norm_num)
  have h2 := count_prime_add_cntCop (B := 316) (a := 91920) (k := 13) (by norm_num) (by norm_num)
  have e1 : (10000 : ℕ) + 5 * 2 ^ 14 = 91920 := by norm_num
  have e2 : (91920 : ℕ) + 2 ^ 13 = 100112 := by norm_num
  rw [e1, count_prime_10000, cnt_A] at h1
  rw [e2, h1, cnt_B] at h2
  exact h2

theorem count_prime_509712 : Nat.count Nat.Prime 509712 = 42269 := by
  have h := count_prime_add_cntChunks (B := 720) (k := 14) 25 100112 (by norm_num) (by norm_num)
  have e : (100112 : ℕ) + 25 * 2 ^ 14 = 509712 := by norm_num
  rw [e, count_prime_100112, cnt_C] at h
  exact h

theorem count_prime_1000001_le : Nat.count Nat.Prime 1000001 ≤ 95090 := by
  have h1 := count_dyadic_le 500000 52821 (by decide +kernel)
  have h2 := Nat.count_monotone Nat.Prime (show 500000 + 1 ≤ 509712 by norm_num)
  rw [count_prime_509712] at h2
  have e : 2 * 500000 + 1 = 1000001 := by norm_num
  rw [e] at h1
  omega

theorem count_prime_10000001_le : Nat.count Nat.Prime 10000001 ≤ 968070 := by
  have h0 := Nat.count_monotone Nat.Prime (show 625000 + 1 ≤ 1000001 by norm_num)
  have h1 := count_dyadic_le 625000 64923 (by decide +kernel)
  have h2 := count_dyadic_le 1250000 123435 (by decide +kernel)
  have h3 := count_dyadic_le 2500000 235255 (by decide +kernel)
  have h4 := count_dyadic_le 5000000 449367 (by decide +kernel)
  have h5 := count_prime_1000001_le
  have e1 : 2 * 625000 + 1 = 1250000 + 1 := by norm_num
  have e2 : 2 * 1250000 + 1 = 2500000 + 1 := by norm_num
  have e3 : 2 * 2500000 + 1 = 5000000 + 1 := by norm_num
  have e4 : 2 * 5000000 + 1 = 10000001 := by norm_num
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  omega

theorem count_pow_ten_five : Nat.count Nat.Prime (10 ^ 5) < 10 ^ 4 := by
  have h := Nat.count_monotone Nat.Prime (show 10 ^ 5 ≤ 100112 by norm_num)
  rw [count_prime_100112] at h
  have e : (10 : ℕ) ^ 4 = 10000 := by norm_num
  omega

theorem count_pow_ten_six : Nat.count Nat.Prime (10 ^ 6) < 10 ^ 5 := by
  have h := Nat.count_monotone Nat.Prime (show 10 ^ 6 ≤ 1000001 by norm_num)
  have h' := count_prime_1000001_le
  have e : (10 : ℕ) ^ 5 = 100000 := by norm_num
  omega

theorem count_pow_ten_seven : Nat.count Nat.Prime (10 ^ 7) < 10 ^ 6 := by
  have h := Nat.count_monotone Nat.Prime (show 10 ^ 7 ≤ 10000001 by norm_num)
  have h' := count_prime_10000001_le
  have e : (10 : ℕ) ^ 6 = 1000000 := by norm_num
  omega

theorem count_pow_ten : ∀ e : ℕ, Nat.count Nat.Prime (10 ^ (e + 5)) < 10 ^ (e + 4)
  | 0 => count_pow_ten_five
  | 1 => count_pow_ten_six
  | 2 => count_pow_ten_seven
  | e + 3 => by
    have h := count_step e (count_pow_ten (e + 2))
    rwa [show e + 3 + 5 = e + 8 by omega, show e + 3 + 4 = e + 7 by omega]

/-- `π(10 ^ d) < 10 ^ (d - 1)` for every `d ≥ 5`. -/
theorem count_prime_pow_ten_lt (d : ℕ) (hd : 5 ≤ d) :
    Nat.count Nat.Prime (10 ^ d) < 10 ^ (d - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 5 := ⟨d - 5, by omega⟩
  rw [show e + 5 - 1 = e + 4 by omega]
  exact count_pow_ten e

/-! ## The refutation -/

theorem aStartAt_succ (x n : ℕ) :
    aStartAt x (n + 1) =
      if aStartAt x n = 0 then 0 else reverseDigits (Nat.nth Nat.Prime (aStartAt x n - 1)) :=
  rfl

/-- No orbit with a positive start is ultimately periodic. -/
theorem not_isUltimatelyPeriodic {x : ℕ} (hx : 0 < x) :
    ¬ IsUltimatelyPeriodic (aStartAt x) := by
  rintro ⟨N, P, hP, hper⟩
  have hne : ∀ n, aStartAt x n ≠ 0 := by
    intro n
    induction n with
    | zero => exact hx.ne'
    | succ n ih =>
      rw [aStartAt_succ, if_neg ih]
      intro h0
      have hp := Nat.prime_nth_prime (aStartAt x n - 1)
      have hlen := length_digits_reverseDigits (prime_mod_ten_ne_zero hp)
      rw [h0, Nat.digits_zero, List.length_nil, eq_comm, List.length_eq_zero_iff,
        Nat.digits_eq_nil_iff_eq_zero] at hlen
      exact hp.ne_zero hlen
  have hsucc : ∀ n, aStartAt x (n + 1) = reverseDigits (Nat.nth Nat.Prime (aStartAt x n - 1)) :=
    fun n => by rw [aStartAt_succ, if_neg (hne n)]
  have hstep : ∀ n, (Nat.digits 10 (aStartAt x (n + 1))).length =
      (Nat.digits 10 (Nat.nth Nat.Prime (aStartAt x n - 1))).length := fun n => by
    rw [hsucc, length_digits_reverseDigits (prime_mod_ten_ne_zero (Nat.prime_nth_prime _))]
  have hge : ∀ n, aStartAt x n ≤ Nat.nth Nat.Prime (aStartAt x n - 1) := fun n => by
    have := Nat.add_two_le_nth_prime (aStartAt x n - 1)
    omega
  have hmono : Monotone fun n => (Nat.digits 10 (aStartAt x n)).length :=
    monotone_nat_of_le_succ fun n => by
      rw [hstep]
      exact Nat.le_length_digits_le 10 _ _ (hge n)
  have hperj : ∀ j, aStartAt x (N + j * P) = aStartAt x N := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show N + (j + 1) * P = (N + j * P) + P by ring, hper _ (by omega), ih]
  have hconst : ∀ n, N ≤ n →
      (Nat.digits 10 (aStartAt x n)).length = (Nat.digits 10 (aStartAt x N)).length := by
    intro n hn
    apply le_antisymm
    · have h1 : n ≤ N + n * P := by nlinarith
      have h2 := hmono h1
      simp only [hperj n] at h2
      exact h2
    · exact hmono hn
  set d := (Nat.digits 10 (aStartAt x N)).length with hd
  have hd1 : 1 ≤ d :=
    (Nat.lt_digits_length_iff (by norm_num) _).2 (by have := hne N; simp; omega)
  have hlow : ∀ n, N ≤ n → 10 ^ (d - 1) ≤ aStartAt x n := fun n hn =>
    (Nat.lt_digits_length_iff (by norm_num) _).1 (by rw [hconst n hn]; omega)
  have hhigh : ∀ n, N ≤ n → aStartAt x n < 10 ^ d := fun n hn =>
    (Nat.digits_length_le_iff (by norm_num) _).1 (by rw [hconst n hn])
  have hpl : ∀ n, N ≤ n → Nat.nth Nat.Prime (aStartAt x n - 1) < 10 ^ d := fun n hn =>
    (Nat.digits_length_le_iff (by norm_num) _).1 (by rw [← hstep, hconst (n + 1) (by omega)])
  rcases le_or_gt 5 d with hd5 | hd4
  · -- `d ≥ 5`: too few primes below `10 ^ d`
    have hc := count_prime_pow_ten_lt d hd5
    have h1 : Nat.count Nat.Prime (10 ^ d) ≤ aStartAt x N - 1 :=
      Nat.le_sub_one_of_lt (lt_of_lt_of_le hc (hlow N le_rfl))
    have h2 := (Nat.count_le_iff_le_nth Nat.infinite_setOf_prime).1 h1
    exact absurd (hpl N le_rfl) (not_lt.2 h2)
  · -- `d ≤ 4`: the orbit would stay in a finite band where the kernel check applies
    have hsmall : ∀ n, N ≤ n → aStartAt x n ≤ 1229 := by
      intro n hn
      have h1 : Nat.nth Nat.Prime (aStartAt x n - 1) < 10000 :=
        lt_of_lt_of_le (hpl n hn)
          (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : d ≤ 4)) (by norm_num))
      have h2 := (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).2 h1
      rw [count_prime_10000] at h2
      have := hne n
      omega
    have hG : ∀ n, N ≤ n → aStartAt x (n + 1) = G (aStartAt x n) := fun n hn => by
      rw [hsucc, step_eq_G (by have := hne n; omega) (hsmall n hn)]
    have hiter : ∀ j, aStartAt x (N + j) = G^[j] (aStartAt x N) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [← add_assoc, hG _ (by omega), ih, Function.iterate_succ_apply']
    have hesc := escapes_of_band hd1 (by omega) (hlow N le_rfl) (hhigh N le_rfl) (hsmall N le_rfl)
    obtain ⟨j, hj⟩ := escapes_spec d 1230 _ hesc
    rw [← hiter j, inBand_of (hlow _ (by omega)) (hhigh _ (by omega)) (hsmall _ (by omega))] at hj
    exact Bool.noConfusion hj

/-- The upstream `OeisA100475.conjecture` is false. -/
theorem not_statement : ¬ statement := by
  rintro ⟨x, hx, -, hper⟩
  exact not_isUltimatelyPeriodic hx hper
end AgenticConjectures.OeisA100475
