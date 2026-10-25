import Mathlib

/-!
# OEIS A135508 — McEachen's conjecture `a(p-1) = p`: reduction and partial results

OEIS A135508 is `a(n) = x(n+1)/x(n) - 2` with `x(1) = 1` and
`x(n) = 2 x(n-1) + lcm(x(n-1), n)`. Bill McEachen conjectured (Sep 26 2025) that
`a(p-1) = p` for every prime `p` such that `p - 2` is not prime. The upstream
Formal Conjectures file `FormalConjectures/OEIS/135508.lean` states this as
`OeisA135508.conjecture`; it is open there (`sorry`).

The definitions `x` and `a` below are copied term for term from the upstream
snapshot `problems/oeis-a135508/upstream/135508.lean`; `statement` is the upstream
`conjecture` with its binders turned into a `Prop`. The upstream test values
`a_0`–`a_4` are reproduced with the same `rfl` proofs.

## What is proved here

* Structure: for `n ≥ 1`, `a n = (n + 1) / gcd (x n) (n + 1)` (`a_eq`),
  `x (n + 1) = x n * (a n + 2)` (`x_succ_eq`), and `x m ∣ x n` for `1 ≤ m ≤ n`
  (`x_dvd_x`).
* The exact criterion (`a_pred_eq_iff`): for every prime `p ≥ 5`,
  `a (p - 1) = p ↔ ¬ Nat.Coprime (x (p - 3)) (p - 2)`.
* Residue classes: the conjecture holds for every prime `p ≥ 7` with
  `p % 3 = 2` or `p % 5 = 2`, because `x 4 = 60`
  (`a_pred_eq_of_mod_three_or_five`; this needs no hypothesis on `p - 2`).
* A kernel-checked certificate (`prime_dvd_x_sq_sub_one`): every prime `r < 1009`
  divides `x (r ^ 2 - 1)`. Consequently the conjecture holds at every prime `p` for
  which `p - 2` is composite with least prime factor below `1009`
  (`a_pred_eq_of_minFac_lt`), in particular for every prime `p ≡ 2 (mod r)`,
  `r < 1009` prime, with `p - 2` not prime (`a_pred_eq_of_mod_eq_two`), and for every
  prime `p < 1009 ^ 2 + 2 = 1018083` (`a_pred_eq_of_lt`).
* Conditional reductions: the full conjecture follows from
  `∀ r prime, r ∣ x (r ^ 2 - 1)` (`statement_of_forall_prime_dvd`), and hence from the
  OEIS comment "a(n) is 1 or a prime" (`statement_of_a_eq_one_or_prime`). Neither
  hypothesis is proved here; `statement` itself remains open. The second hypothesis
  would give, for every prime `r ≥ 5`, a prime `s < r ^ 2` with `r ∣ s + 2`
  (`exists_prime_of_a_eq_one_or_prime`), a bound on the least prime in an arithmetic
  progression that is not known unconditionally.

## Faithfulness notes

* `x` and `a` are the upstream definitions verbatim: `x 0 = 0`, `x 1 = 1`, and the
  third clause is the recurrence for `n + 1 ≥ 2`; `a 0 = 0` is the upstream boundary
  value, and `a n = x (n + 1) / x n - 2` uses natural division and truncated
  subtraction. `a_eq` shows that for `n ≥ 1` neither truncation is active: the
  division is exact and the quotient is at least `3`.
* `statement` is `∀ p, p.Prime → ¬ (p - 2).Prime → a (p - 1) = p`, the upstream
  `conjecture` verbatim. For `p = 2, 3` the truncated `p - 2` is `0, 1` (not prime),
  so these primes are included, as in the OEIS wording; `a 1 = 2` and `a 2 = 3`.
* The upstream attributes (`@[category ...]`, `@[AMS ...]`), the `module` /
  `public section` / `@[expose]` header, and the `FormalConjecturesUtil` import are
  dropped; they do not affect the statement.
* The certificate data (`smallCerts`, `largePrimes`) were produced by
  `problems/oeis-a135508/a135508_scan.cpp --certs`, but nothing is trusted: every
  divisibility is re-evaluated by the Lean kernel (`decide +kernel`, no
  `native_decide`).
-/

namespace AgenticConjectures.OeisA135508

/-- Upstream definition, verbatim: the auxiliary sequence with `x(1) = 1` and
`x(n) = 2 x(n-1) + lcm(x(n-1), n)`. -/
def x : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 => 2 * x n + Nat.lcm (x n) (n + 1)

/-- Upstream definition, verbatim: `a(n) = x(n+1)/x(n) - 2` for `n ≥ 1`, and `a(0) = 0`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else (x (n + 1) / x n) - 2

/-- The upstream `conjecture` (Bill McEachen, Sep 26 2025) as a proposition: for every
prime `p` such that `p - 2` is not prime, `a(p-1) = p`. -/
def statement : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p - 2).Prime → a (p - 1) = p

/-! ### Upstream test values -/

theorem a_0 : a 0 = 0 := by rfl

theorem a_1 : a 1 = 2 := by rfl

theorem a_2 : a 2 = 3 := by rfl

theorem a_3 : a 3 = 1 := by rfl

theorem a_4 : a 4 = 1 := by rfl

/-! ### Structure of `x` and `a` -/

theorem x_succ (n : ℕ) (hn : 1 ≤ n) : x (n + 1) = 2 * x n + Nat.lcm (x n) (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rfl

theorem x_pos : ∀ n, 1 ≤ n → 0 < x n
  | 0, h => absurd h (by norm_num)
  | 1, _ => by decide
  | n + 2, _ => by
    rw [x_succ (n + 1) (by omega)]
    have := x_pos (n + 1) (by omega)
    omega

theorem lcm_x_eq (n : ℕ) :
    Nat.lcm (x n) (n + 1) = x n * ((n + 1) / Nat.gcd (x n) (n + 1)) :=
  Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)

theorem x_succ_eq_mul_div (n : ℕ) (hn : 1 ≤ n) :
    x (n + 1) = x n * ((n + 1) / Nat.gcd (x n) (n + 1) + 2) := by
  rw [x_succ n hn, lcm_x_eq]
  ring

/-- For `n ≥ 1`, `a(n) = (n+1) / gcd(x(n), n+1)`. -/
theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = (n + 1) / Nat.gcd (x n) (n + 1) := by
  rw [a, if_neg (by omega), x_succ_eq_mul_div n hn, Nat.mul_div_cancel_left _ (x_pos n hn),
    Nat.add_sub_cancel]

/-- For `n ≥ 1`, `x(n+1) = x(n) * (a(n) + 2)`. -/
theorem x_succ_eq (n : ℕ) (hn : 1 ≤ n) : x (n + 1) = x n * (a n + 2) := by
  rw [a_eq n hn]
  exact x_succ_eq_mul_div n hn

theorem a_dvd (n : ℕ) (hn : 1 ≤ n) : a n ∣ n + 1 := by
  rw [a_eq n hn]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)

theorem a_le (n : ℕ) (hn : 1 ≤ n) : a n ≤ n + 1 :=
  Nat.le_of_dvd (by omega) (a_dvd n hn)

/-- Divisibility along the sequence: `x m ∣ x n` for `1 ≤ m ≤ n`. -/
theorem x_dvd_x {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : x m ∣ x n := by
  induction n, hmn using Nat.le_induction with
  | base => exact dvd_rfl
  | succ k hk ih =>
    rw [x_succ_eq k (by omega)]
    exact ih.mul_right _

/-- A prime `p` does not divide `x n` while `n + 2 < p`: every factor `a(m) + 2` with
`m < n` is at most `m + 3 < p`. -/
theorem not_dvd_x {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hnp : n + 2 < p) : ¬ p ∣ x n := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show x 1 = 1 from rfl, Nat.dvd_one]
    exact hp.one_lt.ne'
  | succ k hk ih =>
    rw [x_succ_eq k hk, hp.dvd_mul]
    rintro (h | h)
    · exact ih (by omega) h
    · have h1 := a_le k hk
      have h2 := Nat.le_of_dvd (by omega) h
      omega

/-! ### The exact criterion -/

/-- **Criterion.** For a prime `p ≥ 5`, `a(p-1) = p` holds exactly when `x(p-3)` and
`p - 2` have a common factor. -/
theorem a_pred_eq_iff {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    a (p - 1) = p ↔ ¬ Nat.Coprime (x (p - 3)) (p - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 3 := ⟨p - 3, by omega⟩
  rw [show n + 3 - 1 = n + 2 by omega, show n + 3 - 3 = n by omega,
    show n + 3 - 2 = n + 1 by omega]
  -- `a (n + 2) = n + 3` iff the prime `n + 3` does not divide `x (n + 2)`.
  have step1 : a (n + 2) = n + 3 ↔ ¬ (n + 3) ∣ x (n + 2) := by
    rw [a_eq (n + 2) (by omega)]
    constructor
    · intro h hdvd
      rw [Nat.gcd_eq_right hdvd, Nat.div_self (by omega)] at h
      omega
    · intro h
      rw [Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 ((hp.coprime_iff_not_dvd).2 h)),
        Nat.div_one]
  have hx : x (n + 2) = x n * (a n + 2) * (a (n + 1) + 2) := by
    rw [x_succ_eq (n + 1) (by omega), x_succ_eq n (by omega)]
  have h3 : ¬ (n + 3) ∣ x n := not_dvd_x hp (by omega) (by omega)
  -- `a (n + 1)` divides `n + 2`, so `a (n + 1) + 2 ∈ [3, n + 4]` and it is not `n + 3`.
  have h4 : ¬ (n + 3) ∣ a (n + 1) + 2 := by
    intro h
    have hle := Nat.le_of_dvd (by omega) h
    have hd := a_dvd (n + 1) (by omega)
    have hle2 := Nat.le_of_dvd (by omega) hd
    rcases (show a (n + 1) = n + 1 ∨ a (n + 1) = n + 2 by omega) with h' | h'
    · rw [h'] at hd
      have h1 : n + 1 ∣ 1 := (Nat.dvd_add_right (dvd_refl (n + 1))).1 hd
      have := Nat.le_of_dvd one_pos h1
      omega
    · rw [h'] at h
      have h1 : n + 3 ∣ 1 := (Nat.dvd_add_right (dvd_refl (n + 3))).1 h
      have := Nat.le_of_dvd one_pos h1
      omega
  -- `a n` divides `n + 1`, so `n + 3 ∣ a n + 2` iff `a n = n + 1` iff the gcd is `1`.
  have h5' : (n + 3) ∣ a n + 2 ↔ Nat.Coprime (x n) (n + 1) := by
    have hle := a_le n (by omega)
    have key : a n = n + 1 ↔ Nat.Coprime (x n) (n + 1) := by
      rw [a_eq n (by omega), Nat.div_eq_self]
      constructor
      · rintro (h | h)
        · omega
        · exact h
      · exact Or.inr
    rw [← key]
    constructor
    · intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    · intro h
      rw [h]
  rw [step1, hx, hp.dvd_mul, hp.dvd_mul, h5']
  tauto

/-- **Transfer.** A common factor `q ≠ 1` of `x N` and `p - 2`, with `N ≤ p - 3`, forces
`a(p-1) = p`. -/
theorem a_pred_eq_of_dvd {p N q : ℕ} (hp : p.Prime) (hN : 1 ≤ N) (hNp : N + 3 ≤ p)
    (hq : q ≠ 1) (hqx : q ∣ x N) (hqp : q ∣ p - 2) : a (p - 1) = p := by
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  rw [a_pred_eq_iff hp (by omega)]
  intro hcop
  exact hq (Nat.eq_one_of_dvd_coprimes hcop (hqx.trans (x_dvd_x hN (by omega))) hqp)

/-! ### Residue classes modulo 3 and 5 -/

theorem x_four : x 4 = 60 := by decide

/-- The conjecture holds for every prime `p ≥ 7` with `p ≡ 2 (mod 3)` or `p ≡ 2 (mod 5)`
(no hypothesis on `p - 2` is needed), since `3 ∣ x 4` and `5 ∣ x 4`. -/
theorem a_pred_eq_of_mod_three_or_five {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (h : p % 3 = 2 ∨ p % 5 = 2) : a (p - 1) = p := by
  rcases h with h | h
  · exact a_pred_eq_of_dvd (N := 4) (q := 3) hp le_add_self (by omega) (by norm_num)
      (by rw [x_four]; norm_num) (Nat.dvd_of_mod_eq_zero (by omega))
  · exact a_pred_eq_of_dvd (N := 4) (q := 5) hp le_add_self (by omega) (by norm_num)
      (by rw [x_four]; norm_num) (Nat.dvd_of_mod_eq_zero (by omega))

/-! ### Kernel-checked certificate: every prime `r < 1009` divides `x (r ^ 2 - 1)` -/

/-- Pairs `(r, c)` for the 46 primes `r < 207`: `c` is the first index with `r ∣ x c`
(as computed by `a135508_scan.cpp --certs`). Only `r ∣ x c` and `1 ≤ c ≤ r ^ 2 - 1` are
used, and both are checked by the kernel in `smallCerts_ok`. -/
def smallCerts : List (ℕ × ℕ) :=
  [(2, 2), (3, 4), (5, 3), (7, 47), (11, 53), (13, 11), (17, 83), (19, 17), (23, 67), (29, 317),
    (31, 29), (37, 257), (41, 367), (43, 41), (47, 233), (53, 157), (59, 293), (61, 59), (67, 467),
    (71, 211), (73, 71), (79, 709), (83, 911), (89, 443), (97, 677), (101, 503), (103, 101),
    (107, 2459), (109, 107), (113, 337), (127, 379), (131, 653), (137, 409), (139, 137),
    (149, 743), (151, 149), (157, 1097), (163, 487), (167, 499), (173, 863), (179, 2683),
    (181, 179), (191, 953), (193, 191), (197, 983), (199, 197)]

/-- The 122 primes `211 ≤ r ≤ 997`. Their product divides `x 42611`, and
`42611 ≤ r ^ 2 - 1` for every `r ≥ 211`. (Primality of the entries is not used: the
coverage lemma `large_cover` below is what the proof relies on.) -/
def largePrimes : List ℕ :=
  [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313,
    317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
    439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563,
    569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673,
    677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811,
    821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
    947, 953, 967, 971, 977, 983, 991, 997]

theorem smallCerts_ok :
    ∀ rc ∈ smallCerts, 1 ≤ rc.2 ∧ rc.2 ≤ rc.1 ^ 2 - 1 ∧ rc.1 ∣ x rc.2 := by
  decide +kernel

theorem largePrimes_prod_dvd : largePrimes.prod ∣ x 42611 := by
  decide +kernel

/-- Every prime below `211` is the first component of an entry of `smallCerts`. -/
theorem prime_lt_211_mem : ∀ r < 211, r.Prime → r ∈ smallCerts.map Prod.fst := by
  decide +kernel

/-- Every `r` with `211 ≤ r < 1009` divides `largePrimes.prod` or has a divisor
`2 ≤ d < 32` (so it is not prime). -/
theorem large_cover :
    ∀ r < 1009, 211 ≤ r → largePrimes.prod % r = 0 ∨ ∃ d < 32, 2 ≤ d ∧ r % d = 0 := by
  decide +kernel

/-- **Certificate.** Every prime `r < 1009` divides `x (r ^ 2 - 1)`. -/
theorem prime_dvd_x_sq_sub_one {r : ℕ} (hr : r.Prime) (h : r < 1009) :
    r ∣ x (r ^ 2 - 1) := by
  rcases Nat.lt_or_ge r 211 with hs | hl
  · obtain ⟨⟨r', c⟩, hmem, rfl⟩ := List.mem_map.1 (prime_lt_211_mem r hs hr)
    obtain ⟨hc1, hc2, hdvd⟩ := smallCerts_ok _ hmem
    exact hdvd.trans (x_dvd_x hc1 hc2)
  · rcases large_cover r h hl with hP | ⟨d, hd32, hd2, hdr⟩
    · have hsq : 211 * 211 ≤ r ^ 2 := by nlinarith
      exact ((Nat.dvd_of_mod_eq_zero hP).trans largePrimes_prod_dvd).trans
        (x_dvd_x (by norm_num) (by omega))
    · rcases hr.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hdr) with h1 | h1 <;> omega

/-! ### Consequences -/

/-- The two primes below `5` that the conjecture covers. -/
theorem a_pred_eq_of_lt_five {p : ℕ} (hp : p.Prime) (h : p < 5) (hp2 : ¬ (p - 2).Prime) :
    a (p - 1) = p := by
  interval_cases p
  · norm_num at hp
  · norm_num at hp
  · exact a_1
  · exact a_2
  · norm_num at hp

/-- If `p - 2` is composite and its least prime factor `r` divides `x (r ^ 2 - 1)`, then
`a(p-1) = p`. (Since `r ^ 2 ≤ p - 2`, this is the transfer theorem with `N = r ^ 2 - 1`.) -/
theorem a_pred_eq_of_minFac_dvd {p : ℕ} (hp : p.Prime) (hp2 : ¬ (p - 2).Prime)
    (h : (p - 2).minFac ∣ x ((p - 2).minFac ^ 2 - 1)) : a (p - 1) = p := by
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · exact a_pred_eq_of_lt_five hp h5 hp2
  have hr := Nat.minFac_prime (show p - 2 ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (show 0 < p - 2 by omega) hp2
  have hr2 : 4 ≤ (p - 2).minFac ^ 2 := by nlinarith [hr.two_le]
  exact a_pred_eq_of_dvd hp (by omega) (by omega) hr.one_lt.ne' h (Nat.minFac_dvd _)

/-- **Main partial result.** The conjecture holds at every prime `p` such that `p - 2` is
not prime and has least prime factor below `1009`. -/
theorem a_pred_eq_of_minFac_lt {p : ℕ} (hp : p.Prime) (hp2 : ¬ (p - 2).Prime)
    (h : (p - 2).minFac < 1009) : a (p - 1) = p := by
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · exact a_pred_eq_of_lt_five hp h5 hp2
  exact a_pred_eq_of_minFac_dvd hp hp2
    (prime_dvd_x_sq_sub_one (Nat.minFac_prime (by omega)) h)

/-- **Residue classes.** For every prime `r < 1009`, the conjecture holds at every prime
`p ≡ 2 (mod r)` (with `p - 2` not prime, as in the conjecture). -/
theorem a_pred_eq_of_mod_eq_two {p r : ℕ} (hp : p.Prime) (hp2 : ¬ (p - 2).Prime)
    (hr : r.Prime) (hr1009 : r < 1009) (hpr : p % r = 2) : a (p - 1) = p := by
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · exact a_pred_eq_of_lt_five hp h5 hp2
  have hr2 : 2 < r := by
    have := Nat.mod_lt p hr.pos
    omega
  have hdvd : r ∣ p - 2 :=
    (Nat.modEq_iff_dvd' (by omega)).1 (show 2 % r = p % r by rw [hpr, Nat.mod_eq_of_lt hr2])
  exact a_pred_eq_of_minFac_lt hp hp2
    (lt_of_le_of_lt (Nat.minFac_le_of_dvd hr.two_le hdvd) hr1009)

/-- **Finite range.** The conjecture holds for every prime `p < 1009 ^ 2 + 2 = 1018083`. -/
theorem a_pred_eq_of_lt {p : ℕ} (hp : p.Prime) (hp2 : ¬ (p - 2).Prime)
    (h : p < 1009 ^ 2 + 2) : a (p - 1) = p := by
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · exact a_pred_eq_of_lt_five hp h5 hp2
  apply a_pred_eq_of_minFac_lt hp hp2
  have hsq := Nat.minFac_sq_le_self (show 0 < p - 2 by omega) hp2
  by_contra hc
  have : 1009 ^ 2 ≤ (p - 2).minFac ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

/-! ### Conditional reductions of the full conjecture -/

/-- The full conjecture follows from `r ∣ x (r ^ 2 - 1)` for every prime `r`. -/
theorem statement_of_forall_prime_dvd (h : ∀ r : ℕ, r.Prime → r ∣ x (r ^ 2 - 1)) :
    statement := by
  intro p hp hp2
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · exact a_pred_eq_of_lt_five hp h5 hp2
  exact a_pred_eq_of_minFac_dvd hp hp2 (h _ (Nat.minFac_prime (by omega)))

/-- If every `a(n)` (`n ≥ 1`) is `1` or a prime, as an OEIS comment asserts, then every
prime `r` divides `x (r ^ 2 - 1)`: otherwise `a (r ^ 2 - 1) = r ^ 2`. -/
theorem prime_dvd_x_of_a_eq_one_or_prime (h : ∀ n, 1 ≤ n → a n = 1 ∨ (a n).Prime)
    {r : ℕ} (hr : r.Prime) : r ∣ x (r ^ 2 - 1) := by
  by_contra hndvd
  have hr2 : 4 ≤ r ^ 2 := by nlinarith [hr.two_le]
  have hcop : Nat.Coprime (x (r ^ 2 - 1)) (r ^ 2) :=
    Nat.Coprime.pow_right 2 (Nat.coprime_comm.1 ((hr.coprime_iff_not_dvd).2 hndvd))
  have ha : a (r ^ 2 - 1) = r ^ 2 := by
    rw [a_eq _ (by omega), Nat.sub_add_cancel (by omega), hcop.gcd_eq_one, Nat.div_one]
  rcases h (r ^ 2 - 1) (by omega) with h1 | hpr
  · rw [ha] at h1
    omega
  · exact Nat.Prime.not_prime_pow le_rfl (ha ▸ hpr)

/-- The OEIS comment "a(n) is 1 or a prime" implies the conjecture. -/
theorem statement_of_a_eq_one_or_prime (h : ∀ n, 1 ≤ n → a n = 1 ∨ (a n).Prime) :
    statement :=
  statement_of_forall_prime_dvd fun _ hr => prime_dvd_x_of_a_eq_one_or_prime h hr

/-! ### What the reduction would require -/

/-- A prime dividing `x N` divides some factor `a m + 2` with `1 ≤ m < N`. -/
theorem exists_dvd_a_add_two {r N : ℕ} (hr : r.Prime) (hN : 1 ≤ N) (h : r ∣ x N) :
    ∃ m, 1 ≤ m ∧ m < N ∧ r ∣ a m + 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [show x 1 = 1 from rfl, Nat.dvd_one] at h
    exact absurd h hr.one_lt.ne'
  | succ k hk ih =>
    rw [x_succ_eq k hk, hr.dvd_mul] at h
    rcases h with h | h
    · obtain ⟨m, hm1, hmk, hdvd⟩ := ih h
      exact ⟨m, hm1, by omega, hdvd⟩
    · exact ⟨k, hk, by omega, h⟩

/-- The OEIS comment "a(n) is 1 or a prime" forces, for every prime `r ≥ 5`, a prime
`s ≡ -2 (mod r)` below `r ^ 2`. Bounds of this strength for the least prime in an
arithmetic progression are not known unconditionally, so this is a limitation of the
conditional route, not a step towards it. -/
theorem exists_prime_of_a_eq_one_or_prime (h : ∀ n, 1 ≤ n → a n = 1 ∨ (a n).Prime)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) : ∃ s, s.Prime ∧ r ∣ s + 2 ∧ s < r ^ 2 := by
  have hsq : 25 ≤ r ^ 2 := by nlinarith
  obtain ⟨m, hm1, hm, hdvd⟩ :=
    exists_dvd_a_add_two hr (by omega) (prime_dvd_x_of_a_eq_one_or_prime h hr)
  rcases h m hm1 with h1 | hs
  · rw [h1] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · refine ⟨a m, hs, hdvd, ?_⟩
    have := a_le m hm1
    omega

end AgenticConjectures.OeisA135508
