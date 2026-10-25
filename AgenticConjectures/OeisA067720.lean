import Mathlib

/-!
# OEIS A067720 — prime-power subfamilies

The pinned upstream snapshot
`problems/oeis-a067720/upstream/67720.lean` defines membership in A067720 by

`Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)`

and conjectures that every member other than `8` has `k + 1` prime. The
definition below copies that proposition exactly. We study `k + 1 = p ^ a`
with `p` prime and `a >= 2`:

* `power_two_add_one_not_solution`: no member has `k + 1 = 2 ^ a`.
* `odd_prime_power_solution_iff_of_two_adic_le_five`: for odd `p` and
  `V := v₂(p ^ a - 1) + v₂(p - 1) <= 5`, `k` is a member iff
  `(p, a, k) = (3, 2, 8)`. This is the odd-prime theorem of
  `problems/oeis-a067720/PROOF.md`.
* `odd_prime_power_solution_iff_of_two_adic_le_six`: the same for `V <= 6`.
* `odd_prime_power_solution_of_two_prime_factors`: for odd `p` and any `V`,
  a member with `k ^ 2 + 1` a product of two primes is `(3, 2, 8)`.

Proof outline for odd `p`, following PROOF.md: with `M = k ^ 2 + 1`, the
equation reads `φ M = k * p ^ (a - 1) * (p - 1)`. No prime factor of `M`
divides `φ M`, so `M` is squarefree, and every prime factor of `M` is
`1 mod 4`. Hence `v₂ (φ M) = V`, and each prime factor contributes at least
`2` to it. Instead of counting prime factors, we peel off least prime factors.
`M` is not prime. A third prime factor forces `2 ^ 6 ∣ φ M`, and a fourth
forces `2 ^ 8 ∣ φ M`. For `V = 6` with exactly three prime factors, each one
is `5 mod 8`, so `M ≡ 5 [MOD 8]`, but `V >= 6` forces `8 ∣ k`, so
`M ≡ 1 [MOD 8]`; this extra step is not in PROOF.md. With exactly two prime
factors `q ≤ r`, their sum and product are fixed, and PROOF.md's quadratic
inequalities trap `q` strictly between consecutive integers unless
`(p, a) = (3, 2)`.

Faithfulness: the statements use natural-number exponentiation exactly as the
upstream statement does. `V` is written with `padicValNat 2`; since `p >= 3`,
the natural subtractions `p ^ a - 1` and `p - 1` are not truncated. The
`2 <= a` hypotheses exclude the prime boundary case `a = 1`. No claim is made
about odd prime powers with `V >= 7` (outside the two-prime-factor case),
general composite values of `k + 1`, or the upstream universal conjecture.
-/

namespace AgenticConjectures.OeisA067720

/-- A number `k` belongs to OEIS A067720. This is the exact proposition used
by the pinned FormalConjectures statement. -/
def A (k : ℕ) : Prop :=
  Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)

/-- No A067720 member has `k + 1 = 2 ^ a` for an exponent `a >= 2`. -/
theorem power_two_add_one_not_solution {k a : ℕ} (ha : 2 ≤ a)
    (hk : k + 1 = 2 ^ a) : ¬ A k := by
  intro hA
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le ha
  let c : ℕ := 2 ^ b
  have hcpos : 0 < c := by simp [c]
  have hk4 : k + 1 = 4 * c := by rw [hk, hb]; simp [c, pow_add]
  let t : ℕ := 2 * c - 1
  have htpos : 0 < t := by dsimp [t]; omega
  have hkt : k = 2 * t + 1 := by dsimp [t]; omega
  let N : ℕ := 2 * t ^ 2 + 2 * t + 1
  have hfac : k ^ 2 + 1 = 2 * N := by rw [hkt]; dsimp [N]; ring
  have hNodd : Odd N := by
    refine ⟨t ^ 2 + t, ?_⟩
    dsimp [N]
    ring
  have ha0 : 0 < a := by omega
  have htotpow : Nat.totient (2 ^ a) = 2 ^ (a - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two ha0]
    simp
  have hpowsucc : 2 ^ a = 2 * 2 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    ring
  have ht_pow : t + 1 = 2 ^ (a - 1) := by
    rw [hkt, hpowsucc] at hk
    omega
  unfold A at hA
  rw [hfac, Nat.totient_two_mul_of_odd hNodd, hk, htotpow] at hA
  have hle : Nat.totient N ≤ N := Nat.totient_le N
  have hstrict : N < k * 2 ^ (a - 1) := by
    rw [hkt, ← ht_pow]
    dsimp [N]
    nlinarith
  have hcontra := lt_of_le_of_lt hle hstrict
  exact hcontra.ne hA

/-! ### Odd prime powers -/

/-- `8` belongs to A067720: `φ 65 = 48 = 8 * φ 9`. -/
theorem a_eight : A 8 := by
  unfold A
  decide

/-- If integers `q ≤ r` have sum `s` and product `n`, the smaller root `q` cannot
lie strictly between `x` and `x + 1`. This holds when `2 * x ≤ s`,
`x * (s - x) < n` and `n < (x + 1) * (s - (x + 1))`. -/
private theorem no_root_between {q r x s n : ℤ} (hsum : q + r = s) (hprod : q * r = n)
    (hqr : q ≤ r) (hx : 2 * x ≤ s) (hlo : x * (s - x) < n)
    (hhi : n < (x + 1) * (s - (x + 1))) : False := by
  subst hsum hprod
  rcases le_or_gt q x with h | h
  · have hr : x ≤ r := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hr)]
  · have h1 : x + 1 ≤ q := h
    have hr : x + 1 ≤ r := le_trans h1 hqr
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hr)]

/-- PROOF.md, case `a ≥ 3` (`Z = p ^ (a - 1) ≥ p ^ 2`): `f(p) < k ^ 2 + 1 < f(p + 1)`
for `f(x) = x (S - x)`, so no prime pair has the required sum and product. -/
private theorem core_big {P Z K Q R : ℤ} (hP : 3 ≤ P) (hZ : P ^ 2 ≤ Z) (hpz : P * Z = K + 1)
    (hsum : Q + R = K * (Z - 1) + 2) (hprod : Q * R = K ^ 2 + 1) (hQR : Q ≤ R) : False := by
  have hK : K = P * Z - 1 := by linarith
  subst hK
  have hZ9 : 9 ≤ Z := by nlinarith
  have hPZ : P * P ^ 2 ≤ P * Z := mul_le_mul_of_nonneg_left hZ (by linarith)
  have hc : 1 ≤ P * Z - P ^ 2 - 1 := by nlinarith
  refine no_root_between (x := P) hsum hprod hQR ?_ ?_ ?_
  · nlinarith
  · nlinarith [mul_pos (by linarith : (0 : ℤ) < P - 1) (by nlinarith : (0 : ℤ) < P * Z + P - 2)]
  · nlinarith [mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℤ) ≤ Z)]

/-- PROOF.md, case `a = 2` with `p > 3`: `f(p + 1) < k ^ 2 + 1 < f(p + 2)`. -/
private theorem core_square {P K Q R : ℤ} (hP : 5 ≤ P) (hpz : P * P = K + 1)
    (hsum : Q + R = K * (P - 1) + 2) (hprod : Q * R = K ^ 2 + 1) (hQR : Q ≤ R) : False := by
  have hK : K = P * P - 1 := by linarith
  subst hK
  refine no_root_between (x := P + 1) hsum hprod hQR ?_ ?_ ?_
  · nlinarith
  · nlinarith
  · nlinarith [mul_pos (mul_pos (by linarith : (0 : ℤ) < P) (by linarith : (0 : ℤ) < P - 3))
      (by linarith : (0 : ℤ) < P + 1)]

/-- For `k + 1 = p ^ a`, the defining equation reads
`φ (k ^ 2 + 1) = k * (p ^ (a - 1) * (p - 1))`. -/
private theorem totient_sq_add_one {p a k : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hk : k + 1 = p ^ a) (hA : A k) :
    Nat.totient (k ^ 2 + 1) = k * (p ^ (a - 1) * (p - 1)) := by
  rw [hA, hk, Nat.totient_prime_pow hp (by omega)]

private theorem sub_one_dvd {p a k : ℕ} (hk : k + 1 = p ^ a) : p - 1 ∣ k := by
  have h := Nat.sub_dvd_pow_sub_pow p 1 a
  rwa [one_pow, show p ^ a - 1 = k by omega] at h

/-- `k ^ 2 + 1 ≡ 2 [MOD p]`, so an odd prime `p` does not divide it. -/
private theorem prime_not_dvd_sq_add_one {p a k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (hk : k + 1 = p ^ a) : ¬ p ∣ k ^ 2 + 1 := by
  intro h
  have hk1 : p ∣ k + 1 := by rw [hk]; exact dvd_pow_self p (by omega)
  have hk0 : 1 ≤ k := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have hid : k ^ 2 + 1 = (k + 1) * (k - 1) + 2 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [hid] at h
  have h2 : p ∣ 2 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hk1 _)).mp h
  have := Nat.le_of_dvd two_pos h2
  have := hp.two_le
  omega

/-- A prime factor of `k ^ 2 + 1` divides none of `k`, `p`, `p - 1`, hence not
`φ (k ^ 2 + 1)` (PROOF.md, equation (2)). -/
private theorem prime_dvd_not_dvd_totient {p a k t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 1 ≤ a) (hk : k + 1 = p ^ a) (hA : A k) (ht : t.Prime) (htM : t ∣ k ^ 2 + 1) :
    ¬ t ∣ Nat.totient (k ^ 2 + 1) := by
  have htk : ¬ t ∣ k := by
    intro h
    have h1 : t ∣ 1 := (Nat.dvd_add_right (dvd_pow h two_ne_zero)).mp htM
    exact ht.one_lt.ne' (Nat.dvd_one.mp h1)
  have htp : ¬ t ∣ p := by
    intro h
    rw [(Nat.prime_dvd_prime_iff_eq ht hp).mp h] at htM
    exact prime_not_dvd_sq_add_one hp hp2 ha hk htM
  rw [totient_sq_add_one hp ha hk hA]
  intro h
  rcases (Nat.Prime.dvd_mul ht).mp h with h | h
  · exact htk h
  rcases (Nat.Prime.dvd_mul ht).mp h with h | h
  · exact htp (ht.dvd_of_dvd_pow h)
  · exact htk (h.trans (sub_one_dvd hk))

/-- `k ^ 2 + 1` is squarefree: `t * t ∣ M` would give `t ∣ φ (t * t) ∣ φ M`. -/
private theorem prime_mul_self_not_dvd {p a k t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 1 ≤ a) (hk : k + 1 = p ^ a) (hA : A k) (ht : t.Prime) (htM : t ∣ k ^ 2 + 1) :
    ¬ t * t ∣ k ^ 2 + 1 := by
  intro h
  have h1 : Nat.totient (t * t) ∣ Nat.totient (k ^ 2 + 1) := Nat.totient_dvd_of_dvd h
  rw [← sq, Nat.totient_prime_pow ht two_pos] at h1
  exact prime_dvd_not_dvd_totient hp hp2 ha hk hA ht htM
    ((dvd_mul_of_dvd_left (dvd_pow_self t (by norm_num)) _).trans h1)

/-- For even `k`, every prime factor of `k ^ 2 + 1` is `1 mod 4` (PROOF.md, (3)). -/
private theorem prime_dvd_mod_four {k t : ℕ} (hk : Even k) (ht : t.Prime)
    (htM : t ∣ k ^ 2 + 1) : t % 4 = 1 := by
  have ht2 : t ≠ 2 := by
    rintro rfl
    obtain ⟨c, rfl⟩ := hk
    have : (c + c) ^ 2 + 1 = 2 * (2 * c ^ 2) + 1 := by ring
    rw [this] at htM
    omega
  haveI := Fact.mk ht
  have hsq : (k : ZMod t) ^ 2 = -1 := by
    have h0 : ((k ^ 2 + 1 : ℕ) : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr htM
    push_cast at h0
    linear_combination h0
  have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq
  have h1 := Nat.odd_iff.mp (ht.odd_of_ne_two ht2)
  omega

/-- A divisor `d ≠ 1` of `k ^ 2 + 1` (`k` even) has `4 ∣ φ d`. -/
private theorem four_dvd_totient_of_dvd {k d : ℕ} (hk : Even k) (hd : d ∣ k ^ 2 + 1)
    (hd1 : d ≠ 1) : 4 ∣ Nat.totient d := by
  have ht := Nat.minFac_prime hd1
  have h4 := prime_dvd_mod_four hk ht ((Nat.minFac_dvd d).trans hd)
  have h1 : Nat.totient d.minFac ∣ Nat.totient d := Nat.totient_dvd_of_dvd (Nat.minFac_dvd d)
  rw [Nat.totient_prime ht] at h1
  exact (Nat.dvd_of_mod_eq_zero (by omega)).trans h1

/-- Peel the least prime factor `q` off a divisor `d ≠ 1` of a squarefree `M`:
`d = q * e` with `φ d = (q - 1) * φ e`. -/
private theorem peel {M d : ℕ} (hsq : ∀ t : ℕ, t.Prime → t ∣ M → ¬ t * t ∣ M) (hd : d ∣ M)
    (hd1 : d ≠ 1) :
    ∃ q e, q.Prime ∧ d = q * e ∧ e ∣ M ∧ Nat.totient d = (q - 1) * Nat.totient e := by
  have hq : d.minFac.Prime := Nat.minFac_prime hd1
  obtain ⟨e, hde⟩ := Nat.minFac_dvd d
  generalize d.minFac = q at hq hde
  subst hde
  have hcop : Nat.Coprime q e := by
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro h
    exact hsq q hq ((dvd_mul_right q e).trans hd) ((Nat.mul_dvd_mul_left q h).trans hd)
  refine ⟨q, e, hq, rfl, (dvd_mul_left e q).trans hd, ?_⟩
  rw [Nat.totient_mul hcop, Nat.totient_prime hq]

/-- `k ^ 2 + 1` is not prime: otherwise `k = p ^ (a - 1) * (p - 1)`, forcing
`p ^ (a - 1) = 1`. -/
private theorem sq_add_one_not_prime {p a k : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hk : k + 1 = p ^ a) (hA : A k) : ¬ (k ^ 2 + 1).Prime := by
  intro hM
  have htot := totient_sq_add_one hp (by omega) hk hA
  rw [Nat.totient_prime hM, Nat.add_sub_cancel, sq] at htot
  have hk0 : 0 < k := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have h1 : k = p ^ (a - 1) * (p - 1) := Nat.eq_of_mul_eq_mul_left hk0 htot
  have hpz : p ^ a = p ^ (a - 1) * p := by rw [← pow_succ]; congr 1; omega
  have hz : p ≤ p ^ (a - 1) := Nat.le_self_pow (by omega) p
  generalize p ^ (a - 1) = z at h1 hpz hz
  rw [hpz, h1] at hk
  have h2 : z * (p - 1) + z = z * p := by
    rw [← Nat.mul_succ]
    congr 1
    have := hp.one_lt
    omega
  have := hp.two_le
  omega

/-- Two prime factors (any `V`): if `k + 1 = p ^ a` with `p` an odd prime and
`a ≥ 2`, `k` is a member, and `k ^ 2 + 1 = q * r` with `q`, `r` prime, then
`(p, a, k) = (3, 2, 8)`. This is the endgame of PROOF.md: `q + r` and `q * r`
are determined by `p` and `a`, and the smaller root is trapped strictly between
consecutive integers unless `(p, a) = (3, 2)`. -/
theorem odd_prime_power_solution_of_two_prime_factors {p a k q r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hk : k + 1 = p ^ a) (hA : A k) (hq : q.Prime)
    (hr : r.Prime) (hM : k ^ 2 + 1 = q * r) : p = 3 ∧ a = 2 ∧ k = 8 := by
  have ha1 : 1 ≤ a := by omega
  have hqr : q ≠ r := by
    rintro rfl
    exact prime_mul_self_not_dvd hp hp2 ha1 hk hA hq (hM ▸ dvd_mul_right q q) (hM ▸ dvd_refl _)
  have hphi := totient_sq_add_one hp ha1 hk hA
  rw [hM, Nat.totient_mul ((Nat.coprime_primes hq hr).mpr hqr), Nat.totient_prime hq,
    Nat.totient_prime hr] at hphi
  have hpz : p * p ^ (a - 1) = k + 1 := by
    rw [hk, ← pow_succ']
    congr 1
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  generalize hz : p ^ (a - 1) = z at hphi hpz
  have hprodZ : (q : ℤ) * r = (k : ℤ) ^ 2 + 1 := by exact_mod_cast hM.symm
  have hphiZ : ((q : ℤ) - 1) * ((r : ℤ) - 1) = k * (z * ((p : ℤ) - 1)) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hphi
    push_cast [Nat.cast_sub hq.one_lt.le, Nat.cast_sub hr.one_lt.le,
      Nat.cast_sub hp.one_lt.le] at h
    exact h
  have hpzZ : (p : ℤ) * z = k + 1 := by exact_mod_cast hpz
  have hsumZ : (q : ℤ) + r = k * ((z : ℤ) - 1) + 2 := by
    linear_combination hprodZ - hphiZ - (k : ℤ) * hpzZ
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · have ha2 : a = 2 := by omega
    subst ha2
    have hzp : z = p := by rw [← hz]; norm_num
    rw [hzp] at hpzZ hsumZ
    by_cases hp3' : p = 3
    · subst hp3'
      refine ⟨rfl, rfl, ?_⟩
      norm_num at hk
      omega
    · exfalso
      have hp5 : 5 ≤ p := by
        have := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
        omega
      have hP : (5 : ℤ) ≤ p := by exact_mod_cast hp5
      rcases le_total (q : ℤ) r with hle | hle
      · exact core_square hP hpzZ hsumZ hprodZ hle
      · exact core_square hP hpzZ (by linarith) (by linarith [mul_comm (q : ℤ) r]) hle
  · exfalso
    have hz2 : p ^ 2 ≤ z := hz ▸ Nat.pow_le_pow_right hp.pos (by omega)
    have hZ : (p : ℤ) ^ 2 ≤ z := by exact_mod_cast hz2
    have hP : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    rcases le_total (q : ℤ) r with hle | hle
    · exact core_big hP hZ hpzZ hsumZ hprodZ hle
    · exact core_big hP hZ hpzZ (by linarith) (by linarith [mul_comm (q : ℤ) r]) hle

/-- The forward direction of the `V ≤ 6` theorem. -/
private theorem odd_prime_power_eq_of_two_adic_le_six {p a k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 2 ≤ a) (hk : k + 1 = p ^ a)
    (hV : padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1) ≤ 6) (hA : A k) :
    p = 3 ∧ a = 2 ∧ k = 8 := by
  rw [show p ^ a - 1 = k by omega] at hV
  have ha1 : 1 ≤ a := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hkeven : Even k := by
    obtain ⟨c, hc⟩ := hpodd.pow (n := a)
    exact ⟨c, by omega⟩
  have hk0 : k ≠ 0 := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hz0 : p ^ (a - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hzodd : ¬ 2 ∣ p ^ (a - 1) := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hpodd.pow
  -- `v₂ (φ M) = V` (PROOF.md, equation (5))
  have hv : padicValNat 2 (Nat.totient (k ^ 2 + 1)) =
      padicValNat 2 k + padicValNat 2 (p - 1) := by
    rw [totient_sq_add_one hp ha1 hk hA, padicValNat.mul hk0 (mul_ne_zero hz0 hp1),
      padicValNat.mul hz0 hp1, padicValNat.eq_zero_of_not_dvd hzodd, zero_add]
  have hφ0 : Nat.totient (k ^ 2 + 1) ≠ 0 := (Nat.totient_pos.mpr (by positivity)).ne'
  have hdvd : ∀ n, 2 ^ n ∣ Nat.totient (k ^ 2 + 1) ↔
      n ≤ padicValNat 2 k + padicValNat 2 (p - 1) := by
    intro n
    rw [← hv]
    exact padicValNat_dvd_iff_le hφ0
  have hnot7 : ¬ 2 ^ 7 ∣ Nat.totient (k ^ 2 + 1) := by
    rw [hdvd]
    omega
  have hsq : ∀ t : ℕ, t.Prime → t ∣ k ^ 2 + 1 → ¬ t * t ∣ k ^ 2 + 1 :=
    fun t ht htM => prime_mul_self_not_dvd hp hp2 ha1 hk hA ht htM
  have hM1 : k ^ 2 + 1 ≠ 1 := by
    have := pow_ne_zero 2 hk0
    omega
  -- `M = q * m`, `m = r * s`; `M` is not prime, so `m ≠ 1`
  obtain ⟨q, m, hq, hqm, hmM, htq⟩ := peel hsq (dvd_refl _) hM1
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hqm
    exact sq_add_one_not_prime hp ha hk hA (hqm ▸ hq)
  obtain ⟨r, s, hr, hrs, hsM, htr⟩ := peel hsq hmM hm1
  by_cases hs1 : s = 1
  · subst hs1
    rw [mul_one] at hrs
    subst hrs
    exact odd_prime_power_solution_of_two_prime_factors hp hp2 ha hk hA hq hr hqm
  -- at least three prime factors: `s = t * u`
  exfalso
  obtain ⟨t, u, ht, htu, huM, htt⟩ := peel hsq hsM hs1
  have hqM : q ∣ k ^ 2 + 1 := hqm ▸ dvd_mul_right q m
  have hrM : r ∣ k ^ 2 + 1 := (hrs ▸ dvd_mul_right r s : r ∣ m).trans hmM
  have htM : t ∣ k ^ 2 + 1 := (htu ▸ dvd_mul_right t u : t ∣ s).trans hsM
  have hq4 := prime_dvd_mod_four hkeven hq hqM
  have hr4 := prime_dvd_mod_four hkeven hr hrM
  have ht4 := prime_dvd_mod_four hkeven ht htM
  have hφ : Nat.totient (k ^ 2 + 1) = (q - 1) * ((r - 1) * ((t - 1) * Nat.totient u)) := by
    rw [htq, htr, htt]
  have h4 : ∀ x, x % 4 = 1 → 4 ∣ x - 1 := fun x hx => Nat.dvd_of_mod_eq_zero (by omega)
  by_cases hu1 : u = 1
  · -- exactly three prime factors: all are `5 mod 8`, so `M ≡ 5 [MOD 8]`, but `8 ∣ k`
    subst hu1
    rw [Nat.totient_one, mul_one] at hφ
    rw [hφ] at hnot7 hdvd
    have h8 : ∀ x, x % 4 = 1 → x % 8 ≠ 5 → 8 ∣ x - 1 :=
      fun x h1 h2 => Nat.dvd_of_mod_eq_zero (by omega)
    have hq8 : q % 8 = 5 := by
      by_contra hne
      exact hnot7 ((show 2 ^ 7 = 8 * (4 * 4) by norm_num) ▸
        Nat.mul_dvd_mul (h8 q hq4 hne) (Nat.mul_dvd_mul (h4 r hr4) (h4 t ht4)))
    have hr8 : r % 8 = 5 := by
      by_contra hne
      exact hnot7 ((show 2 ^ 7 = 4 * (8 * 4) by norm_num) ▸
        Nat.mul_dvd_mul (h4 q hq4) (Nat.mul_dvd_mul (h8 r hr4 hne) (h4 t ht4)))
    have ht8 : t % 8 = 5 := by
      by_contra hne
      exact hnot7 ((show 2 ^ 7 = 4 * (4 * 8) by norm_num) ▸
        Nat.mul_dvd_mul (h4 q hq4) (Nat.mul_dvd_mul (h4 r hr4) (h8 t ht4 hne)))
    have hM8 : (k ^ 2 + 1) % 8 = 5 := by
      rw [hqm, hrs, htu, mul_one, Nat.mul_mod, Nat.mul_mod r, hq8, hr8, ht8]
    have h6 := (hdvd 6).mp ((show 2 ^ 6 = 4 * (4 * 4) by norm_num) ▸
      Nat.mul_dvd_mul (h4 q hq4) (Nat.mul_dvd_mul (h4 r hr4) (h4 t ht4)))
    have hvp : padicValNat 2 (p - 1) ≤ padicValNat 2 k :=
      (padicValNat_dvd_iff_le hk0).mp (pow_padicValNat_dvd.trans (sub_one_dvd hk))
    obtain ⟨c, hc⟩ : 2 ^ 3 ∣ k := (padicValNat_dvd_iff_le hk0).mpr (by omega)
    rw [hc, show (2 ^ 3 * c) ^ 2 + 1 = 8 * (8 * c ^ 2) + 1 by ring] at hM8
    omega
  · -- four or more prime factors: `2 ^ 8 ∣ φ M`
    have hu4 := four_dvd_totient_of_dvd hkeven huM hu1
    rw [hφ] at hnot7
    exact hnot7 ((show 2 ^ 7 ∣ 4 * (4 * (4 * 4)) by norm_num).trans
      (Nat.mul_dvd_mul (h4 q hq4) (Nat.mul_dvd_mul (h4 r hr4) (Nat.mul_dvd_mul (h4 t ht4) hu4))))

/-- Odd prime powers with `V = v₂(p ^ a - 1) + v₂(p - 1) ≤ 6`: if `k + 1 = p ^ a`
with `p` an odd prime and `a ≥ 2`, then `k` is a member of A067720 iff
`(p, a, k) = (3, 2, 8)`. This extends the `V ≤ 5` theorem of PROOF.md by one. -/
theorem odd_prime_power_solution_iff_of_two_adic_le_six {p a k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hk : k + 1 = p ^ a)
    (hV : padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1) ≤ 6) :
    A k ↔ p = 3 ∧ a = 2 ∧ k = 8 := by
  refine ⟨odd_prime_power_eq_of_two_adic_le_six hp hp2 ha hk hV, ?_⟩
  rintro ⟨-, -, rfl⟩
  exact a_eight

/-- The odd-prime theorem of PROOF.md: if `k + 1 = p ^ a` with `p` an odd prime,
`a ≥ 2` and `V = v₂(p ^ a - 1) + v₂(p - 1) ≤ 5`, then `k` is a member of A067720 iff
`(p, a, k) = (3, 2, 8)`. -/
theorem odd_prime_power_solution_iff_of_two_adic_le_five {p a k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 2 ≤ a) (hk : k + 1 = p ^ a)
    (hV : padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1) ≤ 5) :
    A k ↔ p = 3 ∧ a = 2 ∧ k = 8 :=
  odd_prime_power_solution_iff_of_two_adic_le_six hp hp2 ha hk (by omega)

end AgenticConjectures.OeisA067720
