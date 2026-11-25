import Mathlib

/-!
# OEIS A067720 — prime-power subfamily

The pinned upstream snapshot
`problems/oeis-a067720/upstream/67720.lean` defines membership in A067720 by

`Nat.totient (k ^ 2 + 1) = k * Nat.totient (k + 1)`

and conjectures that every member other than `8` has `k + 1` prime. The
definition below copies that proposition exactly.

Two subfamilies are proved, both with `k + 1 = p ^ a` and `a ≥ 2`:

* `power_two_add_one_not_solution`: no solution with `p = 2`.
* `odd_prime_power_small_two_valuation_iff`: if `p` is an odd prime and
  `padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1) ≤ 5`, then the equation
  holds if and only if `(p, a, k) = (3, 2, 8)`.

Faithfulness: both theorems use natural-number exponentiation and
`padicValNat 2` for the 2-adic valuation, exactly as the upstream equation and
the informal argument in `problems/oeis-a067720/PROOF.md`. The hypothesis
`2 ≤ a` excludes the prime boundary `a = 1`. Neither theorem says anything
about a general composite `k + 1`, about odd prime powers with 2-adic sum at
least 6, or about the upstream universal conjecture.
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

/-- `k = 8` satisfies the upstream equation. `65 = 5 * 13` and `9 = 3 ^ 2`. -/
theorem eight_is_solution : A 8 := by
  unfold A
  rw [show (8 ^ 2 + 1 : ℕ) = 5 * 13 by norm_num, show (8 + 1 : ℕ) = 3 ^ 2 by norm_num]
  rw [Nat.totient_mul (by norm_num : (5 : ℕ).Coprime 13),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 13),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2)]
  norm_num

/-- `x ↦ x * (S - x)` is strictly increasing on the integers `0 ≤ x ≤ S / 2`. -/
private lemma quad_strictMono {S x y : ℕ} (hxy : x < y) (hy : 2 * y ≤ S) :
    x * (S - x) < y * (S - y) := by
  have hxS : x ≤ S := by omega
  have hyS : y ≤ S := by omega
  zify [hxS, hyS]
  have hdiff :
      (y : ℤ) * ((S : ℤ) - y) - (x : ℤ) * ((S : ℤ) - x) =
        ((y : ℤ) - x) * ((S : ℤ) - x - y) := by ring
  have hpos : 0 < ((y : ℤ) - x) * ((S : ℤ) - x - y) := by
    have h1 : 0 < (y : ℤ) - x := by omega
    have h2 : 0 < (S : ℤ) - x - y := by omega
    nlinarith
  linarith

/-- For squarefree `n`, `φ(n)` is the product of `p - 1` over the prime factors. -/
private lemma totient_squarefree {n : ℕ} (hn : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
  have h0 : n ≠ 0 := hn.ne_zero
  rw [Nat.totient_eq_prod_factorization h0, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hle : n.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one h0).mp hn p
  have hpos : 0 < n.factorization p := by
    have hone : 1 ≤ n.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization (Nat.prime_of_mem_primeFactors hp) h0).mp
        (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hfac : n.factorization p = 1 := by omega
  simp [hfac]

/-- The `p`-adic valuation of a finite product is the sum of the valuations. -/
private lemma padicValNat_finset_prod {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  induction s using Finset.induction with
  | empty => simp [padicValNat_one_right]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hprod : ∏ i ∈ s, f i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [padicValNat.mul hfa hprod, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- The diameter-side bound `S > 2(p+2)` reduces to this cubic inequality. -/
private lemma two_mul_add_two_lt_square {p : ℕ} (hp : 3 ≤ p) :
    2 * (p + 2) < (p ^ 2 - 1) * (p - 1) + 2 := by
  have hsq : 1 ≤ p ^ 2 := by nlinarith
  have hp1 : 1 ≤ p := by omega
  zify [hsq, hp1]
  nlinarith

private lemma int_k {p z k : ℕ} (hk : k + 1 = p * z) : (k : ℤ) = (p : ℤ) * z - 1 := by
  have : (k : ℤ) + 1 = (p : ℤ) * z := by exact_mod_cast hk
  linarith

private lemma int_S {k z S : ℕ} (hz : 1 ≤ z) (hS : S = k * (z - 1) + 2) :
    (S : ℤ) = (k : ℤ) * ((z : ℤ) - 1) + 2 := by
  rw [hS, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hz]
  simp

private lemma fp_lt_target {p z k S : ℕ} (hp : 3 ≤ p) (hz : 1 ≤ z) (hk : k + 1 = p * z)
    (hS : S = k * (z - 1) + 2) (hpS : p ≤ S) : p * (S - p) < k ^ 2 + 1 := by
  have hkcast := int_k hk
  have hScast := int_S hz hS
  have hid : ((k : ℤ) ^ 2 + 1) - (p : ℤ) * ((S : ℤ) - p) =
      ((p : ℤ) - 1) * ((p : ℤ) * z + p - 2) := by
    rw [hScast, hkcast]
    ring
  have hpos : 0 < ((p : ℤ) - 1) * ((p : ℤ) * z + p - 2) := by
    have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp
    have hzz : (1 : ℤ) ≤ z := by exact_mod_cast hz
    nlinarith
  have hZ : ((p * (S - p) : ℕ) : ℤ) < ((k ^ 2 + 1 : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_sub hpS, Nat.cast_add, Nat.cast_pow]
    simp
    linarith
  exact_mod_cast hZ

private lemma succ_quad_gt {p z k S : ℕ} (hp : 3 ≤ p) (hz2 : p ^ 2 ≤ z) (hk : k + 1 = p * z)
    (hS : S = k * (z - 1) + 2) (hp1S : p + 1 ≤ S) :
    k ^ 2 + 1 < (p + 1) * (S - (p + 1)) := by
  have hkcast := int_k hk
  have hScast := int_S (le_trans (by nlinarith : 1 ≤ p ^ 2) hz2) hS
  have hg : (p + 1 : ℤ) * ((S : ℤ) - (p + 1)) - ((k : ℤ) ^ 2 + 1) =
      (p : ℤ) * z ^ 2 - (p : ℤ) ^ 2 * z - z - (p : ℤ) ^ 2 + p := by
    rw [hScast, hkcast]
    ring
  have hg_pos : 0 < (p : ℤ) * z ^ 2 - (p : ℤ) ^ 2 * z - z - (p : ℤ) ^ 2 + p := by
    have hbase : 0 < (p : ℤ) ^ 4 - (p : ℤ) ^ 3 - 2 * p + 1 := by
      have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp
      have hpow : (27 : ℤ) ≤ (p : ℤ) ^ 3 := by
        have : (3 : ℤ) ^ 3 ≤ (p : ℤ) ^ 3 := pow_le_pow_left₀ (by omega) hpz 3
        norm_num at this
        exact this
      nlinarith
    have hdelta : 0 ≤ ((z : ℤ) - p ^ 2) * ((p : ℤ) * (z + p ^ 2) - (p : ℤ) ^ 2 - 1) := by
      have hzp : (p : ℤ) ^ 2 ≤ z := by exact_mod_cast hz2
      have hcoef : 0 ≤ (p : ℤ) * (z + (p : ℤ) ^ 2) - (p : ℤ) ^ 2 - 1 := by
        have hpz : (3 : ℤ) ≤ p := by exact_mod_cast hp
        nlinarith
      have hgap : 0 ≤ (z : ℤ) - (p : ℤ) ^ 2 := by linarith
      nlinarith
    have hsplit : (p : ℤ) * z ^ 2 - (p : ℤ) ^ 2 * z - z - (p : ℤ) ^ 2 + p =
        (p : ℤ) * ((p : ℤ) ^ 4 - (p : ℤ) ^ 3 - 2 * p + 1) +
          ((z : ℤ) - p ^ 2) * ((p : ℤ) * (z + p ^ 2) - (p : ℤ) ^ 2 - 1) := by ring
    nlinarith
  have hZ : ((k ^ 2 + 1 : ℕ) : ℤ) < (((p + 1) * (S - (p + 1)) : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_sub hp1S]
    simp
    linarith
  exact_mod_cast hZ

private lemma a2_low {p k S : ℕ} (hp : 3 ≤ p) (hk : k + 1 = p * p)
    (hS : S = k * (p - 1) + 2) (hp1S : p + 1 ≤ S) :
    (p + 1) * (S - (p + 1)) < k ^ 2 + 1 := by
  have hkcast := int_k hk
  have hScast := int_S (by omega) hS
  have hid : ((p + 1 : ℤ) * ((S : ℤ) - (p + 1)) : ℤ) + (p : ℤ) ^ 2 = (k : ℤ) ^ 2 + 1 := by
    rw [hScast, hkcast]
    ring
  have hZ : (((p + 1) * (S - (p + 1)) : ℕ) : ℤ) + ((p ^ 2 : ℕ) : ℤ) =
      ((k ^ 2 + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_mul, Nat.cast_sub hp1S, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    linarith
  have hnat : (p + 1) * (S - (p + 1)) + p ^ 2 = k ^ 2 + 1 := by exact_mod_cast hZ
  have hp2 : 0 < p ^ 2 := by nlinarith
  have : (p + 1) * (S - (p + 1)) < (p + 1) * (S - (p + 1)) + p ^ 2 := by omega
  rwa [hnat] at this

private lemma a2_high {p k S : ℕ} (hp : 3 < p) (hk : k + 1 = p * p)
    (hS : S = k * (p - 1) + 2) (hp2S : p + 2 ≤ S) :
    k ^ 2 + 1 < (p + 2) * (S - (p + 2)) := by
  have hkcast := int_k hk
  have hScast := int_S (by omega) hS
  have hid : ((p + 2 : ℤ) * ((S : ℤ) - (p + 2))) =
      ((k : ℤ) ^ 2 + 1) + (p : ℤ) * ((p : ℤ) - 3) * ((p : ℤ) + 1) := by
    rw [hScast, hkcast]
    ring
  have hpos : 0 < (p : ℤ) * ((p : ℤ) - 3) * ((p : ℤ) + 1) := by
    have hpz : (4 : ℤ) ≤ p := by exact_mod_cast hp
    nlinarith
  have hZ : ((k ^ 2 + 1 : ℕ) : ℤ) < (((p + 2) * (S - (p + 2)) : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_sub hp2S]
    simp
    linarith
  exact_mod_cast hZ

/-- Odd prime powers with `V = v₂(p^a - 1) + v₂(p - 1) ≤ 5` solve the upstream
equation if and only if `(p, a, k) = (3, 2, 8)`. -/
theorem odd_prime_power_small_two_valuation_iff {p a k : ℕ} (hp : p.Prime) (hodd : Odd p)
    (ha : 2 ≤ a) (hk : k + 1 = p ^ a)
    (hV : padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1) ≤ 5) :
    A k ↔ p = 3 ∧ a = 2 ∧ k = 8 := by
  constructor
  · intro hA
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      rw [hp2] at hodd
      exact Nat.not_odd_iff_even.mpr even_two hodd
    have hp3 : 3 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have ha_pos : 0 < a := by omega
    have hpa_pos : 0 < p ^ a := Nat.pow_pos hp.pos
    have hk_sub : k = p ^ a - 1 := by omega
    have hk_pos : 0 < k := by
      have : 9 ≤ p ^ a := by
        calc
          9 = 3 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
          _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
      omega
    let M : ℕ := k ^ 2 + 1
    have hMdef : M = k ^ 2 + 1 := rfl
    have hMpos : 0 < M := by omega
    let z : ℕ := p ^ (a - 1)
    have hz_pos : 0 < z := Nat.pow_pos hp.pos
    have hz_ge : p ≤ z := by
      have : 1 ≤ a - 1 := by omega
      simpa [z] using Nat.pow_le_pow_right hp.pos this
    have hkz : k + 1 = p * z := by
      calc
        k + 1 = p ^ a := hk
        _ = p ^ (a - 1 + 1) := by congr 1; omega
        _ = p ^ (a - 1) * p := by rw [Nat.pow_succ]
        _ = p * z := by rw [Nat.mul_comm]
    have hk_eq : k = p * z - 1 := by omega
    have hφpow : Nat.totient (k + 1) = p ^ (a - 1) * (p - 1) := by
      rw [hk, Nat.totient_prime_pow hp ha_pos]
    have hφM : Nat.totient M = k * (z * (p - 1)) := by
      unfold A at hA
      rw [← hMdef, hφpow] at hA
      simpa [z, Nat.mul_assoc] using hA
    have hMk : Nat.Coprime M k := by
      have hshape : M = 1 + k * k := by simp [hMdef, Nat.pow_two, Nat.add_comm]
      rw [hshape, Nat.coprime_add_mul_left_left]
      exact Nat.coprime_one_left k
    have hMp : Nat.Coprime M p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hpdvd
      have hcast : (M : ZMod p) = 2 := by
        have hkcast : (k : ZMod p) = -1 := by
          have hsum0 : ((k + 1 : ℕ) : ZMod p) = 0 := by
            rw [hk]
            exact (ZMod.natCast_eq_zero_iff (p ^ a) p).2 (dvd_pow_self p (by omega))
          have : (k : ZMod p) + 1 = 0 := by simpa using hsum0
          exact eq_neg_of_add_eq_zero_left this
        calc
          (M : ZMod p) = (k : ZMod p) ^ 2 + 1 := by simp [hMdef]
          _ = (-1 : ZMod p) ^ 2 + 1 := by rw [hkcast]
          _ = 2 := by ring
      have htwo0 : (2 : ZMod p) = 0 := by
        rw [← hcast]
        exact (ZMod.natCast_eq_zero_iff M p).2 hpdvd
      have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 htwo0
      exact hp_ne_two ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2)
    have hpm1_dvd_k : p - 1 ∣ k := by
      have hpa1 : 1 ≤ p ^ a := Nat.one_le_pow a p hp.pos
      have hZ : ((p - 1 : ℕ) : ℤ) ∣ ((p ^ a - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub hpa1, Nat.cast_pow]
        exact sub_one_dvd_pow_sub_one (p : ℤ) a
      have : (p - 1) ∣ p ^ a - 1 := Int.natCast_dvd_natCast.mp hZ
      rwa [← hk_sub] at this
    have hMpm1 : Nat.Coprime M (p - 1) := by
      obtain ⟨t, ht⟩ := hpm1_dvd_k
      have hshape : M = 1 + (p - 1) * ((p - 1) * t ^ 2) := by
        rw [hMdef, ht, Nat.pow_two]
        ring
      rw [hshape, Nat.coprime_add_mul_left_left]
      exact Nat.coprime_one_left _
    have hgcd : Nat.Coprime M (Nat.totient M) := by
      rw [hφM]
      refine hMk.mul_right ?_
      refine Nat.Coprime.mul_right ?_ hMpm1
      have hz_exp : 0 < a - 1 := by omega
      rw [show z = p ^ (a - 1) from rfl, Nat.coprime_pow_right_iff hz_exp]
      exact hMp
    have hsq : Squarefree M := by
      rw [Nat.squarefree_iff_factorization_le_one hMpos.ne']
      intro q
      rcases Nat.lt_or_ge (M.factorization q) 2 with hlt | hge
      · omega
      · have hqprime : q.Prime := by
          by_contra hnp
          rw [Nat.factorization_eq_zero_of_not_prime M hnp] at hge
          omega
        have hepos : 0 < M.factorization q := by omega
        have hsplit := Nat.ordProj_mul_ordCompl_eq_self M q
        have hcop : Nat.Coprime (q ^ M.factorization q) (ordCompl[q] M) := by
          rw [Nat.coprime_pow_left_iff hepos]
          exact Nat.coprime_ordCompl hqprime hMpos.ne'
        have hφsplit :
            Nat.totient M =
              Nat.totient (q ^ M.factorization q) * Nat.totient (ordCompl[q] M) := by
          simpa [hsplit] using Nat.totient_mul hcop
        have hφq :
            Nat.totient (q ^ M.factorization q) =
              q ^ (M.factorization q - 1) * (q - 1) :=
          Nat.totient_prime_pow hqprime hepos
        have hqφ : q ∣ Nat.totient M := by
          rw [hφsplit, hφq]
          exact dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_left (dvd_pow_self q (by omega)) _) _
        have hqM : q ∣ M :=
          (hqprime.dvd_iff_one_le_factorization hMpos.ne').2 (by omega)
        have hqgcd : q ∣ Nat.gcd M (Nat.totient M) := Nat.dvd_gcd hqM hqφ
        rw [hgcd.gcd_eq_one] at hqgcd
        exact False.elim (hqprime.not_dvd_one hqgcd)
    have hM_not_prime : ¬M.Prime := by
      intro hMp
      have htot : Nat.totient M = M - 1 := Nat.totient_prime hMp
      have hM1 : M - 1 = k ^ 2 := by omega
      have hcancel : k = z * (p - 1) := by
        have heq : k * k = k * (z * (p - 1)) := by
          calc
            k * k = k ^ 2 := by rw [Nat.pow_two]
            _ = M - 1 := hM1.symm
            _ = Nat.totient M := htot.symm
            _ = k * (z * (p - 1)) := hφM
        exact Nat.eq_of_mul_eq_mul_left hk_pos heq
      have hpow1 : p ^ (a - 1) = 1 := by
        have hgeom : p ^ a - 1 = p ^ (a - 1) * (p - 1) := by
          rw [hk_sub] at hcancel
          simpa [z] using hcancel
        have hpow : p ^ a = p ^ (a - 1) * p := by
          calc
            p ^ a = p ^ ((a - 1) + 1) := by congr 1; omega
            _ = p ^ (a - 1) * p ^ 1 := Nat.pow_add _ _ _
            _ = p ^ (a - 1) * p := by simp
        have hsub : p ^ a - p ^ (a - 1) = p ^ (a - 1) * (p - 1) := by
          rw [hpow]
          calc
            p ^ (a - 1) * p - p ^ (a - 1) = p ^ (a - 1) * p - p ^ (a - 1) * 1 := by simp
            _ = p ^ (a - 1) * (p - 1) := by rw [← Nat.mul_sub_left_distrib]
        have : p ^ a - 1 = p ^ a - p ^ (a - 1) := by rw [hgeom, hsub]
        have hle : p ^ (a - 1) ≤ p ^ a := Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)
        omega
      have : a - 1 = 0 := by
        by_contra h
        have : 1 < p ^ (a - 1) := Nat.one_lt_pow h hp.one_lt
        omega
      omega
    have hkeven : Even k := by
      have hsucc : Odd (k + 1) := by
        rw [hk]
        exact Odd.pow (hp.odd_of_ne_two hp_ne_two)
      rw [← Nat.not_odd_iff_even]
      exact Nat.odd_add_one.mp hsucc
    have hModd : Odd M := by
      rw [hMdef, Nat.pow_two]
      exact Even.add_odd (Even.mul_right hkeven k) odd_one
    have hsquare : IsSquare (-1 : ZMod M) := by
      refine ⟨(k : ZMod M), ?_⟩
      have hzero : ((k ^ 2 + 1 : ℕ) : ZMod M) = 0 := by
        simp
      have hsum : (k : ZMod M) * k + 1 = 0 := by
        simpa [pow_two, Nat.cast_add, Nat.cast_pow] using hzero
      exact (eq_neg_of_add_eq_zero_left hsum).symm
    have hmod4 : ∀ q ∈ M.primeFactors, q % 4 = 1 := by
      intro q hq
      have hqprime := Nat.prime_of_mem_primeFactors hq
      have hq_ne_two : q ≠ 2 := by
        intro hq2
        have hdiv : 2 ∣ M := by simpa [hq2] using Nat.dvd_of_mem_primeFactors hq
        exact Nat.not_even_iff_odd.mpr hModd (even_iff_two_dvd.mpr hdiv)
      have hqodd : Odd q := hqprime.odd_of_ne_two hq_ne_two
      have hne3 : q % 4 ≠ 3 :=
        Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hq hsquare
      have hqmod : q % 2 = 1 := Nat.odd_iff.mp hqodd
      have hlt : q % 4 < 4 := Nat.mod_lt _ (by norm_num)
      omega
    have hvφ : padicValNat 2 (Nat.totient M) =
        padicValNat 2 (p ^ a - 1) + padicValNat 2 (p - 1) := by
      rw [hφM]
      have hk0 : k ≠ 0 := hk_pos.ne'
      have hz0 : z ≠ 0 := hz_pos.ne'
      have hpm0 : p - 1 ≠ 0 := by omega
      rw [padicValNat.mul hk0 (mul_ne_zero hz0 hpm0), padicValNat.mul hz0 hpm0]
      have hzpow : padicValNat 2 z = 0 := by
        rw [show z = p ^ (a - 1) from rfl, padicValNat.pow _ hp.ne_zero]
        have hp2 : padicValNat 2 p = 0 :=
          padicValNat.eq_zero_of_not_dvd (by
            intro hdiv
            exact hp_ne_two (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hdiv).symm))
        simp [hp2]
      rw [hzpow, zero_add, hk_sub]
    have hval_ge : 2 * M.primeFactors.card ≤ padicValNat 2 (Nat.totient M) := by
      have hprod : Nat.totient M = ∏ q ∈ M.primeFactors, (q - 1) := totient_squarefree hsq
      have hsum : padicValNat 2 (Nat.totient M) =
          ∑ q ∈ M.primeFactors, padicValNat 2 (q - 1) := by
        rw [hprod]
        refine padicValNat_finset_prod fun q hq => ?_
        have : 2 ≤ q := (Nat.prime_of_mem_primeFactors hq).two_le
        omega
      rw [hsum]
      have hterm : ∀ q ∈ M.primeFactors, 2 ≤ padicValNat 2 (q - 1) := by
        intro q hq
        have h4 : 4 ∣ q - 1 := by
          have hmod := hmod4 q hq
          have : q = 4 * (q / 4) + 1 := by
            have := Nat.mod_add_div q 4
            omega
          have hqsub : q - 1 = 4 * (q / 4) := by omega
          exact ⟨q / 4, hqsub⟩
        have hq1 : q - 1 ≠ 0 := by
          have : 2 ≤ q := (Nat.prime_of_mem_primeFactors hq).two_le
          omega
        rw [← padicValNat_dvd_iff_le hq1]
        simpa using h4
      have hconst :
          ∑ q ∈ M.primeFactors, (2 : ℕ) ≤ ∑ q ∈ M.primeFactors, padicValNat 2 (q - 1) :=
        Finset.sum_le_sum hterm
      rw [Finset.sum_const] at hconst
      simpa [nsmul_eq_mul, Nat.mul_comm] using hconst
    have hcard_le : M.primeFactors.card ≤ 2 := by
      have : 2 * M.primeFactors.card ≤ 5 := by
        rw [hvφ] at hval_ge
        exact hval_ge.trans hV
      omega
    have hcard_ne0 : M.primeFactors.card ≠ 0 := by
      intro h0
      have hempty : M.primeFactors = ∅ := Finset.card_eq_zero.mp h0
      have hM1 : M = 1 := by
        rw [← Nat.prod_primeFactors_of_squarefree hsq, hempty]
        simp
      have : 1 < M := by
        have : 65 ≤ k ^ 2 + 1 := by nlinarith
        omega
      omega
    have hcard_ne1 : M.primeFactors.card ≠ 1 := by
      intro h1
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1
      have hMq : M = q := by
        rw [← Nat.prod_primeFactors_of_squarefree hsq, hq]
        simp
      have hqmem : q ∈ M.primeFactors := by
        rw [hq]
        simp
      exact hM_not_prime (hMq ▸ Nat.prime_of_mem_primeFactors hqmem)
    have hcard : M.primeFactors.card = 2 := by omega
    obtain ⟨q0, r0, hne, hset⟩ := Finset.card_eq_two.mp hcard
    have horder : q0 < r0 ∨ r0 < q0 := lt_or_gt_of_ne hne
    let q : ℕ := min q0 r0
    let r : ℕ := max q0 r0
    have hqlt : q < r := by
      rcases horder with h | h
      · simpa [q, r, min_eq_left h.le, max_eq_right h.le] using h
      · simpa [q, r, min_eq_right h.le, max_eq_left h.le] using h
    have hset' : M.primeFactors = {q, r} := by
      rcases horder with h | h
      · simp [q, r, hset, min_eq_left h.le, max_eq_right h.le]
      · simpa [q, r, min_eq_right h.le, max_eq_left h.le, Finset.pair_comm] using hset
    have hqmem : q ∈ M.primeFactors := by
      rw [hset']
      simp
    have hrmem : r ∈ M.primeFactors := by
      rw [hset']
      simp
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hrmem
    have hMqr : M = q * r := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq, hset']
      simp [Finset.prod_pair hqlt.ne, mul_comm]
    have hφqr : Nat.totient M = (q - 1) * (r - 1) := by
      rw [totient_squarefree hsq, hset']
      simp [Finset.prod_pair hqlt.ne, mul_comm]
    have hsum_alg : k * (z - 1) + k * z * (p - 1) = k ^ 2 := by
      have hz1 : 1 ≤ z := Nat.one_le_of_lt hz_pos
      have hp1 : 1 ≤ p := by omega
      have hdist : z * (p - 1) = p * z - z := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm z p]
      have hshift : z * (p - 1) + (z - 1) = p * z - 1 := by
        rw [hdist]
        have hle : z ≤ p * z := Nat.le_mul_of_pos_left z hp.pos
        calc
          p * z - z + (z - 1) = p * z - z + z - 1 := by rw [Nat.add_sub_assoc hz1]
          _ = p * z - 1 := by rw [Nat.sub_add_cancel hle]
      have hfactor : (z - 1) + z * (p - 1) = k := by
        rw [Nat.add_comm, hshift, hk_eq]
      calc
        k * (z - 1) + k * z * (p - 1) = k * ((z - 1) + z * (p - 1)) := by ring
        _ = k * k := by rw [hfactor]
        _ = k ^ 2 := by rw [Nat.pow_two]
    let S : ℕ := k * (z - 1) + 2
    have hSφ : S + Nat.totient M = k ^ 2 + 2 := by
      have : Nat.totient M = k * z * (p - 1) := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hφM
      calc
        S + Nat.totient M = k * (z - 1) + 2 + k * z * (p - 1) := by rw [this]
        _ = k * (z - 1) + k * z * (p - 1) + 2 := by omega
        _ = k ^ 2 + 2 := by rw [hsum_alg]
    have hqrS : q + r = S := by
      have hZ : (q : ℤ) + r = S := by
        have hsubq : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 :=
          Nat.cast_sub (hqprime.one_le)
        have hsubr : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 :=
          Nat.cast_sub (hrprime.one_le)
        have hφZ : (Nat.totient M : ℤ) = ((q : ℤ) - 1) * ((r : ℤ) - 1) := by
          rw [← hsubq, ← hsubr]
          exact_mod_cast hφqr
        have hMZ : (q : ℤ) * r = (k : ℤ) ^ 2 + 1 := by
          have : (M : ℤ) = (k : ℤ) ^ 2 + 1 := by exact_mod_cast hMdef
          have : (q : ℤ) * r = M := by exact_mod_cast hMqr.symm
          linarith
        have hSZ : (S : ℤ) + Nat.totient M = (k : ℤ) ^ 2 + 2 := by exact_mod_cast hSφ
        have hprod : ((q : ℤ) - 1) * ((r : ℤ) - 1) = (q : ℤ) * r - ((q : ℤ) + r) + 1 := by ring
        linarith
      exact_mod_cast hZ
    have hS_big : 2 * (p + 2) < S := by
      have hz1 : 1 ≤ z := Nat.one_le_of_lt hz_pos
      have hkmin : p ^ 2 - 1 ≤ k := by
        rw [Nat.pow_two] at *
        have : p * p ≤ p * z := Nat.mul_le_mul_left p hz_ge
        omega
      have hhmin : p - 1 ≤ z - 1 := by omega
      have hSmin : (p ^ 2 - 1) * (p - 1) + 2 ≤ S := by
        have : (p ^ 2 - 1) * (p - 1) ≤ k * (z - 1) := Nat.mul_le_mul hkmin hhmin
        omega
      exact (two_mul_add_two_lt_square hp3).trans_le hSmin
    have hqf : q * (S - q) = k ^ 2 + 1 := by
      have hrS : r = S - q := by omega
      calc
        q * (S - q) = q * r := by rw [hrS]
        _ = M := hMqr.symm
        _ = k ^ 2 + 1 := hMdef
    have hSdef : S = k * (z - 1) + 2 := rfl
    have hfp_lt : p * (S - p) < k ^ 2 + 1 :=
      fp_lt_target hp3 (Nat.one_le_of_lt hz_pos) hkz hSdef (by omega)
    by_cases ha3 : 3 ≤ a
    · have hz2 : p ^ 2 ≤ z := by
        have : 2 ≤ a - 1 := by omega
        simpa [z] using Nat.pow_le_pow_right hp.pos this
      have hgt : k ^ 2 + 1 < (p + 1) * (S - (p + 1)) :=
        succ_quad_gt hp3 hz2 hkz hSdef (by omega)
      have htwo_p : 2 * p ≤ S := by omega
      have htwo_p1 : 2 * (p + 1) ≤ S := by omega
      have hq_le : 2 * q ≤ S := by omega
      by_cases hqp : q ≤ p
      · have hle : q * (S - q) ≤ p * (S - p) := by
          rcases eq_or_lt_of_le hqp with heq | hlt
          · rw [heq]
          · exact (quad_strictMono hlt htwo_p).le
        have : k ^ 2 + 1 ≤ p * (S - p) := by simpa [hqf] using hle
        omega
      · have hp1q : p + 1 ≤ q := by omega
        have hge : (p + 1) * (S - (p + 1)) ≤ q * (S - q) := by
          rcases eq_or_lt_of_le hp1q with heq | hlt
          · rw [heq]
          · exact (quad_strictMono hlt hq_le).le
        have : (p + 1) * (S - (p + 1)) ≤ k ^ 2 + 1 := by simpa [hqf] using hge
        omega
    · have ha2 : a = 2 := by omega
      have hzp : z = p := by simp [z, ha2]
      have hkpp : k + 1 = p * p := by simpa [hzp] using hkz
      have hSp : S = k * (p - 1) + 2 := by simpa [hzp] using hSdef
      by_cases hp_eq3 : p = 3
      · refine ⟨hp_eq3, ha2, ?_⟩
        have : k + 1 = 9 := by simpa [hp_eq3, ha2] using hk
        omega
      · have hpgt : 3 < p := by omega
        have hlt1 : (p + 1) * (S - (p + 1)) < k ^ 2 + 1 :=
          a2_low (by omega) hkpp hSp (by omega)
        have hgt2 : k ^ 2 + 1 < (p + 2) * (S - (p + 2)) :=
          a2_high hpgt hkpp hSp (by omega)
        have htwo_p1 : 2 * (p + 1) ≤ S := by omega
        have hq_le : 2 * q ≤ S := by omega
        by_cases hqp : q ≤ p + 1
        · have hle : q * (S - q) ≤ (p + 1) * (S - (p + 1)) := by
            rcases eq_or_lt_of_le hqp with heq | hlt
            · rw [heq]
            · exact (quad_strictMono hlt htwo_p1).le
          have : k ^ 2 + 1 ≤ (p + 1) * (S - (p + 1)) := by simpa [hqf] using hle
          omega
        · have hp2q : p + 2 ≤ q := by omega
          have hge : (p + 2) * (S - (p + 2)) ≤ q * (S - q) := by
            rcases eq_or_lt_of_le hp2q with heq | hlt
            · rw [heq]
            · exact (quad_strictMono hlt hq_le).le
          have : (p + 2) * (S - (p + 2)) ≤ k ^ 2 + 1 := by simpa [hqf] using hge
          omega
  · rintro ⟨hp3, ha2, hk8⟩
    simpa [hk8] using eight_is_solution

end AgenticConjectures.OeisA067720
