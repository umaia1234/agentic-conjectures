import Mathlib

/-!
# OEIS A239293 — the immediate-successor conjecture, proved

OEIS A239293 defines `a(n)` as the least composite `c > n` for which
`n^c ≡ n (mod c)`, and conjectures that `a(n) = n + 1` exactly when `n + 1`
is odd and composite.

This module proves that characterization for every official index `n ≥ 1`.
The forward implication uses only the residue `n = -1` modulo `n + 1`: an even
exponent would force `1 = -1`, hence `n + 1 ∣ 2`, contradicting compositeness.
The reverse implication uses the same residue with an odd exponent; minimality
then follows because no natural number lies strictly between `n` and `n + 1`.

Faithfulness notes (there is no upstream Lean snapshot for this entry):
- `WeakPseudoprimeAbove n c` spells out the OEIS conditions: `c > n`, `c` is
  composite (`1 < c` and not prime), and `n^c ≡ n (mod c)`.
- `a n` is the infimum of exactly those candidates. For `n ≥ 1`,
  `weakPseudoprimeAbove_nonempty` proves that this set is nonempty, using
  mathlib's theorem that arbitrarily large Fermat pseudoprimes exist to every
  positive base. Thus the infimum is genuinely the least candidate.
- The theorem starts at `n = 1`, matching the OEIS offset. No claim is made
  about a synthetic `n = 0` term.
- The congruence is represented by equality in `ZMod c`, which is equivalent
  to ordinary natural-number congruence modulo `c`.
-/

namespace AgenticConjectures.OeisA239293

/-- A composite `c > n` that satisfies the weak Fermat congruence to base `n`. -/
def WeakPseudoprimeAbove (n c : ℕ) : Prop :=
  n < c ∧ 1 < c ∧ ¬c.Prime ∧ (n : ZMod c) ^ c = n

/-- For every positive base, the set of weak pseudoprimes above that base is
nonempty. This makes the `sInf` in `a` an attained minimum at every official
OEIS index. -/
theorem weakPseudoprimeAbove_nonempty (n : ℕ) (hn : 1 ≤ n) :
    Set.Nonempty {c : ℕ | WeakPseudoprimeAbove n c} := by
  obtain ⟨c, hc, hnc⟩ := Nat.exists_infinite_pseudoprimes hn (n + 1)
  refine ⟨c, ?_⟩
  rcases hc with ⟨hprobable, hnotprime, hcomposite⟩
  refine ⟨by omega, hcomposite, hnotprime, ?_⟩
  have hmod : n ^ (c - 1) ≡ 1 [MOD c] :=
    (Nat.probablePrime_iff_modEq c hn).mp hprobable
  have hzmod : (n : ZMod c) ^ (c - 1) = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (n ^ (c - 1)) 1 c).2 hmod
  calc
    (n : ZMod c) ^ c = (n : ZMod c) ^ (c - 1 + 1) := by
      rw [Nat.sub_add_cancel (by omega)]
    _ = (n : ZMod c) ^ (c - 1) * n := by rw [pow_succ]
    _ = n := by rw [hzmod, one_mul]

/-- OEIS A239293, defined as the least qualifying composite above `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {c : ℕ | WeakPseudoprimeAbove n c}

private theorem a_mem (n : ℕ) (hn : 1 ≤ n) : WeakPseudoprimeAbove n (a n) := by
  exact Nat.sInf_mem (weakPseudoprimeAbove_nonempty n hn)

private theorem cast_succ_eq_neg_one (n : ℕ) :
    (n : ZMod (n + 1)) = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (n + 1)

/-- The exact OEIS conjecture, with its official offset `n ≥ 1`. -/
def statement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (a n = n + 1 ↔ Odd (n + 1) ∧ 1 < n + 1 ∧ ¬(n + 1).Prime)

/-- **OEIS A239293:** `a(n) = n + 1` if and only if `n + 1` is an odd
composite number. -/
theorem a_eq_succ_iff_odd_composite : statement := by
  intro n hn
  constructor
  · intro ha
    have hc := a_mem n hn
    rw [ha] at hc
    refine ⟨?_, hc.2.1, hc.2.2.1⟩
    by_contra hodd
    have heven : Even (n + 1) := Nat.not_odd_iff_even.mp hodd
    have hbase : (n : ZMod (n + 1)) = -1 := cast_succ_eq_neg_one n
    have hone_eq_neg_one : (1 : ZMod (n + 1)) = -1 := by
      calc
        (1 : ZMod (n + 1)) = (-1) ^ (n + 1) := (heven.neg_one_pow).symm
        _ = (n : ZMod (n + 1)) ^ (n + 1) := by rw [hbase]
        _ = (n : ZMod (n + 1)) := hc.2.2.2
        _ = -1 := hbase
    have htwo_zero : (2 : ZMod (n + 1)) = 0 := by
      calc
        (2 : ZMod (n + 1)) = 1 + 1 := by norm_num
        _ = -1 + 1 := congrArg (fun x : ZMod (n + 1) => x + 1) hone_eq_neg_one
        _ = 0 := neg_add_cancel 1
    have hdiv : n + 1 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (n + 1)).mp htwo_zero
    have hle : n + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have heq : n + 1 = 2 := by omega
    exact hc.2.2.1 (heq.symm ▸ Nat.prime_two)
  · rintro ⟨hodd, hgt, hnotprime⟩
    have hbase : (n : ZMod (n + 1)) = -1 := cast_succ_eq_neg_one n
    have hcandidate : WeakPseudoprimeAbove n (n + 1) := by
      refine ⟨by omega, hgt, hnotprime, ?_⟩
      calc
        (n : ZMod (n + 1)) ^ (n + 1) = (-1) ^ (n + 1) := by rw [hbase]
        _ = -1 := hodd.neg_one_pow
        _ = (n : ZMod (n + 1)) := hbase.symm
    apply Nat.le_antisymm
    · exact Nat.sInf_le hcandidate
    · have hleast := a_mem n hn
      exact hleast.1

end AgenticConjectures.OeisA239293
