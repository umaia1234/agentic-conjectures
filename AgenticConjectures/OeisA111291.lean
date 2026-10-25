import Mathlib

/-!
# OEIS A111291 — Colton's conjecture on refactorable numbers

A positive integer `k` is *refactorable* (a tau number, OEIS A033950) if its number of divisors
`τ(k)` divides `k`, and OEIS A111291 counts the refactorable numbers `≤ 10^n`. Write `T(n)` for
the number of refactorable numbers `≤ n`. Colton's conjecture, as stated by Zelinsky
(J. Integer Seq. 5 (2002), Article 02.2.8), is `π(n) ≤ 2 T(n)` for every `n`.

Upstream: `FormalConjectures/OEIS/111291.lean` in google-deepmind/formal-conjectures at commit
`c094b979118b89adb77cf5f8d923ac9dd2e51b1d` (snapshot in `problems/oeis-a111291/upstream/`).
`countRefactorableNat`, `a` and `countRefactorable` and the tests `a_0`, `a_1`, `a_2` are copied
term for term. `statement` is the proposition of the upstream theorem `colton_conjecture`,
written as a `def … : Prop` because its proof is computer-assisted and is not formalized here.
Adaptations: `import Mathlib` replaces the upstream `module` header (`public import
FormalConjecturesUtil`, `meta import Mathlib.NumberTheory.PrimeCounting`, `@[expose] public
section`); the namespace is `AgenticConjectures.OeisA111291`; the `category` and `AMS`
attributes are dropped; the tests `a_3`, `a_4` and `colton_conjecture_le_500` (proved upstream by
`native_decide`) and the asymptotic theorem `conjecture` (a `sorry` upstream, not part of this
problem) are omitted.

The theorems below are the elementary steps of the proof in `problems/oeis-a111291/DETAILS.md`:
the bound `π(7) = 2 T(7)` shows that the constant `2` cannot be lowered; `grid_step` is the
monotonicity step of the grid certificate; `isSquare_of_odd_refactorable` and
`two_mul_refactorable_iff` are the reductions used by the structured counter;
`refactorable_mul_prime` (Zelinsky's Lemma 6) and `sum_primeCounting_sub_le` give the lower
bound `T(x) ≥ ∑_{d ∈ G} (π(x / d) - π(P(d)))` on which the analytic tail rests.
-/

namespace AgenticConjectures.OeisA111291

open Nat Finset Real

/-- Helper function: number of refactorable numbers $\le m$. -/
def countRefactorableNat (m : ℕ) : ℕ :=
  (Icc 1 m).filter (fun k => k.divisors.card ∣ k) |>.card

/--
`a n` is the number of refactorable numbers $\le 10^n$.
A number $k$ is refactorable if its number of divisors, $\tau(k)$, divides $k$.
-/
def a (n : ℕ) : ℕ :=
  countRefactorableNat (10 ^ n)

theorem a_0 : a 0 = 1 := by rfl

theorem a_1 : a 1 = 4 := by rfl

theorem a_2 : a 2 = 16 := by rfl

/--
`countRefactorable x` is the number of refactorable numbers $\le x$.
-/
noncomputable def countRefactorable (x : ℝ) : ℕ :=
  if _hx : x ≥ 1 then
    countRefactorableNat (Int.toNat (floor x))
  else
    0

/-- Colton's conjecture (upstream `colton_conjecture`): `π(n) ≤ 2 T(n)` for every `n`. -/
def statement : Prop :=
  ∀ n : ℕ, Nat.primeCounting n ≤ 2 * countRefactorableNat n

/-- Equality holds at `n = 7`: `π(7) = 4` and the refactorable numbers `≤ 7` are `1` and `2`. -/
theorem primeCounting_seven : Nat.primeCounting 7 = 2 * countRefactorableNat 7 := by
  decide

/-- `T` is monotone. -/
theorem countRefactorableNat_mono : Monotone countRefactorableNat := fun _ _ h =>
  card_le_card (filter_subset_filter _ (Icc_subset_Icc_right h))

/-- Grid step: if `x ≤ n ≤ y` and `π(y) ≤ 2 T(x)`, then `π(n) ≤ 2 T(n)`. -/
theorem grid_step {x y n : ℕ} (h : Nat.primeCounting y ≤ 2 * countRefactorableNat x)
    (hx : x ≤ n) (hy : n ≤ y) : Nat.primeCounting n ≤ 2 * countRefactorableNat n :=
  ((Nat.monotone_primeCounting hy).trans h).trans
    (Nat.mul_le_mul_left 2 (countRefactorableNat_mono hx))

/-- An odd refactorable number is a perfect square (Colton). -/
theorem isSquare_of_odd_refactorable {n : ℕ} (hn : Odd n) (h : n.divisors.card ∣ n) :
    IsSquare n := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hodd : Odd (n.primeFactors.prod (n.factorization · + 1)) :=
    Nat.card_divisors hn0 ▸ hn.of_dvd_nat h
  have hev : ∀ p ∈ n.factorization.support, Even (n.factorization p) := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have := hodd.of_dvd_nat (dvd_prod_of_mem (n.factorization · + 1) hp)
    simpa [Nat.odd_add_one] using this
  refine ⟨n.factorization.prod fun p e => p ^ (e / 2), ?_⟩
  rw [← Finsupp.prod_mul]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
  refine Finsupp.prod_congr fun p hp => ?_
  obtain ⟨k, hk⟩ := hev p hp
  rw [← pow_add, hk]
  congr 1
  omega

/-- For odd `u`, `2 u` is refactorable iff `u` is (Colton). -/
theorem two_mul_refactorable_iff {u : ℕ} (hu : Odd u) :
    (2 * u).divisors.card ∣ 2 * u ↔ u.divisors.card ∣ u := by
  rw [Nat.Coprime.card_divisors_mul (Nat.coprime_two_left.mpr hu), Nat.prime_two.divisors,
    card_pair (by decide)]
  exact Nat.mul_dvd_mul_iff_left two_pos

/-- Zelinsky's Lemma 6: if `2 τ(d) ∣ d` and `p` is a prime not dividing `d`, then `d p` is
refactorable. -/
theorem refactorable_mul_prime {d p : ℕ} (hd : 2 * d.divisors.card ∣ d) (hp : p.Prime)
    (hpd : ¬ p ∣ d) : (d * p).divisors.card ∣ d * p := by
  rw [Nat.Coprime.card_divisors_mul (hp.coprime_iff_not_dvd.mpr hpd).symm, hp.divisors,
    card_pair hp.one_lt.ne, mul_comm _ 2]
  exact hd.mul_right p

/-- `#{p prime : x < p ≤ y} = π(y) - π(x)` (truncated subtraction). -/
theorem card_filter_prime_Ioc (x y : ℕ) :
    ((Ioc x y).filter Nat.Prime).card = Nat.primeCounting y - Nat.primeCounting x := by
  rcases le_total y x with hyx | hxy
  · rw [Ioc_eq_empty_of_le hyx, filter_empty, card_empty,
      Nat.sub_eq_zero_of_le (Nat.monotone_primeCounting hyx)]
  · have hsplit : (range (y + 1)).filter Nat.Prime =
        (range (x + 1)).filter Nat.Prime ∪ (Ioc x y).filter Nat.Prime := by
      ext q
      by_cases hq : q.Prime <;> simp [hq]
      omega
    have hdisj : Disjoint ((range (x + 1)).filter Nat.Prime) ((Ioc x y).filter Nat.Prime) := by
      rw [disjoint_left]
      intro q h1 h2
      simp only [mem_filter, mem_range, mem_Ioc] at h1 h2
      omega
    rw [← primesLE_card_eq_primeCounting, ← primesLE_card_eq_primeCounting,
      primesLE_eq_filter_range, primesLE_eq_filter_range, hsplit, card_union_of_disjoint hdisj]
    omega

/-- Zelinsky's families: for a set `G` of `p`-generators (`2 τ(d) ∣ d`) and bounds `P d` for the
prime factors of each `d ∈ G`, the products `d p` with `p` prime and `P d < p ≤ x / d` are
pairwise distinct refactorable numbers `≤ x` (the largest prime factor of `d p` is `p`). -/
theorem sum_card_primes_le_count (G : Finset ℕ) (P : ℕ → ℕ)
    (hG : ∀ d ∈ G, 0 < d ∧ 2 * d.divisors.card ∣ d)
    (hP : ∀ d ∈ G, ∀ q, q.Prime → q ∣ d → q ≤ P d) (x : ℕ) :
    ∑ d ∈ G, ((Ioc (P d) (x / d)).filter Nat.Prime).card ≤ countRefactorableNat x := by
  rw [← card_sigma, countRefactorableNat]
  refine card_le_card_of_injOn (fun s => s.1 * s.2) ?_ ?_
  · rintro ⟨d, p⟩ hs
    simp only [mem_coe, mem_sigma, mem_filter, mem_Ioc] at hs
    obtain ⟨hd, ⟨hPp, hpx⟩, hp⟩ := hs
    obtain ⟨hd0, hgen⟩ := hG d hd
    have hpd : ¬ p ∣ d := fun h => (hP d hd p hp h).not_gt hPp
    have hdp : p * d ≤ x := (Nat.le_div_iff_mul_le hd0).mp hpx
    simp only [mem_coe, mem_filter, mem_Icc]
    exact ⟨⟨Nat.mul_pos hd0 hp.pos, by rw [mul_comm]; exact hdp⟩,
      refactorable_mul_prime hgen hp hpd⟩
  · rintro ⟨d, p⟩ hs ⟨d', p'⟩ hs' heq
    simp only [mem_coe, mem_sigma, mem_filter, mem_Ioc] at hs hs'
    obtain ⟨hd, ⟨hPp, -⟩, hp⟩ := hs
    obtain ⟨hd', ⟨hPp', -⟩, hp'⟩ := hs'
    simp only at heq
    have key : p = p' := by
      by_contra hne
      have h1 : p ∣ d' := by
        rcases (Nat.Prime.dvd_mul hp).mp (heq ▸ dvd_mul_left p d) with h | h
        · exact h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hp').mp h) hne
      have h2 : p' ∣ d := by
        rcases (Nat.Prime.dvd_mul hp').mp (heq.symm ▸ dvd_mul_left p' d') with h | h
        · exact h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp' hp).mp h).symm hne
      have := hP d' hd' p hp h1
      have := hP d hd p' hp' h2
      omega
    subst key
    obtain rfl : d = d' := Nat.eq_of_mul_eq_mul_right hp.pos heq
    rfl

/-- The lower bound behind the analytic tail, `T(x) ≥ ∑_{d ∈ G} (π(x / d) - π(P d))`
(truncated subtraction), for `p`-generators `d ∈ G` whose prime factors are `≤ P d`. -/
theorem sum_primeCounting_sub_le (G : Finset ℕ) (P : ℕ → ℕ)
    (hG : ∀ d ∈ G, 0 < d ∧ 2 * d.divisors.card ∣ d)
    (hP : ∀ d ∈ G, ∀ q, q.Prime → q ∣ d → q ≤ P d) (x : ℕ) :
    ∑ d ∈ G, (Nat.primeCounting (x / d) - Nat.primeCounting (P d)) ≤
      countRefactorableNat x := by
  simpa only [card_filter_prime_Ioc] using sum_card_primes_le_count G P hG hP x

end AgenticConjectures.OeisA111291
