import Mathlib

/-!
# Erdős problem 307 — forcing identities and local necessary conditions

The upstream FormalConjectures statement `Erdos307.erdos_307` (snapshot in
`problems/erdos-307/upstream/307.lean`) asks whether there are finite sets of primes `P`, `Q`
with `1 = (∑ p ∈ P, 1/p) * (∑ q ∈ Q, 1/q)`.  It is `answer(sorry)`-backed and the problem is
open; nothing here decides it.

`statement` is, verbatim, the right-hand side of the upstream `iff` (the same `Finset ℕ`
witnesses, `Nat.Prime` hypotheses and equation in `ℚ`), and `IsSolution P Q` is the body of its
existential.  With `M S = ∏ p ∈ S, p` and `A S = ∑ p ∈ S, ∏ q ∈ S.erase p, q` (so
`∑ p ∈ S, 1/p = A S / M S` for a set of positive integers) this module proves, for every
witness `P`, `Q`:

* the forcing identities `A P = M Q` and `A Q = M P`, and their converse, so the upstream
  existential is equivalent to the existence of a forcing pair (`statement_iff_forcing`);
* `P` and `Q` are disjoint, `A (P ∪ Q) = M P ^ 2 + M Q ^ 2`, and `2 < ∑ r ∈ P ∪ Q, 1/r`;
* the local square condition: for every `r ∈ P ∪ Q` the product of the other primes is a nonzero
  square modulo `r`; equivalently the Jacobi (here Legendre) symbols `J(s | r)`,
  `s ∈ (P ∪ Q).erase r`, multiply to `1`, i.e. an even number of them equal `-1`.  This is the
  pruning rule of the search programs in `problems/erdos-307`.  At `r = 2` it is vacuous;
* congruences modulo any `m` in which all relevant primes square to `1`, specialised to the
  mod-8 and mod-24 conditions of `PROOF.md` and to the parity of `#P` and `#Q`;
* `59 ≤ #(P ∪ Q)` (`card_union_ge_59`), the left conjunct of the upstream
  `erdos_307.barrier`, by a kernel-checked argument: `decide` on explicit natural-number
  computations, no `native_decide`.  Upstream also assumes `Q.Nonempty`, which follows from
  the equation; its right conjunct (a lower bound for `∏ P`) is not treated here.

The computational bounds of `problems/erdos-307` (`#(P ∪ Q) ≥ 60` and the lower bounds on
`max (P ∪ Q)`) and the aggregate quadratic-reciprocity conditions of `PROOF.md` §3 are not
formalized here.
-/

namespace AgenticConjectures.Erdos307

/-- The open statement: verbatim the right-hand side of upstream `Erdos307.erdos_307`.  It is
not decided here. -/
def statement : Prop :=
  ∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)

/-- The body of the upstream existential in `Erdos307.erdos_307`. -/
def IsSolution (P Q : Finset ℕ) : Prop :=
  (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧
    1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)

/-- Product of the elements of a finite set. -/
def M (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- Numerator of `∑ p ∈ S, 1/p` over the denominator `M S`. -/
def A (S : Finset ℕ) : ℕ := ∑ p ∈ S, ∏ q ∈ S.erase p, q

theorem IsSolution.symm {P Q : Finset ℕ} (h : IsSolution P Q) : IsSolution Q P :=
  ⟨h.2.1, h.1, by rw [mul_comm]; exact h.2.2⟩

theorem prime_of_mem {P Q : Finset ℕ} (h : IsSolution P Q) {s : ℕ} (hs : s ∈ P ∪ Q) :
    s.Prime :=
  (Finset.mem_union.mp hs).elim (h.1 s) (h.2.1 s)

/-! ### Arithmetic of `A` and `M` -/

theorem M_pos {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) : 0 < M S :=
  Finset.prod_pos hS

theorem sum_inv_eq {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) :
    ∑ p ∈ S, (p : ℚ)⁻¹ = (A S : ℚ) / (M S : ℚ) := by
  have hM : (M S : ℚ) ≠ 0 := by exact_mod_cast (M_pos hS).ne'
  rw [eq_div_iff hM, Finset.sum_mul]
  unfold A
  push_cast
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hS p hp).ne'
  unfold M
  push_cast
  rw [← Finset.mul_prod_erase S (fun q => (q : ℚ)) hp, ← mul_assoc, inv_mul_cancel₀ hp0,
    one_mul]

theorem A_cast_eq {S : Finset ℕ} {r : ℕ} (hr : r ∈ S) :
    (A S : ZMod r) = ∏ q ∈ S.erase r, (q : ZMod r) := by
  unfold A
  push_cast
  refine Finset.sum_eq_single r (fun p _ hpr => ?_) (fun h => absurd hr h)
  have hrp : r ∈ S.erase p := Finset.mem_erase.mpr ⟨fun h => hpr h.symm, hr⟩
  rw [← Finset.mul_prod_erase _ (fun q : ℕ => (q : ZMod r)) hrp]
  simp

theorem prime_not_dvd_prod_erase {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {r : ℕ}
    (hr : r ∈ S) : ¬ r ∣ ∏ q ∈ S.erase r, q := by
  intro h
  obtain ⟨q, hq, hrq⟩ := (Prime.dvd_finsetProd_iff (hS r hr).prime (fun q => q)).mp h
  have := (Nat.prime_dvd_prime_iff_eq (hS r hr) (hS q (Finset.mem_of_mem_erase hq))).mp hrq
  exact Finset.ne_of_mem_erase hq this.symm

theorem prime_not_dvd_A {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {r : ℕ} (hr : r ∈ S) :
    ¬ r ∣ A S := by
  intro h
  apply prime_not_dvd_prod_erase hS hr
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rw [A_cast_eq hr] at h
  push_cast
  exact h

theorem coprime_A_M {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) : Nat.Coprime (A S) (M S) := by
  unfold M
  rw [Nat.coprime_prod_right_iff]
  intro r hr
  exact ((Nat.Prime.coprime_iff_not_dvd (hS r hr)).mpr (prime_not_dvd_A hS hr)).symm

theorem A_union {P Q : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q)
    (hd : Disjoint P Q) : A (P ∪ Q) = A P * M Q + A Q * M P := by
  have hU : ∀ r ∈ P ∪ Q, 0 < r := fun r hr => (Finset.mem_union.mp hr).elim (hP r) (hQ r)
  have hMP : (M P : ℚ) ≠ 0 := by exact_mod_cast (M_pos hP).ne'
  have hMQ : (M Q : ℚ) ≠ 0 := by exact_mod_cast (M_pos hQ).ne'
  have h := sum_inv_eq hU
  rw [Finset.sum_union hd, sum_inv_eq hP, sum_inv_eq hQ,
    show M (P ∪ Q) = M P * M Q from Finset.prod_union hd, Nat.cast_mul,
    eq_div_iff (mul_ne_zero hMP hMQ)] at h
  have h' : (A (P ∪ Q) : ℚ) = A P * M Q + A Q * M P := by
    rw [← h, div_add_div _ _ hMP hMQ, div_mul_cancel₀ _ (mul_ne_zero hMP hMQ)]
    ring
  exact_mod_cast h'

theorem A_insert {S : Finset ℕ} {a : ℕ} (ha : a ∉ S) : A (insert a S) = M S + a * A S := by
  unfold A M
  rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hap : a ≠ p := fun h => ha (h ▸ hp)
  rw [Finset.erase_insert_of_ne hap,
    Finset.prod_insert fun h => ha (Finset.mem_of_mem_erase h)]

/-! ### The forcing identities -/

/-- Forcing: every solution satisfies `A P = M Q` and `A Q = M P`. -/
theorem forcing {P Q : Finset ℕ} (h : IsSolution P Q) : A P = M Q ∧ A Q = M P := by
  obtain ⟨hP, hQ, h1⟩ := h
  have hP0 : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  have hQ0 : ∀ q ∈ Q, 0 < q := fun q hq => (hQ q hq).pos
  have hMP := M_pos hP0
  have hMQ : (M Q : ℚ) ≠ 0 := by exact_mod_cast (M_pos hQ0).ne'
  have hMP' : (M P : ℚ) ≠ 0 := by exact_mod_cast hMP.ne'
  have key : M P * M Q = A P * A Q := by
    rw [sum_inv_eq hP0, sum_inv_eq hQ0, div_mul_div_comm, eq_div_iff (mul_ne_zero hMP' hMQ),
      one_mul] at h1
    exact_mod_cast h1
  have d1 : A Q ∣ M P := (coprime_A_M hQ).dvd_of_dvd_mul_right ⟨A P, by rw [key, mul_comm]⟩
  have d2 : M P ∣ A Q := (coprime_A_M hP).symm.dvd_of_dvd_mul_left ⟨M Q, key.symm⟩
  have e2 : A Q = M P := Nat.dvd_antisymm d1 d2
  refine ⟨?_, e2⟩
  rw [e2, mul_comm (A P)] at key
  exact (Nat.eq_of_mul_eq_mul_left hMP key).symm

/-- Converse of `forcing`. -/
theorem isSolution_of_forcing {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (h1 : A P = M Q) (h2 : A Q = M P) : IsSolution P Q := by
  refine ⟨hP, hQ, ?_⟩
  have hP0 : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  have hQ0 : ∀ q ∈ Q, 0 < q := fun q hq => (hQ q hq).pos
  have hMP : (M P : ℚ) ≠ 0 := by exact_mod_cast (M_pos hP0).ne'
  have hMQ : (M Q : ℚ) ≠ 0 := by exact_mod_cast (M_pos hQ0).ne'
  rw [sum_inv_eq hP0, sum_inv_eq hQ0, h1, h2, div_mul_div_comm, mul_comm (M Q : ℚ),
    div_self (mul_ne_zero hMP hMQ)]

/-- The upstream existential is equivalent to the existence of a forcing pair. -/
theorem statement_iff_forcing :
    statement ↔
      ∃ P Q : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ (∀ q ∈ Q, q.Prime) ∧ A P = M Q ∧ A Q = M P := by
  unfold statement
  constructor
  · rintro ⟨P, Q, h⟩
    exact ⟨P, Q, h.1, h.2.1, forcing h⟩
  · rintro ⟨P, Q, hP, hQ, h1, h2⟩
    exact ⟨P, Q, isSolution_of_forcing hP hQ h1 h2⟩

theorem disjoint_of_isSolution {P Q : Finset ℕ} (h : IsSolution P Q) : Disjoint P Q := by
  rw [Finset.disjoint_left]
  intro r hrP hrQ
  apply prime_not_dvd_A h.1 hrP
  rw [(forcing h).1]
  exact Finset.dvd_prod_of_mem (fun q => q) hrQ

/-- The union identity `A (P ∪ Q) = M P ^ 2 + M Q ^ 2`. -/
theorem union_identity {P Q : Finset ℕ} (h : IsSolution P Q) :
    A (P ∪ Q) = M P ^ 2 + M Q ^ 2 := by
  obtain ⟨e1, e2⟩ := forcing h
  rw [A_union (fun p hp => (h.1 p hp).pos) (fun q hq => (h.2.1 q hq).pos)
    (disjoint_of_isSolution h), e1, e2]
  ring

/-- The reciprocal sum over `P ∪ Q` exceeds `2` (AM-GM, strict since `∑ 1/p ≠ 1`). -/
theorem two_lt_sum_inv_union {P Q : Finset ℕ} (h : IsSolution P Q) :
    2 < ∑ r ∈ P ∪ Q, (r : ℚ)⁻¹ := by
  rw [Finset.sum_union (disjoint_of_isSolution h)]
  obtain ⟨hP, hQ, h1⟩ := h
  have ha : 0 ≤ ∑ p ∈ P, (p : ℚ)⁻¹ := Finset.sum_nonneg fun p _ => by positivity
  have ha1 : ∑ p ∈ P, (p : ℚ)⁻¹ ≠ 1 := by
    intro ha1
    have hP0 : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
    have hM : (M P : ℚ) ≠ 0 := by exact_mod_cast (M_pos hP0).ne'
    rw [sum_inv_eq hP0, div_eq_one_iff_eq hM] at ha1
    have hAM : A P = M P := by exact_mod_cast ha1
    obtain ⟨p, hp⟩ : P.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp [A, M] at hAM
    have hpA : p ∣ A P := by
      rw [hAM]
      exact Finset.dvd_prod_of_mem (fun q => q) hp
    exact prime_not_dvd_A hP hp hpA
  have hsq : 0 < (∑ p ∈ P, (p : ℚ)⁻¹ - 1) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr ha1)))
  by_contra hle
  nlinarith [mul_nonneg ha (sub_nonneg.mpr (not_lt.mp hle))]

/-! ### The local square (Legendre) condition -/

/-- For every `r ∈ P ∪ Q`, the product of the other elements is a nonzero square mod `r`. -/
theorem isSquare_prod_erase {P Q : Finset ℕ} (h : IsSolution P Q) {r : ℕ} (hr : r ∈ P ∪ Q) :
    IsSquare (∏ s ∈ (P ∪ Q).erase r, (s : ZMod r)) ∧
      ∏ s ∈ (P ∪ Q).erase r, (s : ZMod r) ≠ 0 := by
  have hU : ∀ s ∈ P ∪ Q, s.Prime := fun s hs => prime_of_mem h hs
  refine ⟨?_, ?_⟩
  · have hc := A_cast_eq (S := P ∪ Q) hr
    rw [union_identity h] at hc
    push_cast at hc
    rcases Finset.mem_union.mp hr with hrP | hrQ
    · have h0 : (M P : ZMod r) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.dvd_prod_of_mem (fun q => q) hrP)
      rw [h0] at hc
      exact ⟨(M Q : ZMod r), by rw [← hc]; ring⟩
    · have h0 : (M Q : ZMod r) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.dvd_prod_of_mem (fun q => q) hrQ)
      rw [h0] at hc
      exact ⟨(M P : ZMod r), by rw [← hc]; ring⟩
  · intro h0
    apply prime_not_dvd_prod_erase hU hr
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact h0

/-- The symbols `J(s | r)` over `s ∈ (P ∪ Q).erase r` multiply to `1`. -/
theorem prod_jacobiSym_eq_one {P Q : Finset ℕ} (h : IsSolution P Q) {r : ℕ}
    (hr : r ∈ P ∪ Q) : ∏ s ∈ (P ∪ Q).erase r, jacobiSym s r = 1 := by
  obtain ⟨hsq, hne⟩ := isSquare_prod_erase h hr
  haveI := Fact.mk (prime_of_mem h hr)
  have hcast : ((∏ s ∈ (P ∪ Q).erase r, (s : ℤ) : ℤ) : ZMod r) =
      ∏ s ∈ (P ∪ Q).erase r, (s : ZMod r) := by
    push_cast
    rfl
  calc ∏ s ∈ (P ∪ Q).erase r, jacobiSym s r
      = ∏ s ∈ (P ∪ Q).erase r, legendreSym.hom r s :=
        Finset.prod_congr rfl fun s _ => (jacobiSym.legendreSym.to_jacobiSym r s).symm
    _ = legendreSym r (∏ s ∈ (P ∪ Q).erase r, (s : ℤ)) :=
        (map_prod (legendreSym.hom r) _ _).symm
    _ = 1 := (legendreSym.eq_one_iff r (by rw [hcast]; exact hne)).mpr (by rw [hcast]; exact hsq)

/-- The pruning rule of the searches: for every `r ∈ P ∪ Q`, an even number of the other
elements are quadratic non-residues modulo `r`. -/
theorem even_card_nonresidues {P Q : Finset ℕ} (h : IsSolution P Q) {r : ℕ}
    (hr : r ∈ P ∪ Q) :
    Even (((P ∪ Q).erase r).filter (fun s : ℕ => jacobiSym s r = -1)).card := by
  have hpm : ∀ s ∈ (P ∪ Q).erase r, jacobiSym s r = 1 ∨ jacobiSym s r = -1 := by
    intro s hs
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes (prime_of_mem h (Finset.mem_of_mem_erase hs))
      (prime_of_mem h hr)).mpr (Finset.ne_of_mem_erase hs)
  have h1 : ∏ s ∈ ((P ∪ Q).erase r).filter (fun s : ℕ => jacobiSym s r = -1), jacobiSym s r =
      (-1) ^ (((P ∪ Q).erase r).filter (fun s : ℕ => jacobiSym s r = -1)).card :=
    Finset.prod_eq_pow_card fun s hs => (Finset.mem_filter.mp hs).2
  have h2 : ∏ s ∈ ((P ∪ Q).erase r).filter (fun s : ℕ => ¬ jacobiSym s r = -1), jacobiSym s r =
      1 :=
    Finset.prod_eq_one fun s hs =>
      (hpm s (Finset.mem_filter.mp hs).1).resolve_right (Finset.mem_filter.mp hs).2
  have hprod := prod_jacobiSym_eq_one h hr
  rw [← Finset.prod_filter_mul_prod_filter_not ((P ∪ Q).erase r)
    (fun s : ℕ => jacobiSym s r = -1), h1, h2, mul_one] at hprod
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hprod

/-! ### Congruences modulo `m` -/

theorem M_cast_sq {m : ℕ} {S : Finset ℕ} (hS : ∀ s ∈ S, (s : ZMod m) ^ 2 = 1) :
    (M S : ZMod m) ^ 2 = 1 := by
  unfold M
  push_cast
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one hS

/-- If every element of `S` squares to `1` modulo `m`, then `A S ≡ M S · ∑ S (mod m)`. -/
theorem A_cast_eq_mul_sum {m : ℕ} {S : Finset ℕ} (hS : ∀ s ∈ S, (s : ZMod m) ^ 2 = 1) :
    (A S : ZMod m) = M S * ∑ s ∈ S, (s : ZMod m) := by
  unfold A
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  unfold M
  push_cast
  rw [← Finset.mul_prod_erase S (fun q => (q : ZMod m)) hp]
  linear_combination (-(∏ q ∈ S.erase p, (q : ZMod m))) * hS p hp

/-- `PROOF.md` (8a), (8b) for a general modulus: if all elements of `P ∪ Q` square to `1`
modulo `m`, then `∑ P ≡ ∑ Q ≡ M (P ∪ Q)` and `∑ (P ∪ Q) ≡ 2 M (P ∪ Q)`. -/
theorem sum_cast_eq_M {P Q : Finset ℕ} (h : IsSolution P Q) {m : ℕ}
    (hU : ∀ s ∈ P ∪ Q, (s : ZMod m) ^ 2 = 1) :
    ∑ p ∈ P, (p : ZMod m) = M (P ∪ Q) ∧ ∑ q ∈ Q, (q : ZMod m) = M (P ∪ Q) ∧
      ∑ s ∈ P ∪ Q, (s : ZMod m) = 2 * M (P ∪ Q) := by
  have hd := disjoint_of_isSolution h
  obtain ⟨e1, e2⟩ := forcing h
  have hP : ∀ s ∈ P, (s : ZMod m) ^ 2 = 1 := fun s hs => hU s (Finset.mem_union_left _ hs)
  have hQ : ∀ s ∈ Q, (s : ZMod m) ^ 2 = 1 := fun s hs => hU s (Finset.mem_union_right _ hs)
  have hMU : (M (P ∪ Q) : ZMod m) = M P * M Q := by
    rw [show M (P ∪ Q) = M P * M Q from Finset.prod_union hd, Nat.cast_mul]
  have a1 := A_cast_eq_mul_sum hP
  have a2 := A_cast_eq_mul_sum hQ
  rw [e1] at a1
  rw [e2] at a2
  have sP : ∑ p ∈ P, (p : ZMod m) = M (P ∪ Q) := by
    rw [hMU]
    linear_combination (-(∑ p ∈ P, (p : ZMod m))) * M_cast_sq hP - (M P : ZMod m) * a1
  have sQ : ∑ q ∈ Q, (q : ZMod m) = M (P ∪ Q) := by
    rw [hMU]
    linear_combination (-(∑ q ∈ Q, (q : ZMod m))) * M_cast_sq hQ - (M Q : ZMod m) * a2
  refine ⟨sP, sQ, ?_⟩
  rw [Finset.sum_union hd, sP, sQ]
  ring

/-- `PROOF.md` (8c), (8d) for a general modulus, when `2 ∈ P`: with `T = M ((P ∪ Q).erase 2)`,
`1 + 2 ∑ (P.erase 2) ≡ T`, `∑ Q ≡ 2T` and `1 + 2 ∑ ((P ∪ Q).erase 2) ≡ 5T`. -/
theorem sum_cast_eq_of_two_mem {P Q : Finset ℕ} (h : IsSolution P Q) (h2 : 2 ∈ P) {m : ℕ}
    (hU : ∀ s ∈ (P ∪ Q).erase 2, (s : ZMod m) ^ 2 = 1) :
    1 + 2 * ∑ p ∈ P.erase 2, (p : ZMod m) = M ((P ∪ Q).erase 2) ∧
      ∑ q ∈ Q, (q : ZMod m) = 2 * M ((P ∪ Q).erase 2) ∧
      1 + 2 * ∑ s ∈ (P ∪ Q).erase 2, (s : ZMod m) = 5 * M ((P ∪ Q).erase 2) := by
  have hd := disjoint_of_isSolution h
  obtain ⟨e1, e2⟩ := forcing h
  have h2Q : 2 ∉ Q := Finset.disjoint_left.mp hd h2
  have hE : (P ∪ Q).erase 2 = P.erase 2 ∪ Q := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_union]
    constructor
    · rintro ⟨hx, hxP | hxQ⟩
      · exact Or.inl ⟨hx, hxP⟩
      · exact Or.inr hxQ
    · rintro (⟨hx, hxP⟩ | hxQ)
      · exact ⟨hx, Or.inl hxP⟩
      · exact ⟨fun hx => h2Q (hx ▸ hxQ), Or.inr hxQ⟩
  have hd' : Disjoint (P.erase 2) Q :=
    Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd
  rw [hE] at hU ⊢
  have hP0 : ∀ s ∈ P.erase 2, (s : ZMod m) ^ 2 = 1 :=
    fun s hs => hU s (Finset.mem_union_left _ hs)
  have hQ : ∀ s ∈ Q, (s : ZMod m) ^ 2 = 1 := fun s hs => hU s (Finset.mem_union_right _ hs)
  have hT : (M (P.erase 2 ∪ Q) : ZMod m) = M (P.erase 2) * M Q := by
    rw [show M (P.erase 2 ∪ Q) = M (P.erase 2) * M Q from Finset.prod_union hd', Nat.cast_mul]
  have hMP : M P = 2 * M (P.erase 2) := (Finset.mul_prod_erase P (fun p => p) h2).symm
  have hAP : A P = M (P.erase 2) + 2 * A (P.erase 2) := by
    have := A_insert (Finset.notMem_erase 2 P)
    rwa [Finset.insert_erase h2] at this
  have c1 : (M Q : ZMod m) = M (P.erase 2) + 2 * (A (P.erase 2) : ZMod m) := by
    rw [← e1, hAP]
    push_cast
    ring
  have c2 : (A Q : ZMod m) = 2 * M (P.erase 2) := by
    rw [e2, hMP]
    push_cast
    ring
  have a0 := A_cast_eq_mul_sum hP0
  have aQ := A_cast_eq_mul_sum hQ
  have r1 : 1 + 2 * ∑ p ∈ P.erase 2, (p : ZMod m) = M (P.erase 2 ∪ Q) := by
    rw [hT]
    linear_combination (-(1 + 2 * ∑ p ∈ P.erase 2, (p : ZMod m))) * M_cast_sq hP0 -
      (M (P.erase 2) : ZMod m) * c1 - 2 * (M (P.erase 2) : ZMod m) * a0
  have r2 : ∑ q ∈ Q, (q : ZMod m) = 2 * M (P.erase 2 ∪ Q) := by
    rw [hT]
    linear_combination (-(∑ q ∈ Q, (q : ZMod m))) * M_cast_sq hQ - (M Q : ZMod m) * aQ +
      (M Q : ZMod m) * c2
  refine ⟨r1, r2, ?_⟩
  rw [Finset.sum_union hd']
  linear_combination r1 + 2 * r2

/-! ### The concrete moduli 2, 8 and 24 -/

theorem sq_cast_eq_one_eight {s : ℕ} (hs : Odd s) : (s : ZMod 8) ^ 2 = 1 := by
  have key : ∀ x : ZMod 8, x.val % 2 = 1 → x ^ 2 = 1 := by decide
  apply key
  rw [ZMod.val_natCast]
  have := Nat.odd_iff.mp hs
  omega

theorem sq_cast_eq_one_twentyFour {s : ℕ} (hs : s.Prime) (h2 : s ≠ 2) (h3 : s ≠ 3) :
    (s : ZMod 24) ^ 2 = 1 := by
  have key : ∀ x : ZMod 24, x.val % 2 = 1 → x.val % 3 ≠ 0 → x ^ 2 = 1 := by decide
  have o2 := Nat.odd_iff.mp (hs.odd_of_ne_two h2)
  have o3 : s % 3 ≠ 0 := fun h0 =>
    h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).mp (Nat.dvd_of_mod_eq_zero h0)).symm
  apply key <;> rw [ZMod.val_natCast] <;> omega

/-- Mod-8 conditions (8a), (8b) when `2 ∉ P ∪ Q`. -/
theorem mod_eight {P Q : Finset ℕ} (h : IsSolution P Q) (h2 : 2 ∉ P ∪ Q) :
    ∑ p ∈ P, (p : ZMod 8) = M (P ∪ Q) ∧ ∑ q ∈ Q, (q : ZMod 8) = M (P ∪ Q) ∧
      ∑ s ∈ P ∪ Q, (s : ZMod 8) = 2 * M (P ∪ Q) :=
  sum_cast_eq_M h fun _ hs =>
    sq_cast_eq_one_eight ((prime_of_mem h hs).odd_of_ne_two fun e => h2 (e ▸ hs))

/-- Mod-8 conditions (8c), (8d) when `2 ∈ P` (apply to `h.symm` when `2 ∈ Q`). -/
theorem mod_eight_of_two_mem {P Q : Finset ℕ} (h : IsSolution P Q) (h2 : 2 ∈ P) :
    1 + 2 * ∑ p ∈ P.erase 2, (p : ZMod 8) = M ((P ∪ Q).erase 2) ∧
      ∑ q ∈ Q, (q : ZMod 8) = 2 * M ((P ∪ Q).erase 2) ∧
      1 + 2 * ∑ s ∈ (P ∪ Q).erase 2, (s : ZMod 8) = 5 * M ((P ∪ Q).erase 2) :=
  sum_cast_eq_of_two_mem h h2 fun _ hs =>
    sq_cast_eq_one_eight ((prime_of_mem h (Finset.mem_of_mem_erase hs)).odd_of_ne_two
      (Finset.ne_of_mem_erase hs))

/-- Mod-24 conditions when `2, 3 ∉ P ∪ Q`. -/
theorem mod_twentyFour {P Q : Finset ℕ} (h : IsSolution P Q) (h2 : 2 ∉ P ∪ Q)
    (h3 : 3 ∉ P ∪ Q) :
    ∑ p ∈ P, (p : ZMod 24) = M (P ∪ Q) ∧ ∑ q ∈ Q, (q : ZMod 24) = M (P ∪ Q) ∧
      ∑ s ∈ P ∪ Q, (s : ZMod 24) = 2 * M (P ∪ Q) :=
  sum_cast_eq_M h fun _ hs =>
    sq_cast_eq_one_twentyFour (prime_of_mem h hs) (fun e => h2 (e ▸ hs)) (fun e => h3 (e ▸ hs))

/-- Mod-24 conditions when `2 ∈ P` and `3 ∉ P ∪ Q`. -/
theorem mod_twentyFour_of_two_mem {P Q : Finset ℕ} (h : IsSolution P Q) (h2 : 2 ∈ P)
    (h3 : 3 ∉ P ∪ Q) :
    1 + 2 * ∑ p ∈ P.erase 2, (p : ZMod 24) = M ((P ∪ Q).erase 2) ∧
      ∑ q ∈ Q, (q : ZMod 24) = 2 * M ((P ∪ Q).erase 2) ∧
      1 + 2 * ∑ s ∈ (P ∪ Q).erase 2, (s : ZMod 24) = 5 * M ((P ∪ Q).erase 2) :=
  sum_cast_eq_of_two_mem h h2 fun _ hs =>
    sq_cast_eq_one_twentyFour (prime_of_mem h (Finset.mem_of_mem_erase hs))
      (Finset.ne_of_mem_erase hs) (fun e => h3 (e ▸ Finset.mem_of_mem_erase hs))

/-- Parity: if `2 ∉ P ∪ Q` then `#P` and `#Q` are odd. -/
theorem odd_card_of_two_not_mem {P Q : Finset ℕ} (h : IsSolution P Q) (h2 : 2 ∉ P ∪ Q) :
    Odd P.card ∧ Odd Q.card := by
  have hU : ∀ s ∈ P ∪ Q, (s : ZMod 2) = 1 := fun s hs =>
    ZMod.natCast_eq_one_iff_odd.mpr ((prime_of_mem h hs).odd_of_ne_two fun e => h2 (e ▸ hs))
  obtain ⟨e1, e2, -⟩ := sum_cast_eq_M h fun s hs => by rw [hU s hs, one_pow]
  have hM : (M (P ∪ Q) : ZMod 2) = 1 := by
    unfold M
    push_cast
    exact Finset.prod_eq_one hU
  rw [Finset.sum_eq_card_nsmul fun s hs => hU s (Finset.mem_union_left Q hs), nsmul_eq_mul,
    mul_one, hM] at e1
  rw [Finset.sum_eq_card_nsmul fun s hs => hU s (Finset.mem_union_right P hs), nsmul_eq_mul,
    mul_one, hM] at e2
  exact ⟨ZMod.natCast_eq_one_iff_odd.mp e1, ZMod.natCast_eq_one_iff_odd.mp e2⟩

/-- Parity: if `2 ∈ P` then `#Q` is even. -/
theorem even_card_of_two_mem {P Q : Finset ℕ} (h : IsSolution P Q) (h2 : 2 ∈ P) :
    Even Q.card := by
  have h2Q : 2 ∉ Q := Finset.disjoint_left.mp (disjoint_of_isSolution h) h2
  have hU : ∀ s ∈ (P ∪ Q).erase 2, (s : ZMod 2) = 1 := fun s hs =>
    ZMod.natCast_eq_one_iff_odd.mpr ((prime_of_mem h (Finset.mem_of_mem_erase hs)).odd_of_ne_two
      (Finset.ne_of_mem_erase hs))
  obtain ⟨-, e2, -⟩ := sum_cast_eq_of_two_mem h h2 fun s hs => by rw [hU s hs, one_pow]
  have hQ : ∀ s ∈ Q, (s : ZMod 2) = 1 := fun s hs =>
    hU s (Finset.mem_erase.mpr ⟨fun e => h2Q (e ▸ hs), Finset.mem_union_right P hs⟩)
  rw [Finset.sum_eq_card_nsmul hQ, nsmul_eq_mul, mul_one,
    show (2 : ZMod 2) = 0 by decide, zero_mul] at e2
  exact ZMod.natCast_eq_zero_iff_even.mp e2

/-! ### At least 59 primes -/

/-- The first 58 primes. -/
def first58 : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
    191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271}

theorem card_first58 : first58.card = 58 := by decide +kernel

theorem bounds_first58 : ∀ l ∈ first58, 2 ≤ l ∧ l ≤ 271 := by decide +kernel

theorem mem_first58_of_prime {p : ℕ} (hp : p.Prime) (h : p ≤ 271) : p ∈ first58 := by
  have key : ∀ n < 272, n.Prime → n ∈ first58 := by decide +kernel
  exact key p (by omega) hp

/-- `∑_{i ≤ 58} 1/p_i < 2`, checked by `decide` as `A first58 < 2 * M first58`. -/
theorem sum_inv_first58_lt_two : ∑ p ∈ first58, (p : ℚ)⁻¹ < 2 := by
  have hpos : ∀ p ∈ first58, 0 < p := fun p hp => by have := (bounds_first58 p hp).1; omega
  have key : A first58 < 2 * M first58 := by decide +kernel
  rw [sum_inv_eq hpos, div_lt_iff₀ (by exact_mod_cast M_pos hpos)]
  exact_mod_cast key

/-- A set of at most 58 primes has reciprocal sum at most that of the first 58 primes. -/
theorem sum_inv_le_first58 {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 58) :
    ∑ p ∈ S, (p : ℚ)⁻¹ ≤ ∑ p ∈ first58, (p : ℚ)⁻¹ := by
  have hcard' : (S \ first58).card ≤ (first58 \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S first58
    have h2 := Finset.card_sdiff_add_card_inter first58 S
    rw [Finset.inter_comm, card_first58] at h2
    omega
  rw [← Finset.sum_inter_add_sum_diff S first58, ← Finset.sum_inter_add_sum_diff first58 S,
    Finset.inter_comm first58 S]
  refine add_le_add le_rfl ?_
  calc ∑ p ∈ S \ first58, (p : ℚ)⁻¹ ≤ ∑ _p ∈ S \ first58, (271 : ℚ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpS, hpL⟩ := Finset.mem_sdiff.mp hp
        have h271 : 271 < p := by
          by_contra hle
          exact hpL (mem_first58_of_prime (hS p hpS) (not_lt.mp hle))
        exact inv_anti₀ (by norm_num) (by exact_mod_cast h271.le)
    _ = (S \ first58).card * (271 : ℚ)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (first58 \ S).card * (271 : ℚ)⁻¹ := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard') (by norm_num)
    _ = ∑ _p ∈ first58 \ S, (271 : ℚ)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ first58 \ S, (p : ℚ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨h2, h271⟩ := bounds_first58 p (Finset.mem_sdiff.mp hp).1
        exact inv_anti₀ (by exact_mod_cast (show 0 < p by omega)) (by exact_mod_cast h271)

/-- Left conjunct of the upstream `erdos_307.barrier`: every solution uses at least 59 primes.
(Upstream also assumes `Q.Nonempty`; that follows from the equation.) -/
theorem card_union_ge_59 {P Q : Finset ℕ} (h : IsSolution P Q) : 59 ≤ (P ∪ Q).card := by
  by_contra hlt
  have h1 := sum_inv_le_first58 (fun s hs => prime_of_mem h hs) (by omega)
  have h2 := two_lt_sum_inv_union h
  have h3 := sum_inv_first58_lt_two
  linarith

end AgenticConjectures.Erdos307
