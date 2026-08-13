import Mathlib

/-!
# Let's Prove Goldbach prize problem 3

The current prize page at <https://www.dimostriamogoldbach.it/en/prizes/>
fixes integers `1 < n₁ < ⋯ < nₖ` and asks for arithmetic functions `f,g`
and finite positive sets `I₂,…,Iₖ` representing the positive integers `y`
which are divisible by none of the `nᵢ` and satisfy `n₁ ∣ y+1`.

The source explicitly allows multiplication, subtraction, modulo, and a finite
number of cases in `f,g`, while imposing only finiteness and positivity on the
sets `Iᵢ`.  Every relevant predicate is periodic modulo
`M = n₂⋯nₖ`.  We encode its one-period residue set in `I₂`, take every
later `Iᵢ` to be the singleton `{1}`, and use the other summands only as a
constant offset.  The theorem below proves the resulting set equality.

The formal statement uses a finite list `ns = [n₂,…,nₖ]`; its nonemptiness
corresponds to the source's use of `n₂`.  Positivity and strict ordering are
irrelevant to the periodic identity except for `n₁ > 1` and all later moduli
being greater than one, so we state exactly those needed hypotheses.
-/

namespace AgenticConjectures.GoldbachPrize3

open scoped BigOperators

/-- The target set from prize problem 3. -/
def TargetSet (n₁ : ℕ) (ns : List ℕ) : Set ℕ :=
  {y | 0 < y ∧ ¬ n₁ ∣ y ∧ n₁ ∣ y + 1 ∧ ∀ n ∈ ns, ¬ n ∣ y}

/-- The product period `n₂⋯nₖ`. -/
def period (ns : List ℕ) : ℕ := ns.prod

/-- The positive representative in `1,…,M` of the residue class of `q`
modulo the positive period `M`. -/
def residue (M q : ℕ) : ℕ := 1 + (q - 1) % M

/-- The finite set stored in the source's `I₂`: precisely the residues for
which `n₁*r-1` avoids every later modulus. -/
def residueSet (n₁ : ℕ) (ns : List ℕ) : Set ℕ :=
  {r | 0 < r ∧ r ≤ period ns ∧ ∀ n ∈ ns, ¬ n ∣ n₁ * r - 1}

/-- The requested arithmetic function `f`. -/
def f (n₁ q : ℕ) : ℕ := n₁ * q - 1

/-- The requested arithmetic function `g`; `n₂` is the head of `ns`, and
the tail sum is the contribution obtained by taking `I₃=⋯=Iₖ={1}`. -/
def g (ns : List ℕ) (q : ℕ) : ℕ :=
  ns.headD 0 * residue (period ns) q + ns.tail.sum

/-- The right-hand finite sumset after taking `I₃=⋯=Iₖ={1}`. -/
def sumset (n₁ : ℕ) (ns : List ℕ) : Set ℕ :=
  {z | ∃ r ∈ residueSet n₁ ns, z = ns.headD 0 * r + ns.tail.sum}

/-- A list-based statement of the advertised representation problem. -/
def statement : Prop :=
  ∀ (n₁ : ℕ) (ns : List ℕ),
    1 < n₁ → ns ≠ [] → (∀ n ∈ ns, 1 < n) →
    TargetSet n₁ ns =
      {y | ∃ q > 0, y = f n₁ q ∧ g ns q ∈ sumset n₁ ns}

private lemma period_pos {ns : List ℕ} (hmods : ∀ n ∈ ns, 1 < n) :
    0 < period ns := by
  simp only [period]
  exact List.prod_pos fun n hn ↦ (hmods n hn).trans' Nat.zero_lt_one

theorem residueSet_finite (n₁ : ℕ) (ns : List ℕ) :
    (residueSet n₁ ns).Finite := by
  apply (Set.finite_le_nat (period ns)).subset
  intro r hr
  exact hr.2.1

private lemma mem_residueSet_iff {n₁ q : ℕ} {ns : List ℕ}
    (hn₁ : 1 < n₁) (hq : 0 < q) (hmods : ∀ n ∈ ns, 1 < n) :
    residue (period ns) q ∈ residueSet n₁ ns ↔
      ∀ n ∈ ns, ¬ n ∣ n₁ * q - 1 := by
  let M := period ns
  have hM : 0 < M := period_pos hmods
  have hrpos : 0 < residue M q := by simp [residue]
  have hrle : residue M q ≤ M := by
    have hmodlt : (q - 1) % M < M := Nat.mod_lt _ hM
    simp only [residue]
    omega
  have hcongr : q ≡ residue M q [MOD M] := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    simp [Nat.ModEq, residue, Nat.add_mod, Nat.add_comm]
  have hleft : 1 ≤ n₁ * q := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.zero_lt_of_lt hn₁).ne' hq.ne')
  have hright : 1 ≤ n₁ * residue M q := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.zero_lt_of_lt hn₁).ne' hrpos.ne')
  constructor
  · intro hr n hn hdq
    have hnM : n ∣ M := List.dvd_prod hn
    have hlin : n₁ * q - 1 ≡ n₁ * residue M q - 1 [MOD n] :=
      Nat.ModEq.sub hleft hright ((hcongr.of_dvd hnM).mul_left n₁) Nat.ModEq.rfl
    have hdiv : n ∣ n₁ * q - 1 ↔ n ∣ n₁ * residue M q - 1 :=
      hlin.dvd_iff (dvd_refl n)
    exact hr.2.2 n hn (hdiv.mp hdq)
  · intro havoid
    refine ⟨hrpos, hrle, ?_⟩
    intro n hn hdr
    have hnM : n ∣ M := List.dvd_prod hn
    have hlin : n₁ * q - 1 ≡ n₁ * residue M q - 1 [MOD n] :=
      Nat.ModEq.sub hleft hright ((hcongr.of_dvd hnM).mul_left n₁) Nat.ModEq.rfl
    have hdiv : n ∣ n₁ * q - 1 ↔ n ∣ n₁ * residue M q - 1 :=
      hlin.dvd_iff (dvd_refl n)
    exact havoid n hn (hdiv.mpr hdr)

/-- The construction represents exactly the source's target set. -/
theorem representation
    {n₁ : ℕ} {ns : List ℕ} (hn₁ : 1 < n₁) (hns : ns ≠ [])
    (hmods : ∀ n ∈ ns, 1 < n) :
    TargetSet n₁ ns = {y | ∃ q > 0, y = f n₁ q ∧ g ns q ∈ sumset n₁ ns} := by
  ext y
  constructor
  · rintro ⟨hy, _hyn₁, hydiv, hyavoid⟩
    obtain ⟨q, hq⟩ := hydiv
    have hqpos : 0 < q := by
      rw [Nat.add_comm] at hq
      nlinarith
    have hyf : y = f n₁ q := by
      simp only [f]
      omega
    refine ⟨q, hqpos, hyf, ?_⟩
    · refine ⟨residue (period ns) q, ?_, rfl⟩
      rw [mem_residueSet_iff hn₁ hqpos hmods]
      intro n hn hd
      apply hyavoid n hn
      rw [hyf]
      simpa only [f] using hd
  · rintro ⟨q, hq, rfl, hg⟩
    rcases hg with ⟨r, hr, heq⟩
    have hhead : 0 < ns.headD 0 := by
      obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hns
      exact (hmods a (by simp)).trans' Nat.zero_lt_one
    have hre : residue (period ns) q = r := by
      simp only [g] at heq
      exact Nat.eq_of_mul_eq_mul_left hhead (Nat.add_right_cancel heq)
    have hres : residue (period ns) q ∈ residueSet n₁ ns := hre ▸ hr
    rw [mem_residueSet_iff hn₁ hq hmods] at hres
    have hqone : 1 ≤ q := hq
    have hle : n₁ ≤ n₁ * q := by
      calc
        n₁ = n₁ * 1 := by simp
        _ ≤ n₁ * q := Nat.mul_le_mul_left n₁ hqone
    have hprod : 1 < n₁ * q := hn₁.trans_le hle
    have hplus : n₁ ∣ f n₁ q + 1 := by
      use q
      simp only [f]
      omega
    have hnot : ¬ n₁ ∣ f n₁ q := by
      intro hd
      have hone : n₁ ∣ 1 := (Nat.dvd_add_iff_right hd).mpr hplus
      exact hn₁.ne' (Nat.eq_one_of_dvd_one hone)
    exact ⟨by simp only [f]; omega, hnot, hplus, hres⟩

theorem proved : statement := by
  intro n₁ ns hn₁ hns hmods
  exact representation hn₁ hns hmods

end AgenticConjectures.GoldbachPrize3
