import Mathlib

/-!
# Let's Prove Goldbach prize problem 2

For fixed integers `1 < n₁ < n₂ < n₃`, the prize problem asks for an
elementary finite-case formula approximating the `x`-th positive integer
divisible by none of the three moduli.  In fact the periodicity modulo
`P = n₁*n₂*n₃` gives an exact formula.
-/

namespace AgenticConjectures.GoldbachPrize2

/-- Positive integers divisible by none of the three fixed moduli. -/
def Allowed (n₁ n₂ n₃ y : ℕ) : Prop :=
  0 < y ∧ ¬ n₁ ∣ y ∧ ¬ n₂ ∣ y ∧ ¬ n₃ ∣ y

instance (n₁ n₂ n₃ : ℕ) : DecidablePred (Allowed n₁ n₂ n₃) := by
  intro y
  unfold Allowed
  infer_instance

/-- A period common to all three divisibility predicates. -/
def period (n₁ n₂ n₃ : ℕ) : ℕ := n₁ * n₂ * n₃

/-- The allowed residues in the half-open fundamental period `[0,P)`. -/
def residueFinset (n₁ n₂ n₃ : ℕ) : Finset ℕ :=
  (Finset.range (period n₁ n₂ n₃)).filter (Allowed n₁ n₂ n₃)

/-- The allowed residues, in increasing order. -/
def residueList (n₁ n₂ n₃ : ℕ) : List ℕ :=
  (residueFinset n₁ n₂ n₃).sort (· ≤ ·)

/-- The number of allowed residues in one period. -/
def countPerPeriod (n₁ n₂ n₃ : ℕ) : ℕ :=
  (residueList n₁ n₂ n₃).length

/-- Zero-based exact finite-case formula.  `getD` is just a compact encoding
of the finite table of residue cases. -/
def formula0 (n₁ n₂ n₃ m : ℕ) : ℕ :=
  let P := period n₁ n₂ n₃
  let A := countPerPeriod n₁ n₂ n₃
  P * (m / A) + (residueList n₁ n₂ n₃).getD (m % A) 0

/-- The one-based function requested on the prize page. -/
def formula (n₁ n₂ n₃ x : ℕ) : ℕ := formula0 n₁ n₂ n₃ (x - 1)

/-- The source's one-based `t_space` sequence. -/
noncomputable def tSpace (n₁ n₂ n₃ x : ℕ) : ℕ :=
  Nat.nth (Allowed n₁ n₂ n₃) (x - 1)

private lemma one_allowed {n₁ n₂ n₃ : ℕ}
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) (hn₃ : 1 < n₃) :
    Allowed n₁ n₂ n₃ 1 := by
  simp [Allowed, hn₁.ne', hn₂.ne', hn₃.ne']

lemma countPerPeriod_pos {n₁ n₂ n₃ : ℕ}
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) (hn₃ : 1 < n₃) :
    0 < countPerPeriod n₁ n₂ n₃ := by
  have hP : 1 < period n₁ n₂ n₃ := by
    simp only [period]
    have h₁ : 2 ≤ n₁ := hn₁
    have h₂ : 1 ≤ n₂ := hn₂.le
    have h₃ : 1 ≤ n₃ := hn₃.le
    calc
      1 < 2 * 1 * 1 := by norm_num
      _ ≤ n₁ * n₂ * n₃ := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
  have hmem : 1 ∈ residueFinset n₁ n₂ n₃ := by
    simp [residueFinset, hP, one_allowed hn₁ hn₂ hn₃]
  simp only [countPerPeriod, residueList, Finset.length_sort]
  exact Finset.card_pos.mpr ⟨1, hmem⟩

private lemma dvd_period_left (n₁ n₂ n₃ : ℕ) :
    n₁ ∣ period n₁ n₂ n₃ := by
  exact ⟨n₂ * n₃, by simp [period, Nat.mul_assoc]⟩

private lemma dvd_period_mid (n₁ n₂ n₃ : ℕ) :
    n₂ ∣ period n₁ n₂ n₃ := by
  exact ⟨n₁ * n₃, by simp [period, Nat.mul_left_comm, Nat.mul_assoc]⟩

private lemma dvd_period_right (n₁ n₂ n₃ : ℕ) :
    n₃ ∣ period n₁ n₂ n₃ := by
  exact ⟨n₁ * n₂, by simp [period, Nat.mul_comm, Nat.mul_left_comm]⟩

private lemma dvd_period_mul_add_iff {d P q r : ℕ} (hd : d ∣ P) :
    d ∣ P * q + r ↔ d ∣ r := by
  constructor
  · intro h
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hd q)).mp h
  · intro h
    exact dvd_add (dvd_mul_of_dvd_left hd q) h

lemma allowed_period_mul_add_iff {n₁ n₂ n₃ q r : ℕ}
    (hr : 0 < r) :
    Allowed n₁ n₂ n₃ (period n₁ n₂ n₃ * q + r) ↔
      Allowed n₁ n₂ n₃ r := by
  simp only [Allowed, Nat.add_pos_iff_pos_or_pos, hr, or_true, true_and]
  rw [dvd_period_mul_add_iff (dvd_period_left n₁ n₂ n₃)]
  rw [dvd_period_mul_add_iff (dvd_period_mid n₁ n₂ n₃)]
  rw [dvd_period_mul_add_iff (dvd_period_right n₁ n₂ n₃)]

private lemma residue_getD_mem {n₁ n₂ n₃ j : ℕ}
    (hj : j < countPerPeriod n₁ n₂ n₃) :
    (residueList n₁ n₂ n₃).getD j 0 ∈ residueFinset n₁ n₂ n₃ := by
  have hj' : j < (residueList n₁ n₂ n₃).length := hj
  rw [List.getD_eq_getElem _ _ hj']
  exact (Finset.mem_sort (· ≤ ·)).mp (List.get_mem _ ⟨j, hj'⟩)

private lemma residue_getD_pos {n₁ n₂ n₃ j : ℕ}
    (hj : j < countPerPeriod n₁ n₂ n₃) :
    0 < (residueList n₁ n₂ n₃).getD j 0 := by
  exact (Finset.mem_filter.mp (residue_getD_mem hj)).2.1

private lemma residue_getD_lt_period {n₁ n₂ n₃ j : ℕ}
    (hj : j < countPerPeriod n₁ n₂ n₃) :
    (residueList n₁ n₂ n₃).getD j 0 < period n₁ n₂ n₃ := by
  exact Finset.mem_range.mp (Finset.mem_filter.mp (residue_getD_mem hj)).1

private lemma residue_getD_allowed {n₁ n₂ n₃ j : ℕ}
    (hj : j < countPerPeriod n₁ n₂ n₃) :
    Allowed n₁ n₂ n₃ ((residueList n₁ n₂ n₃).getD j 0) := by
  exact (Finset.mem_filter.mp (residue_getD_mem hj)).2

private lemma residue_getD_strictMono {n₁ n₂ n₃ : ℕ} :
    StrictMonoOn (fun j ↦ (residueList n₁ n₂ n₃).getD j 0)
      (Set.Iio (countPerPeriod n₁ n₂ n₃)) := by
  intro i hi j hj hij
  have hi' : i < (residueList n₁ n₂ n₃).length := hi
  have hj' : j < (residueList n₁ n₂ n₃).length := hj
  change (residueList n₁ n₂ n₃).getD i 0 <
    (residueList n₁ n₂ n₃).getD j 0
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj']
  exact (Finset.sortedLT_sort (residueFinset n₁ n₂ n₃)).strictMono_get hij

private lemma formula0_strictMono {n₁ n₂ n₃ : ℕ}
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) (hn₃ : 1 < n₃) :
    StrictMono (formula0 n₁ n₂ n₃) := by
  let P := period n₁ n₂ n₃
  let A := countPerPeriod n₁ n₂ n₃
  have hA : 0 < A := countPerPeriod_pos hn₁ hn₂ hn₃
  intro m n hmn
  have hmrem : m % A < A := Nat.mod_lt _ hA
  have hnrem : n % A < A := Nat.mod_lt _ hA
  have hmdecomp : m = A * (m / A) + m % A := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod m A).symm
  have hndecomp : n = A * (n / A) + n % A := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod n A).symm
  simp only [formula0]
  by_cases hq : m / A = n / A
  · have hr : m % A < n % A := by
      rw [hmdecomp, hndecomp, hq] at hmn
      omega
    rw [hq]
    exact Nat.add_lt_add_left (residue_getD_strictMono hmrem hnrem hr) _
  · have hqlt : m / A < n / A := by
      exact lt_of_le_of_ne (Nat.div_le_div_right hmn.le) hq
    have hmreslt : (residueList n₁ n₂ n₃).getD (m % A) 0 < P :=
      residue_getD_lt_period hmrem
    have hnrespos : 0 < (residueList n₁ n₂ n₃).getD (n % A) 0 :=
      residue_getD_pos hnrem
    calc
      P * (m / A) + (residueList n₁ n₂ n₃).getD (m % A) 0
          < P * (m / A) + P := Nat.add_lt_add_left hmreslt _
      _ = P * (m / A + 1) := by simp [Nat.mul_add]
      _ ≤ P * (n / A) := Nat.mul_le_mul_left P hqlt
      _ < P * (n / A) + (residueList n₁ n₂ n₃).getD (n % A) 0 :=
        Nat.lt_add_of_pos_right hnrespos

private lemma formula0_allowed {n₁ n₂ n₃ : ℕ}
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) (hn₃ : 1 < n₃) (m : ℕ) :
    Allowed n₁ n₂ n₃ (formula0 n₁ n₂ n₃ m) := by
  let A := countPerPeriod n₁ n₂ n₃
  have hA : 0 < A := countPerPeriod_pos hn₁ hn₂ hn₃
  have hj : m % A < A := Nat.mod_lt _ hA
  rw [formula0]
  exact (allowed_period_mul_add_iff (residue_getD_pos hj)).mpr
    (residue_getD_allowed hj)

private lemma allowed_mod_period {n₁ n₂ n₃ y : ℕ}
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) (hn₃ : 1 < n₃)
    (hy : Allowed n₁ n₂ n₃ y) :
    Allowed n₁ n₂ n₃ (y % period n₁ n₂ n₃) := by
  let P := period n₁ n₂ n₃
  have hP : 0 < P := by
    simp only [P, period]
    positivity
  have hdecomp : y = P * (y / P) + y % P := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod y P).symm
  have hrpos : 0 < y % P := by
    by_contra hz
    have hz' : y % P = 0 := Nat.eq_zero_of_not_pos hz
    have hPy : P ∣ y := Nat.dvd_of_mod_eq_zero hz'
    exact hy.2.1 ((dvd_period_left n₁ n₂ n₃).trans hPy)
  rw [hdecomp] at hy
  exact (allowed_period_mul_add_iff hrpos).mp hy

private lemma allowed_decompose {n₁ n₂ n₃ y : ℕ}
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) (hn₃ : 1 < n₃)
    (hy : Allowed n₁ n₂ n₃ y) :
    ∃ q j, j < countPerPeriod n₁ n₂ n₃ ∧
      y = period n₁ n₂ n₃ * q + (residueList n₁ n₂ n₃).getD j 0 := by
  let P := period n₁ n₂ n₃
  let r := y % P
  have hP : 0 < P := by
    simp only [P, period]
    positivity
  have hrallowed : Allowed n₁ n₂ n₃ r :=
    allowed_mod_period hn₁ hn₂ hn₃ hy
  have hrlt : r < P := Nat.mod_lt y hP
  have hrmem : r ∈ residueFinset n₁ n₂ n₃ := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrlt, hrallowed⟩
  have hrsort : r ∈ residueList n₁ n₂ n₃ :=
    (Finset.mem_sort (· ≤ ·)).mpr hrmem
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hrsort
  refine ⟨y / P, j, ?_, ?_⟩
  · simpa [countPerPeriod] using hj
  · have hdecomp : y = P * (y / P) + r := by
      dsimp [r]
      simpa [Nat.mul_comm] using (Nat.div_add_mod y P).symm
    rw [List.getD_eq_getElem _ _ hj, hget]
    exact hdecomp

private lemma formula0_surjective_on_allowed {n₁ n₂ n₃ : ℕ}
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) (hn₃ : 1 < n₃) :
    Set.SurjOn (formula0 n₁ n₂ n₃) Set.univ {y | Allowed n₁ n₂ n₃ y} := by
  intro y hy
  obtain ⟨q, j, hj, hyformula⟩ := allowed_decompose hn₁ hn₂ hn₃ hy
  let A := countPerPeriod n₁ n₂ n₃
  have hA : 0 < A := countPerPeriod_pos hn₁ hn₂ hn₃
  change j < A at hj
  have hjdiv : j / A = 0 := Nat.div_eq_of_lt hj
  have hjmod : j % A = j := Nat.mod_eq_of_lt hj
  refine ⟨A * q + j, Set.mem_univ _, ?_⟩
  simp only [formula0]
  rw [Nat.mul_add_div hA, Nat.mul_add_mod]
  rw [hjdiv, hjmod]
  simp only [Nat.add_zero]
  exact hyformula.symm

/-- The finite-case periodic formula enumerates the allowed positive integers
exactly, in increasing order. -/
theorem exact_formula0 {n₁ n₂ n₃ : ℕ}
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) (hn₃ : 1 < n₃) (m : ℕ) :
    formula0 n₁ n₂ n₃ m = Nat.nth (Allowed n₁ n₂ n₃) m := by
  apply Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn
  · intro y hy
    obtain ⟨m, _, hm⟩ := formula0_surjective_on_allowed hn₁ hn₂ hn₃ hy
    exact ⟨m, fun hf ↦ absurd hf
      (Set.infinite_of_injective_forall_mem (formula0_strictMono hn₁ hn₂ hn₃).injective
        (formula0_allowed hn₁ hn₂ hn₃)), hm⟩
  · intro m _
    exact formula0_allowed hn₁ hn₂ hn₃ m
  · exact (formula0_strictMono hn₁ hn₂ hn₃).strictMonoOn _
  · intro hf
    exact absurd hf
      (Set.infinite_of_injective_forall_mem (formula0_strictMono hn₁ hn₂ hn₃).injective
        (formula0_allowed hn₁ hn₂ hn₃))

/-- The requested one-based formula is exact, hence satisfies the advertised
error bound with zero error. -/
theorem exact_formula {n₁ n₂ n₃ x : ℕ}
    (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) (hn₃ : 1 < n₃) :
    formula n₁ n₂ n₃ x = tSpace n₁ n₂ n₃ x := by
  exact exact_formula0 hn₁ hn₂ hn₃ (x - 1)

def statement : Prop :=
  ∀ n₁ n₂ n₃ : ℕ, 1 < n₁ → n₁ < n₂ → n₂ < n₃ →
    ∃ f : ℕ → ℕ, ∀ x > 0,
      2 * Nat.dist (f x) (tSpace n₁ n₂ n₃ x) ≤ n₃ ^ 2

theorem proved : statement := by
  intro n₁ n₂ n₃ hn₁ hn₁₂ hn₂₃
  refine ⟨formula n₁ n₂ n₃, ?_⟩
  intro x _
  rw [exact_formula hn₁ (hn₁.trans hn₁₂) (hn₁.trans (hn₁₂.trans hn₂₃))]
  simp

end AgenticConjectures.GoldbachPrize2
