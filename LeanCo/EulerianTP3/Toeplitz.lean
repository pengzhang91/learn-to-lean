import LeanCo.EulerianTP3.Minors

/-!
# Toeplitz matrices of products of positive linear factors

This file proves, directly through order three, the part of the
Aissen--Edrei--Schoenberg--Whitney theorem needed for the Eulerian TP3
argument.  Multiplication by `1 + r X` adds `r` times every column to its
successor.  Multilinearity of `det2` and `det3` then proves preservation of
nonnegative minors without invoking a general Cauchy--Binet theorem.
-/

namespace LeanCo.EulerianTP3

open scoped BigOperators
open Polynomial

/-- A product of linear factors indexed by an arbitrary finite set.  This
version is convenient for root-deleted products. -/
noncomputable def factorPolynomialOn {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) : ℝ[X] :=
  ∏ i ∈ s, (1 + C (r i) * X)

/-- A polynomial presented as a product of linear factors `1 + rᵢ X`. -/
noncomputable def factorPolynomial {n : ℕ} (r : Fin n → ℝ) : ℝ[X] :=
  ∏ i, (1 + C (r i) * X)

theorem factorPolynomial_eq_factorPolynomialOn_univ {n : ℕ}
    (r : Fin n → ℝ) :
    factorPolynomial r = factorPolynomialOn Finset.univ r := by
  rfl

private lemma factorPolynomialOn_insert {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (r : ι → ℝ) (a : ι) (ha : a ∉ s) :
    factorPolynomialOn (insert a s) r =
      factorPolynomialOn s r * (1 + C (r a) * X) := by
  classical
  rw [factorPolynomialOn, Finset.prod_insert ha, factorPolynomialOn]
  exact mul_comm _ _

/-- The infinite upper Toeplitz matrix of the coefficient sequence of `p`. -/
def upperToeplitz (p : ℝ[X]) : ℕ → ℕ → ℝ := fun i j =>
  if i ≤ j then p.coeff (j - i) else 0

/-- The column operation induced on an upper Toeplitz matrix by multiplying
its polynomial by `1 + t X`. -/
private def columnStep (t : ℝ) (M : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | i, 0 => M i 0
  | i, j + 1 => M i (j + 1) + t * M i j

@[simp] private lemma columnStep_zero (t : ℝ) (M : ℕ → ℕ → ℝ) (i : ℕ) :
    columnStep t M i 0 = M i 0 := rfl

@[simp] private lemma columnStep_succ (t : ℝ) (M : ℕ → ℕ → ℝ) (i j : ℕ) :
    columnStep t M i (j + 1) = M i (j + 1) + t * M i j := rfl

private lemma coeff_mul_linear_zero (p : ℝ[X]) (t : ℝ) :
    (p * (1 + C t * X)).coeff 0 = p.coeff 0 := by
  simp

private lemma coeff_mul_linear_succ (p : ℝ[X]) (t : ℝ) (k : ℕ) :
    (p * (1 + C t * X)).coeff (k + 1) =
      p.coeff (k + 1) + t * p.coeff k := by
  rw [mul_add, mul_one, coeff_add, ← mul_assoc, coeff_mul_X, coeff_mul_C]
  ring

private lemma upperToeplitz_mul_linear (p : ℝ[X]) (t : ℝ) :
    upperToeplitz (p * (1 + C t * X)) = columnStep t (upperToeplitz p) := by
  funext i j
  rcases j with _ | j
  · by_cases hi : i = 0
    · subst i
      simp [upperToeplitz]
    · have hni : ¬i ≤ 0 := by omega
      simp [upperToeplitz, hni]
  · by_cases hij : i ≤ j
    · have hij' : i ≤ j + 1 := by omega
      have hsub : j + 1 - i = (j - i) + 1 := by omega
      simp only [upperToeplitz, columnStep_succ, if_pos hij, if_pos hij']
      rw [hsub, coeff_mul_linear_succ]
    · by_cases hi : i = j + 1
      · subst i
        simp [upperToeplitz]
      · have hij' : ¬i ≤ j + 1 := by omega
        simp [upperToeplitz, hij, hij']

private lemma factorPolynomial_succ {n : ℕ} (r : Fin (n + 1) → ℝ) :
    factorPolynomial r =
      factorPolynomial (fun i : Fin n => r i.succ) * (1 + C (r 0) * X) := by
  rw [factorPolynomial, Fin.prod_univ_succ, factorPolynomial]
  ac_rfl

@[simp] private lemma det2_same_columns (M : ℕ → ℕ → ℝ)
    (i₀ i₁ j : ℕ) : det2 M i₀ i₁ j j = 0 := by
  simp [det2]

@[simp] private lemma det3_same_columns_left (M : ℕ → ℕ → ℝ)
    (i₀ i₁ i₂ j k : ℕ) : det3 M i₀ i₁ i₂ j j k = 0 := by
  simp [det3]

@[simp] private lemma det3_same_columns_right (M : ℕ → ℕ → ℝ)
    (i₀ i₁ i₂ j k : ℕ) : det3 M i₀ i₁ i₂ j k k = 0 := by
  simp [det3]
  ring

private lemma TotallyNonnegativeUpToThree.det2_nonneg_of_le
    {M : ℕ → ℕ → ℝ} (hM : TotallyNonnegativeUpToThree M)
    {i₀ i₁ j₀ j₁ : ℕ} (hi : i₀ < i₁) (hj : j₀ ≤ j₁) :
    0 ≤ det2 M i₀ i₁ j₀ j₁ := by
  rcases hj.eq_or_lt with rfl | hj
  · simp
  · exact hM.det2_nonneg i₀ i₁ j₀ j₁ hi hj

private lemma TotallyNonnegativeUpToThree.det3_nonneg_of_le
    {M : ℕ → ℕ → ℝ} (hM : TotallyNonnegativeUpToThree M)
    {i₀ i₁ i₂ j₀ j₁ j₂ : ℕ}
    (hi01 : i₀ < i₁) (hi12 : i₁ < i₂)
    (hj01 : j₀ ≤ j₁) (hj12 : j₁ ≤ j₂) :
    0 ≤ det3 M i₀ i₁ i₂ j₀ j₁ j₂ := by
  rcases hj01.eq_or_lt with rfl | hj01
  · simp
  rcases hj12.eq_or_lt with rfl | hj12
  · simp
  exact hM.det3_nonneg i₀ i₁ i₂ j₀ j₁ j₂ hi01 hi12 hj01 hj12

private lemma det2_columnStep_zero_succ (t : ℝ) (M : ℕ → ℕ → ℝ)
    (i₀ i₁ j : ℕ) :
    det2 (columnStep t M) i₀ i₁ 0 (j + 1) =
      det2 M i₀ i₁ 0 (j + 1) + t * det2 M i₀ i₁ 0 j := by
  simp [det2]
  ring

private lemma det2_columnStep_succ_succ (t : ℝ) (M : ℕ → ℕ → ℝ)
    (i₀ i₁ j₀ j₁ : ℕ) :
    det2 (columnStep t M) i₀ i₁ (j₀ + 1) (j₁ + 1) =
      det2 M i₀ i₁ (j₀ + 1) (j₁ + 1)
        + t * det2 M i₀ i₁ j₀ (j₁ + 1)
        + t * det2 M i₀ i₁ (j₀ + 1) j₁
        + t ^ 2 * det2 M i₀ i₁ j₀ j₁ := by
  simp [det2]
  ring

private lemma det3_columnStep_zero_succ_succ (t : ℝ) (M : ℕ → ℕ → ℝ)
    (i₀ i₁ i₂ j₁ j₂ : ℕ) :
    det3 (columnStep t M) i₀ i₁ i₂ 0 (j₁ + 1) (j₂ + 1) =
      det3 M i₀ i₁ i₂ 0 (j₁ + 1) (j₂ + 1)
        + t * det3 M i₀ i₁ i₂ 0 j₁ (j₂ + 1)
        + t * det3 M i₀ i₁ i₂ 0 (j₁ + 1) j₂
        + t ^ 2 * det3 M i₀ i₁ i₂ 0 j₁ j₂ := by
  simp [det3]
  ring

private lemma det3_columnStep_succ_succ_succ (t : ℝ) (M : ℕ → ℕ → ℝ)
    (i₀ i₁ i₂ j₀ j₁ j₂ : ℕ) :
    det3 (columnStep t M) i₀ i₁ i₂ (j₀ + 1) (j₁ + 1) (j₂ + 1) =
      det3 M i₀ i₁ i₂ (j₀ + 1) (j₁ + 1) (j₂ + 1)
        + t * det3 M i₀ i₁ i₂ j₀ (j₁ + 1) (j₂ + 1)
        + t * det3 M i₀ i₁ i₂ (j₀ + 1) j₁ (j₂ + 1)
        + t * det3 M i₀ i₁ i₂ (j₀ + 1) (j₁ + 1) j₂
        + t ^ 2 * det3 M i₀ i₁ i₂ j₀ j₁ (j₂ + 1)
        + t ^ 2 * det3 M i₀ i₁ i₂ j₀ (j₁ + 1) j₂
        + t ^ 2 * det3 M i₀ i₁ i₂ (j₀ + 1) j₁ j₂
        + t ^ 3 * det3 M i₀ i₁ i₂ j₀ j₁ j₂ := by
  simp [det3]
  ring

private lemma TotallyNonnegativeUpToThree.columnStep
    {M : ℕ → ℕ → ℝ} (hM : TotallyNonnegativeUpToThree M)
    {t : ℝ} (ht : 0 ≤ t) :
    TotallyNonnegativeUpToThree (columnStep t M) := by
  constructor
  · intro i j
    rcases j with _ | j
    · simpa using hM.entry_nonneg i 0
    · simp only [columnStep_succ]
      exact add_nonneg (hM.entry_nonneg i (j + 1))
        (mul_nonneg ht (hM.entry_nonneg i j))
  · intro i₀ i₁ j₀ j₁ hi hj
    rcases j₀ with _ | j₀
    · rcases j₁ with _ | j₁
      · omega
      · rw [det2_columnStep_zero_succ]
        have h₀ := hM.det2_nonneg i₀ i₁ 0 (j₁ + 1) hi (by omega)
        have h₁ := hM.det2_nonneg_of_le hi (show 0 ≤ j₁ by omega)
        positivity
    · rcases j₁ with _ | j₁
      · omega
      · have hj' : j₀ < j₁ := by omega
        rw [det2_columnStep_succ_succ]
        have h₀ := hM.det2_nonneg i₀ i₁ (j₀ + 1) (j₁ + 1) hi (by omega)
        have h₁ := hM.det2_nonneg i₀ i₁ j₀ (j₁ + 1) hi (by omega)
        have h₂ := hM.det2_nonneg_of_le hi (show j₀ + 1 ≤ j₁ by omega)
        have h₃ := hM.det2_nonneg i₀ i₁ j₀ j₁ hi hj'
        positivity
  · intro i₀ i₁ i₂ j₀ j₁ j₂ hi01 hi12 hj01 hj12
    rcases j₀ with _ | j₀
    · rcases j₁ with _ | j₁
      · omega
      · rcases j₂ with _ | j₂
        · omega
        · have hj' : j₁ < j₂ := by omega
          rw [det3_columnStep_zero_succ_succ]
          have h₀ := hM.det3_nonneg i₀ i₁ i₂ 0 (j₁ + 1) (j₂ + 1)
            hi01 hi12 (by omega) (by omega)
          have h₁ := hM.det3_nonneg_of_le hi01 hi12
            (show 0 ≤ j₁ by omega) (show j₁ ≤ j₂ + 1 by omega)
          have h₂ := hM.det3_nonneg_of_le hi01 hi12
            (show 0 ≤ j₁ + 1 by omega) (show j₁ + 1 ≤ j₂ by omega)
          have h₃ := hM.det3_nonneg_of_le hi01 hi12
            (show 0 ≤ j₁ by omega) (show j₁ ≤ j₂ by omega)
          positivity
    · rcases j₁ with _ | j₁
      · omega
      · rcases j₂ with _ | j₂
        · omega
        · have hj01' : j₀ < j₁ := by omega
          have hj12' : j₁ < j₂ := by omega
          rw [det3_columnStep_succ_succ_succ]
          have h₀ := hM.det3_nonneg i₀ i₁ i₂
            (j₀ + 1) (j₁ + 1) (j₂ + 1) hi01 hi12 (by omega) (by omega)
          have h₁ := hM.det3_nonneg i₀ i₁ i₂
            j₀ (j₁ + 1) (j₂ + 1) hi01 hi12 (by omega) (by omega)
          have h₂ := hM.det3_nonneg_of_le hi01 hi12
            (show j₀ + 1 ≤ j₁ by omega) (show j₁ ≤ j₂ + 1 by omega)
          have h₃ := hM.det3_nonneg_of_le hi01 hi12
            (show j₀ + 1 ≤ j₁ + 1 by omega) (show j₁ + 1 ≤ j₂ by omega)
          have h₄ := hM.det3_nonneg i₀ i₁ i₂
            j₀ j₁ (j₂ + 1) hi01 hi12 hj01' (by omega)
          have h₅ := hM.det3_nonneg_of_le hi01 hi12
            (show j₀ ≤ j₁ + 1 by omega) (show j₁ + 1 ≤ j₂ by omega)
          have h₆ := hM.det3_nonneg_of_le hi01 hi12
            (show j₀ + 1 ≤ j₁ by omega) (show j₁ ≤ j₂ by omega)
          have h₇ := hM.det3_nonneg i₀ i₁ i₂
            j₀ j₁ j₂ hi01 hi12 hj01' hj12'
          positivity

private lemma upperToeplitz_one_apply (i j : ℕ) :
    upperToeplitz (1 : ℝ[X]) i j = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst i
    simp [upperToeplitz]
  · by_cases hle : i ≤ j
    · have hsub : j - i ≠ 0 := by omega
      simp [upperToeplitz, hle, coeff_one, hsub, hij]
    · simp [upperToeplitz, hle, hij]

private lemma upperToeplitz_one :
    TotallyNonnegativeUpToThree (upperToeplitz (1 : ℝ[X])) := by
  have hentry : ∀ i j, 0 ≤ upperToeplitz (1 : ℝ[X]) i j := by
    intro i j
    rw [upperToeplitz_one_apply]
    split_ifs <;> norm_num
  constructor
  · exact hentry
  · intro i₀ i₁ j₀ j₁ hi hj
    simp only [det2]
    have hcross : upperToeplitz (1 : ℝ[X]) i₀ j₁ *
        upperToeplitz (1 : ℝ[X]) i₁ j₀ = 0 := by
      simp only [upperToeplitz_one_apply]
      split_ifs <;> simp_all <;> omega
    rw [hcross, sub_zero]
    exact mul_nonneg (hentry i₀ j₀) (hentry i₁ j₁)
  · intro i₀ i₁ i₂ j₀ j₁ j₂ hi01 hi12 hj01 hj12
    have hn₀ : upperToeplitz (1 : ℝ[X]) i₀ j₂ *
        upperToeplitz (1 : ℝ[X]) i₁ j₁ *
        upperToeplitz (1 : ℝ[X]) i₂ j₀ = 0 := by
      simp only [upperToeplitz_one_apply]
      split_ifs <;> simp_all <;> omega
    have hn₁ : upperToeplitz (1 : ℝ[X]) i₀ j₁ *
        upperToeplitz (1 : ℝ[X]) i₁ j₀ *
        upperToeplitz (1 : ℝ[X]) i₂ j₂ = 0 := by
      simp only [upperToeplitz_one_apply]
      split_ifs <;> simp_all <;> omega
    have hn₂ : upperToeplitz (1 : ℝ[X]) i₀ j₀ *
        upperToeplitz (1 : ℝ[X]) i₁ j₂ *
        upperToeplitz (1 : ℝ[X]) i₂ j₁ = 0 := by
      simp only [upperToeplitz_one_apply]
      split_ifs <;> simp_all <;> omega
    rw [det3, hn₀, hn₁, hn₂]
    have h₀ := hentry i₀ j₀
    have h₁ := hentry i₁ j₁
    have h₂ := hentry i₂ j₂
    have h₃ := hentry i₀ j₁
    have h₄ := hentry i₁ j₂
    have h₅ := hentry i₂ j₀
    have h₆ := hentry i₀ j₂
    have h₇ := hentry i₁ j₀
    have h₈ := hentry i₂ j₁
    have hp₀ : 0 ≤ upperToeplitz (1 : ℝ[X]) i₀ j₀ *
        upperToeplitz (1 : ℝ[X]) i₁ j₁ *
        upperToeplitz (1 : ℝ[X]) i₂ j₂ :=
      mul_nonneg (mul_nonneg h₀ h₁) h₂
    have hp₁ : 0 ≤ upperToeplitz (1 : ℝ[X]) i₀ j₁ *
        upperToeplitz (1 : ℝ[X]) i₁ j₂ *
        upperToeplitz (1 : ℝ[X]) i₂ j₀ :=
      mul_nonneg (mul_nonneg h₃ h₄) h₅
    have hp₂ : 0 ≤ upperToeplitz (1 : ℝ[X]) i₀ j₂ *
        upperToeplitz (1 : ℝ[X]) i₁ j₀ *
        upperToeplitz (1 : ℝ[X]) i₂ j₁ :=
      mul_nonneg (mul_nonneg h₆ h₇) h₈
    simpa only [sub_zero] using add_nonneg (add_nonneg hp₀ hp₁) hp₂

/-- Products of nonnegative linear factors have all ordered Toeplitz minors
of orders one, two, and three nonnegative. -/
theorem factorPolynomial_totallyNonnegativeUpToThree {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) :
    TotallyNonnegativeUpToThree (upperToeplitz (factorPolynomial r)) := by
  induction n with
  | zero =>
      simpa [factorPolynomial] using upperToeplitz_one
  | succ n ih =>
      rw [factorPolynomial_succ, upperToeplitz_mul_linear]
      exact (ih (fun i : Fin n => r i.succ) (fun i => hr i.succ)).columnStep (hr 0)

/-- Entrywise nonnegativity, extracted from
`factorPolynomial_totallyNonnegativeUpToThree`. -/
theorem factorPolynomial_upperToeplitz_entry_nonneg {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (i j : ℕ) :
    0 ≤ upperToeplitz (factorPolynomial r) i j :=
  (factorPolynomial_totallyNonnegativeUpToThree r hr).entry_nonneg i j

/-- Every ordered two-by-two minor of the factor polynomial's Toeplitz
matrix is nonnegative. -/
theorem factorPolynomial_upperToeplitz_det2_nonneg {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    {i₀ i₁ j₀ j₁ : ℕ} (hi : i₀ < i₁) (hj : j₀ < j₁) :
    0 ≤ det2 (upperToeplitz (factorPolynomial r)) i₀ i₁ j₀ j₁ :=
  (factorPolynomial_totallyNonnegativeUpToThree r hr).det2_nonneg
    i₀ i₁ j₀ j₁ hi hj

/-- Every ordered three-by-three minor of the factor polynomial's Toeplitz
matrix is nonnegative. -/
theorem factorPolynomial_upperToeplitz_det3_nonneg {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    {i₀ i₁ i₂ j₀ j₁ j₂ : ℕ}
    (hi01 : i₀ < i₁) (hi12 : i₁ < i₂)
    (hj01 : j₀ < j₁) (hj12 : j₁ < j₂) :
    0 ≤ det3 (upperToeplitz (factorPolynomial r)) i₀ i₁ i₂ j₀ j₁ j₂ :=
  (factorPolynomial_totallyNonnegativeUpToThree r hr).det3_nonneg
    i₀ i₁ i₂ j₀ j₁ j₂ hi01 hi12 hj01 hj12

/-! ## Common-factor bridges for coefficient minors -/

/-- The coefficient matrix of a family of polynomials. -/
def coefficientMatrix (p : ℕ → ℝ[X]) : ℕ → ℕ → ℝ := fun i j =>
  (p i).coeff j

/-- Nonnegativity of all ordered two-column minors on two fixed rows. -/
def OrderedDet2Nonnegative (M : ℕ → ℕ → ℝ) (i₀ i₁ : ℕ) : Prop :=
  ∀ j₀ j₁, j₀ < j₁ → 0 ≤ det2 M i₀ i₁ j₀ j₁

/-- Nonnegativity of all ordered three-column minors on three fixed rows. -/
def OrderedDet3Nonnegative (M : ℕ → ℕ → ℝ) (i₀ i₁ i₂ : ℕ) : Prop :=
  ∀ j₀ j₁ j₂, j₀ < j₁ → j₁ < j₂ →
    0 ≤ det3 M i₀ i₁ i₂ j₀ j₁ j₂

private lemma OrderedDet2Nonnegative.nonneg_of_le
    {M : ℕ → ℕ → ℝ} {i₀ i₁ : ℕ}
    (hM : OrderedDet2Nonnegative M i₀ i₁)
    {j₀ j₁ : ℕ} (hj : j₀ ≤ j₁) :
    0 ≤ det2 M i₀ i₁ j₀ j₁ := by
  rcases hj.eq_or_lt with rfl | hj
  · simp
  · exact hM j₀ j₁ hj

private lemma OrderedDet3Nonnegative.nonneg_of_le
    {M : ℕ → ℕ → ℝ} {i₀ i₁ i₂ : ℕ}
    (hM : OrderedDet3Nonnegative M i₀ i₁ i₂)
    {j₀ j₁ j₂ : ℕ} (hj01 : j₀ ≤ j₁) (hj12 : j₁ ≤ j₂) :
    0 ≤ det3 M i₀ i₁ i₂ j₀ j₁ j₂ := by
  rcases hj01.eq_or_lt with rfl | hj01
  · simp
  rcases hj12.eq_or_lt with rfl | hj12
  · simp
  exact hM j₀ j₁ j₂ hj01 hj12

private lemma OrderedDet2Nonnegative.columnStep
    {M : ℕ → ℕ → ℝ} {i₀ i₁ : ℕ}
    (hM : OrderedDet2Nonnegative M i₀ i₁)
    {t : ℝ} (ht : 0 ≤ t) :
    OrderedDet2Nonnegative (columnStep t M) i₀ i₁ := by
  intro j₀ j₁ hj
  rcases j₀ with _ | j₀
  · rcases j₁ with _ | j₁
    · omega
    · rw [det2_columnStep_zero_succ]
      have h₀ := hM 0 (j₁ + 1) (by omega)
      have h₁ := hM.nonneg_of_le (show 0 ≤ j₁ by omega)
      positivity
  · rcases j₁ with _ | j₁
    · omega
    · have hj' : j₀ < j₁ := by omega
      rw [det2_columnStep_succ_succ]
      have h₀ := hM (j₀ + 1) (j₁ + 1) (by omega)
      have h₁ := hM j₀ (j₁ + 1) (by omega)
      have h₂ := hM.nonneg_of_le (show j₀ + 1 ≤ j₁ by omega)
      have h₃ := hM j₀ j₁ hj'
      positivity

private lemma OrderedDet3Nonnegative.columnStep
    {M : ℕ → ℕ → ℝ} {i₀ i₁ i₂ : ℕ}
    (hM : OrderedDet3Nonnegative M i₀ i₁ i₂)
    {t : ℝ} (ht : 0 ≤ t) :
    OrderedDet3Nonnegative (columnStep t M) i₀ i₁ i₂ := by
  intro j₀ j₁ j₂ hj01 hj12
  rcases j₀ with _ | j₀
  · rcases j₁ with _ | j₁
    · omega
    · rcases j₂ with _ | j₂
      · omega
      · have hj' : j₁ < j₂ := by omega
        rw [det3_columnStep_zero_succ_succ]
        have h₀ := hM 0 (j₁ + 1) (j₂ + 1) (by omega) (by omega)
        have h₁ := hM.nonneg_of_le
          (show 0 ≤ j₁ by omega) (show j₁ ≤ j₂ + 1 by omega)
        have h₂ := hM.nonneg_of_le
          (show 0 ≤ j₁ + 1 by omega) (show j₁ + 1 ≤ j₂ by omega)
        have h₃ := hM.nonneg_of_le
          (show 0 ≤ j₁ by omega) (show j₁ ≤ j₂ by omega)
        positivity
  · rcases j₁ with _ | j₁
    · omega
    · rcases j₂ with _ | j₂
      · omega
      · have hj01' : j₀ < j₁ := by omega
        have hj12' : j₁ < j₂ := by omega
        rw [det3_columnStep_succ_succ_succ]
        have h₀ := hM (j₀ + 1) (j₁ + 1) (j₂ + 1) (by omega) (by omega)
        have h₁ := hM j₀ (j₁ + 1) (j₂ + 1) (by omega) (by omega)
        have h₂ := hM.nonneg_of_le
          (show j₀ + 1 ≤ j₁ by omega) (show j₁ ≤ j₂ + 1 by omega)
        have h₃ := hM.nonneg_of_le
          (show j₀ + 1 ≤ j₁ + 1 by omega) (show j₁ + 1 ≤ j₂ by omega)
        have h₄ := hM j₀ j₁ (j₂ + 1) hj01' (by omega)
        have h₅ := hM.nonneg_of_le
          (show j₀ ≤ j₁ + 1 by omega) (show j₁ + 1 ≤ j₂ by omega)
        have h₆ := hM.nonneg_of_le
          (show j₀ + 1 ≤ j₁ by omega) (show j₁ ≤ j₂ by omega)
        have h₇ := hM j₀ j₁ j₂ hj01' hj12'
        positivity

private lemma coefficientMatrix_mul_linear (p : ℕ → ℝ[X]) (t : ℝ) :
    coefficientMatrix (fun i => p i * (1 + C t * X)) =
      columnStep t (coefficientMatrix p) := by
  funext i j
  rcases j with _ | j
  · simp [coefficientMatrix]
  · simp only [coefficientMatrix, columnStep_succ, coeff_mul_linear_succ]

/-- Multiplying every polynomial in a family by the same product of
nonnegative linear factors preserves all ordered two-column coefficient
minors on any fixed pair of rows. -/
theorem coefficientMatrix_mul_factorPolynomial_det2_nonnegative {n : ℕ}
    (p : ℕ → ℝ[X]) (i₀ i₁ : ℕ) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hp : OrderedDet2Nonnegative (coefficientMatrix p) i₀ i₁) :
    OrderedDet2Nonnegative
      (coefficientMatrix (fun i => p i * factorPolynomial r)) i₀ i₁ := by
  induction n with
  | zero =>
      simpa [factorPolynomial, coefficientMatrix] using hp
  | succ n ih =>
      rw [factorPolynomial_succ]
      simp_rw [← mul_assoc]
      rw [coefficientMatrix_mul_linear]
      exact (ih (r := fun i : Fin n => r i.succ)
        (hr := fun i => hr i.succ)).columnStep (hr 0)

/-- Multiplying every polynomial in a family by the same product of
nonnegative linear factors preserves all ordered three-column coefficient
minors on any fixed triple of rows.  This is the fixed-order
Cauchy--Binet bridge used by the local `Phi` tables. -/
theorem coefficientMatrix_mul_factorPolynomial_det3_nonnegative {n : ℕ}
    (p : ℕ → ℝ[X]) (i₀ i₁ i₂ : ℕ) (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hp : OrderedDet3Nonnegative (coefficientMatrix p) i₀ i₁ i₂) :
    OrderedDet3Nonnegative
      (coefficientMatrix (fun i => p i * factorPolynomial r)) i₀ i₁ i₂ := by
  induction n with
  | zero =>
      simpa [factorPolynomial, coefficientMatrix] using hp
  | succ n ih =>
      rw [factorPolynomial_succ]
      simp_rw [← mul_assoc]
      rw [coefficientMatrix_mul_linear]
      exact (ih (r := fun i : Fin n => r i.succ)
        (hr := fun i => hr i.succ)).columnStep (hr 0)

/-- The order-two common-factor bridge for a product indexed by an arbitrary
`Finset`.  In particular it applies directly to a root-deleted factor set. -/
theorem coefficientMatrix_mul_factorPolynomialOn_det2_nonnegative
    {ι : Type*} (p : ℕ → ℝ[X]) (i₀ i₁ : ℕ)
    (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hp : OrderedDet2Nonnegative (coefficientMatrix p) i₀ i₁) :
    OrderedDet2Nonnegative
      (coefficientMatrix (fun i => p i * factorPolynomialOn s r)) i₀ i₁ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa [factorPolynomialOn, coefficientMatrix] using hp
  | @insert a s ha ih =>
      rw [factorPolynomialOn_insert s r a ha]
      simp_rw [← mul_assoc]
      rw [coefficientMatrix_mul_linear]
      exact (ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))).columnStep
        (hr a (Finset.mem_insert_self a s))

/-- The order-three common-factor bridge for a product indexed by an
arbitrary `Finset`. -/
theorem coefficientMatrix_mul_factorPolynomialOn_det3_nonnegative
    {ι : Type*} (p : ℕ → ℝ[X]) (i₀ i₁ i₂ : ℕ)
    (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i)
    (hp : OrderedDet3Nonnegative (coefficientMatrix p) i₀ i₁ i₂) :
    OrderedDet3Nonnegative
      (coefficientMatrix (fun i => p i * factorPolynomialOn s r)) i₀ i₁ i₂ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa [factorPolynomialOn, coefficientMatrix] using hp
  | @insert a s ha ih =>
      rw [factorPolynomialOn_insert s r a ha]
      simp_rw [← mul_assoc]
      rw [coefficientMatrix_mul_linear]
      exact (ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))).columnStep
        (hr a (Finset.mem_insert_self a s))

/-- Strict positivity of the consecutive Toeplitz minors with initial rows.
The degree bound is recorded explicitly because these are the solid minors
used in the Eulerian argument. -/
private structure InitialSolidStrictUpToThree
    (M : ℕ → ℕ → ℝ) (n : ℕ) : Prop where
  entry_pos : ∀ k, k ≤ n → 0 < M 0 k
  det2_pos : ∀ k, k ≤ n → 0 < det2 M 0 1 k (k + 1)
  det3_pos : ∀ k, k ≤ n → 0 < det3 M 0 1 2 k (k + 1) (k + 2)

private lemma initialSolidStrict_one :
    InitialSolidStrictUpToThree (upperToeplitz (1 : ℝ[X])) 0 := by
  constructor
  · intro k hk
    have : k = 0 := by omega
    subst k
    norm_num [upperToeplitz]
  · intro k hk
    have : k = 0 := by omega
    subst k
    norm_num [det2, upperToeplitz, coeff_one]
  · intro k hk
    have : k = 0 := by omega
    subst k
    norm_num [det3, upperToeplitz, coeff_one]

private lemma InitialSolidStrictUpToThree.columnStep
    {M : ℕ → ℕ → ℝ} {n : ℕ}
    (hstrict : InitialSolidStrictUpToThree M n)
    (hTN : TotallyNonnegativeUpToThree M)
    {t : ℝ} (ht : 0 < t) :
    InitialSolidStrictUpToThree (columnStep t M) (n + 1) := by
  constructor
  · intro k hk
    rcases k with _ | k
    · simpa using hstrict.entry_pos 0 (by omega)
    · simp only [columnStep_succ]
      have hleft := hTN.entry_nonneg 0 (k + 1)
      have hright := hstrict.entry_pos k (by omega)
      positivity
  · intro k hk
    rcases k with _ | k
    · rw [det2_columnStep_zero_succ]
      simpa using hstrict.det2_pos 0 (by omega)
    · rw [det2_columnStep_succ_succ]
      have h₀ := hTN.det2_nonneg 0 1 (k + 1) (k + 2) (by omega) (by omega)
      have h₁ := hTN.det2_nonneg 0 1 k (k + 2) (by omega) (by omega)
      have h₂ := hTN.det2_nonneg_of_le (show 0 < 1 by omega)
        (show k + 1 ≤ k + 1 by omega)
      have h₃ := hstrict.det2_pos k (by omega)
      positivity
  · intro k hk
    rcases k with _ | k
    · rw [det3_columnStep_zero_succ_succ]
      simpa using hstrict.det3_pos 0 (by omega)
    · rw [det3_columnStep_succ_succ_succ]
      have h₀ := hTN.det3_nonneg 0 1 2
        (k + 1) (k + 2) (k + 3) (by omega) (by omega) (by omega) (by omega)
      have h₁ := hTN.det3_nonneg 0 1 2
        k (k + 2) (k + 3) (by omega) (by omega) (by omega) (by omega)
      have h₂ := hTN.det3_nonneg_of_le (show 0 < 1 by omega) (show 1 < 2 by omega)
        (show k + 1 ≤ k + 1 by omega) (show k + 1 ≤ k + 3 by omega)
      have h₃ := hTN.det3_nonneg_of_le (show 0 < 1 by omega) (show 1 < 2 by omega)
        (show k + 1 ≤ k + 2 by omega) (show k + 2 ≤ k + 2 by omega)
      have h₄ := hTN.det3_nonneg 0 1 2
        k (k + 1) (k + 3) (by omega) (by omega) (by omega) (by omega)
      have h₅ := hTN.det3_nonneg_of_le (show 0 < 1 by omega) (show 1 < 2 by omega)
        (show k ≤ k + 2 by omega) (show k + 2 ≤ k + 2 by omega)
      have h₆ := hTN.det3_nonneg_of_le (show 0 < 1 by omega) (show 1 < 2 by omega)
        (show k + 1 ≤ k + 1 by omega) (show k + 1 ≤ k + 2 by omega)
      have h₇ := hstrict.det3_pos k (by omega)
      positivity

private lemma factorPolynomial_initialSolidStrictUpToThree {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    InitialSolidStrictUpToThree (upperToeplitz (factorPolynomial r)) n := by
  induction n with
  | zero =>
      simpa [factorPolynomial] using initialSolidStrict_one
  | succ n ih =>
      rw [factorPolynomial_succ, upperToeplitz_mul_linear]
      exact (ih (fun i : Fin n => r i.succ) (fun i => hr i.succ)).columnStep
        (factorPolynomial_totallyNonnegativeUpToThree
          (fun i : Fin n => r i.succ) (fun i => (hr i.succ).le))
        (hr 0)

/-- Every coefficient through the degree is positive when all linear-factor
parameters are positive. -/
theorem factorPolynomial_upperToeplitz_entry_pos {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (k : ℕ) (hk : k ≤ n) :
    0 < upperToeplitz (factorPolynomial r) 0 k :=
  (factorPolynomial_initialSolidStrictUpToThree r hr).entry_pos k hk

/-- The consecutive two-by-two Toeplitz minors on rows `0,1` are positive
through the degree. -/
theorem factorPolynomial_upperToeplitz_det2_consecutive_pos {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (k : ℕ) (hk : k ≤ n) :
    0 < det2 (upperToeplitz (factorPolynomial r)) 0 1 k (k + 1) :=
  (factorPolynomial_initialSolidStrictUpToThree r hr).det2_pos k hk

/-- The consecutive three-by-three Toeplitz minors on rows `0,1,2` are
positive through the degree. -/
theorem factorPolynomial_upperToeplitz_det3_consecutive_pos {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (k : ℕ) (hk : k ≤ n) :
    0 < det3 (upperToeplitz (factorPolynomial r)) 0 1 2
      k (k + 1) (k + 2) :=
  (factorPolynomial_initialSolidStrictUpToThree r hr).det3_pos k hk

end LeanCo.EulerianTP3
