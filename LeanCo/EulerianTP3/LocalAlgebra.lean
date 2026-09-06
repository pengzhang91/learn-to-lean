import LeanCo.EulerianTP3.Toeplitz

/-!
# Local algebra for the Eulerian three-row minor

This file contains the finite algebra that replaces the rectangular
Cauchy--Binet and Schur-function steps in arXiv:2608.29224.  The key point
is that a common factor `1 + t X` performs the same adjacent-column
operation on every local triple.  Determinant multilinearity therefore
preserves a *weighted aggregate* of ordered minors; the individual local
minors need not be nonnegative.
-/

namespace LeanCo.EulerianTP3

open scoped BigOperators
open Polynomial

/-! ## Weighted common-factor bridge -/

/-- Regard three coefficient rows as an ordinary matrix. -/
def tripleCoefficientMatrix (A : Fin 3 → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => A 0 j
  | 1, j => A 1 j
  | 2, j => A 2 j
  | _, _ => 0

/-- A three-column determinant of three coefficient rows. -/
def coefficientMinor3 (A : Fin 3 → ℕ → ℝ) (j₀ j₁ j₂ : ℕ) : ℝ :=
  det3 (tripleCoefficientMatrix A) 0 1 2 j₀ j₁ j₂

/-- The column operation induced by multiplying all three rows by
`1 + t X`. -/
def commonLinearStep (t : ℝ) (A : Fin 3 → ℕ → ℝ) : Fin 3 → ℕ → ℝ
  | i, 0 => A i 0
  | i, j + 1 => A i (j + 1) + t * A i j

@[simp] lemma coefficientMinor3_same_left (A : Fin 3 → ℕ → ℝ) (j k : ℕ) :
    coefficientMinor3 A j j k = 0 := by
  simp [coefficientMinor3, tripleCoefficientMatrix, det3]

@[simp] lemma coefficientMinor3_same_right (A : Fin 3 → ℕ → ℝ) (j k : ℕ) :
    coefficientMinor3 A j k k = 0 := by
  simp [coefficientMinor3, tripleCoefficientMatrix, det3]
  ring

lemma coefficientMinor3_commonLinearStep_zero (t : ℝ) (A : Fin 3 → ℕ → ℝ)
    (j₁ j₂ : ℕ) :
    coefficientMinor3 (commonLinearStep t A) 0 (j₁ + 1) (j₂ + 1) =
      coefficientMinor3 A 0 (j₁ + 1) (j₂ + 1)
        + t * coefficientMinor3 A 0 j₁ (j₂ + 1)
        + t * coefficientMinor3 A 0 (j₁ + 1) j₂
        + t ^ 2 * coefficientMinor3 A 0 j₁ j₂ := by
  simp [coefficientMinor3, tripleCoefficientMatrix, commonLinearStep, det3]
  ring

lemma coefficientMinor3_commonLinearStep_succ (t : ℝ) (A : Fin 3 → ℕ → ℝ)
    (j₀ j₁ j₂ : ℕ) :
    coefficientMinor3 (commonLinearStep t A) (j₀ + 1) (j₁ + 1) (j₂ + 1) =
      coefficientMinor3 A (j₀ + 1) (j₁ + 1) (j₂ + 1)
        + t * coefficientMinor3 A j₀ (j₁ + 1) (j₂ + 1)
        + t * coefficientMinor3 A (j₀ + 1) j₁ (j₂ + 1)
        + t * coefficientMinor3 A (j₀ + 1) (j₁ + 1) j₂
        + t ^ 2 * coefficientMinor3 A j₀ j₁ (j₂ + 1)
        + t ^ 2 * coefficientMinor3 A j₀ (j₁ + 1) j₂
        + t ^ 2 * coefficientMinor3 A (j₀ + 1) j₁ j₂
        + t ^ 3 * coefficientMinor3 A j₀ j₁ j₂ := by
  simp [coefficientMinor3, tripleCoefficientMatrix, commonLinearStep, det3]
  ring

/-- A signed or weighted sum of local three-row minors. -/
def weightedCoefficientMinor3 {s : Type*} [Fintype s] (w : s → ℝ)
    (A : s → Fin 3 → ℕ → ℝ) (j₀ j₁ j₂ : ℕ) : ℝ :=
  ∑ u, w u * coefficientMinor3 (A u) j₀ j₁ j₂

/-- Nonnegativity of every ordered three-column aggregate. -/
def WeightedOrderedDet3Nonnegative {s : Type*} [Fintype s] (w : s → ℝ)
    (A : s → Fin 3 → ℕ → ℝ) : Prop :=
  ∀ j₀ j₁ j₂, j₀ < j₁ → j₁ < j₂ →
    0 ≤ weightedCoefficientMinor3 w A j₀ j₁ j₂

@[simp] lemma weightedCoefficientMinor3_same_left {s : Type*} [Fintype s]
    (w : s → ℝ) (A : s → Fin 3 → ℕ → ℝ) (j k : ℕ) :
    weightedCoefficientMinor3 w A j j k = 0 := by
  simp [weightedCoefficientMinor3]

@[simp] lemma weightedCoefficientMinor3_same_right {s : Type*} [Fintype s]
    (w : s → ℝ) (A : s → Fin 3 → ℕ → ℝ) (j k : ℕ) :
    weightedCoefficientMinor3 w A j k k = 0 := by
  simp [weightedCoefficientMinor3]

lemma WeightedOrderedDet3Nonnegative.nonneg_of_le {s : Type*} [Fintype s]
    {w : s → ℝ} {A : s → Fin 3 → ℕ → ℝ}
    (hA : WeightedOrderedDet3Nonnegative w A)
    {j₀ j₁ j₂ : ℕ} (h₀₁ : j₀ ≤ j₁) (h₁₂ : j₁ ≤ j₂) :
    0 ≤ weightedCoefficientMinor3 w A j₀ j₁ j₂ := by
  rcases h₀₁.eq_or_lt with rfl | h₀₁
  · simp
  rcases h₁₂.eq_or_lt with rfl | h₁₂
  · simp
  exact hA j₀ j₁ j₂ h₀₁ h₁₂

lemma weightedCoefficientMinor3_commonLinearStep_zero {s : Type*} [Fintype s]
    (w : s → ℝ) (A : s → Fin 3 → ℕ → ℝ) (t : ℝ) (j₁ j₂ : ℕ) :
    weightedCoefficientMinor3 w (fun u ↦ commonLinearStep t (A u)) 0 (j₁ + 1) (j₂ + 1) =
      weightedCoefficientMinor3 w A 0 (j₁ + 1) (j₂ + 1)
        + t * weightedCoefficientMinor3 w A 0 j₁ (j₂ + 1)
        + t * weightedCoefficientMinor3 w A 0 (j₁ + 1) j₂
        + t ^ 2 * weightedCoefficientMinor3 w A 0 j₁ j₂ := by
  classical
  unfold weightedCoefficientMinor3
  have pull (a : ℝ) (f : s → ℝ) :
      (∑ u, w u * (a * f u)) = a * ∑ u, w u * f u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  simp_rw [coefficientMinor3_commonLinearStep_zero, mul_add]
  simp only [Finset.sum_add_distrib]
  simp_rw [pull]

lemma weightedCoefficientMinor3_commonLinearStep_succ {s : Type*} [Fintype s]
    (w : s → ℝ) (A : s → Fin 3 → ℕ → ℝ) (t : ℝ)
    (j₀ j₁ j₂ : ℕ) :
    weightedCoefficientMinor3 w (fun u ↦ commonLinearStep t (A u))
        (j₀ + 1) (j₁ + 1) (j₂ + 1) =
      weightedCoefficientMinor3 w A (j₀ + 1) (j₁ + 1) (j₂ + 1)
        + t * weightedCoefficientMinor3 w A j₀ (j₁ + 1) (j₂ + 1)
        + t * weightedCoefficientMinor3 w A (j₀ + 1) j₁ (j₂ + 1)
        + t * weightedCoefficientMinor3 w A (j₀ + 1) (j₁ + 1) j₂
        + t ^ 2 * weightedCoefficientMinor3 w A j₀ j₁ (j₂ + 1)
        + t ^ 2 * weightedCoefficientMinor3 w A j₀ (j₁ + 1) j₂
        + t ^ 2 * weightedCoefficientMinor3 w A (j₀ + 1) j₁ j₂
        + t ^ 3 * weightedCoefficientMinor3 w A j₀ j₁ j₂ := by
  classical
  unfold weightedCoefficientMinor3
  have pull (a : ℝ) (f : s → ℝ) :
      (∑ u, w u * (a * f u)) = a * ∑ u, w u * f u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  simp_rw [coefficientMinor3_commonLinearStep_succ, mul_add]
  simp only [Finset.sum_add_distrib]
  simp_rw [pull]

/-- Weighted ordered minor nonnegativity is preserved by a common positive
linear factor.  No sign condition is imposed on the weights. -/
theorem WeightedOrderedDet3Nonnegative.commonLinearStep {s : Type*} [Fintype s]
    {w : s → ℝ} {A : s → Fin 3 → ℕ → ℝ}
    (hA : WeightedOrderedDet3Nonnegative w A) {t : ℝ} (ht : 0 ≤ t) :
    WeightedOrderedDet3Nonnegative w (fun u ↦ commonLinearStep t (A u)) := by
  intro j₀ j₁ j₂ hj₀₁ hj₁₂
  rcases j₀ with _ | j₀
  · rcases j₁ with _ | j₁
    · omega
    rcases j₂ with _ | j₂
    · omega
    rw [weightedCoefficientMinor3_commonLinearStep_zero]
    have h₀ := hA 0 (j₁ + 1) (j₂ + 1) (by omega) (by omega)
    have h₁ := hA.nonneg_of_le (show 0 ≤ j₁ by omega) (show j₁ ≤ j₂ + 1 by omega)
    have h₂ := hA.nonneg_of_le (show 0 ≤ j₁ + 1 by omega) (show j₁ + 1 ≤ j₂ by omega)
    have h₃ := hA.nonneg_of_le (show 0 ≤ j₁ by omega) (show j₁ ≤ j₂ by omega)
    positivity
  · rcases j₁ with _ | j₁
    · omega
    rcases j₂ with _ | j₂
    · omega
    have h₀₁ : j₀ < j₁ := by omega
    have h₁₂ : j₁ < j₂ := by omega
    rw [weightedCoefficientMinor3_commonLinearStep_succ]
    have h₀ := hA (j₀ + 1) (j₁ + 1) (j₂ + 1) (by omega) (by omega)
    have h₁ := hA j₀ (j₁ + 1) (j₂ + 1) (by omega) (by omega)
    have h₂ := hA.nonneg_of_le (show j₀ + 1 ≤ j₁ by omega)
      (show j₁ ≤ j₂ + 1 by omega)
    have h₃ := hA.nonneg_of_le (show j₀ + 1 ≤ j₁ + 1 by omega)
      (show j₁ + 1 ≤ j₂ by omega)
    have h₄ := hA j₀ j₁ (j₂ + 1) h₀₁ (by omega)
    have h₅ := hA.nonneg_of_le (show j₀ ≤ j₁ + 1 by omega)
      (show j₁ + 1 ≤ j₂ by omega)
    have h₆ := hA.nonneg_of_le (show j₀ + 1 ≤ j₁ by omega)
      (show j₁ ≤ j₂ by omega)
    have h₇ := hA j₀ j₁ j₂ h₀₁ h₁₂
    positivity

/-- Coefficient rows associated with a finite weighted family of polynomial
triples. -/
def polynomialTripleCoefficients {s : Type*} (p : s → Fin 3 → ℝ[X]) :
    s → Fin 3 → ℕ → ℝ :=
  fun u i j ↦ (p u i).coeff j

private lemma coeff_mul_linear_zero_local (p : ℝ[X]) (t : ℝ) :
    (p * (1 + C t * X)).coeff 0 = p.coeff 0 := by simp

private lemma coeff_mul_linear_succ_local (p : ℝ[X]) (t : ℝ) (j : ℕ) :
    (p * (1 + C t * X)).coeff (j + 1) = p.coeff (j + 1) + t * p.coeff j := by
  rw [mul_add, mul_one, coeff_add, ← mul_assoc, coeff_mul_X, coeff_mul_C]
  ring

lemma polynomialTripleCoefficients_mul_linear {s : Type*}
    (p : s → Fin 3 → ℝ[X]) (t : ℝ) :
    polynomialTripleCoefficients (fun u i ↦ p u i * (1 + C t * X)) =
      fun u ↦ commonLinearStep t (polynomialTripleCoefficients p u) := by
  funext u i j
  rcases j with _ | j
  · exact coeff_mul_linear_zero_local _ _
  · exact coeff_mul_linear_succ_local _ _ _

private lemma factorPolynomial_succ_local {n : ℕ} (r : Fin (n + 1) → ℝ) :
    factorPolynomial r =
      factorPolynomial (fun i : Fin n ↦ r i.succ) * (1 + C (r 0) * X) := by
  rw [factorPolynomial, Fin.prod_univ_succ, factorPolynomial]
  ac_rfl

/-- The aggregate common-factor bridge, specialized to the products of
positive linear factors used by the root-deletion expansion. -/
theorem weightedPolynomialTriple_mul_factorPolynomial_nonnegative
    {s : Type*} [Fintype s] {n : ℕ} (w : s → ℝ)
    (p : s → Fin 3 → ℝ[X]) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hp : WeightedOrderedDet3Nonnegative w (polynomialTripleCoefficients p)) :
    WeightedOrderedDet3Nonnegative w
      (polynomialTripleCoefficients (fun u i ↦ p u i * factorPolynomial r)) := by
  induction n with
  | zero => simpa [factorPolynomial, polynomialTripleCoefficients] using hp
  | succ n ih =>
      rw [factorPolynomial_succ_local]
      simp_rw [← mul_assoc]
      rw [polynomialTripleCoefficients_mul_linear]
      exact (ih (fun i : Fin n ↦ r i.succ) (fun i ↦ hr i.succ)).commonLinearStep (hr 0)

private lemma factorPolynomialOn_insert_local {iota : Type*} [DecidableEq iota]
    (s : Finset iota) (r : iota → ℝ) (a : iota) (ha : a ∉ s) :
    factorPolynomialOn (insert a s) r =
      factorPolynomialOn s r * (1 + C (r a) * X) := by
  rw [factorPolynomialOn, Finset.prod_insert ha, factorPolynomialOn]
  exact mul_comm _ _

/-- The weighted common-factor bridge for an arbitrary finite factor set.
This is the form used for the root-deleted polynomial `f_U`. -/
theorem weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    {s iota : Type*} [Fintype s] (w : s → ℝ)
    (p : s → Fin 3 → ℝ[X]) (factors : Finset iota) (r : iota → ℝ)
    (hr : ∀ i ∈ factors, 0 ≤ r i)
    (hp : WeightedOrderedDet3Nonnegative w (polynomialTripleCoefficients p)) :
    WeightedOrderedDet3Nonnegative w
      (polynomialTripleCoefficients
        (fun u i ↦ p u i * factorPolynomialOn factors r)) := by
  classical
  induction factors using Finset.induction_on with
  | empty => simpa [factorPolynomialOn, polynomialTripleCoefficients] using hp
  | @insert a factors ha ih =>
      rw [factorPolynomialOn_insert_local factors r a ha]
      simp_rw [← mul_assoc]
      rw [polynomialTripleCoefficients_mul_linear]
      exact (ih (fun i hi ↦ hr i (Finset.mem_insert_of_mem hi))).commonLinearStep
        (hr a (Finset.mem_insert_self a factors))

/-! ## The four local `Phi` tables -/

abbrev LocalVec := ℕ → ℝ

def localOne : LocalVec
  | 0 => 1
  | _ + 1 => 0

def localLinear (a : ℝ) : LocalVec
  | 0 => 1
  | 1 => a
  | _ + 2 => 0

def localQuadratic (a b : ℝ) : LocalVec
  | 0 => 1
  | 1 => a + b
  | 2 => a * b
  | _ + 3 => 0

def localCubic (a b c : ℝ) : LocalVec
  | 0 => 1
  | 1 => a + b + c
  | 2 => a * b + a * c + b * c
  | 3 => a * b * c
  | _ + 4 => 0

def shiftOne (v : LocalVec) : LocalVec
  | 0 => 0
  | j + 1 => v j

def shiftTwo (v : LocalVec) : LocalVec
  | 0 => 0
  | 1 => 0
  | j + 2 => v j

def localMinor (p q r : LocalVec) (i j k : ℕ) : ℝ :=
  det3 (fun row col ↦ match row with
    | 0 => p col
    | 1 => q col
    | _ => r col) 0 1 2 i j k

def phiZero (i j k : ℕ) : ℝ :=
  localMinor localOne (shiftOne localOne) (shiftTwo localOne) i j k

def phiSingleton (a : ℝ) (i j k : ℕ) : ℝ :=
  3 * (1 + a) * localMinor (localLinear a) (shiftOne (localLinear a))
      (shiftTwo localOne) i j k
    + (1 + a) * localMinor (localLinear a) (shiftOne localOne)
      (shiftTwo (localLinear a)) i j k
    + 3 * (1 + a) ^ 2 * localMinor (localLinear a) (shiftOne localOne)
      (shiftTwo localOne) i j k

def phiPair (a b : ℝ) (i j k : ℕ) : ℝ :=
  2 * (1 + a) * (1 + b) *
      localMinor (localQuadratic a b) (shiftOne (localQuadratic a b))
        (shiftTwo localOne) i j k
    + 3 * (1 + a) * (1 + b) *
      localMinor (localQuadratic a b) (shiftOne (localLinear b))
        (shiftTwo (localLinear a)) i j k
    + 3 * (1 + b) * (1 + a) *
      localMinor (localQuadratic a b) (shiftOne (localLinear a))
        (shiftTwo (localLinear b)) i j k
    + 2 * (1 + a) ^ 2 * (1 + b) *
      localMinor (localQuadratic a b) (shiftOne (localLinear b))
        (shiftTwo localOne) i j k
    + 2 * (1 + b) ^ 2 * (1 + a) *
      localMinor (localQuadratic a b) (shiftOne (localLinear a))
        (shiftTwo localOne) i j k

def phiTriple (a b c : ℝ) (i j k : ℕ) : ℝ :=
  2 * (1 + a) * (1 + b) * (1 + c) *
      localMinor (localCubic a b c) (shiftOne (localQuadratic b c))
        (shiftTwo (localLinear a)) i j k
    + 2 * (1 + b) * (1 + a) * (1 + c) *
      localMinor (localCubic a b c) (shiftOne (localQuadratic a c))
        (shiftTwo (localLinear b)) i j k
    + 2 * (1 + c) * (1 + a) * (1 + b) *
      localMinor (localCubic a b c) (shiftOne (localQuadratic a b))
        (shiftTwo (localLinear c)) i j k

theorem phiZero_table :
    phiZero 0 1 2 = 1 ∧ phiZero 0 1 3 = 0 ∧
      phiZero 0 2 3 = 0 ∧ phiZero 1 2 3 = 0 := by
  norm_num [phiZero, localMinor, localOne, shiftOne, shiftTwo, det3]

theorem phiSingleton_table (a : ℝ) :
    phiSingleton a 0 1 2 = (1 + a) * (3 * a + 7) ∧
      phiSingleton a 0 1 3 = (1 + a) * a ∧
      phiSingleton a 0 2 3 = 0 ∧ phiSingleton a 1 2 3 = 0 := by
  norm_num [phiSingleton, localMinor, localOne, localLinear, shiftOne, shiftTwo, det3]
  repeat' apply And.intro
  all_goals ring

theorem phiPair_table (a b : ℝ) :
    phiPair a b 0 1 2 = 2 * (1 + a) * (1 + b) * (a + b + 6) ∧
      phiPair a b 0 1 3 = 3 * (1 + a) * (1 + b) * (a + b) ∧
      phiPair a b 0 2 3 = 4 * (1 + a) * (1 + b) * a * b ∧
      phiPair a b 1 2 3 = (1 + a) * (1 + b) * a * b * (a + b) := by
  norm_num [phiPair, localMinor, localOne, localLinear, localQuadratic,
    shiftOne, shiftTwo, det3]
  repeat' apply And.intro
  all_goals ring

theorem phiTriple_table (a b c : ℝ) :
    phiTriple a b c 0 1 2 = 6 * (1 + a) * (1 + b) * (1 + c) ∧
      phiTriple a b c 0 1 3 =
        2 * (1 + a) * (1 + b) * (1 + c) * (a + b + c) ∧
      phiTriple a b c 0 2 3 =
        2 * (1 + a) * (1 + b) * (1 + c) * (a * b + a * c + b * c) ∧
      phiTriple a b c 1 2 3 =
        6 * (1 + a) * (1 + b) * (1 + c) * a * b * c := by
  norm_num [phiTriple, localMinor, localLinear, localQuadratic, localCubic,
    shiftOne, shiftTwo, det3]
  repeat' apply And.intro
  all_goals ring

def SupportedThroughThree (v : LocalVec) : Prop := ∀ j, 4 ≤ j → v j = 0

lemma localOne_supported : SupportedThroughThree localOne := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [localOne] <;> omega

lemma localLinear_supported (a : ℝ) : SupportedThroughThree (localLinear a) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [localLinear] <;> omega

lemma localQuadratic_supported (a b : ℝ) : SupportedThroughThree (localQuadratic a b) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [localQuadratic] <;> omega

lemma localCubic_supported (a b c : ℝ) : SupportedThroughThree (localCubic a b c) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [localCubic] <;> omega

lemma shiftOne_localOne_supported : SupportedThroughThree (shiftOne localOne) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [shiftOne, localOne] <;> omega

lemma shiftOne_localLinear_supported (a : ℝ) :
    SupportedThroughThree (shiftOne (localLinear a)) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [shiftOne, localLinear] <;> omega

lemma shiftOne_localQuadratic_supported (a b : ℝ) :
    SupportedThroughThree (shiftOne (localQuadratic a b)) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [shiftOne, localQuadratic] <;> omega

lemma shiftTwo_localOne_supported : SupportedThroughThree (shiftTwo localOne) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [shiftTwo, localOne] <;> omega

lemma shiftTwo_localLinear_supported (a : ℝ) :
    SupportedThroughThree (shiftTwo (localLinear a)) := by
  intro j hj
  rcases j with _ | _ | _ | _ | j <;> simp [shiftTwo, localLinear] <;> omega

lemma localMinor_eq_zero_of_last {p q r : LocalVec} (hp : SupportedThroughThree p)
    (hq : SupportedThroughThree q) (hr : SupportedThroughThree r)
    (i j k : ℕ) (hk : 4 ≤ k) : localMinor p q r i j k = 0 := by
  have hp0 := hp k hk
  have hq0 := hq k hk
  have hr0 := hr k hk
  simp [localMinor, det3, hp0, hq0, hr0]

lemma phiZero_eq_zero_of_four_le (i j k : ℕ) (hk : 4 ≤ k) : phiZero i j k = 0 := by
  exact localMinor_eq_zero_of_last localOne_supported shiftOne_localOne_supported
    shiftTwo_localOne_supported i j k hk

lemma phiSingleton_eq_zero_of_four_le (a : ℝ) (i j k : ℕ) (hk : 4 ≤ k) :
    phiSingleton a i j k = 0 := by
  unfold phiSingleton
  rw [localMinor_eq_zero_of_last (localLinear_supported a)
      (shiftOne_localLinear_supported a) shiftTwo_localOne_supported i j k hk,
    localMinor_eq_zero_of_last (localLinear_supported a) shiftOne_localOne_supported
      (shiftTwo_localLinear_supported a) i j k hk,
    localMinor_eq_zero_of_last (localLinear_supported a) shiftOne_localOne_supported
      shiftTwo_localOne_supported i j k hk]
  ring

lemma phiPair_eq_zero_of_four_le (a b : ℝ) (i j k : ℕ) (hk : 4 ≤ k) :
    phiPair a b i j k = 0 := by
  unfold phiPair
  rw [localMinor_eq_zero_of_last (localQuadratic_supported a b)
      (shiftOne_localQuadratic_supported a b) shiftTwo_localOne_supported i j k hk,
    localMinor_eq_zero_of_last (localQuadratic_supported a b)
      (shiftOne_localLinear_supported b) (shiftTwo_localLinear_supported a) i j k hk,
    localMinor_eq_zero_of_last (localQuadratic_supported a b)
      (shiftOne_localLinear_supported a) (shiftTwo_localLinear_supported b) i j k hk,
    localMinor_eq_zero_of_last (localQuadratic_supported a b)
      (shiftOne_localLinear_supported b) shiftTwo_localOne_supported i j k hk,
    localMinor_eq_zero_of_last (localQuadratic_supported a b)
      (shiftOne_localLinear_supported a) shiftTwo_localOne_supported i j k hk]
  ring

lemma phiTriple_eq_zero_of_four_le (a b c : ℝ) (i j k : ℕ) (hk : 4 ≤ k) :
    phiTriple a b c i j k = 0 := by
  unfold phiTriple
  rw [localMinor_eq_zero_of_last (localCubic_supported a b c)
      (shiftOne_localQuadratic_supported b c) (shiftTwo_localLinear_supported a) i j k hk,
    localMinor_eq_zero_of_last (localCubic_supported a b c)
      (shiftOne_localQuadratic_supported a c) (shiftTwo_localLinear_supported b) i j k hk,
    localMinor_eq_zero_of_last (localCubic_supported a b c)
      (shiftOne_localQuadratic_supported a b) (shiftTwo_localLinear_supported c) i j k hk]
  ring

private lemma ordered_triple_through_three {i j k : ℕ}
    (hij : i < j) (hjk : j < k) (hk : k ≤ 3) :
    (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 3) := by
  omega

theorem phiZero_ordered_nonnegative {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ phiZero i j k := by
  by_cases hk : k ≤ 3
  · rcases ordered_triple_through_three hij hjk hk with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals have ht := phiZero_table
    all_goals norm_num [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]
  · rw [phiZero_eq_zero_of_four_le i j k (by omega)]

theorem phiSingleton_ordered_nonnegative (a : ℝ) (ha : 0 ≤ a)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) : 0 ≤ phiSingleton a i j k := by
  by_cases hk : k ≤ 3
  · rcases ordered_triple_through_three hij hjk hk with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals have ht := phiSingleton_table a
    all_goals simp only [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]
    all_goals positivity
  · rw [phiSingleton_eq_zero_of_four_le a i j k (by omega)]

theorem phiPair_ordered_nonnegative (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) : 0 ≤ phiPair a b i j k := by
  by_cases hk : k ≤ 3
  · rcases ordered_triple_through_three hij hjk hk with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals have ht := phiPair_table a b
    all_goals simp only [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]
    all_goals positivity
  · rw [phiPair_eq_zero_of_four_le a b i j k (by omega)]

theorem phiTriple_ordered_nonnegative (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ phiTriple a b c i j k := by
  by_cases hk : k ≤ 3
  · rcases ordered_triple_through_three hij hjk hk with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals have ht := phiTriple_table a b c
    all_goals simp only [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]
    all_goals positivity
  · rw [phiTriple_eq_zero_of_four_le a b c i j k (by omega)]

end LeanCo.EulerianTP3
