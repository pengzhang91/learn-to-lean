import LeanCo.EulerianTP3.LocalAlgebra
import LeanCo.EulerianTP3.RootDeletion

/-!
# Positive blocks for the solid third-order Eulerian minor

The root-deletion expansion groups its summands by a union `U` of at most
three deleted factors.  This file packages the four local `Phi` tables as
actual polynomial triples and proves that each block stays nonnegative
after multiplication by every factor outside `U`.
-/

namespace LeanCo.EulerianTP3

open scoped BigOperators Matrix
open Polynomial

/-! ## Turning the four-entry coefficient vectors into polynomials -/

/-- The polynomial represented by a local coefficient vector supported in
degrees at most three. -/
noncomputable def polynomialOfLocalVec (v : LocalVec) : ℝ[X] :=
  C (v 0) + C (v 1) * X + C (v 2) * X ^ 2 + C (v 3) * X ^ 3

theorem polynomialOfLocalVec_coeff (v : LocalVec) (hv : SupportedThroughThree v)
    (j : ℕ) : (polynomialOfLocalVec v).coeff j = v j := by
  rcases j with _ | _ | _ | _ | j
  · simp [polynomialOfLocalVec]
  · simp [polynomialOfLocalVec]
  · simp [polynomialOfLocalVec, coeff_X_pow]
  · simp [polynomialOfLocalVec, coeff_X_pow]
  · have hz := hv (j + 4) (by omega)
    simp [polynomialOfLocalVec, coeff_X_pow, hz]

@[simp] theorem polynomialOfLocalVec_localOne_coeff (j : ℕ) :
    (polynomialOfLocalVec localOne).coeff j = localOne j :=
  polynomialOfLocalVec_coeff localOne localOne_supported j

@[simp] theorem polynomialOfLocalVec_localLinear_coeff (a : ℝ) (j : ℕ) :
    (polynomialOfLocalVec (localLinear a)).coeff j = localLinear a j :=
  polynomialOfLocalVec_coeff (localLinear a) (localLinear_supported a) j

@[simp] theorem polynomialOfLocalVec_localQuadratic_coeff (a b : ℝ) (j : ℕ) :
    (polynomialOfLocalVec (localQuadratic a b)).coeff j = localQuadratic a b j :=
  polynomialOfLocalVec_coeff (localQuadratic a b) (localQuadratic_supported a b) j

@[simp] theorem polynomialOfLocalVec_localCubic_coeff (a b c : ℝ) (j : ℕ) :
    (polynomialOfLocalVec (localCubic a b c)).coeff j = localCubic a b c j :=
  polynomialOfLocalVec_coeff (localCubic a b c) (localCubic_supported a b c) j

@[simp] theorem polynomialOfLocalVec_shiftOne_localOne_coeff (j : ℕ) :
    (polynomialOfLocalVec (shiftOne localOne)).coeff j = shiftOne localOne j :=
  polynomialOfLocalVec_coeff _ shiftOne_localOne_supported j

@[simp] theorem polynomialOfLocalVec_shiftOne_localLinear_coeff (a : ℝ) (j : ℕ) :
    (polynomialOfLocalVec (shiftOne (localLinear a))).coeff j =
      shiftOne (localLinear a) j :=
  polynomialOfLocalVec_coeff _ (shiftOne_localLinear_supported a) j

@[simp] theorem polynomialOfLocalVec_shiftOne_localQuadratic_coeff
    (a b : ℝ) (j : ℕ) :
    (polynomialOfLocalVec (shiftOne (localQuadratic a b))).coeff j =
      shiftOne (localQuadratic a b) j :=
  polynomialOfLocalVec_coeff _ (shiftOne_localQuadratic_supported a b) j

@[simp] theorem polynomialOfLocalVec_shiftTwo_localOne_coeff (j : ℕ) :
    (polynomialOfLocalVec (shiftTwo localOne)).coeff j = shiftTwo localOne j :=
  polynomialOfLocalVec_coeff _ shiftTwo_localOne_supported j

@[simp] theorem polynomialOfLocalVec_shiftTwo_localLinear_coeff (a : ℝ) (j : ℕ) :
    (polynomialOfLocalVec (shiftTwo (localLinear a))).coeff j =
      shiftTwo (localLinear a) j :=
  polynomialOfLocalVec_coeff _ (shiftTwo_localLinear_supported a) j

theorem polynomialOfLocalVec_localOne : polynomialOfLocalVec localOne = 1 := by
  simp [polynomialOfLocalVec, localOne]

theorem polynomialOfLocalVec_localLinear (a : ℝ) :
    polynomialOfLocalVec (localLinear a) = 1 + C a * X := by
  simp [polynomialOfLocalVec, localLinear]

theorem polynomialOfLocalVec_localQuadratic (a b : ℝ) :
    polynomialOfLocalVec (localQuadratic a b) =
      (1 + C a * X) * (1 + C b * X) := by
  simp [polynomialOfLocalVec, localQuadratic]
  ring

theorem polynomialOfLocalVec_localCubic (a b c : ℝ) :
    polynomialOfLocalVec (localCubic a b c) =
      (1 + C a * X) * (1 + C b * X) * (1 + C c * X) := by
  simp [polynomialOfLocalVec, localCubic]
  ring

theorem polynomialOfLocalVec_shiftOne_localOne :
    polynomialOfLocalVec (shiftOne localOne) = X := by
  simp [polynomialOfLocalVec, shiftOne, localOne]

theorem polynomialOfLocalVec_shiftTwo_localOne :
    polynomialOfLocalVec (shiftTwo localOne) = X ^ 2 := by
  simp [polynomialOfLocalVec, shiftTwo, localOne]

theorem polynomialOfLocalVec_shiftOne_localLinear (a : ℝ) :
    polynomialOfLocalVec (shiftOne (localLinear a)) = X * (1 + C a * X) := by
  simp [polynomialOfLocalVec, shiftOne, localLinear]
  ring

theorem polynomialOfLocalVec_shiftTwo_localLinear (a : ℝ) :
    polynomialOfLocalVec (shiftTwo (localLinear a)) = X ^ 2 * (1 + C a * X) := by
  simp [polynomialOfLocalVec, shiftTwo, localLinear]
  ring

theorem polynomialOfLocalVec_shiftOne_localQuadratic (a b : ℝ) :
    polynomialOfLocalVec (shiftOne (localQuadratic a b)) =
      X * ((1 + C a * X) * (1 + C b * X)) := by
  simp [polynomialOfLocalVec, shiftOne, localQuadratic]
  ring

/-! ## Polynomial packages for the four union sizes -/

noncomputable def phiZeroWeights : Fin 1 → ℝ := ![1]

noncomputable def phiZeroTriples : Fin 1 → Fin 3 → ℝ[X] :=
  ![![polynomialOfLocalVec localOne,
      polynomialOfLocalVec (shiftOne localOne),
      polynomialOfLocalVec (shiftTwo localOne)]]

noncomputable def phiSingletonWeights (a : ℝ) : Fin 3 → ℝ :=
  ![3 * (1 + a), 1 + a, 3 * (1 + a) ^ 2]

noncomputable def phiSingletonTriples (a : ℝ) : Fin 3 → Fin 3 → ℝ[X] :=
  ![![polynomialOfLocalVec (localLinear a),
      polynomialOfLocalVec (shiftOne (localLinear a)),
      polynomialOfLocalVec (shiftTwo localOne)],
    ![polynomialOfLocalVec (localLinear a),
      polynomialOfLocalVec (shiftOne localOne),
      polynomialOfLocalVec (shiftTwo (localLinear a))],
    ![polynomialOfLocalVec (localLinear a),
      polynomialOfLocalVec (shiftOne localOne),
      polynomialOfLocalVec (shiftTwo localOne)]]

noncomputable def phiPairWeights (a b : ℝ) : Fin 5 → ℝ :=
  ![2 * (1 + a) * (1 + b),
    3 * (1 + a) * (1 + b),
    3 * (1 + b) * (1 + a),
    2 * (1 + a) ^ 2 * (1 + b),
    2 * (1 + b) ^ 2 * (1 + a)]

noncomputable def phiPairTriples (a b : ℝ) : Fin 5 → Fin 3 → ℝ[X] :=
  ![![polynomialOfLocalVec (localQuadratic a b),
      polynomialOfLocalVec (shiftOne (localQuadratic a b)),
      polynomialOfLocalVec (shiftTwo localOne)],
    ![polynomialOfLocalVec (localQuadratic a b),
      polynomialOfLocalVec (shiftOne (localLinear b)),
      polynomialOfLocalVec (shiftTwo (localLinear a))],
    ![polynomialOfLocalVec (localQuadratic a b),
      polynomialOfLocalVec (shiftOne (localLinear a)),
      polynomialOfLocalVec (shiftTwo (localLinear b))],
    ![polynomialOfLocalVec (localQuadratic a b),
      polynomialOfLocalVec (shiftOne (localLinear b)),
      polynomialOfLocalVec (shiftTwo localOne)],
    ![polynomialOfLocalVec (localQuadratic a b),
      polynomialOfLocalVec (shiftOne (localLinear a)),
      polynomialOfLocalVec (shiftTwo localOne)]]

noncomputable def phiTripleWeights (a b c : ℝ) : Fin 3 → ℝ :=
  ![2 * (1 + a) * (1 + b) * (1 + c),
    2 * (1 + b) * (1 + a) * (1 + c),
    2 * (1 + c) * (1 + a) * (1 + b)]

noncomputable def phiTripleTriples (a b c : ℝ) : Fin 3 → Fin 3 → ℝ[X] :=
  ![![polynomialOfLocalVec (localCubic a b c),
      polynomialOfLocalVec (shiftOne (localQuadratic b c)),
      polynomialOfLocalVec (shiftTwo (localLinear a))],
    ![polynomialOfLocalVec (localCubic a b c),
      polynomialOfLocalVec (shiftOne (localQuadratic a c)),
      polynomialOfLocalVec (shiftTwo (localLinear b))],
    ![polynomialOfLocalVec (localCubic a b c),
      polynomialOfLocalVec (shiftOne (localQuadratic a b)),
      polynomialOfLocalVec (shiftTwo (localLinear c))]]

theorem phiZero_weighted_eq (i j k : ℕ) :
    weightedCoefficientMinor3 phiZeroWeights
        (polynomialTripleCoefficients phiZeroTriples) i j k = phiZero i j k := by
  simp [weightedCoefficientMinor3, phiZeroWeights, phiZeroTriples,
    polynomialTripleCoefficients, coefficientMinor3, tripleCoefficientMatrix,
    phiZero, localMinor, det3]

theorem phiSingleton_weighted_eq (a : ℝ) (i j k : ℕ) :
    weightedCoefficientMinor3 (phiSingletonWeights a)
        (polynomialTripleCoefficients (phiSingletonTriples a)) i j k =
      phiSingleton a i j k := by
  simp [weightedCoefficientMinor3, phiSingletonWeights, phiSingletonTriples,
    polynomialTripleCoefficients, coefficientMinor3, tripleCoefficientMatrix,
    phiSingleton, localMinor, det3, Fin.sum_univ_succ]
  ring

theorem phiPair_weighted_eq (a b : ℝ) (i j k : ℕ) :
    weightedCoefficientMinor3 (phiPairWeights a b)
        (polynomialTripleCoefficients (phiPairTriples a b)) i j k =
      phiPair a b i j k := by
  simp [weightedCoefficientMinor3, phiPairWeights, phiPairTriples,
    polynomialTripleCoefficients, coefficientMinor3, tripleCoefficientMatrix,
    phiPair, localMinor, det3, Fin.sum_univ_succ]
  ring

theorem phiTriple_weighted_eq (a b c : ℝ) (i j k : ℕ) :
    weightedCoefficientMinor3 (phiTripleWeights a b c)
        (polynomialTripleCoefficients (phiTripleTriples a b c)) i j k =
      phiTriple a b c i j k := by
  simp [weightedCoefficientMinor3, phiTripleWeights, phiTripleTriples,
    polynomialTripleCoefficients, coefficientMinor3, tripleCoefficientMatrix,
    phiTriple, localMinor, det3, Fin.sum_univ_succ]
  ring

theorem phiZero_weighted_ordered_nonnegative :
    WeightedOrderedDet3Nonnegative phiZeroWeights
      (polynomialTripleCoefficients phiZeroTriples) := by
  intro i j k hij hjk
  rw [phiZero_weighted_eq]
  exact phiZero_ordered_nonnegative hij hjk

theorem phiSingleton_weighted_ordered_nonnegative (a : ℝ) (ha : 0 ≤ a) :
    WeightedOrderedDet3Nonnegative (phiSingletonWeights a)
      (polynomialTripleCoefficients (phiSingletonTriples a)) := by
  intro i j k hij hjk
  rw [phiSingleton_weighted_eq]
  exact phiSingleton_ordered_nonnegative a ha hij hjk

theorem phiPair_weighted_ordered_nonnegative (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    WeightedOrderedDet3Nonnegative (phiPairWeights a b)
      (polynomialTripleCoefficients (phiPairTriples a b)) := by
  intro i j k hij hjk
  rw [phiPair_weighted_eq]
  exact phiPair_ordered_nonnegative a b ha hb hij hjk

theorem phiTriple_weighted_ordered_nonnegative (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    WeightedOrderedDet3Nonnegative (phiTripleWeights a b c)
      (polynomialTripleCoefficients (phiTripleTriples a b c)) := by
  intro i j k hij hjk
  rw [phiTriple_weighted_eq]
  exact phiTriple_ordered_nonnegative a b c ha hb hc hij hjk

/-! ## Nonnegative blocks after the common undeleted factors -/

theorem phiZero_block_nonnegative {iota : Type*} (factors : Finset iota)
    (r : iota → ℝ) (hr : ∀ i ∈ factors, 0 ≤ r i) :
    WeightedOrderedDet3Nonnegative phiZeroWeights
      (polynomialTripleCoefficients
        (fun u row ↦ phiZeroTriples u row * factorPolynomialOn factors r)) :=
  weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    phiZeroWeights phiZeroTriples factors r hr phiZero_weighted_ordered_nonnegative

theorem phiSingleton_block_nonnegative {iota : Type*} (a : ℝ) (ha : 0 ≤ a)
    (factors : Finset iota) (r : iota → ℝ) (hr : ∀ i ∈ factors, 0 ≤ r i) :
    WeightedOrderedDet3Nonnegative (phiSingletonWeights a)
      (polynomialTripleCoefficients
        (fun u row ↦ phiSingletonTriples a u row * factorPolynomialOn factors r)) :=
  weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    (phiSingletonWeights a) (phiSingletonTriples a) factors r hr
      (phiSingleton_weighted_ordered_nonnegative a ha)

theorem phiPair_block_nonnegative {iota : Type*} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (factors : Finset iota) (r : iota → ℝ) (hr : ∀ i ∈ factors, 0 ≤ r i) :
    WeightedOrderedDet3Nonnegative (phiPairWeights a b)
      (polynomialTripleCoefficients
        (fun u row ↦ phiPairTriples a b u row * factorPolynomialOn factors r)) :=
  weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    (phiPairWeights a b) (phiPairTriples a b) factors r hr
      (phiPair_weighted_ordered_nonnegative a b ha hb)

theorem phiTriple_block_nonnegative {iota : Type*} (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (factors : Finset iota) (r : iota → ℝ) (hr : ∀ i ∈ factors, 0 ≤ r i) :
    WeightedOrderedDet3Nonnegative (phiTripleWeights a b c)
      (polynomialTripleCoefficients
        (fun u row ↦ phiTripleTriples a b c u row * factorPolynomialOn factors r)) :=
  weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    (phiTripleWeights a b c) (phiTripleTriples a b c) factors r hr
      (phiTriple_weighted_ordered_nonnegative a b c ha hb hc)

/-! ## Strict empty-union term and the three-row split -/

theorem coefficientMatrix_X_pow_mul (p : ℝ[X]) :
    coefficientMatrix (fun i ↦ X ^ i * p) = upperToeplitz p := by
  funext i j
  simp [coefficientMatrix, upperToeplitz, coeff_X_pow_mul']

theorem phiZero_fullFactor_eq_toeplitz {n : ℕ} (r : Fin n → ℝ)
    (i j k : ℕ) :
    weightedCoefficientMinor3 phiZeroWeights
        (polynomialTripleCoefficients
          (fun u row ↦ phiZeroTriples u row * factorPolynomial r)) i j k =
      det3 (upperToeplitz (factorPolynomial r)) 0 1 2 i j k := by
  rw [← coefficientMatrix_X_pow_mul (factorPolynomial r)]
  simp [weightedCoefficientMinor3, phiZeroWeights, phiZeroTriples,
    coefficientMinor3, polynomialOfLocalVec_localOne,
    polynomialOfLocalVec_shiftOne_localOne,
    polynomialOfLocalVec_shiftTwo_localOne, Fin.sum_univ_succ]
  simp [det3, tripleCoefficientMatrix, polynomialTripleCoefficients, coefficientMatrix]

/-- The `U = ∅` contribution is strictly positive on every relevant
consecutive column triple.  This replaces the Schur-function argument in
the paper. -/
theorem phiZero_fullFactor_consecutive_pos {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (k : ℕ) (hk : k ≤ n) :
    0 < weightedCoefficientMinor3 phiZeroWeights
      (polynomialTripleCoefficients
        (fun u row ↦ phiZeroTriples u row * factorPolynomial r))
      k (k + 1) (k + 2) := by
  rw [phiZero_fullFactor_eq_toeplitz]
  exact factorPolynomial_upperToeplitz_det3_consecutive_pos r hr k hk

/-- Three polynomial rows viewed as a coefficient matrix. -/
def threePolynomialRows (p q r : ℝ[X]) : ℕ → ℝ[X]
  | 0 => p
  | 1 => q
  | _ => r

/-- The coefficient determinant of three polynomials in the selected
columns. -/
def polynomialMinor3 (p q r : ℝ[X]) (i j k : ℕ) : ℝ :=
  det3 (coefficientMatrix (threePolynomialRows p q r)) 0 1 2 i j k

/-- The elementary row operations behind equation (3.7) of the paper. -/
theorem polynomialMinor3_three_row_split (P V₁ V₂ V₃ : ℝ[X]) (i j k : ℕ) :
    polynomialMinor3 P (P + V₁) (P + 3 * V₁ + V₂ + V₃) i j k =
      polynomialMinor3 P V₁ V₂ i j k + polynomialMinor3 P V₁ V₃ i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

/-! ## The first summand `D(P,V₁,V₂)` -/

def firstLocalMiddle (a : ℝ) : LocalVec := fun j ↦ (1 + a) * shiftOne localOne j

def firstLocalPhi (a : ℝ) (i j k : ℕ) : ℝ :=
  localMinor (localLinear a) (firstLocalMiddle a)
    (shiftOne (localLinear a)) i j k

theorem firstLocalPhi_table (a : ℝ) :
    firstLocalPhi a 0 1 2 = a * (1 + a) ∧
      firstLocalPhi a 0 1 3 = 0 ∧
      firstLocalPhi a 0 2 3 = 0 ∧ firstLocalPhi a 1 2 3 = 0 := by
  norm_num [firstLocalPhi, firstLocalMiddle, localMinor, localLinear,
    localOne, shiftOne, det3]
  ring

lemma firstLocalMiddle_supported (a : ℝ) : SupportedThroughThree (firstLocalMiddle a) := by
  intro j hj
  rw [firstLocalMiddle, shiftOne_localOne_supported j hj]
  ring

lemma firstLocalPhi_eq_zero_of_four_le (a : ℝ) (i j k : ℕ) (hk : 4 ≤ k) :
    firstLocalPhi a i j k = 0 :=
  localMinor_eq_zero_of_last (localLinear_supported a) (firstLocalMiddle_supported a)
    (shiftOne_localLinear_supported a) i j k hk

theorem firstLocalPhi_ordered_nonnegative (a : ℝ) (ha : 0 ≤ a)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) : 0 ≤ firstLocalPhi a i j k := by
  by_cases hk : k ≤ 3
  · have hcases :
        (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
          (i = 0 ∧ j = 2 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 3) := by
        omega
    rcases hcases with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals have ht := firstLocalPhi_table a
    all_goals simp only [ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]
    all_goals positivity
  · rw [firstLocalPhi_eq_zero_of_four_le a i j k (by omega)]

noncomputable def firstBlockWeights : Fin 1 → ℝ := ![1]

noncomputable def firstBlockTriples (a : ℝ) : Fin 1 → Fin 3 → ℝ[X] :=
  ![![polynomialOfLocalVec (localLinear a),
      polynomialOfLocalVec (firstLocalMiddle a),
      polynomialOfLocalVec (shiftOne (localLinear a))]]

lemma polynomialOfLocalVec_firstLocalMiddle_coeff (a : ℝ) (j : ℕ) :
    (polynomialOfLocalVec (firstLocalMiddle a)).coeff j = firstLocalMiddle a j :=
  polynomialOfLocalVec_coeff _ (firstLocalMiddle_supported a) j

theorem firstBlock_weighted_eq (a : ℝ) (i j k : ℕ) :
    weightedCoefficientMinor3 firstBlockWeights
        (polynomialTripleCoefficients (firstBlockTriples a)) i j k =
      firstLocalPhi a i j k := by
  simp [weightedCoefficientMinor3, firstBlockWeights, firstBlockTriples,
    polynomialTripleCoefficients, coefficientMinor3, tripleCoefficientMatrix,
    polynomialOfLocalVec_firstLocalMiddle_coeff, firstLocalPhi, localMinor, det3]

theorem firstBlock_weighted_ordered_nonnegative (a : ℝ) (ha : 0 ≤ a) :
    WeightedOrderedDet3Nonnegative firstBlockWeights
      (polynomialTripleCoefficients (firstBlockTriples a)) := by
  intro i j k hij hjk
  rw [firstBlock_weighted_eq]
  exact firstLocalPhi_ordered_nonnegative a ha hij hjk

/-- Every individual root-deletion block in the first summand is
nonnegative after restoring its common undeleted factors. -/
theorem firstBlock_nonnegative {iota : Type*} (a : ℝ) (ha : 0 ≤ a)
    (factors : Finset iota) (r : iota → ℝ) (hr : ∀ i ∈ factors, 0 ≤ r i) :
    WeightedOrderedDet3Nonnegative firstBlockWeights
      (polynomialTripleCoefficients
        (fun u row ↦ firstBlockTriples a u row * factorPolynomialOn factors r)) :=
  weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    firstBlockWeights (firstBlockTriples a) factors r hr
      (firstBlock_weighted_ordered_nonnegative a ha)

theorem polynomialOfLocalVec_firstLocalMiddle (a : ℝ) :
    polynomialOfLocalVec (firstLocalMiddle a) = C (1 + a) * X := by
  simp [polynomialOfLocalVec, firstLocalMiddle, shiftOne, localOne]

theorem polynomialMinor3_add_middle (P Q₁ Q₂ R : ℝ[X]) (i j k : ℕ) :
    polynomialMinor3 P (Q₁ + Q₂) R i j k =
      polynomialMinor3 P Q₁ R i j k + polynomialMinor3 P Q₂ R i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

theorem polynomialMinor3_sum_middle {iota : Type*} (s : Finset iota)
    (P R : ℝ[X]) (Q : iota → ℝ[X]) (i j k : ℕ) :
    polynomialMinor3 P (∑ u ∈ s, Q u) R i j k =
      ∑ u ∈ s, polynomialMinor3 P (Q u) R i j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, polynomialMinor3_add_middle, ih, Finset.sum_insert ha]

theorem firstBlockTerm_eq {n : ℕ} (r : Fin n → ℝ) (u : Fin n)
    (i j k : ℕ) :
    weightedCoefficientMinor3 firstBlockWeights
        (polynomialTripleCoefficients
          (fun t row ↦ firstBlockTriples (r u) t row *
            factorPolynomialOn (Finset.univ.erase u) r)) i j k =
      polynomialMinor3 (factorPolynomial r)
        (X * (C (1 + r u) * deletedFactorPolynomial r u))
        (X * factorPolynomial r) i j k := by
  have hP := factorPolynomial_eq_linear_mul_deletedFactor r u
  have hf := deletedFactorPolynomial_eq_factorPolynomialOn r u
  have hrow₀ :
      polynomialOfLocalVec (localLinear (r u)) *
          factorPolynomialOn (Finset.univ.erase u) r = factorPolynomial r := by
    rw [polynomialOfLocalVec_localLinear, ← hf, hP]
  have hrow₁ :
      polynomialOfLocalVec (firstLocalMiddle (r u)) *
          factorPolynomialOn (Finset.univ.erase u) r =
        X * (C (1 + r u) * deletedFactorPolynomial r u) := by
    rw [polynomialOfLocalVec_firstLocalMiddle, ← hf]
    ring
  have hrow₂ :
      polynomialOfLocalVec (shiftOne (localLinear (r u))) *
          factorPolynomialOn (Finset.univ.erase u) r = X * factorPolynomial r := by
    rw [polynomialOfLocalVec_shiftOne_localLinear, ← hf, hP]
    ring
  simp [weightedCoefficientMinor3, firstBlockWeights, firstBlockTriples,
    coefficientMinor3, polynomialTripleCoefficients, hrow₀, hrow₁, hrow₂,
    polynomialMinor3, threePolynomialRows, tripleCoefficientMatrix, coefficientMatrix]
  simp [det3, tripleCoefficientMatrix, polynomialTripleCoefficients,
    coefficientMatrix, threePolynomialRows, hrow₀, hrow₁, hrow₂]

theorem firstSummand_eq_sum_blocks {n : ℕ} (r : Fin n → ℝ) (i j k : ℕ) :
    polynomialMinor3 (factorPolynomial r) (X * G1 r) (X * factorPolynomial r) i j k =
      ∑ u, weightedCoefficientMinor3 firstBlockWeights
        (polynomialTripleCoefficients
          (fun t row ↦ firstBlockTriples (r u) t row *
            factorPolynomialOn (Finset.univ.erase u) r)) i j k := by
  rw [G1]
  rw [Finset.mul_sum]
  rw [polynomialMinor3_sum_middle]
  apply Finset.sum_congr rfl
  intro u hu
  rw [firstBlockTerm_eq]

/-- The first summand in the three-row split is nonnegative for every
ordered column triple. -/
theorem firstSummand_nonnegative {n : ℕ} (r : Fin n → ℝ) (hr : ∀ u, 0 ≤ r u)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ polynomialMinor3 (factorPolynomial r) (X * G1 r)
      (X * factorPolynomial r) i j k := by
  rw [firstSummand_eq_sum_blocks]
  apply Finset.sum_nonneg
  intro u hu
  exact firstBlock_nonnegative (r u) (hr u) (Finset.univ.erase u) r
    (fun v hv ↦ hr v) i j k hij hjk

end LeanCo.EulerianTP3
