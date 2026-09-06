import LeanCo.EulerianTP3.GeneralizedLocalAlgebra
import LeanCo.EulerianTP3.SolidThreeRegroup
import LeanCo.EulerianTP3.GeneralizedRows

/-!
# The generalized solid three-row minor

This file carries out the global root-deletion regrouping in Section 4 of
arXiv:2608.29224.  It starts with an arbitrary product of positive factors,
applies two consecutive parameterized Eulerian differential steps, and proves
strict positivity of every relevant consecutive three-column coefficient
minor.
-/

namespace LeanCo.EulerianTP3

open scoped BigOperators Matrix
open Polynomial

private lemma C_two_generalized : C (2 : ℝ) = (2 : ℝ[X]) := by
  exact (map_ofNat (C : ℝ →+* ℝ[X]) 2).symm.symm

/-! ## The two differential steps and their root-deletion normal forms -/

/-- One parameterized Eulerian differential step at row index `n`. -/
noncomputable def generalizedEulerianStep (n : ℕ) (a t : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (1 + C ((n : ℝ) * t + a) * X) * p +
    C t * X * (1 - X) * p.derivative

/-- The polynomial denoted by `V` in the proof of Theorem 4.1. -/
noncomputable def generalizedThreeV {n : ℕ} (a t : ℝ) (r : Fin n → ℝ) : ℝ[X] :=
  C a * factorPolynomial r + C t * G1 r

/-- The polynomial denoted by `Q` in the proof of Theorem 4.1. -/
noncomputable def generalizedThreeQ {n : ℕ} (a b t : ℝ)
    (r : Fin n → ℝ) : ℝ[X] :=
  C (a * b) * factorPolynomial r +
    C (t * (a + b + t)) * G1 r + C (2 * t ^ 2) * G2 r

/-- Root-deletion form of the first parameterized differential step. -/
theorem generalizedEulerianStep_factorPolynomial_formula {n : ℕ}
    (r : Fin n → ℝ) (a t : ℝ) :
    generalizedEulerianStep n a t (factorPolynomial r) =
      factorPolynomial r + X * generalizedThreeV a t r := by
  rw [generalizedEulerianStep, generalizedThreeV,
    G1_eq_nat_mul_factorPolynomial_add_derivative]
  have hC : C ((n : ℝ) * t + a) = C t * C (n : ℝ) + C a := by
    rw [map_add, map_mul]
    ring
  rw [hC]
  ring

/-- Root-deletion form after the second consecutive parameterized step. -/
theorem generalizedEulerianStep_second_formula {n : ℕ}
    (r : Fin n → ℝ) (a b t : ℝ) :
    generalizedEulerianStep (n + 1) b t
        (generalizedEulerianStep n a t (factorPolynomial r)) =
      factorPolynomial r + C (t + 2) * X * generalizedThreeV a t r +
        C (b - a + t) * X * factorPolynomial r +
          X ^ 2 * generalizedThreeQ a b t r := by
  rw [generalizedEulerianStep_factorPolynomial_formula]
  cases n with
  | zero =>
      simp [generalizedEulerianStep, generalizedThreeV, generalizedThreeQ,
        factorPolynomial, G1, G2, deletedFactorPolynomial,
        deletedPairFactorPolynomial, C_two_generalized]
      ring
  | succ n =>
      have hPder :
          (1 - X) * (factorPolynomial r).derivative =
            G1 r - C (n + 1 : ℝ) * factorPolynomial r := by
        rw [G1_eq_nat_mul_factorPolynomial_add_derivative]
        norm_num [Nat.cast_add]
      have hGder :
          (1 - X) * (G1 r).derivative =
            C (2 : ℝ) * G2 r - C (n : ℝ) * G1 r := by
        rw [two_mul_G2_eq_nat_sub_one_mul_G1_add_derivative]
        simp only [Nat.add_sub_cancel]
        ring
      have hder :
          (factorPolynomial r + X * generalizedThreeV a t r).derivative =
            (factorPolynomial r).derivative + generalizedThreeV a t r +
              X * (C a * (factorPolynomial r).derivative +
                C t * (G1 r).derivative) := by
        simp [generalizedThreeV]
        ring
      rw [generalizedEulerianStep, hder]
      unfold generalizedThreeV generalizedThreeQ
      have hcast : C ((((n + 1 : ℕ) + 1 : ℕ) : ℝ) * t + b) =
          C (((n + 1 : ℕ) : ℝ) * t + t + b) := by
        congr 1
        push_cast
        ring
      rw [hcast]
      simp only [map_add, map_sub, map_mul, map_pow, C_two_generalized]
        at hPder hGder ⊢
      norm_num [Nat.cast_add] at hPder hGder ⊢
      linear_combination
        (C t * X * (1 + C a * X)) * hPder +
          (C t ^ 2 * X ^ 2) * hGder

/-! ## Determinant row operations -/

/-- The row split used after writing the two steps in root-deletion form. -/
theorem polynomialMinor3_parameterized_three_row_split
    (P V W Z : ℝ[X]) (c : ℝ) (i j k : ℕ) :
    polynomialMinor3 P (P + V) (P + C c * V + W + Z) i j k =
      polynomialMinor3 P V W i j k + polynomialMinor3 P V Z i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

theorem polynomialMinor3_C_mul_middle_generalized
    (P Q R : ℝ[X]) (c : ℝ) (i j k : ℕ) :
    polynomialMinor3 P (C c * Q) R i j k =
      c * polynomialMinor3 P Q R i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

theorem polynomialMinor3_C_mul_right_generalized
    (P Q R : ℝ[X]) (c : ℝ) (i j k : ℕ) :
    polynomialMinor3 P Q (C c * R) i j k =
      c * polynomialMinor3 P Q R i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

@[simp] theorem polynomialMinor3_same_last_two_generalized
    (P Q : ℝ[X]) (i j k : ℕ) :
    polynomialMinor3 P Q Q i j k = 0 := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

/-- The first determinant after the row split is exactly the paper's
`t * (b-a+t)` multiple. -/
theorem generalizedThree_first_split_eq {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (i j k : ℕ) :
    polynomialMinor3 (factorPolynomial r)
        (X * generalizedThreeV a t r)
        (C (b - a + t) * X * factorPolynomial r) i j k =
      t * (b - a + t) *
        polynomialMinor3 (factorPolynomial r) (X * G1 r)
          (X * factorPolynomial r) i j k := by
  have hmiddle : X * generalizedThreeV a t r =
      C a * (X * factorPolynomial r) + C t * (X * G1 r) := by
    simp [generalizedThreeV]
    ring
  have hright : C (b - a + t) * X * factorPolynomial r =
      C (b - a + t) * (X * factorPolynomial r) := by ring
  rw [hmiddle, hright, polynomialMinor3_add_middle,
    polynomialMinor3_C_mul_middle_generalized,
    polynomialMinor3_C_mul_middle_generalized,
    polynomialMinor3_C_mul_right_generalized,
    polynomialMinor3_C_mul_right_generalized]
  simp
  ring

/-! ## The strictly positive empty-union block -/

theorem generalizedPhiZero_fullFactor_eq_toeplitz {n : ℕ}
    (r : Fin n → ℝ) (a b t : ℝ) (i j k : ℕ) :
    weightedCoefficientMinor3 (generalizedPhiZeroWeights a b t)
        (polynomialTripleCoefficients
          (fun q row ↦ phiZeroTriples q row * factorPolynomial r)) i j k =
      a ^ 2 * b * det3 (upperToeplitz (factorPolynomial r)) 0 1 2 i j k := by
  calc
    weightedCoefficientMinor3 (generalizedPhiZeroWeights a b t)
        (polynomialTripleCoefficients
          (fun q row ↦ phiZeroTriples q row * factorPolynomial r)) i j k =
        a ^ 2 * b *
          weightedCoefficientMinor3 phiZeroWeights
            (polynomialTripleCoefficients
              (fun q row ↦ phiZeroTriples q row * factorPolynomial r)) i j k := by
            have hw : generalizedPhiZeroWeights a b t (0 : Fin 1) = a ^ 2 * b := by
              change generalizedMu a t 0 * generalizedNu a b t 0 = a ^ 2 * b
              simp
              ring
            have ho : phiZeroWeights (0 : Fin 1) = 1 := by rfl
            unfold weightedCoefficientMinor3
            rw [Fin.sum_univ_one, Fin.sum_univ_one]
            rw [hw, ho]
            ring
    _ = a ^ 2 * b *
        det3 (upperToeplitz (factorPolynomial r)) 0 1 2 i j k := by
          rw [phiZero_fullFactor_eq_toeplitz]

/-- The `U = empty` term supplies strict positivity; all other union blocks
only need to be nonnegative. -/
theorem generalizedPhiZero_fullFactor_consecutive_pos {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (k : ℕ) (hk : k ≤ n) :
    0 < weightedCoefficientMinor3 (generalizedPhiZeroWeights a b t)
      (polynomialTripleCoefficients
        (fun q row ↦ phiZeroTriples q row * factorPolynomial r))
      k (k + 1) (k + 2) := by
  rw [generalizedPhiZero_fullFactor_eq_toeplitz]
  exact mul_pos (mul_pos (sq_pos_of_pos ha) hb)
    (factorPolynomial_upperToeplitz_det3_consecutive_pos r hr k hk)

/-! ## Global union blocks -/

/-- The empty-union contribution to `D(P, X V, X^2 Q)`. -/
noncomputable def generalizedSecondZeroBlock {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (i j k : ℕ) : ℝ :=
  weightedCoefficientMinor3 (generalizedPhiZeroWeights a b t)
    (polynomialTripleCoefficients
      (fun q row ↦ phiZeroTriples q row * factorPolynomial r)) i j k

/-- The contribution whose union of deleted roots is `{u}`. -/
noncomputable def generalizedSecondSingletonBlock {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (u : Fin n) (i j k : ℕ) : ℝ :=
  weightedCoefficientMinor3 (generalizedPhiSingletonWeights a b t (r u))
    (polynomialTripleCoefficients
      (fun q row ↦ phiSingletonTriples (r u) q row *
        factorPolynomialOn (Finset.univ.erase u) r)) i j k

/-- The contribution whose union of deleted roots is `{u,v}`. -/
noncomputable def generalizedSecondPairBlock {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (u v : Fin n) (i j k : ℕ) : ℝ :=
  weightedCoefficientMinor3 (generalizedPhiPairWeights a b t (r u) (r v))
    (polynomialTripleCoefficients
      (fun q row ↦ phiPairTriples (r u) (r v) q row *
        factorPolynomialOn ((Finset.univ.erase u).erase v) r)) i j k

/-- The contribution whose union of deleted roots is `{u,v,w}`. -/
noncomputable def generalizedSecondTripleBlock {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (u v w : Fin n) (i j k : ℕ) : ℝ :=
  weightedCoefficientMinor3
    (generalizedPhiTripleWeights a b t (r u) (r v) (r w))
    (polynomialTripleCoefficients
      (fun q row ↦ phiTripleTriples (r u) (r v) (r w) q row *
        factorPolynomialOn (((Finset.univ.erase u).erase v).erase w) r)) i j k

private theorem generalized_coefficientMinor3_polynomialTriple_apply
    {α : Type*} (p : α → Fin 3 → ℝ[X]) (q : α) (i j k : ℕ) :
    coefficientMinor3 (polynomialTripleCoefficients p q) i j k =
      polynomialMinor3 (p q 0) (p q 1) (p q 2) i j k := by
  simp [coefficientMinor3, polynomialTripleCoefficients, polynomialMinor3,
    tripleCoefficientMatrix, threePolynomialRows, coefficientMatrix, det3]

theorem generalizedSecondZeroBlock_eq {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (i j k : ℕ) :
    generalizedSecondZeroBlock r a b t i j k =
      a ^ 2 * b * polynomialMinor3 (factorPolynomial r)
        (X * factorPolynomial r) (X ^ 2 * factorPolynomial r) i j k := by
  rw [generalizedSecondZeroBlock,
    generalizedPhiZero_fullFactor_eq_toeplitz]
  rw [← coefficientMatrix_X_pow_mul (factorPolynomial r)]
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]

theorem generalizedSecondSingletonBlock_eq {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (u : Fin n) (i j k : ℕ) :
    generalizedSecondSingletonBlock r a b t u i j k =
      a * t * (a + b + t) * (1 + r u) *
        polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
          (X ^ 2 * deletedFactorPolynomial r u) i j k
      + t * (a * b) * (1 + r u) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
          (X ^ 2 * factorPolynomial r) i j k
      + t ^ 2 * (a + b + t) * (1 + r u) ^ 2 *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
          (X ^ 2 * deletedFactorPolynomial r u) i j k := by
  have hP := factorPolynomial_eq_linear_mul_deletedFactor r u
  have hf := deletedFactorPolynomial_eq_factorPolynomialOn r u
  have hrow₀ :
      polynomialOfLocalVec (localLinear (r u)) *
          factorPolynomialOn (Finset.univ.erase u) r = factorPolynomial r := by
    rw [polynomialOfLocalVec_localLinear, ← hf, hP]
  have hrow₁ :
      polynomialOfLocalVec (shiftOne (localLinear (r u))) *
          factorPolynomialOn (Finset.univ.erase u) r = X * factorPolynomial r := by
    rw [polynomialOfLocalVec_shiftOne_localLinear, ← hf, hP]
    ring
  have hrow₁' :
      polynomialOfLocalVec (shiftOne localOne) *
          factorPolynomialOn (Finset.univ.erase u) r =
        X * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftOne_localOne, ← hf]
  have hrow₂ :
      polynomialOfLocalVec (shiftTwo (localLinear (r u))) *
          factorPolynomialOn (Finset.univ.erase u) r = X ^ 2 * factorPolynomial r := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, ← hf, hP]
    ring
  have hrow₂' :
      polynomialOfLocalVec (shiftTwo localOne) *
          factorPolynomialOn (Finset.univ.erase u) r =
        X ^ 2 * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftTwo_localOne, ← hf]
  have hrow₀r := hrow₀
  have hrow₁r := hrow₁
  have hrow₁r' := hrow₁'
  have hrow₂r := hrow₂
  have hrow₂r' := hrow₂'
  rw [mul_comm] at hrow₀r hrow₁r hrow₁r' hrow₂r hrow₂r'
  simp [generalizedSecondSingletonBlock, weightedCoefficientMinor3,
    generalizedPhiSingletonWeights, phiSingletonTriples,
    generalized_coefficientMinor3_polynomialTriple_apply,
    hrow₀, hrow₁, hrow₁', hrow₂, hrow₂', hrow₀r, hrow₁r,
    hrow₁r', hrow₂r, hrow₂r', Fin.sum_univ_succ]
  ring

theorem generalizedSecondPairBlock_eq {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (u v : Fin n) (huv : u ≠ v) (i j k : ℕ) :
    generalizedSecondPairBlock r a b t u v i j k =
      2 * a * t ^ 2 * (1 + r u) * (1 + r v) *
        polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
          (X ^ 2 * deletedPairFactorPolynomial r u v) i j k
      + t ^ 2 * (a + b + t) * (1 + r u) * (1 + r v) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
          (X ^ 2 * deletedFactorPolynomial r v) i j k
      + t ^ 2 * (a + b + t) * (1 + r v) * (1 + r u) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r v)
          (X ^ 2 * deletedFactorPolynomial r u) i j k
      + 2 * t ^ 3 * (1 + r u) ^ 2 * (1 + r v) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
          (X ^ 2 * deletedPairFactorPolynomial r u v) i j k
      + 2 * t ^ 3 * (1 + r v) ^ 2 * (1 + r u) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r v)
          (X ^ 2 * deletedPairFactorPolynomial r u v) i j k := by
  have hpair := deletedPairFactorPolynomial_eq_factorPolynomialOn r u v
  have hP := factorPolynomial_eq_linear_mul_linear_mul_deletedPair r u v huv
  have hfu := deletedFactorPolynomial_eq_linear_mul_deletedPair r u v huv
  have hfvu := deletedFactorPolynomial_eq_linear_mul_deletedPair r v u huv.symm
  have hcomm := deletedPairFactorPolynomial_comm r v u
  have hfv : deletedFactorPolynomial r v =
      (1 + C (r u) * X) * deletedPairFactorPolynomial r u v := by
    rw [hfvu, hcomm]
  have hrow₀ :
      polynomialOfLocalVec (localQuadratic (r u) (r v)) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r = factorPolynomial r := by
    rw [polynomialOfLocalVec_localQuadratic, ← hpair, hP]
  have hrow₁ :
      polynomialOfLocalVec (shiftOne (localQuadratic (r u) (r v))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X * factorPolynomial r := by
    rw [polynomialOfLocalVec_shiftOne_localQuadratic, ← hpair, hP]
    ring
  have hrow₁u :
      polynomialOfLocalVec (shiftOne (localLinear (r v))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftOne_localLinear, ← hpair, hfu]
    ring
  have hrow₁v :
      polynomialOfLocalVec (shiftOne (localLinear (r u))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X * deletedFactorPolynomial r v := by
    rw [polynomialOfLocalVec_shiftOne_localLinear, ← hpair, hfv]
    ring
  have hrow₂pair :
      polynomialOfLocalVec (shiftTwo localOne) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X ^ 2 * deletedPairFactorPolynomial r u v := by
    rw [polynomialOfLocalVec_shiftTwo_localOne, ← hpair]
  have hrow₂u :
      polynomialOfLocalVec (shiftTwo (localLinear (r v))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X ^ 2 * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, ← hpair, hfu]
    ring
  have hrow₂v :
      polynomialOfLocalVec (shiftTwo (localLinear (r u))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X ^ 2 * deletedFactorPolynomial r v := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, ← hpair, hfv]
    ring
  simp [generalizedSecondPairBlock, weightedCoefficientMinor3,
    generalizedPhiPairWeights, phiPairTriples,
    generalized_coefficientMinor3_polynomialTriple_apply,
    hrow₀, hrow₁, hrow₁u, hrow₁v, hrow₂pair, hrow₂u, hrow₂v,
    Fin.sum_univ_succ]
  ring

private lemma generalized_factorPolynomialOn_eq_linear_mul_erase
    {α : Type*} [DecidableEq α] (r : α → ℝ) (s : Finset α)
    {u : α} (hu : u ∈ s) :
    factorPolynomialOn s r =
      (1 + C (r u) * X) * factorPolynomialOn (s.erase u) r := by
  simpa [factorPolynomialOn] using
    (Finset.mul_prod_erase s (fun v ↦ (1 + C (r v) * X)) hu).symm

theorem generalizedSecondTripleBlock_eq {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (u v w : Fin n)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (i j k : ℕ) :
    generalizedSecondTripleBlock r a b t u v w i j k =
      2 * t ^ 3 * (1 + r u) * (1 + r v) * (1 + r w) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
          (X ^ 2 * deletedPairFactorPolynomial r v w) i j k
      + 2 * t ^ 3 * (1 + r v) * (1 + r u) * (1 + r w) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r v)
          (X ^ 2 * deletedPairFactorPolynomial r u w) i j k
      + 2 * t ^ 3 * (1 + r w) * (1 + r u) * (1 + r v) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r w)
          (X ^ 2 * deletedPairFactorPolynomial r u v) i j k := by
  let outside := ((Finset.univ.erase u).erase v).erase w
  have hwmem : w ∈ (Finset.univ.erase u).erase v := by simp [huw.symm, hvw.symm]
  have hpUV : deletedPairFactorPolynomial r u v =
      (1 + C (r w) * X) * factorPolynomialOn outside r := by
    simpa [outside, deletedPairFactorPolynomial_eq_factorPolynomialOn] using
      generalized_factorPolynomialOn_eq_linear_mul_erase
        r ((Finset.univ.erase u).erase v) hwmem
  have hpUW : deletedPairFactorPolynomial r u w =
      (1 + C (r v) * X) * factorPolynomialOn outside r := by
    have hvmem : v ∈ (Finset.univ.erase u).erase w := by simp [huv.symm, hvw]
    have h := generalized_factorPolynomialOn_eq_linear_mul_erase
      r ((Finset.univ.erase u).erase w) hvmem
    rw [show ((Finset.univ.erase u).erase w).erase v = outside by
      simp [outside, Finset.erase_right_comm]] at h
    simpa [deletedPairFactorPolynomial_eq_factorPolynomialOn] using h
  have hpVW : deletedPairFactorPolynomial r v w =
      (1 + C (r u) * X) * factorPolynomialOn outside r := by
    have humem : u ∈ (Finset.univ.erase v).erase w := by simp [huv, huw]
    have h := generalized_factorPolynomialOn_eq_linear_mul_erase
      r ((Finset.univ.erase v).erase w) humem
    rw [show ((Finset.univ.erase v).erase w).erase u = outside by
      ext x
      simp only [Finset.mem_erase, Finset.mem_univ, true_and, outside]
      tauto] at h
    simpa [deletedPairFactorPolynomial_eq_factorPolynomialOn] using h
  have hfu := deletedFactorPolynomial_eq_linear_mul_deletedPair r u v huv
  have hfv := deletedFactorPolynomial_eq_linear_mul_deletedPair r v u huv.symm
  rw [deletedPairFactorPolynomial_comm r v u] at hfv
  have hfw := deletedFactorPolynomial_eq_linear_mul_deletedPair r w u huw.symm
  rw [deletedPairFactorPolynomial_comm r w u] at hfw
  have hP := factorPolynomial_eq_linear_mul_linear_mul_deletedPair r u v huv
  have hrow₀ :
      polynomialOfLocalVec (localCubic (r u) (r v) (r w)) *
          factorPolynomialOn outside r = factorPolynomial r := by
    rw [polynomialOfLocalVec_localCubic, hP, hpUV]
    ring
  have hrow₁u :
      polynomialOfLocalVec (shiftOne (localQuadratic (r v) (r w))) *
          factorPolynomialOn outside r = X * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftOne_localQuadratic, hfu, hpUV]
    ring
  have hrow₁v :
      polynomialOfLocalVec (shiftOne (localQuadratic (r u) (r w))) *
          factorPolynomialOn outside r = X * deletedFactorPolynomial r v := by
    rw [polynomialOfLocalVec_shiftOne_localQuadratic, hfv, hpUV]
    ring
  have hrow₁w :
      polynomialOfLocalVec (shiftOne (localQuadratic (r u) (r v))) *
          factorPolynomialOn outside r = X * deletedFactorPolynomial r w := by
    rw [polynomialOfLocalVec_shiftOne_localQuadratic, hfw, hpUW]
    ring
  have hrow₂u :
      polynomialOfLocalVec (shiftTwo (localLinear (r u))) *
          factorPolynomialOn outside r =
        X ^ 2 * deletedPairFactorPolynomial r v w := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, hpVW]
    ring
  have hrow₂v :
      polynomialOfLocalVec (shiftTwo (localLinear (r v))) *
          factorPolynomialOn outside r =
        X ^ 2 * deletedPairFactorPolynomial r u w := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, hpUW]
    ring
  have hrow₂w :
      polynomialOfLocalVec (shiftTwo (localLinear (r w))) *
          factorPolynomialOn outside r =
        X ^ 2 * deletedPairFactorPolynomial r u v := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, hpUV]
    ring
  simp [generalizedSecondTripleBlock, outside, weightedCoefficientMinor3,
    generalizedPhiTripleWeights, phiTripleTriples,
    generalized_coefficientMinor3_polynomialTriple_apply,
    hrow₀, hrow₁u, hrow₁v, hrow₁w, hrow₂u, hrow₂v, hrow₂w,
    Fin.sum_univ_succ]
  ring

theorem generalizedSecondZeroBlock_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ generalizedSecondZeroBlock r a b t i j k := by
  unfold generalizedSecondZeroBlock
  exact generalizedPhiZero_block_nonnegative a b t ha hb Finset.univ r
    (fun u hu ↦ hr u) i j k hij hjk

theorem generalizedSecondSingletonBlock_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) (a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (u : Fin n)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ generalizedSecondSingletonBlock r a b t u i j k := by
  unfold generalizedSecondSingletonBlock
  exact generalizedPhiSingleton_block_nonnegative
    a b t (r u) ha hb ht (hr u) (Finset.univ.erase u) r
      (fun v hv ↦ hr v) i j k hij hjk

theorem generalizedSecondPairBlock_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) (a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hdelta : 0 ≤ b - a + t)
    (u v : Fin n) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ generalizedSecondPairBlock r a b t u v i j k := by
  unfold generalizedSecondPairBlock
  exact generalizedPhiPair_block_nonnegative
    a b t (r u) (r v) ha hb ht hdelta (hr u) (hr v)
      ((Finset.univ.erase u).erase v) r (fun w hw ↦ hr w) i j k hij hjk

theorem generalizedSecondTripleBlock_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) (a b t : ℝ) (ht : 0 < t)
    (u v w : Fin n) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ generalizedSecondTripleBlock r a b t u v w i j k := by
  unfold generalizedSecondTripleBlock
  exact generalizedPhiTriple_block_nonnegative
    a b t (r u) (r v) (r w) ht (hr u) (hr v) (hr w)
      (((Finset.univ.erase u).erase v).erase w) r (fun x hx ↦ hr x)
        i j k hij hjk

/-! ## Raw bilinear expansion before regrouping by the union -/

theorem polynomialMinor3_add_last_generalized
    (P Q R₁ R₂ : ℝ[X]) (i j k : ℕ) :
    polynomialMinor3 P Q (R₁ + R₂) i j k =
      polynomialMinor3 P Q R₁ i j k + polynomialMinor3 P Q R₂ i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

theorem polynomialMinor3_sum_last_generalized {α : Type*} (s : Finset α)
    (P Q : ℝ[X]) (R : α → ℝ[X]) (i j k : ℕ) :
    polynomialMinor3 P Q (∑ u ∈ s, R u) i j k =
      ∑ u ∈ s, polynomialMinor3 P Q (R u) i j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, polynomialMinor3_add_last_generalized,
        ih, Finset.sum_insert hx]

/-- Expanding `D(P,X V,X^2 Q)` gives six index-pattern sums.  The following
regrouping step partitions those sums by `I union J`. -/
theorem generalizedSecondSummand_raw_expansion {n : ℕ}
    (r : Fin n → ℝ) (a b t : ℝ) (i j k : ℕ) :
    polynomialMinor3 (factorPolynomial r) (X * generalizedThreeV a t r)
        (X ^ 2 * generalizedThreeQ a b t r) i j k =
      a ^ 2 * b *
        polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
          (X ^ 2 * factorPolynomial r) i j k
      + ∑ u, a * t * (a + b + t) * (1 + r u) *
          polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
            (X ^ 2 * deletedFactorPolynomial r u) i j k
      + ∑ u, t * (a * b) * (1 + r u) *
          polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
            (X ^ 2 * factorPolynomial r) i j k
      + ∑ u, ∑ v, t ^ 2 * (a + b + t) * (1 + r u) * (1 + r v) *
          polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
            (X ^ 2 * deletedFactorPolynomial r v) i j k
      + ∑ u, ∑ v ∈ Finset.univ.erase u,
          a * t ^ 2 * (1 + r u) * (1 + r v) *
            polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
              (X ^ 2 * deletedPairFactorPolynomial r u v) i j k
      + ∑ u, ∑ v, ∑ w ∈ Finset.univ.erase v,
          t ^ 3 * (1 + r u) * (1 + r v) * (1 + r w) *
            polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
              (X ^ 2 * deletedPairFactorPolynomial r v w) i j k := by
  classical
  let P := factorPolynomial r
  let F := fun u ↦ deletedFactorPolynomial r u
  let H := fun u v ↦ deletedPairFactorPolynomial r u v
  have hmiddle : X * generalizedThreeV a t r =
      C a * (X * P) + ∑ u, C (t * (1 + r u)) * (X * F u) := by
    rw [generalizedThreeV, G1, Finset.mul_sum, mul_add, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · dsimp [P]
      ring
    · apply Finset.sum_congr rfl
      intro u hu
      dsimp [F]
      rw [map_mul]
      ring
  have hscaledG2 : C (2 * t ^ 2) * G2 r =
      ∑ u, ∑ v ∈ Finset.univ.erase u,
        C (t ^ 2 * (1 + r u) * (1 + r v)) * H u v := by
    simp only [G2]
    have hc : C (2 * t ^ 2) * C (1 / 2 : ℝ) = C (t ^ 2) := by
      rw [← C_mul]
      congr 1
      ring
    rw [← mul_assoc, hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp [H]
    simp only [map_mul]
    ring
  have hsingle : X ^ 2 * (C (t * (a + b + t)) * G1 r) =
      ∑ u, C (t * (a + b + t) * (1 + r u)) * (X ^ 2 * F u) := by
    rw [G1, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [F]
    have hC : C (t * (a + b + t)) * C (1 + r u) =
        C (t * (a + b + t) * (1 + r u)) := by
      rw [← C_mul]
    calc
      X ^ 2 * (C (t * (a + b + t)) *
          (C (1 + r u) * deletedFactorPolynomial r u)) =
          X ^ 2 * (C (t * (a + b + t)) * C (1 + r u)) *
            deletedFactorPolynomial r u := by ring
      _ =
          X ^ 2 * (C (t * (a + b + t) * (1 + r u)) *
            deletedFactorPolynomial r u) := by
              rw [hC]
              ring
      _ = C (t * (a + b + t) * (1 + r u)) *
          (X ^ 2 * deletedFactorPolynomial r u) := by ring
  have hpairs : X ^ 2 * (C (2 * t ^ 2) * G2 r) =
      ∑ u, ∑ v ∈ Finset.univ.erase u,
        C (t ^ 2 * (1 + r u) * (1 + r v)) * (X ^ 2 * H u v) := by
    rw [hscaledG2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  have hlast : X ^ 2 * generalizedThreeQ a b t r =
      C (a * b) * (X ^ 2 * P)
        + ∑ u, C (t * (a + b + t) * (1 + r u)) * (X ^ 2 * F u)
        + ∑ u, ∑ v ∈ Finset.univ.erase u,
            C (t ^ 2 * (1 + r u) * (1 + r v)) * (X ^ 2 * H u v) := by
    calc
      _ = C (a * b) * (X ^ 2 * P) +
          X ^ 2 * (C (t * (a + b + t)) * G1 r) +
            X ^ 2 * (C (2 * t ^ 2) * G2 r) := by
              dsimp [generalizedThreeQ, P]
              ring
      _ = _ := by rw [hsingle, hpairs]
  rw [hmiddle, hlast]
  simp_rw [polynomialMinor3_add_middle,
    polynomialMinor3_add_last_generalized]
  simp_rw [polynomialMinor3_sum_middle,
    polynomialMinor3_sum_last_generalized]
  simp_rw [polynomialMinor3_C_mul_middle_generalized,
    polynomialMinor3_C_mul_right_generalized]
  dsimp [P, F, H]
  ring

/-! ## Regrouping the raw sums by their deletion-index union -/

/-- The sum of the four union-cardinality blocks.  Ordered pairs and triples
are divided by their orbit cardinalities `2` and `6`. -/
noncomputable def generalizedSecondBlockSum {n : ℕ} (r : Fin n → ℝ)
    (a b t : ℝ) (i j k : ℕ) : ℝ :=
  generalizedSecondZeroBlock r a b t i j k
    + ∑ u, generalizedSecondSingletonBlock r a b t u i j k
    + (1 / 2 : ℝ) *
        (∑ u, ∑ v ∈ Finset.univ.erase u,
          generalizedSecondPairBlock r a b t u v i j k)
    + (1 / 6 : ℝ) *
        (∑ u, ∑ v ∈ Finset.univ.erase u,
          ∑ w ∈ (Finset.univ.erase u).erase v,
            generalizedSecondTripleBlock r a b t u v w i j k)

/-- The global `I union J` regrouping from Section 4. -/
theorem generalizedSecondSummand_eq_blockSum {n : ℕ}
    (r : Fin n → ℝ) (a b t : ℝ) (i j k : ℕ) :
    polynomialMinor3 (factorPolynomial r) (X * generalizedThreeV a t r)
        (X ^ 2 * generalizedThreeQ a b t r) i j k =
      generalizedSecondBlockSum r a b t i j k := by
  classical
  let P := factorPolynomial r
  let F := fun u ↦ deletedFactorPolynomial r u
  let H := fun u v ↦ deletedPairFactorPolynomial r u v
  let A := fun u ↦ a * t * (a + b + t) * (1 + r u) *
    polynomialMinor3 P (X * P) (X ^ 2 * F u) i j k
  let B := fun u ↦ t * (a * b) * (1 + r u) *
    polynomialMinor3 P (X * F u) (X ^ 2 * P) i j k
  let d := fun u v ↦ t ^ 2 * (a + b + t) * (1 + r u) * (1 + r v) *
    polynomialMinor3 P (X * F u) (X ^ 2 * F v) i j k
  let e := fun u v ↦ a * t ^ 2 * (1 + r u) * (1 + r v) *
    polynomialMinor3 P (X * P) (X ^ 2 * H u v) i j k
  let h := fun u v w ↦ t ^ 3 * (1 + r u) * (1 + r v) * (1 + r w) *
    polynomialMinor3 P (X * F u) (X ^ 2 * H v w) i j k
  have hsym : ∀ u v w, h u v w = h u w v := by
    intro u v w
    dsimp [h, H]
    rw [deletedPairFactorPolynomial_comm r v w]
    ring
  have horbit := orderedDeletion_orbit_regroup d e h hsym
  have hsingle :
      (∑ u, generalizedSecondSingletonBlock r a b t u i j k) =
        (∑ u, A u) + (∑ u, B u) + ∑ u, d u u := by
    simp_rw [generalizedSecondSingletonBlock_eq]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [A, B, d, P, F]
    ring
  have hpair :
      (∑ u, ∑ v ∈ Finset.univ.erase u,
        generalizedSecondPairBlock r a b t u v i j k) =
      ∑ u, ∑ v ∈ Finset.univ.erase u,
        (2 * e u v + d u v + d v u + 2 * h u u v + 2 * h v v u) := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    rw [generalizedSecondPairBlock_eq r a b t u v hvu.symm]
    dsimp [d, e, h, P, F, H]
    rw [deletedPairFactorPolynomial_comm r v u]
    ring
  have htriple :
      (∑ u, ∑ v ∈ Finset.univ.erase u,
        ∑ w ∈ (Finset.univ.erase u).erase v,
          generalizedSecondTripleBlock r a b t u v w i j k) =
      ∑ u, ∑ v ∈ Finset.univ.erase u,
        ∑ w ∈ (Finset.univ.erase u).erase v,
          (2 * h u v w + 2 * h v u w + 2 * h w u v) := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    apply Finset.sum_congr rfl
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    have hwu : w ≠ u :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    rw [generalizedSecondTripleBlock_eq
      r a b t u v w hvu.symm hwu.symm hwv.symm]
    dsimp [h, P, F, H]
    ring
  rw [generalizedSecondSummand_raw_expansion]
  unfold generalizedSecondBlockSum
  rw [generalizedSecondZeroBlock_eq, hsingle, hpair, htriple]
  dsimp [A, B, d, e, h, P, F, H] at horbit ⊢
  linear_combination horbit

theorem generalizedSecondBlockSum_nonnegative {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ u, 0 ≤ r u)
    (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hdelta : 0 ≤ b - a + t)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ generalizedSecondBlockSum r a b t i j k := by
  have h₀ := generalizedSecondZeroBlock_nonnegative
    r hr a b t ha hb hij hjk
  have h₁ : 0 ≤ ∑ u, generalizedSecondSingletonBlock r a b t u i j k := by
    apply Finset.sum_nonneg
    intro u hu
    exact generalizedSecondSingletonBlock_nonnegative
      r hr a b t ha hb ht u hij hjk
  have h₂ : 0 ≤ ∑ u, ∑ v ∈ Finset.univ.erase u,
      generalizedSecondPairBlock r a b t u v i j k := by
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro v hv
    exact generalizedSecondPairBlock_nonnegative
      r hr a b t ha hb ht hdelta u v hij hjk
  have h₃ : 0 ≤ ∑ u, ∑ v ∈ Finset.univ.erase u,
      ∑ w ∈ (Finset.univ.erase u).erase v,
        generalizedSecondTripleBlock r a b t u v w i j k := by
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro v hv
    apply Finset.sum_nonneg
    intro w hw
    exact generalizedSecondTripleBlock_nonnegative
      r hr a b t ht u v w hij hjk
  unfold generalizedSecondBlockSum
  exact add_nonneg
    (add_nonneg (add_nonneg h₀ h₁) (mul_nonneg (by norm_num) h₂))
    (mul_nonneg (by norm_num) h₃)

/-- Strict positivity of the second split summand.  The empty-union term is
`a^2*b` times the strict consecutive Toeplitz minor. -/
theorem generalizedSecondSummand_consecutive_pos {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ u, 0 < r u)
    (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hdelta : 0 ≤ b - a + t) (k : ℕ) (hk : k ≤ n) :
    0 < polynomialMinor3 (factorPolynomial r) (X * generalizedThreeV a t r)
      (X ^ 2 * generalizedThreeQ a b t r) k (k + 1) (k + 2) := by
  rw [generalizedSecondSummand_eq_blockSum]
  have hzero : 0 < generalizedSecondZeroBlock r a b t k (k + 1) (k + 2) :=
    generalizedPhiZero_fullFactor_consecutive_pos r hr a b t ha hb k hk
  have hrest₁ : 0 ≤ ∑ u,
      generalizedSecondSingletonBlock r a b t u k (k + 1) (k + 2) := by
    apply Finset.sum_nonneg
    intro u hu
    exact generalizedSecondSingletonBlock_nonnegative
      r (fun x ↦ (hr x).le) a b t ha hb ht u (by omega) (by omega)
  have hrest₂ : 0 ≤ ∑ u, ∑ v ∈ Finset.univ.erase u,
      generalizedSecondPairBlock r a b t u v k (k + 1) (k + 2) := by
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro v hv
    exact generalizedSecondPairBlock_nonnegative r (fun x ↦ (hr x).le)
      a b t ha hb ht hdelta u v (by omega) (by omega)
  have hrest₃ : 0 ≤ ∑ u, ∑ v ∈ Finset.univ.erase u,
      ∑ w ∈ (Finset.univ.erase u).erase v,
        generalizedSecondTripleBlock r a b t u v w k (k + 1) (k + 2) := by
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro v hv
    apply Finset.sum_nonneg
    intro w hw
    exact generalizedSecondTripleBlock_nonnegative r (fun x ↦ (hr x).le)
      a b t ht u v w (by omega) (by omega)
  unfold generalizedSecondBlockSum
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg hzero hrest₁)
      (mul_nonneg (by norm_num) hrest₂))
    (mul_nonneg (by norm_num) hrest₃)

/-! ## The factor-level and row-level end theorems -/

/-- Two successive generalized Eulerian steps have a strictly positive
consecutive `3 x 3` coefficient minor. -/
theorem factorPolynomial_generalizedSteps_det3_consecutive_pos {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ u, 0 < r u)
    (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hdelta : 0 ≤ b - a + t) (k : ℕ) (hk : k ≤ n) :
    0 < polynomialMinor3 (factorPolynomial r)
      (generalizedEulerianStep n a t (factorPolynomial r))
      (generalizedEulerianStep (n + 1) b t
        (generalizedEulerianStep n a t (factorPolynomial r)))
      k (k + 1) (k + 2) := by
  let P := factorPolynomial r
  let Q := generalizedEulerianStep n a t P
  let R := generalizedEulerianStep (n + 1) b t Q
  let V₁ := X * generalizedThreeV a t r
  let V₂ := C (b - a + t) * X * P
  let V₃ := X ^ 2 * generalizedThreeQ a b t r
  have hQsplit : Q = P + V₁ := by
    dsimp [Q, P, V₁]
    exact generalizedEulerianStep_factorPolynomial_formula r a t
  have hRsplit : R = P + C (t + 2) * V₁ + V₂ + V₃ := by
    dsimp [R, Q, P, V₁, V₂, V₃]
    simpa [mul_assoc] using generalizedEulerianStep_second_formula r a b t
  have hfirst : 0 ≤ polynomialMinor3 P V₁ V₂ k (k + 1) (k + 2) := by
    dsimp [P, V₁, V₂]
    rw [generalizedThree_first_split_eq]
    have hbase := firstSummand_nonnegative r (fun u ↦ (hr u).le)
      (show k < k + 1 by omega) (show k + 1 < k + 2 by omega)
    exact mul_nonneg (mul_nonneg ht.le hdelta) hbase
  have hsecond : 0 < polynomialMinor3 P V₁ V₃ k (k + 1) (k + 2) := by
    dsimp [P, V₁, V₃]
    exact generalizedSecondSummand_consecutive_pos
      r hr a b t ha hb ht hdelta k hk
  change 0 < polynomialMinor3 P Q R k (k + 1) (k + 2)
  rw [hQsplit, hRsplit, polynomialMinor3_parameterized_three_row_split]
  exact add_pos_of_nonneg_of_pos hfirst hsecond

private theorem polynomialMinor3_eulerianTypePoly_eq_triangle
    (β : ℝ) (alpha : ℕ → ℝ) (n i j k : ℕ) :
    polynomialMinor3 (eulerianTypePoly β alpha n)
        (eulerianTypePoly β alpha (n + 1))
        (eulerianTypePoly β alpha (n + 2)) i j k =
      det3 (eulerianTypeTriangle β alpha) n (n + 1) (n + 2) i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix,
    eulerianTypeTriangle, det3]

/-- Row-level generalized conclusion for the canonical coefficient triangle. -/
theorem eulerianTypeTriangle_det3_solid_pos
    {β : ℝ} {alpha : ℕ → ℝ} (hβ : 0 < β) (halpha : ∀ m, 0 < alpha m)
    (hdelta : ∀ m, 0 ≤ alpha (m + 1) - alpha m + β)
    (n k : ℕ) (hk : k ≤ n) :
    0 < det3 (eulerianTypeTriangle β alpha) n (n + 1) (n + 2)
      k (k + 1) (k + 2) := by
  obtain ⟨r, hr, hfactor⟩ :=
    eulerianTypePoly_exists_positive_linearFactors hβ halpha n
  have hfactor' : eulerianTypePoly β alpha n = factorPolynomial r := by
    simpa [factorPolynomial] using hfactor
  have h := factorPolynomial_generalizedSteps_det3_consecutive_pos
    r hr (alpha n) (alpha (n + 1)) β (halpha n) (halpha (n + 1)) hβ
      (hdelta n) k hk
  rw [← hfactor'] at h
  change 0 < polynomialMinor3 (eulerianTypePoly β alpha n)
      (generalizedEulerianStep n (alpha n) β (eulerianTypePoly β alpha n))
      (generalizedEulerianStep (n + 1) (alpha (n + 1)) β
        (generalizedEulerianStep n (alpha n) β (eulerianTypePoly β alpha n)))
      k (k + 1) (k + 2) at h
  rw [show generalizedEulerianStep n (alpha n) β (eulerianTypePoly β alpha n) =
      eulerianTypePoly β alpha (n + 1) by
        simp [generalizedEulerianStep, eulerianTypePoly_succ]] at h
  rw [show generalizedEulerianStep (n + 1) (alpha (n + 1)) β
      (eulerianTypePoly β alpha (n + 1)) = eulerianTypePoly β alpha (n + 2) by
        simpa [generalizedEulerianStep, Nat.add_assoc] using
          (eulerianTypePoly_succ β alpha (n + 1)).symm] at h
  rwa [polynomialMinor3_eulerianTypePoly_eq_triangle] at h

end LeanCo.EulerianTP3
