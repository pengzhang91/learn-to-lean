import LeanCo.EulerianTP3.RootDeletion
import LeanCo.EulerianTP3.Rows
import LeanCo.EulerianTP3.GeneralizedRows

/-!
# Strict solid minors of order two

The paper derives these minors from Newton inequalities.  Here they are
proved directly from the positive linear-factor presentation: the strict
Toeplitz term survives, while every root-deletion term is nonnegative.
-/

namespace LeanCo.EulerianTP3

open scoped BigOperators
open Polynomial

/-- The two-column coefficient determinant of a pair of polynomials. -/
def coefficientDet2 (p q : ℝ[X]) (j₀ j₁ : ℕ) : ℝ :=
  p.coeff j₀ * q.coeff j₁ - p.coeff j₁ * q.coeff j₀

private def polynomialPair (p q : ℝ[X]) : ℕ → ℝ[X]
  | 0 => p
  | _ => q

@[simp] private lemma coefficientDet2_add_right (p q r : ℝ[X]) (j₀ j₁ : ℕ) :
    coefficientDet2 p (q + r) j₀ j₁ =
      coefficientDet2 p q j₀ j₁ + coefficientDet2 p r j₀ j₁ := by
  simp [coefficientDet2]
  ring

@[simp] private lemma coefficientDet2_C_mul_right (p q : ℝ[X]) (c : ℝ)
    (j₀ j₁ : ℕ) :
    coefficientDet2 p (C c * q) j₀ j₁ = c * coefficientDet2 p q j₀ j₁ := by
  simp [coefficientDet2]
  ring

private lemma coefficientDet2_sum_right {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ℝ[X]) (q : ι → ℝ[X]) (j₀ j₁ : ℕ) :
    coefficientDet2 p (∑ i ∈ s, q i) j₀ j₁ =
      ∑ i ∈ s, coefficientDet2 p (q i) j₀ j₁ := by
  induction s using Finset.induction_on with
  | empty => simp [coefficientDet2]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [coefficientDet2_add_right, ih]

private theorem localPair_ordered_nonnegative (a : ℝ) (ha : 0 ≤ a) :
    OrderedDet2Nonnegative
      (coefficientMatrix
        (polynomialPair (1 + C a * X) (C (1 + a) * X))) 0 1 := by
  intro j₀ j₁ hj
  rcases j₀ with _ | j₀
  · rcases j₁ with _ | j₁
    · omega
    · rcases j₁ with _ | j₁
      · simp [coefficientMatrix, polynomialPair, det2]
        linarith
      · simp [coefficientMatrix, polynomialPair, det2, coeff_add, coeff_one, coeff_C,
          coeff_X, coeff_mul_X]
  · rcases j₁ with _ | j₁
    · omega
    · rcases j₁ with _ | j₁
      · omega
      · simp [coefficientMatrix, polynomialPair, det2, coeff_add, coeff_one, coeff_C,
          coeff_mul_X]

private lemma deleted_term_det2_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (i : Fin n) (j₀ j₁ : ℕ) (hj : j₀ < j₁) :
    0 ≤ coefficientDet2 (factorPolynomial r)
      (X * (C (1 + r i) * deletedFactorPolynomial r i)) j₀ j₁ := by
  let localRows := polynomialPair (1 + C (r i) * X) (C (1 + r i) * X)
  have hlocal : OrderedDet2Nonnegative (coefficientMatrix localRows) 0 1 := by
    simpa [localRows] using localPair_ordered_nonnegative (r i) (hr i)
  have hmul := coefficientMatrix_mul_factorPolynomialOn_det2_nonnegative
    localRows 0 1 (Finset.univ.erase i) r
      (fun j _ ↦ hr j) hlocal
  have hdet := hmul j₀ j₁ hj
  have hrow0 :
      (1 + C (r i) * X) * deletedFactorPolynomial r i = factorPolynomial r := by
    symm
    exact factorPolynomial_eq_linear_mul_deletedFactor r i
  have hrow1 :
      (C (1 + r i) * X) * deletedFactorPolynomial r i =
        X * (C (1 + r i) * deletedFactorPolynomial r i) := by ring
  change 0 ≤ coefficientDet2
    ((1 + C (r i) * X) * factorPolynomialOn (Finset.univ.erase i) r)
    ((C (1 + r i) * X) * factorPolynomialOn (Finset.univ.erase i) r) j₀ j₁ at hdet
  rw [← deletedFactorPolynomial_eq_factorPolynomialOn r i, hrow0, hrow1] at hdet
  exact hdet

private theorem G1_term_det2_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ r i) (j₀ j₁ : ℕ) (hj : j₀ < j₁) :
    0 ≤ coefficientDet2 (factorPolynomial r) (X * G1 r) j₀ j₁ := by
  rw [G1, Finset.mul_sum]
  rw [coefficientDet2_sum_right]
  exact Finset.sum_nonneg fun i _ ↦ deleted_term_det2_nonnegative r hr i j₀ j₁ hj

private lemma coefficientDet2_mul_X_eq_toeplitz (p : ℝ[X]) (k : ℕ) :
    coefficientDet2 p (X * p) k (k + 1) =
      det2 (upperToeplitz p) 0 1 k (k + 1) := by
  rcases k with _ | k
  · simp [coefficientDet2, det2, upperToeplitz]
  · simp [coefficientDet2, det2, upperToeplitz, coeff_X_mul]

/-- One Eulerian differential step has a strictly positive consecutive
two-column determinant over every positive factor polynomial. -/
theorem factorPolynomial_eulerianStep_det2_consecutive_pos {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (k : ℕ) (hk : k ≤ n) :
    0 < coefficientDet2 (factorPolynomial r)
      ((1 + C (n + 1 : ℝ) * X) * factorPolynomial r +
        X * (1 - X) * (factorPolynomial r).derivative) k (k + 1) := by
  rw [ordinaryEulerian_Q_formula]
  rw [show
      (1 + X) * factorPolynomial r + X * G1 r =
        factorPolynomial r + X * factorPolynomial r + X * G1 r by ring]
  rw [coefficientDet2_add_right, coefficientDet2_add_right]
  have hstrict : 0 < coefficientDet2 (factorPolynomial r)
      (X * factorPolynomial r) k (k + 1) := by
    rw [coefficientDet2_mul_X_eq_toeplitz]
    exact factorPolynomial_upperToeplitz_det2_consecutive_pos r hr k hk
  have hnonneg : 0 ≤ coefficientDet2 (factorPolynomial r) (X * G1 r) k (k + 1) :=
    G1_term_det2_nonnegative r (fun i ↦ (hr i).le) k (k + 1) (by omega)
  have hsame : coefficientDet2 (factorPolynomial r) (factorPolynomial r)
      k (k + 1) = 0 := by simp [coefficientDet2]; ring
  rw [hsame, zero_add]
  exact add_pos_of_pos_of_nonneg hstrict hnonneg

/-- The order-two argument in the parameterized recurrence of Theorem 4.1. -/
theorem factorPolynomial_generalizedStep_det2_consecutive_pos {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (a t : ℝ) (ha : 0 < a) (ht : 0 < t) (k : ℕ) (hk : k ≤ n) :
    0 < coefficientDet2 (factorPolynomial r)
      ((1 + C ((n : ℝ) * t + a) * X) * factorPolynomial r +
        C t * X * (1 - X) * (factorPolynomial r).derivative) k (k + 1) := by
  have hformula :
      (1 + C ((n : ℝ) * t + a) * X) * factorPolynomial r +
          C t * X * (1 - X) * (factorPolynomial r).derivative =
        factorPolynomial r +
          C a * (X * factorPolynomial r) + C t * (X * G1 r) := by
    rw [G1_eq_nat_mul_factorPolynomial_add_derivative]
    have hC : C ((n : ℝ) * t + a) = C t * C (n : ℝ) + C a := by
      rw [map_add, map_mul]
      ring
    rw [hC]
    ring
  rw [hformula, coefficientDet2_add_right, coefficientDet2_add_right,
    coefficientDet2_C_mul_right, coefficientDet2_C_mul_right]
  have hstrict : 0 < coefficientDet2 (factorPolynomial r)
      (X * factorPolynomial r) k (k + 1) := by
    rw [coefficientDet2_mul_X_eq_toeplitz]
    exact factorPolynomial_upperToeplitz_det2_consecutive_pos r hr k hk
  have hnonneg : 0 ≤ coefficientDet2 (factorPolynomial r) (X * G1 r) k (k + 1) :=
    G1_term_det2_nonnegative r (fun i ↦ (hr i).le) k (k + 1) (by omega)
  have hsame : coefficientDet2 (factorPolynomial r) (factorPolynomial r)
      k (k + 1) = 0 := by simp [coefficientDet2]; ring
  rw [hsame, zero_add]
  exact add_pos_of_pos_of_nonneg (mul_pos ha hstrict) (mul_nonneg ht.le hnonneg)

/-- Every solid admissible order-two minor of the ordinary Eulerian triangle
is strictly positive. -/
theorem eulerianTriangle_det2_solid_pos (n k : ℕ) (hk : k ≤ n) :
    0 < det2 eulerianTriangle n (n + 1) k (k + 1) := by
  obtain ⟨r, hr, hfactor⟩ := eulerianPoly_exists_positive_linearFactors n
  have h := factorPolynomial_eulerianStep_det2_consecutive_pos r hr k hk
  change eulerianPoly n = factorPolynomial r at hfactor
  rw [← hfactor] at h
  simpa [coefficientDet2, det2, eulerianTriangle, eulerianPoly_succ] using h

/-- Every solid admissible order-two minor of a generalized Eulerian-type
triangle is strictly positive under the positivity assumptions of
Theorem 4.1. -/
theorem eulerianTypeTriangle_det2_solid_pos {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n)
    (n k : ℕ) (hk : k ≤ n) :
    0 < det2 (eulerianTypeTriangle β alpha) n (n + 1) k (k + 1) := by
  obtain ⟨r, hr, hfactor⟩ :=
    eulerianTypePoly_exists_positive_linearFactors hβ halpha n
  have h := factorPolynomial_generalizedStep_det2_consecutive_pos
    r hr (alpha n) β (halpha n) hβ k hk
  change eulerianTypePoly β alpha n = factorPolynomial r at hfactor
  rw [← hfactor] at h
  simpa [coefficientDet2, det2, eulerianTypeTriangle,
    eulerianTypePoly_succ] using h

end LeanCo.EulerianTP3
