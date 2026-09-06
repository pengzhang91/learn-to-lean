import LeanCo.EulerianTP3.GeneralizedRoots
import LeanCo.EulerianTP3.Minors

/-!
# Rows of the generalized Eulerian-type triangle

This file exposes the coefficient array governed by the recurrence in
Theorem 4.1 and records its triangular support and entry positivity.
-/

namespace LeanCo.EulerianTP3

open Polynomial

/-- The coefficient triangle attached to the parameterized Eulerian-type
polynomial recurrence. -/
noncomputable def eulerianTypeTriangle (β : ℝ) (alpha : ℕ → ℝ)
    (n k : ℕ) : ℝ :=
  (eulerianTypePoly β alpha n).coeff k

@[simp] lemma eulerianTypeTriangle_zero_zero (β : ℝ) (alpha : ℕ → ℝ) :
    eulerianTypeTriangle β alpha 0 0 = 1 := by
  simp [eulerianTypeTriangle]

@[simp] lemma eulerianTypeTriangle_zero_succ (β : ℝ) (alpha : ℕ → ℝ)
    (k : ℕ) :
    eulerianTypeTriangle β alpha 0 (k + 1) = 0 := by
  simp [eulerianTypeTriangle, coeff_one]

@[simp] lemma eulerianTypeTriangle_succ_zero (β : ℝ) (alpha : ℕ → ℝ)
    (n : ℕ) :
    eulerianTypeTriangle β alpha (n + 1) 0 = 1 := by
  simpa [eulerianTypeTriangle, coeff_zero_eq_eval_zero] using
    eulerianTypePoly_eval_zero β alpha (n + 1)

/-- The coefficient form of the parameterized differential recurrence. -/
lemma eulerianTypeTriangle_succ_succ (β : ℝ) (alpha : ℕ → ℝ)
    (n k : ℕ) :
    eulerianTypeTriangle β alpha (n + 1) (k + 1) =
      (1 + β * (k + 1 : ℝ)) * eulerianTypeTriangle β alpha n (k + 1)
        + (alpha n + β * (n - k : ℝ)) * eulerianTypeTriangle β alpha n k := by
  exact eulerianTypePoly_succ_coeff_succ β alpha n k

lemma eulerianTypeTriangle_eq_zero_of_lt {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n)
    (n k : ℕ) (h : n < k) :
    eulerianTypeTriangle β alpha n k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  simpa [eulerianTypePoly_natDegree hβ halpha] using h

/-- The generalized coefficient array is lower triangular. -/
theorem eulerianTypeTriangle_lowerTriangular {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) :
    LowerTriangular (eulerianTypeTriangle β alpha) := by
  intro n k h
  exact eulerianTypeTriangle_eq_zero_of_lt hβ halpha n k h

/-- Every entry in the triangular support is strictly positive. -/
theorem eulerianTypeTriangle_entry_pos {β : ℝ} {alpha : ℕ → ℝ}
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n)
    (n k : ℕ) (hk : k ≤ n) :
    0 < eulerianTypeTriangle β alpha n k := by
  exact eulerianTypePoly_coeff_pos hβ halpha hk

/-! ## An arbitrary lower-triangular matrix satisfying the recurrence -/

/-- The finite row-generating polynomial of an infinite real matrix.  For a
lower-triangular matrix this contains every potentially nonzero entry of the
row. -/
noncomputable def rowGeneratingPolynomial (M : ℕ → ℕ → ℝ) (n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (M n k) * X ^ k

@[simp] lemma rowGeneratingPolynomial_coeff (M : ℕ → ℕ → ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    (rowGeneratingPolynomial M n).coeff k = M n k := by
  simp [rowGeneratingPolynomial, coeff_X_pow, hk]

lemma rowGeneratingPolynomial_coeff_eq_zero (M : ℕ → ℕ → ℝ)
    (n k : ℕ) (hk : n < k) :
    (rowGeneratingPolynomial M n).coeff k = 0 := by
  simp [rowGeneratingPolynomial, coeff_X_pow, show k ∉ Finset.range (n + 1) by simp; omega]

/-- The differential recurrence and initial row uniquely determine the
polynomial sequence. -/
theorem polynomialSequence_eq_eulerianTypePoly
    (β : ℝ) (alpha : ℕ → ℝ) (P : ℕ → ℝ[X])
    (hzero : P 0 = 1)
    (hsucc : ∀ n, P (n + 1) =
      (1 + C ((n : ℝ) * β + alpha n) * X) * P n
        + C β * X * (1 - X) * (P n).derivative) :
    ∀ n, P n = eulerianTypePoly β alpha n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      rw [hsucc n, ih]
      exact eulerianTypePoly_succ β alpha n

/-- Matrix-level uniqueness: a lower-triangular coefficient array whose row
polynomials satisfy the recurrence is exactly the canonical generalized
Eulerian-type triangle. -/
theorem matrix_eq_eulerianTypeTriangle
    (β : ℝ) (alpha : ℕ → ℝ) (M : ℕ → ℕ → ℝ)
    (htri : LowerTriangular M)
    (hzero : rowGeneratingPolynomial M 0 = 1)
    (hsucc : ∀ n, rowGeneratingPolynomial M (n + 1) =
      (1 + C ((n : ℝ) * β + alpha n) * X) * rowGeneratingPolynomial M n
        + C β * X * (1 - X) * (rowGeneratingPolynomial M n).derivative)
    (hβ : 0 < β) (halpha : ∀ n, 0 < alpha n) :
    M = eulerianTypeTriangle β alpha := by
  funext n k
  have hpoly := polynomialSequence_eq_eulerianTypePoly β alpha
    (rowGeneratingPolynomial M) hzero hsucc n
  by_cases hk : k ≤ n
  · have := congrArg (fun p : ℝ[X] ↦ p.coeff k) hpoly
    simpa [eulerianTypeTriangle, rowGeneratingPolynomial_coeff M n k hk] using this
  · rw [htri n k (by omega)]
    exact (eulerianTypeTriangle_eq_zero_of_lt hβ halpha n k (by omega)).symm

end LeanCo.EulerianTP3
