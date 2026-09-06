import LeanCo.EulerianTP3.RealRoots
import LeanCo.EulerianTP3.Minors

/-!
# Rows of the Eulerian triangle

This file turns the polynomial recurrence into the literal coefficient
triangle used in arXiv:2608.29224.  In particular it proves the support and
strict entry-positivity statements rather than building either fact into the
definition of the matrix.
-/

namespace LeanCo.EulerianTP3

open Polynomial

/-- The ordinary Eulerian triangle, regarded as a real infinite matrix. -/
noncomputable def eulerianTriangle (n k : ℕ) : ℝ :=
  (eulerianPoly n).coeff k

@[simp] lemma eulerianTriangle_zero_zero : eulerianTriangle 0 0 = 1 := by
  simp [eulerianTriangle]

@[simp] lemma eulerianTriangle_zero_succ (k : ℕ) :
    eulerianTriangle 0 (k + 1) = 0 := by
  simp [eulerianTriangle, coeff_one]

@[simp] lemma eulerianTriangle_succ_zero (n : ℕ) :
    eulerianTriangle (n + 1) 0 = eulerianTriangle n 0 := by
  simp [eulerianTriangle, eulerianPoly_succ]

/-- The coefficient form of the Eulerian-polynomial differential recurrence. -/
lemma eulerianTriangle_succ_succ (n k : ℕ) :
    eulerianTriangle (n + 1) (k + 1) =
      (k + 2 : ℝ) * eulerianTriangle n (k + 1) +
        ((n + 1 : ℝ) - k) * eulerianTriangle n k := by
  simp only [eulerianTriangle, eulerianPoly_succ]
  rw [show
      (1 + C (n + 1 : ℝ) * X) * eulerianPoly n
          + X * (1 - X) * (eulerianPoly n).derivative =
        eulerianPoly n + C (n + 1 : ℝ) * (X * eulerianPoly n)
          + X * (eulerianPoly n).derivative
          - X * (X * (eulerianPoly n).derivative) by ring]
  cases k with
  | zero =>
      simp only [coeff_sub, coeff_add, coeff_C_mul]
      simp only [coeff_X_mul]
      rw [coeff_derivative]
      simp [mul_coeff_zero]
      ring
  | succ k =>
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_derivative]
      push_cast
      ring

lemma eulerianTriangle_eq_zero_of_lt (n k : ℕ) (h : n < k) :
    eulerianTriangle n k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  simpa [eulerianPoly_natDegree] using h

/-- The Eulerian coefficient triangle is lower triangular. -/
theorem eulerianTriangle_lowerTriangular : LowerTriangular eulerianTriangle := by
  intro n k h
  exact eulerianTriangle_eq_zero_of_lt n k h

@[simp] theorem eulerianTriangle_firstColumn (n : ℕ) :
    eulerianTriangle n 0 = 1 := by
  induction n with
  | zero => exact eulerianTriangle_zero_zero
  | succ n ih => simpa using (eulerianTriangle_succ_zero n).trans ih

/-- Every entry in the triangular support is strictly positive. -/
theorem eulerianTriangle_entry_pos (n k : ℕ) (hk : k ≤ n) :
    0 < eulerianTriangle n k := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      rcases k with _ | k
      · simp
      rw [eulerianTriangle_succ_succ]
      by_cases hkn : k < n + 1
      · have hk' : k ≤ n := by omega
        have hcoef : 0 < (n + 1 : ℝ) - k := by
          apply sub_pos.mpr
          exact_mod_cast hkn
        have hright : 0 < ((n + 1 : ℝ) - k) * eulerianTriangle n k :=
          mul_pos hcoef (ih k hk')
        have hleft : 0 ≤ (k + 2 : ℝ) * eulerianTriangle n (k + 1) := by
          by_cases hle : k + 1 ≤ n
          · exact (mul_pos (by positivity) (ih (k + 1) hle)).le
          · rw [eulerianTriangle_eq_zero_of_lt n (k + 1) (by omega)]
            simp
        exact add_pos_of_nonneg_of_pos hleft hright
      · omega

end LeanCo.EulerianTP3
