import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# The complete two-boundary calculation

This file formalizes Propositions 6.1 and 6.2 of arXiv:2608.30053.
The matrix is written in the order `(C,D)`, where `C` is the one-block
partition and `D` is the discrete partition.
-/

namespace LeanCo.Negami

section TwoBoundary

variable {F : Type*} [Field F]

/-- The two-boundary connectivity matrix from Proposition 6.1. -/
def twoBoundaryMatrix (t : F) : Matrix (Fin 2) (Fin 2) F :=
  !![t, t; t, t ^ 2]

/-- The explicit inverse kernel from Proposition 6.2. -/
def twoBoundaryInverse (t : F) : Matrix (Fin 2) (Fin 2) F :=
  let d := t ^ 2 * (t - 1)
  !![t ^ 2 / d, -t / d; -t / d, t / d]

/-- The determinant exposes exactly the exceptional parameters `0` and `1`. -/
theorem twoBoundaryMatrix_det (t : F) :
    Matrix.det (twoBoundaryMatrix t) = t ^ 2 * (t - 1) := by
  simp [twoBoundaryMatrix, Matrix.det_fin_two]
  ring

/-- The displayed kernel is a right inverse away from the exceptional
parameters. -/
theorem twoBoundaryMatrix_mul_inverse (t : F) (ht : t ≠ 0) (ht1 : t ≠ 1) :
    twoBoundaryMatrix t * twoBoundaryInverse t = 1 := by
  have hs : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hd : t ^ 2 * (t - 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 ht) hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoBoundaryMatrix, twoBoundaryInverse, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    field_simp [hd, ht, hs] <;> ring

/-- The displayed kernel is also a left inverse. -/
theorem twoBoundaryInverse_mul_matrix (t : F) (ht : t ≠ 0) (ht1 : t ≠ 1) :
    twoBoundaryInverse t * twoBoundaryMatrix t = 1 := by
  have hs : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hd : t ^ 2 * (t - 1) ≠ 0 := mul_ne_zero (pow_ne_zero 2 ht) hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoBoundaryMatrix, twoBoundaryInverse, Matrix.mul_apply,
      Fin.sum_univ_two] <;>
    field_simp [hd, ht, hs] <;> ring

end TwoBoundary

end LeanCo.Negami
