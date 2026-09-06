import LeanCo.LaplacianLFunctions.Picard
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# Rooted coordinates for degree-zero divisors

After choosing a root vertex, a degree-zero divisor is determined by its
coefficients away from the root.  This elementary integral linear
equivalence is the coordinate system used to prove finiteness of the graph
Jacobian without importing a matrix-tree theorem.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

/-- Vertices other than the chosen root. -/
abbrev ReducedVertex {V : Type*} (root : V) := {v : V // v ≠ root}

namespace Divisor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extend coefficients away from `root` to a divisor of degree zero. -/
def extendReduced (root : V) :
    (ReducedVertex root → ℤ) →ₗ[ℤ] Divisor V where
  toFun f v := if hv : v = root then -∑ w : ReducedVertex root, f w
    else f ⟨v, hv⟩
  map_add' f g := by
    funext v
    by_cases hv : v = root
    · subst v
      simp [Finset.sum_add_distrib]
      abel
    · simp [hv]
  map_smul' n f := by
    funext v
    by_cases hv : v = root
    · subst v
      simp only [Pi.smul_apply, smul_eq_mul]
      simp [Finset.mul_sum]
    · simp [hv]

@[simp]
theorem extendReduced_apply_root (root : V) (f : ReducedVertex root → ℤ) :
    extendReduced root f root = -∑ w, f w := by
  simp [extendReduced]

@[simp]
theorem extendReduced_apply_ne (root : V) (f : ReducedVertex root → ℤ)
    {v : V} (hv : v ≠ root) :
    extendReduced root f v = f ⟨v, hv⟩ := by
  simp [extendReduced, hv]

/-- The extension really has degree zero. -/
theorem degree_extendReduced (root : V) (f : ReducedVertex root → ℤ) :
    degree (extendReduced root f) = 0 := by
  rw [degree_apply, Fintype.sum_eq_add_sum_subtype_ne _ root]
  rw [extendReduced_apply_root]
  have hrest :
      (∑ x : ReducedVertex root, extendReduced root f x.1) = ∑ x, f x := by
    apply Fintype.sum_congr
    intro x
    exact extendReduced_apply_ne root f x.2
  rw [hrest]
  simp

/-- Restrict a degree-zero divisor to the vertices away from the root. -/
def restrictDegreeZero (root : V) :
    LinearMap.ker (degree (V := V)) →ₗ[ℤ] (ReducedVertex root → ℤ) where
  toFun D v := D.1 v.1
  map_add' D E := rfl
  map_smul' n D := rfl

/-- Extend rooted coordinates and record the degree-zero certificate. -/
def reducedToDegreeZero (root : V) :
    (ReducedVertex root → ℤ) →ₗ[ℤ] LinearMap.ker (degree (V := V)) :=
  (extendReduced root).codRestrict (LinearMap.ker degree)
    (degree_extendReduced root)

@[simp]
theorem reducedToDegreeZero_coe (root : V) (f : ReducedVertex root → ℤ) :
    (reducedToDegreeZero root f : Divisor V) = extendReduced root f :=
  rfl

/-- Rooted coordinates give an integral linear equivalence with all
degree-zero divisors. -/
def degreeZeroEquivReduced (root : V) :
    LinearMap.ker (degree (V := V)) ≃ₗ[ℤ] (ReducedVertex root → ℤ) where
  toLinearMap := restrictDegreeZero root
  invFun := reducedToDegreeZero root
  left_inv D := by
    apply Subtype.ext
    funext v
    by_cases hv : v = root
    · subst v
      have hd : ∑ x, D.1 x = 0 := D.2
      rw [Fintype.sum_eq_add_sum_subtype_ne _ root] at hd
      change extendReduced root (restrictDegreeZero root D) root = D.1 root
      rw [extendReduced_apply_root]
      change -(∑ w : ReducedVertex root, D.1 w.1) = D.1 root
      linarith
    · change extendReduced root (restrictDegreeZero root D) v = D.1 v
      rw [extendReduced_apply_ne root _ hv]
      rfl
  right_inv f := by
    funext v
    change extendReduced root f v.1 = f v
    rw [extendReduced_apply_ne root f v.2]

@[simp]
theorem degreeZeroEquivReduced_apply (root : V)
    (D : LinearMap.ker (degree (V := V))) (v : ReducedVertex root) :
    degreeZeroEquivReduced root D v = D.1 v.1 :=
  rfl

end Divisor

end LeanCo.LaplacianLFunctions
