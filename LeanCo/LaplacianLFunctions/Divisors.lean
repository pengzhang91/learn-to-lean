import LeanCo.LaplacianLFunctions.Multigraph
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Pi

/-!
# Divisors on a finite multigraph

A divisor is an integer-valued function on the vertices.  The degree is its
finite sum, and `vertexDivisor v` is the degree-one divisor concentrated at
`v`.
-/

namespace LeanCo.LaplacianLFunctions

/-- The group (and `ℤ`-module) of divisors on a vertex type. -/
abbrev Divisor (V : Type*) := V → ℤ

namespace Divisor

variable {V : Type*} [Fintype V]

/-- Degree of a divisor, as a `ℤ`-linear map. -/
def degree : Divisor V →ₗ[ℤ] ℤ where
  toFun D := ∑ v, D v
  map_add' D E := by
    exact Finset.sum_add_distrib
  map_smul' n D := by
    change (∑ v, n * D v) = n * ∑ v, D v
    exact (Finset.mul_sum _ _ _).symm

@[simp]
theorem degree_apply (D : Divisor V) : degree D = ∑ v, D v :=
  rfl

@[simp]
theorem degree_zero : degree (0 : Divisor V) = 0 := by
  simp

@[simp]
theorem degree_add (D E : Divisor V) : degree (D + E) = degree D + degree E := by
  exact LinearMap.map_add degree D E

@[simp]
theorem degree_neg (D : Divisor V) : degree (-D) = -degree D := by
  simp

@[simp]
theorem degree_sub (D E : Divisor V) : degree (D - E) = degree D - degree E := by
  simp

/-- The divisor with coefficient one at `v` and zero elsewhere. -/
def vertexDivisor [DecidableEq V] (v : V) : Divisor V :=
  fun w ↦ if w = v then 1 else 0

variable [DecidableEq V]

@[simp]
theorem vertexDivisor_apply (v w : V) : vertexDivisor v w = if w = v then 1 else 0 := by
  rfl

@[simp]
theorem vertexDivisor_same (v : V) : vertexDivisor v v = 1 := by
  simp

@[simp]
theorem vertexDivisor_of_ne {v w : V} (h : w ≠ v) : vertexDivisor v w = 0 := by
  simp [vertexDivisor, h]

@[simp]
theorem degree_vertexDivisor (v : V) : degree (vertexDivisor v) = 1 := by
  simp [degree, vertexDivisor]

end Divisor

end LeanCo.LaplacianLFunctions
