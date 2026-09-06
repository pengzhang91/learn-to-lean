import LeanCo.LaplacianLFunctions.Laplacian
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Picard groups and Jacobians of finite multigraphs

For a finite loopless multigraph `G`, the Picard group is the quotient of
integer-valued divisors by the Laplacian lattice.  Since every principal
divisor has degree zero, degree descends to the quotient.  Its degree-zero
submodule is the graph Jacobian.
-/

namespace LeanCo.LaplacianLFunctions

namespace LooplessMultigraph

variable {V : Type*} [Fintype V]

/-- Divisor classes modulo the Laplacian lattice. -/
abbrev Picard (G : LooplessMultigraph V) :=
  Divisor V ⧸ G.laplacianLattice

/-- The canonical map from divisors to divisor classes. -/
def divisorClass (G : LooplessMultigraph V) : Divisor V →ₗ[ℤ] G.Picard :=
  G.laplacianLattice.mkQ

@[simp]
theorem divisorClass_apply (G : LooplessMultigraph V) (D : Divisor V) :
    G.divisorClass D = Submodule.Quotient.mk D :=
  rfl

/-- Degree on divisor classes. -/
def picardDegree (G : LooplessMultigraph V) : G.Picard →ₗ[ℤ] ℤ :=
  G.laplacianLattice.liftQ Divisor.degree
    G.laplacianLattice_le_degree_ker

@[simp]
theorem picardDegree_divisorClass (G : LooplessMultigraph V)
    (D : Divisor V) :
    G.picardDegree (G.divisorClass D) = Divisor.degree D :=
  rfl

/-- The Jacobian is the degree-zero part of the Picard group. -/
abbrev Jacobian (G : LooplessMultigraph V) :=
  LinearMap.ker G.picardDegree

/-- Divisor classes of a fixed degree. -/
abbrev PicardDegree (G : LooplessMultigraph V) (d : ℤ) :=
  {C : G.Picard // G.picardDegree C = d}

/-- A principal divisor has trivial divisor class. -/
@[simp]
theorem divisorClass_laplacian (G : LooplessMultigraph V)
    (D : Divisor V) :
    G.divisorClass (G.laplacian D) = 0 := by
  change Submodule.Quotient.mk (G.laplacian D) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨D, rfl⟩

/-- Two divisors have the same Picard class exactly when their difference is
principal. -/
theorem divisorClass_eq_iff_sub_mem (G : LooplessMultigraph V)
    (D E : Divisor V) :
    G.divisorClass D = G.divisorClass E ↔
      D - E ∈ G.laplacianLattice := by
  exact Submodule.Quotient.eq G.laplacianLattice

/-- A degree-zero divisor determines a Jacobian element. -/
def jacobianClass (G : LooplessMultigraph V)
    (D : LinearMap.ker (Divisor.degree (V := V))) : G.Jacobian :=
  ⟨G.divisorClass D.1, by
    change G.picardDegree (G.divisorClass D.1) = 0
    rw [G.picardDegree_divisorClass]
    exact D.2⟩

@[simp]
theorem jacobianClass_coe (G : LooplessMultigraph V)
    (D : LinearMap.ker (Divisor.degree (V := V))) :
    (G.jacobianClass D : G.Picard) = G.divisorClass D.1 :=
  rfl

/-- The class of a vertex divisor, viewed in degree one. -/
def vertexClass (G : LooplessMultigraph V) [DecidableEq V]
    (v : V) : G.PicardDegree 1 :=
  ⟨G.divisorClass (Divisor.vertexDivisor v), by
    change G.picardDegree
      (G.divisorClass (Divisor.vertexDivisor v)) = 1
    rw [G.picardDegree_divisorClass]
    exact Divisor.degree_vertexDivisor v⟩

@[simp]
theorem vertexClass_coe (G : LooplessMultigraph V) [DecidableEq V]
    (v : V) :
    (G.vertexClass v : G.Picard) =
      G.divisorClass (Divisor.vertexDivisor v) :=
  rfl

/-- Equality of vertex classes is exactly principality of the difference of
the corresponding degree-one divisors. -/
theorem vertexClass_eq_iff (G : LooplessMultigraph V) [DecidableEq V]
    (v w : V) :
    G.vertexClass v = G.vertexClass w ↔
      Divisor.vertexDivisor v - Divisor.vertexDivisor w ∈
        G.laplacianLattice := by
  rw [Subtype.ext_iff]
  exact G.divisorClass_eq_iff_sub_mem _ _

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
