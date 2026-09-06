import LeanCo.LaplacianLFunctions.Picard
import Mathlib.LinearAlgebra.StdBasis

/-!
# Transporting the Laplacian lattice from vertex classes

This file formalizes Lemma 4.2 of arXiv:2608.29981.  A bijection of vertices
reindexes the free abelian groups of divisors.  If an additive equivalence of
Picard groups sends every degree-one vertex class to the correspondingly
reindexed vertex class, then the reindexing carries one Laplacian lattice
exactly onto the other.
-/

namespace LeanCo.LaplacianLFunctions

/-- Reindex integer-valued divisors along a vertex equivalence. -/
def divisorReindex {V' V : Type*} (sigma : V' ≃ V) :
    Divisor V' ≃ₗ[ℤ] Divisor V where
  toFun D v := D (sigma.symm v)
  invFun D v' := D (sigma v')
  left_inv D := by
    funext v'
    simp
  right_inv D := by
    funext v
    simp
  map_add' D E := by
    rfl
  map_smul' n D := by
    rfl

@[simp]
theorem divisorReindex_apply {V' V : Type*} (sigma : V' ≃ V)
    (D : Divisor V') (v : V) :
    divisorReindex sigma D v = D (sigma.symm v) :=
  rfl

@[simp]
theorem divisorReindex_symm_apply {V' V : Type*} (sigma : V' ≃ V)
    (D : Divisor V) (v' : V') :
    (divisorReindex sigma).symm D v' = D (sigma v') :=
  rfl

@[simp]
theorem divisorReindex_vertexDivisor {V' V : Type*}
    [Fintype V'] [Fintype V] [DecidableEq V'] [DecidableEq V]
    (sigma : V' ≃ V) (v' : V') :
    divisorReindex sigma (Divisor.vertexDivisor v') =
      Divisor.vertexDivisor (sigma v') := by
  ext v
  by_cases h : sigma.symm v = v'
  · have hv : v = sigma v' := by
      rw [← h]
      simp
    simp [Divisor.vertexDivisor_apply, hv]
  · have hv : v ≠ sigma v' := by
      intro hv
      apply h
      rw [hv]
      simp
    simp [Divisor.vertexDivisor_apply, h, hv]

namespace Divisor

/-- The paper's vertex divisor is the standard basis vector of the free
`ℤ`-module of divisors. -/
theorem vertexDivisor_eq_basisFun {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) :
    vertexDivisor v = Pi.basisFun ℤ V v := by
  ext w
  simp [Pi.basisFun_apply, Pi.single_apply, vertexDivisor_apply, eq_comm]

end Divisor

namespace LooplessMultigraph

variable {V' V : Type*} [Fintype V'] [Fintype V]

/-- Compatibility on vertex classes extends to all divisor classes because
the vertex divisors form the standard basis of the divisor module. -/
theorem picardEquiv_divisorClass_reindex
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    [DecidableEq V'] [DecidableEq V]
    (F : G'.Picard ≃+ G.Picard) (sigma : V' ≃ V)
    (hvertex : ∀ v' : V',
      F (G'.vertexClass v' : G'.Picard) =
        (G.vertexClass (sigma v') : G.Picard))
    (D : Divisor V') :
    F (G'.divisorClass D) =
      G.divisorClass (divisorReindex sigma D) := by
  let lhs : Divisor V' →ₗ[ℤ] G.Picard :=
    F.toIntLinearEquiv.toLinearMap.comp G'.divisorClass
  let rhs : Divisor V' →ₗ[ℤ] G.Picard :=
    G.divisorClass.comp (divisorReindex sigma).toLinearMap
  have hlr : lhs = rhs := by
    apply (Pi.basisFun ℤ V').ext
    intro v'
    change F (G'.divisorClass (Pi.basisFun ℤ V' v')) =
      G.divisorClass (divisorReindex sigma (Pi.basisFun ℤ V' v'))
    rw [← Divisor.vertexDivisor_eq_basisFun v']
    rw [divisorReindex_vertexDivisor]
    exact hvertex v'
  exact LinearMap.congr_fun hlr D

/-- Membership in the Laplacian lattice is equivalent to vanishing of the
corresponding divisor class. -/
theorem mem_laplacianLattice_iff_divisorClass_eq_zero
    (G : LooplessMultigraph V) (D : Divisor V) :
    D ∈ G.laplacianLattice ↔ G.divisorClass D = 0 := by
  change D ∈ G.laplacianLattice ↔
    Submodule.Quotient.mk D = 0
  rw [Submodule.Quotient.mk_eq_zero]

/-- **Lemma 4.2 (lattice transport).**  An additive Picard equivalence that
matches all vertex classes transports the entire Laplacian lattice along the
same vertex ordering. -/
theorem map_laplacianLattice_eq_of_picardEquiv
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    [DecidableEq V'] [DecidableEq V]
    (F : G'.Picard ≃+ G.Picard) (sigma : V' ≃ V)
    (hvertex : ∀ v' : V',
      F (G'.vertexClass v' : G'.Picard) =
        (G.vertexClass (sigma v') : G.Picard)) :
    Submodule.map (divisorReindex sigma).toLinearMap
        G'.laplacianLattice = G.laplacianLattice := by
  ext D
  constructor
  · rintro ⟨D', hD', rfl⟩
    apply (G.mem_laplacianLattice_iff_divisorClass_eq_zero _).mpr
    change G.divisorClass (divisorReindex sigma D') = 0
    rw [← G'.picardEquiv_divisorClass_reindex G F sigma hvertex]
    rw [(G'.mem_laplacianLattice_iff_divisorClass_eq_zero D').mp hD']
    exact F.map_zero
  · intro hD
    let D' : Divisor V' := (divisorReindex sigma).symm D
    have hclassD : G.divisorClass D = 0 :=
      (G.mem_laplacianLattice_iff_divisorClass_eq_zero D).mp hD
    have hFD' : F (G'.divisorClass D') = 0 := by
      rw [G'.picardEquiv_divisorClass_reindex G F sigma hvertex]
      simpa [D'] using hclassD
    have hclassD' : G'.divisorClass D' = 0 := by
      apply F.injective
      simpa using hFD'
    refine ⟨D',
      (G'.mem_laplacianLattice_iff_divisorClass_eq_zero D').mpr hclassD', ?_⟩
    simp [D']

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
