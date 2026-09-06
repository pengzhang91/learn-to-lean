import LeanCo.LaplacianLFunctions.Connectivity
import LeanCo.LaplacianLFunctions.RootCoordinates
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Finiteness of the Jacobian

For a finite nonempty connected loopless multigraph, the Laplacian lattice has
full rank in the lattice of degree-zero divisors.  Consequently the quotient
of degree-zero divisors by principal divisors is finite.  The latter quotient
is canonically linearly equivalent to the Jacobian.

The rank computation uses rooted coordinates for degree-zero divisors and the
fact that an integral harmonic potential on a connected graph is constant.
-/

namespace LeanCo.LaplacianLFunctions

open scoped BigOperators

namespace LooplessMultigraph

variable {V : Type*} [Fintype V]

/-- The Laplacian lattice, regarded as a submodule of the degree-zero
divisors. -/
def degreeZeroLaplacianLattice (G : LooplessMultigraph V) :
    Submodule ℤ (LinearMap.ker (Divisor.degree (V := V))) :=
  G.laplacianLattice.comap
    (LinearMap.ker (Divisor.degree (V := V))).subtype

@[simp]
theorem mem_degreeZeroLaplacianLattice_iff
    (G : LooplessMultigraph V)
    (D : LinearMap.ker (Divisor.degree (V := V))) :
    D ∈ G.degreeZeroLaplacianLattice ↔
      (D.1 : Divisor V) ∈ G.laplacianLattice :=
  Iff.rfl

/-- Evaluation at a root identifies harmonic integral potentials with
integers on a connected graph. -/
noncomputable def laplacianKernelEquivInt
    (G : LooplessMultigraph V) (hconn : G.Connected) (root : V) :
    LinearMap.ker G.laplacian ≃ₗ[ℤ] ℤ where
  toFun D := D.1 root
  invFun z := ⟨fun _ ↦ z, by
    ext v
    simp [laplacian_apply]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv D := by
    apply Subtype.ext
    funext v
    exact G.constant_of_laplacian_eq_zero hconn D.1 D.2 root v
  right_inv _ := rfl

/-- Rooted coordinates compute the rank of degree-zero divisors. -/
theorem finrank_degreeZero_eq_card_sub_one (root : V) :
    Module.finrank ℤ (LinearMap.ker (Divisor.degree (V := V))) =
      Fintype.card V - 1 := by
  classical
  calc
    Module.finrank ℤ (LinearMap.ker (Divisor.degree (V := V))) =
        Module.finrank ℤ (ReducedVertex root → ℤ) :=
      (Divisor.degreeZeroEquivReduced root).finrank_eq
    _ = Fintype.card (ReducedVertex root) := Module.finrank_pi ℤ
    _ = Fintype.card V - 1 := Set.card_ne_eq root

/-- On a connected graph, the Laplacian lattice has the same rank as the
degree-zero divisor lattice. -/
theorem finrank_degreeZeroLaplacianLattice_eq
    (G : LooplessMultigraph V) [Nonempty V] (hconn : G.Connected) :
    Module.finrank ℤ G.degreeZeroLaplacianLattice =
      Module.finrank ℤ (LinearMap.ker (Divisor.degree (V := V))) := by
  classical
  let root : V := Classical.choice (inferInstance : Nonempty V)
  rw [degreeZeroLaplacianLattice,
    (Submodule.comapSubtypeEquivOfLe
      G.laplacianLattice_le_degree_ker).finrank_eq]
  have hnullity :=
    (LinearMap.ker G.laplacian).finrank_quotient_add_finrank
  rw [(G.laplacian.quotKerEquivRange).finrank_eq] at hnullity
  have hker : Module.finrank ℤ (LinearMap.ker G.laplacian) = 1 := by
    simpa using (G.laplacianKernelEquivInt hconn root).finrank_eq
  have hdivisor : Module.finrank ℤ (Divisor V) = Fintype.card V :=
    Module.finrank_pi ℤ
  have hlattice : Module.finrank ℤ G.laplacianLattice = Fintype.card V - 1 := by
    change Module.finrank ℤ (LinearMap.range G.laplacian) = Fintype.card V - 1
    rw [hker, hdivisor] at hnullity
    have hcard : 1 ≤ Fintype.card V := Fintype.card_pos
    omega
  rw [hlattice, finrank_degreeZero_eq_card_sub_one root]

/-- The canonical linear map from degree-zero divisors to the Jacobian. -/
def jacobianClassLinear (G : LooplessMultigraph V) :
    LinearMap.ker (Divisor.degree (V := V)) →ₗ[ℤ] G.Jacobian where
  toFun := G.jacobianClass
  map_add' D E := by
    apply Subtype.ext
    exact G.divisorClass.map_add D.1 E.1
  map_smul' n D := by
    apply Subtype.ext
    exact G.divisorClass.map_smul n D.1

/-- Every Jacobian class has a degree-zero divisor representative. -/
theorem jacobianClassLinear_surjective (G : LooplessMultigraph V) :
    Function.Surjective G.jacobianClassLinear := by
  intro C
  obtain ⟨D, hD⟩ := Submodule.Quotient.mk_surjective
    G.laplacianLattice C.1
  change G.divisorClass D = C.1 at hD
  have hdegree : Divisor.degree D = 0 := by
    calc
      Divisor.degree D = G.picardDegree (G.divisorClass D) :=
        (G.picardDegree_divisorClass D).symm
      _ = G.picardDegree C.1 := congrArg G.picardDegree hD
      _ = 0 := C.2
  refine ⟨⟨D, hdegree⟩, ?_⟩
  apply Subtype.ext
  exact hD

/-- The kernel of the degree-zero class map consists exactly of principal
degree-zero divisors. -/
theorem ker_jacobianClassLinear (G : LooplessMultigraph V) :
    LinearMap.ker G.jacobianClassLinear =
      G.degreeZeroLaplacianLattice := by
  ext D
  constructor
  · intro h
    have hclass : G.divisorClass D.1 = 0 := by
      exact congrArg Subtype.val h
    change Submodule.Quotient.mk D.1 = 0 at hclass
    change D.1 ∈ G.laplacianLattice
    exact (Submodule.Quotient.mk_eq_zero G.laplacianLattice).mp hclass
  · intro h
    change D.1 ∈ G.laplacianLattice at h
    apply Subtype.ext
    change G.divisorClass D.1 = 0
    change Submodule.Quotient.mk D.1 = 0
    exact (Submodule.Quotient.mk_eq_zero G.laplacianLattice).mpr h

/-- Degree-zero divisors modulo the Laplacian lattice are canonically the
Jacobian. -/
noncomputable def degreeZeroQuotientEquivJacobian
    (G : LooplessMultigraph V) :
    (LinearMap.ker (Divisor.degree (V := V)) ⧸
      G.degreeZeroLaplacianLattice) ≃ₗ[ℤ] G.Jacobian :=
  (Submodule.quotEquivOfEq G.degreeZeroLaplacianLattice
      (LinearMap.ker G.jacobianClassLinear)
      G.ker_jacobianClassLinear.symm).trans
    (G.jacobianClassLinear.quotKerEquivOfSurjective
      G.jacobianClassLinear_surjective)

/-- The Jacobian of a finite nonempty connected loopless multigraph is a
finite type. -/
theorem finite_jacobian (G : LooplessMultigraph V) [Nonempty V]
    (hconn : G.Connected) : Finite G.Jacobian := by
  letI : Finite
      (LinearMap.ker (Divisor.degree (V := V)) ⧸
        G.degreeZeroLaplacianLattice) :=
    Submodule.finiteQuotientOfFreeOfRankEq
      G.degreeZeroLaplacianLattice
      (G.finrank_degreeZeroLaplacianLattice_eq hconn)
  exact Finite.of_equiv _ G.degreeZeroQuotientEquivJacobian.toEquiv

/-- A noncomputable `Fintype` instance on the Jacobian of a connected graph. -/
noncomputable instance jacobianFintype (G : LooplessMultigraph V) [Nonempty V]
    [hconn : Fact G.Connected] : Fintype G.Jacobian := by
  letI := G.finite_jacobian hconn.out
  exact Fintype.ofFinite G.Jacobian

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
