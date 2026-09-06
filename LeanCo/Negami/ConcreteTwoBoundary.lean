import LeanCo.Negami.ConcreteSplitting
import LeanCo.Negami.GraphInvariance
import LeanCo.Negami.TwoBoundaryFormula

/-!
# Fully concrete two-boundary splitting formula

This specializes the general concrete splitting theorem to a two-element
boundary, supplies the explicit inverse proved in Proposition 6.2, transports
from actual partitions to the paper's `(C,D)` ordering, and expands the result
into the four terms of Corollary 6.3.
-/

open scoped Matrix

namespace LeanCo.Negami
namespace GraphOverBoundary

/-- For the discrete two-boundary partition, the generated vertex relation is
just equality.  Notice that the elementary relation itself need not contain
the diagonal at an internal vertex; reflexivity is supplied by `EqvGen`. -/
theorem discrete_boundaryQuotientSetoid_rel_iff_eq
    (K : GraphOverBoundary (Fin 2)) (u v : K.graph.Vertex) :
    (K.toBoundaryMultigraph.boundaryQuotientSetoid
      discreteTwoPartition) u v ↔ u = v := by
  constructor
  · intro h
    change Relation.EqvGen
      (K.toBoundaryMultigraph.boundaryIdentification
        discreteTwoPartition) u v at h
    induction h with
    | rel a b hab =>
        rcases hab with ⟨i, j, hi, hj, hij⟩
        have hEq : i = j := (discreteTwoPartition_rel i j).mp hij
        subst j
        exact hi.symm.trans hj
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    subst v
    exact Relation.EqvGen.refl u

/-- The vertex quotient by the discrete two-boundary partition is canonically
equivalent to the original vertex type. -/
noncomputable def discreteQuotientVertexEquiv
    (K : GraphOverBoundary (Fin 2)) :
    Quotient (K.toBoundaryMultigraph.boundaryQuotientSetoid
      discreteTwoPartition) ≃ K.graph.Vertex where
  toFun := Quotient.lift id (by
    intro u v huv
    exact (K.discrete_boundaryQuotientSetoid_rel_iff_eq u v).mp huv)
  invFun := K.toBoundaryMultigraph.boundaryQuotientVertex
    discreteTwoPartition
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ v => rfl
  right_inv v := rfl

/-- Quotienting a graph over a two-element boundary by the discrete
partition gives an actually isomorphic labelled multigraph. -/
noncomputable def discreteQuotientIso
    (K : GraphOverBoundary (Fin 2)) :
    FiniteMultigraph.Iso K.graph
      (K.toBoundaryMultigraph.quotientGraph discreteTwoPartition) where
  vertexEquiv := (K.discreteQuotientVertexEquiv).symm
  edgeEquiv := Equiv.refl _
  map_ends _ := rfl

/-- The discrete boundary quotient has exactly the original graph state
sum, as a consequence of the explicit labelled multigraph isomorphism. -/
theorem stateSum_discreteQuotient
    (K : GraphOverBoundary (Fin 2)) {R : Type*} [CommSemiring R]
    (t x y : R) :
    (K.toBoundaryMultigraph.quotientGraph
      discreteTwoPartition).stateSum t x y = K.graph.stateSum t x y := by
  exact (K.discreteQuotientIso.stateSum_eq t x y).symm

/-- Quotient state sums in the `(connected, discrete)` partition ordering. -/
noncomputable def twoQuotientStateVector
    (K : GraphOverBoundary (Fin 2)) {F : Type*} [Field F]
    (t x y : F) : Fin 2 → F :=
  fun i =>
    (K.toBoundaryMultigraph.quotientGraph (twoPartition i)).stateSum t x y

/-- Corollary 6.3 for actual finite multigraphs and their actual pushout and
quotient graphs.  The necessary restrictions `t != 0,1` are explicit. -/
theorem concrete_twoBoundary_four_term
    (K H : GraphOverBoundary (Fin 2)) {F : Type*} [Field F]
    (t x y : F) (ht : t ≠ 0) (ht1 : t ≠ 1) :
    (K.toBoundaryMultigraph.gluedGraph H.toBoundaryMultigraph
      (Equiv.refl (Fin 2))).stateSum t x y =
      (K.toBoundaryMultigraph.quotientGraph
          connectedTwoPartition).stateSum t x y *
          (H.toBoundaryMultigraph.quotientGraph
            connectedTwoPartition).stateSum t x y / (t - 1) -
        (K.toBoundaryMultigraph.quotientGraph
          connectedTwoPartition).stateSum t x y *
          H.graph.stateSum t x y / (t * (t - 1)) -
        K.graph.stateSum t x y *
          (H.toBoundaryMultigraph.quotientGraph
            connectedTwoPartition).stateSum t x y / (t * (t - 1)) +
        K.graph.stateSum t x y * H.graph.stateSum t x y /
          (t * (t - 1)) := by
  let qK := BoundaryData.quotientStateVector K.quotientFamily t x y
  let qH := BoundaryData.quotientStateVector H.quotientFamily t x y
  calc
    (K.toBoundaryMultigraph.gluedGraph H.toBoundaryMultigraph
      (Equiv.refl (Fin 2))).stateSum t x y =
        qK ⬝ᵥ (twoBoundaryPartitionInverse t *ᵥ qH) := by
      exact K.concrete_negami_splitting H t x y
        (twoBoundaryPartitionInverse t)
        (twoBoundaryPartitionInverse_mul_connectivity t ht ht1)
    _ = K.twoQuotientStateVector t x y ⬝ᵥ
        (twoBoundaryInverse t *ᵥ H.twoQuotientStateVector t x y) := by
      have hqK : (fun i => qK (twoPartitionEquiv i)) =
          K.twoQuotientStateVector t x y := by
        funext i
        rfl
      have hqH : (fun i => qH (twoPartitionEquiv i)) =
          H.twoQuotientStateVector t x y := by
        funext i
        rfl
      rw [← hqK, ← hqH]
      exact reindexed_inverse_pairing twoPartitionEquiv
        (twoBoundaryInverse t) qK qH
    _ = K.twoQuotientStateVector t x y 0 *
          H.twoQuotientStateVector t x y 0 / (t - 1) -
        K.twoQuotientStateVector t x y 0 *
          H.twoQuotientStateVector t x y 1 / (t * (t - 1)) -
        K.twoQuotientStateVector t x y 1 *
          H.twoQuotientStateVector t x y 0 / (t * (t - 1)) +
        K.twoQuotientStateVector t x y 1 *
          H.twoQuotientStateVector t x y 1 / (t * (t - 1)) :=
      twoBoundary_inverse_pairing t ht ht1 _ _
    _ = _ := by
      simp only [twoQuotientStateVector]
      rw [show twoPartition 0 = connectedTwoPartition by
          simp [twoPartition],
        show twoPartition 1 = discreteTwoPartition by
          simp [twoPartition],
        K.stateSum_discreteQuotient t x y,
        H.stateSum_discreteQuotient t x y]

end GraphOverBoundary
end LeanCo.Negami
