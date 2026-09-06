import LeanCo.Negami.ConcreteBoundaryGluing
import LeanCo.Negami.SplittingMatrix

/-!
# Fully concrete Negami splitting theorem

The paper's common-boundary hypothesis is represented by two finite
multigraphs equipped with embeddings of the same finite boundary type.  This
module combines the concrete pushout graph, the concrete quotient graphs,
and the abstract inverse-kernel calculation.  Thus the final theorem has no
unverified graph-theoretic gluing or quotient hypothesis.
-/

namespace LeanCo.Negami

open scoped Matrix

/-- A finite multigraph carrying a fixed labelled boundary type. -/
structure GraphOverBoundary (B : Type) [Fintype B] [DecidableEq B] where
  graph : FiniteMultigraph
  boundaryEmbedding : B ↪ graph.Vertex

namespace GraphOverBoundary

variable {B : Type} [Fintype B] [DecidableEq B]

/-- Forget that the boundary type was fixed externally. -/
abbrev toBoundaryMultigraph (K : GraphOverBoundary B) : BoundaryMultigraph where
  graph := K.graph
  Boundary := B
  boundaryFintype := inferInstance
  boundaryDecidableEq := inferInstance
  boundaryEmbedding := K.boundaryEmbedding

/-- The family of actual graph quotients indexed by every boundary
partition. -/
noncomputable def quotientFamily (K : GraphOverBoundary B)
    (α : FinitePartition B) : NegamiData :=
  (K.toBoundaryMultigraph.quotientGraph α).toNegamiData

/-- Theorem 5.2, fully instantiated with actual finite multigraphs, actual
pushout gluing, and actual boundary quotient graphs.  The only hypothesis is
the paper's stated algebraic condition that `Binv` is a left inverse of the
connectivity matrix. -/
theorem concrete_negami_splitting (K H : GraphOverBoundary B)
    {F : Type*} [Field F] (t x y : F)
    (Binv : Matrix (FinitePartition B) (FinitePartition B) F)
    (hBT : Binv * BoundaryData.connectivityMatrix FinitePartition.rho t = 1) :
    (K.toBoundaryMultigraph.gluedGraph H.toBoundaryMultigraph
      (Equiv.refl B)).stateSum t x y =
      BoundaryData.quotientStateVector K.quotientFamily t x y ⬝ᵥ
        (Binv *ᵥ
          (BoundaryData.quotientStateVector H.quotientFamily t x y)) := by
  apply BoundaryData.Gluing.negami_splitting
    (K.toBoundaryMultigraph.concreteGluingWitness H.toBoundaryMultigraph
      (Equiv.refl B))
    K.quotientFamily H.quotientFamily
  · intro α
    exact K.toBoundaryMultigraph.concreteQuotientWitness α
  · intro α
    exact H.toBoundaryMultigraph.concreteQuotientWitness α
  · exact FinitePartition.rho_comm
  · exact hBT

end GraphOverBoundary
end LeanCo.Negami
