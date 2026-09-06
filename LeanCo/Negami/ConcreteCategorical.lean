import LeanCo.Negami.CategoricalBoundary
import LeanCo.Negami.ConcreteBoundaryGluing

/-!
# Concrete categorical gluing for finite multigraphs

The abstract object-level formula is instantiated here by the pushout-style
graph construction and the component equivalence proved in
`ConcreteBoundaryGluing`.
-/

namespace LeanCo.Negami
namespace BoundaryMultigraph

variable (K H : BoundaryMultigraph)

/-- Theorem 4.5 in its fully concrete and partition-grouped form. -/
noncomputable def categoricalObjectEquiv_gluedGraph
    (e : K.Boundary ≃ H.Boundary) :
    GradedObject.Equiv (K.gluedGraph H e).stateObject
      (BoundaryData.categoricalPairing K.toBoundaryData
        (K.reindexedBoundaryData H e) FinitePartition.rho) :=
  (K.concreteGluingWitness H e).categoricalObjectEquiv

/-- The same formula after realization as finite free modules. -/
noncomputable def categoricalRealizationEquiv_gluedGraph
    (e : K.Boundary ≃ H.Boundary) (k : Type*) [Semiring k] :
    (K.gluedGraph H e).stateObject.realization k ≃ₗ[k]
      (BoundaryData.categoricalPairing K.toBoundaryData
        (K.reindexedBoundaryData H e) FinitePartition.rho).realization k :=
  (K.concreteGluingWitness H e).categoricalRealizationEquiv k

/-- Equation (4.8): decategorification is the sum over the two boundary
partition sectors with connectivity weight `t^rho`. -/
theorem stateSum_gluedGraph_partitioned
    (e : K.Boundary ≃ H.Boundary)
    {R : Type*} [CommSemiring R] (t x y : R) :
    (K.gluedGraph H e).stateSum t x y =
      ∑ p : FinitePartition K.Boundary × FinitePartition K.Boundary,
        t ^ FinitePartition.rho p.1 p.2 *
          (K.toBoundaryData.boundaryObject p.1).hilbert t x y *
          ((K.reindexedBoundaryData H e).boundaryObject p.2).hilbert t x y := by
  rw [← (K.gluedGraph H e).hilbert_stateObject]
  exact (K.concreteGluingWitness H e).hilbert_categoricalPairing t x y

end BoundaryMultigraph
end LeanCo.Negami
