import LeanCo.Negami.GraphInvariance
import LeanCo.Negami.InitialValue
import LeanCo.Negami.Minors
import LeanCo.Negami.TutteRelation
import LeanCo.Negami.ConcreteCategorical
import LeanCo.Negami.ConcreteSplitting
import LeanCo.Negami.ConcreteTwoBoundary
import LeanCo.Negami.CycleFour
import LeanCo.Negami.ConcreteCycleFour
import LeanCo.Negami.CompletionObstruction

/-!
# End-to-end entry point for arXiv:2608.30053

Importing this module exposes the complete formal chain used by the proved
results of the paper:

* finite labelled multigraphs with loops and parallel edges;
* the spanning-state polynomial, its isolated-vertex value, and the
  deletion--contraction recurrence;
* an explicit finite triply graded object, its free-module realization, and
  graph-isomorphism invariance;
* actual boundary partitions, graph quotients, and pushout-style gluing;
* the object-level partitioned splitting equivalence and its Hilbert sum;
* the quotient-vector identity `q = T F` and the inverse-kernel splitting
  theorem for actual graphs;
* the exhaustive two-boundary partition calculation, explicit inverse, and
  four-term specialization;
* the complete finite state check for the four-cycle example, including
  explicit graph isomorphisms for its quotient and glued graphs;
* the Laurent finite-support obstruction and a locally finite infinite
  graded object whose completed Euler series supplies the inverse.

The paper's Conjecture 9.1 is intentionally not asserted: it asks for new
derived categorical structure beyond the additive construction proved in the
paper.  The formalization proves the additive and scalar results and records
the exact finite-support obstruction motivating that conjecture.
-/

namespace LeanCo.Negami

open scoped Matrix

namespace BoundaryMultigraph

/-- Mizukai, Theorem 4.5, after realization as a state-sum identity. -/
theorem mizukai_theorem_4_5
    (K H : BoundaryMultigraph) (e : K.Boundary ≃ H.Boundary)
    {R : Type*} [CommSemiring R] (t x y : R) :
    (K.gluedGraph H e).stateSum t x y =
      ∑ p : FinitePartition K.Boundary × FinitePartition K.Boundary,
        t ^ FinitePartition.rho p.1 p.2 *
          (K.toBoundaryData.boundaryObject p.1).hilbert t x y *
          ((K.reindexedBoundaryData H e).boundaryObject p.2).hilbert t x y :=
  K.stateSum_gluedGraph_partitioned H e t x y

end BoundaryMultigraph

namespace GraphOverBoundary

/-- Mizukai, Theorem 5.2, for concrete finite multigraphs and quotients. -/
theorem mizukai_theorem_5_2
    {B : Type} [Fintype B] [DecidableEq B]
    (K H : GraphOverBoundary B)
    {F : Type*} [Field F] (t x y : F)
    (Binv : Matrix (FinitePartition B) (FinitePartition B) F)
    (hBT : Binv * BoundaryData.connectivityMatrix FinitePartition.rho t = 1) :
    (K.toBoundaryMultigraph.gluedGraph H.toBoundaryMultigraph
      (Equiv.refl B)).stateSum t x y =
      BoundaryData.quotientStateVector K.quotientFamily t x y ⬝ᵥ
        (Binv *ᵥ
          (BoundaryData.quotientStateVector H.quotientFamily t x y)) :=
  K.concrete_negami_splitting H t x y Binv hBT

end GraphOverBoundary

end LeanCo.Negami
