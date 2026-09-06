import LeanCo.Negami.StateSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite labelled multigraphs

This is the concrete graph model used for arXiv:2608.30053.  Vertices and
edge labels are finite types, while an edge label is sent to an unordered
pair of endpoints.  Consequently distinct labels can describe parallel
edges and a diagonal unordered pair describes a loop.

A state is a finite set of edge labels.  Its connectivity is the equivalence
closure of adjacency in the associated spanning simple graph.  Loops are
discarded by that simple graph, exactly because they do not alter connected
components.
-/

namespace LeanCo.Negami

/-- A finite undirected multigraph, allowing loops and parallel edges. -/
structure FiniteMultigraph where
  Vertex : Type
  Edge : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  [edgeFintype : Fintype Edge]
  [edgeDecidableEq : DecidableEq Edge]
  ends : Edge → Sym2 Vertex

attribute [instance] FiniteMultigraph.vertexFintype
  FiniteMultigraph.vertexDecidableEq FiniteMultigraph.edgeFintype
  FiniteMultigraph.edgeDecidableEq

namespace FiniteMultigraph

variable (G : FiniteMultigraph)

/-- The spanning simple graph that records the connectivity of a state. -/
def stateGraph (S : Finset G.Edge) : SimpleGraph G.Vertex :=
  SimpleGraph.fromEdgeSet ↑(S.image G.ends)

/-- An alias emphasizing that all vertices, including isolated ones, remain. -/
abbrev spanningGraph (S : Finset G.Edge) : SimpleGraph G.Vertex :=
  G.stateGraph S

/-- Two vertices are connected in the spanning state. -/
def StateConnected (S : Finset G.Edge) (u v : G.Vertex) : Prop :=
  (G.stateGraph S).Reachable u v

theorem stateConnected_iff_reachable (S : Finset G.Edge) (u v : G.Vertex) :
    G.StateConnected S u v ↔ (G.stateGraph S).Reachable u v :=
  Iff.rfl

/-- State connectivity as a setoid on the fixed vertex set. -/
def stateSetoid (S : Finset G.Edge) : Setoid G.Vertex :=
  (G.stateGraph S).reachableSetoid

@[simp] theorem stateSetoid_rel (S : Finset G.Edge) (u v : G.Vertex) :
    G.stateSetoid S u v ↔ G.StateConnected S u v :=
  Iff.rfl

/-- The equivalence-closure presentation of state connectivity. -/
theorem stateConnected_iff_eqvGen (S : Finset G.Edge) (u v : G.Vertex) :
    G.StateConnected S u v ↔
      Relation.EqvGen (G.stateGraph S).Adj u v := by
  constructor
  · intro h
    rw [StateConnected, SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Relation.EqvGen.refl _
    | tail hxy hyz ih =>
        exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hyz)
  · intro h
    induction h with
    | rel _ _ hxy => exact SimpleGraph.Adj.reachable hxy
    | refl x => exact SimpleGraph.Reachable.refl x
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Connected components of a spanning state. -/
abbrev StateComponent (S : Finset G.Edge) :=
  Quotient (G.stateSetoid S)

/-- The number `ω_G(S)` of connected components of a spanning state. -/
noncomputable def omega (S : Finset G.Edge) : ℕ :=
  Nat.card (G.StateComponent S)

/-- Compatibility alias for graph-theoretic component terminology. -/
noncomputable abbrev components (S : Finset G.Edge) : ℕ := G.omega S

theorem omega_eq_card_components (S : Finset G.Edge) :
    G.omega S = Nat.card (G.StateComponent S) :=
  rfl

/-! ## The concrete state-sum data -/

/-- Forget the vertex presentation after recording the component count of
every spanning state. -/
noncomputable abbrev toNegamiData : NegamiData where
  Edge := G.Edge
  edgeFintype := G.edgeFintype
  edgeDecidableEq := G.edgeDecidableEq
  components := G.omega

@[simp] theorem toNegamiData_components (S : Finset G.Edge) :
    G.toNegamiData.components S = G.omega S :=
  rfl

/-- The concrete three-variable Negami polynomial. -/
noncomputable abbrev polynomial (R : Type*) [CommSemiring R] :
    MvPolynomial Degree R :=
  G.toNegamiData.polynomial R

/-- The concrete scalar state sum. -/
noncomputable abbrev stateSum {R : Type*} [CommSemiring R]
    (t x y : R) : R :=
  G.toNegamiData.stateSum t x y

/-- The finite triply graded state object attached to a graph. -/
noncomputable abbrev stateObject : GradedObject :=
  G.toNegamiData.stateObject

theorem polynomial_eq_state_sum (R : Type*) [CommSemiring R] :
    G.polynomial R =
      ∑ S : Finset G.Edge,
        MvPolynomial.monomial
          (Finsupp.single 0 (G.omega S) + Finsupp.single 1 S.card +
            Finsupp.single 2 (Nat.card G.Edge - S.card)) 1 :=
  rfl

theorem hilbert_stateObject {R : Type*} [CommSemiring R]
    (t x y : R) :
    G.stateObject.hilbert t x y = G.stateSum t x y :=
  G.toNegamiData.hilbert_stateObject t x y

theorem eval_polynomial {R : Type*} [CommSemiring R]
    (t x y : R) :
    MvPolynomial.eval (NegamiData.evalPoint t x y) (G.polynomial R) =
      G.stateSum t x y :=
  G.toNegamiData.eval_polynomial t x y

end FiniteMultigraph

end LeanCo.Negami
