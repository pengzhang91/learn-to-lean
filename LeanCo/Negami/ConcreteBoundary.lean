import LeanCo.Negami.FiniteGraph
import LeanCo.Negami.FinitePartition
import LeanCo.Negami.BoundaryGluing

/-! Concrete boundary partitions induced by multigraph connectivity. -/

namespace LeanCo.Negami

/-- A finite multigraph with a labelled, injectively embedded boundary. -/
structure BoundaryMultigraph where
  graph : FiniteMultigraph
  Boundary : Type
  [boundaryFintype : Fintype Boundary]
  [boundaryDecidableEq : DecidableEq Boundary]
  boundaryEmbedding : Boundary ↪ graph.Vertex

attribute [instance] BoundaryMultigraph.boundaryFintype
  BoundaryMultigraph.boundaryDecidableEq

namespace BoundaryMultigraph

variable (K : BoundaryMultigraph)

/-- The equivalence relation on boundary labels induced by a spanning state. -/
noncomputable def boundaryPartition (S : Finset K.graph.Edge) :
    FinitePartition K.Boundary := by
  classical
  refine ⟨fun i j ↦ decide ((K.graph.spanningGraph S).Reachable
    (K.boundaryEmbedding i) (K.boundaryEmbedding j)), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp
  · intro i j
    simp [SimpleGraph.reachable_comm]
  · intro i j k hij hjk
    simp only [decide_eq_true_eq] at hij hjk ⊢
    exact hij.trans hjk

theorem boundaryPartition_rel (S : Finset K.graph.Edge) (i j : K.Boundary) :
    (K.boundaryPartition S).1 i j = true ↔ (K.graph.spanningGraph S).Reachable
      (K.boundaryEmbedding i) (K.boundaryEmbedding j) := by
  classical
  simp [boundaryPartition]

/-- A boundary component maps to the ambient connected component containing
it. -/
noncomputable def boundaryComponentMap (S : Finset K.graph.Edge) :
    Quotient (K.boundaryPartition S).toSetoid →
      (K.graph.spanningGraph S).ConnectedComponent := by
  classical
  refine Quot.map (fun i ↦ K.boundaryEmbedding i) ?_
  intro i j hij
  change (K.boundaryPartition S).1 i j = true at hij
  exact (K.boundaryPartition_rel S i j).mp hij

theorem boundaryComponentMap_injective (S : Finset K.graph.Edge) :
    Function.Injective (K.boundaryComponentMap S) := by
  classical
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ i =>
    induction y using Quotient.inductionOn with
    | _ j =>
      apply Quotient.sound
      change Quot.mk (K.graph.spanningGraph S).Reachable (K.boundaryEmbedding i) =
        Quot.mk (K.graph.spanningGraph S).Reachable (K.boundaryEmbedding j) at hxy
      have hr : (K.graph.spanningGraph S).Reachable
          (K.boundaryEmbedding i) (K.boundaryEmbedding j) :=
        SimpleGraph.ConnectedComponent.exact hxy
      exact (K.boundaryPartition_rel S i j).mpr hr

/-- The concrete boundary graph supplies the abstract boundary-state data. -/
noncomputable def toBoundaryData : BoundaryData (FinitePartition K.Boundary) where
  toNegamiData := K.graph.toNegamiData
  boundaryType := K.boundaryPartition
  blocks := FinitePartition.blocks
  blocks_le_components := by
    intro S
    change Nat.card (Quotient (K.boundaryPartition S).toSetoid) ≤
      Nat.card (K.graph.spanningGraph S).ConnectedComponent
    exact Nat.card_le_card_of_injective (K.boundaryComponentMap S)
      (K.boundaryComponentMap_injective S)

end BoundaryMultigraph
end LeanCo.Negami
