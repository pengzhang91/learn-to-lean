import LeanCo.PackingEdgeColoring.ComponentRotation

/-!
# Components after deleting a bridge

Deleting a bridge from a preconnected graph produces precisely the two
endpoint components.  This file packages that fact and combines it with
component restriction of a rotation system, giving exact additive vertex,
edge, and face bookkeeping.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

/-- Deleting a bridge from a preconnected graph leaves every vertex on one
of the two endpoint sides. -/
theorem reachable_deleteEdge_fst_or_snd {u v x : V}
    (hconn : G.Preconnected) (hbridge : G.IsBridge s(u, v)) :
    (G.deleteEdges {s(u, v)}).Reachable u x ∨
      (G.deleteEdges {s(u, v)}).Reachable v x := by
  let H := G.deleteEdges {s(u, v)}
  by_cases hux : H.Reachable u x
  · exact Or.inl hux
  · right
    have huv : ¬ H.Reachable u v := SimpleGraph.isBridge_iff.mp hbridge
    have hvu : ¬ H.Reachable v u := fun h ↦ huv h.symm
    have hxu : ¬ H.Reachable x u := fun h ↦ hux h.symm
    have hvu' : ¬ (G.deleteEdges {s(v, u)}).Reachable v u := by
      simpa [Sym2.eq_swap] using hvu
    have hxu' : ¬ (G.deleteEdges {s(v, u)}).Reachable x u := by
      simpa [Sym2.eq_swap] using hxu
    obtain ⟨p, hp⟩ := (hconn v x).exists_isPath
    have he : s(v, u) ∉ p.edges :=
      hp.isTrail.not_mem_edges_of_not_reachable hvu' hxu'
    exact SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
      ⟨p, by simpa [Sym2.eq_swap] using he⟩

/-- In a preconnected graph with bridge `uv`, the endpoint components after
deletion partition the vertex set. -/
theorem not_mem_deleteEdge_fstComponent_iff_mem_sndComponent
    {u v x : V} (hconn : G.Preconnected) (hbridge : G.IsBridge s(u, v)) :
    x ∉ ((G.deleteEdges {s(u, v)}).connectedComponentMk u).supp ↔
      x ∈ ((G.deleteEdges {s(u, v)}).connectedComponentMk v).supp := by
  let H := G.deleteEdges {s(u, v)}
  constructor
  · intro hxu
    rcases reachable_deleteEdge_fst_or_snd hconn hbridge (x := x) with h | h
    · exfalso
      apply hxu
      exact ConnectedComponent.sound h.symm
    · exact ConnectedComponent.sound h.symm
  · intro hxv hxu
    have hcu : H.connectedComponentMk x = H.connectedComponentMk u := hxu
    have hcv : H.connectedComponentMk x = H.connectedComponentMk v := hxv
    have huv : H.connectedComponentMk u = H.connectedComponentMk v :=
      hcu.symm.trans hcv
    exact (SimpleGraph.isBridge_iff.mp hbridge)
      (ConnectedComponent.exact huv)

/-- If the endpoints of an edge remain reachable after its deletion, every
ambient reachable pair remains reachable after deletion. -/
theorem reachable_deleteEdge_of_reachable_endpoints
    {u v x y : V}
    (huv : (G.deleteEdges {s(u, v)}).Reachable u v)
    (hxy : G.Reachable x y) :
    (G.deleteEdges {s(u, v)}).Reachable x y := by
  rw [reachable_iff_reflTransGen] at hxy
  let H := G.deleteEdges {s(u, v)}
  have hstep : ∀ {a b : V}, G.Adj a b → H.Reachable a b := by
    intro a b hab
    by_cases he : s(a, b) = s(u, v)
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
    · exact ((SimpleGraph.deleteEdges_adj.mpr
        ⟨hab, by simpa only [Set.mem_singleton_iff] using he⟩).reachable)
  exact Relation.ReflTransGen.trans_induction_on hxy
    (fun a ↦ SimpleGraph.Reachable.refl a)
    (fun hab ↦ hstep hab)
    (fun _ _ h₁ h₂ ↦ h₁.trans h₂)

/-- Deleting a non-bridge edge from a preconnected graph preserves
preconnectedness. -/
theorem deleteEdge_preconnected_of_not_isBridge
    {u v : V} (hconn : G.Preconnected)
    (hnot : ¬ G.IsBridge s(u, v)) :
    (G.deleteEdges {s(u, v)}).Preconnected := by
  have huv : (G.deleteEdges {s(u, v)}).Reachable u v := by
    simpa [SimpleGraph.isBridge_iff] using hnot
  intro x y
  exact reachable_deleteEdge_of_reachable_endpoints huv (hconn x y)

namespace RotationSystem

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

local instance componentFintype
    (C : G.ConnectedComponent) : Fintype C := Fintype.ofFinite C

local instance componentDecidableEq
    (C : G.ConnectedComponent) : DecidableEq C := Classical.decEq C

local instance componentDecidableAdj
    (C : G.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj :=
  Classical.decRel _

/-- Exact face decomposition of the rotation obtained after deleting a
bridge, into the two endpoint components. -/
theorem deleteBridge_faceCount_eq_add_restrictComponents
    (R : RotationSystem G) (a : G.Dart)
    (hconn : G.Preconnected) (hbridge : G.IsBridge a.edge) :
    (R.deleteEdge a.edge a rfl).faceCount =
      ((R.deleteEdge a.edge a rfl).restrictComponent
        ((G.deleteEdges {a.edge}).connectedComponentMk a.fst)).faceCount +
      ((R.deleteEdge a.edge a rfl).restrictComponent
        ((G.deleteEdges {a.edge}).connectedComponentMk a.snd)).faceCount := by
  apply faceCount_eq_add_restrictComponent_of_complement
  intro v
  simpa only [Dart.edge] using
    (not_mem_deleteEdge_fstComponent_iff_mem_sndComponent
      hconn hbridge (x := v))

/-- Vertex cardinality decomposition after deleting a bridge. -/
theorem deleteBridge_card_vertices_eq_add_restrictComponents
    (a : G.Dart) (hconn : G.Preconnected) (hbridge : G.IsBridge a.edge) :
    Fintype.card V =
      Fintype.card ((G.deleteEdges {a.edge}).connectedComponentMk a.fst) +
      Fintype.card ((G.deleteEdges {a.edge}).connectedComponentMk a.snd) := by
  apply card_vertices_eq_add_restrictComponents
  intro v
  simpa only [Dart.edge] using
    (not_mem_deleteEdge_fstComponent_iff_mem_sndComponent
      hconn hbridge (x := v))

/-- Edge cardinality decomposition after deleting a bridge. -/
theorem deleteBridge_card_edges_eq_add_restrictComponents
    (a : G.Dart) (hconn : G.Preconnected) (hbridge : G.IsBridge a.edge) :
    (G.deleteEdges {a.edge}).edgeFinset.card =
      ((G.deleteEdges {a.edge}).connectedComponentMk a.fst).toSimpleGraph.edgeFinset.card +
      ((G.deleteEdges {a.edge}).connectedComponentMk a.snd).toSimpleGraph.edgeFinset.card := by
  apply card_edges_eq_add_restrictComponents
  intro v
  simpa only [Dart.edge] using
    (not_mem_deleteEdge_fstComponent_iff_mem_sndComponent
      hconn hbridge (x := v))

end Finite

end RotationSystem

end


end LeanCo.PackingEdgeColoring
