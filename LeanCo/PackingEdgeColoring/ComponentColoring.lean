import LeanCo.PackingEdgeColoring.GoodColoring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Gluing packing edge-colourings across connected components

The planar hypothesis used later is componentwise.  This file records the
corresponding component reduction for packing edge-colourings.  The point is
slightly more delicate than for ordinary vertex colourings: equal induced
edge colours must also have no cross-edge between their endpoints.  Distinct
connected components give exactly that separation.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- The connected component containing an edge (chosen through the first
endpoint of `Sym2.out`). -/
def edgeComponent (e : G.edgeSet) : G.ConnectedComponent :=
  G.connectedComponentMk e.1.out.1

private theorem edge_out_adj (e : G.edgeSet) :
    G.Adj e.1.out.1 e.1.out.2 := by
  rw [← G.mem_edgeSet]
  change Quot.mk (Sym2.Rel V) e.1.out ∈ G.edgeSet
  rw [Quot.out_eq]
  exact e.2

/-- Every endpoint of an edge lies in the component selected by
`edgeComponent`. -/
theorem endpoint_mem_edgeComponent (e : G.edgeSet) {u : V}
    (hu : u ∈ (e : Sym2 V)) : u ∈ (edgeComponent G e).supp := by
  have hu' : u ∈ s(e.1.out.1, e.1.out.2) := by
    simpa only [e.1.out_eq] using hu
  rcases (Sym2.mem_iff.mp hu') with rfl | rfl
  · exact ConnectedComponent.connectedComponentMk_mem
  · exact (edgeComponent G e).mem_supp_of_adj_mem_supp
      ConnectedComponent.connectedComponentMk_mem (edge_out_adj G e)

/-- Regard an edge as an edge of its selected connected-component graph. -/
def edgeInComponent (e : G.edgeSet) :
    (edgeComponent G e).toSimpleGraph.edgeSet :=
  ⟨s(⟨e.1.out.1, endpoint_mem_edgeComponent G e (Sym2.out_fst_mem e.1)⟩,
      ⟨e.1.out.2, endpoint_mem_edgeComponent G e (Sym2.out_snd_mem e.1)⟩),
    edge_out_adj G e⟩

@[simp] theorem edgeInComponent_val_map (e : G.edgeSet) :
    (edgeInComponent G e).1.map (fun x => x.1) = e.1 := by
  change s(e.1.out.1, e.1.out.2) = e.1
  exact e.1.out_eq

/-- Two edges which share an endpoint have the same selected component. -/
theorem edgeComponent_eq_of_common_endpoint {e f : G.edgeSet} {u : V}
    (hue : u ∈ (e : Sym2 V)) (huf : u ∈ (f : Sym2 V)) :
    edgeComponent G e = edgeComponent G f := by
  exact ConnectedComponent.eq_of_common_vertex
    (endpoint_mem_edgeComponent G e hue)
    (endpoint_mem_edgeComponent G f huf)

/-- An adjacency between endpoints of two edges forces the two edges into
the same connected component. -/
theorem edgeComponent_eq_of_crossEdge {e f : G.edgeSet} {u v : V}
    (hue : u ∈ (e : Sym2 V)) (hvf : v ∈ (f : Sym2 V))
    (huv : G.Adj u v) : edgeComponent G e = edgeComponent G f := by
  exact ConnectedComponent.eq_of_common_vertex
    ((edgeComponent G e).mem_supp_of_adj_mem_supp
      (endpoint_mem_edgeComponent G e hue) huv)
    (endpoint_mem_edgeComponent G f hvf)

/-- Edges in different connected components are endpoint-disjoint. -/
theorem endpointDisjoint_of_edgeComponent_ne {e f : G.edgeSet}
    (hcomp : edgeComponent G e ≠ edgeComponent G f) :
    EndpointDisjoint G e f := by
  intro u hue huf
  exact hcomp (edgeComponent_eq_of_common_endpoint G hue huf)

/-- Edges in different connected components have no endpoint cross-edge. -/
theorem no_hasCrossEdge_of_edgeComponent_ne {e f : G.edgeSet}
    (hcomp : edgeComponent G e ≠ edgeComponent G f) :
    ¬ HasCrossEdge G e f := by
  rintro ⟨u, hue, v, hvf, huv⟩
  exact hcomp (edgeComponent_eq_of_crossEdge G hue hvf huv)

/-- Any two colours are compatible on edges in distinct components. -/
theorem pairCompatible_of_edgeComponent_ne {k : ℕ} {e f : G.edgeSet}
    {a b : OneTwoColor k}
    (hcomp : edgeComponent G e ≠ edgeComponent G f) :
    PairCompatible G e f a b := by
  by_cases hab : a = b
  · subst b
    cases a with
    | none =>
        simpa using endpointDisjoint_of_edgeComponent_ne G hcomp
    | some i =>
        simp only [pairCompatible_some_self]
        exact ⟨endpointDisjoint_of_edgeComponent_ne G hcomp,
          no_hasCrossEdge_of_edgeComponent_ne G hcomp⟩
  · exact pairCompatible_of_ne G hab

/-! ## Edge decomposition by connected components -/

/-- The disjoint sum of the edge sets of all connected components. -/
abbrev ComponentEdge :=
  (C : G.ConnectedComponent) ×' C.toSimpleGraph.edgeSet

/-- Include a component edge into the ambient graph. -/
def componentEdgeMap (x : ComponentEdge G) : G.edgeSet :=
  (SimpleGraph.Embedding.induce x.1.supp).mapEdgeSet x.2

@[simp] theorem componentEdgeMap_val (x : ComponentEdge G) :
    (componentEdgeMap G x).1 = x.2.1.map (fun u => u.1) := rfl

theorem edgeComponent_componentEdgeMap (x : ComponentEdge G) :
    edgeComponent G (componentEdgeMap G x) = x.1 := by
  let u : x.1 := x.2.1.out.1
  have huMap : (u : V) ∈ ((componentEdgeMap G x : G.edgeSet) : Sym2 V) := by
    change (u : V) ∈ x.2.1.map (fun z => z.1)
    exact Sym2.mem_map.mpr ⟨u, Sym2.out_fst_mem x.2.1, rfl⟩
  exact ConnectedComponent.eq_of_common_vertex
    (endpoint_mem_edgeComponent G (componentEdgeMap G x) huMap) u.2

theorem componentEdgeMap_injective :
    Function.Injective (componentEdgeMap G) := by
  rintro ⟨C, e⟩ ⟨D, f⟩ hef
  have hCD : C = D := by
    have howner := congrArg (edgeComponent G) hef
    simpa only [edgeComponent_componentEdgeMap] using howner
  subst D
  have hef' : e = f := by
    apply (SimpleGraph.Embedding.induce C.supp).mapEdgeSet.injective
    exact hef
  subst f
  rfl

theorem componentEdgeMap_surjective :
    Function.Surjective (componentEdgeMap G) := by
  intro e
  refine ⟨⟨edgeComponent G e, edgeInComponent G e⟩, ?_⟩
  apply Subtype.ext
  exact edgeInComponent_val_map G e

/-- Ambient edges are canonically equivalent to the disjoint sum of the
component edge sets. -/
def componentEdgeEquiv : ComponentEdge G ≃ G.edgeSet :=
  Equiv.ofBijective (componentEdgeMap G)
    ⟨componentEdgeMap_injective G, componentEdgeMap_surjective G⟩

@[simp] theorem componentEdgeEquiv_apply (x : ComponentEdge G) :
    componentEdgeEquiv G x = componentEdgeMap G x := rfl

/-! ## Compatibility transported through graph embeddings -/

variable {W : Type*} {H : SimpleGraph W}

theorem endpointDisjoint_map_embedding (φ : G ↪g H) {e f : G.edgeSet}
    (h : EndpointDisjoint G e f) :
    EndpointDisjoint H (φ.mapEdgeSet e) (φ.mapEdgeSet f) := by
  intro v hve hvf
  change v ∈ e.1.map φ at hve
  change v ∈ f.1.map φ at hvf
  rcases Sym2.mem_map.mp hve with ⟨u, hue, huv⟩
  rcases Sym2.mem_map.mp hvf with ⟨w, hwf, hwv⟩
  have huw : u = w := φ.injective (huv.trans hwv.symm)
  subst w
  exact h u hue hwf

theorem no_hasCrossEdge_map_embedding (φ : G ↪g H) {e f : G.edgeSet}
    (h : ¬ HasCrossEdge G e f) :
    ¬ HasCrossEdge H (φ.mapEdgeSet e) (φ.mapEdgeSet f) := by
  rintro ⟨v, hve, w, hwf, hvw⟩
  change v ∈ e.1.map φ at hve
  change w ∈ f.1.map φ at hwf
  rcases Sym2.mem_map.mp hve with ⟨u, hue, rfl⟩
  rcases Sym2.mem_map.mp hwf with ⟨z, hzf, rfl⟩
  exact h ⟨u, hue, z, hzf, φ.map_adj_iff.mp hvw⟩

theorem inducedSeparated_map_embedding (φ : G ↪g H) {e f : G.edgeSet}
    (h : InducedSeparated G e f) :
    InducedSeparated H (φ.mapEdgeSet e) (φ.mapEdgeSet f) :=
  ⟨endpointDisjoint_map_embedding G φ h.1,
    no_hasCrossEdge_map_embedding G φ h.2⟩

theorem pairCompatible_map_embedding (φ : G ↪g H) {k : ℕ}
    {e f : G.edgeSet} {a b : OneTwoColor k}
    (h : PairCompatible G e f a b) :
    PairCompatible H (φ.mapEdgeSet e) (φ.mapEdgeSet f) a b := by
  by_cases hab : a = b
  · subst b
    cases a with
    | none =>
        simpa using endpointDisjoint_map_embedding G φ (by simpa using h)
    | some i =>
        simpa using inducedSeparated_map_embedding G φ (by simpa using h)
  · exact pairCompatible_of_ne H hab

/-! ## Gluing local colour assignments -/

/-- Glue one semantic edge-colour assignment from each connected component. -/
def glueComponentColoring {k : ℕ}
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor k) :
    G.edgeSet → OneTwoColor k := fun e =>
  let x := (componentEdgeEquiv G).symm e
  colour x.1 x.2

@[simp] theorem glueComponentColoring_componentEdgeMap {k : ℕ}
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor k)
    (x : ComponentEdge G) :
    glueComponentColoring G colour (componentEdgeMap G x) = colour x.1 x.2 := by
  change colour ((componentEdgeEquiv G).symm ((componentEdgeEquiv G) x)).1
      ((componentEdgeEquiv G).symm ((componentEdgeEquiv G) x)).2 = colour x.1 x.2
  rw [Equiv.symm_apply_apply]

/-- Valid semantic packing colourings glue across connected components. -/
theorem isOneTwoColoring_of_connectedComponents {k : ℕ}
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor k)
    (hcolour : ∀ C, IsOneTwoColoring C.toSimpleGraph (colour C)) :
    IsOneTwoColoring G (glueComponentColoring G colour) := by
  intro e _ f _ hef
  obtain ⟨⟨C, eC⟩, rfl⟩ := componentEdgeMap_surjective G e
  obtain ⟨⟨D, fD⟩, rfl⟩ := componentEdgeMap_surjective G f
  by_cases hCD : C = D
  · subst D
    have hefC : eC ≠ fD := by
      intro h
      subst fD
      exact hef rfl
    have hp := hcolour C eC (by simp) fD (by simp) hefC
    have hp' : PairCompatible G (componentEdgeMap G ⟨C, eC⟩)
        (componentEdgeMap G ⟨C, fD⟩) (colour C eC) (colour C fD) := by
      change PairCompatible G
        ((SimpleGraph.Embedding.induce C.supp).mapEdgeSet eC)
        ((SimpleGraph.Embedding.induce C.supp).mapEdgeSet fD)
        (colour C eC) (colour C fD)
      exact pairCompatible_map_embedding C.toSimpleGraph
        (SimpleGraph.Embedding.induce C.supp) hp
    simpa only [glueComponentColoring_componentEdgeMap] using hp'
  · apply pairCompatible_of_edgeComponent_ne G
    simpa only [edgeComponent_componentEdgeMap] using hCD

/-- Componentwise local colourability is sufficient for ambient packing
edge-colourability. -/
theorem hasOneTwoPackingEdgeColoring_of_connectedComponents {k : ℕ}
    (h : ∀ C : G.ConnectedComponent,
      HasOneTwoPackingEdgeColoring C.toSimpleGraph k) :
    HasOneTwoPackingEdgeColoring G k := by
  rw [hasOneTwoPackingEdgeColoring_iff_exists_local]
  choose colour hcolour using fun C =>
    (hasOneTwoPackingEdgeColoring_iff_exists_local C.toSimpleGraph k).mp (h C)
  exact ⟨glueComponentColoring G colour,
    isOneTwoColoring_of_connectedComponents G colour hcolour⟩

/-! ## Ambient hypotheses inherited by a connected component -/

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem degree_toSimpleGraph_connectedComponent (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (v : C) : C.toSimpleGraph.degree v = G.degree v := by
  let E : C.toSimpleGraph.neighborSet v ≃ G.neighborSet (v : V) :=
    { toFun := fun w => ⟨w.1.1, w.2⟩
      invFun := fun w =>
        ⟨⟨w.1, C.mem_supp_of_adj_mem_supp v.2 w.2⟩, w.2⟩
      left_inv := by intro w; ext; rfl
      right_inv := by intro w; ext; rfl }
  rw [← C.toSimpleGraph.card_neighborSet_eq_degree,
    ← G.card_neighborSet_eq_degree]
  exact Fintype.card_congr E

theorem IsSubcubic.connectedComponent (h : IsSubcubic G)
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj] :
    IsSubcubic C.toSimpleGraph := by
  intro v
  rw [degree_toSimpleGraph_connectedComponent G C v]
  exact h v

theorem activeMinDegree_connectedComponent
    (h : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (v : C)
    (hv : 0 < C.toSimpleGraph.degree v) :
    2 ≤ C.toSimpleGraph.degree v := by
  rw [degree_toSimpleGraph_connectedComponent G C v] at hv ⊢
  exact h v hv

theorem egirth_le_connectedComponent (C : G.ConnectedComponent) :
    G.egirth ≤ C.toSimpleGraph.egirth := by
  exact (SimpleGraph.Embedding.induce C.supp).isContained.egirth_le

theorem girth_lowerBound_connectedComponent {n : ℕ∞}
    (h : n ≤ G.egirth) (C : G.ConnectedComponent) :
    n ≤ C.toSimpleGraph.egirth :=
  h.trans (egirth_le_connectedComponent G C)

end Finite

end

end LeanCo.PackingEdgeColoring
