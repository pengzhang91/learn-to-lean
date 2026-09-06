import LeanCo.PackingEdgeColoring.ComponentColoring

/-!
# Gluing the Section 4 auxiliary invariants across components

Semantic packing colourings already glue in `ComponentColoring`.  The
minimal-counterexample proof for Section 4 also needs the auxiliary
`OneSaturated`, `ConditionTwo`, and `ConditionThree` predicates to glue.  This
file develops that component-locality layer.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

namespace ConnectedComponent

/-- Lift an ambient walk whose endpoints lie in one connected component to
the induced graph on that component. -/
def walkToSimpleGraph (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) (p : G.Walk u v) :
    C.toSimpleGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  cases p with
  | nil => exact .nil
  | @cons v w u h p =>
      have hw : w ∈ C.supp := C.mem_supp_of_adj_mem_supp hu h
      have h' : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨w, hw⟩ :=
        (ConnectedComponent.toSimpleGraph_adj C hu hw).mpr h
      exact .cons h' (walkToSimpleGraph C hw hv p)

/-- Mapping the lifted walk back to the ambient graph recovers the original
walk. -/
theorem map_walkToSimpleGraph (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) (p : G.Walk u v) :
    (walkToSimpleGraph G C hu hv p).map C.toSimpleGraph_hom = p := by
  induction p with
  | nil =>
      rw [walkToSimpleGraph]
      congr
  | @cons v w u h p ih =>
      have hw : w ∈ C.supp := C.mem_supp_of_adj_mem_supp hu h
      rw [walkToSimpleGraph]
      rw [Walk.map_cons, ih hw hv]
      congr

@[simp] theorem length_walkToSimpleGraph (C : G.ConnectedComponent)
    {u v : V} (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (p : G.Walk u v) :
    (walkToSimpleGraph G C hu hv p).length = p.length := by
  let q := walkToSimpleGraph G C hu hv p
  calc
    q.length = (q.map C.toSimpleGraph_hom).length :=
      (Walk.length_map C.toSimpleGraph_hom q).symm
    _ = p.length := congrArg Walk.length
      (map_walkToSimpleGraph G C hu hv p)

theorem coe_getVert_walkToSimpleGraph (C : G.ConnectedComponent)
    {u v : V} (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (p : G.Walk u v) (i : ℕ) :
    ((walkToSimpleGraph G C hu hv p).getVert i : V) = p.getVert i := by
  let q := walkToSimpleGraph G C hu hv p
  calc
    ((q.getVert i : C) : V) =
        C.toSimpleGraph_hom (q.getVert i) := rfl
    _ = (q.map C.toSimpleGraph_hom).getVert i :=
      (Walk.getVert_map C.toSimpleGraph_hom q i).symm
    _ = p.getVert i := congrArg (fun r : G.Walk u v ↦ r.getVert i)
      (map_walkToSimpleGraph G C hu hv p)

end ConnectedComponent

/-- The canonical component edge associated with an ambient edge maps back
to that same ambient edge. -/
theorem componentEdgeMap_edgeInComponent (e : G.edgeSet) :
    componentEdgeMap G ⟨edgeComponent G e, edgeInComponent G e⟩ = e := by
  apply Subtype.ext
  exact edgeInComponent_val_map G e

/-- Externality at a component vertex is preserved exactly by the canonical
component embedding. -/
theorem isExternalAt_componentEdgeMap_iff
    (C : G.ConnectedComponent) (u : C)
    (threadEdge e : C.toSimpleGraph.edgeSet) :
    IsExternalAt G u.1 (componentEdgeMap G ⟨C, threadEdge⟩)
        (componentEdgeMap G ⟨C, e⟩) ↔
      IsExternalAt C.toSimpleGraph u threadEdge e := by
  constructor
  · rintro ⟨hue, hne⟩
    constructor
    · change (u : V) ∈ e.1.map (fun z : C ↦ z.1) at hue
      obtain ⟨x, hxe, hxu⟩ := Sym2.mem_map.mp hue
      have hxu' : x = u := Subtype.ext hxu
      simpa only [hxu'] using hxe
    · intro he
      apply hne
      subst e
      rfl
  · rintro ⟨hue, hne⟩
    constructor
    · change (u : V) ∈ e.1.map (fun z : C ↦ z.1)
      exact Sym2.mem_map.mpr ⟨u, hue, rfl⟩
    · intro he
      apply hne
      apply (SimpleGraph.Embedding.induce C.supp).mapEdgeSet.injective
      exact he

/-- Pointwise form of component gluing at an arbitrary ambient edge. -/
@[simp] theorem glueComponentColoring_edgeInComponent {k : ℕ}
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor k)
    (e : G.edgeSet) :
    glueComponentColoring G colour e =
      colour (edgeComponent G e) (edgeInComponent G e) := by
  let x : ComponentEdge G :=
    ⟨edgeComponent G e, edgeInComponent G e⟩
  calc
    glueComponentColoring G colour e =
        glueComponentColoring G colour (componentEdgeMap G x) := by
      rw [componentEdgeMap_edgeInComponent G e]
    _ = colour x.1 x.2 :=
      glueComponentColoring_componentEdgeMap G colour x

/-- Ambient external-edge induction restricts to the component containing
the endpoint. -/
theorem externalEdgesInduced_component_of_glue {k : ℕ}
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor k)
    (C : G.ConnectedComponent) (u : C)
    (threadEdge : C.toSimpleGraph.edgeSet)
    (h : ExternalEdgesInduced G (glueComponentColoring G colour) u.1
      (componentEdgeMap G ⟨C, threadEdge⟩)) :
    ExternalEdgesInduced C.toSimpleGraph (colour C) u threadEdge := by
  intro e he
  have heMap : IsExternalAt G u.1 (componentEdgeMap G ⟨C, threadEdge⟩)
      (componentEdgeMap G ⟨C, e⟩) :=
    (isExternalAt_componentEdgeMap_iff G C u threadEdge e).mpr he
  obtain ⟨i, hi⟩ := h (componentEdgeMap G ⟨C, e⟩) heMap
  exact ⟨i, by
    simpa only [glueComponentColoring_componentEdgeMap] using hi⟩

/-- The induced-colour set external to a component thread endpoint is
exactly its ambient counterpart after gluing. -/
theorem mem_externalInducedColors_glue_iff {k : ℕ}
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor k)
    (C : G.ConnectedComponent) (u : C)
    (threadEdge : C.toSimpleGraph.edgeSet) (i : Fin k) :
    i ∈ ExternalInducedColors G (glueComponentColoring G colour) u.1
        (componentEdgeMap G ⟨C, threadEdge⟩) ↔
      i ∈ ExternalInducedColors C.toSimpleGraph (colour C) u
        threadEdge := by
  constructor
  · rintro ⟨e, he, hi⟩
    obtain ⟨⟨D, eD⟩, rfl⟩ := componentEdgeMap_surjective G e
    have huD : (u : V) ∈ D.supp := by
      have hue := he.1
      change (u : V) ∈ eD.1.map (fun z : D ↦ z.1) at hue
      obtain ⟨uD, huDe, huDu⟩ := Sym2.mem_map.mp hue
      rw [← huDu]
      exact uD.2
    have hCD : C = D :=
      ConnectedComponent.eq_of_common_vertex u.2 huD
    cases hCD
    refine ⟨eD, ?_, ?_⟩
    · exact (isExternalAt_componentEdgeMap_iff G C u threadEdge eD).mp he
    · simpa only [glueComponentColoring_componentEdgeMap] using hi
  · rintro ⟨e, he, hi⟩
    refine ⟨componentEdgeMap G ⟨C, e⟩, ?_, ?_⟩
    · exact (isExternalAt_componentEdgeMap_iff G C u threadEdge e).mpr he
    · simpa only [glueComponentColoring_componentEdgeMap] using hi

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A thread lying in one component remains a thread in the induced
component graph. -/
theorem IsKThread.toConnectedComponent
    {u v : V} {p : G.Walk u v} {k : ℕ}
    (hp : IsKThread G p k) (C : G.ConnectedComponent)
    (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj] :
    IsKThread C.toSimpleGraph
      (ConnectedComponent.walkToSimpleGraph G C hu hv p) k := by
  have hpathMap :
      ((ConnectedComponent.walkToSimpleGraph G C hu hv p).map
        C.toSimpleGraph_hom).IsPath := by
    rw [ConnectedComponent.map_walkToSimpleGraph G C hu hv p]
    exact hp.1
  refine ⟨hpathMap.of_map, ?_, ?_, ?_, ?_⟩
  · rw [ConnectedComponent.length_walkToSimpleGraph G C hu hv p]
    exact hp.length
  · unfold IsThreeVertex
    rw [degree_toSimpleGraph_connectedComponent G C]
    exact hp.start_three
  · unfold IsThreeVertex
    rw [degree_toSimpleGraph_connectedComponent G C]
    exact hp.end_three
  · intro i hi hil
    unfold IsTwoVertex
    rw [degree_toSimpleGraph_connectedComponent G C,
      ConnectedComponent.coe_getVert_walkToSimpleGraph G C hu hv p i]
    apply IsKThread.internal_two G hp hi
    rwa [ConnectedComponent.length_walkToSimpleGraph G C hu hv p] at hil

/-- The first thread edge of the lifted component walk embeds to the
original first thread edge. -/
theorem componentEdgeMap_threadFirstEdge_walkToSimpleGraph
    {u v : V} {p : G.Walk u v} {k : ℕ}
    (hp : IsKThread G p k) (C : G.ConnectedComponent)
    (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (hpC : IsKThread C.toSimpleGraph
      (ConnectedComponent.walkToSimpleGraph G C hu hv p) k) :
    componentEdgeMap G ⟨C, threadFirstEdge C.toSimpleGraph
        (ConnectedComponent.walkToSimpleGraph G C hu hv p) hpC⟩ =
      threadFirstEdge G p hp := by
  apply Subtype.ext
  change s((u : V),
      ((ConnectedComponent.walkToSimpleGraph G C hu hv p).getVert 1 : C)) =
    s(u, p.getVert 1)
  rw [ConnectedComponent.coe_getVert_walkToSimpleGraph G C hu hv p]

/-- The last thread edge of the lifted component walk embeds to the
original last thread edge. -/
theorem componentEdgeMap_threadLastEdge_walkToSimpleGraph
    {u v : V} {p : G.Walk u v} {k : ℕ}
    (hp : IsKThread G p k) (C : G.ConnectedComponent)
    (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (hpC : IsKThread C.toSimpleGraph
      (ConnectedComponent.walkToSimpleGraph G C hu hv p) k) :
    componentEdgeMap G ⟨C, threadLastEdge C.toSimpleGraph
        (ConnectedComponent.walkToSimpleGraph G C hu hv p) hpC⟩ =
      threadLastEdge G p hp := by
  apply Subtype.ext
  change s(((ConnectedComponent.walkToSimpleGraph G C hu hv p).getVert k).1,
      v) = s(p.getVert k, v)
  rw [ConnectedComponent.coe_getVert_walkToSimpleGraph G C hu hv p]

/-- Inclusion-maximality of the matching class is component-local. -/
theorem oneSaturated_glueComponentColoring {k : ℕ}
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor k)
    (hsaturated : ∀ C : G.ConnectedComponent,
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
      OneSaturated C.toSimpleGraph (colour C)) :
    OneSaturated G (glueComponentColoring G colour) := by
  intro e he
  obtain ⟨⟨C, eC⟩, rfl⟩ := componentEdgeMap_surjective G e
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have heC : colour C eC ≠ none := by
    simpa only [glueComponentColoring_componentEdgeMap] using he
  obtain ⟨fC, hfC, x, hxe, hxf⟩ := hsaturated C eC heC
  refine ⟨componentEdgeMap G ⟨C, fC⟩, ?_, x.1, ?_, ?_⟩
  · simpa only [glueComponentColoring_componentEdgeMap] using hfC
  · change x.1 ∈ eC.1.map (fun z : C ↦ z.1)
    exact Sym2.mem_map.mpr ⟨x, hxe, rfl⟩
  · change x.1 ∈ fC.1.map (fun z : C ↦ z.1)
    exact Sym2.mem_map.mpr ⟨x, hxf, rfl⟩

/-- Condition 2 is component-local.  Every edge witnessing that a vertex
sees a colour lies in the component of any matching edge incident with the
vertex. -/
theorem conditionTwo_glueComponentColoring
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor 4)
    (hcondition : ∀ C : G.ConnectedComponent,
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
      ConditionTwo C.toSimpleGraph (colour C)) :
    ConditionTwo G (glueComponentColoring G colour) := by
  intro u huTwo huMatching hall
  rw [vertexSeesMatching_iff] at huMatching
  obtain ⟨e, heColour, hue⟩ := huMatching
  obtain ⟨⟨C, eC⟩, rfl⟩ := componentEdgeMap_surjective G e
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  change u ∈ eC.1.map (fun z : C ↦ z.1) at hue
  obtain ⟨uC, huCe, huCu⟩ := Sym2.mem_map.mp hue
  subst u
  have huTwoC : IsTwoVertex C.toSimpleGraph uC := by
    unfold IsTwoVertex at huTwo ⊢
    rw [degree_toSimpleGraph_connectedComponent G C uC]
    exact huTwo
  have huMatchingC : VertexSeesMatching C.toSimpleGraph (colour C) uC := by
    rw [vertexSeesMatching_iff]
    refine ⟨eC, ?_, huCe⟩
    simpa only [glueComponentColoring_componentEdgeMap] using heColour
  have hallC : ∀ i : Fin 4,
      VertexSeesInduced C.toSimpleGraph (colour C) uC i := by
    intro i
    rw [vertexSeesInduced_iff]
    have hglobal := hall i
    rw [vertexSeesInduced_iff] at hglobal
    obtain ⟨f, hfColour, v, hvf, huv⟩ := hglobal
    obtain ⟨⟨D, fD⟩, rfl⟩ := componentEdgeMap_surjective G f
    change v ∈ fD.1.map (fun z : D ↦ z.1) at hvf
    obtain ⟨vD, hvDf, hvDv⟩ := Sym2.mem_map.mp hvf
    have huD : (uC : V) ∈ D.supp := by
      rcases huv with huv | huv
      · have huvD : (uC : V) = (vD : V) := huv.trans hvDv.symm
        rw [huvD]
        exact vD.2
      · have hadj : G.Adj (uC : V) (vD : V) := by
          simpa only [hvDv] using huv
        exact D.mem_supp_of_adj_mem_supp vD.2 hadj.symm
    have hCD : C = D :=
      ConnectedComponent.eq_of_common_vertex uC.2 huD
    cases hCD
    refine ⟨fD, ?_, vD, hvDf, ?_⟩
    · simpa only [glueComponentColoring_componentEdgeMap] using hfColour
    · rcases huv with huv | huv
      · left
        apply Subtype.ext
        exact huv.trans hvDv.symm
      · right
        apply (ConnectedComponent.toSimpleGraph_adj C uC.2 vD.2).mpr
        simpa only [hvDv] using huv
  exact hcondition C uC huTwoC huMatchingC hallC

/-- Condition 3 is component-local.  A certified 2-thread and every edge
external to either endpoint all lie in the component of its first endpoint. -/
theorem conditionThree_glueComponentColoring
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor 4)
    (hcondition : ∀ C : G.ConnectedComponent,
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
      ConditionThree C.toSimpleGraph (colour C)) :
    ConditionThree G (glueComponentColoring G colour) := by
  intro u₁ u₂ p hp hleft hright
  let C : G.ConnectedComponent := G.connectedComponentMk u₁
  have hu : u₁ ∈ C.supp := by
    dsimp [C]
    exact ConnectedComponent.connectedComponentMk_mem
  have hcomp : G.connectedComponentMk u₁ = G.connectedComponentMk u₂ :=
    ConnectedComponent.sound p.reachable
  have hv : u₂ ∈ C.supp := by
    dsimp [C]
    rw [hcomp]
    exact ConnectedComponent.connectedComponentMk_mem
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let u₁C : C := ⟨u₁, hu⟩
  let u₂C : C := ⟨u₂, hv⟩
  let q := ConnectedComponent.walkToSimpleGraph G C hu hv p
  have hpC : IsKThread C.toSimpleGraph q 2 :=
    IsKThread.toConnectedComponent G hp C hu hv
  let firstC := threadFirstEdge C.toSimpleGraph q hpC
  let lastC := threadLastEdge C.toSimpleGraph q hpC
  have hfirst : componentEdgeMap G ⟨C, firstC⟩ =
      threadFirstEdge G p hp := by
    exact componentEdgeMap_threadFirstEdge_walkToSimpleGraph G hp C hu hv hpC
  have hlast : componentEdgeMap G ⟨C, lastC⟩ =
      threadLastEdge G p hp := by
    exact componentEdgeMap_threadLastEdge_walkToSimpleGraph G hp C hu hv hpC
  have hleftC : ExternalEdgesInduced C.toSimpleGraph (colour C) u₁C
      firstC := by
    apply externalEdgesInduced_component_of_glue G colour C u₁C firstC
    simpa only [u₁C, hfirst] using hleft
  have hrightC : ExternalEdgesInduced C.toSimpleGraph (colour C) u₂C
      lastC := by
    apply externalEdgesInduced_component_of_glue G colour C u₂C lastC
    simpa only [u₂C, hlast] using hright
  have hneC : ExternalInducedColors C.toSimpleGraph (colour C) u₁C
        firstC ≠
      ExternalInducedColors C.toSimpleGraph (colour C) u₂C lastC :=
    hcondition C u₁C u₂C q hpC hleftC hrightC
  intro heq
  apply hneC
  ext i
  rw [← mem_externalInducedColors_glue_iff G colour C u₁C firstC i,
    ← mem_externalInducedColors_glue_iff G colour C u₂C lastC i]
  simpa only [u₁C, u₂C, hfirst, hlast] using Set.ext_iff.mp heq i

/-- All three auxiliary Section 4 invariants glue componentwise. -/
theorem goodFour_of_connectedComponents
    (colour : (C : G.ConnectedComponent) →
      C.toSimpleGraph.edgeSet → OneTwoColor 4)
    (hgood : ∀ C : G.ConnectedComponent,
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
      GoodFour C.toSimpleGraph (colour C)) :
    GoodFour G (glueComponentColoring G colour) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply isOneTwoColoring_of_connectedComponents G colour
    intro C
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    exact (hgood C).valid
  · apply oneSaturated_glueComponentColoring G colour
    intro C
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    exact (hgood C).oneSaturated
  · apply conditionTwo_glueComponentColoring G colour
    intro C
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    exact (hgood C).paletteCondition
  · apply conditionThree_glueComponentColoring G colour
    intro C
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    exact (hgood C).conditionThree

end Finite

end

end LeanCo.PackingEdgeColoring
