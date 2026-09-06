import LeanCo.PackingEdgeColoring.MinimalCounterexample
import LeanCo.PackingEdgeColoring.GoodExtension
import LeanCo.PackingEdgeColoring.AvailabilityMultiplicity
import LeanCo.PackingEdgeColoring.SectionThreeNoThreeChain

/-!
# Deleting and restoring an edge at a leaf

Both minimal-counterexample arguments first rule out degree-one vertices.
Unlike arbitrary single-edge deletion, deleting the unique edge at a leaf
does reflect all adjacencies between endpoints of retained edges: no retained
edge can use the leaf.  This file packages that exact transport fact.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Uniqueness of the neighbour of a degree-one vertex. -/
theorem eq_neighbor_of_degree_eq_one {u v w : V}
    (hu : G.degree u = 1) (huv : G.Adj u v) (huw : G.Adj u w) :
    w = v := by
  obtain ⟨x, hux, hunique⟩ :=
    (G.degree_eq_one_iff_existsUnique_adj (v := u)).mp hu
  exact (hunique w huw).trans (hunique v huv).symm

/-- A degree-three vertex with one specified neighbor has exactly two other,
distinct neighbors.  The explicit neighbor-finset identity is useful for
the finite case split in the hard leaf branch. -/
theorem exists_two_other_neighbors_of_isThreeVertex {u v : V}
    (hv : IsThreeVertex G v) (huv : G.Adj u v) :
    ∃ a b : V, a ≠ b ∧ a ≠ u ∧ b ≠ u ∧
      G.Adj v a ∧ G.Adj v b ∧
      G.neighborFinset v = {u, a, b} := by
  classical
  have hcard : (G.neighborFinset v).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hv
  have huN : u ∈ G.neighborFinset v :=
    (G.mem_neighborFinset v u).mpr huv.symm
  have hcardErase : ((G.neighborFinset v).erase u).card = 2 := by
    rw [Finset.card_erase_of_mem huN, hcard]
  obtain ⟨a, b, hab, hErase⟩ := Finset.card_eq_two.mp hcardErase
  have haErase : a ∈ (G.neighborFinset v).erase u := by
    rw [hErase]
    simp
  have hbErase : b ∈ (G.neighborFinset v).erase u := by
    rw [hErase]
    simp
  have hau : a ≠ u := (Finset.mem_erase.mp haErase).1
  have hbu : b ≠ u := (Finset.mem_erase.mp hbErase).1
  have hva : G.Adj v a :=
    (G.mem_neighborFinset v a).mp (Finset.mem_erase.mp haErase).2
  have hvb : G.Adj v b :=
    (G.mem_neighborFinset v b).mp (Finset.mem_erase.mp hbErase).2
  have hN : G.neighborFinset v = {u, a, b} := by
    calc
      G.neighborFinset v = insert u ((G.neighborFinset v).erase u) :=
        (Finset.insert_erase huN).symm
      _ = {u, a, b} := by rw [hErase]
  exact ⟨a, b, hab, hau, hbu, hva, hvb, hN⟩

/-- Every edge incident with a leaf is its prescribed unique edge. -/
theorem edge_eq_of_incident_degree_eq_one {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (e : G.edgeSet) (hue : u ∈ (e : Sym2 V)) :
    e = (⟨s(u, v), huv⟩ : G.edgeSet) := by
  obtain ⟨w, hew⟩ := Sym2.mem_iff_exists.mp hue
  have huw : G.Adj u w := by
    rw [← G.mem_edgeSet, ← hew]
    exact e.2
  have hwv := eq_neighbor_of_degree_eq_one G hu huv huw
  apply Subtype.ext
  simpa [hwv] using hew

/-- The spanning graph obtained by deleting a leaf edge. -/
abbrev deleteLeafEdge {u v : V} (huv : G.Adj u v) : SimpleGraph V :=
  G.deleteEdges ({s(u, v)} : Set (Sym2 V))

theorem mem_retained_deleteLeafEdge_iff {u v : V} (huv : G.Adj u v)
    (e : G.edgeSet) :
    e ∈ RetainedEdges (deleteLeafEdge G huv) G ↔
      e ≠ (⟨s(u, v), huv⟩ : G.edgeSet) := by
  rw [RetainedEdges, SimpleGraph.edgeSet_deleteEdges]
  constructor
  · intro he hEq
    subst e
    exact he.2 (by simp)
  · intro hne
    exact ⟨e.2, by
      intro hs
      apply hne
      apply Subtype.ext
      simpa using hs⟩

/-- No retained edge after leaf-edge deletion is incident with the leaf. -/
theorem no_retained_edge_incident_leaf {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (e : (deleteLeafEdge G huv).edgeSet)
    (hue : u ∈ (e : Sym2 V)) : False := by
  have heParts : e.1 ∈ G.edgeSet ∧ e.1 ∉ ({s(u, v)} : Set (Sym2 V)) := by
    simpa [deleteLeafEdge, SimpleGraph.edgeSet_deleteEdges] using e.2
  let eG : G.edgeSet := ⟨e.1, heParts.1⟩
  have heq := edge_eq_of_incident_degree_eq_one G hu huv eG hue
  apply heParts.2
  simp only [Set.mem_singleton_iff]
  exact congrArg Subtype.val heq

/-- At the degree-three endpoint of a deleted leaf edge, every retained
incident edge is one of the two explicitly named nonleaf edges. -/
theorem retained_edge_incident_three_eq_first_or_second
    {u v a b : V} (huv : G.Adj u v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hN : G.neighborFinset v = {u, a, b})
    (f : G.edgeSet)
    (hfD : f ∈ RetainedEdges (deleteLeafEdge G huv) G)
    (hvf : v ∈ (f : Sym2 V)) :
    f = (⟨s(v, a), hva⟩ : G.edgeSet) ∨
      f = (⟨s(v, b), hvb⟩ : G.edgeSet) := by
  obtain ⟨z, hfz⟩ := Sym2.mem_iff_exists.mp hvf
  have hvz : G.Adj v z := by
    have hfG := f.2
    rw [hfz] at hfG
    simpa using hfG
  have hzN : z ∈ ({u, a, b} : Finset V) := by
    rw [← hN]
    exact (G.mem_neighborFinset v z).mpr hvz
  have hz : z = u ∨ z = a ∨ z = b := by simpa using hzN
  rcases hz with hzu | hza | hzb
  · have hfe : f = (⟨s(u, v), huv⟩ : G.edgeSet) := by
      apply Subtype.ext
      simpa only [hzu, Sym2.eq_swap] using hfz
    exact False.elim (((mem_retained_deleteLeafEdge_iff G huv f).mp hfD) hfe)
  · apply Or.inl
    apply Subtype.ext
    simpa only [hza] using hfz
  · apply Or.inr
    apply Subtype.ext
    simpa only [hzb] using hfz

/-- Leaf-edge deletion reflects every adjacency between endpoints of
retained edges, so transporting a packing colouring is sound. -/
theorem deleteLeafEdge_reflectsAdjacency {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v) :
    ReflectsAdjacencyOnEdgeEndpoints
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) := by
  intro e f p q hpe hqf hpq
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨hpq, ?_⟩
  intro hdeleted
  have heq : s(p, q) = s(u, v) := by simpa using hdeleted
  rcases (Sym2.eq_iff.mp heq) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact no_retained_edge_incident_leaf G hu huv e hpe
  · exact no_retained_edge_incident_leaf G hu huv f hqf

/-- A valid colouring of the leaf-deleted graph transports to all retained
ambient edges without creating any old-old conflict. -/
theorem transport_deleteLeafEdge_valid {k : ℕ} {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor k)
    (hsmall : IsOneTwoColoring (deleteLeafEdge G huv) small) :
    IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small) := by
  exact transportColoringToSupergraph_valid
    (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V)))
    (deleteLeafEdge_reflectsAdjacency G hu huv) hsmall

/-! ## Transporting the Section 3 palette condition -/

/-- Deleting `u-v` changes no degree away from its endpoints. -/
theorem degree_deleteLeafEdge_eq_of_ne {u v q : V} (huv : G.Adj u v)
    (hqu : q ≠ u) (hqv : q ≠ v) :
    (deleteLeafEdge G huv).degree q = G.degree q := by
  have hadj (w : V) :
      (deleteLeafEdge G huv).Adj q w ↔ G.Adj q w := by
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · exact fun h => h.1
    · intro hqw
      refine ⟨hqw, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hs
      have hqmem : q ∈ (s(u, v) : Sym2 V) := by rw [← hs]; simp
      rcases (Sym2.mem_iff.mp hqmem) with h | h
      · exact hqu h
      · exact hqv h
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  rw [G.mem_neighborFinset, (deleteLeafEdge G huv).mem_neighborFinset,
    hadj]

/-- A degree-two vertex adjacent to a leaf sees at most four graph edges in
a subcubic graph. -/
theorem card_vertexVisibleEdgeFinset_le_four_of_adjacent_leaf
    (hsub : IsSubcubic G) {q u : V}
    (hq : IsTwoVertex G q) (hqu : G.Adj q u) (hu : G.degree u = 1) :
    (vertexVisibleEdgeFinset G q).card ≤ 4 := by
  classical
  have hcardN : (G.neighborFinset q).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hq
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hcardN
  have huN : u ∈ ({a, b} : Finset V) := by
    rw [← hN]
    exact (G.mem_neighborFinset q u).mpr hqu
  calc
    (vertexVisibleEdgeFinset G q).card ≤
        ∑ w ∈ G.neighborFinset q, (G.incidenceFinset w).card :=
      Finset.card_biUnion_le
    _ = G.degree a + G.degree b := by
      rw [hN]
      simp [hab, SimpleGraph.card_incidenceFinset_eq_degree]
    _ ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at huN
      rcases huN with rfl | rfl
      · rw [hu]
        exact Nat.add_le_add_left (hsub b) 1
      · rw [hu]
        exact Nat.add_le_add_right (hsub a) 1

/-- Fewer than six visible edges make the five-colour palette condition
automatic whenever a matching colour is visible. -/
theorem paletteCondition_at_of_visible_card_lt_six
    {colour : G.edgeSet → OneTwoColor 5} {q : V}
    (hcard : (vertexVisibleEdgeFinset G q).card < 6)
    (hmatch : VertexSeesMatching G colour q) :
    ¬ ∀ i : Fin 5, VertexSeesInduced G colour q i := by
  classical
  intro hall
  obtain ⟨m, hm, hqm⟩ := (vertexSeesMatching_iff G colour q).mp hmatch
  choose f hf z hz hclose using fun i =>
    (vertexSeesInduced_iff G colour q i).mp (hall i)
  let witness : OneTwoColor 5 → G.edgeSet
    | none => m
    | some i => f i
  have hwcolour (c : OneTwoColor 5) : colour (witness c) = c := by
    cases c with
    | none => exact hm
    | some i => exact hf i
  have hwmem (c : OneTwoColor 5) :
      (witness c : Sym2 V) ∈ vertexVisibleEdgeFinset G q := by
    cases c with
    | none =>
        exact mem_vertexVisibleEdgeFinset_of_endpoint_close G hqm (Or.inl rfl)
    | some i =>
        exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (hz i) (hclose i)
  let intoVisible : OneTwoColor 5 ↪
      {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} :=
    { toFun := fun c => ⟨witness c, hwmem c⟩
      inj' := by
        intro a b hab
        have hval : (witness a : Sym2 V) = (witness b : Sym2 V) :=
          congrArg (fun e : {e : Sym2 V //
            e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hab
        have hedge : witness a = witness b := Subtype.ext hval
        exact (hwcolour a).symm.trans
          ((congrArg colour hedge).trans (hwcolour b)) }
  have hsix : 6 ≤ (vertexVisibleEdgeFinset G q).card := by
    have hc := Fintype.card_le_of_injective intoVisible intoVisible.injective
    simpa using hc
  omega

theorem paletteCondition_at_of_adjacent_leaf
    (hsub : IsSubcubic G) {colour : G.edgeSet → OneTwoColor 5}
    {q u : V} (hq : IsTwoVertex G q) (hqu : G.Adj q u)
    (hu : G.degree u = 1)
    (hmatch : VertexSeesMatching G colour q) :
    ¬ ∀ i : Fin 5, VertexSeesInduced G colour q i := by
  apply paletteCondition_at_of_visible_card_lt_six G _ hmatch
  have hfour := card_vertexVisibleEdgeFinset_le_four_of_adjacent_leaf
    G hsub hq hqu hu
  omega

/-- Away from the deleted leaf edge, matching visibility of the transported
colouring is unchanged. -/
theorem vertexSeesMatching_transport_deleteLeafEdge_iff_of_ne
    {u v q : V} (huv : G.Adj u v) (hqu : q ≠ u) (hqv : q ≠ v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5) :
    VertexSeesMatching G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small) q ↔
      VertexSeesMatching (deleteLeafEdge G huv) small q := by
  rw [vertexSeesMatching_iff, vertexSeesMatching_iff]
  constructor
  · rintro ⟨e, hecolour, hqe⟩
    have heD : e ∈ RetainedEdges (deleteLeafEdge G huv) G := by
      by_contra heNot
      have heeq : e = (⟨s(u, v), huv⟩ : G.edgeSet) := by
        by_contra hne
        exact heNot ((mem_retained_deleteLeafEdge_iff G huv e).mpr hne)
      have heval : (e : Sym2 V) = s(u, v) :=
        congrArg Subtype.val heeq
      have hqmem : q ∈ (s(u, v) : Sym2 V) := by rw [← heval]; exact hqe
      rcases (Sym2.mem_iff.mp hqmem) with h | h
      · exact hqu h
      · exact hqv h
    let eH : (deleteLeafEdge G huv).edgeSet := ⟨e.1, heD⟩
    refine ⟨eH, ?_, hqe⟩
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small heD] at hecolour
    exact hecolour
  · rintro ⟨e, hecolour, hqe⟩
    let eG := edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) e
    exact ⟨eG, by simpa [eG] using hecolour, hqe⟩

/-- Away from the deleted edge's endpoints, induced-colour visibility of
the transported colouring is unchanged. -/
theorem vertexSeesInduced_transport_deleteLeafEdge_iff_of_ne
    {u v q : V} (huv : G.Adj u v) (hqu : q ≠ u) (hqv : q ≠ v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (i : Fin 5) :
    VertexSeesInduced G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small) q i ↔
      VertexSeesInduced (deleteLeafEdge G huv) small q i := by
  rw [vertexSeesInduced_iff, vertexSeesInduced_iff]
  constructor
  · rintro ⟨e, hecolour, z, hze, hqz⟩
    have heD : e ∈ RetainedEdges (deleteLeafEdge G huv) G := by
      by_contra heNot
      have heeq : e = (⟨s(u, v), huv⟩ : G.edgeSet) := by
        by_contra hne
        exact heNot ((mem_retained_deleteLeafEdge_iff G huv e).mpr hne)
      have heval : (e : Sym2 V) = s(u, v) :=
        congrArg Subtype.val heeq
      have : transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small e = none := by
        simp [transportColoringToSupergraph, heval]
      rw [this] at hecolour
      contradiction
    let eH : (deleteLeafEdge G huv).edgeSet := ⟨e.1, heD⟩
    refine ⟨eH, ?_, z, hze, ?_⟩
    · rw [transportColoringToSupergraph_of_mem
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small heD] at hecolour
      exact hecolour
    · rcases hqz with rfl | hqz
      · exact Or.inl rfl
      · right
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hqz, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro hs
        have hqmem : q ∈ (s(u, v) : Sym2 V) := by rw [← hs]; simp
        rcases (Sym2.mem_iff.mp hqmem) with h | h
        · exact hqu h
        · exact hqv h
  · rintro ⟨e, hecolour, z, hze, hqz⟩
    let eG := edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) e
    refine ⟨eG, by simpa [eG] using hecolour, z, hze, ?_⟩
    exact hqz.imp_right (fun h =>
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) h)

/-- Condition I of a good colouring of the leaf-deleted graph transports to
the ambient graph.  The only new ambient degree-two endpoint is handled by
the visible-edge capacity bound above. -/
theorem conditionI_transport_deleteLeafEdge
    (hsub : IsSubcubic G) {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : ConditionI (deleteLeafEdge G huv) small) :
    ConditionI G
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small) := by
  intro q hq hmatch hall
  by_cases hqu : q = u
  · subst q
    unfold IsTwoVertex at hq
    omega
  by_cases hqv : q = v
  · subst q
    exact (paletteCondition_at_of_adjacent_leaf G hsub hq huv.symm hu hmatch) hall
  have hqSmall : IsTwoVertex (deleteLeafEdge G huv) q := by
    unfold IsTwoVertex at hq ⊢
    rw [degree_deleteLeafEdge_eq_of_ne G huv hqu hqv]
    exact hq
  apply hsmall q hqSmall
  · exact (vertexSeesMatching_transport_deleteLeafEdge_iff_of_ne G huv
      hqu hqv small).mp hmatch
  · intro i
    exact (vertexSeesInduced_transport_deleteLeafEdge_iff_of_ne G huv
      hqu hqv small i).mp (hall i)

/-! ## Restoring the leaf edge with the matching colour -/

theorem leafEdge_not_mem_retained {u v : V} (huv : G.Adj u v) :
    (⟨s(u, v), huv⟩ : G.edgeSet) ∉
      RetainedEdges (deleteLeafEdge G huv) G := by
  rw [mem_retained_deleteLeafEdge_iff]
  simp

theorem insert_leafEdge_retained_eq_univ {u v : V} (huv : G.Adj u v) :
    insert (⟨s(u, v), huv⟩ : G.edgeSet)
        (RetainedEdges (deleteLeafEdge G huv) G) = Set.univ := by
  ext f
  constructor
  · exact fun _ => Set.mem_univ f
  · intro _
    by_cases hfe : f = (⟨s(u, v), huv⟩ : G.edgeSet)
    · exact Set.mem_insert_iff.mpr (Or.inl hfe)
    · exact Set.mem_insert_iff.mpr (Or.inr
        ((mem_retained_deleteLeafEdge_iff G huv f).mpr hfe))

/-- If no retained matching-coloured edge is incident with the nonleaf
endpoint, the missing leaf edge can receive the matching colour. -/
theorem matching_available_leafEdge_of_no_matching_at_neighbor
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hnoMatch : ∀ f : G.edgeSet,
      f ∈ RetainedEdges (deleteLeafEdge G huv) G →
      v ∈ (f : Sym2 V) →
      transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small f ≠ none) :
    ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G)
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
      (⟨s(u, v), huv⟩ : G.edgeSet) none := by
  rw [colorAvailableOn_none_iff]
  intro f hfD _ hcf x hxe hxf
  have hx : x = u ∨ x = v := by simpa using hxe
  rcases hx with rfl | rfl
  · let fH : (deleteLeafEdge G huv).edgeSet := ⟨f.1, hfD⟩
    exact no_retained_edge_incident_leaf G hu huv fH hxf
  · exact hnoMatch f hfD hxf hcf

/-- A colour absent from the induced-colour view of the nonleaf endpoint
is available on the deleted leaf edge.  The leaf hypothesis is what turns
every possible distance-two blocker through `u` back into an edge visible
from `v`. -/
theorem induced_available_leafEdge_of_not_seen_at_neighbor
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (D : Set G.edgeSet) (hD : D ⊆ RetainedEdges (deleteLeafEdge G huv) G)
    (colour : G.edgeSet → OneTwoColor 5) (i : Fin 5)
    (hmiss : ¬ VertexSeesInduced G colour v i) :
    ColorAvailableOn G D colour
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i) := by
  rw [colorAvailableOn_some_iff]
  intro f hfD hfe hfi
  rw [inducedSeparated_iff_forall_endpoints]
  intro p hpe q hqf
  have hp : p = u ∨ p = v := by simpa using hpe
  constructor
  · intro hpq
    rcases hp with hpu | hpv
    · have huf : u ∈ (f : Sym2 V) := by
        rw [← hpu, hpq]
        exact hqf
      have hfRetained := hD hfD
      let hfSmall : (deleteLeafEdge G huv).edgeSet :=
        ⟨f.1, hfRetained⟩
      apply no_retained_edge_incident_leaf G hu huv hfSmall
      simpa [hfSmall] using huf
    · have hvf : v ∈ (f : Sym2 V) := by
        rw [← hpv, hpq]
        exact hqf
      apply hmiss
      rw [vertexSeesInduced_iff]
      exact ⟨f, hfi, v, hvf, Or.inl rfl⟩
  · intro hpq
    rcases hp with hpu | hpv
    · have huq : G.Adj u q := by simpa [hpu] using hpq
      have hqv : q = v := eq_neighbor_of_degree_eq_one G hu huv huq
      subst q
      apply hmiss
      rw [vertexSeesInduced_iff]
      exact ⟨f, hfi, v, hqf, Or.inl rfl⟩
    · have hvq : G.Adj v q := by simpa [hpv] using hpq
      apply hmiss
      rw [vertexSeesInduced_iff]
      exact ⟨f, hfi, q, hqf, Or.inr hvq⟩

/-- If the nonleaf endpoint is a two-vertex which sees the matching colour,
Condition I supplies an induced colour available on the missing leaf edge. -/
theorem exists_induced_available_leafEdge_of_two_neighbor
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (colour : G.edgeSet → OneTwoColor 5)
    (hcondition : ConditionI G colour) (hv : IsTwoVertex G v)
    (hmatch : VertexSeesMatching G colour v) :
    ∃ i : Fin 5, ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i) := by
  classical
  have hnotAll := hcondition v hv hmatch
  push_neg at hnotAll
  obtain ⟨i, hi⟩ := hnotAll
  exact ⟨i, induced_available_leafEdge_of_not_seen_at_neighbor G hu huv _
    (fun _ h ↦ h) colour i hi⟩

/-- Recolouring the deleted leaf edge with an induced colour preserves
Condition I when its nonleaf endpoint has degree two.  Every affected
two-vertex is either that endpoint (where the adjacent-leaf capacity bound
applies) or is adjacent to it (where the adjacent-two-vertices bound
applies). -/
theorem conditionI_recolor_leafEdge_of_two_neighbor
    (hsub : IsSubcubic G) {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsTwoVertex G v)
    (colour : G.edgeSet → OneTwoColor 5)
    (hcondition : ConditionI G colour) (i : Fin 5) :
    ConditionI G
      (recolor G colour (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  apply hcondition.recolor_of_local G
  intro q hq haffect hmatch
  have haffect' :
      q ∈ (e : Sym2 V) ∨
        ∃ p, p ∈ (e : Sym2 V) ∧ (q = p ∨ G.Adj q p) := by
    simpa [e] using haffect
  have hnear : q = u ∨ q = v ∨ G.Adj q u ∨ G.Adj q v := by
    rcases haffect' with hqe | ⟨p, hpe, hqp⟩
    · have hq : q = u ∨ q = v := by simpa [e] using hqe
      exact hq.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
    · have hp : p = u ∨ p = v := by simpa [e] using hpe
      rcases hp with rfl | rfl
      · rcases hqp with rfl | hqu
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl hqu))
      · rcases hqp with rfl | hqv
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr hqv))
  rcases hnear with rfl | rfl | hqu | hqv
  · unfold IsTwoVertex at hq
    omega
  · exact paletteCondition_at_of_adjacent_leaf G hsub hv huv.symm hu hmatch
  · have hqv' : q = v :=
      eq_neighbor_of_degree_eq_one G hu huv hqu.symm
    subst q
    exact paletteCondition_at_of_adjacent_leaf G hsub hv huv.symm hu hmatch
  · exact paletteCondition_at_of_adjacent_two G hsub hq hqv hv hmatch

/-- Complete extension across a leaf whose nonleaf endpoint has degree two,
provided that endpoint already sees a retained matching edge. -/
theorem exists_goodFive_extension_leaf_of_two_neighbor
    (hsub : IsSubcubic G) {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsTwoVertex G v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteLeafEdge G huv) small)
    (hmatch : VertexSeesMatching G
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small) v) :
    ∃ i : Fin 5, GoodFive G
      (recolor G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
  have hcondition : ConditionI G base := by
    exact conditionI_transport_deleteLeafEdge G hsub hu huv small
      hsmall.paletteCondition
  obtain ⟨i, hi⟩ := exists_induced_available_leafEdge_of_two_neighbor
    G hu huv base hcondition hv (by simpa [base] using hmatch)
  refine ⟨i, ?_⟩
  have hvalidD : IsOneTwoColoringOn G D base := by
    exact transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hnot : e ∉ D := by
    exact leafEdge_not_mem_retained G huv
  have htotal := hvalidD.extend_one G hnot (by simpa [D, base, e] using hi)
  have hset : insert e D = Set.univ := by
    exact insert_leafEdge_retained_eq_univ G huv
  rw [hset] at htotal
  refine ⟨htotal, ?_⟩
  exact conditionI_recolor_leafEdge_of_two_neighbor G hsub hu huv hv base
    hcondition i

/-- The complete easy leaf-extension branch: a good colouring of the
deleted graph extends whenever the matching colour is available. -/
theorem goodFive_of_leaf_matching_available
    (hsub : IsSubcubic G) {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteLeafEdge G huv) small)
    (havail : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
      (⟨s(u, v), huv⟩ : G.edgeSet) none) :
    GoodFive G
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small) := by
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
  have hvalidD : IsOneTwoColoringOn G D base := by
    exact transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hnot : e ∉ D := leafEdge_not_mem_retained G huv
  have heBase : base e = none := by
    simp [base, e, transportColoringToSupergraph]
  have hrecolor : recolor G base e none = base := by
    funext f
    by_cases hfe : f = e
    · subst f
      simp [recolor, heBase]
    · simp [recolor, hfe]
  have htotal := hvalidD.extend_one G hnot havail
  have hset : insert e D = Set.univ :=
    insert_leafEdge_retained_eq_univ G huv
  rw [hset, hrecolor] at htotal
  exact ⟨htotal,
    conditionI_transport_deleteLeafEdge G hsub hu huv small
      hsmall.paletteCondition⟩

end Finite

end

end LeanCo.PackingEdgeColoring
