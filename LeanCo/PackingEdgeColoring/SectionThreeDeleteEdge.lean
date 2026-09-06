import LeanCo.PackingEdgeColoring.SectionThreeNoThreeChain
import LeanCo.PackingEdgeColoring.AvailabilityMultiplicity
import LeanCo.PackingEdgeColoring.ColorSymmetry

/-!
# Deleting the middle edge of a two-thread

The reductions for the `(2,1,1)` and `(2,2,0)` configurations delete the
edge between the two degree-two vertices of a two-thread.  Restoring that
edge can shorten the line-graph distance between the two surviving outer
edges.  This file records that single exceptional pair explicitly; no
generic (and false) subgraph-to-supergraph transport principle is used.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The spanning graph obtained by deleting the middle edge `a-x`. -/
abbrev deleteMiddleEdge {a x : V} (hax : G.Adj a x) : SimpleGraph V :=
  G.deleteEdges ({s(a, x)} : Set (Sym2 V))

/-- A retained ambient edge is exactly an edge other than the deleted
middle edge. -/
theorem mem_retained_deleteMiddleEdge_iff
    {a x : V} (hax : G.Adj a x) (f : G.edgeSet) :
    f ∈ RetainedEdges (deleteMiddleEdge G hax) G ↔
      f ≠ (⟨s(a, x), hax⟩ : G.edgeSet) := by
  rw [RetainedEdges, edgeSet_deleteEdges]
  constructor
  · intro hf hEq
    subst f
    exact hf.2 (by simp)
  · intro hne
    exact ⟨f.2, by
      intro hf
      have hval : (f : Sym2 V) = s(a, x) := by simpa using hf
      exact hne (Subtype.ext hval)⟩

/-- At the left degree-two endpoint, the only retained incident edge is
the prescribed outer edge. -/
theorem retained_edge_eq_leftOuter_of_incident
    {u a x : V} (ha : IsTwoVertex G a)
    (hua : G.Adj u a) (hax : G.Adj a x) (hux : u ≠ x)
    (f : G.edgeSet)
    (hfD : f ∈ RetainedEdges (deleteMiddleEdge G hax) G)
    (haf : a ∈ (f : Sym2 V)) :
    f = (⟨s(u, a), hua⟩ : G.edgeSet) := by
  rcases edge_eq_left_or_right_of_incident_two G ha hua.symm hax hux
      f haf with hf | hf
  · exact Subtype.ext (by simpa only [Sym2.eq_swap] using hf)
  · have heq : f = (⟨s(a, x), hax⟩ : G.edgeSet) := Subtype.ext hf
    exact False.elim ((mem_retained_deleteMiddleEdge_iff G hax f).mp hfD heq)

/-- Symmetric retained-edge description at the right endpoint. -/
theorem retained_edge_eq_rightOuter_of_incident
    {a x z : V} (hx : IsTwoVertex G x)
    (hax : G.Adj a x) (hxz : G.Adj x z) (haz : a ≠ z)
    (f : G.edgeSet)
    (hfD : f ∈ RetainedEdges (deleteMiddleEdge G hax) G)
    (hxf : x ∈ (f : Sym2 V)) :
    f = (⟨s(x, z), hxz⟩ : G.edgeSet) := by
  rcases edge_eq_left_or_right_of_incident_two G hx hax.symm hxz haz
      f hxf with hf | hf
  · have heq : f = (⟨s(a, x), hax⟩ : G.edgeSet) := by
      apply Subtype.ext
      simpa only [Sym2.eq_swap] using hf
    exact False.elim ((mem_retained_deleteMiddleEdge_iff G hax f).mp hfD heq)
  · exact Subtype.ext hf

/-- The left outer edge survives deletion of the middle edge. -/
theorem leftOuter_mem_deleteMiddleEdge
    {u a x : V} (hua : G.Adj u a) (hax : G.Adj a x) (hux : u ≠ x) :
    s(u, a) ∈ (deleteMiddleEdge G hax).edgeSet := by
  rw [edgeSet_deleteEdges]
  refine ⟨hua, ?_⟩
  intro hm
  have hs : s(u, a) = s(a, x) := by simpa using hm
  have hxmem : x ∈ (s(u, a) : Sym2 V) := by rw [hs]; simp
  have hx : x = u ∨ x = a := by simpa using hxmem
  rcases hx with hxu | hxa
  · exact hux hxu.symm
  · exact hax.ne hxa.symm

/-- The right outer edge survives deletion of the middle edge. -/
theorem rightOuter_mem_deleteMiddleEdge
    {a x z : V} (hax : G.Adj a x) (hxz : G.Adj x z) (haz : a ≠ z) :
    s(x, z) ∈ (deleteMiddleEdge G hax).edgeSet := by
  rw [edgeSet_deleteEdges]
  refine ⟨hxz, ?_⟩
  intro hm
  have hs : s(x, z) = s(a, x) := by simpa using hm
  have hamem : a ∈ (s(x, z) : Sym2 V) := by rw [hs]; simp
  have ha : a = x ∨ a = z := by simpa using hamem
  rcases ha with hax' | haz'
  · exact hax.ne hax'
  · exact haz haz'

/-- If an ambient adjacency between endpoints of two retained edges is
lost after deleting `a-x`, then the endpoint pair is exactly `a,x`, up to
order. -/
theorem deleted_middle_endpoint_pair
    {a x p q : V} (hax : G.Adj a x)
    (hpq : G.Adj p q)
    (hnot : ¬ (deleteMiddleEdge G hax).Adj p q) :
    (p = a ∧ q = x) ∨ (p = x ∧ q = a) := by
  rw [deleteMiddleEdge, SimpleGraph.deleteEdges_adj] at hnot
  push_neg at hnot
  have hs : s(p, q) = s(a, x) := by simpa using hnot hpq
  simpa only [Sym2.eq_iff] using hs

/-- Induced separation transports across the middle-edge deletion provided
the two surviving outer edges are themselves separated in the ambient
graph. -/
theorem inducedSeparated_of_deleteMiddleEdge
    {u a x z : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    {f g : G.edgeSet}
    (hfD : f ∈ RetainedEdges (deleteMiddleEdge G hax) G)
    (hgD : g ∈ RetainedEdges (deleteMiddleEdge G hax) G)
    (hsmall : InducedSeparated (deleteMiddleEdge G hax)
      ⟨f.1, hfD⟩ ⟨g.1, hgD⟩)
    (houter : InducedSeparated G
      (⟨s(u, a), hua⟩ : G.edgeSet)
      (⟨s(x, z), hxz⟩ : G.edgeSet)) :
    InducedSeparated G f g := by
  refine ⟨hsmall.1, ?_⟩
  rintro ⟨p, hpf, q, hqg, hpq⟩
  have hnotSmall : ¬ (deleteMiddleEdge G hax).Adj p q := by
    intro hpqSmall
    exact hsmall.2 ⟨p, hpf, q, hqg, hpqSmall⟩
  rcases deleted_middle_endpoint_pair G hax hpq hnotSmall with hpair | hpair
  · have hfa : a ∈ (f : Sym2 V) := hpair.1.symm ▸ hpf
    have hgx : x ∈ (g : Sym2 V) := hpair.2.symm ▸ hqg
    have hfEq := retained_edge_eq_leftOuter_of_incident G ha hua hax hux
      f hfD hfa
    have hgEq := retained_edge_eq_rightOuter_of_incident G hx hax hxz haz
      g hgD hgx
    apply houter.2
    refine ⟨a, ?_, x, ?_, hax⟩
    · rw [← hfEq]
      exact hfa
    · rw [← hgEq]
      exact hgx
  · have hfx : x ∈ (f : Sym2 V) := hpair.1.symm ▸ hpf
    have hga : a ∈ (g : Sym2 V) := hpair.2.symm ▸ hqg
    have hfEq := retained_edge_eq_rightOuter_of_incident G hx hax hxz haz
      f hfD hfx
    have hgEq := retained_edge_eq_leftOuter_of_incident G ha hua hax hux
      g hgD hga
    apply ((inducedSeparated_comm G).mp houter).2
    refine ⟨x, ?_, a, ?_, hax.symm⟩
    · exact hfEq ▸ hfx
    · exact hgEq ▸ hga

/-- A valid colouring of the deleted graph transports to all retained
ambient edges once the only exceptional outer pair is dealt with. -/
theorem transport_deleteMiddleEdge_valid
    {u a x z : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    (small : (deleteMiddleEdge G hax).edgeSet → OneTwoColor 5)
    (hsmall : IsOneTwoColoring (deleteMiddleEdge G hax) small)
    (houter : ∀ i : Fin 5,
      small ⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩ = some i →
      small ⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩ = some i →
      InducedSeparated G
        (⟨s(u, a), hua⟩ : G.edgeSet)
        (⟨s(x, z), hxz⟩ : G.edgeSet)) :
    IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G)
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small) := by
  let H := deleteMiddleEdge G hax
  let base := transportColoringToSupergraph
    (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small
  apply (isOneTwoColoringOn_transport_iff
    (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small).mpr
  intro f g hfg
  have hp := hsmall f (by simp) g (by simp) hfg
  cases hcf : small f with
  | none =>
      cases hcg : small g with
      | none =>
          have hend : EndpointDisjoint H f g := by
            simpa [H, hcf, hcg, PairCompatible] using hp
          right
          exact hend
      | some j => exact pairCompatible_of_ne G (by simp [hcf, hcg])
  | some i =>
      cases hcg : small g with
      | none => exact pairCompatible_of_ne G (by simp [hcf, hcg])
      | some j =>
          by_cases hij : i = j
          · subst j
            have hsepH : InducedSeparated H f g := by
              simpa [H, hcf, hcg, PairCompatible] using hp
            let fG := edgeEmbeddingOfLE
              (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) f
            let gG := edgeEmbeddingOfLE
              (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) g
            refine (pairCompatible_some_self G i).mpr ⟨hsepH.1, ?_⟩
            rintro ⟨p, hpf, q, hqg, hpq⟩
            have hnotSmall : ¬ H.Adj p q := by
              intro hpqH
              exact hsepH.2 ⟨p, hpf, q, hqg, hpqH⟩
            have hfD : fG ∈ RetainedEdges H G := f.2
            have hgD : gG ∈ RetainedEdges H G := g.2
            rcases deleted_middle_endpoint_pair G hax hpq hnotSmall with
                hpair | hpair
            · have hfa : a ∈ (fG : Sym2 V) := hpair.1.symm ▸ hpf
              have hgx : x ∈ (gG : Sym2 V) := hpair.2.symm ▸ hqg
              have hfEq := retained_edge_eq_leftOuter_of_incident G ha hua
                hax hux fG hfD hfa
              have hgEq := retained_edge_eq_rightOuter_of_incident G hx hax
                hxz haz gG hgD hgx
              have hfEqH : f =
                  ⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩ := by
                apply Subtype.ext
                exact congrArg (fun e : G.edgeSet => (e : Sym2 V)) hfEq
              have hgEqH : g =
                  ⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩ := by
                apply Subtype.ext
                exact congrArg (fun e : G.edgeSet => (e : Sym2 V)) hgEq
              have hsepOuter := houter i (hfEqH ▸ hcf) (hgEqH ▸ hcg)
              exact hsepOuter.2 ⟨a, by simp, x, by simp, hax⟩
            · have hfx : x ∈ (fG : Sym2 V) := hpair.1.symm ▸ hpf
              have hga : a ∈ (gG : Sym2 V) := hpair.2.symm ▸ hqg
              have hfEq := retained_edge_eq_rightOuter_of_incident G hx hax
                hxz haz fG hfD hfx
              have hgEq := retained_edge_eq_leftOuter_of_incident G ha hua
                hax hux gG hgD hga
              have hfEqH : f =
                  ⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩ := by
                apply Subtype.ext
                exact congrArg (fun e : G.edgeSet => (e : Sym2 V)) hfEq
              have hgEqH : g =
                  ⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩ := by
                apply Subtype.ext
                exact congrArg (fun e : G.edgeSet => (e : Sym2 V)) hgEq
              have hsepOuter := houter i (hgEqH ▸ hcg) (hfEqH ▸ hcf)
              exact ((inducedSeparated_comm G).mp hsepOuter).2
                ⟨x, by simp, a, by simp, hax.symm⟩
          · exact pairCompatible_of_ne G (by simp [hcf, hcg, hij])

/-- Removing the left outer edge from the retained domain eliminates the
only possible transport obstruction. -/
theorem transport_deleteMiddleEdge_valid_without_left
    {u a x z : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    (small : (deleteMiddleEdge G hax).edgeSet → OneTwoColor 5)
    (hsmall : IsOneTwoColoring (deleteMiddleEdge G hax) small) :
    IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(u, a), hua⟩ : G.edgeSet)})
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small) := by
  -- The proof is the preceding transport argument with the exceptional
  -- pair impossible because its left member is absent.
  let H := deleteMiddleEdge G hax
  let base := transportColoringToSupergraph
    (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small
  intro f hf g hg hfg
  have hfD := hf.1
  have hgD := hg.1
  let fH : H.edgeSet := ⟨f.1, hfD⟩
  let gH : H.edgeSet := ⟨g.1, hgD⟩
  have hfgH : fH ≠ gH := by
    intro heq
    apply hfg
    apply Subtype.ext
    exact congrArg (fun e : H.edgeSet => (e : Sym2 V)) heq
  have hp := hsmall fH (by simp) gH (by simp) hfgH
  change PairCompatible G f g
    (transportColoringToSupergraph
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small f)
    (transportColoringToSupergraph
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small g)
  rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small hfD,
    transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small hgD]
  change PairCompatible G f g (small fH) (small gH)
  cases hcf : small fH with
  | none =>
      cases hcg : small gH with
      | none =>
          have hend : EndpointDisjoint H fH gH := by
            simpa [H, hcf, hcg, PairCompatible] using hp
          right
          exact hend
      | some j => exact pairCompatible_of_ne G (by simp [hcf, hcg])
  | some i =>
      cases hcg : small gH with
      | none => exact pairCompatible_of_ne G (by simp [hcf, hcg])
      | some j =>
          by_cases hij : i = j
          · subst j
            have hsepH : InducedSeparated H fH gH := by
              simpa [H, hcf, hcg, PairCompatible] using hp
            refine (pairCompatible_some_self G i).mpr ⟨hsepH.1, ?_⟩
            rintro ⟨p, hpf, q, hqg, hpq⟩
            have hnotSmall : ¬ H.Adj p q := by
              intro hpqH
              exact hsepH.2 ⟨p, hpf, q, hqg, hpqH⟩
            rcases deleted_middle_endpoint_pair G hax hpq hnotSmall with
                hpair | hpair
            · have hfa : a ∈ (f : Sym2 V) := hpair.1.symm ▸ hpf
              have hfEq := retained_edge_eq_leftOuter_of_incident G ha hua
                hax hux f hfD hfa
              exact hf.2 (by simpa using hfEq)
            · have hga : a ∈ (g : Sym2 V) := hpair.2.symm ▸ hqg
              have hgEq := retained_edge_eq_leftOuter_of_incident G ha hua
                hax hux g hgD hga
              exact hg.2 (by simpa using hgEq)
          · exact pairCompatible_of_ne G (by simp [hcf, hcg, hij])

/-- Right-handed version of
`transport_deleteMiddleEdge_valid_without_left`. -/
theorem transport_deleteMiddleEdge_valid_without_right
    {u a x z : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    (small : (deleteMiddleEdge G hax).edgeSet → OneTwoColor 5)
    (hsmall : IsOneTwoColoring (deleteMiddleEdge G hax) small) :
    IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(x, z), hxz⟩ : G.edgeSet)})
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small) := by
  let H := deleteMiddleEdge G hax
  intro f hf g hg hfg
  have hfD := hf.1
  have hgD := hg.1
  let fH : H.edgeSet := ⟨f.1, hfD⟩
  let gH : H.edgeSet := ⟨g.1, hgD⟩
  have hfgH : fH ≠ gH := by
    intro heq
    apply hfg
    apply Subtype.ext
    exact congrArg (fun e : H.edgeSet => (e : Sym2 V)) heq
  have hp := hsmall fH (by simp) gH (by simp) hfgH
  change PairCompatible G f g
    (transportColoringToSupergraph
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small f)
    (transportColoringToSupergraph
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small g)
  rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small hfD,
    transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small hgD]
  change PairCompatible G f g (small fH) (small gH)
  cases hcf : small fH with
  | none =>
      cases hcg : small gH with
      | none =>
          have hend : EndpointDisjoint H fH gH := by
            simpa [H, hcf, hcg, PairCompatible] using hp
          right
          exact hend
      | some j => exact pairCompatible_of_ne G (by simp [hcf, hcg])
  | some i =>
      cases hcg : small gH with
      | none => exact pairCompatible_of_ne G (by simp [hcf, hcg])
      | some j =>
          by_cases hij : i = j
          · subst j
            have hsepH : InducedSeparated H fH gH := by
              simpa [H, hcf, hcg, PairCompatible] using hp
            refine (pairCompatible_some_self G i).mpr ⟨hsepH.1, ?_⟩
            rintro ⟨p, hpf, q, hqg, hpq⟩
            have hnotSmall : ¬ H.Adj p q := by
              intro hpqH
              exact hsepH.2 ⟨p, hpf, q, hqg, hpqH⟩
            rcases deleted_middle_endpoint_pair G hax hpq hnotSmall with
                hpair | hpair
            · have hgx : x ∈ (g : Sym2 V) := hpair.2.symm ▸ hqg
              have hgEq := retained_edge_eq_rightOuter_of_incident G hx hax
                hxz haz g hgD hgx
              exact hg.2 (by simpa using hgEq)
            · have hfx : x ∈ (f : Sym2 V) := hpair.1.symm ▸ hpf
              have hfEq := retained_edge_eq_rightOuter_of_incident G hx hax
                hxz haz f hfD hfx
              exact hf.2 (by simpa using hfEq)
          · exact pairCompatible_of_ne G (by simp [hcf, hcg, hij])

/-! ## Transporting Condition I -/

/-- Deleting `a-x` does not change the degree of any other vertex. -/
theorem degree_deleteMiddleEdge_eq_of_ne
    {a x q : V} (hax : G.Adj a x) (hqa : q ≠ a) (hqx : q ≠ x) :
    (deleteMiddleEdge G hax).degree q = G.degree q := by
  have hadj (v : V) :
      (deleteMiddleEdge G hax).Adj q v ↔ G.Adj q v := by
    rw [deleteMiddleEdge, SimpleGraph.deleteEdges_adj]
    constructor
    · exact fun h => h.1
    · intro hqv
      refine ⟨hqv, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hs
      have hqmem : q ∈ (s(a, x) : Sym2 V) := by rw [← hs]; simp
      have hq : q = a ∨ q = x := by simpa using hqmem
      exact hq.elim hqa hqx
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext v
  rw [G.mem_neighborFinset, (deleteMiddleEdge G hax).mem_neighborFinset,
    hadj]

/-- Away from the endpoints of the deleted edge, matching visibility of
the transported colouring is unchanged. -/
theorem vertexSeesMatching_transport_deleteMiddleEdge_iff_of_ne
    {a x q : V} (hax : G.Adj a x) (hqa : q ≠ a) (hqx : q ≠ x)
    (small : (deleteMiddleEdge G hax).edgeSet → OneTwoColor 5) :
    VertexSeesMatching G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small) q ↔
      VertexSeesMatching (deleteMiddleEdge G hax) small q := by
  rw [vertexSeesMatching_iff, vertexSeesMatching_iff]
  constructor
  · rintro ⟨e, hecolour, hqe⟩
    have heD : e ∈ RetainedEdges (deleteMiddleEdge G hax) G := by
      by_contra heNot
      have heEq : e = (⟨s(a, x), hax⟩ : G.edgeSet) := by
        by_contra hne
        exact heNot ((mem_retained_deleteMiddleEdge_iff G hax e).mpr hne)
      subst e
      have hq : q = a ∨ q = x := by simpa using hqe
      exact hq.elim hqa hqx
    let eH : (deleteMiddleEdge G hax).edgeSet := ⟨e.1, heD⟩
    refine ⟨eH, ?_, hqe⟩
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small heD] at hecolour
    exact hecolour
  · rintro ⟨e, hecolour, hqe⟩
    let eG := edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) e
    exact ⟨eG, by simpa [eG] using hecolour, hqe⟩

/-- Away from the endpoints of the deleted edge, induced-colour visibility
of the transported colouring is unchanged. -/
theorem vertexSeesInduced_transport_deleteMiddleEdge_iff_of_ne
    {a x q : V} (hax : G.Adj a x) (hqa : q ≠ a) (hqx : q ≠ x)
    (small : (deleteMiddleEdge G hax).edgeSet → OneTwoColor 5)
    (i : Fin 5) :
    VertexSeesInduced G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small) q i ↔
      VertexSeesInduced (deleteMiddleEdge G hax) small q i := by
  rw [vertexSeesInduced_iff, vertexSeesInduced_iff]
  constructor
  · rintro ⟨e, hecolour, v, hve, hqv⟩
    have heD : e ∈ RetainedEdges (deleteMiddleEdge G hax) G := by
      by_contra heNot
      have heEq : e = (⟨s(a, x), hax⟩ : G.edgeSet) := by
        by_contra hne
        exact heNot ((mem_retained_deleteMiddleEdge_iff G hax e).mpr hne)
      subst e
      simp [transportColoringToSupergraph] at hecolour
    let eH : (deleteMiddleEdge G hax).edgeSet := ⟨e.1, heD⟩
    refine ⟨eH, ?_, v, hve, ?_⟩
    · rw [transportColoringToSupergraph_of_mem
        (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small heD] at hecolour
      exact hecolour
    · rcases hqv with rfl | hqv
      · exact Or.inl rfl
      · right
        rw [deleteMiddleEdge, SimpleGraph.deleteEdges_adj]
        refine ⟨hqv, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro hs
        have hqmem : q ∈ (s(a, x) : Sym2 V) := by rw [← hs]; simp
        have hq : q = a ∨ q = x := by simpa using hqmem
        exact hq.elim hqa hqx
  · rintro ⟨e, hecolour, v, hve, hqv⟩
    let eG := edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) e
    refine ⟨eG, by simpa [eG] using hecolour, v, hve, ?_⟩
    exact hqv.imp_right (fun h =>
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) h)

/-- Condition I of a good colouring of the deleted graph transports to the
ambient graph.  The two endpoints, which have dropped to degree one in the
deleted graph, are discharged by the adjacent-degree-two capacity lemma. -/
theorem conditionI_transport_deleteMiddleEdge
    (hsub : IsSubcubic G)
    {a x : V} (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hax : G.Adj a x)
    (small : (deleteMiddleEdge G hax).edgeSet → OneTwoColor 5)
    (hsmall : ConditionI (deleteMiddleEdge G hax) small) :
    ConditionI G
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small) := by
  intro q hq hmatch hall
  by_cases hqa : q = a
  · subst q
    exact (paletteCondition_at_of_adjacent_two G hsub ha hax hx hmatch) hall
  by_cases hqx : q = x
  · subst q
    exact (paletteCondition_at_of_adjacent_two G hsub hx hax.symm ha hmatch) hall
  have hqSmall : IsTwoVertex (deleteMiddleEdge G hax) q := by
    unfold IsTwoVertex at hq ⊢
    rw [degree_deleteMiddleEdge_eq_of_ne G hax hqa hqx]
    exact hq
  apply hsmall q hqSmall
  · exact (vertexSeesMatching_transport_deleteMiddleEdge_iff_of_ne G hax
      hqa hqx small).mp hmatch
  · intro i
    exact (vertexSeesInduced_transport_deleteMiddleEdge_iff_of_ne G hax
      hqa hqx small i).mp (hall i)

/-! ## Directional preservation of Condition I -/

/-- A condition-I proof can be transferred when all newly matching edges
lie in `M`, all newly induced-coloured edges lie in `I`, and precisely the
vertices which can notice those gains are checked explicitly.  Edges whose
old colour merely disappears need not be placed in either support. -/
theorem ConditionI.of_new_supports
    {old new : G.edgeSet → OneTwoColor 5}
    (hold : ConditionI G old) (M I : Set G.edgeSet)
    (hmatching : ∀ e, new e = none → old e = none ∨ e ∈ M)
    (hinduced : ∀ e i, new e = some i → old e = some i ∨ e ∈ I)
    (hcheck : ∀ q, IsTwoVertex G q →
      (MatchingAffectedBy G M q ∨ InducedAffectedBy G I q) →
      VertexSeesMatching G new q →
      ¬ ∀ i : Fin 5, VertexSeesInduced G new q i) :
    ConditionI G new := by
  intro q hq hmatch hall
  by_cases haffect : MatchingAffectedBy G M q ∨ InducedAffectedBy G I q
  · exact hcheck q hq haffect hmatch hall
  apply hold q hq
  · rw [vertexSeesMatching_iff] at hmatch ⊢
    obtain ⟨e, he, hqe⟩ := hmatch
    rcases hmatching e he with heOld | heM
    · exact ⟨e, heOld, hqe⟩
    · exact False.elim (haffect (Or.inl ⟨e, heM, hqe⟩))
  · intro i
    rw [vertexSeesInduced_iff]
    obtain ⟨e, he, v, hve, hqv⟩ :=
      (vertexSeesInduced_iff G new q i).mp (hall i)
    rcases hinduced e i he with heOld | heI
    · exact ⟨e, heOld, v, hve, hqv⟩
    · exact False.elim (haffect (Or.inr ⟨e, heI, v, hve, hqv⟩))

/-- A degree-two vertex in a subcubic graph sees at most six ambient
edges. -/
theorem card_vertexVisibleEdgeFinset_le_six
    (hsub : IsSubcubic G) {q : V} (hq : IsTwoVertex G q) :
    (vertexVisibleEdgeFinset G q).card ≤ 6 := by
  classical
  have hcardN : (G.neighborFinset q).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hq
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hcardN
  calc
    (vertexVisibleEdgeFinset G q).card ≤
        ∑ v ∈ G.neighborFinset q, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = G.degree a + G.degree b := by
      rw [hN]
      simp [hab, SimpleGraph.card_incidenceFinset_eq_degree]
    _ ≤ 6 := by
      have ha := hsub a
      have hb := hsub b
      omega

/-- Two distinct matching-coloured edges visible from a degree-two vertex
leave room for at most four induced colours among its at most six visible
edges. -/
theorem paletteCondition_at_of_two_visible_matching
    (hsub : IsSubcubic G) {colour : G.edgeSet → OneTwoColor 5}
    {q : V} (hq : IsTwoVertex G q)
    (m n : G.edgeSet) (hmn : m ≠ n)
    (hm : colour m = none) (hn : colour n = none)
    (hmvis : (m : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hnvis : (n : Sym2 V) ∈ vertexVisibleEdgeFinset G q) :
    ¬ ∀ i : Fin 5, VertexSeesInduced G colour q i := by
  classical
  intro hall
  choose f hfcolour v hv hclose using fun i =>
    (vertexSeesInduced_iff G colour q i).mp (hall i)
  have hfvis (i : Fin 5) :
      (f i : Sym2 V) ∈ vertexVisibleEdgeFinset G q :=
    mem_vertexVisibleEdgeFinset_of_endpoint_close G (hv i) (hclose i)
  let witness : Option (Option (Fin 5)) →
      {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q}
    | none => ⟨m, hmvis⟩
    | some none => ⟨n, hnvis⟩
    | some (some i) => ⟨f i, hfvis i⟩
  have hinj : Function.Injective witness := by
    intro r s hrs
    cases r with
    | none =>
        cases s with
        | none => rfl
        | some s =>
            cases s with
            | none =>
                exfalso
                apply hmn
                apply Subtype.ext
                have hval := congrArg
                  (fun e : {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} =>
                    (e : Sym2 V)) hrs
                exact hval
            | some j =>
                exfalso
                have hedge : m = f j := by
                  apply Subtype.ext
                  have hval := congrArg
                    (fun e : {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} =>
                      (e : Sym2 V)) hrs
                  exact hval
                have := hm.symm.trans ((congrArg colour hedge).trans (hfcolour j))
                simp at this
    | some r =>
        cases r with
        | none =>
            cases s with
            | none =>
                exfalso
                apply hmn
                apply Subtype.ext
                have hval := congrArg
                  (fun e : {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} =>
                    (e : Sym2 V)) hrs
                exact hval.symm
            | some s =>
                cases s with
                | none => rfl
                | some j =>
                    exfalso
                    have hedge : n = f j := by
                      apply Subtype.ext
                      have hval := congrArg
                        (fun e : {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} =>
                          (e : Sym2 V)) hrs
                      exact hval
                    have := hn.symm.trans
                      ((congrArg colour hedge).trans (hfcolour j))
                    simp at this
        | some i =>
            cases s with
            | none =>
                exfalso
                have hedge : f i = m := by
                  apply Subtype.ext
                  have hval := congrArg
                    (fun e : {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} =>
                      (e : Sym2 V)) hrs
                  exact hval
                have := (hfcolour i).symm.trans
                  ((congrArg colour hedge).trans hm)
                simp at this
            | some s =>
                cases s with
                | none =>
                    exfalso
                    have hedge : f i = n := by
                      apply Subtype.ext
                      have hval := congrArg
                        (fun e : {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} =>
                          (e : Sym2 V)) hrs
                      exact hval
                    have := (hfcolour i).symm.trans
                      ((congrArg colour hedge).trans hn)
                    simp at this
                | some j =>
                    congr
                    have hedge : f i = f j := by
                      apply Subtype.ext
                      have hval := congrArg
                        (fun e : {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} =>
                          (e : Sym2 V)) hrs
                      exact hval
                    exact Option.some.inj
                      ((hfcolour i).symm.trans
                        ((congrArg colour hedge).trans (hfcolour j)))
  have hseven : 7 ≤ (vertexVisibleEdgeFinset G q).card := by
    have hcard := Fintype.card_le_of_injective witness hinj
    simpa using hcard
  have hsix := card_vertexVisibleEdgeFinset_le_six G hsub hq
  omega

/-! ## Blockers of the missing middle edge -/

theorem middleEdge_ne_leftOuter
    {u a x : V} (hua : G.Adj u a) (hax : G.Adj a x) (hux : u ≠ x) :
    (⟨s(a, x), hax⟩ : G.edgeSet) ≠
      (⟨s(u, a), hua⟩ : G.edgeSet) := by
  intro heq
  have hval : s(a, x) = s(u, a) :=
    congrArg (fun e : G.edgeSet => (e : Sym2 V)) heq
  have hxmem : x ∈ (s(u, a) : Sym2 V) := by
    rw [← hval]
    simp
  have hx : x = u ∨ x = a := by simpa using hxmem
  exact hx.elim (fun h => hux h.symm) (fun h => hax.ne h.symm)

theorem middleEdge_ne_rightOuter
    {a x z : V} (hax : G.Adj a x) (hxz : G.Adj x z) (haz : a ≠ z) :
    (⟨s(a, x), hax⟩ : G.edgeSet) ≠
      (⟨s(x, z), hxz⟩ : G.edgeSet) := by
  intro heq
  have hval : s(a, x) = s(x, z) :=
    congrArg (fun e : G.edgeSet => (e : Sym2 V)) heq
  have hamem : a ∈ (s(x, z) : Sym2 V) := by
    rw [← hval]
    simp
  have ha : a = x ∨ a = z := by simpa using hamem
  exact ha.elim hax.ne haz

theorem leftOuter_ne_rightOuter
    {u a x z : V} (hua : G.Adj u a) (hax : G.Adj a x)
    (hxz : G.Adj x z) (hux : u ≠ x) :
    (⟨s(u, a), hua⟩ : G.edgeSet) ≠
      (⟨s(x, z), hxz⟩ : G.edgeSet) := by
  intro heq
  have hval : s(u, a) = s(x, z) :=
    congrArg (fun e : G.edgeSet => (e : Sym2 V)) heq
  have hxmem : x ∈ (s(u, a) : Sym2 V) := by
    rw [hval]
    simp
  have hx : x = u ∨ x = a := by simpa using hxmem
  exact hx.elim (fun h => hux h.symm) (fun h => hax.ne h.symm)

/-- Every induced blocker of the missing middle edge is incident with one
of the two degree-three terminals.  This remains true when the terminals
coincide or when the local two-thread lies in a triangle. -/
theorem inducedBlockerEdgesOn_middle_subset_terminal_incidence
    {u a x z : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor 5} :
    inducedBlockerEdgesOn G D colour
        (⟨s(a, x), hax⟩ : G.edgeSet) ⊆
      incidentEdgeFinset G u ∪ incidentEdgeFinset G z := by
  classical
  intro f hf
  have hf' := (mem_inducedBlockerEdgesOn G D colour
    (⟨s(a, x), hax⟩ : G.edgeSet) f).mp hf
  have hfe := hf'.2.1
  have putU (huf : u ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G u ∪ incidentEdgeFinset G z := by
    exact Finset.mem_union_left _ ((mem_incidentEdgeFinset (G := G)).mpr huf)
  have putZ (hzf : z ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G u ∪ incidentEdgeFinset G z := by
    exact Finset.mem_union_right _ ((mem_incidentEdgeFinset (G := G)).mpr hzf)
  have fromA (haf : a ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G u ∪ incidentEdgeFinset G z := by
    rcases edge_eq_left_or_right_of_incident_two G ha hua.symm hax hux f haf
        with hfL | hfM
    · apply putU
      rw [hfL]
      simp
    · have heq : f = (⟨s(a, x), hax⟩ : G.edgeSet) :=
        Subtype.ext hfM
      exact False.elim (hfe heq)
  have fromX (hxf : x ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G u ∪ incidentEdgeFinset G z := by
    rcases edge_eq_left_or_right_of_incident_two G hx hax.symm hxz haz f hxf
        with hfM | hfR
    · have heq : f = (⟨s(a, x), hax⟩ : G.edgeSet) := by
        apply Subtype.ext
        simpa only [Sym2.eq_swap] using hfM
      exact False.elim (hfe heq)
    · apply putZ
      rw [hfR]
      simp
  by_cases hdisj : EndpointDisjoint G
      (⟨s(a, x), hax⟩ : G.edgeSet) f
  · have hcross : HasCrossEdge G
        (⟨s(a, x), hax⟩ : G.edgeSet) f := by
      by_contra hn
      exact hf'.2.2 ⟨hdisj, hn⟩
    obtain ⟨p, hp, q, hqf, hpq⟩ := hcross
    have hpax : p = a ∨ p = x := by simpa using hp
    rcases hpax with hpa | hpx
    · have haq : G.Adj a q := by simpa [hpa] using hpq
      have hq : q = u ∨ q = x := by
        have hqN := (G.mem_neighborFinset a q).mpr haq
        rw [neighborFinset_eq_pair_of_isTwoVertex G ha hua.symm hax hux] at hqN
        simpa using hqN
      rcases hq with hqu | hqx
      · exact putU (hqu ▸ hqf)
      · exact fromX (hqx ▸ hqf)
    · have hxq : G.Adj x q := by simpa [hpx] using hpq
      have hq : q = a ∨ q = z := by
        have hqN := (G.mem_neighborFinset x q).mpr hxq
        rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz haz] at hqN
        simpa using hqN
      rcases hq with hqa | hqz
      · exact fromA (hqa ▸ hqf)
      · exact putZ (hqz ▸ hqf)
  · have hshared : ∃ p, p ∈ (s(a, x) : Sym2 V) ∧
        p ∈ (f : Sym2 V) := by
      by_contra hn
      apply hdisj
      intro p hp hpf
      exact hn ⟨p, hp, hpf⟩
    obtain ⟨p, hp, hpf⟩ := hshared
    have hpax : p = a ∨ p = x := by simpa using hp
    exact hpax.elim (fun h => fromA (h ▸ hpf))
      (fun h => fromX (h ▸ hpf))

theorem activeInducedBlockerEdgesOn_middle_subset_terminal_incidence
    {u a x z : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor 5} :
    activeInducedBlockerEdgesOn G D colour
        (⟨s(a, x), hax⟩ : G.edgeSet) ⊆
      incidentEdgeFinset G u ∪ incidentEdgeFinset G z := by
  intro f hf
  exact inducedBlockerEdgesOn_middle_subset_terminal_incidence G ha hx hua hax
    hxz hux haz (Finset.mem_filter.mp hf).1

/-- Two distinct matching-coloured terminal-incidence edges force an
available induced colour on the missing middle edge. -/
theorem exists_available_middle_of_two_matching_terminal_edges
    {u a x z : V}
    (hu : IsThreeVertex G u) (hz : IsThreeVertex G z)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor 5)
    (m n : G.edgeSet) (hmn : m ≠ n)
    (hmS : m ∈ incidentEdgeFinset G u ∪ incidentEdgeFinset G z)
    (hnS : n ∈ incidentEdgeFinset G u ∪ incidentEdgeFinset G z)
    (hm : colour m = none) (hn : colour n = none) :
    ∃ i : Fin 5, ColorAvailableOn G D colour
      (⟨s(a, x), hax⟩ : G.edgeSet) (some i) := by
  classical
  let S := incidentEdgeFinset G u ∪ incidentEdgeFinset G z
  have hactive : activeInducedBlockerEdgesOn G D colour
      (⟨s(a, x), hax⟩ : G.edgeSet) ⊆ (S.erase m).erase n := by
    intro f hf
    have hfS : f ∈ S :=
      activeInducedBlockerEdgesOn_middle_subset_terminal_incidence G ha hx hua
        hax hxz hux haz hf
    have hfcolour := (Finset.mem_filter.mp hf).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hfS⟩⟩
    · intro hfn
      subst f
      exact hfcolour hn
    · intro hfm
      subst f
      exact hfcolour hm
  have hScard : S.card ≤ 6 := by
    dsimp [S]
    calc
      (incidentEdgeFinset G u ∪ incidentEdgeFinset G z).card ≤
          (incidentEdgeFinset G u).card +
          (incidentEdgeFinset G z).card :=
        Finset.card_union_le _ _
      _ = G.degree u + G.degree z := by rw [card_incidentEdgeFinset,
        card_incidentEdgeFinset]
      _ = 6 := by rw [hu, hz]
  have hmS' : m ∈ S := by simpa [S] using hmS
  have hnS' : n ∈ S := by simpa [S] using hnS
  have hnErase : n ∈ S.erase m := Finset.mem_erase.mpr ⟨hmn.symm, hnS'⟩
  have hcard : ((S.erase m).erase n).card < 5 := by
    rw [Finset.card_erase_of_mem hnErase, Finset.card_erase_of_mem hmS']
    omega
  apply exists_available_induced_of_card_activeBlockers_lt G D colour
  exact lt_of_le_of_lt (Finset.card_le_card hactive) hcard

/-- If the two terminals coincide, one known matching edge already leaves
at most two active terminal blockers. -/
theorem exists_available_middle_of_coincident_terminals
    {u a x : V}
    (hu : IsThreeVertex G u) (ha : IsTwoVertex G a)
    (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxu : G.Adj x u)
    (hux : u ≠ x) (hau : a ≠ u)
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor 5)
    (m : G.edgeSet) (hmS : m ∈ incidentEdgeFinset G u)
    (hm : colour m = none) :
    ∃ i : Fin 5, ColorAvailableOn G D colour
      (⟨s(a, x), hax⟩ : G.edgeSet) (some i) := by
  classical
  have hactive : activeInducedBlockerEdgesOn G D colour
      (⟨s(a, x), hax⟩ : G.edgeSet) ⊆
        (incidentEdgeFinset G u).erase m := by
    intro f hf
    have hfS : f ∈ incidentEdgeFinset G u := by
      have hfUnion :=
        activeInducedBlockerEdgesOn_middle_subset_terminal_incidence G ha hx
          hua hax hxu hux hau hf
      simpa using hfUnion
    apply Finset.mem_erase.mpr
    refine ⟨?_, hfS⟩
    intro hfm
    subst f
    exact (Finset.mem_filter.mp hf).2 hm
  have hcard : ((incidentEdgeFinset G u).erase m).card < 5 := by
    rw [Finset.card_erase_of_mem hmS, card_incidentEdgeFinset, hu]
    omega
  apply exists_available_induced_of_card_activeBlockers_lt G D colour
  exact lt_of_le_of_lt (Finset.card_le_card hactive) hcard

/-! ## A common extension lemma for the four easy outer-colour cases -/

/-- Adding the uniquely deleted middle edge back to the retained domain
recovers the whole ambient edge set. -/
theorem insert_middle_retained_deleteMiddleEdge_eq_univ
    {a x : V} (hax : G.Adj a x) :
    insert (⟨s(a, x), hax⟩ : G.edgeSet)
        (RetainedEdges (deleteMiddleEdge G hax) G) = Set.univ := by
  ext f
  simp only [Set.mem_insert_iff, Set.mem_univ, iff_true]
  by_cases hfe : f = (⟨s(a, x), hax⟩ : G.edgeSet)
  · exact Or.inl hfe
  · exact Or.inr ((mem_retained_deleteMiddleEdge_iff G hax f).mpr hfe)

/-- Only `a` and `x` can be degree-two vertices which notice a newly
matching outer edge or a newly induced-coloured middle edge.  Consequently
each such vertex has the other degree-two endpoint as a neighbour. -/
theorem exists_adjacent_two_of_middle_new_support
    {u a x z q : V}
    (hu : IsThreeVertex G u) (hz : IsThreeVertex G z)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    (hq : IsTwoVertex G q)
    (haffect :
      MatchingAffectedBy G
          ({(⟨s(u, a), hua⟩ : G.edgeSet),
            (⟨s(x, z), hxz⟩ : G.edgeSet)} : Set G.edgeSet) q ∨
        InducedAffectedBy G
          ({(⟨s(a, x), hax⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    ∃ r, G.Adj q r ∧ IsTwoVertex G r := by
  rcases haffect with hmatch | hinduced
  · obtain ⟨e, he, hqe⟩ := hmatch
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · have hq' : q = u ∨ q = a := by simpa using hqe
      rcases hq' with hqu | hqa
      · have hu' : G.degree q = 3 := by
          rw [hqu]
          exact hu
        have hq' : G.degree q = 2 := hq
        omega
      · exact ⟨x, by simpa [hqa] using hax, hx⟩
    · have hq' : q = x ∨ q = z := by simpa using hqe
      rcases hq' with hqx | hqz
      · exact ⟨a, by simpa [hqx] using hax.symm, ha⟩
      · have hz' : G.degree q = 3 := by
          rw [hqz]
          exact hz
        have hq' : G.degree q = 2 := hq
        omega
  · obtain ⟨e, he, v, hve, hqv⟩ := hinduced
    simp only [Set.mem_singleton_iff] at he
    subst e
    have hv : v = a ∨ v = x := by simpa using hve
    rcases hqv with hqv | hqv
    · subst q
      rcases hv with hva | hvx
      · exact ⟨x, by simpa [hva] using hax, hx⟩
      · exact ⟨a, by simpa [hvx] using hax.symm, ha⟩
    · rcases hv with hva | hvx
      · have hqN : q ∈ G.neighborFinset a :=
          (G.mem_neighborFinset a q).mpr (by simpa [hva] using hqv.symm)
        rw [neighborFinset_eq_pair_of_isTwoVertex G ha hua.symm hax hux] at hqN
        have hq' : q = u ∨ q = x := by simpa using hqN
        rcases hq' with hqu | hqx
        · have hu' : G.degree q = 3 := by
            rw [hqu]
            exact hu
          have hq' : G.degree q = 2 := hq
          omega
        · exact ⟨a, by simpa [hqx] using hax.symm, ha⟩
      · have hqN : q ∈ G.neighborFinset x :=
          (G.mem_neighborFinset x q).mpr (by simpa [hvx] using hqv.symm)
        rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz haz] at hqN
        have hq' : q = a ∨ q = z := by simpa using hqN
        rcases hq' with hqa | hqz
        · exact ⟨x, by simpa [hqa] using hax, hx⟩
        · have hz' : G.degree q = 3 := by
            rw [hqz]
            exact hz
          have hq' : G.degree q = 2 := hq
          omega

/-- Directional Condition-I preservation tailored to the middle-edge
extension.  The outer edges may only gain the matching colour, while the
middle edge may only gain an induced colour.  Colour removals need no
support. -/
theorem ConditionI.of_middle_new_support
    {u a x z : V}
    (hsub : IsSubcubic G)
    (hu : IsThreeVertex G u) (hz : IsThreeVertex G z)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    {old new : G.edgeSet → OneTwoColor 5}
    (hold : ConditionI G old)
    (hmatching : ∀ e, new e = none → old e = none ∨
      e = (⟨s(u, a), hua⟩ : G.edgeSet) ∨
      e = (⟨s(x, z), hxz⟩ : G.edgeSet))
    (hinduced : ∀ e i, new e = some i → old e = some i ∨
      e = (⟨s(a, x), hax⟩ : G.edgeSet)) :
    ConditionI G new := by
  apply hold.of_new_supports G
    ({(⟨s(u, a), hua⟩ : G.edgeSet),
      (⟨s(x, z), hxz⟩ : G.edgeSet)} : Set G.edgeSet)
    ({(⟨s(a, x), hax⟩ : G.edgeSet)} : Set G.edgeSet)
  · intro e he
    rcases hmatching e he with he | he | he
    · exact Or.inl he
    · exact Or.inr (by simp [he])
    · exact Or.inr (by simp [he])
  · intro e i he
    rcases hinduced e i he with he | he
    · exact Or.inl he
    · exact Or.inr (by simp [he])
  · intro q hq haffect hmatch
    obtain ⟨r, hqr, hr⟩ :=
      exists_adjacent_two_of_middle_new_support G hu hz ha hx hua hax hxz
        hux haz hq haffect
    exact paletteCondition_at_of_adjacent_two G hsub hq hqr hr hmatch

end Finite

end

end LeanCo.PackingEdgeColoring
