import LeanCo.PackingEdgeColoring.LeafDeletion

/-!
# The Section 3 minimum-degree reduction

This module connects leaf-edge deletion to the edge-minimal-counterexample
framework.  It first isolates the exact hard branch of Lemma 3.3: in every
good colouring of the deleted graph, the nonleaf endpoint must already be
incident with a retained matching-coloured edge.  Otherwise the leaf edge
can be restored with the matching colour and the counterexample disappears.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Subcubicity is independent of the chosen decision procedure for
adjacency. -/
theorem isSubcubic_change_decidableRel
    (d₁ d₂ : DecidableRel G.Adj)
    (h : @IsSubcubic V G _ d₁) : @IsSubcubic V G _ d₂ := by
  intro z
  have hzCard : Nat.card (G.neighborSet z) ≤ 3 := by
    letI : DecidableRel G.Adj := d₁
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
    exact h z
  letI : DecidableRel G.Adj := d₂
  rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  exact hzCard

/-- Deleting an actual edge preserves Section 3 eligibility. -/
theorem sectionThreeEligible_deleteEdge
    (hEligible : SectionThreeEligible G) (e : G.edgeSet) :
    SectionThreeEligible (G.deleteEdges ({e.1} : Set (Sym2 V))) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : DecidableRel (G.deleteEdges ({e.1} : Set (Sym2 V))).Adj :=
    Classical.decRel (G.deleteEdges ({e.1} : Set (Sym2 V))).Adj
  rw [SectionThreeEligible] at hEligible ⊢
  constructor
  · intro z
    exact ((G.deleteEdges ({e.1} : Set (Sym2 V))).degree_le_of_le
      (G.deleteEdges_le ({e.1} : Set (Sym2 V)))).trans (hEligible.1 z)
  · exact MaximumAverageDegreeLT.mono
      (G.deleteEdges_le ({e.1} : Set (Sym2 V))) hEligible.2

/-- The exact residual branch after the easy matching-colour extension.
For a leaf in an edge-minimal bad graph, minimality supplies a good colouring
of the leaf-deleted graph, and that colouring necessarily has a retained
matching edge at the nonleaf endpoint. -/
theorem IsEdgeMinimalBad.exists_deleteLeaf_goodFive_and_matching_at_neighbor
    (hmin : IsEdgeMinimalBad SectionThreeEligible HasGoodFive G)
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v) :
    ∃ small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5,
      GoodFive (deleteLeafEdge G huv) small ∧
      ∃ f : G.edgeSet,
        f ∈ RetainedEdges (deleteLeafEdge G huv) G ∧
        transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small f = none ∧
        v ∈ (f : Sym2 V) := by
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  have hEligibleDelete :
      SectionThreeEligible (G.deleteEdges ({e.1} : Set (Sym2 V))) :=
    sectionThreeEligible_deleteEdge G hmin.eligible e
  have hgoodDelete :
      HasGoodFive (G.deleteEdges ({e.1} : Set (Sym2 V))) :=
    hmin.good_deleteEdge e hEligibleDelete
  rw [HasGoodFive] at hgoodDelete
  obtain ⟨small, hsmallClassical⟩ := hgoodDelete
  have hsmall : GoodFive (deleteLeafEdge G huv) small := by
    apply goodFive_change_decidableRel
      (G := deleteLeafEdge G huv)
      (Classical.decRel (deleteLeafEdge G huv).Adj)
      inferInstance small
    simpa [e, deleteLeafEdge] using hsmallClassical
  refine ⟨small, hsmall, ?_⟩
  by_contra hnone
  push_neg at hnone
  have hnoMatch : ∀ f : G.edgeSet,
      f ∈ RetainedEdges (deleteLeafEdge G huv) G →
      v ∈ (f : Sym2 V) →
      transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small f ≠ none := by
    intro f hfD hvf hcolour
    exact hnone f hfD hcolour hvf
  have havail := matching_available_leafEdge_of_no_matching_at_neighbor
    G hu huv small hnoMatch
  have hsubCurrent : IsSubcubic G :=
    isSubcubic_change_decidableRel G
      (Classical.decRel G.Adj) inferInstance hmin.eligible.1
  have hgoodG := goodFive_of_leaf_matching_available
    G hsubCurrent hu huv small hsmall havail
  apply hmin.not_good
  rw [HasGoodFive]
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
  refine ⟨base, ?_⟩
  apply goodFive_change_decidableRel
    (G := G) inferInstance (Classical.decRel G.Adj) base
  simpa [base] using hgoodG

/-- The first full structural consequence of the leaf reduction: in a
minimal Section 3 counterexample, every leaf is adjacent to a three-vertex.
The degree-one and degree-two alternatives are both discharged, including
Condition I in the degree-two extension. -/
theorem IsEdgeMinimalBad.leaf_neighbor_isThreeVertex_sectionThree
    (hmin : IsEdgeMinimalBad SectionThreeEligible HasGoodFive G)
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v) :
    IsThreeVertex G v := by
  obtain ⟨small, hsmall, f, hfD, hfnone, hvf⟩ :=
    hmin.exists_deleteLeaf_goodFive_and_matching_at_neighbor G hu huv
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
  have hmatch : VertexSeesMatching G base v := by
    rw [vertexSeesMatching_iff]
    exact ⟨f, by simpa [base] using hfnone, hvf⟩
  have hsub : IsSubcubic G :=
    isSubcubic_change_decidableRel G
      (Classical.decRel G.Adj) inferInstance hmin.eligible.1
  have hvpos : 0 < G.degree v := by
    rw [G.degree_pos_iff_exists_adj v]
    exact ⟨u, huv.symm⟩
  have hvle : G.degree v ≤ 3 := hsub v
  unfold IsThreeVertex
  by_contra hvne
  have hvCases : G.degree v = 1 ∨ G.degree v = 2 := by omega
  rcases hvCases with hvOne | hvTwo
  · have hfe : f = (⟨s(u, v), huv⟩ : G.edgeSet) := by
      have hfv := edge_eq_of_incident_degree_eq_one G hvOne huv.symm f hvf
      apply Subtype.ext
      simpa only [Sym2.eq_swap] using congrArg Subtype.val hfv
    exact ((mem_retained_deleteLeafEdge_iff G huv f).mp hfD) hfe
  · obtain ⟨i, hgoodG⟩ := exists_goodFive_extension_leaf_of_two_neighbor
      G hsub hu huv hvTwo small hsmall (by simpa [base] using hmatch)
    apply hmin.not_good
    rw [HasGoodFive]
    let colour : G.edgeSet → OneTwoColor 5 :=
      recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)
    refine ⟨colour, ?_⟩
    apply goodFive_change_decidableRel
      (G := G) inferInstance (Classical.decRel G.Adj) colour
    simpa [colour, base] using hgoodG

end Finite

end

end LeanCo.PackingEdgeColoring
