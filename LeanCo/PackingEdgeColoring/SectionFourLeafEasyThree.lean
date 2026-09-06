import LeanCo.PackingEdgeColoring.SectionFourMinDegree
import LeanCo.PackingEdgeColoring.SectionFourLeafC3

/-!
# An easy degree-three branch in the Section 4 leaf reduction

When the two nonleaf neighbours of the degree-three vertex are not
two-vertices, the local Condition-2 obligations are vacuous.  A retained
matching edge on either branch also supplies both saturation and the
matching guard needed by the Condition-3 reduction.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A leaf whose degree-three neighbour has no two-vertex among its two
other neighbours can be restored from any good colouring of the
leaf-deleted graph, provided one of the retained branch edges is matching.
-/
theorem exists_goodFour_extension_leaf_of_three_neighbor_both_not_two
    (hsub : IsSubcubic G) {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hN : G.neighborFinset v = {u, a, b})
    (haNot : ¬ IsTwoVertex G a) (hbNot : ¬ IsTwoVertex G b)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (hAnone : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  have hAE : A ≠ E := by
    intro hEq
    have haE : a ∈ (E : Sym2 V) := by
      rw [← hEq]
      simp [A]
    have haCases : a = u ∨ a = v := by
      simpa [E] using haE
    exact haCases.elim hau (fun hav ↦ hva.ne hav.symm)
  have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hvA : v ∈ (A : Sym2 V) := by simp [A]
  have hmatchSmall :
      VertexSeesMatching (deleteLeafEdge G huv) small v := by
    rw [vertexSeesMatching_iff]
    let AH : (deleteLeafEdge G huv).edgeSet := ⟨A.1, hAD⟩
    refine ⟨AH, ?_, ?_⟩
    · have htransport : leafBaseFour G huv small A = small AH := by
        exact transportColoringToSupergraph_of_mem
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small hAD
      rw [← htransport]
      simpa only [A] using hAnone
    · simpa [AH, A] using hvA
  obtain ⟨i, havail⟩ :=
    exists_available_leafEdge_at_three_neighbor_four G hu huv hv
      small hsmall hmatchSmall
  have hbaseThree : ConditionThree G (leafBaseFour G huv small) :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hfinalThree : ConditionThree G
      (recolor G (leafBaseFour G huv small) E (some i)) := by
    exact ConditionThree.recolor_leafEdge_of_matching_otherNeighbor_not_two
      G hu huv hva hau haNot (leafBaseFour G huv small) i
        (by simpa only [A] using hAnone) hbaseThree
  refine ⟨recolor G (leafBaseFour G huv small) E (some i), ?_⟩
  apply goodFour_recolor_leafEdge_of_local G hsub hu huv hv hva hvb hN
    small hsmall A hAD (by simpa only [A] using hAnone) hvA i
    (by simpa only [E] using havail)
  · intro ha
    exact False.elim (haNot ha)
  · intro hb
    exact False.elim (hbNot hb)
  · intro r t p hp _hr hleft hright
    exact hfinalThree r t p hp hleft hright
  · intro r t p hp _ht hleft hright
    exact hfinalThree r t p hp hleft hright

end Finite

end

end LeanCo.PackingEdgeColoring
