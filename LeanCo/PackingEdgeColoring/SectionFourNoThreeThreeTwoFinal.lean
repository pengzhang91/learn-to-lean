import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeTwo
import LeanCo.PackingEdgeColoring.SectionFourLongTwoThreadClaim
import LeanCo.PackingEdgeColoring.SectionFourLongPreparedOuter

/-!
# Closing the no332 configuration

The ordinary Claim-1 swap has one possible Condition-3 obstruction, on
the displayed two-thread itself.  We break it by using the fourth colour
on the selected outer edge and making the two-thread first edge matching.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Condition 2 for the alternate fresh swap.  The other 3-thread supplies
the extra matching guard at its first degree-two vertex, so every affected
vertex has two visible matching edges. -/
theorem longPair_conditionTwo_selectedFresh_twoThreadFirstMatching
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (hsat : OneSaturated G colour)
    (d j : Fin 4)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hUP : (⟨s(x₂, y), r.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let U : G.edgeSet := ⟨s(x₂, y), r.last_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) T none
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  have hTP : T ≠ P := hPT.symm
  have hUT : U ≠ T := by
    simpa [U, T] using (twoThreadCore_firstEdge_ne_lastEdge G r).symm
  have hUP' : U ≠ P := by simpa [U, P] using hUP
  have hAP : A ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      h.start_three h.left_adj h.first_adj.symm
  have hAT : A ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      h.start_three h.left_adj r.first_adj.symm
  have hBP : B ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      h.start_three h.right_adj.symm h.first_adj.symm
  have hBT : B ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      h.start_three h.right_adj.symm r.first_adj.symm
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj h.first_adj.symm
  have hCT : C ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj r.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hTU : T ≠ U := hUT.symm
  have hTne : colour T ≠ none := by
    rw [hT]
    simp
  have hU : colour U = none := by
    exact longPair_twoThread_last_matching_of_first_two_induced G r colour hsat
      (by simpa [T] using hTne)
      (by simpa using hS)
  have hnewT : new T = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBT, B, hB]
  have hnewC : new C = none := by simp [new, hCP, hCT, C, hC]
  have hnewU : new U = none := by simp [new, hUP', hUT, U, hU]
  have hagree : ColoringsAgreeOff G ({P, T} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ T := by simpa using he
    simp [new, hne.1, hne.2]
  have hNu : G.neighborFinset u = {v₁, w₁, x₁} :=
    neighborFinset_eq_triple_of_isThreeVertex G h.start_three
      h.first_adj g.first_adj r.first_adj hvw hvx hwx
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases longPair_twoVertex_paletteAffectedBy_twoThreadFirst_swap_cases
      G h r hq (by simpa [P, T] using haffect) with hqv₂ | hqx₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub r.second_two
      r.middle_adj.symm r.first_two T U hTU hnewT hnewU
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [T]) (Or.inr r.middle_adj.symm)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [U]) (Or.inl rfl)
    · exact hall
  · have hqmem : q ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u q).mpr hqu.symm
    rw [hNu] at hqmem
    have hqcases : q = v₁ ∨ q = w₁ ∨ q = x₁ := by simpa using hqmem
    rcases hqcases with hqv₁ | hqw₁ | hqx₁
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub h.first_two
        h.left_adj h.middle_two A B hAB hnewA hnewB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [B]) (Or.inr h.left_adj)
      · exact hall
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub g.first_two
        g.left_adj g.middle_two C T hCT hnewC hnewT
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [T]) (Or.inr g.first_adj.symm)
      · exact hall
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub r.first_two
        r.middle_adj r.second_two T U hTU hnewT hnewU
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [T]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [U]) (Or.inr r.middle_adj)
      · exact hall

end Finite

end

end LeanCo.PackingEdgeColoring
