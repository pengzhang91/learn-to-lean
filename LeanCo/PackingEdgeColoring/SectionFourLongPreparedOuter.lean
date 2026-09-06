import LeanCo.PackingEdgeColoring.SectionFourLongThreadPair

/-!
# Generic completion of a prepared three-thread gap

This module packages the second half of the neighbour-arm swap: once the
selected left outer edge is induced, a matching guard remains at its
degree-three endpoint, and the right outer edge is matching, the two gap
edges can be restored.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Complete a prepared 3-thread gap after a neighbour-arm recolouring has
made the selected left outer edge induced.  The explicit `mL` hypothesis is
the matching guard left at the degree-three start (in applications it is
the first edge of the swapped neighbouring arm). -/
theorem longPair_hasGoodFour_of_prepared_left_outer_induced
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (base : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h base)
    (hP : base (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠ none)
    (hR : base (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hA : base (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : base (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (mL : G.edgeSet) (hmL : base mL = none) (humL : u ∈ (mL : Sym2 V))
    (hmLA : mL ≠ (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet))
    (hmLB : mL ≠ (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hRD : R ∈ Dset := by
    change R ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [R, h.right_adj.ne, h.middle_ne_end]
  have hAR : A ≠ R := fun heq ↦ hAD (heq ▸ hRD)
  have hBR : B ≠ R := fun heq ↦ hBD (heq ▸ hRD)
  have hmLA' : mL ≠ A := by simpa [A] using hmLA
  have hmLB' : mL ≠ B := by simpa [B] using hmLB
  have havailA : ColorAvailableOn G Dset base A none := by
    exact matching_available_left_gap_of_outer_nonmatching G h base
      (by simpa [P] using hP)
  let afterA : G.edgeSet → OneTwoColor 4 := recolor G base A none
  have hafterAOn : IsOneTwoColoringOn G (insert A Dset) afterA :=
    hprepared.1.extend_one G hAD havailA
  have hafterAA : afterA A = none := by simp [afterA]
  have hafterAR : afterA R = none := by
    rw [show afterA R = base R by exact recolor_ne G base none hAR.symm]
    simpa [R] using hR
  obtain ⟨b, hb⟩ := exists_available_right_gap_after_left_matching G h
    afterA (by simpa [A] using hafterAA) R
      (by simpa [R] using hafterAR) (by simp [R])
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterA B (some b)
  have hBfresh : B ∉ insert A Dset := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨hAB.symm, hBD⟩
  have hfinalOn : IsOneTwoColoringOn G (insert B (insert A Dset)) final :=
    hafterAOn.extend_one G hBfresh hb
  have hvalid : IsOneTwoColoring G final := by
    simpa [IsOneTwoColoring, Dset, A, B,
      insert_threeThread_gap_retained_eq_univ G h] using hfinalOn
  have hagree : ColoringsAgreeOff G ({A, B} : Set G.edgeSet) base final := by
    intro e he
    have hne : e ≠ A ∧ e ≠ B := by simpa using he
    simp [final, afterA, hne.1, hne.2]
  have hfinalA : final A = none := by simp [final, afterA, hAB]
  have hfinalB : final B = some b := by simp [final]
  have hfinalR : final R = none := by
    simp [final, afterA, hAR.symm, hBR.symm, R, hR]
  have hfinalML : final mL = none := by
    simp [final, afterA, hmLA', hmLB', hmL]
  have hsaturated : OneSaturated G final := by
    intro e he
    by_cases heA : e = A
    · subst e
      exact False.elim (he hfinalA)
    by_cases heB : e = B
    · subst e
      exact ⟨A, hfinalA, v₂, by simp [B], by simp [A]⟩
    have heBase : base e ≠ none := by
      intro heNone
      apply he
      exact (hagree e (by simpa [heA, heB])).symm.trans heNone
    obtain ⟨f, hf, y, hye, hyf⟩ := hprepared.2.1 e heBase
    by_cases hfB : f = B
    · subst f
      have hycase : y = v₃ ∨ y = v₂ := by simpa [B] using hyf
      rcases hycase with hyv₃ | hyv₂
      · exact ⟨R, hfinalR, y, hye, by simpa [R, hyv₃]⟩
      · exact ⟨A, hfinalA, y, hye, by simpa [A, hyv₂]⟩
    · by_cases hfA : f = A
      · subst f
        exact ⟨A, hfinalA, y, hye, hyf⟩
      · refine ⟨f, ?_, y, hye, hyf⟩
        exact (hagree f (by simpa [hfA, hfB])).symm.trans hf
  have hpalette : ∀ q : V, q = v₁ ∨ q = v₂ ∨ q = v₃ →
      VertexSeesMatching G final q →
      ¬ ∀ i : Fin 4, VertexSeesInduced G final q i := by
    intro q hqcase hmatch hall
    rcases hqcase with rfl | rfl | rfl
    · apply longPair_paletteCondition_at_two_visible_matching G hsub
        h.first_two h.left_adj h.middle_two A mL hmLA'.symm
        hfinalA hfinalML
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G humL
          (Or.inr h.first_adj.symm)
      · exact hall
    · exact (longPair_paletteCondition_at_two_two_neighbours G
        h.middle_two h.left_adj.symm h.right_adj h.first_ne_third
        h.first_two h.third_two hmatch) hall
    · apply longPair_paletteCondition_at_two_visible_matching G hsub
        h.third_two h.right_adj.symm h.middle_two A R hAR hfinalA hfinalR
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inr h.right_adj.symm)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [R]) (Or.inl rfl)
      · exact hall
  have hgood : GoodFour G final :=
    longPair_goodFour_of_preparedThreeThreadGap_recolour G h base final
      hprepared hvalid hsaturated (by simpa [A, B] using hagree) hpalette
  let d : DecidableRel G.Adj := inferInstance
  rw [HasGoodFour]
  exact ⟨final, goodFour_change_decidableRel d (Classical.decRel _) final hgood⟩

end Finite

end

end LeanCo.PackingEdgeColoring
