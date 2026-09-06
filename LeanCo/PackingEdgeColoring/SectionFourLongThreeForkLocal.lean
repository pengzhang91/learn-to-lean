import LeanCo.PackingEdgeColoring.SectionFourLongThreadPair
import LeanCo.PackingEdgeColoring.SectionThreeTwoTwoZero

/-!
# Local recolouring at a three-thread fork

This module isolates preservation facts used by the no-`(3,3,3)`
reduction.  It deliberately lives outside `SectionFourLongThreadPair` so
that the final configuration arguments can be developed independently.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Recolouring one first edge `Q` of a 3-thread at `u` to an induced
colour preserves Condition 3 when a different first edge `P` at `u`
stays matching-coloured.

Indeed, an affected 2-thread must have `u` as the affected endpoint.  Its
designated edge cannot be `P`, because the first internal vertex of the
3-thread defining `P` has degree two and does not lie on a 2-thread.  Thus
`P` is an external matching edge at that endpoint, contradicting the
premise that all external edges there are induced-coloured. -/
theorem longThreeFork_conditionThree_recolor_forkFirst_induced
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    ConditionThree G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hnewP : new P = none := by
    rw [show new P = colour P by exact recolor_ne G colour (some k) hPQ']
    simpa [P] using hP
  have hagree : ColoringsAgreeOff G ({Q} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour Q (some k)
  change ConditionThree G new
  apply hold.of_agreeOff G hagree
  intro r s₀ p hp haffect hleft hright
  rcases haffect with ⟨e, heS, hext⟩ | ⟨e, heS, hext⟩
  · have heQ : e = Q := by simpa using heS
    subst e
    have hru : r = u :=
      longPair_start_eq_three_of_external_selectedOuter G p hp g
        (by simpa [Q] using hext)
    subst r
    have hTP : threadFirstEdge G p hp ≠ P := by
      simpa [P] using
        longPair_twoThread_firstEdge_ne_threeThread_firstEdge G p hp h
    have hPext : IsExternalAt G u (threadFirstEdge G p hp) P := by
      exact ⟨by simp [P], fun heq ↦ hTP heq.symm⟩
    obtain ⟨i, hi⟩ := hleft P hPext
    rw [hnewP] at hi
    simp at hi
  · have heQ : e = Q := by simpa using heS
    subst e
    have hsu : s₀ = u :=
      longPair_end_eq_three_of_external_selectedOuter G p hp g
        (by simpa [Q] using hext)
    subst s₀
    have hTP : threadLastEdge G p hp ≠ P := by
      simpa [P] using
        longPair_twoThread_lastEdge_ne_threeThread_firstEdge G p hp h
    have hPext : IsExternalAt G u (threadLastEdge G p hp) P := by
      exact ⟨by simp [P], fun heq ↦ hTP heq.symm⟩
    obtain ⟨i, hi⟩ := hright P hPext
    rw [hnewP] at hi
    simp at hi

/-- A degree-two vertex whose palette can change when only the first edge
of a 3-thread is recoloured is either the second vertex of that thread or
is adjacent to its degree-three start. -/
theorem longThreeFork_twoVertex_paletteAffectedBy_forkFirst_cases
    {u w₁ w₂ w₃ t q : V}
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet) q) :
    q = w₂ ∨ G.Adj q u := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, heS, x, hxe, hqx⟩ := haffect
  have heQ : e = (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) := by
    simpa using heS
  subst e
  have hqne : q ≠ u := by
    intro hqu
    have hthree := g.start_three
    have htwo := hq
    unfold IsThreeVertex at hthree
    unfold IsTwoVertex at htwo
    rw [hqu] at htwo
    omega
  have hxcase : x = w₁ ∨ x = u := by simpa using hxe
  rcases hxcase with hxw₁ | hxu
  · subst x
    rcases hqx with hqw₁ | hqw₁
    · exact Or.inr (by simpa [hqw₁] using g.first_adj.symm)
    · have hqN : q ∈ G.neighborFinset w₁ :=
        (G.mem_neighborFinset w₁ q).mpr hqw₁.symm
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.left_adj g.first_adj.symm g.middle_ne_start] at hqN
      have hqcase : q = w₂ ∨ q = u := by simpa using hqN
      exact hqcase.elim Or.inl (fun hqu' ↦ False.elim (hqne hqu'))
  · subst x
    rcases hqx with hqu | hqu
    · exact False.elim (hqne hqu)
    · exact Or.inr hqu

/-- At a fork of three certified 3-threads, changing the first edge of the
middle arm to an induced colour preserves Condition 2 when the displayed
five guard edges remain matching-coloured.

The only affected degree-two vertices are `w₂` and neighbours of `u`.
The latter are exactly `v₁,w₁,x₁`; at each of them two distinct
visible matching edges give the required four-colour capacity
contradiction. -/
theorem longThreeFork_conditionTwo_recolor_forkFirst_induced
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ x₃ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ThreeThreadCore G u x₁ x₂ x₃ y)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.left_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none) :
    ConditionTwo G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.left_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ : P ≠ Q := by
    intro heq
    have hval : s(v₁, u) = s(w₁, u) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hswap
    · exact hv₁w₁ hsame.1
    · exact h.first_adj.ne hswap.1.symm
  have hCQ : C ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      g.start_three g.left_adj g.first_adj.symm
  have hSQ : S ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G r.first_two r.middle_two
      g.start_three r.left_adj g.first_adj.symm
  have hAQ : A ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      g.start_three h.left_adj g.first_adj.symm
  have hBQ : B ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      g.start_three h.right_adj.symm g.first_adj.symm
  have hCP : C ≠ P := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj h.first_adj.symm
  have hSP : S ≠ P := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G r.first_two r.middle_two
      h.start_three r.left_adj h.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hnewP : new P = none := by
    rw [show new P = colour P by exact recolor_ne G colour (some k) hPQ]
    simpa [P] using hP
  have hnewC : new C = none := by
    rw [show new C = colour C by exact recolor_ne G colour (some k) hCQ]
    simpa [C] using hC
  have hnewS : new S = none := by
    rw [show new S = colour S by exact recolor_ne G colour (some k) hSQ]
    simpa [S] using hS
  have hnewA : new A = none := by
    rw [show new A = colour A by exact recolor_ne G colour (some k) hAQ]
    simpa [A] using hA
  have hnewB : new B = none := by
    rw [show new B = colour B by exact recolor_ne G colour (some k) hBQ]
    simpa [B] using hB
  have hagree : ColoringsAgreeOff G ({Q} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour Q (some k)
  have hNu : G.neighborFinset u = {v₁, w₁, x₁} :=
    neighborFinset_eq_triple_of_isThreeVertex G h.start_three
      h.first_adj g.first_adj r.first_adj
      hv₁w₁ hv₁x₁ hw₁x₁
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases longThreeFork_twoVertex_paletteAffectedBy_forkFirst_cases G g hq
      (by simpa [Q] using haffect) with hqw₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G g.middle_two
      g.left_adj.symm g.right_adj g.first_ne_third g.first_two g.third_two
      hmatch) hall
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
        g.left_adj g.middle_two C P hCP hnewC hnewP
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [P]) (Or.inr g.first_adj.symm)
      · exact hall
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub r.first_two
        r.left_adj r.middle_two S P hSP hnewS hnewP
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [S]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [P]) (Or.inr r.first_adj.symm)
      · exact hall
end Finite

end

end LeanCo.PackingEdgeColoring
