import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeZero
import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeOne
import LeanCo.PackingEdgeColoring.SectionFourLongTwoThreadSecondMatching
import LeanCo.PackingEdgeColoring.SectionFourLongMinimal
import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoTwo
import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoZeroShift

/-!
# The `(3,2,0)` reduction for Section 4

This module treats a three-thread and a two-thread at a common degree-three
vertex whose remaining incident edge is a zero-thread.  It deliberately lives
apart from the `(3,3,0)` development: only the local zero-thread lemmas are
reused from there.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The middle edge of a certified 2-thread, with the orientation used by
`TwoThreadCoreData`. -/
abbrev no320ThreadMiddleEdge {u t : V} (q : G.Walk u t)
    (hq : IsKThread G q 2) : G.edgeSet :=
  ⟨s(q.getVert 1, q.getVert 2), (hq.twoThreadCoreData G).middle_adj⟩

/-- Condition 2 for the selected-edge/zero-thread swap when the other arm is
a two-thread.  Its matching middle edge supplies the witness at the first
degree-two vertex of that arm. -/
theorem longPair_conditionTwo_swap_selectedOuter_zeroThread_twoThread
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (hsat : OneSaturated G colour)
    (j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) ≠ none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hguard : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none ∨
      colour (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) = none)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPT : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet))
    (hEP : (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some j))
        (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) none) := by
  classical
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let E : G.edgeSet := ⟨s(w₂, t), g.last_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some j)) T none
  have hPT' : P ≠ T := by simpa [P, T] using hPT
  have hPD : P ∈ D := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hTD' : T ∈ D := by simpa [D, T] using hTD
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ D := by
    simpa [D, B] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD')
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD)
  have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ hTD')
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj h.first_adj.symm
  have hCT : C ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      r.start_three g.middle_adj r.adj.symm
  have hET : E ≠ T := by
    intro heq
    have hval : s(w₂, t) = s(x, u) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact (isThreeVertex_ne_isTwoVertex G r.end_three g.second_two)
        hval.1.symm
    · exact (isThreeVertex_ne_isTwoVertex G r.start_three g.second_two)
        hval.1.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hnewP : new P = some j := by simp [new, hPT']
  have hnewT : new T = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBT, B, hB]
  have hnewGuard : new C = none ∨ new E = none := by
    rcases hguard with hC | hE
    · exact Or.inl (by simp [new, hCP, hCT, C, hC])
    · exact Or.inr (by simp [new, hEP, hET, E, P, hE])
  have hnewOff (e : G.edgeSet) (heP : e ≠ P) (heT : e ≠ T) :
      new e = colour e := by simp [new, heP, heT]
  have hagree : ColoringsAgreeOff G ({P, T} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ T := by simpa using he
    exact (hnewOff e hne.1 hne.2).symm
  have hNu : G.neighborFinset u = {v₁, w₁, x} :=
    longPair_neighborFinset_eq_three G h.start_three h.first_adj
      g.first_adj r.adj hv₁w₁ hv₁x hw₁x
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases longPair_twoVertex_paletteAffectedBy_zeroSwap_cases G h r hq
      (by simpa [P, T] using haffect) with hqv₂ | hqu | hqx
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  · have hqN : q ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u q).mpr hqu.symm
    rw [hNu] at hqN
    have hqcase : q = v₁ ∨ q = w₁ ∨ q = x := by simpa using hqN
    rcases hqcase with hqv₁ | hqw₁ | hqxEq
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub h.first_two
        h.left_adj h.middle_two A B hAB hnewA hnewB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [B]) (Or.inr h.left_adj)
      · exact hall
    · subst q
      rcases hnewGuard with hnewC | hnewE
      · apply longPair_paletteCondition_at_two_visible_matching G hsub g.first_two
          g.middle_adj g.second_two C T hCT hnewC hnewT
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
            (by simp [C]) (Or.inl rfl)
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
            (by simp [T]) (Or.inr g.first_adj.symm)
        · exact hall
      · apply longPair_paletteCondition_at_two_visible_matching G hsub g.first_two
          g.middle_adj g.second_two E T hET hnewE hnewT
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
            (by simp [E]) (Or.inr g.middle_adj)
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
            (by simp [T]) (Or.inr g.first_adj.symm)
        · exact hall
    · subst q
      exact False.elim ((isThreeVertex_ne_isTwoVertex G r.end_three hq) rfl)
  · have hqN : q ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x q).mpr hqx.symm
    rw [hNfar] at hqN
    have hqcase : q = u ∨ q = a ∨ q = b := by simpa using hqN
    rcases hqcase with hquEq | hqa | hqb
    · subst q
      exact False.elim ((isThreeVertex_ne_isTwoVertex G r.start_three hq) rfl)
    · subst q
      obtain ⟨m, hm, ham⟩ :=
        exists_matching_incident_zero_far_neighbor_of_all_induced G r ha hb
          hNfar colour hsat (by simp [hT]) hU hV
      have hmatchOld : VertexSeesMatching G colour a :=
        (vertexSeesMatching_iff G colour a).mpr ⟨m, hm, ham⟩
      apply hold a hq hmatchOld
      intro k
      by_cases hkj : k = j
      · subst k
        apply (vertexSeesInduced_iff G colour a j).mpr
        exact ⟨T, by simpa [T] using hT, x, by simp [T], Or.inr ha.symm⟩
      · obtain ⟨e, he, y, hye, hclose⟩ :=
          (vertexSeesInduced_iff G new a k).mp (hall k)
        have heP : e ≠ P := by
          intro hEq
          subst e
          have hjk : j = k := Option.some.inj (hnewP.symm.trans he)
          exact hkj hjk.symm
        have heT : e ≠ T := by
          intro hEq
          subst e
          have hfalse : none = some k := hnewT.symm.trans he
          simp at hfalse
        exact (vertexSeesInduced_iff G colour a k).mpr
          ⟨e, by simpa [hnewOff e heP heT] using he, y, hye, hclose⟩
    · subst q
      have hNfar' : G.neighborFinset x = {u, b, a} := by
        simpa [Finset.pair_comm] using hNfar
      obtain ⟨m, hm, hbm⟩ :=
        exists_matching_incident_zero_far_neighbor_of_all_induced G r hb ha
          hNfar' colour hsat (by simp [hT]) hV hU
      have hmatchOld : VertexSeesMatching G colour b :=
        (vertexSeesMatching_iff G colour b).mpr ⟨m, hm, hbm⟩
      apply hold b hq hmatchOld
      intro k
      by_cases hkj : k = j
      · subst k
        apply (vertexSeesInduced_iff G colour b j).mpr
        exact ⟨T, by simpa [T] using hT, x, by simp [T], Or.inr hb.symm⟩
      · obtain ⟨e, he, y, hye, hclose⟩ :=
          (vertexSeesInduced_iff G new b k).mp (hall k)
        have heP : e ≠ P := by
          intro hEq
          subst e
          have hjk : j = k := Option.some.inj (hnewP.symm.trans he)
          exact hkj hjk.symm
        have heT : e ≠ T := by
          intro hEq
          subst e
          have hfalse : none = some k := hnewT.symm.trans he
          simp at hfalse
        exact (vertexSeesInduced_iff G colour b k).mpr
          ⟨e, by simpa [hnewOff e heP heT] using he, y, hye, hclose⟩

/-- Prepared-gap preservation for the zero-thread swap in the `(3,2,0)`
configuration, assuming the middle edge of the two-thread is matching. -/
theorem longPair_prepared_swap_selectedOuter_zeroThread_twoThread
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) ≠ none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hguard : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none ∨
      colour (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) = none)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPT : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet))
    (hEP : (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    PreparedThreeThreadGap G h
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some j))
        (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) none) := by
  refine ⟨
    longPair_validOn_swap_selectedOuter_zeroThread G h r ha hb hNfar colour
      hprepared.1 j hP hT hU hV hTD hPT,
    longPair_oneSaturated_swap_selectedOuter_zeroThread G h r colour
      hprepared.2.1 j hT hA hTD hPT,
    longPair_conditionTwo_swap_selectedOuter_zeroThread_twoThread G hsub h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour hprepared.2.2.1
      hprepared.2.1 j hP hT hU hV hA hB hguard hTD hPT hEP,
    longPair_conditionThree_swap_selectedOuter_zeroThread G h r colour
      hprepared.2.2.2 j hPT⟩

/-- The all-induced far-end branch of the `(3,2,0)` hard case. -/
theorem longPair_hasGoodFour_of_zeroThread_twoThread_far_both_induced
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) ≠ none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hguard : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none ∨
      colour (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) = none)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPT : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet))
    (hEP : (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    HasGoodFour G := by
  classical
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some j)
  let new : G.edgeSet → OneTwoColor 4 := recolor G afterP T none
  have hPT' : P ≠ T := by simpa [P, T] using hPT
  have hPD : P ∈ D := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hTD' : T ∈ D := by simpa [D, T] using hTD
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ D := by
    simpa [D, B] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD')
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD)
  have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ hTD')
  have hRP : R ≠ P := by
    intro heq
    have hval : s(v₃, z) = s(v₁, u) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hswap
    · exact h.first_ne_third hsame.1.symm
    · exact (isThreeVertex_ne_isTwoVertex G h.start_three h.third_two)
        hswap.1.symm
  have hRT : R ≠ T := by
    intro heq
    have hc := congrArg colour heq
    rw [show colour R = none by simpa [R] using hR,
      show colour T = some j by simpa [T] using hT] at hc
    simp at hc
  have hpreparedNew : PreparedThreeThreadGap G h new := by
    exact longPair_prepared_swap_selectedOuter_zeroThread_twoThread G hsub h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour hprepared j hP hT hU hV
      hA hB hguard hTD hPT hEP
  have hnewP : new P = some j := by simp [new, afterP, hPT']
  have hnewT : new T = none := by simp [new]
  have hnewR : new R = none := by simp [new, afterP, hRP, hRT, R, hR]
  have hnewA : new A = none := by simp [new, afterP, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, afterP, hBP, hBT, B, hB]
  exact longPair_hasGoodFour_of_prepared_left_outer_induced G hsub h new
    hpreparedNew (by change new P ≠ none; simp [hnewP]) hnewR hnewA hnewB
    T hnewT (by simp [T]) hAT.symm hBT.symm

/-! ## Recolouring the first edge of the two-thread -/

/-- Forget the last edge of a two-thread. -/
theorem TwoThreadCoreData.forkTwoStep
    {u w₁ w₂ t : V} (g : TwoThreadCoreData G u w₁ w₂ t) :
    ForkTwoStepCore G u w₁ w₂ :=
  ⟨g.first_two, g.second_two, g.first_adj, g.middle_adj, g.second_ne_start⟩

/-- Saturation is unchanged when an induced colour on the first edge of a
two-thread is replaced by another induced colour and its middle edge is
matching. -/
theorem longPair_oneSaturated_recolor_twoThreadFirst_induced
    {u w₁ w₂ t : V}
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : OneSaturated G colour)
    (i k : Fin 4)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none) :
    OneSaturated G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  classical
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hCQ : C ≠ Q := by
    intro heq
    have hv : s(w₁, w₂) = s(w₁, u) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hv
    rcases hv with hv | hv
    · exact g.second_ne_start hv.2
    · exact g.first_adj.ne hv.1.symm
  have hnewQ : new Q = some k := by simp [new]
  have hnewC : new C = none := by
    rw [show new C = colour C by exact recolor_ne G colour (some k) hCQ]
    simpa [C] using hC
  change OneSaturated G new
  intro e he
  by_cases heQ : e = Q
  · subst e
    exact ⟨C, hnewC, w₁, by simp [Q], by simp [C]⟩
  · have heOld : colour e ≠ none := by
      intro heNone
      apply he
      rw [show new e = colour e by exact recolor_ne G colour (some k) heQ]
      exact heNone
    obtain ⟨f, hf, y, hye, hyf⟩ := hold e heOld
    have hfQ : f ≠ Q := by
      intro hfEq
      subst f
      have hQnone : colour Q = none := hf
      have hQsome : colour Q = some i := by simpa [Q] using hQ
      have hfalse : none = some i := hQnone.symm.trans hQsome
      simp at hfalse
    refine ⟨f, ?_, y, hye, hyf⟩
    rw [show new f = colour f by exact recolor_ne G colour (some k) hfQ]
    exact hf

/-- A degree-two vertex affected by recolouring the first edge of a
two-thread is its second internal vertex or is adjacent to the start. -/
theorem longPair_twoVertex_paletteAffectedBy_twoThreadFirst_cases
    {u w₁ w₂ t q : V}
    (g : TwoThreadCoreData G u w₁ w₂ t) (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = w₂ ∨ G.Adj q u := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, heS, y, hye, hqy⟩ := haffect
  have heQ : e = (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) := by
    simpa using heS
  subst e
  have hqne : q ≠ u :=
    (isThreeVertex_ne_isTwoVertex G g.start_three hq).symm
  have hycase : y = w₁ ∨ y = u := by simpa using hye
  rcases hycase with hyw₁ | hyu
  · subst y
    rcases hqy with hqw₁ | hqw₁
    · exact Or.inr (by simpa [hqw₁] using g.first_adj.symm)
    · have hqN : q ∈ G.neighborFinset w₁ :=
        (G.mem_neighborFinset w₁ q).mpr hqw₁.symm
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start] at hqN
      have hqcase : q = w₂ ∨ q = u := by simpa using hqN
      exact hqcase.elim Or.inl (fun hqu' ↦ False.elim (hqne hqu'))
  · subst y
    rcases hqy with hqu | hqu
    · exact False.elim (hqne hqu)
    · exact Or.inr hqu

/-- Condition 3 is protected by the selected matching outer edge while the
first edge of the two-thread is recoloured induced. -/
theorem longPair_conditionThree_recolor_twoThreadFirst_induced
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (k : Fin 4)
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
  have hnewP : new P = none := by simp [new, hPQ', P, hP]
  have hagree : ColoringsAgreeOff G ({Q} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour Q (some k)
  change ConditionThree G new
  apply hold.of_agreeOff G hagree
  intro a b p hp haffect hleft hright
  rcases haffect with ⟨e, heS, hext⟩ | ⟨e, heS, hext⟩
  · have heQ : e = Q := by simpa using heS
    subst e
    have hau : a = u := by
      have hamem : a = w₁ ∨ a = u := by simpa [Q] using hext.1
      rcases hamem with haw₁ | hau
      · exact False.elim
          ((isThreeVertex_ne_isTwoVertex G hp.start_three g.first_two) haw₁)
      · exact hau
    subst a
    have hTP : threadFirstEdge G p hp ≠ P := by
      simpa [P] using longPair_twoThread_firstEdge_ne_threeThread_firstEdge G p hp h
    obtain ⟨i, hi⟩ := hleft P ⟨by simp [P], fun heq ↦ hTP heq.symm⟩
    rw [hnewP] at hi
    simp at hi
  · have heQ : e = Q := by simpa using heS
    subst e
    have hbu : b = u := by
      have hbmem : b = w₁ ∨ b = u := by simpa [Q] using hext.1
      rcases hbmem with hbw₁ | hbu
      · exact False.elim
          ((isThreeVertex_ne_isTwoVertex G hp.end_three g.first_two) hbw₁)
      · exact hbu
    subst b
    have hTP : threadLastEdge G p hp ≠ P := by
      simpa [P] using longPair_twoThread_lastEdge_ne_threeThread_firstEdge G p hp h
    obtain ⟨i, hi⟩ := hright P ⟨by simp [P], fun heq ↦ hTP heq.symm⟩
    rw [hnewP] at hi
    simp at hi

/-- A colour absent from the centre palette, the induced far zero-thread
edge, and the last edge of the two-thread is available on its first edge. -/
theorem longPair_twoThreadFirst_fresh_available_zeroThird
    {u v₁ v₂ v₃ z w₁ w₂ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hVk : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ some k)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDk : colour (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) ≠ some k)
    (hretained : ∀ f : G.edgeSet, f ∈ Dset → v₂ ∉ (f : Sym2 V)) :
    ColorAvailableOn G Dset colour
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, t), g.last_adj⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let W : G.edgeSet := ⟨s(x, b), hb⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hC' : colour C = none := by simpa [C] using hC
  have hU' : colour U = none := by simpa [U] using hU
  have hWk : colour W ≠ some k := by simpa [W] using hVk
  have hDk' : colour D ≠ some k := by simpa [D] using hDk
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hv₁x
  have noAtU (f : G.edgeSet) (hfQ : f ≠ Q)
      (huf : u ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    obtain ⟨c, hfc⟩ := Sym2.mem_iff_exists.mp huf
    have huc : G.Adj u c := by
      have hadj := f.2
      rw [hfc] at hadj
      simpa using hadj
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.adj hv₁w₁ hv₁x hw₁x huc with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfc)
      have hfalse : none = some k := hP'.symm.trans (by simpa [hfP] using hcf)
      simp at hfalse
    · exact hfQ (Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfc))
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfc)
      apply hk
      exact ⟨T, ⟨by simp [T], hPT.symm⟩, by simpa [hfT] using hcf⟩
  have noAtV₁ (f : G.edgeSet) (hfD : f ∈ Dset)
      (hvf : v₁ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start f hvf with hfA | hfP
    · have hfA' : f = A := Subtype.ext (by simpa [A] using hfA)
      exact hretained f hfD (by simpa [hfA', A])
    · have hfP' : f = P := Subtype.ext (by simpa [P] using hfP)
      have hfalse : none = some k := hP'.symm.trans (by simpa [hfP'] using hcf)
      simp at hfalse
  have noAtW₁ (f : G.edgeSet) (hfQ : f ≠ Q)
      (hwf : w₁ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start f hwf with hfC | hfQ'
    · have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
      have hfalse : none = some k := hC'.symm.trans (by simpa [hfC'] using hcf)
      simp at hfalse
    · exact hfQ (Subtype.ext (by simpa [Q] using hfQ'))
  have noAtX (f : G.edgeSet)
      (hxf : x ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    obtain ⟨c, hfc⟩ := Sym2.mem_iff_exists.mp hxf
    have hxc : G.Adj x c := by
      have hadj := f.2
      rw [hfc] at hadj
      simpa using hadj
    have hcN : c ∈ G.neighborFinset x := (G.mem_neighborFinset x c).mpr hxc
    rw [hNfar] at hcN
    have hccase : c = u ∨ c = a ∨ c = b := by simpa using hcN
    rcases hccase with rfl | rfl | rfl
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfc)
      apply hk
      exact ⟨T, ⟨by simp [T], hPT.symm⟩, by simpa [hfT] using hcf⟩
    · have hfU : f = U := Subtype.ext (by simpa [U, Sym2.eq_swap] using hfc)
      have hfalse : none = some k := hU'.symm.trans (by simpa [hfU] using hcf)
      simp at hfalse
    · have hfW : f = W := Subtype.ext (by simpa [W, Sym2.eq_swap] using hfc)
      exact hWk (by simpa [hfW] using hcf)
  have noAtW₂ (f : G.edgeSet)
      (hwf : w₂ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end f hwf with hfC | hfD
    · have hfC' : f = C := Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC)
      have hfalse : none = some k := hC'.symm.trans (by simpa [hfC'] using hcf)
      simp at hfalse
    · have hfD' : f = D := Subtype.ext (by simpa [D] using hfD)
      exact hDk' (by simpa [hfD'] using hcf)
  apply (colorAvailableOn_some_iff G Dset colour Q k).mpr
  intro f hfD hfQ hcf
  rw [inducedSeparated_iff_forall_endpoints]
  intro c hc d hdf
  have hccase : c = w₁ ∨ c = u := by simpa [Q] using hc
  rcases hccase with hcw₁ | hcu
  · constructor
    · intro hwd
      exact noAtW₁ f hfQ (by simpa [hcw₁.symm.trans hwd] using hdf) hcf
    · intro hwd
      have hw₁d : G.Adj w₁ d := by simpa [hcw₁] using hwd
      have hdN : d ∈ G.neighborFinset w₁ :=
        (G.mem_neighborFinset w₁ d).mpr hw₁d
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start] at hdN
      have hdcase : d = w₂ ∨ d = u := by simpa using hdN
      exact hdcase.elim
        (fun hd ↦ noAtW₂ f (by simpa [hd] using hdf) hcf)
        (fun hd ↦ noAtU f hfQ (by simpa [hd] using hdf) hcf)
  · constructor
    · intro hud
      exact noAtU f hfQ (by simpa [hcu.symm.trans hud] using hdf) hcf
    · intro hud
      have hud' : G.Adj u d := by simpa [hcu] using hud
      rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
          g.first_adj r.adj hv₁w₁ hv₁x hw₁x hud' with rfl | rfl | rfl
      · exact noAtV₁ f hfD hdf hcf
      · exact noAtW₁ f hfQ hdf hcf
      · exact noAtX f hdf hcf

/-- Condition 2 survives a fresh induced recolouring of the two-thread's
first edge while its middle edge remains matching. -/
theorem longPair_conditionTwo_recolor_twoThreadFirst_zeroThird
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hlocal : VertexSeesMatching G
        (recolor G colour
          (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) w₂ →
      ¬ ∀ i : Fin 4, VertexSeesInduced G
        (recolor G colour
          (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) w₂ i) :
    ConditionTwo G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hv₁w₁
  have hCQ : C ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      g.start_three g.middle_adj g.first_adj.symm
  have hAQ : A ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      g.start_three h.left_adj g.first_adj.symm
  have hBQ : B ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      g.start_three h.right_adj.symm g.first_adj.symm
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj h.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hnewP : new P = none := by simp [new, hPQ, P, hP]
  have hnewC : new C = none := by simp [new, hCQ, C, hC]
  have hnewA : new A = none := by simp [new, hAQ, A, hA]
  have hnewB : new B = none := by simp [new, hBQ, B, hB]
  have hagree : ColoringsAgreeOff G ({Q} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour Q (some k)
  have hNu : G.neighborFinset u = {v₁, w₁, x} :=
    longPair_neighborFinset_eq_three G h.start_three h.first_adj
      g.first_adj r.adj hv₁w₁ hv₁x hw₁x
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases longPair_twoVertex_paletteAffectedBy_twoThreadFirst_cases G g hq
      (by simpa [Q] using haffect) with hqw₂ | hqu
  · subst q
    exact (hlocal hmatch) hall
  · have hqN : q ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u q).mpr hqu.symm
    rw [hNu] at hqN
    have hqcase : q = v₁ ∨ q = w₁ ∨ q = x := by simpa using hqN
    rcases hqcase with hqv₁ | hqw₁ | hqx
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
        g.middle_adj g.second_two C P hCP hnewC hnewP
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [P]) (Or.inr g.first_adj.symm)
      · exact hall
    · subst q
      exact False.elim ((isThreeVertex_ne_isTwoVertex G r.end_three hq) rfl)

/-- The prepared-gap package after the fresh first-edge recolouring. -/
theorem longPair_prepared_recolor_twoThreadFirst_fresh_zeroThird
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hVk : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ some k)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDk : colour (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) ≠ some k)
    (hlocal : VertexSeesMatching G
        (recolor G colour
          (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) w₂ →
      ¬ ∀ i : Fin 4, VertexSeesInduced G
        (recolor G colour
          (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) w₂ i)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    PreparedThreeThreadGap G h
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hv₁w₁
  have havail : ColorAvailableOn G Dset colour Q (some k) := by
    exact longPair_twoThreadFirst_fresh_available_zeroThird G h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour Dset k hP hC hU hVk hk hDk
      (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalid : IsOneTwoColoringOn G Dset new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := Q) (a := some k)
      (by simpa [Dset, Q] using hQD)).mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.sdiff_subset, havail⟩
  have hsat : OneSaturated G new :=
    longPair_oneSaturated_recolor_twoThreadFirst_induced G g colour
      hprepared.2.1 i k hQ hC
  have htwo : ConditionTwo G new :=
    longPair_conditionTwo_recolor_twoThreadFirst_zeroThird G hsub h g r
      hv₁w₁ hv₁x hw₁x colour hprepared.2.2.1 k hP hC hA hB hlocal
  have hthree : ConditionThree G new :=
    longPair_conditionThree_recolor_twoThreadFirst_induced G h g colour
      hprepared.2.2.2 k hP (by simpa [P, Q] using hPQ)
  exact ⟨hvalid, hsat, htwo, hthree⟩

/-- A fresh colour on the first edge of the two-thread gives the usual
crossed-palette completion.  The explicit missing-colour premise records
the only possible Condition-2 obstruction, at the second internal vertex. -/
theorem longPair_hasGoodFour_of_zeroThread_twoThread_far_matching_of_fresh
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b) (hbu : b ≠ u)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m l : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hVD : (⟨s(x, b), hb⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzQ : z ∉ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet).1)
    (hlPair : l ∉ ({i, j} : Set (Fin 4)))
    (hlm : l ≠ m)
    (hDl : colour (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) ≠ some l)
    (hlocal : VertexSeesMatching G
        (recolor G colour
          (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some l)) w₂ →
      ¬ ∀ k : Fin 4, VertexSeesInduced G
        (recolor G colour
          (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some l)) w₂ k) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let Vedge : G.edgeSet := ⟨s(x, b), hb⟩
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hv₁w₁
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hv₁x
  have hQT : Q ≠ T := by
    simpa [Q, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      g.first_adj r.adj hw₁x
  have hQD' : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hTD' : T ∈ Dset := by simpa [Dset, T] using hTD
  have hVD' : Vedge ∈ Dset := by simpa [Dset, Vedge] using hVD
  have hvalid : IsOneTwoColoringOn G Dset colour := by simpa [Dset] using hprepared.1
  have hij : i ≠ j := by
    intro hij
    subst j
    have hp := hvalid Q hQD' T hTD' hQT
    have hsep : InducedSeparated G Q T := by simpa [Q, T, hQ, hT] using hp
    exact hsep.1 u (by simp [Q]) (by simp [T])
  have hLold : ExternalInducedColors G colour u P = {i, j} := by
    simpa [P, Q, T] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        h.first_adj g.first_adj r.adj hv₁w₁ hv₁x hw₁x colour i j hP hQ hT
  have hmi : m ≠ i := by
    intro hEq
    subst m
    have hQV : Q ≠ Vedge := by
      intro heq
      have hval : s(w₁, u) = s(x, b) := congrArg Subtype.val heq
      simp only [Sym2.eq_iff] at hval
      rcases hval with hval | hval
      · exact hw₁x hval.1
      · exact r.adj.ne hval.2
    have hp := hvalid Q hQD' Vedge hVD' hQV
    have hsep : InducedSeparated G Q Vedge := by
      simpa [Q, Vedge, hQ, hV] using hp
    exact hsep.2 ⟨u, by simp [Q], x, by simp [Vedge], r.adj⟩
  have hmj : m ≠ j := by
    intro hEq
    subst m
    have hTV : T ≠ Vedge := by
      intro heq
      have hval : s(x, u) = s(x, b) := congrArg Subtype.val heq
      simp only [Sym2.eq_iff] at hval
      rcases hval with hval | hval
      · exact hbu hval.2.symm
      · exact hb.ne hval.1
    have hp := hvalid T hTD' Vedge hVD' hTV
    have hsep : InducedSeparated G T Vedge := by
      simpa [T, Vedge, hT, hV] using hp
    exact hsep.1 x (by simp [T]) (by simp [Vedge])
  have hlOld : l ∉ ExternalInducedColors G colour u P := by
    rw [hLold]
    exact hlPair
  have hlData : l ≠ i ∧ l ≠ j := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hlPair
  let fresh : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some l)
  have hpreparedFresh : PreparedThreeThreadGap G h fresh := by
    exact longPair_prepared_recolor_twoThreadFirst_fresh_zeroThird G hsub h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour hprepared i l hP hQ hC hU
      (by simpa [Vedge, hV] using hlm.symm) hA hB (by simpa [P] using hlOld)
      hDl hlocal hQD
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAQ : A ≠ Q := fun heq ↦ hAD (heq ▸ hQD')
  have hBQ : B ≠ Q := fun heq ↦ hBD (heq ▸ hQD')
  have hRQ : R ≠ Q := by
    intro heq
    apply hzQ
    have hzR : z ∈ (R : Sym2 V) := by simp [R]
    rw [heq] at hzR
    exact hzR
  have hfreshP : fresh P = none := by simp [fresh, hPQ, P, hP]
  have hfreshR : fresh R = none := by simp [fresh, hRQ, R, hR]
  have hfreshA : fresh A = none := by simp [fresh, hAQ, A, hA]
  have hfreshB : fresh B = none := by simp [fresh, hBQ, B, hB]
  have hfreshQ : fresh Q = some l := by simp [fresh]
  have hfreshT : fresh T = some j := by simp [fresh, hQT.symm, T, hT]
  have hLfresh : ExternalInducedColors G fresh u P = {l, j} := by
    simpa [P, Q, T] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        h.first_adj g.first_adj r.adj hv₁w₁ hv₁x hw₁x fresh l j
        hfreshP hfreshQ hfreshT
  have hagreeFresh : ColoringsAgreeOff G ({Q} : Set G.edgeSet) colour fresh := by
    simpa [fresh] using coloringsAgreeOff_recolor G colour Q (some l)
  have hRunchanged : ExternalInducedColors G colour z R =
      ExternalInducedColors G fresh z R := by
    apply externalInducedColors_eq_of_agreeOff G hagreeFresh
    intro e hext heQ
    have heq : e = Q := by simpa using heQ
    subst e
    exact hzQ hext.1
  have hRfresh : ExternalInducedColors G fresh z R = {i, j} := by
    calc
      ExternalInducedColors G fresh z R =
          ExternalInducedColors G colour z R := hRunchanged.symm
      _ = ExternalInducedColors G colour u P := hpal.symm
      _ = {i, j} := hLold
  apply longPair_hasGoodFour_of_prepared_cross_fill G hsub h fresh
    hpreparedFresh i l m hfreshA hfreshB hfreshP hfreshR
  · rw [hLfresh]
    simp [hlData.1.symm, hij]
  · rw [hRfresh]
    exact hlPair
  · rw [hRfresh]
    simp
  · rw [hLfresh]
    simp
  · rw [hLfresh]
    simp [hmi, hmj, hlm.symm]
  · rw [hRfresh]
    simp [hmi, hmj, hlm.symm]

/-! ## Claim 1 for a two-thread beside a zero-thread -/

/-- In the far-matching zero-thread branch, a colour absent from the two
other first edges, the two-thread middle edge, and the sole induced far
zero-thread edge is available on the selected outer edge. -/
theorem longPair_selectedFirst_fresh_available_twoZero
    {u v₁ v₂ v₃ z w₁ w₂ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x) (hwx : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some i)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some j)
    (hCd : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ some d)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hVd : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ some d)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hretained : ∀ f : G.edgeSet, f ∈ Dset → v₂ ∉ (f : Sym2 V)) :
    ColorAvailableOn G Dset colour
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let W : G.edgeSet := ⟨s(x, b), hb⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hT' : colour T = some i := by simpa [T] using hT
  have hQ' : colour Q = some j := by simpa [Q] using hQ
  have hCd' : colour C ≠ some d := by simpa [C] using hCd
  have hU' : colour U = none := by simpa [U] using hU
  have hWd' : colour W ≠ some d := by simpa [W] using hVd
  have noAtU (f : G.edgeSet) (hfP : f ≠ P)
      (huf : u ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    obtain ⟨c, hfc⟩ := Sym2.mem_iff_exists.mp huf
    have huc : G.Adj u c := by
      have hadj := f.2
      rw [hfc] at hadj
      simpa using hadj
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.adj hvw hvx hwx huc with rfl | rfl | rfl
    · exact hfP (Subtype.ext (by simpa [P, Sym2.eq_swap] using hfc))
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfc)
      have hjd : j = d := Option.some.inj (hQ'.symm.trans (by simpa [hfQ] using hcf))
      exact hdj hjd.symm
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfc)
      have hid : i = d := Option.some.inj (hT'.symm.trans (by simpa [hfT] using hcf))
      exact hdi hid.symm
  have noAtV₁ (f : G.edgeSet) (hfD : f ∈ Dset) (hfP : f ≠ P)
      (hvf : v₁ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start f hvf with hfA | hfP'
    · have hfA' : f = A := Subtype.ext (by simpa [A] using hfA)
      exact hretained f hfD (by simpa [hfA', A])
    · exact hfP (Subtype.ext (by simpa [P] using hfP'))
  have noAtW₁ (f : G.edgeSet)
      (hwf : w₁ ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start f hwf with hfC | hfQ
    · exact hCd' (by
        have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
        simpa [hfC'] using hcf)
    · have hfQ' : f = Q := Subtype.ext (by simpa [Q] using hfQ)
      have hjd : j = d := Option.some.inj (hQ'.symm.trans (by simpa [hfQ'] using hcf))
      exact hdj hjd.symm
  have noAtX (f : G.edgeSet)
      (hxf : x ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    obtain ⟨c, hfc⟩ := Sym2.mem_iff_exists.mp hxf
    have hxc : G.Adj x c := by
      have hadj := f.2
      rw [hfc] at hadj
      simpa using hadj
    have hcN : c ∈ G.neighborFinset x := (G.mem_neighborFinset x c).mpr hxc
    rw [hNfar] at hcN
    have hccase : c = u ∨ c = a ∨ c = b := by simpa using hcN
    rcases hccase with rfl | rfl | rfl
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfc)
      have hid : i = d := Option.some.inj (hT'.symm.trans (by simpa [hfT] using hcf))
      exact hdi hid.symm
    · have hfU : f = U := Subtype.ext (by simpa [U, Sym2.eq_swap] using hfc)
      have hfalse : none = some d := hU'.symm.trans (by simpa [hfU] using hcf)
      simp at hfalse
    · have hfW : f = W := Subtype.ext (by simpa [W, Sym2.eq_swap] using hfc)
      exact hWd' (by simpa [hfW] using hcf)
  apply (colorAvailableOn_some_iff G Dset colour P d).mpr
  intro f hfD hfP hcf
  rw [inducedSeparated_iff_forall_endpoints]
  intro c hc e hef
  have hccase : c = v₁ ∨ c = u := by simpa [P] using hc
  rcases hccase with hcv₁ | hcu
  · constructor
    · intro hEq
      exact noAtV₁ f hfD hfP (by simpa [hcv₁.symm.trans hEq] using hef)
    · intro hadj
      have hve : G.Adj v₁ e := by simpa [hcv₁] using hadj
      have heN : e ∈ G.neighborFinset v₁ := (G.mem_neighborFinset v₁ e).mpr hve
      rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start] at heN
      have hecase : e = v₂ ∨ e = u := by simpa using heN
      exact hecase.elim
        (fun he ↦ hretained f hfD (by simpa [he] using hef))
        (fun he ↦ noAtU f hfP (by simpa [he] using hef) hcf)
  · constructor
    · intro hEq
      exact noAtU f hfP (by simpa [hcu.symm.trans hEq] using hef) hcf
    · intro hadj
      have hue : G.Adj u e := by simpa [hcu] using hadj
      rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
          g.first_adj r.adj hvw hvx hwx hue with rfl | rfl | rfl
      · exact noAtV₁ f hfD hfP hef
      · exact noAtW₁ f hef hcf
      · exact noAtX f hef hcf

/-- After the selected edge receives a fresh induced colour, the first
edge of the two-thread can receive matching. -/
theorem longPair_twoThreadFirst_matching_available_after_selectedFresh_twoZero
    {u v₁ v₂ v₃ z w₁ w₂ t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x) (hwx : w₁ ≠ x)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (d i j : Fin 4)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some i)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some j)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G Dset
      (recolor G colour
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some d)
  have hPT : P ≠ T := by simpa [P, T] using
    longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.adj hvx
  have hPQ : P ≠ Q := by simpa [P, Q] using
    longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have hPC : P ≠ C := by exact
    (longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj h.first_adj.symm).symm
  have hafterP : afterP P = some d := by simp [afterP]
  have hafterT : afterP T = some i := by simp [afterP, hPT.symm, T, hT]
  have hafterC : afterP C ≠ none := by simpa [afterP, hPC.symm, C] using hC
  have noAtU (f : G.edgeSet) (hfQ : f ≠ Q)
      (huf : u ∈ (f : Sym2 V)) (hcf : afterP f = none) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hadj := f.2
      rw [hfa] at hadj
      simpa using hadj
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.adj hvw hvx hwx hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      simp [hfP, hafterP] at hcf
    · exact hfQ (Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa))
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      simp [hfT, hafterT] at hcf
  have noAtW₁ (f : G.edgeSet) (hfQ : f ≠ Q)
      (hwf : w₁ ∈ (f : Sym2 V)) (hcf : afterP f = none) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start f hwf with hfC | hfQ'
    · have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
      exact hafterC (by simpa [hfC'] using hcf)
    · exact hfQ (Subtype.ext (by simpa [Q] using hfQ'))
  apply (colorAvailableOn_none_iff G Dset afterP Q).mpr
  intro f _hfD hfQ hcf a ha haf
  have hacase : a = w₁ ∨ a = u := by simpa [Q] using ha
  exact hacase.elim
    (fun haw ↦ noAtW₁ f hfQ (by simpa [haw] using haf) hcf)
    (fun hau ↦ noAtU f hfQ (by simpa [hau] using haf) hcf)

/-- Condition 2 for the selected-fresh/two-thread-first-matching swap in
the zero-thread configuration. -/
theorem longPair_conditionTwo_selectedFresh_twoThreadFirstMatching_twoZero
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x) (hwx : w₁ ≠ x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (hsat : OneSaturated G colour)
    (d j : Fin 4)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some j)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hDP : (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let D : G.edgeSet := ⟨s(w₂, t), g.last_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hQDne : Q ≠ D := by
    simpa [Q, D] using twoThreadCore_firstEdge_ne_lastEdge G g
  have hDP' : D ≠ P := by simpa [D, P] using hDP
  have hPD : P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hAD : A ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [B] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
  have hAQ : A ≠ Q := fun heq ↦ hAD (heq ▸ hQD)
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD)
  have hBQ : B ≠ Q := fun heq ↦ hBD (heq ▸ hQD)
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hD : colour D = none :=
    longPair_twoThread_last_matching_of_first_two_induced G g colour hsat
      (by simpa [Q, hQ]) (by simpa using hC)
  have hnewQ : new Q = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAQ, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBQ, B, hB]
  have hnewD : new D = none := by
    simp [new, hDP', hQDne.symm, D, hD]
  have hagree : ColoringsAgreeOff G ({P, Q} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ Q := by simpa using he
    simp [new, hne.1, hne.2]
  have hNu : G.neighborFinset u = {v₁, w₁, x} :=
    longPair_neighborFinset_eq_three G h.start_three h.first_adj
      g.first_adj r.adj hvw hvx hwx
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases longPair_twoVertex_paletteAffectedBy_twoThreadFirst_swap_cases
      G h g hq (by simpa [P, Q] using haffect) with hqv₂ | hqw₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub g.second_two
      g.middle_adj.symm g.first_two Q D hQDne hnewQ hnewD
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [Q]) (Or.inr g.middle_adj.symm)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [D]) (Or.inl rfl)
    · exact hall
  · have hqN : q ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u q).mpr hqu.symm
    rw [hNu] at hqN
    have hqcase : q = v₁ ∨ q = w₁ ∨ q = x := by simpa using hqN
    rcases hqcase with hqv₁ | hqw₁ | hqx
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
        g.middle_adj g.second_two Q D hQDne hnewQ hnewD
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [Q]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [D]) (Or.inr g.middle_adj)
      · exact hall
    · subst q
      exact False.elim ((isThreeVertex_ne_isTwoVertex G r.end_three hq) rfl)

/-- Replacing the critical colour on the selected edge by a colour outside
the two centre colours breaks the displayed two-thread's sole Condition-3
obstruction; the third arm is a zero-thread. -/
theorem longPair_conditionThreeAtTwoThread_alt_of_critical_twoZero
    {u v₁ v₂ v₃ z x t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : ZeroThreadCore G u x)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (base : G.edgeSet → OneTwoColor 4) (i j d : Fin 4)
    (hP : base (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hT : base (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some i)
    (hQ : base (threadFirstEdge G q hq) = some j)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let Q : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G base P (some j)) Q none
      ExternalEdgesInduced G critical u Q ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u Q =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q : G.edgeSet := threadFirstEdge G q hq
    let alt := recolor G (recolor G base P (some d)) Q none
    ConditionThreeAtTwoThread G q hq alt := by
  dsimp only
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let U : G.edgeSet := threadLastEdge G q hq
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G base P (some j)) Q none
  let alt : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G base P (some d)) Q none
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hvx
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj
        r.adj hqx
  have hcriticalP : critical P = some j := by simp [critical, hPQ]
  have hcriticalT : critical T = some i := by
    simp [critical, hPT.symm, hQT.symm, T, hT]
  have hcriticalQ : critical Q = none := by simp [critical]
  have haltP : alt P = some d := by simp [alt, hPQ]
  have haltT : alt T = some i := by simp [alt, hPT.symm, hQT.symm, T, hT]
  have haltQ : alt Q = none := by simp [alt]
  have hQeq :
      (⟨s(q.getVert 1, u), hq.first_step_adj.symm⟩ : G.edgeSet) = Q := by
    apply Subtype.ext
    simp [Q, threadFirstEdge, Sym2.eq_swap]
  have hcriticalQ' :
      critical (⟨s(q.getVert 1, u), hq.first_step_adj.symm⟩ : G.edgeSet) = none := by
    rw [hQeq]
    exact hcriticalQ
  have haltQ' :
      alt (⟨s(q.getVert 1, u), hq.first_step_adj.symm⟩ : G.edgeSet) = none := by
    rw [hQeq]
    exact haltQ
  have hcriticalStart : ExternalInducedColors G critical u Q = {j, i} := by
    simpa [Q, P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        hq.first_step_adj h.first_adj r.adj hvq.symm hqx hvx critical j i
        hcriticalQ' hcriticalP hcriticalT
  have haltStart : ExternalInducedColors G alt u Q = {d, i} := by
    simpa [Q, P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        hq.first_step_adj h.first_adj r.adj hvq.symm hqx hvx alt d i
        haltQ' haltP haltT
  have htP : t ∉ (P : Sym2 V) := by
    intro hmem
    have htcase : t = v₁ ∨ t = u := by simpa [P] using hmem
    rcases htcase with htv₁ | htu
    · exact (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two) htv₁
    · exact (IsKThread.endpoints_ne G hq) htu.symm
  have hagree : ColoringsAgreeOff G ({P} : Set G.edgeSet) critical alt := by
    intro e he
    have heP : e ≠ P := by simpa using he
    by_cases heQ : e = Q
    · subst e
      simp [critical, alt]
    · simp [critical, alt, heP, heQ]
  have hmiss : ∀ e, IsExternalAt G t U e → e ∉ ({P} : Set G.edgeSet) := by
    intro e hext heS
    have heq : e = P := by simpa using heS
    subst e
    exact htP hext.1
  have hfarEq : ExternalInducedColors G critical t U =
      ExternalInducedColors G alt t U :=
    externalInducedColors_eq_of_agreeOff G hagree hmiss
  have hfarAlt : ExternalInducedColors G alt t U = {j, i} := by
    rw [← hfarEq, ← hcritical.2.2]
    exact hcriticalStart
  change ConditionThreeAtTwoThread G q hq alt
  intro _hleft _hright
  rw [haltStart, hfarAlt]
  intro heq
  have hdmem : d ∈ ({j, i} : Set (Fin 4)) := by
    rw [← heq]
    simp
  simpa [hdj, hdi] using hdmem

/-- The complete prepared-gap package for the alternate selected/far-zero
swap in a `(3,2,0)` fork.  The first edge of the 2-thread is made matching. -/
theorem longPair_prepared_selectedFresh_twoThreadFirstMatching_twoZero
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some i)
    (hQ : colour (threadFirstEdge G q hq) = some j)
    (hCd : colour (no320ThreadMiddleEdge G q hq) ≠ some d)
    (hC : colour (no320ThreadMiddleEdge G q hq) ≠ none)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hVd : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ some d)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let Q : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) Q none
      ExternalEdgesInduced G critical u Q ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u Q =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q : G.edgeSet := threadFirstEdge G q hq
    PreparedThreeThreadGap G h
      (recolor G (recolor G colour P (some d)) Q none) := by
  dsimp only
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some d)
  let alt : G.edgeSet → OneTwoColor 4 := recolor G afterP Q none
  let g := hq.twoThreadCoreData G
  let g₂ := hq.twoStepArmCore G
  have hQexplicit :
      (⟨s(q.getVert 1, u), g.first_adj.symm⟩ : G.edgeSet) = Q := by
    apply Subtype.ext
    simp [g, Q, threadFirstEdge, Sym2.eq_swap]
  have hLastExplicit :
      (⟨s(q.getVert 2, t), g.last_adj⟩ : G.edgeSet) =
        threadLastEdge G q hq := by
    apply Subtype.ext
    simp [g, threadLastEdge]
  have hPD' : P ∈ Dset := by simpa [P, Dset] using hPD
  have hQD' : Q ∈ Dset := by simpa [Q, Dset] using hQD
  have havailP : ColorAvailableOn G Dset colour P (some d) := by
    exact longPair_selectedFirst_fresh_available_twoZero G h g r
      hvq hvx hqx
      ha hb hNfar colour Dset d i j hP hT
      (by simpa [g, threadFirstEdge, Sym2.eq_swap] using hQ)
      (by simpa [g, no320ThreadMiddleEdge] using hCd) hU hVd hdi hdj
      (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalidAfterP : IsOneTwoColoringOn G Dset afterP := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := P) (a := some d) hPD').mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.diff_subset, havailP⟩
  have havailQ : ColorAvailableOn G Dset afterP Q none := by
    rw [← hQexplicit]
    exact longPair_twoThreadFirst_matching_available_after_selectedFresh_twoZero
      G h g r hvq hvx hqx
      colour Dset d i j hT (by simpa [hQexplicit] using hQ)
      (by simpa [g, no320ThreadMiddleEdge] using hC)
  have hvalidAlt : IsOneTwoColoringOn G Dset alt := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := afterP) (e := Q) (a := none) hQD').mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G) hvalidAfterP Set.diff_subset,
      havailQ⟩
  have hsatAlt : OneSaturated G alt := by
    simpa [alt, afterP, P, Q, g₂, threadFirstEdge, Sym2.eq_swap] using
      longPair_oneSaturated_selectedFresh_twoStepFirstMatching
        G h g₂ hvq colour hprepared.2.1 d j
          (by simpa [hQexplicit] using hQ) hA
  have htwoAlt : ConditionTwo G alt := by
    simpa [alt, afterP, P, Q, hQexplicit, hLastExplicit] using
      longPair_conditionTwo_selectedFresh_twoThreadFirstMatching_twoZero
        G hsub h g r hvq hvx hqx colour hprepared.2.2.1
        hprepared.2.1 d j (by simpa [hQexplicit] using hQ)
        (by simpa [g, no320ThreadMiddleEdge] using hC) hA hB
        (by simpa [hQexplicit] using hQD)
        (by
          simpa [P, Q, hQexplicit] using
            longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
              hq.first_step_adj hvq)
        (by simpa [hLastExplicit, P] using hDP)
  have hcriticalAlt : ConditionThreeAtTwoThread G q hq alt := by
    exact longPair_conditionThreeAtTwoThread_alt_of_critical_twoZero
      G h r q hq hvq hvx hqx colour i j d hP hT hQ hdi hdj
        (by simpa [P, Q, alt, afterP] using hcritical)
  have hthreeAlt : ConditionThree G alt := by
    exact (longPair_conditionThree_swap_selectedOuter_twoThreadFirst_iff
      G h q hq colour hprepared.2.2.2 d).2
        (by simpa [P, Q, alt, afterP] using hcriticalAlt)
  exact ⟨by simpa [Dset, alt, afterP] using hvalidAlt,
    by simpa [alt, afterP] using hsatAlt,
    by simpa [alt, afterP] using htwoAlt,
    by simpa [alt, afterP] using hthreeAlt⟩

/-- Once the Claim swap is prepared, the newly matching 2-thread first
edge guards the selected end while the two deleted chain edges are restored. -/
theorem longPair_hasGoodFour_of_twoThread_middle_induced_alt_twoZero
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some i)
    (hQ : colour (threadFirstEdge G q hq) = some j)
    (hCd : colour (no320ThreadMiddleEdge G q hq) ≠ some d)
    (hC : colour (no320ThreadMiddleEdge G q hq) ≠ none)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hVd : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ some d)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠ threadFirstEdge G q hq)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let Q : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) Q none
      ExternalEdgesInduced G critical u Q ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u Q =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    HasGoodFour G := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let alt : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) Q none
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hpreparedAlt : PreparedThreeThreadGap G h alt := by
    exact longPair_prepared_selectedFresh_twoThreadFirstMatching_twoZero
      G hsub h q hq r hvq hvx hqx ha hb hNfar colour hprepared
        d i j hP hT hQ hCd hC hU hVd hA hB hPD hQD hDP hdi hdj
        (by simpa [P, Q] using hcritical)
  have hAltP : alt P ≠ none := by simp [alt, hPQ]
  have hAltR : alt R = none := by simp [alt, R, P, Q, hRP, hRQ, hR]
  have hAD : A ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [B] using right_chain_edge_not_retained G h.right_adj
  have hAQ : A ≠ Q := fun heq ↦ hAD (heq ▸ hQD)
  have hBQ : B ≠ Q := fun heq ↦ hBD (heq ▸ hQD)
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD)
  have hAltA : alt A = none := by simp [alt, A, hAP, hAQ, hA]
  have hAltB : alt B = none := by simp [alt, B, hBP, hBQ, hB]
  have hAltQ : alt Q = none := by simp [alt]
  apply longPair_hasGoodFour_of_prepared_left_outer_induced
    G hsub h alt hpreparedAlt
      (by simpa [P] using hAltP) (by simpa [R] using hAltR)
      (by simpa [A] using hAltA) (by simpa [B] using hAltB)
      Q hAltQ
  · simp [Q, threadFirstEdge]
  · exact hAQ.symm
  · exact hBQ.symm

/-! ## The distinct-colour preliminary middle-edge move -/

/-- In a `(3,2,0)` fork, an induced colour outside the two centre colours
and the current middle colour is available on the 2-thread middle edge,
provided the critical normal form gives the usual far palette. -/
theorem longPair_twoThreadMiddle_otherColour_available_twoZero
    {u v₁ v₂ v₃ z w₁ w₂ t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : ZeroThreadCore G u x)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x) (hwx : w₁ ≠ x)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (i j c e : Fin 4) (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some i)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some j)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = some c)
    (hD : colour (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) = none)
    (hfar : ExternalInducedColors G colour t
      (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) = {i, j}) :
    ColorAvailableOn G Dset colour
      (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some e) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, t), g.last_adj⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hT' : colour T = some i := by simpa [T] using hT
  have hQ' : colour Q = some j := by simpa [Q] using hQ
  have hC' : colour C = some c := by simpa [C] using hC
  have hD' : colour D = none := by simpa [D] using hD
  have noAtU (f : G.edgeSet) (huf : u ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hf := f.2
      rw [hfa] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.adj hvw hvx hwx hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      have hf : none = some e := hP'.symm.trans (by simpa [hfP] using hcf)
      simp at hf
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hje : j = e := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ] using hcf))
      exact hej hje.symm
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      have hie : i = e := Option.some.inj
        (hT'.symm.trans (by simpa [hfT] using hcf))
      exact hei hie.symm
  have noAtW₁ (f : G.edgeSet) (hwf : w₁ ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start f hwf with hfC | hfQ
    · have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
      have hce : c = e := Option.some.inj
        (hC'.symm.trans (by simpa [hfC'] using hcf))
      exact hec hce.symm
    · have hfQ' : f = Q := Subtype.ext (by simpa [Q] using hfQ)
      have hje : j = e := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ'] using hcf))
      exact hej hje.symm
  have noAtW₂ (f : G.edgeSet) (hwf : w₂ ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end f hwf with hfC | hfD
    · have hfC' : f = C := Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC)
      have hce : c = e := Option.some.inj
        (hC'.symm.trans (by simpa [hfC'] using hcf))
      exact hec hce.symm
    · have hfD' : f = D := Subtype.ext (by simpa [D] using hfD)
      have hf : none = some e := hD'.symm.trans (by simpa [hfD'] using hcf)
      simp at hf
  have noAtT (f : G.edgeSet) (htf : t ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    by_cases hfD : f = D
    · subst f
      have hf : none = some e := hD'.symm.trans hcf
      simp at hf
    · have hemem : e ∈ ExternalInducedColors G colour t D :=
        ⟨f, ⟨htf, hfD⟩, hcf⟩
      rw [hfar] at hemem
      simpa [hei, hej] using hemem
  apply (colorAvailableOn_some_iff G Dset colour C e).mpr
  intro f _hfD hfC hcf
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = w₁ ∨ a = w₂ := by simpa [C] using ha
  rcases hacase with haw₁ | haw₂
  · constructor
    · intro hab
      exact noAtW₁ f (by simpa [haw₁.symm.trans hab] using hbf) hcf
    · intro hab
      have hwb : G.Adj w₁ b := by simpa [haw₁] using hab
      have hbN : b ∈ G.neighborFinset w₁ := (G.mem_neighborFinset w₁ b).mpr hwb
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start] at hbN
      have hbcase : b = w₂ ∨ b = u := by simpa using hbN
      exact hbcase.elim
        (fun hbw ↦ noAtW₂ f (by simpa [hbw] using hbf) hcf)
        (fun hbu ↦ noAtU f (by simpa [hbu] using hbf) hcf)
  · constructor
    · intro hab
      exact noAtW₂ f (by simpa [haw₂.symm.trans hab] using hbf) hcf
    · intro hab
      have hwb : G.Adj w₂ b := by simpa [haw₂] using hab
      have hbN : b ∈ G.neighborFinset w₂ := (G.mem_neighborFinset w₂ b).mpr hwb
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end] at hbN
      have hbcase : b = w₁ ∨ b = t := by simpa using hbN
      exact hbcase.elim
        (fun hbw ↦ noAtW₁ f (by simpa [hbw] using hbf) hcf)
        (fun hbt ↦ noAtT f (by simpa [hbt] using hbf) hcf)

/-- Recolouring the 2-thread middle edge with another induced colour
preserves every prepared-gap invariant in the zero-thread configuration. -/
theorem longPair_prepared_recolor_twoThreadMiddle_twoZero
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j c e : Fin 4) (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some i)
    (hQ : colour (threadFirstEdge G q hq) = some j)
    (hC : colour (no320ThreadMiddleEdge G q hq) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let Q : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) Q none
      ExternalEdgesInduced G critical u Q ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u Q =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    PreparedThreeThreadGap G h
      (recolor G colour (no320ThreadMiddleEdge G q hq) (some e)) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  let g := hq.twoThreadCoreData G
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some j)) Q none
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour C (some e)
  have hCD' : C ∈ Dset := by simpa [C, Dset] using hCD
  have hQexplicit :
      (⟨s(q.getVert 1, u), g.first_adj.symm⟩ : G.edgeSet) = Q := by
    apply Subtype.ext
    simp [Q, g, threadFirstEdge, Sym2.eq_swap]
  have hCexplicit :
      (⟨s(q.getVert 1, q.getVert 2), g.middle_adj⟩ : G.edgeSet) = C := by
    rfl
  have hD : colour D = none := by
    have hQnon : colour Q ≠ none := by rw [hQ]; simp
    have hCval : colour C = some c := by simpa [C] using hC
    have hCnon : colour C ≠ none := by rw [hCval]; simp
    exact longPair_twoThread_last_matching_of_first_two_induced G g colour
      hprepared.2.1
        (by rw [hQexplicit]; exact hQnon)
        (by rw [hCexplicit]; exact hCnon)
  have hDexplicit :
      (⟨s(q.getVert 2, t), g.last_adj⟩ : G.edgeSet) = D := by
    apply Subtype.ext
    simp [D, g, threadLastEdge]
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hvx
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj r.adj hqx
  have hcriticalP : critical P = some j := by simp [critical, hPQ]
  have hcriticalT : critical T = some i := by
    simp [critical, hPT.symm, hQT.symm, T, hT]
  have hcriticalQ : critical Q = none := by simp [critical]
  have hQeq :
      (⟨s(q.getVert 1, u), hq.first_step_adj.symm⟩ : G.edgeSet) = Q := by
    apply Subtype.ext
    simp [Q, threadFirstEdge, Sym2.eq_swap]
  have hcriticalQ' :
      critical (⟨s(q.getVert 1, u), hq.first_step_adj.symm⟩ : G.edgeSet) = none := by
    rw [hQeq]
    exact hcriticalQ
  have hcriticalStart : ExternalInducedColors G critical u Q = {j, i} := by
    simpa [Q, P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        hq.first_step_adj h.first_adj r.adj hvq.symm hqx hvx critical j i
        hcriticalQ' hcriticalP hcriticalT
  have htP : t ∉ (P : Sym2 V) := by
    intro hmem
    have hcase : t = v₁ ∨ t = u := by simpa [P] using hmem
    rcases hcase with htv₁ | htu
    · exact (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two) htv₁
    · exact (IsKThread.endpoints_ne G hq) htu.symm
  have htQ : t ∉ (Q : Sym2 V) := by
    intro hmem
    have hcase : t = u ∨ t = q.getVert 1 := by
      simpa [Q, threadFirstEdge] using hmem
    rcases hcase with htu | htq
    · exact (IsKThread.endpoints_ne G hq) htu.symm
    · exact (isThreeVertex_ne_isTwoVertex G hq.end_three g.first_two) htq
  have hagreeCritical : ColoringsAgreeOff G ({P, Q} : Set G.edgeSet)
      colour critical := by
    intro f hf
    have hne : f ≠ P ∧ f ≠ Q := by simpa using hf
    simp [critical, hne.1, hne.2]
  have hmissFar : ∀ f, IsExternalAt G t D f →
      f ∉ ({P, Q} : Set G.edgeSet) := by
    intro f hfext hfset
    have hfcase : f = P ∨ f = Q := by simpa using hfset
    exact hfcase.elim
      (fun hf ↦ htP (by simpa [hf] using hfext.1))
      (fun hf ↦ htQ (by simpa [hf] using hfext.1))
  have hfarEq : ExternalInducedColors G colour t D =
      ExternalInducedColors G critical t D :=
    externalInducedColors_eq_of_agreeOff G hagreeCritical hmissFar
  have hfar : ExternalInducedColors G colour t D = {i, j} := by
    rw [hfarEq, ← hcritical.2.2]
    simpa [Set.pair_comm] using hcriticalStart
  have havail : ColorAvailableOn G Dset colour C (some e) := by
    simpa [C, D, g, no320ThreadMiddleEdge, threadFirstEdge,
      threadLastEdge, Sym2.eq_swap] using
      longPair_twoThreadMiddle_otherColour_available_twoZero G h g r
        hvq hvx hqx colour Dset i j c e hei hej hec hP hT
        (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQ)
        (by simpa [g, C, no320ThreadMiddleEdge] using hC)
        (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hD)
        (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hfar)
  have hvalid : IsOneTwoColoringOn G Dset new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := C) (a := some e) hCD').mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.sdiff_subset, havail⟩
  have hsat : OneSaturated G new := by
    simpa [new, C] using oneSaturated_recolor_induced_to_induced
      G hprepared.2.1 C c e (by simpa [C] using hC)
  have htwo : ConditionTwo G new := by
    simpa [new, C, D, g, no320ThreadMiddleEdge, threadFirstEdge,
      threadLastEdge, Sym2.eq_swap] using
      conditionTwo_recolor_twoThreadMiddle_to_induced G hsub h g colour
        hprepared.2.2.1 (by simpa [Dset] using hprepared.1) c e hec hP
        (by simpa [g, C, no320ThreadMiddleEdge] using hC)
        (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hD)
        hA hB (by simpa [C, Dset] using hCD')
        (by rw [hDexplicit]; exact hDP)
  have hthree : ConditionThree G new := by
    simpa [new, C, g, no320ThreadMiddleEdge] using
      conditionThree_recolor_edge_between_two_vertices G g.first_two
        g.second_two g.middle_adj colour hprepared.2.2.2 e
  exact ⟨by simpa [Dset, new] using hvalid,
    by simpa [new] using hsat, by simpa [new] using htwo,
    by simpa [new] using hthree⟩

/-- If the induced colour on the far zero-thread edge differs from the
2-thread middle colour, first move the middle edge to that far colour and
then use its old colour in the Claim swap. -/
theorem longPair_hasGoodFour_of_twoThread_middle_induced_distinct_twoZero
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j c e : Fin 4)
    (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c)
    (hci : c ≠ i) (hcj : c ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some i)
    (hQ : colour (threadFirstEdge G q hq) = some j)
    (hC : colour (no320ThreadMiddleEdge G q hq) = some c)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some e)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠ threadFirstEdge G q hq)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let Q : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) Q none
      ExternalEdgesInduced G critical u Q ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u Q =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    HasGoodFour G := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let W : G.edgeSet := ⟨s(x, b), hb⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let changed : G.edgeSet → OneTwoColor 4 := recolor G colour C (some e)
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some j)) Q none
  let changedCritical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G changed P (some j)) Q none
  let g := hq.twoThreadCoreData G
  have hcriticalBase :
      ExternalEdgesInduced G critical u Q ∧
        ExternalEdgesInduced G critical t D ∧
        ExternalInducedColors G critical u Q =
          ExternalInducedColors G critical t D := by
    simpa [critical, P, Q, D] using hcritical
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPC : P ≠ C := by
    intro hEq
    have hf : none = some c := hP.symm.trans (by simpa [P, C, hEq] using hC)
    simp at hf
  have hRC : R ≠ C := by
    intro hEq
    have hf : none = some c := hR.symm.trans (by simpa [R, C, hEq] using hC)
    simp at hf
  have hTC : T ≠ C := by
    intro hEq
    have hf : some i = some c := hT.symm.trans (by simpa [T, C, hEq] using hC)
    exact hci (Option.some.inj hf).symm
  have hQC : Q ≠ C := by
    intro hEq
    have hf : some j = some c := hQ.symm.trans (by simpa [Q, C, hEq] using hC)
    exact hcj (Option.some.inj hf).symm
  have hUC : U ≠ C := by
    intro hEq
    have hf : none = some c := hU.symm.trans (by simpa [U, C, hEq] using hC)
    simp at hf
  have hWC : W ≠ C := by
    intro hEq
    have hf : some e = some c := hV.symm.trans (by simpa [W, C, hEq] using hC)
    exact hec (Option.some.inj hf)
  have hAC : A ≠ C := by
    intro hEq
    have hf : none = some c := hA.symm.trans (by simpa [A, C, hEq] using hC)
    simp at hf
  have hBC : B ≠ C := by
    intro hEq
    have hf : none = some c := hB.symm.trans (by simpa [B, C, hEq] using hC)
    simp at hf
  have hDval : colour D = none := by
    exact longPair_twoThread_last_matching_of_first_two_induced G g colour
      hprepared.2.1
        (by
          have hnon : colour Q ≠ none := by rw [hQ]; simp
          simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hnon)
        (by
          have hnon : colour C ≠ none := by rw [hC]; simp
          simpa [g, C, no320ThreadMiddleEdge] using hnon)
  have hDC : D ≠ C := by
    intro hEq
    have hf : none = some c := hDval.symm.trans
      (by simpa [D, C, hEq] using hC)
    simp at hf
  have hpreparedChanged : PreparedThreeThreadGap G h changed := by
    exact longPair_prepared_recolor_twoThreadMiddle_twoZero G hsub h q hq r
      hvq hvx hqx colour hprepared i j c e hei hej hec hP hT hQ hC
        hA hB hCD hDP (by simpa [P, Q] using hcritical)
  have hchangedP : changed P = none := by simp [changed, hPC, P, hP]
  have hchangedR : changed R = none := by simp [changed, hRC, R, hR]
  have hchangedT : changed T = some i := by simp [changed, hTC, T, hT]
  have hchangedQ : changed Q = some j := by simp [changed, hQC, Q, hQ]
  have hchangedC : changed C = some e := by simp [changed]
  have hchangedD : changed D = none := by simp [changed, hDC, D, hDval]
  have hchangedU : changed U = none := by simp [changed, hUC, U, hU]
  have hchangedW : changed W = some e := by simp [changed, hWC, W, hV]
  have hchangedA : changed A = none := by simp [changed, hAC, A, hA]
  have hchangedB : changed B = none := by simp [changed, hBC, B, hB]
  have hcritEq : changedCritical = recolor G critical C (some e) := by
    funext f
    by_cases hfP : f = P
    · subst f
      simp [changedCritical, changed, critical, hPC, hPC.symm,
        hPQ, hPQ.symm]
    · by_cases hfQ : f = Q
      · subst f
        simp [changedCritical, changed, critical, hPQ, hPQ.symm,
          hQC, hQC.symm]
      · by_cases hfC : f = C
        · subst f
          simp [changedCritical, changed, critical, hPC, hPC.symm,
            hQC, hQC.symm]
        · simp [changedCritical, changed, critical, hfP, hfQ, hfC]
  have huC : u ∉ (C : Sym2 V) := by
    intro hmem
    have hcase : u = q.getVert 1 ∨ u = q.getVert 2 := by
      simpa [C, no320ThreadMiddleEdge] using hmem
    rcases hcase with huq₁ | huq₂
    · exact hq.first_step_adj.ne huq₁
    · exact g.second_ne_start huq₂.symm
  have htC : t ∉ (C : Sym2 V) := by
    intro hmem
    have hcase : t = q.getVert 1 ∨ t = q.getVert 2 := by
      simpa [C, no320ThreadMiddleEdge] using hmem
    rcases hcase with htq₁ | htq₂
    · exact g.first_ne_end htq₁.symm
    · exact g.last_adj.ne htq₂.symm
  have hagreeCrit : ColoringsAgreeOff G ({C} : Set G.edgeSet)
      critical changedCritical := by
    rw [hcritEq]
    simpa using coloringsAgreeOff_recolor G critical C (some e)
  have hmissStart : ∀ f, IsExternalAt G u Q f →
      f ∉ ({C} : Set G.edgeSet) := by
    intro f hfext hfset
    have hf : f = C := by simpa using hfset
    subst f
    exact huC hfext.1
  have hmissFar : ∀ f, IsExternalAt G t D f →
      f ∉ ({C} : Set G.edgeSet) := by
    intro f hfext hfset
    have hf : f = C := by simpa using hfset
    subst f
    exact htC hfext.1
  have hcriticalChanged :
      ExternalEdgesInduced G changedCritical u Q ∧
        ExternalEdgesInduced G changedCritical t D ∧
        ExternalInducedColors G changedCritical u Q =
          ExternalInducedColors G changedCritical t D := by
    have hstart := externalEdgesInduced_of_agreeOff G hagreeCrit
      hmissStart hcriticalBase.1
    have hfar := externalEdgesInduced_of_agreeOff G hagreeCrit
      hmissFar hcriticalBase.2.1
    have hstartEq := externalInducedColors_eq_of_agreeOff G hagreeCrit hmissStart
    have hfarEq := externalInducedColors_eq_of_agreeOff G hagreeCrit hmissFar
    refine ⟨hstart, hfar, ?_⟩
    calc
      ExternalInducedColors G changedCritical u Q =
          ExternalInducedColors G critical u Q := hstartEq.symm
      _ = ExternalInducedColors G critical t D := hcriticalBase.2.2
      _ = ExternalInducedColors G changedCritical t D := hfarEq
  apply longPair_hasGoodFour_of_twoThread_middle_induced_alt_twoZero
    G hsub h q hq r hvq hvx hqx ha hb hNfar changed hpreparedChanged
      c i j
  · exact hchangedP
  · exact hchangedR
  · exact hchangedT
  · exact hchangedQ
  · rw [hchangedC]
    simpa using hec
  · rw [hchangedC]
    simp
  · exact hchangedU
  · rw [hchangedW]
    simpa using hec
  · exact hchangedA
  · exact hchangedB
  · exact hPD
  · exact hQD
  · exact hDP
  · exact hRP
  · exact hRQ
  · exact hci
  · exact hcj
  · simpa [P, Q, changedCritical] using hcriticalChanged

/-! ## Claim 1: the 2-thread middle edge is matching -/

/-- In a bad graph, the middle edge of the displayed 2-thread in a
`(3,2,0)` fork is matching-coloured in the colouring obtained after
deleting the selected 3-thread middle vertex. -/
theorem longPair_twoThread_middle_matching_in_bad_graph_twoZero
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t x : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u x}
    (hp : IsKThread G p 3) (hq : IsKThread G q 2) (hr : IsKThread G r 0)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) :
    (transportColoringToSupergraph
        (G.deleteIncidenceSet_le (p.getVert 2)) small)
      (no320ThreadMiddleEdge G q hq) = none := by
  classical
  let h := hp.threeThreadCore G
  let g := hq.twoThreadCoreData G
  let rr := hr.zeroThreadCore G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le (p.getVert 2)) small
  let Dset : Set G.edgeSet :=
    RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
  let P : G.edgeSet := threadFirstEdge G p hp
  let R : G.edgeSet := threadLastEdge G p hp
  let Q : G.edgeSet := threadFirstEdge G q hq
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  let T : G.edgeSet := threadFirstEdge G r hr
  let A : G.edgeSet :=
    ⟨s(p.getVert 1, p.getVert 2),
      p.adj_getVert_succ (i := 1) (by
        have hlen : p.length = 4 := by simpa using hp.length
        omega)⟩
  let B : G.edgeSet :=
    ⟨s(p.getVert 3, p.getVert 2),
      (p.adj_getVert_succ (i := 2) (by
        have hlen : p.length = 4 := by simpa using hp.length
        omega)).symm⟩
  have hpLen : p.length = 4 := by simpa using hp.length
  have hqLen : q.length = 3 := by simpa using hq.length
  have hpGetNe (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) (hab : a ≠ b) :
      p.getVert a ≠ p.getVert b := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using ha)
      (show b ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using hb) heq
    exact hab hinj
  have hqGetNe (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (hab : a ≠ b) :
      q.getVert a ≠ q.getVert b := by
    intro heq
    have hinj := hq.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ q.length} by simpa [hqLen] using ha)
      (show b ∈ {n : ℕ | n ≤ q.length} by simpa [hqLen] using hb) heq
    exact hab hinj
  have hpEnd : p.getVert 4 = z := by
    rw [← hpLen]
    exact p.getVert_length
  have hqEnd : q.getVert 3 = t := by
    rw [← hqLen]
    exact q.getVert_length
  have hrFirst : r.getVert 1 = x := by
    have hrLen : r.length = 1 := by simpa using hr.length
    rw [← hrLen]
    exact r.getVert_length
  have hpr' : p.getVert 1 ≠ x := by simpa [hrFirst] using hpr
  have hqr' : q.getVert 1 ≠ x := by simpa [hrFirst] using hqr
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = u ∨ p.getVert 2 = p.getVert 1 := by
      simpa [P, threadFirstEdge] using hmem
    exact hcase.elim
      (fun he ↦ hpGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using he))
      (hpGetNe 2 1 (by omega) (by omega) (by omega))
  have huFarQ := twoThread_vertex_far_from_threeThread_middle G hq h
    q.start_mem_support
  have hQD : Q ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      huFarQ.1 huFarQ.2 Q (by simp [Q, threadFirstEdge])
  have hCD : C ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = q.getVert 1 ∨
        p.getVert 2 = q.getVert 2 := by
      simpa [C, no320ThreadMiddleEdge] using hmem
    rcases hcase with hcase | hcase
    · exact (twoThread_vertex_far_from_threeThread_middle G hq h
        (q.getVert_mem_support 1)).1 hcase.symm
    · exact (twoThread_vertex_far_from_threeThread_middle G hq h
        (q.getVert_mem_support 2)).1 hcase.symm
  have hx₂ : x ≠ p.getVert 2 := by
    exact isThreeVertex_ne_isTwoVertex G rr.end_three h.middle_two
  have hnotX₂ : ¬ G.Adj x (p.getVert 2) := by
    intro hxadj
    have hxN : x ∈ G.neighborFinset (p.getVert 2) :=
      (G.mem_neighborFinset (p.getVert 2) x).mpr hxadj.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third] at hxN
    have hxcase : x = p.getVert 1 ∨ x = p.getVert 3 := by simpa using hxN
    exact hxcase.elim
      (fun he ↦ (isThreeVertex_ne_isTwoVertex G rr.end_three h.first_two) he)
      (fun he ↦ (isThreeVertex_ne_isTwoVertex G rr.end_three h.third_two) he)
  have hTD : T ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G hx₂ hnotX₂
      T (by simp [T, threadFirstEdge, hrFirst])
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hpq
  have hPT : P ≠ T := by
    simpa [P, T, h, rr, threadFirstEdge, hrFirst, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj rr.adj hpr'
  have hQT : Q ≠ T := by
    simpa [Q, T, rr, threadFirstEdge, hrFirst, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj rr.adj hqr'
  have hDP : D ≠ P := by
    intro heq
    have hval : s(q.getVert 2, t) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hqGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hqGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa [hqEnd] using hval.2)
  have hRP : R ≠ P := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hpGetNe 3 1 (by omega) (by omega) (by omega) hval.1
  have hRQ : R ≠ Q := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, q.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hpGetNe 4 0 (by omega) (by omega) (by omega)
        (by simpa [hpEnd] using hval.2)
  obtain ⟨hP, hR, _hpal⟩ :=
    longPair_threeThread_hard_normal_form_of_no_goodFour G hgirth h small
      hsmall hsub hbad
  have hprepared : PreparedThreeThreadGap G h base :=
    preparedThreeThreadGap_of_goodFour G hsub h small hsmall
  have hAD : A ∉ Dset := by
    simpa [h, A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [h, B, Dset, Sym2.eq_swap] using
      right_chain_edge_not_retained G h.right_adj
  have hA : base A = none := by
    have hAe : A.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [Dset, RetainedEdges] using hAD
    simp [base, transportColoringToSupergraph, hAe]
  have hB : base B = none := by
    have hBe : B.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [Dset, RetainedEdges] using hBD
    simp [base, transportColoringToSupergraph, hBe]
  by_contra hCne
  have hCnon : base C ≠ none := by
    simpa [base, C] using hCne
  obtain ⟨j, hQval, hcritical⟩ :=
    longPair_twoThread_second_induced_critical_normal_form
      G hp hq hpq small hsmall hsub
        (by simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP)
        (by simpa [h, base, R, threadLastEdge] using hR)
        (by simpa [C, base, no320ThreadMiddleEdge] using hCnon) hbad
  have hPval : base P = none := by
    simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP
  have hRval : base R = none := by
    simpa [h, base, R, threadLastEdge] using hR
  have hQval' : base Q = some j := by simpa [base, Q] using hQval
  have hvalid : IsOneTwoColoringOn G Dset base := by
    simpa [Dset] using hprepared.1
  have hTne : base T ≠ none := by
    intro hTnone
    have hcompat := hvalid P hPD T hTD hPT
    have hdisj : EndpointDisjoint G P T := by
      simpa [hPval, hTnone] using hcompat
    exact hdisj u (by simp [P, threadFirstEdge])
      (by simp [T, threadFirstEdge])
  cases hTval : base T with
  | none => exact False.elim (hTne hTval)
  | some i =>
      have hij : i ≠ j := by
        intro hij
        subst j
        have hcompat := hvalid T hTD Q hQD hQT.symm
        have hsep : InducedSeparated G T Q := by
          simpa [hTval, hQval'] using hcompat
        exact hsep.1 u (by simp [T, threadFirstEdge])
          (by simp [Q, threadFirstEdge])
      cases hCval : base C with
      | none => exact False.elim (hCnon hCval)
      | some c =>
          have hCT : C ≠ T := by
            simpa [C, T, g, rr, no320ThreadMiddleEdge, threadFirstEdge,
              hrFirst, Sym2.eq_swap] using
              longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two
                g.second_two h.start_three g.middle_adj rr.adj.symm
          have hci : c ≠ i := by
            intro hci
            subst c
            have hcompat := hvalid C hCD T hTD hCT
            have hsep : InducedSeparated G C T := by
              simpa [hCval, hTval] using hcompat
            exact hsep.2 ⟨q.getVert 1,
              by simp [C, no320ThreadMiddleEdge], u,
              by simp [T, threadFirstEdge], hq.first_step_adj.symm⟩
          have hcj : c ≠ j := by
            intro hcj
            subst c
            have hQC : Q ≠ C := by
              intro heq
              have hval : s(u, q.getVert 1) =
                  s(q.getVert 1, q.getVert 2) := congrArg Subtype.val heq
              simp only [Sym2.eq_iff] at hval
              rcases hval with hval | hval
              · exact hq.first_step_adj.ne hval.1
              · exact hqGetNe 0 2 (by omega) (by omega) (by omega)
                  (by simpa using hval.1)
            have hcompat := hvalid Q hQD C hCD hQC
            have hsep : InducedSeparated G Q C := by
              simpa [hQval', hCval] using hcompat
            exact hsep.1 (q.getVert 1)
              (by simp [Q, threadFirstEdge])
              (by simp [C, no320ThreadMiddleEdge])
          have hDval : base D = none := by
            exact longPair_twoThread_last_matching_of_first_two_induced G g base
              hprepared.2.1
                (by
                  have hn : base Q ≠ none := by rw [hQval']; simp
                  simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hn)
                (by
                  have hn : base C ≠ none := by rw [hCval]; simp
                  simpa [g, C, no320ThreadMiddleEdge] using hn)
          obtain ⟨a, b, hab, hau, hbu, ha, hb, hNfar⟩ :=
            rr.exists_far_neighbors G
          let U : G.edgeSet := ⟨s(x, a), ha⟩
          let W : G.edgeSet := ⟨s(x, b), hb⟩
          have hUD : U ∈ Dset := by
            exact longPair_incident_retained_deleteIncidence_of_not_adj G
              hx₂ hnotX₂ U (by simp [U])
          have hWD : W ∈ Dset := by
            exact longPair_incident_retained_deleteIncidence_of_not_adj G
              hx₂ hnotX₂ W (by simp [W])
          have hUW : U ≠ W := by
            intro heq
            have hval : s(x, a) = s(x, b) := congrArg Subtype.val heq
            simp only [Sym2.eq_iff] at hval
            rcases hval with hsame | hswap
            · exact hab hsame.2
            · exact hb.ne hswap.1
          cases hUval : base U with
          | none =>
              cases hWval : base W with
              | none =>
                  have hcompat := hvalid U hUD W hWD hUW
                  have hdisj : EndpointDisjoint G U W := by
                    simpa [hUval, hWval] using hcompat
                  exact False.elim (hdisj x (by simp [U]) (by simp [W]))
              | some m =>
                  have hmi : m ≠ i := by
                    intro hmi
                    subst m
                    have hTW : T ≠ W := by
                      intro heq
                      have hval := congrArg Subtype.val heq
                      dsimp [T, W, threadFirstEdge] at hval
                      rw [hrFirst] at hval
                      simp only [Sym2.eq_iff] at hval
                      rcases hval with hval | hval
                      · exact rr.adj.ne hval.1
                      · exact hbu hval.1.symm
                    have hcompat := hvalid T hTD W hWD hTW
                    have hsep : InducedSeparated G T W := by
                      simpa [hTval, hWval] using hcompat
                    exact hsep.1 x (by simp [T, threadFirstEdge, hrFirst])
                      (by simp [W])
                  have hmj : m ≠ j := by
                    intro hmj
                    subst m
                    have hQW : Q ≠ W := by
                      intro heq
                      have hval : s(u, q.getVert 1) = s(x, b) :=
                        congrArg Subtype.val heq
                      simp only [Sym2.eq_iff] at hval
                      rcases hval with hval | hval
                      · exact rr.adj.ne hval.1
                      · exact hqr' hval.2
                    have hcompat := hvalid Q hQD W hWD hQW
                    have hsep : InducedSeparated G Q W := by
                      simpa [hQval', hWval] using hcompat
                    exact hsep.2 ⟨u, by simp [Q, threadFirstEdge], x,
                      by simp [W], rr.adj⟩
                  by_cases hmc : m = c
                  · subst m
                    have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by
                      simp [hij]
                    obtain ⟨d, hdPair, hcd⟩ :=
                      longPair_exists_fresh_outside_two_palette
                        ({i, j} : Set (Fin 4)) hpairCard (some c)
                    have hdData : d ≠ i ∧ d ≠ j := by
                      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
                        not_or] using hdPair
                    apply hbad
                    exact longPair_hasGoodFour_of_twoThread_middle_induced_alt_twoZero
                      G hsub h q hq rr hpq hpr' hqr' ha hb hNfar base hprepared
                        d i j
                        (by simpa [h, P, threadFirstEdge, Sym2.eq_swap] using hPval)
                        (by simpa [h, R, threadLastEdge] using hRval)
                        (by simpa [rr, T, threadFirstEdge, hrFirst,
                          Sym2.eq_swap] using hTval)
                        (by simpa [Q] using hQval')
                        (by simpa [C, no320ThreadMiddleEdge, hCval] using hcd)
                        (by simpa [C] using hCnon)
                        (by simpa [U] using hUval)
                        (by simpa [W, hWval] using hcd)
                        (by simpa [h, A] using hA)
                        (by simpa [h, B] using hB)
                        (by simpa [h, P, Dset, threadFirstEdge,
                          Sym2.eq_swap] using hPD)
                        (by simpa [Q, Dset] using hQD)
                        (by simpa [h, D, P, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hDP)
                        (by simpa [h, R, P, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hRP)
                        (by simpa [h, R, Q, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hRQ)
                        hdData.1 hdData.2
                        (by simpa [base, P, Q, threadFirstEdge,
                          Sym2.eq_swap] using hcritical)
                  · apply hbad
                    exact longPair_hasGoodFour_of_twoThread_middle_induced_distinct_twoZero
                      G hsub h q hq rr hpq hpr' hqr' ha hb hNfar base hprepared
                        i j c m hmi hmj hmc hci hcj
                        (by simpa [h, P, threadFirstEdge, Sym2.eq_swap] using hPval)
                        (by simpa [h, R, threadLastEdge] using hRval)
                        (by simpa [rr, T, threadFirstEdge, hrFirst,
                          Sym2.eq_swap] using hTval)
                        (by simpa [Q] using hQval')
                        (by simpa [C] using hCval)
                        (by simpa [U] using hUval)
                        (by simpa [W] using hWval)
                        (by simpa [h, A] using hA)
                        (by simpa [h, B] using hB)
                        (by simpa [h, P, Dset, threadFirstEdge,
                          Sym2.eq_swap] using hPD)
                        (by simpa [Q, Dset] using hQD)
                        (by simpa [C, Dset] using hCD)
                        (by simpa [h, D, P, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hDP)
                        (by simpa [h, R, P, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hRP)
                        (by simpa [h, R, Q, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hRQ)
                        (by simpa [base, P, Q, threadFirstEdge,
                          Sym2.eq_swap] using hcritical)
          | some m =>
              cases hWval : base W with
              | none =>
                  have hNswap : G.neighborFinset x = {u, b, a} := by
                    simpa [Finset.pair_comm] using hNfar
                  have hmi : m ≠ i := by
                    intro hmi
                    subst m
                    have hTU : T ≠ U := by
                      intro heq
                      have hval := congrArg Subtype.val heq
                      dsimp [T, U, threadFirstEdge] at hval
                      rw [hrFirst] at hval
                      simp only [Sym2.eq_iff] at hval
                      rcases hval with hval | hval
                      · exact rr.adj.ne hval.1
                      · exact hau hval.1.symm
                    have hcompat := hvalid T hTD U hUD hTU
                    have hsep : InducedSeparated G T U := by
                      simpa [hTval, hUval] using hcompat
                    exact hsep.1 x (by simp [T, threadFirstEdge, hrFirst])
                      (by simp [U])
                  have hmj : m ≠ j := by
                    intro hmj
                    subst m
                    have hQU : Q ≠ U := by
                      intro heq
                      have hval : s(u, q.getVert 1) = s(x, a) :=
                        congrArg Subtype.val heq
                      simp only [Sym2.eq_iff] at hval
                      rcases hval with hval | hval
                      · exact rr.adj.ne hval.1
                      · exact hqr' hval.2
                    have hcompat := hvalid Q hQD U hUD hQU
                    have hsep : InducedSeparated G Q U := by
                      simpa [hQval', hUval] using hcompat
                    exact hsep.2 ⟨u, by simp [Q, threadFirstEdge], x,
                      by simp [U], rr.adj⟩
                  by_cases hmc : m = c
                  · subst m
                    have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by
                      simp [hij]
                    obtain ⟨d, hdPair, hcd⟩ :=
                      longPair_exists_fresh_outside_two_palette
                        ({i, j} : Set (Fin 4)) hpairCard (some c)
                    have hdData : d ≠ i ∧ d ≠ j := by
                      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
                        not_or] using hdPair
                    apply hbad
                    exact longPair_hasGoodFour_of_twoThread_middle_induced_alt_twoZero
                      G hsub h q hq rr hpq hpr' hqr' hb ha hNswap base hprepared
                        d i j
                        (by simpa [h, P, threadFirstEdge, Sym2.eq_swap] using hPval)
                        (by simpa [h, R, threadLastEdge] using hRval)
                        (by simpa [rr, T, threadFirstEdge, hrFirst,
                          Sym2.eq_swap] using hTval)
                        (by simpa [Q] using hQval')
                        (by simpa [C, no320ThreadMiddleEdge, hCval] using hcd)
                        (by simpa [C] using hCnon)
                        (by simpa [W] using hWval)
                        (by simpa [U, hUval] using hcd)
                        (by simpa [h, A] using hA)
                        (by simpa [h, B] using hB)
                        (by simpa [h, P, Dset, threadFirstEdge,
                          Sym2.eq_swap] using hPD)
                        (by simpa [Q, Dset] using hQD)
                        (by simpa [h, D, P, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hDP)
                        (by simpa [h, R, P, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hRP)
                        (by simpa [h, R, Q, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hRQ)
                        hdData.1 hdData.2
                        (by simpa [base, P, Q, threadFirstEdge,
                          Sym2.eq_swap] using hcritical)
                  · apply hbad
                    exact longPair_hasGoodFour_of_twoThread_middle_induced_distinct_twoZero
                      G hsub h q hq rr hpq hpr' hqr' hb ha hNswap base hprepared
                        i j c m hmi hmj hmc hci hcj
                        (by simpa [h, P, threadFirstEdge, Sym2.eq_swap] using hPval)
                        (by simpa [h, R, threadLastEdge] using hRval)
                        (by simpa [rr, T, threadFirstEdge, hrFirst,
                          Sym2.eq_swap] using hTval)
                        (by simpa [Q] using hQval')
                        (by simpa [C] using hCval)
                        (by simpa [W] using hWval)
                        (by simpa [U] using hUval)
                        (by simpa [h, A] using hA)
                        (by simpa [h, B] using hB)
                        (by simpa [h, P, Dset, threadFirstEdge,
                          Sym2.eq_swap] using hPD)
                        (by simpa [Q, Dset] using hQD)
                        (by simpa [C, Dset] using hCD)
                        (by simpa [h, D, P, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hDP)
                        (by simpa [h, R, P, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hRP)
                        (by simpa [h, R, Q, threadFirstEdge, threadLastEdge,
                          Sym2.eq_swap] using hRQ)
                        (by simpa [base, P, Q, threadFirstEdge,
                          Sym2.eq_swap] using hcritical)
              | some n =>
                  apply hbad
                  exact longPair_hasGoodFour_of_zeroThread_twoThread_far_both_induced
                    G hsub h g rr hpq hpr' hqr' ha hb hNfar base hprepared i
                      (by simpa [h, P, threadFirstEdge, Sym2.eq_swap] using hPval)
                      (by simpa [h, R, threadLastEdge] using hRval)
                      (by simpa [rr, T, threadFirstEdge, hrFirst,
                        Sym2.eq_swap] using hTval)
                      (by
                        have hn : base U ≠ none := by rw [hUval]; simp
                        simpa [U] using hn)
                      (by
                        have hn : base W ≠ none := by rw [hWval]; simp
                        simpa [W] using hn)
                      (by simpa [h, A] using hA)
                      (by simpa [h, B] using hB)
                      (Or.inr (by simpa [g, D, threadLastEdge,
                        Sym2.eq_swap] using hDval))
                      (by simpa [rr, T, Dset, threadFirstEdge, hrFirst,
                        Sym2.eq_swap] using hTD)
                      (by simpa [h, rr, P, T, threadFirstEdge, hrFirst,
                        Sym2.eq_swap] using hPT)
                      (by simpa [g, D, P, threadFirstEdge, threadLastEdge,
                        Sym2.eq_swap] using hDP)

/-- External data at the common centre after the first edge of the displayed
2-thread has become matching.  The third arm is a zero-thread. -/
theorem longPair_twoThreadFirst_external_data_twoZero
    {u v₁ v₂ v₃ z x t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : ZeroThreadCore G u x)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (colour : G.edgeSet → OneTwoColor 4) (d i : Fin 4)
    (hQ : colour (threadFirstEdge G q hq) = none)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = some d)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some i) :
    ExternalEdgesInduced G colour u (threadFirstEdge G q hq) ∧
      ExternalInducedColors G colour u (threadFirstEdge G q hq) = {d, i} := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hTQ : T ≠ Q := by
    simpa [T, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G r.adj
        hq.first_step_adj hqx.symm
  have classify (f : G.edgeSet) (huf : u ∈ (f : Sym2 V)) :
      f = P ∨ f = T ∨ f = Q := by
    obtain ⟨y, hfy⟩ := Sym2.mem_iff_exists.mp huf
    have huy : G.Adj u y := by
      have hf := f.2
      rw [hfy] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        hq.first_step_adj r.adj hvq hvx hqx huy with rfl | rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa [P, Sym2.eq_swap] using hfy))
    · exact Or.inr (Or.inr
        (Subtype.ext (by simpa [Q, threadFirstEdge] using hfy)))
    · exact Or.inr (Or.inl
        (Subtype.ext (by simpa [T, Sym2.eq_swap] using hfy)))
  constructor
  · intro f hfext
    rcases classify f hfext.1 with rfl | rfl | rfl
    · exact ⟨d, by simpa [P] using hP⟩
    · exact ⟨i, by simpa [T] using hT⟩
    · exact False.elim (hfext.2 rfl)
  · ext a
    constructor
    · rintro ⟨f, hfext, hfa⟩
      rcases classify f hfext.1 with rfl | rfl | rfl
      · have hfaP : colour P = some a := by simpa [P] using hfa
        have had : a = d := Option.some.inj
          (hfaP.symm.trans (by simpa [P] using hP))
        simp [had]
      · have hfaT : colour T = some a := by simpa [T] using hfa
        have hai : a = i := Option.some.inj
          (hfaT.symm.trans (by simpa [T] using hT))
        simp [hai]
      · exact False.elim (hfext.2 rfl)
    · intro ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact ⟨P, ⟨by simp [P], hPQ⟩, by simpa [P] using hP⟩
      · exact ⟨T, ⟨by simp [T], hTQ⟩, by simpa [T] using hT⟩

/-- If the terminal edge of the 2-thread has the colour displayed on the
induced far edge of the zero-thread, a full-palette obstruction forces the
two centre colours at the far endpoint.  Moving that terminal colour inward
then exposes the already proved selected-edge swap. -/
theorem longPair_hasGoodFour_of_twoZero_terminal_farColour_full
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x) (htx : t ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m k : Fin 4)
    (hij : i ≠ j) (him : i ≠ m) (hik : i ≠ k)
    (hjm : j ≠ m) (hjk : j ≠ k) (hmk : m ≠ k)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (no320ThreadMiddleEdge G q hq) = none)
    (hD : colour (threadLastEdge G q hq) = some m)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : threadLastEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hret : ∀ f, IsExternalAt G t (threadLastEdge G q hq) f →
      f ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hall : ∀ c : Fin 4, VertexSeesInduced G
      (recolor G colour (threadFirstEdge G q hq) (some k))
        (q.getVert 2) c) :
    HasGoodFour G := by
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let Vedge : G.edgeSet := ⟨s(x, b), hb⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  have hvalid : IsOneTwoColoringOn G Dset colour := by
    simpa [Dset] using hprepared.1
  have hfar := full_second_palette_after_fresh_far_normal_form_twoTwo
    G hsub g Dset colour hvalid hprepared.2.2.1 i j m k hij him hik
      hjm hjk hmk
      (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQ)
      (by simpa [g, C, no320ThreadMiddleEdge] using hC)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hD)
      (by simpa [g, D, Dset, threadLastEdge, Sym2.eq_swap] using hDD)
      (by
        intro f hf
        exact hret f (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hf))
      (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hall)
  let inner : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some m)) D none
  have hcenter : ExternalInducedColors G colour u P = {i, j} := by
    simpa [P, Q, T, g, threadFirstEdge, Sym2.eq_swap] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        h.first_adj hq.first_step_adj r.adj hvq hvx hqx colour i j
          hP (by simpa [threadFirstEdge, Sym2.eq_swap] using hQ) hT
  have hmCenter : m ∉ ExternalInducedColors G colour u P := by
    rw [hcenter]
    simp [him.symm, hjm.symm]
  have hpreparedInner : PreparedThreeThreadGap G h inner := by
    exact longPair_prepared_shift_twoThreadTail_twoTwo G h g colour
      hprepared m hP
      (by simpa [g, C, no320ThreadMiddleEdge] using hC)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hD)
      (by simpa [g, C, Dset, no320ThreadMiddleEdge] using hCD)
      (by simpa [g, D, Dset, threadLastEdge, Sym2.eq_swap] using hDD)
      (by simpa [P] using hmCenter)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hfar.1)
  have hCP : C ≠ P := by
    simpa [C, P, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.start_three g.middle_adj h.first_adj.symm
  have hCR : C ≠ R := by
    simpa [C, R, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.end_three g.middle_adj h.last_adj
  have hCQ : C ≠ Q := by
    simpa [C, Q, g, no320ThreadMiddleEdge, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        g.start_three g.middle_adj g.first_adj.symm
  have hCT : C ≠ T := by
    simpa [C, T, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        r.start_three g.middle_adj r.adj.symm
  have hDQ : D ≠ Q := by
    simpa [D, Q, g, threadLastEdge, threadFirstEdge, Sym2.eq_swap] using
      (twoThreadCore_firstEdge_ne_lastEdge G g).symm
  have hDP' : D ≠ P := by simpa [D, P] using hDP
  have hDR : D ≠ R := by
    intro heq
    have he : some m = none := hD.symm.trans ((congrArg colour heq).trans hR)
    simp at he
  have hDT : D ≠ T := by
    intro heq
    have he : some m = some j := hD.symm.trans ((congrArg colour heq).trans hT)
    exact hjm (Option.some.inj he).symm
  have hCDne : C ≠ D := by
    simpa [C, D, g, no320ThreadMiddleEdge, threadLastEdge, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hinnerP : inner P = none := by
    rw [show inner P = colour P by simp [inner, hCP.symm, hDP'.symm]]
    simpa [P] using hP
  have hinnerR : inner R = none := by
    rw [show inner R = colour R by simp [inner, hCR.symm, hDR.symm]]
    simpa [R] using hR
  have hinnerQ : inner Q = some i := by
    rw [show inner Q = colour Q by simp [inner, hCQ.symm, hDQ.symm]]
    simpa [Q] using hQ
  have hinnerT : inner T = some j := by
    rw [show inner T = colour T by simp [inner, hCT.symm, hDT.symm]]
    simpa [T] using hT
  have hinnerC : inner C = some m := by simp [inner, hCDne]
  have hinnerD : inner D = none := by simp [inner]
  have hADset : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBDset : B ∉ Dset := by
    simpa [B, Dset] using right_chain_edge_not_retained G h.right_adj
  have hAC : A ≠ C := fun heq ↦ hADset (heq ▸ (by simpa [Dset, C] using hCD))
  have hADedge : A ≠ D := fun heq ↦ hADset (heq ▸ (by simpa [Dset, D] using hDD))
  have hBC : B ≠ C := fun heq ↦ hBDset (heq ▸ (by simpa [Dset, C] using hCD))
  have hBDedge : B ≠ D := fun heq ↦ hBDset (heq ▸ (by simpa [Dset, D] using hDD))
  have hinnerA : inner A = none := by simp [inner, hAC, hADedge, A, hA]
  have hinnerB : inner B = none := by simp [inner, hBC, hBDedge, B, hB]
  have hUC : U ≠ C := by
    intro heq
    have hxC : x ∈ (C : Sym2 V) := by rw [← heq]; simp [U]
    have hxcase : x = q.getVert 1 ∨ x = q.getVert 2 := by
      simpa [C, no320ThreadMiddleEdge] using hxC
    exact hxcase.elim
      (isThreeVertex_ne_isTwoVertex G r.end_three g.first_two)
      (isThreeVertex_ne_isTwoVertex G r.end_three g.second_two)
  have hUDedge : U ≠ D := by
    intro heq
    have he : none = some m := hU.symm.trans ((congrArg colour heq).trans hD)
    simp at he
  have hVC : Vedge ≠ C := by
    intro heq
    have he : some m = none := hV.symm.trans ((congrArg colour heq).trans hC)
    simp at he
  have hVDedge : Vedge ≠ D := by
    intro heq
    have hxD : x ∈ (D : Sym2 V) := by rw [← heq]; simp [Vedge]
    have hxcase : x = q.getVert 2 ∨ x = t := by
      simpa [D, threadLastEdge] using hxD
    exact hxcase.elim
      (isThreeVertex_ne_isTwoVertex G r.end_three g.second_two)
      htx.symm
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G inner P (some i)) Q none
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hvx
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj r.adj hqx
  have hcriticalQ : critical Q = none := by simp [critical]
  have hcriticalP : critical P = some i := by simp [critical, hPQ]
  have hcriticalT : critical T = some j := by
    simp [critical, hPT.symm, hQT.symm, hinnerT]
  have hcriticalStart := longPair_twoThreadFirst_external_data_twoZero
    G h r q hq hvq hvx hqx critical i j hcriticalQ hcriticalP hcriticalT
  have hmissFar : ∀ e, IsExternalAt G t D e →
      e ∉ ({C, D, P, Q} : Set G.edgeSet) := by
    intro e hext heS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heS
    rcases heS with rfl | rfl | rfl | rfl
    · have htcase : t = q.getVert 1 ∨ t = q.getVert 2 := by
        simpa [C, no320ThreadMiddleEdge] using hext.1
      exact htcase.elim
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.first_two)
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.second_two)
    · exact hext.2 rfl
    · have htcase : t = v₁ ∨ t = u := by simpa [P] using hext.1
      exact htcase.elim
        (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two)
        (IsKThread.endpoints_ne G hq).symm
    · have htcase : t = u ∨ t = q.getVert 1 := by
        simpa [Q, threadFirstEdge] using hext.1
      exact htcase.elim (IsKThread.endpoints_ne G hq).symm
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.first_two)
  have hagreeCritical : ColoringsAgreeOff G
      ({C, D, P, Q} : Set G.edgeSet) colour critical := by
    intro e he
    have hne : e ≠ C ∧ e ≠ D ∧ e ≠ P ∧ e ≠ Q := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using he
    simp [critical, inner, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2]
  have hcriticalFarEdges : ExternalEdgesInduced G critical t D :=
    externalEdgesInduced_of_agreeOff G hagreeCritical hmissFar hfar.1
  have hcriticalFarPalette : ExternalInducedColors G critical t D = {i, j} := by
    have heq := externalInducedColors_eq_of_agreeOff G hagreeCritical hmissFar
    rw [← heq]
    exact hfar.2
  have hcriticalData :
      ExternalEdgesInduced G critical u Q ∧
        ExternalEdgesInduced G critical t D ∧
        ExternalInducedColors G critical u Q =
          ExternalInducedColors G critical t D :=
    ⟨hcriticalStart.1, hcriticalFarEdges,
      hcriticalStart.2.trans hcriticalFarPalette.symm⟩
  exact longPair_hasGoodFour_of_twoThread_middle_induced_alt_twoZero
    G hsub h q hq r hvq hvx hqx ha hb hNfar inner hpreparedInner
      k j i hinnerP hinnerR hinnerT hinnerQ
      (by simpa [C, hinnerC] using hmk)
      (by simpa [C, hinnerC])
      (by simp [inner, hUC, hUDedge, U, hU])
      (by simp [inner, hVC, hVDedge, Vedge, hV, hmk])
      (by simpa [A] using hinnerA) (by simpa [B] using hinnerB)
      hPD hQD hDP hRP hRQ hjk.symm hik.symm hcriticalData

/-- After the usual terminal shift on a 2-thread, swapping its first edge
with the selected matching edge closes the gap whenever the resulting
centre palette differs from the unchanged far palette. -/
theorem longPair_hasGoodFour_after_twoThreadTail_shift_and_selected_swap_twoZero
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j k : Fin 4) (hkj : k ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (no320ThreadMiddleEdge G q hq) = none)
    (hD : colour (threadLastEdge G q hq) = some k)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : threadLastEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hfarEdges : ExternalEdgesInduced G colour t (threadLastEdge G q hq))
    (hfarNe : ({i, j} : Set (Fin 4)) ≠
      ExternalInducedColors G colour t (threadLastEdge G q hq)) :
    HasGoodFour G := by
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  let inner : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some k)) D none
  have hpreparedInner : PreparedThreeThreadGap G h inner := by
    exact longPair_prepared_shift_twoThreadTail_twoTwo G h g colour
      hprepared k hP
      (by simpa [g, C, no320ThreadMiddleEdge] using hC)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hD)
      (by simpa [g, C, Dset, no320ThreadMiddleEdge] using hCD)
      (by simpa [g, D, Dset, threadLastEdge, Sym2.eq_swap] using hDD)
      (by simpa [P] using hk)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hfarEdges)
  have hCP : C ≠ P := by
    simpa [C, P, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.start_three g.middle_adj h.first_adj.symm
  have hCR : C ≠ R := by
    simpa [C, R, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.end_three g.middle_adj h.last_adj
  have hCQ : C ≠ Q := by
    simpa [C, Q, g, no320ThreadMiddleEdge, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        g.start_three g.middle_adj g.first_adj.symm
  have hCT : C ≠ T := by
    simpa [C, T, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        r.start_three g.middle_adj r.adj.symm
  have hDQ : D ≠ Q := by
    simpa [D, Q, g, threadLastEdge, threadFirstEdge, Sym2.eq_swap] using
      (twoThreadCore_firstEdge_ne_lastEdge G g).symm
  have hDP' : D ≠ P := by simpa [D, P] using hDP
  have hDR : D ≠ R := by
    intro heq
    have he : some k = none := hD.symm.trans ((congrArg colour heq).trans hR)
    simp at he
  have hDT : D ≠ T := by
    intro heq
    have he : some k = some j := hD.symm.trans ((congrArg colour heq).trans hT)
    exact hkj (Option.some.inj he)
  have hCDne : C ≠ D := by
    simpa [C, D, g, no320ThreadMiddleEdge, threadLastEdge, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hinnerP : inner P = none := by
    rw [show inner P = colour P by simp [inner, hCP.symm, hDP'.symm]]
    simpa [P] using hP
  have hinnerR : inner R = none := by
    rw [show inner R = colour R by simp [inner, hCR.symm, hDR.symm]]
    simpa [R] using hR
  have hinnerQ : inner Q = some i := by
    rw [show inner Q = colour Q by simp [inner, hCQ.symm, hDQ.symm]]
    simpa [Q] using hQ
  have hinnerT : inner T = some j := by
    rw [show inner T = colour T by simp [inner, hCT.symm, hDT.symm]]
    simpa [T] using hT
  have hinnerC : inner C = some k := by simp [inner, hCDne]
  have hinnerD : inner D = none := by simp [inner]
  have hADset : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBDset : B ∉ Dset := by
    simpa [B, Dset] using right_chain_edge_not_retained G h.right_adj
  have hAC : A ≠ C := fun heq ↦ hADset (heq ▸ (by simpa [Dset, C] using hCD))
  have hADedge : A ≠ D := fun heq ↦ hADset (heq ▸ (by simpa [Dset, D] using hDD))
  have hBC : B ≠ C := fun heq ↦ hBDset (heq ▸ (by simpa [Dset, C] using hCD))
  have hBDedge : B ≠ D := fun heq ↦ hBDset (heq ▸ (by simpa [Dset, D] using hDD))
  have hinnerA : inner A = none := by simp [inner, hAC, hADedge, A, hA]
  have hinnerB : inner B = none := by simp [inner, hBC, hBDedge, B, hB]
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hvx
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj r.adj hqx
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G inner P (some i)) Q none
  have hfinalQ : final Q = none := by simp [final]
  have hfinalP : final P = some i := by simp [final, hPQ]
  have hfinalT : final T = some j := by
    simp [final, hPT.symm, hQT.symm, hinnerT]
  have hstart := longPair_twoThreadFirst_external_data_twoZero
    G h r q hq hvq hvx hqx final i j hfinalQ hfinalP hfinalT
  have hmissFar : ∀ e, IsExternalAt G t D e →
      e ∉ ({C, D, P, Q} : Set G.edgeSet) := by
    intro e hext heS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heS
    rcases heS with rfl | rfl | rfl | rfl
    · have htcase : t = q.getVert 1 ∨ t = q.getVert 2 := by
        simpa [C, no320ThreadMiddleEdge] using hext.1
      exact htcase.elim
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.first_two)
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.second_two)
    · exact hext.2 rfl
    · have htcase : t = v₁ ∨ t = u := by simpa [P] using hext.1
      exact htcase.elim
        (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two)
        (IsKThread.endpoints_ne G hq).symm
    · have htcase : t = u ∨ t = q.getVert 1 := by
        simpa [Q, threadFirstEdge] using hext.1
      exact htcase.elim (IsKThread.endpoints_ne G hq).symm
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.first_two)
  have hagree : ColoringsAgreeOff G ({C, D, P, Q} : Set G.edgeSet)
      colour final := by
    intro e he
    have hne : e ≠ C ∧ e ≠ D ∧ e ≠ P ∧ e ≠ Q := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using he
    simp [final, inner, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2]
  have hfarFinalEdges : ExternalEdgesInduced G final t D :=
    externalEdgesInduced_of_agreeOff G hagree hmissFar hfarEdges
  have hfarPalEq : ExternalInducedColors G colour t D =
      ExternalInducedColors G final t D :=
    externalInducedColors_eq_of_agreeOff G hagree hmissFar
  have hcritical : ConditionThreeAtTwoThread G q hq final := by
    intro _ _
    intro heq
    apply hfarNe
    calc
      ({i, j} : Set (Fin 4)) = ExternalInducedColors G final u Q :=
        hstart.2.symm
      _ = ExternalInducedColors G final t D := heq
      _ = ExternalInducedColors G colour t D := hfarPalEq.symm
  have hpreparedFinal : PreparedThreeThreadGap G h final := by
    simpa [final, P, Q] using
      longPair_preparedThreeThreadGap_swap_selectedOuter_twoThreadFirst
        G hsub h q hq inner hpreparedInner i
          (by simpa [P] using hinnerP)
          (by simpa [Q] using hinnerQ)
          (by simpa [C, no320ThreadMiddleEdge] using
            (show inner C ≠ none by rw [hinnerC]; simp))
          (by simpa [A] using hinnerA) (by simpa [B] using hinnerB)
          hQD hPQ hDP hcritical
  have hfinalR : final R = none := by
    simp [final, R, P, Q, hRP, hRQ, hinnerR]
  have hAP : A ≠ P := fun heq ↦ hADset (heq ▸ (by simpa [Dset, P] using hPD))
  have hAQ : A ≠ Q := fun heq ↦ hADset (heq ▸ (by simpa [Dset, Q] using hQD))
  have hBP : B ≠ P := fun heq ↦ hBDset (heq ▸ (by simpa [Dset, P] using hPD))
  have hBQ : B ≠ Q := fun heq ↦ hBDset (heq ▸ (by simpa [Dset, Q] using hQD))
  have hfinalA : final A = none := by
    simp [final, hAP, hAQ, hinnerA]
  have hfinalB : final B = none := by
    simp [final, hBP, hBQ, hinnerB]
  apply longPair_hasGoodFour_of_prepared_left_outer_induced
    G hsub h final hpreparedFinal
      (by simpa [P, hfinalP]) (by simpa [R] using hfinalR)
      (by simpa [A] using hfinalA) (by simpa [B] using hfinalB)
      Q hfinalQ
  · simp [Q, threadFirstEdge]
  · exact hAQ.symm
  · exact hBQ.symm

/-- The fourth terminal colour with far palette equal to the two centre
colours is closed by the terminal shift, followed by the already packaged
middle-colour change and alternate selected-edge swap. -/
theorem longPair_hasGoodFour_of_twoZero_terminal_complement_far_centerPair
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x) (htx : t ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m k : Fin 4)
    (hij : i ≠ j) (him : i ≠ m) (hik : i ≠ k)
    (hjm : j ≠ m) (hjk : j ≠ k) (hmk : m ≠ k)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (no320ThreadMiddleEdge G q hq) = none)
    (hD : colour (threadLastEdge G q hq) = some k)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : threadLastEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hfarEdges : ExternalEdgesInduced G colour t (threadLastEdge G q hq))
    (hfarPal : ExternalInducedColors G colour t (threadLastEdge G q hq) =
      {i, j}) :
    HasGoodFour G := by
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let Vedge : G.edgeSet := ⟨s(x, b), hb⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  have hcenter : ExternalInducedColors G colour u P = {i, j} := by
    simpa [P, Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        h.first_adj hq.first_step_adj r.adj hvq hvx hqx colour i j hP
          (by simpa [threadFirstEdge, Sym2.eq_swap] using hQ) hT
  have hkCenter : k ∉ ExternalInducedColors G colour u P := by
    rw [hcenter]
    simp [hik.symm, hjk.symm]
  let inner : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some k)) D none
  have hpreparedInner : PreparedThreeThreadGap G h inner := by
    exact longPair_prepared_shift_twoThreadTail_twoTwo G h g colour
      hprepared k hP
      (by simpa [g, C, no320ThreadMiddleEdge] using hC)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hD)
      (by simpa [g, C, Dset, no320ThreadMiddleEdge] using hCD)
      (by simpa [g, D, Dset, threadLastEdge, Sym2.eq_swap] using hDD)
      (by simpa [P] using hkCenter)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hfarEdges)
  have hCP : C ≠ P := by
    simpa [C, P, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.start_three g.middle_adj h.first_adj.symm
  have hCR : C ≠ R := by
    simpa [C, R, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.end_three g.middle_adj h.last_adj
  have hCQ : C ≠ Q := by
    simpa [C, Q, g, no320ThreadMiddleEdge, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        g.start_three g.middle_adj g.first_adj.symm
  have hCT : C ≠ T := by
    simpa [C, T, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        r.start_three g.middle_adj r.adj.symm
  have hDQ : D ≠ Q := by
    simpa [D, Q, g, threadLastEdge, threadFirstEdge, Sym2.eq_swap] using
      (twoThreadCore_firstEdge_ne_lastEdge G g).symm
  have hDP' : D ≠ P := by simpa [D, P] using hDP
  have hDR : D ≠ R := by
    intro heq
    have he : some k = none := hD.symm.trans ((congrArg colour heq).trans hR)
    simp at he
  have hDT : D ≠ T := by
    intro heq
    have he : some k = some j := hD.symm.trans ((congrArg colour heq).trans hT)
    exact hjk (Option.some.inj he).symm
  have hCDne : C ≠ D := by
    simpa [C, D, g, no320ThreadMiddleEdge, threadLastEdge, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hinnerP : inner P = none := by
    rw [show inner P = colour P by simp [inner, hCP.symm, hDP'.symm]]
    simpa [P] using hP
  have hinnerR : inner R = none := by
    rw [show inner R = colour R by simp [inner, hCR.symm, hDR.symm]]
    simpa [R] using hR
  have hinnerQ : inner Q = some i := by
    rw [show inner Q = colour Q by simp [inner, hCQ.symm, hDQ.symm]]
    simpa [Q] using hQ
  have hinnerT : inner T = some j := by
    rw [show inner T = colour T by simp [inner, hCT.symm, hDT.symm]]
    simpa [T] using hT
  have hinnerC : inner C = some k := by simp [inner, hCDne]
  have hADset : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBDset : B ∉ Dset := by
    simpa [B, Dset] using right_chain_edge_not_retained G h.right_adj
  have hAC : A ≠ C := fun heq ↦ hADset (heq ▸ (by simpa [Dset, C] using hCD))
  have hADedge : A ≠ D := fun heq ↦ hADset (heq ▸ (by simpa [Dset, D] using hDD))
  have hBC : B ≠ C := fun heq ↦ hBDset (heq ▸ (by simpa [Dset, C] using hCD))
  have hBDedge : B ≠ D := fun heq ↦ hBDset (heq ▸ (by simpa [Dset, D] using hDD))
  have hinnerA : inner A = none := by simp [inner, hAC, hADedge, A, hA]
  have hinnerB : inner B = none := by simp [inner, hBC, hBDedge, B, hB]
  have hUC : U ≠ C := by
    intro heq
    have hxC : x ∈ (C : Sym2 V) := by rw [← heq]; simp [U]
    have hxcase : x = q.getVert 1 ∨ x = q.getVert 2 := by
      simpa [C, no320ThreadMiddleEdge] using hxC
    exact hxcase.elim
      (isThreeVertex_ne_isTwoVertex G r.end_three g.first_two)
      (isThreeVertex_ne_isTwoVertex G r.end_three g.second_two)
  have hUDedge : U ≠ D := by
    intro heq
    have he : none = some k := hU.symm.trans ((congrArg colour heq).trans hD)
    simp at he
  have hVC : Vedge ≠ C := by
    intro heq
    have he : some m = none := hV.symm.trans ((congrArg colour heq).trans hC)
    simp at he
  have hVDedge : Vedge ≠ D := by
    intro heq
    have hxD : x ∈ (D : Sym2 V) := by rw [← heq]; simp [Vedge]
    have hxcase : x = q.getVert 2 ∨ x = t := by
      simpa [D, threadLastEdge] using hxD
    exact hxcase.elim
      (isThreeVertex_ne_isTwoVertex G r.end_three g.second_two)
      htx.symm
  have hinnerU : inner U = none := by
    simp [inner, hUC, hUDedge, U, hU]
  have hinnerV : inner Vedge = some m := by
    simp [inner, hVC, hVDedge, Vedge, hV]
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G inner P (some i)) Q none
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hvx
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj r.adj hqx
  have hcriticalQ : critical Q = none := by simp [critical]
  have hcriticalP : critical P = some i := by simp [critical, hPQ]
  have hcriticalT : critical T = some j := by
    simp [critical, hPT.symm, hQT.symm, hinnerT]
  have hcriticalStart := longPair_twoThreadFirst_external_data_twoZero
    G h r q hq hvq hvx hqx critical i j hcriticalQ hcriticalP hcriticalT
  have hmissFar : ∀ e, IsExternalAt G t D e →
      e ∉ ({C, D, P, Q} : Set G.edgeSet) := by
    intro e hext heS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heS
    rcases heS with rfl | rfl | rfl | rfl
    · have htcase : t = q.getVert 1 ∨ t = q.getVert 2 := by
        simpa [C, no320ThreadMiddleEdge] using hext.1
      exact htcase.elim
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.first_two)
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.second_two)
    · exact hext.2 rfl
    · have htcase : t = v₁ ∨ t = u := by simpa [P] using hext.1
      exact htcase.elim
        (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two)
        (IsKThread.endpoints_ne G hq).symm
    · have htcase : t = u ∨ t = q.getVert 1 := by
        simpa [Q, threadFirstEdge] using hext.1
      exact htcase.elim (IsKThread.endpoints_ne G hq).symm
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.first_two)
  have hagreeCritical : ColoringsAgreeOff G
      ({C, D, P, Q} : Set G.edgeSet) colour critical := by
    intro e he
    have hne : e ≠ C ∧ e ≠ D ∧ e ≠ P ∧ e ≠ Q := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using he
    simp [critical, inner, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2]
  have hcriticalFarEdges : ExternalEdgesInduced G critical t D :=
    externalEdgesInduced_of_agreeOff G hagreeCritical hmissFar hfarEdges
  have hcriticalFarPalette : ExternalInducedColors G critical t D = {i, j} := by
    have heq := externalInducedColors_eq_of_agreeOff G hagreeCritical hmissFar
    rw [← heq]
    exact hfarPal
  have hcriticalData :
      ExternalEdgesInduced G critical u Q ∧
        ExternalEdgesInduced G critical t D ∧
        ExternalInducedColors G critical u Q =
          ExternalInducedColors G critical t D :=
    ⟨hcriticalStart.1, hcriticalFarEdges,
      hcriticalStart.2.trans hcriticalFarPalette.symm⟩
  exact longPair_hasGoodFour_of_twoThread_middle_induced_distinct_twoZero
    G hsub h q hq r hvq hvx hqx ha hb hNfar inner hpreparedInner
      j i k m hjm.symm him.symm hmk hjk.symm hik.symm
      hinnerP hinnerR hinnerT hinnerQ hinnerC hinnerU hinnerV
      hinnerA hinnerB hPD hQD hCD hDP hRP hRQ hcriticalData

/-- If the terminal edge has the centre-zero colour, the full-palette
obstruction gives the far palette `{i,m}`.  The different-colour terminal
shift puts the fourth colour on the middle edge; the ordinary selected/first
swap then has unequal endpoint palettes and closes the gap. -/
theorem longPair_hasGoodFour_of_twoZero_terminal_centerColour_full
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m k : Fin 4)
    (hij : i ≠ j) (him : i ≠ m) (hik : i ≠ k)
    (hjm : j ≠ m) (hjk : j ≠ k) (hmk : m ≠ k)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (no320ThreadMiddleEdge G q hq) = none)
    (hD : colour (threadLastEdge G q hq) = some j)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : threadLastEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hfarEdges : ExternalEdgesInduced G colour t (threadLastEdge G q hq))
    (hfarPal : ExternalInducedColors G colour t (threadLastEdge G q hq) =
      {i, m}) :
    HasGoodFour G := by
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  have hcenter : ExternalInducedColors G colour u P = {i, j} := by
    simpa [P, Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        h.first_adj hq.first_step_adj r.adj hvq hvx hqx colour i j hP
          (by simpa [threadFirstEdge, Sym2.eq_swap] using hQ) hT
  have hkCenter : k ∉ ExternalInducedColors G colour u P := by
    rw [hcenter]
    simp [hik.symm, hjk.symm]
  have hkFar : k ∉ ExternalInducedColors G colour t D := by
    rw [show ExternalInducedColors G colour t D = {i, m} by
      simpa [D] using hfarPal]
    simp [hik.symm, hmk.symm]
  let inner : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some k)) D none
  have hpreparedInner : PreparedThreeThreadGap G h inner := by
    exact longPair_prepared_shift_twoThreadTail_fresh G hsub h g colour
      hprepared i j m k hij hjk.symm hjm hP
      (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQ)
      (by simpa [g, C, no320ThreadMiddleEdge] using hC)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hD)
      (by simpa [g, C, no320ThreadMiddleEdge] using hCD)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hDD)
      (by simpa [P] using hkCenter)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hkFar)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hfarEdges)
      (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hfarPal)
  have hCP : C ≠ P := by
    simpa [C, P, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.start_three g.middle_adj h.first_adj.symm
  have hCR : C ≠ R := by
    simpa [C, R, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.end_three g.middle_adj h.last_adj
  have hCQ : C ≠ Q := by
    simpa [C, Q, g, no320ThreadMiddleEdge, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        g.start_three g.middle_adj g.first_adj.symm
  have hCT : C ≠ T := by
    simpa [C, T, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        r.start_three g.middle_adj r.adj.symm
  have hDQ : D ≠ Q := by
    simpa [D, Q, g, threadLastEdge, threadFirstEdge, Sym2.eq_swap] using
      (twoThreadCore_firstEdge_ne_lastEdge G g).symm
  have hDP' : D ≠ P := by simpa [D, P] using hDP
  have hDR : D ≠ R := by
    intro heq
    have he : some j = none := hD.symm.trans ((congrArg colour heq).trans hR)
    simp at he
  have hDT : D ≠ T := by
    intro heq
    have hval : s(q.getVert 2, t) = s(x, u) := by
      simpa [D, T, threadLastEdge] using congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact (isThreeVertex_ne_isTwoVertex G r.end_three g.second_two)
        hval.1.symm
    · exact (isThreeVertex_ne_isTwoVertex G h.start_three g.second_two)
        hval.1.symm
  have hCDne : C ≠ D := by
    simpa [C, D, g, no320ThreadMiddleEdge, threadLastEdge, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hinnerP : inner P = none := by
    rw [show inner P = colour P by simp [inner, hCP.symm, hDP'.symm]]
    simpa [P] using hP
  have hinnerR : inner R = none := by
    rw [show inner R = colour R by simp [inner, hCR.symm, hDR.symm]]
    simpa [R] using hR
  have hinnerQ : inner Q = some i := by
    rw [show inner Q = colour Q by simp [inner, hCQ.symm, hDQ.symm]]
    simpa [Q] using hQ
  have hinnerT : inner T = some j := by
    rw [show inner T = colour T by simp [inner, hCT.symm, hDT.symm]]
    simpa [T] using hT
  have hinnerC : inner C = some k := by simp [inner, hCDne]
  have hADset : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBDset : B ∉ Dset := by
    simpa [B, Dset] using right_chain_edge_not_retained G h.right_adj
  have hAC : A ≠ C := fun heq ↦
    hADset (heq ▸ (by simpa [Dset, C] using hCD))
  have hADedge : A ≠ D := fun heq ↦
    hADset (heq ▸ (by simpa [Dset, D] using hDD))
  have hBC : B ≠ C := fun heq ↦
    hBDset (heq ▸ (by simpa [Dset, C] using hCD))
  have hBDedge : B ≠ D := fun heq ↦
    hBDset (heq ▸ (by simpa [Dset, D] using hDD))
  have hinnerA : inner A = none := by simp [inner, hAC, hADedge, A, hA]
  have hinnerB : inner B = none := by simp [inner, hBC, hBDedge, B, hB]
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hvx
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj r.adj hqx
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G inner P (some i)) Q none
  have hfinalQ : final Q = none := by simp [final]
  have hfinalP : final P = some i := by simp [final, hPQ]
  have hfinalT : final T = some j := by
    simp [final, hPT.symm, hQT.symm, hinnerT]
  have hstart := longPair_twoThreadFirst_external_data_twoZero
    G h r q hq hvq hvx hqx final i j hfinalQ hfinalP hfinalT
  have hmissFar : ∀ e, IsExternalAt G t D e →
      e ∉ ({C, D, P, Q} : Set G.edgeSet) := by
    intro e hext heS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heS
    rcases heS with rfl | rfl | rfl | rfl
    · have htcase : t = q.getVert 1 ∨ t = q.getVert 2 := by
        simpa [C, no320ThreadMiddleEdge] using hext.1
      exact htcase.elim
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.first_two)
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.second_two)
    · exact hext.2 rfl
    · have htcase : t = v₁ ∨ t = u := by simpa [P] using hext.1
      exact htcase.elim
        (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two)
        (IsKThread.endpoints_ne G hq).symm
    · have htcase : t = u ∨ t = q.getVert 1 := by
        simpa [Q, threadFirstEdge] using hext.1
      exact htcase.elim (IsKThread.endpoints_ne G hq).symm
        (isThreeVertex_ne_isTwoVertex G hq.end_three g.first_two)
  have hagree : ColoringsAgreeOff G ({C, D, P, Q} : Set G.edgeSet)
      colour final := by
    intro e he
    have hne : e ≠ C ∧ e ≠ D ∧ e ≠ P ∧ e ≠ Q := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using he
    simp [final, inner, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2]
  have hfarFinalEdges : ExternalEdgesInduced G final t D :=
    externalEdgesInduced_of_agreeOff G hagree hmissFar hfarEdges
  have hfarPalEq : ExternalInducedColors G colour t D =
      ExternalInducedColors G final t D :=
    externalInducedColors_eq_of_agreeOff G hagree hmissFar
  have hcritical : ConditionThreeAtTwoThread G q hq final := by
    intro _ _
    intro heq
    have hne : ({i, j} : Set (Fin 4)) ≠ {i, m} := by
      intro hpair
      have : j ∈ ({i, m} : Set (Fin 4)) := by rw [← hpair]; simp
      simpa [hij.symm, hjm] using this
    apply hne
    calc
      ({i, j} : Set (Fin 4)) = ExternalInducedColors G final u Q :=
        hstart.2.symm
      _ = ExternalInducedColors G final t D := heq
      _ = ExternalInducedColors G colour t D := hfarPalEq.symm
      _ = {i, m} := by simpa [D] using hfarPal
  have hpreparedFinal : PreparedThreeThreadGap G h final := by
    simpa [final, P, Q] using
      longPair_preparedThreeThreadGap_swap_selectedOuter_twoThreadFirst
        G hsub h q hq inner hpreparedInner i
          (by simpa [P] using hinnerP)
          (by simpa [Q] using hinnerQ)
          (by simpa [C, no320ThreadMiddleEdge] using
            (show inner C ≠ none by rw [hinnerC]; simp))
          (by simpa [A] using hinnerA) (by simpa [B] using hinnerB)
          hQD hPQ hDP hcritical
  have hfinalR : final R = none := by
    simp [final, R, P, Q, hRP, hRQ, hinnerR]
  have hAP : A ≠ P := fun heq ↦
    hADset (heq ▸ (by simpa [Dset, P] using hPD))
  have hAQ : A ≠ Q := fun heq ↦
    hADset (heq ▸ (by simpa [Dset, Q] using hQD))
  have hBP : B ≠ P := fun heq ↦
    hBDset (heq ▸ (by simpa [Dset, P] using hPD))
  have hBQ : B ≠ Q := fun heq ↦
    hBDset (heq ▸ (by simpa [Dset, Q] using hQD))
  have hfinalA : final A = none := by simp [final, hAP, hAQ, hinnerA]
  have hfinalB : final B = none := by simp [final, hBP, hBQ, hinnerB]
  apply longPair_hasGoodFour_of_prepared_left_outer_induced
    G hsub h final hpreparedFinal
      (by simpa [P, hfinalP]) (by simpa [R] using hfinalR)
      (by simpa [A] using hfinalA) (by simpa [B] using hfinalB)
      Q hfinalQ
  · simp [Q, threadFirstEdge]
  · exact hAQ.symm
  · exact hBQ.symm

/-- Dispatcher for the matching middle-edge normal form.  The only branch
left abstract here is the one in which the terminal edge receives the fourth
colour; the other two terminal colours are discharged by the fresh-first-edge
recolouring and its full-palette normal form. -/
theorem longPair_hasGoodFour_of_twoZero_middle_matching_of_complement
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x) (htx : t ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b) (hbu : b ≠ u)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m k : Fin 4)
    (hij : i ≠ j) (him : i ≠ m) (hik : i ≠ k)
    (hjm : j ≠ m) (hjk : j ≠ k) (hmk : m ≠ k)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (no320ThreadMiddleEdge G q hq) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : threadLastEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hVD : (⟨s(x, b), hb⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzQ : z ∉ (threadFirstEdge G q hq : Sym2 V))
    (hret : ∀ f, IsExternalAt G t (threadLastEdge G q hq) f →
      f ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hcomplement : colour (threadLastEdge G q hq) = some k →
      HasGoodFour G) :
    HasGoodFour G := by
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  have hvalid : IsOneTwoColoringOn G Dset colour := by
    simpa [Dset] using hprepared.1
  have hCDne : C ≠ D := by
    simpa [C, D, g, no320ThreadMiddleEdge, threadLastEdge, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hDnon : colour D ≠ none := by
    intro hDnone
    have hp := hvalid C (by simpa [C, Dset] using hCD)
      D (by simpa [D, Dset] using hDD) hCDne
    have hdisj : EndpointDisjoint G C D := by
      simpa [C, D, hC, hDnone] using hp
    exact hdisj (q.getVert 2)
      (by simp [C, no320ThreadMiddleEdge])
      (by simp [D, threadLastEdge])
  cases hDval : colour D with
  | none => exact False.elim (hDnon hDval)
  | some d =>
      have hDQ : D ≠ Q := by
        simpa [D, Q, g, threadLastEdge, threadFirstEdge, Sym2.eq_swap] using
          (twoThreadCore_firstEdge_ne_lastEdge G g).symm
      have hdi : d ≠ i := by
        intro hEq
        subst d
        have hp := hvalid Q (by simpa [Q, Dset] using hQD)
          D (by simpa [D, Dset] using hDD) hDQ.symm
        have hsep : InducedSeparated G Q D := by
          simpa [Q, D, hQ, hDval] using hp
        exact hsep.2 ⟨q.getVert 1,
          by simp [Q, threadFirstEdge], q.getVert 2,
          by simp [D, threadLastEdge], g.middle_adj⟩
      rcases finFour_eq_one_of_pairwise_distinct i j m k d
          hij him hik hjm hjk hmk with hdi' | hdj | hdm | hdk
      · exact False.elim (hdi hdi')
      · subst d
        let fresh : G.edgeSet → OneTwoColor 4 :=
          recolor G colour Q (some k)
        by_cases hall : ∀ c : Fin 4,
            VertexSeesInduced G fresh (q.getVert 2) c
        · have hfar := full_second_palette_after_fresh_far_normal_form_twoTwo
            G hsub g Dset colour hvalid hprepared.2.2.1
              i m j k him hij hik hjm.symm hmk hjk
              (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQ)
              (by simpa [g, C, no320ThreadMiddleEdge] using hC)
              (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hDval)
              (by simpa [g, D, Dset, threadLastEdge, Sym2.eq_swap] using hDD)
              (by
                intro f hf
                exact hret f (by simpa [g, D, threadLastEdge,
                  Sym2.eq_swap] using hf))
              (by simpa [fresh, g, Q, threadFirstEdge,
                Sym2.eq_swap] using hall)
          exact longPair_hasGoodFour_of_twoZero_terminal_centerColour_full
            G hsub h q hq r hvq hvx hqx colour hprepared i j m k
              hij him hik hjm hjk hmk hP hR hQ hT hA hB hC
              (by simpa [D] using hDval) hPD hQD hCD hDD hDP hRP hRQ
              (by simpa [D, g, threadLastEdge, Sym2.eq_swap] using hfar.1)
              (by simpa [D, g, threadLastEdge, Sym2.eq_swap] using hfar.2)
        · exact longPair_hasGoodFour_of_zeroThread_twoThread_far_matching_of_fresh
            G hsub h g r hvq hvx hqx ha hb hbu hNfar colour hprepared
              i j m k hP hR
              (by simpa [g, threadFirstEdge, Sym2.eq_swap] using hQ)
              hT hU hV hA hB
              (by simpa [g, C, no320ThreadMiddleEdge] using hC)
              (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQD)
              hTD hVD hpal
              (by simpa [g, threadFirstEdge, Sym2.eq_swap] using hzQ)
              (by simp [hik.symm, hjk.symm]) hmk.symm
              (by
                have hDjk : colour D ≠ some k := by
                  rw [hDval]
                  simp [hjk]
                simpa [g, D, threadLastEdge, Sym2.eq_swap] using hDjk)
              (fun _ ↦ by
                simpa [fresh, g, Q, threadFirstEdge,
                  Sym2.eq_swap] using hall)
      · subst d
        let fresh : G.edgeSet → OneTwoColor 4 :=
          recolor G colour Q (some k)
        by_cases hall : ∀ c : Fin 4,
            VertexSeesInduced G fresh (q.getVert 2) c
        · exact longPair_hasGoodFour_of_twoZero_terminal_farColour_full
            G hsub h q hq r hvq hvx hqx htx ha hb hNfar colour hprepared
              i j m k hij him hik hjm hjk hmk hP hR hQ hT hU hV hA hB hC
              (by simpa [D] using hDval) hPD hQD hCD hDD hDP hRP hRQ
              hret (by simpa [fresh] using hall)
        · exact longPair_hasGoodFour_of_zeroThread_twoThread_far_matching_of_fresh
            G hsub h g r hvq hvx hqx ha hb hbu hNfar colour hprepared
              i j m k hP hR
              (by simpa [g, threadFirstEdge, Sym2.eq_swap] using hQ)
              hT hU hV hA hB
              (by simpa [g, C, no320ThreadMiddleEdge] using hC)
              (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQD)
              hTD hVD hpal
              (by simpa [g, threadFirstEdge, Sym2.eq_swap] using hzQ)
              (by simp [hik.symm, hjk.symm]) hmk.symm
              (by
                have hDmk : colour D ≠ some k := by
                  rw [hDval]
                  simp [hmk]
                simpa [g, D, threadLastEdge, Sym2.eq_swap] using hDmk)
              (fun _ ↦ by
                simpa [fresh, g, Q, threadFirstEdge,
                  Sym2.eq_swap] using hall)
      · exact hcomplement (by simpa [D, hdk] using hDval)

end Finite

end

end LeanCo.PackingEdgeColoring
