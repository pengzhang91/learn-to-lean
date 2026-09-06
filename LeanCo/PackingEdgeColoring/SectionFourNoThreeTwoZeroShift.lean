import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoTwo

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/- A colour absent from both endpoint palettes is available on the middle
edge while the middle and terminal edges are temporarily omitted. -/
theorem longPair_twoThreadMiddle_fresh_available_twoZeroShift
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (Dset : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor 4)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hkCenter : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hkFar : k ∉ ExternalInducedColors G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)) :
    ColorAvailableOn G
      (Dset \ {(⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet),
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)})
      colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let D₀ : Set G.edgeSet := Dset \ {C, D}
  have hP' : colour P = none := by simpa [P] using hP
  change ColorAvailableOn G D₀ colour C (some k)
  apply (colorAvailableOn_some_iff G D₀ colour C k).mpr
  intro f hf₀ hfC hfk
  have hfne : f ≠ C ∧ f ≠ D := by simpa [D₀] using hf₀.2
  have noAtU (huf : u ∈ (f : Sym2 V)) : False := by
    by_cases hfP : f = P
    · subst f
      have hfalse : none = some k := hP'.symm.trans hfk
      simp at hfalse
    · exact hkCenter ⟨f, ⟨huf, hfP⟩, hfk⟩
  have noAtW₁ (hw₁f : w₁ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.first_adj.symm g.middle_adj g.second_ne_start.symm f hw₁f with
      hfQ | hfC'
    · have hEqQ : f = Q :=
        Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfQ)
      exact noAtU (by simpa [hEqQ, Q])
    · exact hfne.1 (Subtype.ext (by simpa [C] using hfC'))
  have noAtW₂ (hw₂f : w₂ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end f hw₂f with hfC' | hfD'
    · exact hfne.1 (Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC'))
    · exact hfne.2 (Subtype.ext (by simpa [D] using hfD'))
  have noAtS (hsf : s ∈ (f : Sym2 V)) : False := by
    exact hkFar ⟨f, ⟨hsf, hfne.2⟩, hfk⟩
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = w₁ ∨ a = w₂ := by simpa [C] using ha
  rcases hacase with haw₁ | haw₂
  · constructor
    · intro hab
      exact noAtW₁ (by simpa [haw₁.symm.trans hab] using hbf)
    · intro hab
      have hwb : G.Adj w₁ b := by simpa [haw₁] using hab
      have hbN : b ∈ G.neighborFinset w₁ := (G.mem_neighborFinset w₁ b).mpr hwb
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start] at hbN
      have hbcase : b = w₂ ∨ b = u := by simpa using hbN
      exact hbcase.elim
        (fun hbw₂ ↦ noAtW₂ (by simpa [hbw₂] using hbf))
        (fun hbu ↦ noAtU (by simpa [hbu] using hbf))
  · constructor
    · intro hab
      exact noAtW₂ (by simpa [haw₂.symm.trans hab] using hbf)
    · intro hab
      have hwb : G.Adj w₂ b := by simpa [haw₂] using hab
      have hbN : b ∈ G.neighborFinset w₂ := (G.mem_neighborFinset w₂ b).mpr hwb
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end] at hbN
      have hbcase : b = w₁ ∨ b = s := by simpa using hbN
      exact hbcase.elim
        (fun hbw₁ ↦ noAtW₁ (by simpa [hbw₁] using hbf))
        (fun hbs ↦ noAtS (by simpa [hbs] using hbf))

/- Packing validity for a simultaneous `C : matching, D : old` to
`C : fresh, D : matching` move.  Unlike the existing same-colour shift,
the new middle colour need not be the old terminal colour. -/
theorem longPair_validOn_shift_twoThreadTail_fresh
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hCD : (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hkCenter : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hkFar : k ∉ ExternalInducedColors G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet))
    (hfar : ExternalEdgesInduced G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)) :
    IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G)
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let D₀ : Set G.edgeSet := Dset \ {C, D}
  let afterC : G.edgeSet → OneTwoColor 4 := recolor G colour C (some k)
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterC D none
  have hCD' : C ∈ Dset := by simpa [C, Dset] using hCD
  have hDD' : D ∈ Dset := by simpa [D, Dset] using hDD
  have hCDne : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hvalid₀ : IsOneTwoColoringOn G D₀ colour :=
    hvalid.mono G Set.sdiff_subset
  have hCfresh : C ∉ D₀ := by simp [D₀]
  have havailC : ColorAvailableOn G D₀ colour C (some k) := by
    simpa [Dset, D₀, C, D] using
      longPair_twoThreadMiddle_fresh_available_twoZeroShift G h g Dset colour k hP
        hkCenter hkFar
  have hvalidC : IsOneTwoColoringOn G (insert C D₀) afterC := by
    simpa [afterC] using hvalid₀.extend_one G hCfresh havailC
  have hDfresh : D ∉ insert C D₀ := by simp [D₀, hCDne.symm]
  have havailD : ColorAvailableOn G (insert C D₀) afterC D none := by
    simpa [Dset, D₀, C, D, afterC] using
      longPair_twoThreadLast_shift_matching_available_twoTwo G
        (v₁ := v₁) (v₃ := v₃) (z := z) g colour hvalid k hC hCD hfar
  have hvalidFinal : IsOneTwoColoringOn G (insert D (insert C D₀)) final := by
    simpa [final] using hvalidC.extend_one G hDfresh havailD
  have hcover : insert D (insert C D₀) = Dset := by
    ext f
    simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl | ⟨hf, _⟩)
      · exact hDD'
      · exact hCD'
      · exact hf
    · intro hf
      by_cases hfD : f = D
      · exact Or.inl hfD
      by_cases hfC : f = C
      · exact Or.inr (Or.inl hfC)
      · exact Or.inr (Or.inr ⟨hf, by simp [hfC, hfD]⟩)
  rw [hcover] at hvalidFinal
  simpa [Dset, final, afterC] using hvalidFinal

/- Saturation survives the same simultaneous move whenever the old
terminal edge was induced; its colour need not equal the new middle colour. -/
theorem longPair_oneSaturated_shift_twoThreadTail_fresh
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hDnon : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠ none) :
    OneSaturated G
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some k)) D none
  have hCD : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj h.first_adj.symm
  have hDP : D ≠ P := by
    intro hEq
    exact hDnon (by simpa [D, P, hEq] using hP)
  have hfinalC : final C = some k := by simp [final, hCD]
  have hfinalD : final D = none := by simp [final]
  have hfinalP : final P = none := by
    simp [final, hCP.symm, hDP.symm, P, hP]
  have hfinalOff (e : G.edgeSet) (heC : e ≠ C) (heD : e ≠ D) :
      final e = colour e := by simp [final, heC, heD]
  change OneSaturated G final
  intro e he
  by_cases heC : e = C
  · subst e
    exact ⟨D, hfinalD, w₂, by simp [C], by simp [D]⟩
  by_cases heD : e = D
  · subst e
    exact False.elim (he hfinalD)
  have heOld : colour e ≠ none := by
    intro heNone
    exact he ((hfinalOff e heC heD).trans heNone)
  obtain ⟨f, hf, y, hye, hyf⟩ := hsat e heOld
  by_cases hfC : f = C
  · subst f
    have hycase : y = w₁ ∨ y = w₂ := by simpa [C] using hyf
    rcases hycase with hyw₁ | hyw₂
    · have hw₁e : w₁ ∈ (e : Sym2 V) := by simpa [hyw₁] using hye
      rcases edge_eq_left_or_right_of_incident_two G g.first_two
          g.first_adj.symm g.middle_adj g.second_ne_start.symm e hw₁e with
        heQ | heC'
      · have hEqQ : e = Q :=
          Subtype.ext (by simpa [Q, Sym2.eq_swap] using heQ)
        exact ⟨P, hfinalP, u, by simpa [hEqQ, Q], by simp [P]⟩
      · exact False.elim
          (heC (Subtype.ext (by simpa [C] using heC')))
    · exact ⟨D, hfinalD, y, hye, by simpa [D, hyw₂]⟩
  · have hfD : f ≠ D := by
      intro hEq
      subst f
      exact hDnon (by simpa [D] using hf)
    exact ⟨f, (hfinalOff f hfC hfD).trans hf, y, hye, hyf⟩

/- Condition 2 for a different-colour terminal shift.  The old terminal
colour is excluded at the second internal vertex by the explicit far
palette; at the first internal vertex the new matching terminal edge and
the selected matching edge are both visible. -/
theorem longPair_conditionTwo_shift_twoThreadTail_fresh
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (hsat : OneSaturated G colour)
    (i j m k : Fin 4) (hij : i ≠ j) (hkj : k ≠ j) (hjm : j ≠ m)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hD : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = some j)
    (hfarEdges : ExternalEdgesInduced G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet))
    (hfarPalette : ExternalInducedColors G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = {i, m}) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some k)) D none
  have hCD : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj h.first_adj.symm
  have hCQ : C ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      g.start_three g.middle_adj g.first_adj.symm
  have hDP : D ≠ P := by
    intro hEq
    have he : some j = none := by
      calc
        some j = colour D := hD.symm
        _ = colour P := congrArg colour hEq
        _ = none := by simpa [P] using hP
    simp at he
  have hDQ : D ≠ Q := by
    simpa [D, Q] using (twoThreadCore_firstEdge_ne_lastEdge G g).symm
  have hfinalC : final C = some k := by simp [final, hCD]
  have hfinalD : final D = none := by simp [final]
  have hfinalP : final P = none := by
    simp [final, hCP.symm, hDP.symm, P, hP]
  have hfinalQ : final Q = some i := by
    simp [final, hCQ.symm, hDQ.symm, Q, hQ]
  have hfinalOff (e : G.edgeSet) (heC : e ≠ C) (heD : e ≠ D) :
      final e = colour e := by simp [final, heC, heD]
  have hagree : ColoringsAgreeOff G ({C, D} : Set G.edgeSet) colour final := by
    intro e he
    have hne : e ≠ C ∧ e ≠ D := by simpa using he
    exact (hfinalOff e hne.1 hne.2).symm
  have hnotJ : ¬ VertexSeesInduced G final w₂ j := by
    intro hseen
    obtain ⟨f, hfj, x, hxf, hclose⟩ :=
      (vertexSeesInduced_iff G final w₂ j).mp hseen
    have hfC : f ≠ C := by
      intro hEq
      subst f
      have he : some k = some j := hfinalC.symm.trans hfj
      exact hkj (Option.some.inj he)
    have hfD : f ≠ D := by
      intro hEq
      subst f
      have he : none = some j := hfinalD.symm.trans hfj
      simp at he
    rcases hclose with hxw₂ | hw₂x
    · rcases edge_eq_left_or_right_of_incident_two G g.second_two
          g.middle_adj.symm g.last_adj g.first_ne_end f
          (by simpa [hxw₂] using hxf) with hfC' | hfD'
      · exact hfC (Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC'))
      · exact hfD (Subtype.ext (by simpa [D] using hfD'))
    · have hxN : x ∈ G.neighborFinset w₂ :=
        (G.mem_neighborFinset w₂ x).mpr hw₂x
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end] at hxN
      have hxcase : x = w₁ ∨ x = s := by simpa using hxN
      rcases hxcase with hxw₁ | hxs
      · rcases edge_eq_left_or_right_of_incident_two G g.first_two
            g.middle_adj g.first_adj.symm g.second_ne_start f
            (by simpa [hxw₁] using hxf) with hfC' | hfQ'
        · exact hfC (Subtype.ext (by simpa [C] using hfC'))
        · have hEqQ : f = Q :=
            Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfQ')
          have he : some i = some j := hfinalQ.symm.trans (by simpa [hEqQ] using hfj)
          exact hij (Option.some.inj he)
      · have hfold : colour f = some j := by
          simpa [hfinalOff f hfC hfD] using hfj
        have hjmem : j ∈ ExternalInducedColors G colour s D :=
          ⟨f, ⟨by simpa [hxs] using hxf, hfD⟩, hfold⟩
        rw [show ExternalInducedColors G colour s D = {i, m} by
          simpa [D] using hfarPalette] at hjmem
        simpa [hij.symm, hjm] using hjmem
  have oldAllAway (q : V) (hq : IsTwoVertex G q)
      (hqw₁ : q ≠ w₁) (hqw₂ : q ≠ w₂) (hqs : G.Adj q s)
      (hall : ∀ a : Fin 4, VertexSeesInduced G final q a) :
      ∀ a : Fin 4, VertexSeesInduced G colour q a := by
    intro a
    obtain ⟨f, hfa, x, hxf, hclose⟩ :=
      (vertexSeesInduced_iff G final q a).mp (hall a)
    have hfD : f ≠ D := by
      intro hEq
      subst f
      have he : none = some a := hfinalD.symm.trans hfa
      simp at he
    have hfC : f ≠ C := by
      intro hEq
      subst f
      have hxcase : x = w₁ ∨ x = w₂ := by simpa [C] using hxf
      rcases hxcase with hxw₁ | hxw₂
      · subst x
        rcases hclose with hEq | hadj
        · exact hqw₁ hEq
        · have hqN : q ∈ G.neighborFinset w₁ :=
            (G.mem_neighborFinset w₁ q).mpr hadj.symm
          rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
            g.middle_adj g.first_adj.symm g.second_ne_start] at hqN
          have hqcase : q = w₂ ∨ q = u := by simpa using hqN
          rcases hqcase with hEq | hEq
          · exact hqw₂ hEq
          · exact (isThreeVertex_ne_isTwoVertex G h.start_three hq) hEq.symm
      · subst x
        rcases hclose with hEq | hadj
        · exact hqw₂ hEq
        · have hqN : q ∈ G.neighborFinset w₂ :=
            (G.mem_neighborFinset w₂ q).mpr hadj.symm
          rw [neighborFinset_eq_pair_of_isTwoVertex G g.second_two
            g.middle_adj.symm g.last_adj g.first_ne_end] at hqN
          have hqcase : q = w₁ ∨ q = s := by simpa using hqN
          rcases hqcase with hEq | hEq
          · exact hqw₁ hEq
          · exact (isThreeVertex_ne_isTwoVertex G g.end_three hq) hEq.symm
    exact (vertexSeesInduced_iff G colour q a).mpr
      ⟨f, by simpa [hfinalOff f hfC hfD] using hfa, x, hxf, hclose⟩
  change ConditionTwo G final
  apply hold.of_agreeOff G hagree
  intro q hq haffect _hmatch hall
  have hqcase : q = w₁ ∨ q = w₂ ∨ G.Adj q s :=
    twoVertex_paletteAffectedBy_twoThreadTail_cases G g hq
      (by simpa [C, D, Sym2.eq_swap] using haffect)
  by_cases hqw₁ : q = w₁
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub g.first_two
      g.middle_adj g.second_two P D hDP.symm hfinalP hfinalD
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [P]) (Or.inr g.first_adj.symm)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [D]) (Or.inr g.middle_adj)
    · exact hall
  by_cases hqw₂ : q = w₂
  · subst q
    exact hnotJ (hall j)
  have hqs : G.Adj q s := hqcase.elim
    (fun hEq ↦ False.elim (hqw₁ hEq))
    (fun hrest ↦ hrest.elim
      (fun hEq ↦ False.elim (hqw₂ hEq)) id)
  let E : G.edgeSet := ⟨s(q, s), hqs⟩
  have hED : E ≠ D := by
    intro hEq
    have hw₂E : w₂ ∈ (E : Sym2 V) := by rw [hEq]; simp [D]
    have hwcase : w₂ = q ∨ w₂ = s := by simpa [E] using hw₂E
    rcases hwcase with hwq | hws
    · exact hqw₂ hwq.symm
    · exact (isThreeVertex_ne_isTwoVertex G g.end_three g.second_two) hws.symm
  obtain ⟨a, hEa⟩ := hfarEdges E ⟨by simp [E], hED⟩
  obtain ⟨M, hM, y, hyE, hyM⟩ := hsat E (by
    intro hnone
    have hfalse : some a = none := hEa.symm.trans hnone
    simp at hfalse)
  have hycase : y = q ∨ y = s := by simpa [E] using hyE
  have hyq : y = q := by
    rcases hycase with hyq | hys
    · exact hyq
    · have hMD : M ≠ D := by
        intro hEq
        subst M
        have hD' : colour D = some j := by simpa [D] using hD
        have hfalse : some j = none := hD'.symm.trans hM
        simp at hfalse
      obtain ⟨b, hMb⟩ := hfarEdges M
        ⟨by simpa [hys] using hyM, hMD⟩
      have hfalse : none = some b := hM.symm.trans hMb
      simp at hfalse
  apply hold q hq
  · exact (vertexSeesMatching_iff G colour q).mpr
      ⟨M, hM, by simpa [hyq] using hyM⟩
  · exact oldAllAway q hq hqw₁ hqw₂ hqs hall

/- Complete prepared-gap package for the different-colour simultaneous
terminal shift. -/
theorem longPair_prepared_shift_twoThreadTail_fresh
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m k : Fin 4) (hij : i ≠ j) (hkj : k ≠ j) (hjm : j ≠ m)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = some j)
    (hCD : (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hkCenter : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hkFar : k ∉ ExternalInducedColors G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet))
    (hfarEdges : ExternalEdgesInduced G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet))
    (hfarPalette : ExternalInducedColors G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = {i, m}) :
    PreparedThreeThreadGap G h
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none) := by
  exact ⟨
    longPair_validOn_shift_twoThreadTail_fresh G h g colour hprepared.1 k
      hP hC hCD hDD hkCenter hkFar hfarEdges,
    longPair_oneSaturated_shift_twoThreadTail_fresh G h g colour
      hprepared.2.1 k hP (by rw [hD]; simp),
    longPair_conditionTwo_shift_twoThreadTail_fresh G hsub h g colour
      hprepared.2.2.1 hprepared.2.1 i j m k hij hkj hjm hP hQ hD
      hfarEdges hfarPalette,
    longPair_conditionThree_shift_twoThreadTail_twoTwo G g colour
      hprepared.2.2.2 k⟩

end Finite

end

end LeanCo.PackingEdgeColoring
