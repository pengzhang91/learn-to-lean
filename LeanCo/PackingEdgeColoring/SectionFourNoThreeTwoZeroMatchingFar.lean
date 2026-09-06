import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoZero

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem longPair_conditionTwo_matchingFar_final
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour)
    (c j k missing : Fin 4)
    (hmc : missing ≠ c) (hmj : missing ≠ j) (hmk : missing ≠ k)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hD : colour (threadLastEdge G q hq) = some k)
    (E : G.edgeSet)
    (hEext : IsExternalAt G t (threadLastEdge G q hq) E)
    (hE : colour E = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    let C := no320ThreadMiddleEdge G q hq
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q := threadFirstEdge G q hq
    ConditionTwo G
      (recolor G (recolor G (recolor G colour C (some c)) P (some k)) Q none) := by
  dsimp only
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  let afterC : G.edgeSet → OneTwoColor 4 := recolor G colour C (some c)
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G afterC P (some k)
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterP Q none
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hCQ : C ≠ Q := by
    simpa [C, Q, g, no320ThreadMiddleEdge, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        g.start_three g.middle_adj g.first_adj.symm
  have hCP : C ≠ P := by
    simpa [C, P, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.start_three g.middle_adj h.first_adj.symm
  have hDQ : D ≠ Q := by
    simpa [D, Q, g, threadLastEdge, threadFirstEdge, Sym2.eq_swap] using
      (twoThreadCore_firstEdge_ne_lastEdge G g).symm
  have hDC : D ≠ C := by
    simpa [C, D, g, no320ThreadMiddleEdge, threadLastEdge, Sym2.eq_swap] using
      (chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end).symm
  have hDP' : D ≠ P := by simpa [D, P] using hDP
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hvx
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj r.adj hqx
  have hCT : C ≠ T := by
    simpa [C, T, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        r.start_three g.middle_adj r.adj.symm
  have hfinalQ : final Q = none := by simp [final]
  have hfinalP : final P = some k := by simp [final, afterP, hPQ]
  have hfinalC : final C = some c := by
    simp [final, afterP, afterC, hCQ, hCP]
  have hfinalD : final D = some k := by
    simp [final, afterP, afterC, hDQ, hDP', hDC, D, hD]
  have hfinalT : final T = some j := by
    simp [final, afterP, afterC, hQT.symm, hPT.symm, hCT.symm, T, hT]
  have hAD : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [B, Dset] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ (by simpa [Dset, P] using hPD))
  have hAQ : A ≠ Q := fun heq ↦ hAD (heq ▸ (by simpa [Dset, Q] using hQD))
  have hAC : A ≠ C := fun heq ↦ hAD (heq ▸ (by simpa [Dset, C] using hCD))
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ (by simpa [Dset, P] using hPD))
  have hBQ : B ≠ Q := fun heq ↦ hBD (heq ▸ (by simpa [Dset, Q] using hQD))
  have hBC : B ≠ C := fun heq ↦ hBD (heq ▸ (by simpa [Dset, C] using hCD))
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hfinalA : final A = none := by
    simp [final, afterP, afterC, hAQ, hAP, hAC, A, hA]
  have hfinalB : final B = none := by
    simp [final, afterP, afterC, hBQ, hBP, hBC, B, hB]
  have htP : t ∉ (P : Sym2 V) := by
    intro ht
    have htcase : t = v₁ ∨ t = u := by simpa [P] using ht
    exact htcase.elim
      (isThreeVertex_ne_isTwoVertex G g.end_three h.first_two)
      (fun htu ↦ (IsKThread.endpoints_ne G hq) htu.symm)
  have htQ : t ∉ (Q : Sym2 V) := by
    intro ht
    have htcase : t = u ∨ t = q.getVert 1 := by
      simpa [Q, threadFirstEdge] using ht
    exact htcase.elim
      (fun htu ↦ (IsKThread.endpoints_ne G hq) htu.symm)
      (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two)
  have htC : t ∉ (C : Sym2 V) := by
    intro ht
    have htcase : t = q.getVert 1 ∨ t = q.getVert 2 := by
      simpa [C, no320ThreadMiddleEdge] using ht
    exact htcase.elim
      (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two)
      (isThreeVertex_ne_isTwoVertex G g.end_three g.second_two)
  have hEP : E ≠ P := fun heq ↦ htP (by simpa [heq] using hEext.1)
  have hEQ : E ≠ Q := fun heq ↦ htQ (by simpa [heq] using hEext.1)
  have hEC : E ≠ C := fun heq ↦ htC (by simpa [heq] using hEext.1)
  have hfinalE : final E = none := by
    simp [final, afterP, afterC, hEQ, hEP, hEC, hE]
  have hQE : Q ≠ E := hEQ.symm
  have hagree : ColoringsAgreeOff G ({C, P, Q} : Set G.edgeSet) colour final := by
    intro e he
    have hne : e ≠ C ∧ e ≠ P ∧ e ≠ Q := by simpa using he
    simp [final, afterP, afterC, hne.1, hne.2.1, hne.2.2]
  have hnotMissing : ¬ VertexSeesInduced G final (q.getVert 1) missing := by
    intro hsee
    obtain ⟨f, hf, y, hyf, hclose⟩ :=
      (vertexSeesInduced_iff G final (q.getVert 1) missing).mp hsee
    rcases hclose with hyw₁ | hwy
    · subst y
      rcases edge_eq_left_or_right_of_incident_two G g.first_two
          g.middle_adj g.first_adj.symm g.second_ne_start f hyf with hfC | hfQ'
      · have hEq : f = C := Subtype.ext (by
          simpa [C, no320ThreadMiddleEdge] using hfC)
        have heq : some c = some missing := hfinalC.symm.trans (by simpa [hEq] using hf)
        exact hmc (Option.some.inj heq).symm
      · have hEq : f = Q := Subtype.ext (by
          simpa [Q, threadFirstEdge, Sym2.eq_swap] using hfQ')
        have heq : none = some missing := hfinalQ.symm.trans (by simpa [hEq] using hf)
        simp at heq
    · have hyN : y ∈ G.neighborFinset (q.getVert 1) :=
        (G.mem_neighborFinset (q.getVert 1) y).mpr hwy
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start] at hyN
      have hycase : y = q.getVert 2 ∨ y = u := by simpa using hyN
      rcases hycase with hyw₂ | hyu
      · subst y
        rcases edge_eq_left_or_right_of_incident_two G g.second_two
            g.middle_adj.symm g.last_adj g.first_ne_end f hyf with hfC | hfD'
        · have hEq : f = C := Subtype.ext (by
            simpa [C, no320ThreadMiddleEdge, Sym2.eq_swap] using hfC)
          have heq : some c = some missing := hfinalC.symm.trans (by simpa [hEq] using hf)
          exact hmc (Option.some.inj heq).symm
        · have hEq : f = D := Subtype.ext (by
            simpa [D, threadLastEdge] using hfD')
          have heq : some k = some missing := hfinalD.symm.trans (by simpa [hEq] using hf)
          exact hmk (Option.some.inj heq).symm
      · subst y
        obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp hyf
        have hua : G.Adj u a := by
          have hadj := f.2
          rw [hfa] at hadj
          simpa using hadj
        rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
            hq.first_step_adj r.adj hvq hvx hqx hua with rfl | rfl | rfl
        · have hEq : f = P := Subtype.ext (by
            simpa [P, Sym2.eq_swap] using hfa)
          have heq : some k = some missing := hfinalP.symm.trans (by simpa [hEq] using hf)
          exact hmk (Option.some.inj heq).symm
        · have hEq : f = Q := Subtype.ext (by
            simpa [Q, threadFirstEdge, Sym2.eq_swap] using hfa)
          have heq : none = some missing := hfinalQ.symm.trans (by simpa [hEq] using hf)
          simp at heq
        · have hEq : f = T := Subtype.ext (by
            simpa [T, Sym2.eq_swap] using hfa)
          have heq : some j = some missing := hfinalT.symm.trans (by simpa [hEq] using hf)
          exact hmj (Option.some.inj heq).symm
  have hNu : G.neighborFinset u = {v₁, q.getVert 1, x} :=
    longPair_neighborFinset_eq_three G h.start_three h.first_adj
      hq.first_step_adj r.adj hvq hvx hqx
  change ConditionTwo G final
  apply hold.of_agreeOff G hagree
  intro y hy haffect _hmatch hall
  have hcases : y = v₂ ∨ y = q.getVert 2 ∨ G.Adj y u := by
    rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
    obtain ⟨e, heS, a, hae, hya⟩ := haffect
    have hecase : e = C ∨ e = P ∨ e = Q := by simpa using heS
    rcases hecase with rfl | hePQ
    · have hmidaffect : PaletteAffectedBy G ({C} : Set G.edgeSet) y := by
        rw [paletteAffectedBy_iff_inducedAffectedBy]
        exact ⟨C, by simp, a, hae, hya⟩
      rcases twoVertex_paletteAffectedBy_twoThreadMiddle_cases G g hy
          (by simpa [C, g, no320ThreadMiddleEdge] using hmidaffect) with hyw₁ | hyw₂
      · exact Or.inr (Or.inr (by simpa [hyw₁] using hq.first_step_adj.symm))
      · exact Or.inr (Or.inl hyw₂)
    · have hpqaffect : PaletteAffectedBy G ({P, Q} : Set G.edgeSet) y := by
        rw [paletteAffectedBy_iff_inducedAffectedBy]
        exact ⟨e, by simpa using hePQ, a, hae, hya⟩
      exact longPair_twoVertex_paletteAffectedBy_twoThreadFirst_swap_cases
        G h g hy (by simpa [P, Q, g, threadFirstEdge, Sym2.eq_swap] using hpqaffect)
  rcases hcases with hyv₂ | hyw₂ | hyu
  · subst y
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      (by assumption)) hall
  · subst y
    apply longPair_paletteCondition_at_two_visible_matching G hsub g.second_two
      g.middle_adj.symm g.first_two Q E hQE hfinalQ hfinalE
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [Q, threadFirstEdge]) (Or.inr g.middle_adj.symm)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G hEext.1
        (Or.inr g.last_adj)
    · exact hall
  · have hyN : y ∈ G.neighborFinset u := (G.mem_neighborFinset u y).mpr hyu.symm
    rw [hNu] at hyN
    have hycase : y = v₁ ∨ y = q.getVert 1 ∨ y = x := by simpa using hyN
    rcases hycase with hyv₁ | hyw₁ | hyx
    · subst y
      apply longPair_paletteCondition_at_two_visible_matching G hsub h.first_two
        h.left_adj h.middle_two A B hAB hfinalA hfinalB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [B]) (Or.inr h.left_adj)
      · exact hall
    · subst y
      exact hnotMissing (hall missing)
    · subst y
      exact False.elim ((isThreeVertex_ne_isTwoVertex G r.end_three hy) rfl)

/-- The new middle colour is available once the selected, first, and
middle edges are temporarily removed.  The old last edge stays present. -/
theorem longPair_twoThreadMiddle_available_matchingFar
    {u v₁ v₂ v₃ z t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (c j k n : Fin 4) (hcj : c ≠ j) (hck : c ≠ k) (hcn : c ≠ n)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hD : colour (threadLastEdge G q hq) = some k)
    (hfar : ExternalInducedColors G colour t (threadLastEdge G q hq) = {n}) :
    let C := no320ThreadMiddleEdge G q hq
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q := threadFirstEdge G q hq
    ColorAvailableOn G (insert P (Dset \ {P, Q, C}))
      (recolor G colour P (some k)) C (some c) := by
  dsimp only
  classical
  let g := hq.twoThreadCoreData G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  let D₁ : Set G.edgeSet := insert P (Dset \ {P, Q, C})
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some k)
  change ColorAvailableOn G D₁ afterP C (some c)
  apply (colorAvailableOn_some_iff G D₁ afterP C c).mpr
  intro f hfD hfC hfc
  have hfP : f ≠ P := by
    intro heq
    subst f
    have he : some k = some c := by simpa [afterP] using hfc
    exact hck (Option.some.inj he).symm
  have hfbase : colour f = some c := by simpa [afterP, hfP] using hfc
  have hfrest : f ∈ Dset \ {P, Q, C} := by
    simpa [D₁, hfP] using hfD
  have hfne : f ≠ P ∧ f ≠ Q ∧ f ≠ C := by
    have := hfrest.2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using this
  have noAtU (huf : u ∈ (f : Sym2 V)) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hadj := f.2
      rw [hfa] at hadj
      simpa using hadj
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        hq.first_step_adj r.adj hvq hvx hqx hua with rfl | rfl | rfl
    · exact hfne.1 (Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa))
    · exact hfne.2.1 (Subtype.ext (by
        simpa [Q, threadFirstEdge, Sym2.eq_swap] using hfa))
    · have hEq : f = T := Subtype.ext (by
        simpa [T, Sym2.eq_swap] using hfa)
      have he : some j = some c := hT.symm.trans (by simpa [hEq] using hfbase)
      exact hcj (Option.some.inj he).symm
  have noAtW₁ (hwf : q.getVert 1 ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start f hwf with hfC' | hfQ'
    · exact hfne.2.2 (Subtype.ext (by
        simpa [C, no320ThreadMiddleEdge] using hfC'))
    · exact hfne.2.1 (Subtype.ext (by
        simpa [Q, threadFirstEdge, Sym2.eq_swap] using hfQ'))
  have noAtW₂ (hwf : q.getVert 2 ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end f hwf with hfC' | hfD'
    · exact hfne.2.2 (Subtype.ext (by
        simpa [C, no320ThreadMiddleEdge, Sym2.eq_swap] using hfC'))
    · have hEq : f = D := Subtype.ext (by
        simpa [D, threadLastEdge] using hfD')
      have he : some k = some c := hD.symm.trans (by simpa [hEq] using hfbase)
      exact hck (Option.some.inj he).symm
  have noAtT (htf : t ∈ (f : Sym2 V)) : False := by
    by_cases hfDedge : f = D
    · subst f
      have he : some k = some c := hD.symm.trans hfbase
      exact hck (Option.some.inj he).symm
    · have hcmem : c ∈ ExternalInducedColors G colour t D :=
        ⟨f, ⟨htf, hfDedge⟩, hfbase⟩
      rw [show ExternalInducedColors G colour t D = {n} by
        simpa [D] using hfar] at hcmem
      exact hcn (by simpa using hcmem)
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = q.getVert 1 ∨ a = q.getVert 2 := by
    simpa [C, no320ThreadMiddleEdge] using ha
  rcases hacase with haw₁ | haw₂
  · constructor
    · intro hab
      exact noAtW₁ (by simpa [haw₁.symm.trans hab] using hbf)
    · intro hab
      have hwb : G.Adj (q.getVert 1) b := by simpa [haw₁] using hab
      have hbN : b ∈ G.neighborFinset (q.getVert 1) :=
        (G.mem_neighborFinset (q.getVert 1) b).mpr hwb
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start] at hbN
      have hbcase : b = q.getVert 2 ∨ b = u := by simpa using hbN
      exact hbcase.elim
        (fun hbw ↦ noAtW₂ (by simpa [hbw] using hbf))
        (fun hbu ↦ noAtU (by simpa [hbu] using hbf))
  · constructor
    · intro hab
      exact noAtW₂ (by simpa [haw₂.symm.trans hab] using hbf)
    · intro hab
      have hwb : G.Adj (q.getVert 2) b := by simpa [haw₂] using hab
      have hbN : b ∈ G.neighborFinset (q.getVert 2) :=
        (G.mem_neighborFinset (q.getVert 2) b).mpr hwb
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end] at hbN
      have hbcase : b = q.getVert 1 ∨ b = t := by simpa using hbN
      exact hbcase.elim
        (fun hbw ↦ noAtW₁ (by simpa [hbw] using hbf))
        (fun hbt ↦ noAtT (by simpa [hbt] using hbf))

theorem longPair_validOn_matchingFar_final
    {u v₁ v₂ v₃ z t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (i j m k n c : Fin 4)
    (hki : k ≠ i) (hkj : k ≠ j) (hkm : k ≠ m)
    (hcj : c ≠ j) (hck : c ≠ k) (hcn : c ≠ n)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hC : colour (no320ThreadMiddleEdge G q hq) = none)
    (hD : colour (threadLastEdge G q hq) = some k)
    (hfar : ExternalInducedColors G colour t (threadLastEdge G q hq) = {n})
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    let C := no320ThreadMiddleEdge G q hq
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q := threadFirstEdge G q hq
    IsOneTwoColoringOn G (RetainedEdges (G.deleteIncidenceSet v₂) G)
      (recolor G (recolor G (recolor G colour C (some c)) P (some k)) Q none) := by
  dsimp only
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D₀ : Set G.edgeSet := Dset \ {P, Q, C}
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some k)
  let afterC : G.edgeSet → OneTwoColor 4 := recolor G afterP C (some c)
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterC Q none
  have hPD' : P ∈ Dset := by simpa [P, Dset] using hPD
  have hQD' : Q ∈ Dset := by simpa [Q, Dset] using hQD
  have hCD' : C ∈ Dset := by simpa [C, Dset] using hCD
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hCP : C ≠ P := by
    simpa [C, P, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.start_three g.middle_adj h.first_adj.symm
  have hCQ : C ≠ Q := by
    simpa [C, Q, g, no320ThreadMiddleEdge, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        g.start_three g.middle_adj g.first_adj.symm
  have hvalid₀ : IsOneTwoColoringOn G D₀ colour :=
    hvalid.mono G Set.sdiff_subset
  have havailP : ColorAvailableOn G D₀ colour P (some k) := by
    exact longPair_selectedFirst_fresh_available_twoZero G h g r
      hvq hvx hqx ha hb hNfar colour D₀ k j i hP hT
      (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQ)
      (by simpa [g, C, no320ThreadMiddleEdge, hC]) hU
      (by simpa [hV] using hkm.symm) hkj hki
      (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf.1)
  have hPfresh : P ∉ D₀ := by simp [D₀]
  have hvalidP : IsOneTwoColoringOn G (insert P D₀) afterP := by
    simpa [afterP] using hvalid₀.extend_one G hPfresh havailP
  have havailC : ColorAvailableOn G (insert P D₀) afterP C (some c) := by
    simpa [D₀, P, Q, C, afterP] using
      longPair_twoThreadMiddle_available_matchingFar G h q hq r hvq hvx hqx
        colour Dset c j k n hcj hck hcn hT hD hfar
  have hCfresh : C ∉ insert P D₀ := by simp [D₀, hCP]
  have hvalidC : IsOneTwoColoringOn G (insert C (insert P D₀)) afterC := by
    simpa [afterC] using hvalidP.extend_one G hCfresh havailC
  let baseC : G.edgeSet → OneTwoColor 4 := recolor G colour C (some c)
  have hcomm : afterC = recolor G baseC P (some k) := by
    funext e
    by_cases heC : e = C
    · subst e
      simp [afterC, afterP, baseC, hCP]
    · by_cases heP : e = P
      · subst e
        simp [afterC, afterP, baseC, hCP.symm]
      · simp [afterC, afterP, baseC, heC, heP]
  have hCT : C ≠ T := by
    simpa [C, T, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        r.start_three g.middle_adj r.adj.symm
  have hbaseT : baseC T = some j := by simp [baseC, hCT.symm, T, hT]
  have hbaseQ : baseC Q = some i := by
    simp [baseC, hCQ.symm, Q, hQ]
  have hbaseC : baseC C ≠ none := by simp [baseC]
  have havailQ : ColorAvailableOn G (insert C (insert P D₀)) afterC Q none := by
    rw [hcomm]
    simpa [g, P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoThreadFirst_matching_available_after_selectedFresh_twoZero
        G h g r hvq hvx hqx baseC (insert C (insert P D₀)) k j i
          hbaseT (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hbaseQ)
          (by simpa [g, C, no320ThreadMiddleEdge] using hbaseC)
  have hQfresh : Q ∉ insert C (insert P D₀) := by
    simp [D₀, hCQ.symm, hPQ.symm]
  have hvalidFinal : IsOneTwoColoringOn G
      (insert Q (insert C (insert P D₀))) final := by
    simpa [final] using hvalidC.extend_one G hQfresh havailQ
  have hcover : insert Q (insert C (insert P D₀)) = Dset := by
    ext e
    simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl | rfl | ⟨he, _⟩)
      · exact hQD'
      · exact hCD'
      · exact hPD'
      · exact he
    · intro he
      by_cases heQ : e = Q
      · exact Or.inl heQ
      by_cases heC : e = C
      · exact Or.inr (Or.inl heC)
      by_cases heP : e = P
      · exact Or.inr (Or.inr (Or.inl heP))
      · exact Or.inr (Or.inr (Or.inr ⟨he, by simp [heP, heQ, heC]⟩))
  rw [hcover] at hvalidFinal
  simpa [Dset, final, hcomm, baseC, C, P, Q] using hvalidFinal

/-- Saturation survives the simultaneous move from matching `C,P` and
induced `Q` to induced `C,P` and matching `Q`, provided the terminal
induced edge has an external matching witness. -/
theorem longPair_oneSaturated_matchingFar_final
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (hvw : v₁ ≠ w₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour) (c k i : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) = some k)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hAC0 : (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) ≠
      (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet))
    (E : G.edgeSet)
    (hEext : IsExternalAt G t
      (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) E)
    (hE : colour E = none)
    (hEC0 : E ≠ (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet))
    (hEP0 : E ≠ (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hEQ0 : E ≠ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    OneSaturated G
      (recolor G
        (recolor G
          (recolor G colour
            (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some c))
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some k))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, t), g.last_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G (recolor G colour C (some c)) P (some k)) Q none
  have hPQ : P ≠ Q := by
    simpa [P, Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj h.first_adj.symm
  have hCQ : C ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      g.start_three g.middle_adj g.first_adj.symm
  have hCD : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hDQ : D ≠ Q := by
    simpa [D, Q] using (twoThreadCore_firstEdge_ne_lastEdge G g).symm
  have hDP : D ≠ P := by
    intro heq
    have hfalse : some k = none := by
      calc
        some k = colour D := (by simpa [D] using hD.symm)
        _ = colour P := congrArg colour heq
        _ = none := by simpa [P] using hP
    simp at hfalse
  have hAP : A ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      h.start_three h.left_adj h.first_adj.symm
  have hAQ : A ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      g.start_three h.left_adj g.first_adj.symm
  have hAC : A ≠ C := by simpa [A, C] using hAC0
  have hEC : E ≠ C := by simpa [C] using hEC0
  have hEQ : E ≠ Q := by simpa [Q] using hEQ0
  have hEP : E ≠ P := by simpa [P] using hEP0
  have hfinalP : final P = some k := by simp [final, hPQ, hCP]
  have hfinalQ : final Q = none := by simp [final]
  have hfinalC : final C = some c := by simp [final, hCP, hCQ]
  have hfinalD : final D = some k := by
    simp [final, hCD.symm, hDP, hDQ, D, hD]
  have hfinalA : final A = none := by
    simp [final, hAC, hAP, hAQ, A, hA]
  have hfinalE : final E = none := by
    simp [final, hEC, hEP, hEQ, hE]
  have hfinalOff (e : G.edgeSet) (heC : e ≠ C) (heP : e ≠ P)
      (heQ : e ≠ Q) : final e = colour e := by
    simp [final, heC, heP, heQ]
  change OneSaturated G final
  intro e he
  by_cases heP : e = P
  · subst e
    exact ⟨Q, hfinalQ, u, by simp [P], by simp [Q]⟩
  by_cases heC : e = C
  · subst e
    exact ⟨Q, hfinalQ, w₁, by simp [C], by simp [Q]⟩
  by_cases heQ : e = Q
  · subst e
    exact False.elim (he hfinalQ)
  have heOld : colour e ≠ none := by
    intro heNone
    exact he ((hfinalOff e heC heP heQ).trans heNone)
  obtain ⟨f, hf, y, hye, hyf⟩ := hsat e heOld
  by_cases hfP : f = P
  · subst f
    have hycase : y = v₁ ∨ y = u := by simpa [P] using hyf
    rcases hycase with hyv₁ | hyu
    · exact ⟨A, hfinalA, y, hye, by simpa [A, hyv₁]⟩
    · exact ⟨Q, hfinalQ, y, hye, by simpa [Q, hyu]⟩
  by_cases hfC : f = C
  · subst f
    have hycase : y = w₁ ∨ y = w₂ := by simpa [C] using hyf
    rcases hycase with hyw₁ | hyw₂
    · exact ⟨Q, hfinalQ, y, hye, by simpa [Q, hyw₁]⟩
    · have hw₂e : w₂ ∈ (e : Sym2 V) := by simpa [hyw₂] using hye
      rcases edge_eq_left_or_right_of_incident_two G g.second_two
          g.middle_adj.symm g.last_adj g.first_ne_end e hw₂e with heC' | heD'
      · exact False.elim
          (heC (Subtype.ext (by simpa [C, Sym2.eq_swap] using heC')))
      · have heqD : e = D := Subtype.ext (by simpa [D] using heD')
        exact ⟨E, hfinalE, t, by simpa [heqD, D], hEext.1⟩
  have hfQ : f ≠ Q := by
    intro hfQ
    subst f
    have hfalse : some i = none := hQ.symm.trans (by simpa [Q] using hf)
    simp at hfalse
  exact ⟨f, (hfinalOff f hfC hfP hfQ).trans hf, y, hye, hyf⟩

theorem longPair_conditionThree_matchingFar_final
    {u v₁ v₂ v₃ z t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (c k : Fin 4)
    (E : G.edgeSet)
    (hEext : IsExternalAt G t (threadLastEdge G q hq) E)
    (hE : colour E = none)
    (hEC : E ≠ no320ThreadMiddleEdge G q hq)
    (hEP : E ≠ (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hEQ : E ≠ threadFirstEdge G q hq) :
    let C := no320ThreadMiddleEdge G q hq
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q := threadFirstEdge G q hq
    ConditionThree G
      (recolor G (recolor G (recolor G colour C (some c)) P (some k)) Q none) := by
  dsimp only
  classical
  let g := hq.twoThreadCoreData G
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let baseC : G.edgeSet → OneTwoColor 4 := recolor G colour C (some c)
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G baseC P (some k)) Q none
  have hthreeC : ConditionThree G baseC := by
    simpa [baseC, C, g, no320ThreadMiddleEdge] using
      conditionThree_recolor_edge_between_two_vertices G g.first_two
        g.second_two g.middle_adj colour hold c
  have hfinalE : final E = none := by
    simp [final, baseC, C, P, Q, hEC, hEP, hEQ, hE]
  have hcritical : ConditionThreeAtTwoThread G q hq final := by
    intro _hstart hfar
    obtain ⟨a, hEa⟩ := hfar E hEext
    have hfalse : none = some a := hfinalE.symm.trans hEa
    simp at hfalse
  have hfinal : ConditionThree G final :=
    (longPair_conditionThree_swap_selectedOuter_twoThreadFirst_iff
      G h q hq baseC hthreeC k).2 (by
        simpa [final, P, Q, baseC] using hcritical)
  simpa [final, baseC, C, P, Q] using hfinal

theorem longPair_prepared_matchingFar_final
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
    (i j m k n c missing : Fin 4)
    (hki : k ≠ i) (hkj : k ≠ j) (hkm : k ≠ m)
    (hcj : c ≠ j) (hck : c ≠ k) (hcn : c ≠ n)
    (hmc : missing ≠ c) (hmj : missing ≠ j) (hmk : missing ≠ k)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (no320ThreadMiddleEdge G q hq) = none)
    (hD : colour (threadLastEdge G q hq) = some k)
    (E : G.edgeSet)
    (hEext : IsExternalAt G t (threadLastEdge G q hq) E)
    (hE : colour E = none)
    (hfar : ExternalInducedColors G colour t (threadLastEdge G q hq) = {n})
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    let C := no320ThreadMiddleEdge G q hq
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q := threadFirstEdge G q hq
    PreparedThreeThreadGap G h
      (recolor G (recolor G (recolor G colour C (some c)) P (some k)) Q none) := by
  dsimp only
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let D : G.edgeSet := threadLastEdge G q hq
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G (recolor G colour C (some c)) P (some k)) Q none
  have hAD : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hAC : A ≠ C := fun heq ↦
    hAD (heq ▸ (by simpa [Dset, C] using hCD))
  have htP : t ∉ (P : Sym2 V) := by
    intro ht
    have htcase : t = v₁ ∨ t = u := by simpa [P] using ht
    exact htcase.elim
      (isThreeVertex_ne_isTwoVertex G g.end_three h.first_two)
      (fun htu ↦ (IsKThread.endpoints_ne G hq) htu.symm)
  have htQ : t ∉ (Q : Sym2 V) := by
    intro ht
    have htcase : t = u ∨ t = q.getVert 1 := by
      simpa [Q, threadFirstEdge] using ht
    exact htcase.elim
      (fun htu ↦ (IsKThread.endpoints_ne G hq) htu.symm)
      (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two)
  have htC : t ∉ (C : Sym2 V) := by
    intro ht
    have htcase : t = q.getVert 1 ∨ t = q.getVert 2 := by
      simpa [C, no320ThreadMiddleEdge] using ht
    exact htcase.elim
      (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two)
      (isThreeVertex_ne_isTwoVertex G g.end_three g.second_two)
  have hEP : E ≠ P := fun heq ↦ htP (by simpa [heq] using hEext.1)
  have hEQ : E ≠ Q := fun heq ↦ htQ (by simpa [heq] using hEext.1)
  have hEC : E ≠ C := fun heq ↦ htC (by simpa [heq] using hEext.1)
  have hvalidFinal : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) final := by
    simpa [final, C, P, Q] using
      longPair_validOn_matchingFar_final G h q hq r hvq hvx hqx ha hb hNfar
        colour hprepared.1 i j m k n c hki hkj hkm hcj hck hcn hP hQ hT
        hU hV hC hD hfar hPD hQD hCD
  have hsatFinal : OneSaturated G final := by
    simpa [final, C, P, Q, g, no320ThreadMiddleEdge, threadFirstEdge,
      threadLastEdge, Sym2.eq_swap] using
      longPair_oneSaturated_matchingFar_final
        G h g hvq colour hprepared.2.1 c k i hP
          (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQ)
          (by simpa [g, C, no320ThreadMiddleEdge] using hC)
          (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hD)
          hA (by simpa [A, C, g, no320ThreadMiddleEdge] using hAC)
          E (by simpa [g, D, threadLastEdge, Sym2.eq_swap] using hEext) hE
          (by simpa [C, g, no320ThreadMiddleEdge] using hEC)
          (by simpa [P] using hEP)
          (by simpa [Q, g, threadFirstEdge, Sym2.eq_swap] using hEQ)
  have htwoFinal : ConditionTwo G final := by
    simpa [final, C, P, Q] using
      longPair_conditionTwo_matchingFar_final G hsub h q hq r hvq hvx hqx
        colour hprepared.2.2.1 c j k missing hmc hmj hmk hT hA hB hD E
          hEext hE hPD hQD hCD hDP
  have hthreeFinal : ConditionThree G final := by
    simpa [final, C, P, Q] using
      longPair_conditionThree_matchingFar_final
        G h q hq colour hprepared.2.2.2 c k E hEext hE hEC hEP hEQ
  exact ⟨hvalidFinal, hsatFinal, htwoFinal, hthreeFinal⟩

theorem longPair_hasGoodFour_matchingFar_final
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
    (i j m k n c missing : Fin 4)
    (hki : k ≠ i) (hkj : k ≠ j) (hkm : k ≠ m)
    (hcj : c ≠ j) (hck : c ≠ k) (hcn : c ≠ n)
    (hmc : missing ≠ c) (hmj : missing ≠ j) (hmk : missing ≠ k)
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
    (E : G.edgeSet)
    (hEext : IsExternalAt G t (threadLastEdge G q hq) E)
    (hE : colour E = none)
    (hfar : ExternalInducedColors G colour t (threadLastEdge G q hq) = {n})
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
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq) :
    HasGoodFour G := by
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := no320ThreadMiddleEdge G q hq
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G (recolor G colour C (some c)) P (some k)) Q none
  have hpreparedFinal : PreparedThreeThreadGap G h final := by
    simpa [final, C, P, Q] using
      longPair_prepared_matchingFar_final G hsub h q hq r hvq hvx hqx ha hb
        hNfar colour hprepared i j m k n c missing hki hkj hkm hcj hck hcn
        hmc hmj hmk hP hQ hT hU hV hA hB hC hD E hEext hE hfar hPD hQD
        hCD hDP
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hCP : C ≠ P := by
    simpa [C, P, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.start_three g.middle_adj h.first_adj.symm
  have hCQ : C ≠ Q := by
    simpa [C, Q, g, no320ThreadMiddleEdge, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        g.start_three g.middle_adj g.first_adj.symm
  have hCR : C ≠ R := by
    simpa [C, R, g, no320ThreadMiddleEdge] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
        h.end_three g.middle_adj h.last_adj
  have hfinalP : final P = some k := by simp [final, hPQ, hCP]
  have hfinalQ : final Q = none := by simp [final]
  have hfinalR : final R = none := by
    simp [final, hCR.symm, R, P, Q, hRP, hRQ, hR]
  have hAD : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [B, Dset] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ (by simpa [Dset, P] using hPD))
  have hAQ : A ≠ Q := fun heq ↦ hAD (heq ▸ (by simpa [Dset, Q] using hQD))
  have hAC : A ≠ C := fun heq ↦ hAD (heq ▸ (by simpa [Dset, C] using hCD))
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ (by simpa [Dset, P] using hPD))
  have hBQ : B ≠ Q := fun heq ↦ hBD (heq ▸ (by simpa [Dset, Q] using hQD))
  have hBC : B ≠ C := fun heq ↦ hBD (heq ▸ (by simpa [Dset, C] using hCD))
  have hfinalA : final A = none := by
    simp [final, hAC, hAP, hAQ, A, hA]
  have hfinalB : final B = none := by
    simp [final, hBC, hBP, hBQ, B, hB]
  apply longPair_hasGoodFour_of_prepared_left_outer_induced
    G hsub h final hpreparedFinal
      (by simpa [P, hfinalP]) (by simpa [R] using hfinalR)
      (by simpa [A] using hfinalA) (by simpa [B] using hfinalB)
      Q hfinalQ
  · simp [Q, threadFirstEdge]
  · exact hAQ.symm
  · exact hBQ.symm

end Finite

end

end LeanCo.PackingEdgeColoring
