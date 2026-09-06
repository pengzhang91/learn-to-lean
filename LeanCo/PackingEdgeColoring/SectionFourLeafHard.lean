import LeanCo.PackingEdgeColoring.SectionFourMinDegree
import LeanCo.PackingEdgeColoring.SectionFourLongThreadPair
import LeanCo.PackingEdgeColoring.SectionFourLeafEasyThree
import LeanCo.PackingEdgeColoring.SectionFourLeafC3Choice

/-!
# Hard leaf branches for Section 4

This module records the nontrivial degree-three/degree-two leaf extension.
The key point is to use Condition 3 in the leaf-deleted graph on the
two-thread which disappears when the leaf edge is restored.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem not_adj_other_neighbors_of_girth_sixteen
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) : ¬ G.Adj a b := by
  let p : G.Walk a b := .cons hva.symm hvb.toWalk
  have hp : p.IsPath := by
    apply (Walk.IsPath.of_adj hvb).cons
    simp [hva.ne.symm, hab]
  exact fun hab' =>
    (not_adj_endpoints_of_short_path G hgirth hp
      (by simp [p]) (by simp [p])) hab'.symm

theorem externalEdgesInduced_of_valid_matching_four
    {colour : G.edgeSet → OneTwoColor 4}
    (hvalid : IsOneTwoColoring G colour)
    {x : V} {P : G.edgeSet} (hxP : x ∈ (P : Sym2 V))
    (hP : colour P = none) :
    ExternalEdgesInduced G colour x P := by
  intro e he
  cases hce : colour e with
  | none =>
      have hp := hvalid P (by simp) e (by simp) he.2.symm
      have hdisj : EndpointDisjoint G P e := by
        simpa [hP, hce] using hp
      exact False.elim (hdisj x hxP he.1)
  | some i => exact ⟨i, rfl⟩

theorem other_edge_matching_of_two_vertex
    {b v r : V} (hb : IsTwoVertex G b)
    (hvb : G.Adj v b) (hbr : G.Adj b r) (hrv : r ≠ v)
    (colour : G.edgeSet → OneTwoColor 4) (beta : Fin 4)
    (hB : colour (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (hmatch : VertexSeesMatching G colour b) :
    colour (⟨s(b, r), hbr⟩ : G.edgeSet) = none := by
  obtain ⟨f, hf, hbf⟩ := (vertexSeesMatching_iff G colour b).mp hmatch
  rcases edge_eq_left_or_right_of_incident_two G hb hvb.symm hbr
      hrv.symm f hbf with hfB | hfC
  · have hfeq : f = (⟨s(v, b), hvb⟩ : G.edgeSet) := by
      apply Subtype.ext
      simpa [Sym2.eq_swap] using hfB
    subst f
    rw [hB] at hf
    simp at hf
  · have hfeq : f = (⟨s(b, r), hbr⟩ : G.edgeSet) :=
      Subtype.ext hfC
    simpa [hfeq] using hf

theorem exists_vanished_twoThread_deleteLeafEdge
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v a b r : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsThreeVertex G a)
    (hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hrv : r ≠ v) (hbr : G.Adj b r)
    (hr : IsThreeVertex G r) :
    ∃ p : (deleteLeafEdge G huv).Walk r a,
      ∃ hp : IsKThread (deleteLeafEdge G huv) p 2,
        (threadFirstEdge (deleteLeafEdge G huv) p hp : Sym2 V) = s(r, b) ∧
        (threadLastEdge (deleteLeafEdge G huv) p hp : Sym2 V) = s(v, a) := by
  let H := deleteLeafEdge G huv
  have hrv' : r ≠ v := hrv
  have hru : r ≠ u := by
    intro hru
    subst r
    have hbEq : b = v := eq_neighbor_of_degree_eq_one G hu huv hbr.symm
    exact hvb.ne hbEq.symm
  have hnab : ¬ G.Adj a b :=
    not_adj_other_neighbors_of_girth_sixteen G hgirth hva hvb hab
  have hra : r ≠ a := by
    intro hra
    subst r
    exact hnab hbr.symm
  have hCD : (⟨s(b, r), hbr⟩ : G.edgeSet) ∈
      RetainedEdges H G := by
    apply (mem_retained_deleteLeafEdge_iff G huv _).mpr
    intro heq
    have heqv : s(b, r) = s(u, v) := congrArg Subtype.val heq
    have hbE : b ∈ (s(u, v) : Sym2 V) := by
      rw [← heqv]
      simp
    have hc : b = u ∨ b = v := by simpa using hbE
    exact hc.elim hbu hvb.ne.symm
  have hBD : (⟨s(v, b), hvb⟩ : G.edgeSet) ∈
      RetainedEdges H G := by
    apply (mem_retained_deleteLeafEdge_iff G huv _).mpr
    intro heq
    have heqv : s(v, b) = s(u, v) := congrArg Subtype.val heq
    have hbE : b ∈ (s(u, v) : Sym2 V) := by
      rw [← heqv]
      simp
    have hc : b = u ∨ b = v := by simpa using hbE
    exact hc.elim hbu hvb.ne.symm
  have hAD : (⟨s(v, a), hva⟩ : G.edgeSet) ∈
      RetainedEdges H G := by
    apply (mem_retained_deleteLeafEdge_iff G huv _).mpr
    intro heq
    have heqv : s(v, a) = s(u, v) := congrArg Subtype.val heq
    have haE : a ∈ (s(u, v) : Sym2 V) := by
      rw [← heqv]
      simp
    have hc : a = u ∨ a = v := by simpa using haE
    exact hc.elim hau hva.ne.symm
  have hHrb : H.Adj r b := by
    apply H.mem_edgeSet.mp
    change s(b, r) ∈ H.edgeSet at hCD
    simpa [Sym2.eq_swap] using hCD
  have hHbv : H.Adj b v := by
    apply H.mem_edgeSet.mp
    change s(v, b) ∈ H.edgeSet at hBD
    simpa [Sym2.eq_swap] using hBD
  have hHva : H.Adj v a := by
    apply H.mem_edgeSet.mp
    change s(v, a) ∈ H.edgeSet at hAD
    exact hAD
  have hrH : IsThreeVertex H r := by
    unfold IsThreeVertex at hr ⊢
    rw [degree_deleteLeafEdge_eq_of_ne G huv hru hrv']
    exact hr
  have hbH : IsTwoVertex H b := by
    unfold IsTwoVertex at hb ⊢
    rw [degree_deleteLeafEdge_eq_of_ne G huv hbu hvb.ne.symm]
    exact hb
  have hvH : IsTwoVertex H v :=
    isTwoVertex_deleteLeafEdge_at_three_neighbor_four G huv hv
  have haH : IsThreeVertex H a := by
    unfold IsThreeVertex at ha ⊢
    rw [degree_deleteLeafEdge_eq_of_ne G huv hau hva.ne.symm]
    exact ha
  let p : H.Walk r a := .cons hHrb (.cons hHbv hHva.toWalk)
  have hp : p.IsPath := by
    have htail : (Walk.cons hHbv hHva.toWalk).IsPath := by
      apply (Walk.IsPath.of_adj hHva).cons
      simp [hvb.ne.symm, hab.symm]
    apply htail.cons
    simp [hrv', hra, hbr.ne.symm]
  have hpThread : IsKThread H p 2 := by
    refine ⟨hp, by simp [p], hrH, haH, ?_⟩
    intro i hi0 hil
    have hi : i = 1 ∨ i = 2 := by
      have hlen : p.length = 3 := by simp [p]
      rw [hlen] at hil
      omega
    rcases hi with rfl | rfl
    · simpa [p] using hbH
    · simpa [p] using hvH
  refine ⟨p, hpThread, ?_, ?_⟩
  · simp [threadFirstEdge, p]
  · simp [threadLastEdge, p, Sym2.eq_swap]

set_option maxHeartbeats 1200000 in
theorem palette_safe_three_matching_two_other
    (hsub : IsSubcubic G) (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsThreeVertex G a)
    (hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (beta i : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hmatch : VertexSeesMatching G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b) :
    ¬ ∀ j : Fin 4, VertexSeesInduced G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j := by
  let H := deleteLeafEdge G huv
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let B : G.edgeSet := ⟨s(v, b), hvb⟩
  let base := leafBaseFour G huv small
  let final := recolor G base E (some i)
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hBE : B ≠ E := by
    intro heq
    have huB : u ∈ (B : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = b := by simpa [B] using huB
    exact hc.elim huv.ne hbu.symm
  have hAB : A ≠ B := by
    intro heq
    have hbA : b ∈ (A : Sym2 V) := by rw [heq]; simp [B]
    have hc : b = v ∨ b = a := by simpa [A] using hbA
    exact hc.elim hvb.ne.symm (fun h ↦ hab h.symm)
  have hAD : A ∈ RetainedEdges H G := by
    simpa [H, E] using (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hBD : B ∈ RetainedEdges H G := by
    simpa [H, E] using (mem_retained_deleteLeafEdge_iff G huv B).mpr hBE
  have hvalidD : IsOneTwoColoringOn G (RetainedEdges H G) base := by
    simpa [H, base] using transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hvalidFinalOn := hvalidD.extend_one G
    (by simpa [H, E] using leafEdge_not_mem_retained G huv)
    (by simpa [H, base, E] using hi)
  have hvalidFinal : IsOneTwoColoring G final := by
    rw [insert_leafEdge_retained_eq_univ G huv] at hvalidFinalOn
    simpa [H, final, base, E, IsOneTwoColoring] using hvalidFinalOn
  have hfinalA : final A = none := by
    simpa [final, base, hAE] using hA
  have hfinalB : final B = some beta := by
    simpa [final, base, hBE] using hB
  obtain ⟨r, hrv, hbr⟩ := exists_other_neighbor_of_isTwoVertex G hb hvb.symm
  let C : G.edgeSet := ⟨s(b, r), hbr⟩
  have hCE : C ≠ E := by
    intro heq
    have hbE : b ∈ (E : Sym2 V) := by rw [← heq]; simp [C]
    have hc : b = u ∨ b = v := by simpa [E] using hbE
    exact hc.elim hbu hvb.ne.symm
  have hAC : A ≠ C := by
    intro heq
    have hbA : b ∈ (A : Sym2 V) := by rw [heq]; simp [C]
    have hc : b = v ∨ b = a := by simpa [A] using hbA
    exact hc.elim hvb.ne.symm (fun h ↦ hab h.symm)
  have hCD : C ∈ RetainedEdges H G := by
    simpa [H, E] using (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hfinalC : final C = none := by
    exact other_edge_matching_of_two_vertex G hb hvb hbr hrv final beta
      (by simpa [B] using hfinalB) hmatch
  have hbaseC : base C = none := by
    simpa [final, hCE] using hfinalC
  intro hall
  have hrpos : 0 < G.degree r := by
    rw [G.degree_pos_iff_exists_adj r]
    exact ⟨b, hbr.symm⟩
  have hrle : G.degree r ≤ 3 := hsub r
  by_cases hrThree : IsThreeVertex G r
  · have hru : r ≠ u := by
      intro hru
      subst r
      have hbEq : b = v := eq_neighbor_of_degree_eq_one G hu huv hbr.symm
      exact hvb.ne hbEq.symm
    have hnab : ¬ G.Adj a b :=
      not_adj_other_neighbors_of_girth_sixteen G hgirth hva hvb hab
    obtain ⟨p, hp, hfirstVal, hlastVal⟩ :=
      exists_vanished_twoThread_deleteLeafEdge G hgirth hu huv hv ha hb hva hvb hab hau hbu
        hrv hbr hrThree
    let AH : H.edgeSet := ⟨A.1, hAD⟩
    let BH : H.edgeSet := ⟨B.1, hBD⟩
    let CH : H.edgeSet := ⟨C.1, hCD⟩
    have hfirst : threadFirstEdge H p hp = CH := by
      apply Subtype.ext
      simpa [H, C, CH, Sym2.eq_swap] using hfirstVal
    have hlast : threadLastEdge H p hp = AH := by
      apply Subtype.ext
      simpa [H, A, AH] using hlastVal
    have hsmallA : small AH = none := by
      change transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small A = none at hA
      rw [transportColoringToSupergraph_of_mem
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small hAD] at hA
      simpa [AH, A] using hA
    have hsmallC : small CH = none := by
      change transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small C = none at hbaseC
      rw [transportColoringToSupergraph_of_mem
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small hCD] at hbaseC
      simpa [CH, C] using hbaseC
    have hExtR : ExternalEdgesInduced H small r CH :=
      externalEdgesInduced_of_valid_matching_four H hsmall.valid
        (by simp [CH, C]) hsmallC
    have hExtA : ExternalEdgesInduced H small a AH :=
      externalEdgesInduced_of_valid_matching_four H hsmall.valid
        (by simp [AH, A]) hsmallA
    have hne : ExternalInducedColors H small r CH ≠
        ExternalInducedColors H small a AH := by
      have hcondition : ConditionThree H small := hsmall.conditionThree
      have hc3 := hcondition r a p hp
      rw [hfirst, hlast] at hc3
      exact hc3 hExtR hExtA
    have hrH : IsThreeVertex H r := by
      unfold IsThreeVertex at hrThree ⊢
      rw [degree_deleteLeafEdge_eq_of_ne G huv hru hrv]
      exact hrThree
    have haH : IsThreeVertex H a := by
      unfold IsThreeVertex at ha ⊢
      rw [degree_deleteLeafEdge_eq_of_ne G huv hau hva.ne.symm]
      exact ha
    have hcardR : (ExternalInducedColors H small r CH).ncard = 2 := by
      apply longPair_externalInducedColors_ncard_eq_two_of_validOn_matching H
        Set.univ hrH small hsmall.valid
      · simp
      · simp [CH, C]
      · exact hsmallC
    have hcardA : (ExternalInducedColors H small a AH).ncard = 2 := by
      apply longPair_externalInducedColors_ncard_eq_two_of_validOn_matching H
        Set.univ haH small hsmall.valid
      · simp
      · simp [AH, A]
      · exact hsmallA
    have hsubset : ExternalInducedColors H small a AH ⊆
        ExternalInducedColors H small r CH := by
      intro j hj
      obtain ⟨eH, heExt, hej⟩ := hj
      let eG : G.edgeSet := edgeEmbeddingOfLE
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) eH
      have heGD : eG ∈ RetainedEdges H G := by
        exact edgeEmbeddingOfLE_mem_retained
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) eH
      have heGA : a ∈ (eG : Sym2 V) := by simpa [eG] using heExt.1
      have heGbase : base eG = some j := by
        simpa [base, eG, H] using hej
      have heGE : eG ≠ E := by
        exact (mem_retained_deleteLeafEdge_iff G huv eG).mp
          (by simpa [H] using heGD)
      have heGfinal : final eG = some j := by
        simpa [final, heGE] using heGbase
      have hji : j ≠ i := by
        intro hji
        subst j
        have hpairs := hvalidFinal E (by simp) eG (by simp) heGE.symm
        have hsep : InducedSeparated G E eG := by
          simpa [final, heGfinal] using hpairs
        apply hsep.2
        exact ⟨v, by simp [E], a, heGA, hva⟩
      have hjbeta : j ≠ beta := by
        intro hjbeta
        subst j
        have heGB : eG ≠ B := by
          intro heq
          have haB : a ∈ (B : Sym2 V) := heq ▸ heGA
          have hc : a = v ∨ a = b := by simpa [B] using haB
          exact hc.elim hva.ne.symm hab
        have hpairs := hvalidD B hBD eG heGD heGB.symm
        have hbaseB : base B = some beta := by simpa [base, B] using hB
        have hsep : InducedSeparated G B eG := by
          simpa [hbaseB, heGbase] using hpairs
        apply hsep.2
        exact ⟨v, by simp [B], a, heGA, hva⟩
      obtain ⟨f, hfj, z, hzf, hbz⟩ :=
        (vertexSeesInduced_iff G final b j).mp (hall j)
      have hfE : f ≠ E := by
        intro hEq
        subst f
        have : some i = some j := by simpa [final] using hfj
        exact hji (Option.some.inj this).symm
      have hfA : f ≠ A := by
        intro hEq
        subst f
        rw [hfinalA] at hfj
        simp at hfj
      have hfB : f ≠ B := by
        intro hEq
        subst f
        have : some beta = some j := hfinalB.symm.trans hfj
        exact hjbeta (Option.some.inj this).symm
      have hfC : f ≠ C := by
        intro hEq
        subst f
        rw [hfinalC] at hfj
        simp at hfj
      have hfD : f ∈ RetainedEdges H G := by
        simpa [H, E] using (mem_retained_deleteLeafEdge_iff G huv f).mpr hfE
      have hfBase : base f = some j := by
        simpa [final, hfE] using hfj
      have hzr : z = r := by
        rcases hbz with hzb | hbz
        · subst z
          rcases edge_eq_left_or_right_of_incident_two G hb hvb.symm hbr
              hrv.symm f hzf with hfB' | hfC'
          · exact False.elim (hfB (Subtype.ext (by
                simpa [B, Sym2.eq_swap] using hfB')))
          · exact False.elim (hfC (Subtype.ext (by simpa [C] using hfC')))
        · have hzN : z ∈ ({v, r} : Finset V) := by
            rw [← neighborFinset_eq_pair_of_isTwoVertex G hb hvb.symm hbr
              hrv.symm]
            exact (G.mem_neighborFinset b z).mpr hbz
          have hz : z = v ∨ z = r := by simpa using hzN
          rcases hz with hzv | hzr
          · subst z
            rcases retained_edge_incident_three_eq_first_or_second G huv hva
                hvb hN f (by simpa [H] using hfD) hzf with hfa | hfb
            · exact False.elim (hfA hfa)
            · exact False.elim (hfB hfb)
          · exact hzr
      subst z
      let fH : H.edgeSet := ⟨f.1, hfD⟩
      have hfSmall : small fH = some j := by
        change transportColoringToSupergraph
            (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small f = some j at hfBase
        rw [transportColoringToSupergraph_of_mem
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
          hfD] at hfBase
        simpa [fH] using hfBase
      refine ⟨fH, ⟨by simpa [fH] using hzf, ?_⟩, hfSmall⟩
      intro hEq
      apply hfC
      apply Subtype.ext
      simpa [fH, CH] using congrArg Subtype.val hEq
    have heq : ExternalInducedColors H small a AH =
        ExternalInducedColors H small r CH := by
      apply Set.eq_of_subset_of_ncard_le hsubset
      rw [hcardR, hcardA]
    exact hne heq.symm
  · have hrCases : G.degree r = 1 ∨ G.degree r = 2 := by
      unfold IsThreeVertex at hrThree
      omega
    rcases hrCases with hrOne | hrTwo
    · have hfour := card_vertexVisibleEdgeFinset_le_four_of_adjacent_leaf
          G hsub hb hbr hrOne
      have hfive := five_le_card_vertexVisibleEdgeFinset_of_matching_and_full_four
        G hmatch hall
      omega
    · apply paletteCondition_at_of_two_visible_matching_four G hsub hb hbr
        hrTwo A C hAC hfinalA hfinalC
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inr hvb.symm)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
      · exact hall

theorem exists_goodFour_leaf_three_matching_to_three_other_two
    (hsub : IsSubcubic G) (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsThreeVertex G a)
    (hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (beta : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let H := deleteLeafEdge G huv
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let base := leafBaseFour G huv small
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hAD : A ∈ RetainedEdges H G := by
    simpa [H, E] using (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  let AH : H.edgeSet := ⟨A.1, hAD⟩
  have hsmallA : small AH = none := by
    change transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small A = none at hA
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small hAD] at hA
    simpa [AH, A] using hA
  have hmatchH : VertexSeesMatching H small v := by
    rw [vertexSeesMatching_iff]
    exact ⟨AH, hsmallA, by simp [AH, A]⟩
  obtain ⟨i, hi⟩ := exists_available_leafEdge_at_three_neighbor_four G
    hu huv hv small hsmall hmatchH
  let final := recolor G base E (some i)
  have hbaseTwo : ConditionTwo G base := by
    exact conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have haNot : ¬ IsTwoVertex G a := by
    intro haTwo
    unfold IsThreeVertex at ha
    unfold IsTwoVertex at haTwo
    omega
  have hsafeA : IsTwoVertex G a → VertexSeesMatching G final a →
      ¬ ∀ j : Fin 4, VertexSeesInduced G final a j := by
    intro haTwo
    exact False.elim (haNot haTwo)
  have hsafeB : IsTwoVertex G b → VertexSeesMatching G final b →
      ¬ ∀ j : Fin 4, VertexSeesInduced G final b j := by
    intro _ hmatch
    exact palette_safe_three_matching_two_other G hsub hgirth hu huv hv
      ha hb hva hvb hab hau hbu hN small hsmall beta i hA hB
      (by simpa [H, base, E] using hi) (by simpa [final, base, E] using hmatch)
  have htwo : ConditionTwo G final := by
    apply conditionTwo_recolor_leafEdge_at_three_neighbor_four G hu huv hv
      hva hvb hN base hbaseTwo i
    · simpa [final] using hsafeA
    · simpa [final] using hsafeB
  have hbaseThree : ConditionThree G base := by
    exact conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hthree : ConditionThree G final := by
    exact ConditionThree.recolor_leafEdge_of_matching_otherNeighbor_not_two G
      hu huv hva hau haNot base i (by simpa [base, A] using hA) hbaseThree
  refine ⟨final, ?_⟩
  apply goodFour_recolor_leafEdge_of_available G hu huv small hsmall A
    (by simpa [H] using hAD) (by simpa [base, A] using hA)
    (by simp [A]) i
  · simpa [H, base, E] using hi
  · simpa [final, base, E] using htwo
  · simpa [final, base, E] using hthree

/-- If the matching arm ends in a leaf and the other arm in a two-vertex,
the blocker count leaves two induced choices.  Only one of them can complete
the forbidden palette at the two-vertex. -/
theorem exists_goodFour_leaf_three_matching_to_leaf_other_two
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : G.degree a = 1)
    (hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let H := deleteLeafEdge G huv
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let base := leafBaseFour G huv small
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hAD : A ∈ RetainedEdges H G := by
    simpa [H, E] using (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hactive : (activeInducedBlockerEdgesOn G
      (RetainedEdges H G) base E).card ≤ 2 := by
    have hcount := card_activeBlockers_leafEdge_add_one_le_three_four G hu huv
      hva hvb hN base (by simpa [base, A] using hA)
    unfold IsTwoVertex at hb
    have hcount' : (activeInducedBlockerEdgesOn G
        (RetainedEdges H G) base E).card + 1 ≤ G.degree a + G.degree b := by
      simpa [H, base, E] using hcount
    rw [ha, hb] at hcount'
    omega
  have hblocked : (blockedInducedColorsOn G
      (RetainedEdges H G) base E).card ≤ 2 :=
    (card_blockedInducedColorsOn_le_card_activeBlockers G
      (RetainedEdges H G) base E).trans hactive
  obtain ⟨i, j, hij, hi, hj⟩ :=
    exists_two_distinct_available_induced_of_card_blocked_add_two_le G
      (RetainedEdges H G) base E (by omega)
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have haNot : ¬ IsTwoVertex G a := by
    intro haTwo
    unfold IsTwoVertex at haTwo
    omega
  let Bad (c : Fin 4) : Prop :=
    VertexSeesMatching G (recolor G base E (some c)) b ∧
      ∀ t : Fin 4, VertexSeesInduced G (recolor G base E (some c)) b t
  have makeGood (c : Fin 4)
      (hc : ColorAvailableOn G (RetainedEdges H G) base E (some c))
      (hsafe : ¬ Bad c) :
      GoodFour G (recolor G base E (some c)) := by
    let final := recolor G base E (some c)
    have hsafeA : IsTwoVertex G a → VertexSeesMatching G final a →
        ¬ ∀ t : Fin 4, VertexSeesInduced G final a t := by
      intro haTwo
      exact False.elim (haNot haTwo)
    have hsafeB : IsTwoVertex G b → VertexSeesMatching G final b →
        ¬ ∀ t : Fin 4, VertexSeesInduced G final b t := by
      intro _ hmatch hall
      exact hsafe ⟨hmatch, hall⟩
    have htwo : ConditionTwo G final := by
      apply conditionTwo_recolor_leafEdge_at_three_neighbor_four G hu huv hv
        hva hvb hN base hbaseTwo c
      · simpa [final] using hsafeA
      · simpa [final] using hsafeB
    have hthree : ConditionThree G final := by
      exact ConditionThree.recolor_leafEdge_of_matching_otherNeighbor_not_two G
        hu huv hva hau haNot base c (by simpa [base, A] using hA) hbaseThree
    apply goodFour_recolor_leafEdge_of_available G hu huv small hsmall A
      (by simpa [H] using hAD) (by simpa [base, A] using hA)
      (by simp [A]) c
    · simpa [H, base, E] using hc
    · simpa [final, base, E] using htwo
    · simpa [final, base, E] using hthree
  by_cases hbadI : Bad i
  · refine ⟨recolor G base E (some j), makeGood j hj ?_⟩
    intro hbadJ
    exact full_palette_leaf_colour_unique_at_two_four G huv base hbaseTwo hb hij
      hbadI.1 hbadI.2 hbadJ.1 hbadJ.2
  · exact ⟨recolor G base E (some i), makeGood i hi hbadI⟩

/-- Once the retained matching arm does not end in a two-vertex, all
degree possibilities on that arm are covered.  If the other arm is not a
two-vertex this is the easy branch; otherwise subcubicity says that the
matching arm ends either in a leaf or in a three-vertex, which are the two
preceding local reductions. -/
theorem exists_goodFour_leaf_three_of_matching_neighbor_not_two
    (hsub : IsSubcubic G) (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (beta : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (haNot : ¬ IsTwoVertex G a) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  by_cases hbNot : ¬ IsTwoVertex G b
  · exact exists_goodFour_extension_leaf_of_three_neighbor_both_not_two
      G hsub hu huv hv hva hvb hau hN haNot hbNot small hsmall hA
  · have hbTwo : IsTwoVertex G b := not_not.mp hbNot
    have haPos : 0 < G.degree a := by
      rw [G.degree_pos_iff_exists_adj a]
      exact ⟨v, hva.symm⟩
    have haLe : G.degree a ≤ 3 := hsub a
    have haCases : G.degree a = 1 ∨ G.degree a = 2 ∨ G.degree a = 3 := by
      omega
    rcases haCases with haOne | haTwo | haThree
    · exact exists_goodFour_leaf_three_matching_to_leaf_other_two G hsub
        hu huv hv haOne hbTwo hva hvb hab hau hbu hN small hsmall hA
    · exact False.elim (haNot haTwo)
    · exact exists_goodFour_leaf_three_matching_to_three_other_two G hsub
        hgirth hu huv hv haThree hbTwo hva hvb hab hau hbu hN small hsmall
        beta hA hB

/-- Starting from the matching edge supplied by minimality, either the leaf
already extends or the matching arm in the canonical degree-three normal
form ends at a two-vertex.  Thus the latter is the only local configuration
which remains after the reductions in this module. -/
theorem exists_goodFour_leaf_three_or_matching_two_normal_form
    (hsub : IsSubcubic G) (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (m : G.edgeSet)
    (hmD : m ∈ RetainedEdges (deleteLeafEdge G huv) G)
    (hm : leafBaseFour G huv small m = none)
    (hvm : v ∈ (m : Sym2 V)) :
    (∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour) ∨
      ∃ (a b : V) (hva : G.Adj v a) (hvb : G.Adj v b)
          (beta : Fin 4),
        a ≠ b ∧ a ≠ u ∧ b ≠ u ∧
        G.neighborFinset v = {u, a, b} ∧
        IsTwoVertex G a ∧
        leafBaseFour G huv small
            (⟨s(v, a), hva⟩ : G.edgeSet) = none ∧
        leafBaseFour G huv small
            (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta := by
  obtain ⟨a, b, hva, hvb, beta, hab, hau, hbu, hN, hA, hB⟩ :=
    exists_leaf_three_matching_normal_form G hu huv hv small hsmall m hmD hm hvm
  by_cases haTwo : IsTwoVertex G a
  · exact Or.inr ⟨a, b, hva, hvb, beta, hab, hau, hbu, hN, haTwo, hA, hB⟩
  · exact Or.inl
      (exists_goodFour_leaf_three_of_matching_neighbor_not_two G hsub hgirth
        hu huv hv hva hvb hab hau hbu hN small hsmall beta hA hB haTwo)

/-- A certified two-thread cannot start with `v-a` when `a` is a
two-vertex whose other neighbour is not a two-vertex. -/
theorem no_twoThread_firstEdge_of_two_continuation_not_two
    {v a r t : V} (ha : IsTwoVertex G a)
    (hva : G.Adj v a) (har : G.Adj a r) (hrv : r ≠ v)
    (hrNot : ¬ IsTwoVertex G r)
    (p : G.Walk v t) (hp : IsKThread G p 2)
    (hfirst : threadFirstEdge G p hp =
      (⟨s(v, a), hva⟩ : G.edgeSet)) : False := by
  have hone : p.getVert 1 = a :=
    getVert_one_eq_of_threadFirstEdge_eq G hva p hp hfirst
  have hlen : p.length = 3 := by simpa using hp.length
  have h12 : G.Adj a (p.getVert 2) := by
    have hstep := p.adj_getVert_succ (i := 1) (by omega)
    simpa [hone] using hstep
  have hN : G.neighborFinset a = {v, r} :=
    neighborFinset_eq_pair_of_isTwoVertex G ha hva.symm har hrv.symm
  have hmem : p.getVert 2 ∈ ({v, r} : Finset V) := by
    rw [← hN]
    exact (G.mem_neighborFinset _ _).mpr h12
  have hcases : p.getVert 2 = v ∨ p.getVert 2 = r := by
    simpa using hmem
  have hneV : p.getVert 2 ≠ v := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show 2 ∈ {z : ℕ | z ≤ p.length} by simp [hlen])
      (show 0 ∈ {z : ℕ | z ≤ p.length} by simp)
      (show p.getVert 2 = p.getVert 0 by simpa using heq)
    omega
  have htwo : IsTwoVertex G (p.getVert 2) :=
    IsKThread.internal_two G hp (i := 2) (by omega) (by omega)
  exact hrNot (by rw [(hcases.resolve_left hneV).symm]; exact htwo)

/-- The first two internal vertices of a two-thread are forced by two
successive degree-two neighbourhoods.  This is the geometric core used to
recognize the unique critical thread through a matching leaf arm. -/
theorem twoThread_getVert_two_eq_of_firstEdge_and_two
    {v a r y : V} (ha : IsTwoVertex G a)
    (hva : G.Adj v a) (har : G.Adj a r) (hrv : r ≠ v)
    (p : G.Walk v y) (hp : IsKThread G p 2)
    (hfirst : threadFirstEdge G p hp =
      (⟨s(v, a), hva⟩ : G.edgeSet)) : p.getVert 2 = r := by
  have hone : p.getVert 1 = a :=
    getVert_one_eq_of_threadFirstEdge_eq G hva p hp hfirst
  have hlen : p.length = 3 := by simpa using hp.length
  have h12 : G.Adj a (p.getVert 2) := by
    have hstep := p.adj_getVert_succ (i := 1) (by omega)
    simpa [hone] using hstep
  have hN : G.neighborFinset a = {v, r} :=
    neighborFinset_eq_pair_of_isTwoVertex G ha hva.symm har hrv.symm
  have hmem : p.getVert 2 ∈ ({v, r} : Finset V) := by
    rw [← hN]
    exact (G.mem_neighborFinset _ _).mpr h12
  have hcases : p.getVert 2 = v ∨ p.getVert 2 = r := by
    simpa using hmem
  have hneV : p.getVert 2 ≠ v := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show 2 ∈ {z : ℕ | z ≤ p.length} by simp [hlen])
      (show 0 ∈ {z : ℕ | z ≤ p.length} by simp)
      (show p.getVert 2 = p.getVert 0 by simpa using heq)
    omega
  exact hcases.resolve_left hneV

/-- If the first two internal vertices are the displayed two-vertices,
the far endpoint of the directed two-thread is their uniquely determined
other neighbour. -/
theorem twoThread_endpoint_eq_of_firstEdge_and_two_two
    {v a r t y : V} (ha : IsTwoVertex G a) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (har : G.Adj a r) (hrv : r ≠ v)
    (hrt : G.Adj r t) (hta : t ≠ a)
    (p : G.Walk v y) (hp : IsKThread G p 2)
    (hfirst : threadFirstEdge G p hp =
      (⟨s(v, a), hva⟩ : G.edgeSet)) : y = t := by
  have htwo : p.getVert 2 = r :=
    twoThread_getVert_two_eq_of_firstEdge_and_two G ha hva har hrv p hp hfirst
  have hlen : p.length = 3 := by simpa using hp.length
  have h23 : G.Adj r y := by
    have hstep := p.adj_getVert_succ (i := 2) (by omega)
    have hend : p.getVert 3 = y := by
      rw [← hlen]
      exact p.getVert_length
    simpa [htwo, hend] using hstep
  have hN : G.neighborFinset r = {a, t} :=
    neighborFinset_eq_pair_of_isTwoVertex G hr har.symm hrt hta.symm
  have hymem : y ∈ ({a, t} : Finset V) := by
    rw [← hN]
    exact (G.mem_neighborFinset _ _).mpr h23
  have hycases : y = a ∨ y = t := by simpa using hymem
  have hyneA : y ≠ a := by
    intro hya
    have hone : p.getVert 1 = a :=
      getVert_one_eq_of_threadFirstEdge_eq G hva p hp hfirst
    have hend : p.getVert 3 = y := by
      rw [← hlen]
      exact p.getVert_length
    have hinj := hp.1.getVert_injOn
      (show 3 ∈ {z : ℕ | z ≤ p.length} by simp [hlen])
      (show 1 ∈ {z : ℕ | z ≤ p.length} by simp [hlen])
      (show p.getVert 3 = p.getVert 1 by simpa [hend, hone] using hya)
    omega
  exact hycases.resolve_left hyneA

/-- With two successive two-vertices on the matching arm, a critical
Condition-3 thread would have to end at their displayed continuation.
Consequently no failure is possible when that continuation is not a
three-vertex. -/
theorem ConditionThree.recolor_leafEdge_of_matching_two_two_endpoint_not_three
    {u v a r t : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (ha : IsTwoVertex G a) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (har : G.Adj a r) (hrv : r ≠ v)
    (hrt : G.Adj r t) (hta : t ≠ a) (hau : a ≠ u)
    (htNot : ¬ IsThreeVertex G t)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hold : ConditionThree G old) :
    ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  apply ConditionThree.recolor_leafEdge_of_matching_otherNeighbor G
    hu huv hva hau old i hA hold
  intro x y p hp hcritical _hleft _hright
  exfalso
  rcases hcritical with ⟨hx, hfirst⟩ | ⟨hy, hlast⟩
  · subst x
    apply htNot
    have hyt : y = t :=
      twoThread_endpoint_eq_of_firstEdge_and_two_two G ha hr hva har hrv hrt
        hta p hp hfirst
    simpa [hyt] using hp.end_three
  · subst y
    apply htNot
    have hxt : x = t :=
      twoThread_endpoint_eq_of_firstEdge_and_two_two G ha hr hva har hrv hrt
        hta p.reverse hp.reverse (by
          rw [threadFirstEdge_reverse_two G p hp]
          exact hlast)
    simpa [hxt] using hp.start_three

/-- If the matching arm runs through a two-vertex but its continuation is
not a two-vertex, recolouring the leaf edge cannot create a Condition-3
failure: the only critical directed thread would have to use that
continuation as its second internal two-vertex. -/
theorem ConditionThree.recolor_leafEdge_of_matching_two_continuation_not_two
    {u v a r : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (ha : IsTwoVertex G a) (hva : G.Adj v a)
    (har : G.Adj a r) (hrv : r ≠ v) (hau : a ≠ u)
    (hrNot : ¬ IsTwoVertex G r)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hold : ConditionThree G old) :
    ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  apply ConditionThree.recolor_leafEdge_of_matching_otherNeighbor G
    hu huv hva hau old i hA hold
  intro x y p hp hcritical _hleft _hright
  exfalso
  rcases hcritical with ⟨hx, hfirst⟩ | ⟨hy, hlast⟩
  · subst x
    exact no_twoThread_firstEdge_of_two_continuation_not_two G ha hva har
      hrv hrNot p hp hfirst
  · subst y
    apply no_twoThread_firstEdge_of_two_continuation_not_two G ha hva har
      hrv hrNot p.reverse hp.reverse
    rw [threadFirstEdge_reverse_two G p hp]
    exact hlast

/-- If the matching arm first meets a two-vertex and then a leaf, any
available leaf-edge colour is safe: Condition 2 follows from the four-edge
visibility bound at the adjacent leaf, while Condition 3 follows from the
non-two continuation criterion above. -/
theorem exists_goodFour_leaf_three_matching_two_continuation_leaf
    (hsub : IsSubcubic G)
    {u v a b r : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hbNot : ¬ IsTwoVertex G b)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v) (hrOne : G.degree r = 1)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let H := deleteLeafEdge G huv
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  have hAE : A ≠ (⟨s(u, v), huv⟩ : G.edgeSet) := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hAD : A ∈ RetainedEdges H G := by
    simpa [H] using (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  let AH : H.edgeSet := ⟨A.1, hAD⟩
  have hsmallA : small AH = none := by
    change transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small A = none at hA
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small hAD] at hA
    simpa [AH, A] using hA
  have hmatchH : VertexSeesMatching H small v := by
    rw [vertexSeesMatching_iff]
    exact ⟨AH, hsmallA, by simp [AH, A]⟩
  obtain ⟨i, hi⟩ := exists_available_leafEdge_at_three_neighbor_four G
    hu huv hv small hsmall hmatchH
  have hrNot : ¬ IsTwoVertex G r := by
    intro hrTwo
    unfold IsTwoVertex at hrTwo
    omega
  have hbaseThree : ConditionThree G (leafBaseFour G huv small) :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hthree : ConditionThree G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) :=
    ConditionThree.recolor_leafEdge_of_matching_two_continuation_not_two G
      hu huv ha hva har hrv hau hrNot (leafBaseFour G huv small) i hA
      hbaseThree
  have hsafe : ¬ (VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j) := by
    rintro ⟨hmatch, hall⟩
    exact (conditionTwo_at_adjacent_leaf G hsub ha har hrOne hmatch) hall
  have hbaseTwo : ConditionTwo G (leafBaseFour G huv small) :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have htwo : ConditionTwo G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
    apply conditionTwo_recolor_leafEdge_at_three_neighbor_four G hu huv hv
      hva hvb hN (leafBaseFour G huv small) hbaseTwo i
    · intro _ hmatch hall
      exact hsafe ⟨hmatch, hall⟩
    · intro hb
      exact False.elim (hbNot hb)
  refine ⟨recolor G (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i), ?_⟩
  exact goodFour_recolor_leafEdge_of_available G hu huv small hsmall A hAD
    (by simpa [A] using hA) (by simp [A]) i
    (by simpa [H] using hi) htwo hthree

/-- Local assembly on the remaining orientation: the matching arm ends at
a two-vertex and the other arm is not a two-vertex.  Once the single local
Condition-2 obligation and Condition 3 are safe, availability supplies all
the other clauses of a good colouring. -/
theorem goodFour_leaf_three_matching_two_of_available_safe
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbNot : ¬ IsTwoVertex G b)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (i : Fin 4)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hsafe : ¬ (VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j))
    (hthree : ConditionThree G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i))) :
    GoodFour G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  have hAE : A ≠ (⟨s(u, v), huv⟩ : G.edgeSet) := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hbaseTwo : ConditionTwo G (leafBaseFour G huv small) :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have htwo : ConditionTwo G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
    apply conditionTwo_recolor_leafEdge_at_three_neighbor_four G hu huv hv
      hva hvb hN (leafBaseFour G huv small) hbaseTwo i
    · intro _ hmatch hall
      exact hsafe ⟨hmatch, hall⟩
    · intro hb
      exact False.elim (hbNot hb)
  exact goodFour_recolor_leafEdge_of_available G hu huv small hsmall A hAD
    (by simpa [A] using hA) (by simp [A]) i hi htwo hthree

/-- If the matching two-vertex continues to a non-two-vertex, two available
leaf colours suffice: Condition 3 is safe for both, and Condition 2 can
reject at most one of them. -/
theorem exists_goodFour_leaf_three_matching_two_continuation_not_two_of_two_available
    (hsub : IsSubcubic G)
    {u v a b r : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hbNot : ¬ IsTwoVertex G b)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v) (hrNot : ¬ IsTwoVertex G r)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (beta : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (i j : Fin 4) (hij : i ≠ j)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hj : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let Bad (c : Fin 4) : Prop :=
    VertexSeesMatching G (recolor G base E (some c)) a ∧
      ∀ t : Fin 4, VertexSeesInduced G (recolor G base E (some c)) a t
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hthree (c : Fin 4) :
      ConditionThree G (recolor G base E (some c)) := by
    simpa [base, E] using
      ConditionThree.recolor_leafEdge_of_matching_two_continuation_not_two G
        hu huv ha hva har hrv hau hrNot base c (by simpa [base] using hA)
        hbaseThree
  have makeGood (c : Fin 4)
      (hc : ColorAvailableOn G
        (RetainedEdges (deleteLeafEdge G huv) G) base E (some c))
      (hbad : ¬ Bad c) : GoodFour G (recolor G base E (some c)) := by
    exact goodFour_leaf_three_matching_two_of_available_safe G hsub hu huv hv
      ha hva hvb hau hbNot hN small hsmall c (by simpa [base, E] using hc)
      (by simpa [base] using hA) (by simpa [Bad, base, E] using hbad)
      (hthree c)
  by_cases hbadI : Bad i
  · refine ⟨recolor G base E (some j), makeGood j
        (by simpa [base, E] using hj) ?_⟩
    intro hbadJ
    exact full_palette_leaf_colour_unique_at_two_four G huv base hbaseTwo ha hij
      (by simpa [Bad, base, E] using hbadI.1)
      (by simpa [Bad, base, E] using hbadI.2)
      (by simpa [Bad, base, E] using hbadJ.1)
      (by simpa [Bad, base, E] using hbadJ.2)
  · exact ⟨recolor G base E (some i), makeGood i
        (by simpa [base, E] using hi) hbadI⟩

/-- In the `(matching arm degree 2, other arm leaf)` branch the sharp
blocker bound automatically supplies the two colours needed above.  Hence
the only unresolved continuation of the matching arm is itself a
two-vertex. -/
theorem exists_goodFour_leaf_three_matching_two_other_leaf_of_continuation_not_two
    (hsub : IsSubcubic G)
    {u v a b r : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : G.degree b = 1)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v) (hrNot : ¬ IsTwoVertex G r)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (beta : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  have hactive : (activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base E).card ≤ 2 := by
    have hcount := card_activeBlockers_leafEdge_add_one_le_three_four G hu huv
      hva hvb hN base (by simpa [base] using hA)
    unfold IsTwoVertex at ha
    change (activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base E).card + 1 ≤
        G.degree a + G.degree b at hcount
    rw [ha, hb] at hcount
    omega
  have hblocked : (blockedInducedColorsOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base E).card ≤ 2 :=
    (card_blockedInducedColorsOn_le_card_activeBlockers G
      (RetainedEdges (deleteLeafEdge G huv) G) base E).trans hactive
  obtain ⟨i, j, hij, hi, hj⟩ :=
    exists_two_distinct_available_induced_of_card_blocked_add_two_le G
      (RetainedEdges (deleteLeafEdge G huv) G) base E (by omega)
  have hbNot : ¬ IsTwoVertex G b := by
    intro hbTwo
    unfold IsTwoVertex at hbTwo
    omega
  exact exists_goodFour_leaf_three_matching_two_continuation_not_two_of_two_available
    G hsub hu huv hv ha hva hvb hau hbu hab hbNot hN har hrv hrNot small
    hsmall beta hA hB i j hij (by simpa [base, E] using hi)
    (by simpa [base, E] using hj)

/-- The same leaf-other-arm branch also extends when the matching arm has
two successive two-vertices but their continuation is not a three-vertex.
The two available colours handle Condition 2, and the uniquely forced
two-thread geometry makes Condition 3 automatic. -/
theorem exists_goodFour_leaf_three_matching_two_other_leaf_of_two_two_endpoint_not_three
    (hsub : IsSubcubic G)
    {u v a b r t : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : G.degree b = 1) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v)
    (hrt : G.Adj r t) (hta : t ≠ a) (htNot : ¬ IsThreeVertex G t)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  have hactive : (activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base E).card ≤ 2 := by
    have hcount := card_activeBlockers_leafEdge_add_one_le_three_four G hu huv
      hva hvb hN base (by simpa [base] using hA)
    unfold IsTwoVertex at ha
    change (activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base E).card + 1 ≤
        G.degree a + G.degree b at hcount
    rw [ha, hb] at hcount
    omega
  have hblocked : (blockedInducedColorsOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base E).card ≤ 2 :=
    (card_blockedInducedColorsOn_le_card_activeBlockers G
      (RetainedEdges (deleteLeafEdge G huv) G) base E).trans hactive
  obtain ⟨i, j, hij, hi, hj⟩ :=
    exists_two_distinct_available_induced_of_card_blocked_add_two_le G
      (RetainedEdges (deleteLeafEdge G huv) G) base E (by omega)
  have hbNot : ¬ IsTwoVertex G b := by
    intro hbTwo
    unfold IsTwoVertex at hbTwo
    omega
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  let Bad (c : Fin 4) : Prop :=
    VertexSeesMatching G (recolor G base E (some c)) a ∧
      ∀ x : Fin 4, VertexSeesInduced G (recolor G base E (some c)) a x
  have hthree (c : Fin 4) :
      ConditionThree G (recolor G base E (some c)) := by
    simpa [base, E] using
      ConditionThree.recolor_leafEdge_of_matching_two_two_endpoint_not_three G
        hu huv ha hr hva har hrv hrt hta hau htNot base c
        (by simpa [base] using hA) hbaseThree
  have makeGood (c : Fin 4)
      (hc : ColorAvailableOn G
        (RetainedEdges (deleteLeafEdge G huv) G) base E (some c))
      (hbad : ¬ Bad c) : GoodFour G (recolor G base E (some c)) := by
    exact goodFour_leaf_three_matching_two_of_available_safe G hsub hu huv hv
      ha hva hvb hau hbNot hN small hsmall c (by simpa [base, E] using hc)
      (by simpa [base] using hA) (by simpa [Bad, base, E] using hbad)
      (hthree c)
  by_cases hbadI : Bad i
  · refine ⟨recolor G base E (some j), makeGood j
        (by simpa [base, E] using hj) ?_⟩
    intro hbadJ
    exact full_palette_leaf_colour_unique_at_two_four G huv base hbaseTwo ha hij
      (by simpa [Bad, base, E] using hbadI.1)
      (by simpa [Bad, base, E] using hbadI.2)
      (by simpa [Bad, base, E] using hbadJ.1)
      (by simpa [Bad, base, E] using hbadJ.2)
  · exact ⟨recolor G base E (some i), makeGood i
        (by simpa [base, E] using hi) hbadI⟩

/-- Complete structural reduction of the leaf-other-arm case.  Either the
colouring extends, or the matching arm is exactly an ambient two-thread
whose far endpoint is a three-vertex. -/
theorem exists_goodFour_leaf_three_matching_two_other_leaf_or_twoThread
    (hsub : IsSubcubic G) (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : G.degree b = 1)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (beta : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta) :
    (∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour) ∨
      ∃ (t : V) (p : G.Walk v t) (hp : IsKThread G p 2),
        IsThreeVertex G t ∧
        threadFirstEdge G p hp = (⟨s(v, a), hva⟩ : G.edgeSet) := by
  obtain ⟨r, hrv, har⟩ :=
    exists_other_neighbor_of_isTwoVertex G ha hva.symm
  have hrPos : 0 < G.degree r := by
    rw [G.degree_pos_iff_exists_adj r]
    exact ⟨a, har.symm⟩
  have hrLe : G.degree r ≤ 3 := hsub r
  have hrCases : G.degree r = 1 ∨ G.degree r = 2 ∨ G.degree r = 3 := by
    omega
  rcases hrCases with hrOne | hrTwo | hrThree
  · left
    apply exists_goodFour_leaf_three_matching_two_other_leaf_of_continuation_not_two
      G hsub hu huv hv ha hb hva hvb hau hbu hab hN har hrv
      (by
        intro hrTwo'
        unfold IsTwoVertex at hrTwo'
        omega)
      small hsmall beta hA hB
  · have hrTwo' : IsTwoVertex G r := hrTwo
    obtain ⟨t, hta, hrt⟩ :=
      exists_other_neighbor_of_isTwoVertex G hrTwo' har.symm
    have htPos : 0 < G.degree t := by
      rw [G.degree_pos_iff_exists_adj t]
      exact ⟨r, hrt.symm⟩
    have htLe : G.degree t ≤ 3 := hsub t
    have htCases : G.degree t = 1 ∨ G.degree t = 2 ∨ G.degree t = 3 := by
      omega
    rcases htCases with htOne | htTwo | htThree
    · left
      apply exists_goodFour_leaf_three_matching_two_other_leaf_of_two_two_endpoint_not_three
        G hsub hu huv hv ha hb hrTwo' hva hvb hau hbu hab hN har hrv hrt
        hta (by
          intro htThree'
          unfold IsThreeVertex at htThree'
          omega)
        small hsmall hA
    · left
      apply exists_goodFour_leaf_three_matching_two_other_leaf_of_two_two_endpoint_not_three
        G hsub hu huv hv ha hb hrTwo' hva hvb hau hbu hab hN har hrv hrt
        hta (by
          intro htThree'
          unfold IsThreeVertex at htThree'
          omega)
        small hsmall hA
    · right
      have htv : t ≠ v := by
        intro htv
        subst t
        have hnvr : ¬ G.Adj v r :=
          not_adj_other_neighbors_of_girth_sixteen G hgirth hva.symm har
            hrv.symm
        exact hnvr hrt.symm
      let p : G.Walk v t := .cons hva (.cons har hrt.toWalk)
      have hpPath : p.IsPath := by
        have htail : (Walk.cons har hrt.toWalk).IsPath := by
          apply (Walk.IsPath.of_adj hrt).cons
          simp [har.ne, hta.symm]
        apply htail.cons
        simp [hva.ne, hrv.symm, htv.symm]
      have hpThread : IsKThread G p 2 := by
        refine ⟨hpPath, by simp [p], hv, htThree, ?_⟩
        intro i hi0 hil
        have hi : i = 1 ∨ i = 2 := by
          have hlen : p.length = 3 := by simp [p]
          rw [hlen] at hil
          omega
        rcases hi with rfl | rfl
        · simpa [p] using ha
        · simpa [p] using hrTwo'
      exact ⟨t, p, hpThread, htThree, by simp [threadFirstEdge, p]⟩
  · left
    apply exists_goodFour_leaf_three_matching_two_other_leaf_of_continuation_not_two
      G hsub hu huv hv ha hb hva hvb hau hbu hab hN har hrv
      (by
        intro hrTwo'
        unfold IsTwoVertex at hrTwo'
        omega)
      small hsmall beta hA hB

/-- With three pairwise distinct available colours on the leaf edge, the
remaining matching-two/non-two configuration always extends.  Condition 2
can reject at most one colour, and the two-colour Condition-3 theorem shows
that Condition 3 can reject at most one; hence one of three is safe for
both. -/
theorem exists_goodFour_leaf_three_matching_two_of_three_available
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hbNot : ¬ IsTwoVertex G b)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (beta : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hj : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some j))
    (hk : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some k)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let Bad (c : Fin 4) : Prop :=
    VertexSeesMatching G (recolor G base E (some c)) a ∧
      ∀ t : Fin 4, VertexSeesInduced G (recolor G base E (some c)) a t
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have bad_exclusive {c d : Fin 4} (hcd : c ≠ d)
      (hc : Bad c) (hd : Bad d) : False := by
    exact full_palette_leaf_colour_unique_at_two_four G huv base hbaseTwo ha hcd
      (by simpa [Bad, E, base] using hc.1)
      (by simpa [Bad, E, base] using hc.2)
      (by simpa [Bad, E, base] using hd.1)
      (by simpa [Bad, E, base] using hd.2)
  have c3_pair {c d : Fin 4} (hcd : c ≠ d)
      (hc : ColorAvailableOn G
        (RetainedEdges (deleteLeafEdge G huv) G) base E (some c))
      (hd : ColorAvailableOn G
        (RetainedEdges (deleteLeafEdge G huv) G) base E (some d)) :
      ConditionThree G (recolor G base E (some c)) ∨
        ConditionThree G (recolor G base E (some d)) := by
    simpa [base, E] using
      conditionThree_for_one_of_two_available_leaf_colours G hu huv hva hvb
        hau hbu hab hN base beta (by simpa [base] using hA)
        (by simpa [base] using hB) hbaseThree hcd
        (by simpa [base, E] using hc) (by simpa [base, E] using hd)
  have makeGood (c : Fin 4)
      (hc : ColorAvailableOn G
        (RetainedEdges (deleteLeafEdge G huv) G) base E (some c))
      (hbad : ¬ Bad c)
      (hthree : ConditionThree G (recolor G base E (some c))) :
      GoodFour G (recolor G base E (some c)) := by
    exact goodFour_leaf_three_matching_two_of_available_safe G hsub hu huv hv
      ha hva hvb hau hbNot hN small hsmall c
      (by simpa [base, E] using hc) (by simpa [base] using hA)
      (by simpa [Bad, base, E] using hbad) (by simpa [base, E] using hthree)
  by_cases h3i : ConditionThree G (recolor G base E (some i))
  · by_cases hbi : Bad i
    · rcases c3_pair hjk (by simpa [base, E] using hj)
          (by simpa [base, E] using hk) with h3j | h3k
      · refine ⟨recolor G base E (some j), makeGood j
            (by simpa [base, E] using hj) ?_ h3j⟩
        intro hbj
        exact bad_exclusive hij hbi hbj
      · refine ⟨recolor G base E (some k), makeGood k
            (by simpa [base, E] using hk) ?_ h3k⟩
        intro hbk
        exact bad_exclusive hik hbi hbk
    · exact ⟨recolor G base E (some i), makeGood i
          (by simpa [base, E] using hi) hbi h3i⟩
  · have h3j : ConditionThree G (recolor G base E (some j)) :=
      (c3_pair hij (by simpa [base, E] using hi)
        (by simpa [base, E] using hj)).resolve_left h3i
    have h3k : ConditionThree G (recolor G base E (some k)) :=
      (c3_pair hik (by simpa [base, E] using hi)
        (by simpa [base, E] using hk)).resolve_left h3i
    by_cases hbj : Bad j
    · refine ⟨recolor G base E (some k), makeGood k
          (by simpa [base, E] using hk) ?_ h3k⟩
      intro hbk
      exact bad_exclusive hjk hbj hbk
    · exact ⟨recolor G base E (some j), makeGood j
          (by simpa [base, E] using hj) hbj h3j⟩

end Finite
end
end LeanCo.PackingEdgeColoring
