import LeanCo.PackingEdgeColoring.SectionThreeTwoOneOne

/-!
# Completing the Section 3 `(2,1,1)` reduction

This module packages the local repair kernel into an extension theorem and
then into the edge-minimal-counterexample exclusion.  No girth assumption is
used: remote endpoints may coincide whenever the displayed degree and
separation hypotheses permit it.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Subcubicity does not depend on the chosen decision procedure for
adjacency.  This local copy keeps the reduction independent of the leaf
module. -/
theorem isSubcubic_change_decidableRel_twoOneOne
    (d₁ d₂ : DecidableRel G.Adj)
    (h : @IsSubcubic V G _ d₁) : @IsSubcubic V G _ d₂ := by
  intro q
  have hqCard : Nat.card (G.neighborSet q) ≤ 3 := by
    letI : DecidableRel G.Adj := d₁
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
    exact h q
  letI : DecidableRel G.Adj := d₂
  rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  exact hqCard

/-- Deleting the chosen middle edge preserves the two Section 3 eligibility
conditions. -/
theorem sectionThreeEligible_deleteEdge_twoOneOne
    (hEligible : SectionThreeEligible G) (e : G.edgeSet) :
    SectionThreeEligible (G.deleteEdges ({e.1} : Set (Sym2 V))) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : DecidableRel (G.deleteEdges ({e.1} : Set (Sym2 V))).Adj :=
    Classical.decRel (G.deleteEdges ({e.1} : Set (Sym2 V))).Adj
  rw [SectionThreeEligible] at hEligible ⊢
  constructor
  · intro q
    exact ((G.deleteEdges ({e.1} : Set (Sym2 V))).degree_le_of_le
      (G.deleteEdges_le ({e.1} : Set (Sym2 V)))).trans (hEligible.1 q)
  · exact MaximumAverageDegreeLT.mono
      (G.deleteEdges_le ({e.1} : Set (Sym2 V))) hEligible.2

/-- In the common-induced-colour case, validity in the deleted graph forces
the four displayed edges on the two short branches to survive deletion of
the long branch's middle edge. -/
theorem short_branch_edges_mem_deleteMiddleEdge
    {u a x z b c d t : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (huc : G.Adj u c)
    (hbd : G.Adj b d) (hct : G.Adj c t)
    (hab : a ≠ b) (hac : a ≠ c)
    (hux : u ≠ x) (haz : a ≠ z)
    (hsep : InducedSeparated (deleteMiddleEdge G hax)
      (⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩ :
        (deleteMiddleEdge G hax).edgeSet)
      (⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩ :
        (deleteMiddleEdge G hax).edgeSet)) :
    (⟨s(u, b), hub⟩ : G.edgeSet) ∈
        RetainedEdges (deleteMiddleEdge G hax) G ∧
      (⟨s(u, c), huc⟩ : G.edgeSet) ∈
        RetainedEdges (deleteMiddleEdge G hax) G ∧
      (⟨s(b, d), hbd⟩ : G.edgeSet) ∈
        RetainedEdges (deleteMiddleEdge G hax) G ∧
      (⟨s(c, t), hct⟩ : G.edgeSet) ∈
        RetainedEdges (deleteMiddleEdge G hax) G := by
  have huz : u ≠ z :=
    ((inducedSeparated_iff_forall_endpoints (deleteMiddleEdge G hax)).mp hsep
      u (by simp) z (by simp)).1
  have hbx : b ≠ x := by
    intro hEq
    subst b
    have huN : u ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x u).mpr hub.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz haz] at huN
    have hu' : u = a ∨ u = z := by simpa using huN
    exact hu'.elim hua.ne huz
  have hcx : c ≠ x := by
    intro hEq
    subst c
    have huN : u ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x u).mpr huc.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz haz] at huN
    have hu' : u = a ∨ u = z := by simpa using huN
    exact hu'.elim hua.ne huz
  have hBne : (⟨s(u, b), hub⟩ : G.edgeSet) ≠
      (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro heq
    have hs : s(u, b) = s(a, x) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hua.ne h.1
    · exact hux h.1
  have hCne : (⟨s(u, c), huc⟩ : G.edgeSet) ≠
      (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro heq
    have hs : s(u, c) = s(a, x) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hua.ne h.1
    · exact hux h.1
  have hBDne : (⟨s(b, d), hbd⟩ : G.edgeSet) ≠
      (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro heq
    have hs : s(b, d) = s(a, x) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hab h.1.symm
    · exact hbx h.1
  have hCTne : (⟨s(c, t), hct⟩ : G.edgeSet) ≠
      (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro heq
    have hs : s(c, t) = s(a, x) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hac h.1.symm
    · exact hcx h.1
  exact ⟨(mem_retained_deleteMiddleEdge_iff G hax _).mpr hBne,
    (mem_retained_deleteMiddleEdge_iff G hax _).mpr hCne,
    (mem_retained_deleteMiddleEdge_iff G hax _).mpr hBDne,
    (mem_retained_deleteMiddleEdge_iff G hax _).mpr hCTne⟩

/-! ## Complete extension from the middle-edge deletion -/

set_option maxHeartbeats 1800000 in
theorem exists_goodFive_extension_of_twoOneOne
    (hsub : IsSubcubic G)
    {u a x z b c d t : V}
    (hu : IsThreeVertex G u) (hz : IsThreeVertex G z)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hc : IsTwoVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hux : u ≠ x) (haz : a ≠ z)
    (hbd : G.Adj b d) (hdu : d ≠ u)
    (hct : G.Adj c t) (htu : t ≠ u)
    (small : (deleteMiddleEdge G hax).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteMiddleEdge G hax) small) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  classical
  let H := deleteMiddleEdge G hax
  let D : Set G.edgeSet := RetainedEdges H G
  let E : G.edgeSet := ⟨s(a, x), hax⟩
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  let C : G.edgeSet := ⟨s(u, c), huc⟩
  let LH : H.edgeSet :=
    ⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩
  let RH : H.edgeSet :=
    ⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small
  have hLD : L ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax L).mpr
    exact (middleEdge_ne_leftOuter G hua hax hux).symm
  have hRD : R ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax R).mpr
    exact (middleEdge_ne_rightOuter G hax hxz haz).symm
  have hmiddle : base E = none := by
    simp [base, E, transportColoringToSupergraph, H, deleteMiddleEdge]
  have hcondition : ConditionI G base := by
    simpa [base, H] using conditionI_transport_deleteMiddleEdge G hsub ha hx hax
      small hsmall.2
  have hNoL : IsOneTwoColoringOn G (D \ {L}) base := by
    simpa [D, H, L, base] using
      transport_deleteMiddleEdge_valid_without_left G ha hx hua hax hxz hux haz
        small hsmall.1
  have hbaseLH : base L = small LH := by
    dsimp [base]
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small
      (leftOuter_mem_deleteMiddleEdge G hua hax hux)]
  have hbaseRH : base R = small RH := by
    dsimp [base]
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small
      (rightOuter_mem_deleteMiddleEdge G hax hxz haz)]
  by_cases hsame : ∃ alpha : Fin 5, base L = some alpha ∧ base R = some alpha
  · obtain ⟨alpha, hL, hR⟩ := hsame
    have hLsmall : small LH = some alpha := hbaseLH.symm.trans hL
    have hRsmall : small RH = some alpha := hbaseRH.symm.trans hR
    have hLRH : LH ≠ RH := by
      intro hEq
      apply leftOuter_ne_rightOuter G hua hax hxz hux
      apply Subtype.ext
      exact congrArg (fun e : H.edgeSet => (e : Sym2 V)) hEq
    have hsepDeleted : InducedSeparated H LH RH := by
      have hp := hsmall.1 LH (by simp) RH (by simp) hLRH
      simpa [hLsmall, hRsmall, PairCompatible] using hp
    obtain ⟨hBmem, hCmem, hBDmem, hCTmem⟩ :=
      short_branch_edges_mem_deleteMiddleEdge G ha hx hua hax hxz hub huc hbd
        hct hab hac hux haz (by simpa [H, LH, RH] using hsepDeleted)
    by_cases hBnone : base B = none
    · apply exists_goodFive_extension_twoOneOne_same_induced_matching_branch
        G hsub hu hz ha hx hb hc hua hax hxz hux haz hub huc hab hac hbc hbd
        hdu hct htu base (by simpa [D, H, L] using hNoL) hcondition
        (by simpa [E] using hmiddle) alpha (by simpa [L] using hL)
        (by simpa [R] using hR) (by simpa [B] using hBnone)
        (by simpa [B, H] using hBmem) (by simpa [C, H] using hCmem)
        (by simpa [H] using hBDmem) (by simpa [H] using hCTmem)
    · by_cases hCnone : base C = none
      · apply exists_goodFive_extension_twoOneOne_same_induced_matching_branch
          G hsub hu hz ha hx hc hb hua hax hxz hux haz huc hub hac hab hbc.symm
          hct htu hbd hdu base (by simpa [D, H, L] using hNoL) hcondition
          (by simpa [E] using hmiddle) alpha (by simpa [L] using hL)
          (by simpa [R] using hR) (by simpa [C] using hCnone)
          (by simpa [C, H] using hCmem) (by simpa [B, H] using hBmem)
          (by simpa [H] using hCTmem) (by simpa [H] using hBDmem)
      · have hno : ∀ f, f ∈ D → f ≠ L → u ∈ (f : Sym2 V) →
            base f ≠ none := by
          intro f hfD hfL huf hfnone
          rcases edge_eq_one_of_three_of_incident_three G hu hua hub huc hab hac
              hbc f huf with hfL' | hfB' | hfC'
          · exact hfL (Subtype.ext hfL')
          · apply hBnone
            have hfEq : f = B := Subtype.ext hfB'
            simpa [hfEq] using hfnone
          · apply hCnone
            have hfEq : f = C := Subtype.ext hfC'
            simpa [hfEq] using hfnone
        have havailL : ColorAvailableOn G (D \ {L}) base L none := by
          simpa [D, H, L] using
            matching_available_leftOuter_of_no_other_terminal_matching G ha hua
              hax hux base (by simpa [D, H, L] using hno)
        let after := recolor G base L none
        have hdomainL : insert L (D \ {L}) = D := by
          ext f
          by_cases hfL : f = L
          · subst f
            simp [hLD]
          · simp [hfL]
        have hafterValid : IsOneTwoColoringOn G D after := by
          have h := hNoL.extend_one G (by simp) havailL
          rw [hdomainL] at h
          exact h
        have hafterCondition : ConditionI G after := by
          apply ConditionI.of_middle_new_support G hsub hu hz ha hx hua hax hxz
            hux haz hcondition
          · intro f hf
            by_cases hfL : f = L
            · exact Or.inr (Or.inl hfL)
            · exact Or.inl (by simpa [after, hfL] using hf)
          · intro f i hf
            by_cases hfL : f = L
            · subst f
              simp [after] at hf
            · exact Or.inl (by simpa [after, hfL] using hf)
        have hEL : E ≠ L := middleEdge_ne_leftOuter G hua hax hux
        have hafterMiddle : after E = none := by
          simpa [after, hEL] using hmiddle
        have hafterLeft : after L = none := by simp [after]
        have hnotSame : ¬ ∃ i : Fin 5,
            after L = some i ∧ after R = some i := by
          rintro ⟨i, hi, _⟩
          rw [hafterLeft] at hi
          simp at hi
        apply exists_goodFive_extension_middle_of_outer_not_same_induced G hsub
          hu hz ha hx hua hax hxz hux haz after
          (by simpa [D, H] using hafterValid) hafterCondition
          (by simpa [E] using hafterMiddle)
          (by simpa [L, R] using hnotSame)
  · have hvalid : IsOneTwoColoringOn G D base := by
      simpa [D, H, base] using
        transport_deleteMiddleEdge_valid G ha hx hua hax hxz hux haz small
          hsmall.1 (by
            intro i hiL hiR
            exact False.elim (hsame ⟨i, hbaseLH.trans hiL,
              hbaseRH.trans hiR⟩))
    apply exists_goodFive_extension_middle_of_outer_not_same_induced G hsub hu
      hz ha hx hua hax hxz hux haz base (by simpa [D, H] using hvalid)
      hcondition (by simpa [E] using hmiddle)
      (by simpa [L, R] using hsame)

/-! ## Exclusion in an edge-minimal bad graph -/

set_option maxHeartbeats 1200000 in
theorem IsEdgeMinimalBad.no_twoOneOne_sectionThree
    (hmin : IsEdgeMinimalBad SectionThreeEligible HasGoodFive G) :
    ¬ HasTwoOneOneConfiguration G := by
  intro hconfiguration
  obtain ⟨u, hu, a, b, c, hab, hac, hbc, hlong, hshortB, hshortC⟩ :=
    hconfiguration
  obtain ⟨hua, ha, x, z, hax, hxu, hx, hxz, hza, hz⟩ := hlong
  obtain ⟨hub, hb⟩ := hshortB
  obtain ⟨huc, hc⟩ := hshortC
  obtain ⟨d, hdu, hbd⟩ :=
    exists_other_neighbor_of_isTwoVertex G hb hub.symm
  obtain ⟨t, htu, hct⟩ :=
    exists_other_neighbor_of_isTwoVertex G hc huc.symm
  let e : G.edgeSet := ⟨s(a, x), hax⟩
  have hEligibleDelete :
      SectionThreeEligible (G.deleteEdges ({e.1} : Set (Sym2 V))) :=
    sectionThreeEligible_deleteEdge_twoOneOne G hmin.eligible e
  have hgoodDelete : HasGoodFive (G.deleteEdges ({e.1} : Set (Sym2 V))) :=
    hmin.good_deleteEdge e hEligibleDelete
  rw [HasGoodFive] at hgoodDelete
  obtain ⟨small, hsmallClassical⟩ := hgoodDelete
  have hsmall : GoodFive (deleteMiddleEdge G hax) small := by
    apply goodFive_change_decidableRel
      (G := deleteMiddleEdge G hax)
      (Classical.decRel (deleteMiddleEdge G hax).Adj)
      inferInstance small
    simpa [e, deleteMiddleEdge] using hsmallClassical
  have hsub : IsSubcubic G :=
    isSubcubic_change_decidableRel_twoOneOne G
      (Classical.decRel G.Adj) inferInstance hmin.eligible.1
  obtain ⟨colour, hgood⟩ := exists_goodFive_extension_of_twoOneOne G hsub hu hz
    ha hx hb hc hua hax hxz hub huc hab hac hbc hxu.symm hza.symm hbd hdu
    hct htu small hsmall
  apply hmin.not_good
  rw [HasGoodFive]
  refine ⟨colour, ?_⟩
  apply goodFive_change_decidableRel
    (G := G) inferInstance (Classical.decRel G.Adj) colour
  exact hgood

end Finite

end

end LeanCo.PackingEdgeColoring
