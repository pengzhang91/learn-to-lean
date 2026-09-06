import LeanCo.PackingEdgeColoring.SectionFourLongTwoThreadClaim
import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeTwo
import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeTwoFinal
import LeanCo.PackingEdgeColoring.SectionFourLongPreparedOuter
import LeanCo.PackingEdgeColoring.SectionFourLongMinimal

/-!
# Closing the two-thread part of Claim 4.5

If the middle edge of a displayed two-thread were induced-coloured, the
ordinary arm swap could have one Condition-3 obstruction.  The critical
normal form identifies that obstruction.  Choosing the fourth induced
colour on the selected outer edge breaks it, while making the first edge
of the two-thread matching.  This module packages that alternate swap and
deduces that the middle edge must be matching in every bad graph.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The alternate selected-outer/two-thread-first swap preserves the full
prepared-gap package.  Its only nonlocal Condition-3 premise is precisely
the conclusion furnished by the critical-normal-form escape lemma. -/
theorem longPair_prepared_selectedFresh_twoThreadFirstMatching
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ s)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ none)
    (hSd : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ some d)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let T : G.edgeSet := threadFirstEdge G q hq
    PreparedThreeThreadGap G h
      (recolor G (recolor G colour P (some d)) T none) := by
  dsimp only
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some d)
  let alt : G.edgeSet → OneTwoColor 4 := recolor G afterP T none
  let r := hq.twoThreadCoreData G
  let r₂ := hq.twoStepArmCore G
  have hPD' : P ∈ Dset := by simpa [P, Dset] using hPD
  have hTD' : T ∈ Dset := by simpa [T, Dset] using hTD
  have havailP : ColorAvailableOn G Dset colour P (some d) := by
    exact longPair_selectedFirst_fresh_available_twoStepThird
      G h g r₂ hvw hvq hwq colour Dset d i j hP hQ
        (by simpa [r₂, threadFirstEdge, Sym2.eq_swap] using hT)
        hC (by simpa [r₂] using hSd) hdi hdj
        (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalidAfterP : IsOneTwoColoringOn G Dset afterP := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := P) (a := some d) hPD').mpr
    refine ⟨?_, havailP⟩
    exact IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.diff_subset
  have havailT : ColorAvailableOn G Dset afterP T none := by
    simpa [afterP, P, T, r₂, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoStepFirst_matching_available_after_selectedFresh
        G h g r₂ hvw hvq hwq colour Dset d i j hQ
        (by simpa [r₂, threadFirstEdge, Sym2.eq_swap] using hT)
        (by simpa [r₂] using hS)
  have hvalidAlt : IsOneTwoColoringOn G Dset alt := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := afterP) (e := T) (a := none) hTD').mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G) hvalidAfterP Set.diff_subset,
      havailT⟩
  have hsatAlt : OneSaturated G alt := by
    simpa [alt, afterP, P, T, r₂, threadFirstEdge, Sym2.eq_swap] using
      longPair_oneSaturated_selectedFresh_twoStepFirstMatching
        G h r₂ hvq colour hprepared.2.1 d j
        (by simpa [r₂, threadFirstEdge, Sym2.eq_swap] using hT) hA
  have htwoAlt : ConditionTwo G alt := by
    simpa [alt, afterP, P, T, r, threadFirstEdge, Sym2.eq_swap] using
      longPair_conditionTwo_selectedFresh_twoThreadFirstMatching
        G hsub h g r hvw hvq hwq colour hprepared.2.2.1 hprepared.2.1 d j
        (by simpa [r, threadFirstEdge, Sym2.eq_swap] using hT)
        (by simpa [r] using hS) hA hB hC
        (by simpa [r, threadLastEdge, Sym2.eq_swap] using hUP)
  have hcriticalAlt : ConditionThreeAtTwoThread G q hq alt := by
    exact longPair_conditionThreeAtTwoThread_alt_of_critical
      G h g q hq hvw hvq hwq colour i j d hP hQ hT hdi hdj
        (by simpa [P, T, alt, afterP] using hcritical)
  have hthreeAlt : ConditionThree G alt := by
    exact (longPair_conditionThree_swap_selectedOuter_twoThreadFirst_iff
      G h q hq colour hprepared.2.2.2 d).2
        (by simpa [P, T, alt, afterP] using hcriticalAlt)
  exact ⟨by simpa [Dset, alt, afterP] using hvalidAlt,
    by simpa [alt, afterP] using hsatAlt,
    by simpa [alt, afterP] using htwoAlt,
    by simpa [alt, afterP] using hthreeAlt⟩

/-- Once the alternate swap is prepared, the matching first edge of the
two-thread is the left matching guard needed to fill the deleted pair. -/
theorem longPair_hasGoodFour_of_twoThread_second_induced_alt
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ s)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ none)
    (hSd : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ some d)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRT : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let alt : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) T none
  have hPD' : P ∈ Dset := by simpa [P, Dset] using hPD
  have hTD' : T ∈ Dset := by simpa [T, Dset] using hTD
  have hAD : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [B, Dset] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD')
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD')
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD')
  have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ hTD')
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hpreparedAlt : PreparedThreeThreadGap G h alt := by
    exact longPair_prepared_selectedFresh_twoThreadFirstMatching
      G hsub h g q hq hvw hvq hwq colour hprepared d i j hP hQ hT hC
        hS hSd hA hB hPD hTD hUP hdi hdj
        (by simpa [P, T] using hcritical)
  have hAltP : alt P ≠ none := by simp [alt, hPT]
  have hAltR : alt R = none := by
    simp [alt, R, P, T, hRP, hRT, hR]
  have hAltA : alt A = none := by
    simp [alt, A, P, T, hAP, hAT, hA]
  have hAltB : alt B = none := by
    simp [alt, B, P, T, hBP, hBT, hB]
  have hAltT : alt T = none := by simp [alt]
  apply longPair_hasGoodFour_of_prepared_left_outer_induced
    G hsub h alt hpreparedAlt
      (by simpa [P] using hAltP) (by simpa [R] using hAltR)
      (by simpa [A] using hAltA) (by simpa [B] using hAltB)
      T hAltT
  · simp [T, threadFirstEdge]
  · exact hAT.symm
  · exact hBT.symm

/-- Claim 4.5 for a genuine two-thread: in a bad graph, after deleting the
middle vertex of the selected three-thread, the middle edge of every
distinct two-thread at the common centre is matching-coloured. -/
theorem longPair_twoThread_second_matching_in_bad_graph
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u y}
    (hp : IsKThread G p 3) (hq : IsKThread G q 3)
    (hr : IsKThread G r 2)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) :
    (transportColoringToSupergraph
        (G.deleteIncidenceSet_le (p.getVert 2)) small)
      (⟨s(r.getVert 1, r.getVert 2),
        (hr.twoStepArmCore G).second_adj⟩ : G.edgeSet) = none := by
  classical
  let h := hp.threeThreadCore G
  let g := hq.threeThreadCore G
  let r₂ := hr.twoStepArmCore G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le (p.getVert 2)) small
  let Dset : Set G.edgeSet :=
    RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
  let P : G.edgeSet := threadFirstEdge G p hp
  let R : G.edgeSet := threadLastEdge G p hp
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := threadFirstEdge G r hr
  let S : G.edgeSet :=
    ⟨s(r.getVert 1, r.getVert 2), r₂.second_adj⟩
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
  have hrLen : r.length = 3 := by simpa using hr.length
  have hpGetNe (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) (hab : a ≠ b) :
      p.getVert a ≠ p.getVert b := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using ha)
      (show b ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using hb)
      heq
    exact hab hinj
  have hrGetNe (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (hab : a ≠ b) :
      r.getVert a ≠ r.getVert b := by
    intro heq
    have hinj := hr.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ r.length} by simpa [hrLen] using ha)
      (show b ∈ {n : ℕ | n ≤ r.length} by simpa [hrLen] using hb)
      heq
    exact hab hinj
  have hpEnd : p.getVert 4 = z := by
    rw [← hpLen]
    exact p.getVert_length
  have hrEnd : r.getVert 3 = y := by
    rw [← hrLen]
    exact r.getVert_length
  let pL : G.Walk u (p.getVert 2) := p.take 2
  have hpL : pL.IsPath := hp.1.take 2
  have hnotU₂ : ¬ G.Adj u (p.getVert 2) := by
    intro hadj
    exact longPair_not_adj_endpoints_of_short_path G hgirth hpL
      (by simp [pL, hpLen]) (by simp [pL, hpLen]) hadj.symm
  have hu₂ : u ≠ p.getVert 2 := by
    simpa using hpGetNe 0 2 (by omega) (by omega) (by omega)
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
  have hQD : Q ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G hu₂ hnotU₂
      Q (by simp [Q, threadFirstEdge])
  have hTD : T ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G hu₂ hnotU₂
      T (by simp [T, threadFirstEdge])
  have hPQ : P ≠ Q := by
    intro heq
    have hval : s(u, p.getVert 1) = s(u, q.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hloop
    · exact hpq hsame.2
    · exact hp.first_step_adj.ne hloop.2.symm
  have hPT : P ≠ T := by
    intro heq
    have hval : s(u, p.getVert 1) = s(u, r.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hloop
    · exact hpr hsame.2
    · exact hp.first_step_adj.ne hloop.2.symm
  have hQT : Q ≠ T := by
    intro heq
    have hval : s(u, q.getVert 1) = s(u, r.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hloop
    · exact hqr hsame.2
    · exact hq.first_step_adj.ne hloop.2.symm
  have hUP : threadLastEdge G r hr ≠ P := by
    intro heq
    have hval : s(r.getVert 2, y) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hswap
    · exact hrGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hsame.1)
    · exact hrGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa [hrEnd] using hswap.2)
  have hRP : R ≠ P := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hcase | hcase
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hcase.1)
    · exact hpGetNe 3 1 (by omega) (by omega) (by omega) hcase.1
  have hRT : R ≠ T := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, r.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hcase | hcase
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hcase.1)
    · exact hpGetNe 4 0 (by omega) (by omega) (by omega)
        (by simpa [hpEnd] using hcase.2)
  obtain ⟨hP, hR, _hpal⟩ :=
    longPair_threeThread_hard_normal_form_of_no_goodFour G hgirth h small
      hsmall hsub hbad
  have hC := longPair_fork_second_matching_in_bad_graph G hgirth hp hq hpq
    small hsmall hsub hbad
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
  by_contra hSne
  have hSnon : base S ≠ none := by simpa [S, r₂, base] using hSne
  obtain ⟨j, hTval, hcritical⟩ :=
    longPair_twoThread_second_induced_critical_normal_form
      G hp hr hpr small hsmall hsub
        (by simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP)
        (by simpa [h, base, R, threadLastEdge] using hR)
        (by simpa [S, r₂, base] using hSnon) hbad
  have hPval : base P = none := by
    simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP
  have hTval' : base T = some j := by simpa [base, T] using hTval
  have hvalid : IsOneTwoColoringOn G Dset base := by
    simpa [Dset] using hprepared.1
  have hQne : base Q ≠ none := by
    intro hQnone
    have hpqCompat := hvalid P hPD Q hQD hPQ
    have hdisj : EndpointDisjoint G P Q := by
      simpa [hPval, hQnone] using hpqCompat
    exact hdisj u (by simp [P, threadFirstEdge])
      (by simp [Q, threadFirstEdge])
  cases hQval : base Q with
  | none => exact False.elim (hQne hQval)
  | some i =>
      have hij : i ≠ j := by
        intro hij
        subst j
        have hcompat := hvalid Q hQD T hTD hQT
        have hsep : InducedSeparated G Q T := by
          simpa [hQval, hTval'] using hcompat
        exact hsep.1 u (by simp [Q, threadFirstEdge])
          (by simp [T, threadFirstEdge])
      have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by
        simp [hij]
      obtain ⟨d, hdPair, hSd⟩ :=
        longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
          hpairCard (base S)
      have hdData : d ≠ i ∧ d ≠ j := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using
          hdPair
      apply hbad
      exact longPair_hasGoodFour_of_twoThread_second_induced_alt
        G hsub h g r hr hpq hpr hqr base hprepared d i j
          (by simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP)
          (by simpa [h, base, R, threadLastEdge] using hR)
          (by simpa [g, base, Q, threadFirstEdge, Sym2.eq_swap] using hQval)
          (by simpa [base, T] using hTval)
          (by simpa [g, base] using hC)
          (by simpa [S, r₂, base] using hSnon)
          (by simpa [S, r₂, base] using hSd)
          (by simpa [h, A, base] using hA)
          (by simpa [h, B, base] using hB)
          (by simpa [h, P, Dset, threadFirstEdge, Sym2.eq_swap] using hPD)
          (by simpa [T, Dset] using hTD)
          (by simpa [h, P, threadFirstEdge, Sym2.eq_swap] using hUP)
          (by simpa [h, P, R, threadFirstEdge, threadLastEdge,
            Sym2.eq_swap] using hRP)
          (by simpa [h, R, T, threadFirstEdge, threadLastEdge,
            Sym2.eq_swap] using hRT)
          hdData.1 hdData.2
          (by simpa [base, P, T, threadFirstEdge, Sym2.eq_swap] using hcritical)

/-- The final local no332 reduction, with no exposed colour hypothesis. -/
theorem longPair_no_threeThreeTwo_of_smaller_good
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u y}
    (hp : IsKThread G p 3) (hq : IsKThread G q 3) (hr : IsKThread G r 2)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) : False := by
  have hS := longPair_twoThread_second_matching_in_bad_graph
    G hgirth hp hq hr hpq hpr hqr small hsmall hsub hbad
  exact longPair_no_threeThreeTwo_of_smaller_good_of_second_matching
    G hgirth hp hq hr hpq hpr hqr small hsmall hsub hbad hS

end Finite

section ClassicalMinimal

variable [Fintype V] [DecidableEq V]

/- Minimal-counterexample form of the no332 reduction. -/
set_option maxHeartbeats 2400000 in
theorem IsEdgeMinimalBad.no_threeThreeTwo_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t}
    {r : G.Walk u y}
    (hp : @IsKThread V G _ (Classical.decRel G.Adj) u z p 3)
    (hq : @IsKThread V G _ (Classical.decRel G.Adj) u t q 3)
    (hr : @IsKThread V G _ (Classical.decRel G.Adj) u y r 2)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1) : False := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨small, hsmall⟩ :=
    hmin.exists_good_deleteThreeThreadMiddle (G := G) hp
  have hEligibleG :
      @IsSubcubic V G _ (Classical.decRel G.Adj) ∧
        IsCombinatoriallyPlanar G ∧ (16 : ℕ∞) ≤ G.egirth := by
    simpa [SectionFourEligible] using hmin.eligible
  exact longPair_no_threeThreeTwo_of_smaller_good G hEligibleG.2.2
    hp hq hr hpq hpr hqr small hsmall hEligibleG.1 hmin.not_good

end ClassicalMinimal

end

end LeanCo.PackingEdgeColoring
