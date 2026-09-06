import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoZeroFinal

/-!
# Completion of the `(3,2,0)` local exclusion

This module connects the fully closed local recolouring dispatcher to the
standard smaller-graph colouring obtained by deleting the middle vertex of
the selected 3-thread.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/- A good colouring after deleting the middle vertex of the selected
3-thread rules out a `(3,2,0)` fork in a bad graph. -/
set_option maxHeartbeats 3000000 in
theorem longPair_no_threeTwoZero_of_smaller_good
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t x : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u x}
    (hp : IsKThread G p 3) (hq : IsKThread G q 2) (hr : IsKThread G r 0)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) : False := by
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
  have hrLen : r.length = 1 := by simpa using hr.length
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
  have hrEnd : r.getVert 1 = x := by
    rw [← hrLen]
    exact r.getVert_length
  have hpr' : p.getVert 1 ≠ x := by simpa [hrEnd] using hpr
  have hqr' : q.getVert 1 ≠ x := by simpa [hrEnd] using hqr
  have hu₂ : u ≠ p.getVert 2 := by
    simpa using hpGetNe 0 2 (by omega) (by omega) (by omega)
  let pL : G.Walk u (p.getVert 2) := p.take 2
  have hpL : pL.IsPath := hp.1.take 2
  have hnotU₂ : ¬ G.Adj u (p.getVert 2) := by
    intro hadj
    exact longPair_not_adj_endpoints_of_short_path G hgirth hpL
      (by simp [pL, hpLen]) (by simp [pL, hpLen]) hadj.symm
  have htFar : t ≠ p.getVert 2 ∧ ¬ G.Adj t (p.getVert 2) := by
    exact longPair_short_path_endpoint_far_from_threeThread_middle G hgirth hp
      hq.1 (by simpa [hqLen]) hpq
  have hxFar : x ≠ p.getVert 2 ∧ ¬ G.Adj x (p.getVert 2) := by
    exact longPair_short_path_endpoint_far_from_threeThread_middle G hgirth hp
      hr.1 (by simpa [hrLen]) hpr
  have hnotTU : ¬ G.Adj t u := by
    exact longPair_not_adj_endpoints_of_short_path G hgirth hq.1
      (by simpa [hqLen]) (by simpa [hqLen])
  have htx : t ≠ x := by
    intro hEq
    apply hnotTU
    simpa [hEq] using rr.adj.symm
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
  have hDD : D ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      htFar.1 htFar.2 D (by simp [D, threadLastEdge])
  have hTD : T ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      hxFar.1 hxFar.2 T (by simp [T, threadFirstEdge, hrEnd])
  have hret : ∀ f, IsExternalAt G t D f → f ∈ Dset := by
    intro f hf
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      htFar.1 htFar.2 f hf.1
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hpq
  have hPT : P ≠ T := by
    simpa [P, T, h, rr, threadFirstEdge, hrEnd, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj rr.adj hpr'
  have hQT : Q ≠ T := by
    simpa [Q, T, rr, threadFirstEdge, hrEnd, Sym2.eq_swap] using
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
  have hzQ : z ∉ (Q : Sym2 V) := by
    intro hzmem
    have hzcase : z = u ∨ z = q.getVert 1 := by
      simpa [Q, threadFirstEdge] using hzmem
    rcases hzcase with hzu | hzq
    · exact (IsKThread.endpoints_ne G hp) hzu.symm
    · exact (isThreeVertex_ne_isTwoVertex G h.end_three g.first_two) hzq
  obtain ⟨hP, hR, hpal⟩ :=
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
  have hC := longPair_twoThread_middle_matching_in_bad_graph_twoZero
    G hgirth hp hq hr hpq hpr hqr small hsmall hsub hbad
  have hPval : base P = none := by
    simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP
  have hRval : base R = none := by
    simpa [h, base, R, threadLastEdge] using hR
  have hCval : base C = none := by
    simpa [base, C] using hC
  have hvalid : IsOneTwoColoringOn G Dset base := by
    simpa [Dset] using hprepared.1
  have hQne : base Q ≠ none := by
    intro hQnone
    have hcompat := hvalid P hPD Q hQD hPQ
    have hdisj : EndpointDisjoint G P Q := by
      simpa [hPval, hQnone] using hcompat
    exact hdisj u (by simp [P, threadFirstEdge])
      (by simp [Q, threadFirstEdge])
  have hTne : base T ≠ none := by
    intro hTnone
    have hcompat := hvalid P hPD T hTD hPT
    have hdisj : EndpointDisjoint G P T := by
      simpa [hPval, hTnone] using hcompat
    exact hdisj u (by simp [P, threadFirstEdge])
      (by simp [T, threadFirstEdge])
  obtain ⟨a, b, hab, hau, hbu, ha, hb, hNfar⟩ :=
    rr.exists_far_neighbors G
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let Vedge : G.edgeSet := ⟨s(x, b), hb⟩
  have hUD : U ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      hxFar.1 hxFar.2 U (by simp [U])
  have hVD : Vedge ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      hxFar.1 hxFar.2 Vedge (by simp [Vedge])
  cases hQval : base Q with
  | none => exact False.elim (hQne hQval)
  | some i =>
      cases hTval : base T with
      | none => exact False.elim (hTne hTval)
      | some j =>
          have hij : i ≠ j := by
            intro hij
            subst j
            have hcompat := hvalid Q hQD T hTD hQT
            have hsep : InducedSeparated G Q T := by
              simpa [hQval, hTval] using hcompat
            exact hsep.1 u (by simp [Q, threadFirstEdge])
              (by simp [T, threadFirstEdge])
          apply hbad
          exact longPair_hasGoodFour_of_twoZero_hard G hsub h q hq rr
            hpq hpr' hqr' htx ha hb hab hau hbu hNfar base hprepared i j hij
              (by simpa [h, P, threadFirstEdge, Sym2.eq_swap] using hPval)
              (by simpa [h, R, threadLastEdge] using hRval)
              (by simpa [Q] using hQval)
              (by simpa [rr, T, threadFirstEdge, hrEnd,
                Sym2.eq_swap] using hTval)
              (by simpa [h, A] using hA)
              (by simpa [h, B] using hB)
              (by simpa [C] using hCval)
              (by simpa [h, P, Dset, threadFirstEdge,
                Sym2.eq_swap] using hPD)
              (by simpa [Q, Dset] using hQD)
              (by simpa [C, Dset] using hCD)
              (by simpa [D, Dset] using hDD)
              (by simpa [rr, T, Dset, threadFirstEdge, hrEnd,
                Sym2.eq_swap] using hTD)
              (by simpa [U, Dset] using hUD)
              (by simpa [Vedge, Dset] using hVD)
              (by simpa [h, D, P, threadFirstEdge, threadLastEdge,
                Sym2.eq_swap] using hDP)
              (by simpa [h, R, P, threadFirstEdge, threadLastEdge,
                Sym2.eq_swap] using hRP)
              (by simpa [h, R, Q, threadFirstEdge, threadLastEdge,
                Sym2.eq_swap] using hRQ)
              (by simpa [h, base, P, R, threadFirstEdge, threadLastEdge,
                Sym2.eq_swap] using hpal)
              (by simpa [Q] using hzQ)
              (by
                intro f hf
                exact hret f (by simpa [D] using hf))

end Finite

end

end LeanCo.PackingEdgeColoring
