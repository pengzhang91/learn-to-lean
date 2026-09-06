import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeOne
import LeanCo.PackingEdgeColoring.SectionFourLongTwoThreadClaim
import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeTwo
import LeanCo.PackingEdgeColoring.SectionFourLongMinimal
import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoTwo

/-!
# The `(3,2,1)` reduction for Section 4

The long recolouring argument for `no331` only needs the first two
degree-two vertices of its auxiliary arm.  This file instantiates that
generic core with a genuine 2-thread and isolates the remaining Claim-1
obligation: its middle edge is matching-coloured.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Once Claim 1 supplies a matching middle edge on the 2-thread, the
already verified one-thread hard-case machinery closes `(3,2,1)`. -/
theorem longPair_no_threeTwoOne_of_smaller_good_of_second_matching
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u y}
    (hp : IsKThread G p 3) (hq : IsKThread G q 2) (hr : IsKThread G r 1)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G)
    (hC : (transportColoringToSupergraph
        (G.deleteIncidenceSet_le (p.getVert 2)) small)
      (⟨s(q.getVert 1, q.getVert 2),
        (hq.forkTwoStepCore G).left_adj⟩ : G.edgeSet) = none) : False := by
  classical
  let h := hp.threeThreadCore G
  let g := hq.forkTwoStepCore G
  let rCore := hr.oneThreadCore G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le (p.getVert 2)) small
  let P : G.edgeSet := threadFirstEdge G p hp
  let R : G.edgeSet := threadLastEdge G p hp
  let Q : G.edgeSet := threadFirstEdge G q hq
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
  have hpGetNe (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) (hab : a ≠ b) :
      p.getVert a ≠ p.getVert b := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using ha)
      (show b ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using hb)
      heq
    exact hab hinj
  have hpEnd : p.getVert 4 = z := by
    rw [← hpLen]
    exact p.getVert_length
  let pL : G.Walk u (p.getVert 2) := p.take 2
  have hpL : pL.IsPath := hp.1.take 2
  have hnotU₂ : ¬ G.Adj u (p.getVert 2) := by
    intro hadj
    exact longPair_not_adj_endpoints_of_short_path G hgirth hpL
      (by simp [pL, hpLen]) (by simp [pL, hpLen]) hadj.symm
  have hu₂ : u ≠ p.getVert 2 := by
    simpa using hpGetNe 0 2 (by omega) (by omega) (by omega)
  have hQD : Q ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G hu₂ hnotU₂
      Q (by simp [Q, threadFirstEdge])
  have hTD : T ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G hu₂ hnotU₂
      T (by simp [T, threadFirstEdge])
  obtain ⟨hP, hR, hpal⟩ :=
    longPair_threeThread_hard_normal_form_of_no_goodFour G hgirth h small
      hsmall hsub hbad
  have hprepared : PreparedThreeThreadGap G h base := by
    exact preparedThreeThreadGap_of_goodFour G hsub h small hsmall
  have hAD : A ∉ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G := by
    simpa [h, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G := by
    simpa [h, B, Sym2.eq_swap] using right_chain_edge_not_retained G h.right_adj
  have hA : base A = none := by
    have hAe : A.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [RetainedEdges] using hAD
    simp [base, transportColoringToSupergraph, hAe]
  have hB : base B = none := by
    have hBe : B.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [RetainedEdges] using hBD
    simp [base, transportColoringToSupergraph, hBe]
  have hzT : z ∉ (T : Sym2 V) := by
    intro hz
    have hzcase : z = u ∨ z = r.getVert 1 := by
      simpa [T, threadFirstEdge] using hz
    rcases hzcase with hzu | hzr
    · apply hpGetNe 4 0 (by omega) (by omega) (by omega)
      simpa [hpEnd] using hzu
    · have hzThree : IsThreeVertex G z := hp.end_three
      have hrTwo : IsTwoVertex G (r.getVert 1) :=
        IsKThread.internal_two G hr (by omega) (by
          have hlen : r.length = 2 := by simpa using hr.length
          omega)
      exact (isThreeVertex_ne_isTwoVertex G hzThree hrTwo) hzr
  apply hbad
  exact longPair_hasGoodFour_of_oneThreadThird_hard G hsub h g rCore
    hpq hpr hqr base hprepared
    (by simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP)
    (by simpa [h, base, R, threadLastEdge] using hR)
    (by simpa [h, A] using hA) (by simpa [h, B] using hB)
    (by simpa [g, base] using hC)
    (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQD)
    (by simpa [rCore, T, threadFirstEdge, Sym2.eq_swap] using hTD)
    (by simpa [h, base, P, R, threadFirstEdge, threadLastEdge,
      Sym2.eq_swap] using hpal)
    (by simpa [rCore, T, threadFirstEdge, Sym2.eq_swap] using hzT)

/-! ## The Claim-1 escape with a one-thread third arm -/

/-- A colour absent from the two other first edges, the 2-thread middle
edge, and the 1-thread continuation is available on the selected outer
edge.  This is the validity core of the alternate Claim-1 swap for
`(3,2,1)`. -/
theorem longPair_selectedFirst_fresh_available_twoOne
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hCd : colour (⟨s(w₁, w₂), g.last_adj⟩ : G.edgeSet) ≠ some d)
    (hSd : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) ≠ some d)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hretained : ∀ f : G.edgeSet, f ∈ Dset → v₂ ∉ (f : Sym2 V)) :
    ColorAvailableOn G Dset colour
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.last_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hQ' : colour Q = some i := by simpa [Q] using hQ
  have hT' : colour T = some j := by simpa [T] using hT
  have hCd' : colour C ≠ some d := by simpa [C] using hCd
  have hSd' : colour S ≠ some d := by simpa [S] using hSd
  have noAtU (f : G.edgeSet) (hfP : f ≠ P)
      (huf : u ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hf := f.2
      rw [hfa] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · exact hfP (Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa))
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hdEq : i = d := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ] using hcf))
      exact hdi hdEq.symm
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      have hdEq : j = d := Option.some.inj
        (hT'.symm.trans (by simpa [hfT] using hcf))
      exact hdj hdEq.symm
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
        g.last_adj g.first_adj.symm g.end_ne_start f hwf with hfC | hfQ
    · exact hCd' (by
        have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
        simpa [hfC'] using hcf)
    · have hfQ' : f = Q := Subtype.ext (by simpa [Q] using hfQ)
      have hdEq : i = d := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ'] using hcf))
      exact hdi hdEq.symm
  have noAtX₁ (f : G.edgeSet)
      (hxf : x₁ ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT
    · exact hSd' (by
        have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
        simpa [hfS'] using hcf)
    · have hfT' : f = T := Subtype.ext (by simpa [T] using hfT)
      have hdEq : j = d := Option.some.inj
        (hT'.symm.trans (by simpa [hfT'] using hcf))
      exact hdj hdEq.symm
  apply (colorAvailableOn_some_iff G Dset colour P d).mpr
  intro f hfD hfP hcf
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = v₁ ∨ a = u := by simpa [P] using ha
  rcases hacase with hav | hau
  · constructor
    · intro hvb
      have hvb' : v₁ = b := hav.symm.trans hvb
      exact noAtV₁ f hfD hfP (by rw [hvb']; exact hbf)
    · intro hvb
      have hvb' : G.Adj v₁ b := by simpa [hav] using hvb
      have hbN : b ∈ G.neighborFinset v₁ :=
        (G.mem_neighborFinset v₁ b).mpr hvb'
      rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start] at hbN
      have hbcase : b = v₂ ∨ b = u := by simpa using hbN
      rcases hbcase with hbv₂ | hbu
      · exact hretained f hfD (by simpa [hbv₂] using hbf)
      · exact noAtU f hfP (by simpa [hbu] using hbf) hcf
  · constructor
    · intro hub
      have hub' : u = b := hau.symm.trans hub
      exact noAtU f hfP (by rw [hub']; exact hbf) hcf
    · intro hub
      have hub' : G.Adj u b := by simpa [hau] using hub
      rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
          g.first_adj r.first_adj hvw hvx hwx hub' with rfl | rfl | rfl
      · exact noAtV₁ f hfD hfP hbf
      · exact noAtW₁ f hbf hcf
      · exact noAtX₁ f hbf hcf

/-- After a fresh induced colour is put on the selected outer edge, the
first edge of the displayed 2-thread can be changed to matching. -/
theorem longPair_twoThreadFirst_matching_available_after_selectedFresh_twoOne
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (d i j : Fin 4)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G Dset
      (recolor G colour
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
      (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some d)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  have hPS : P ≠ S := by
    exact (longPair_twoTwoEdge_ne_edgeEndingAtThree G r.first_two r.second_two
      h.start_three r.middle_adj h.first_adj.symm).symm
  have hafterP : afterP P = some d := by simp [afterP]
  have hafterQ : afterP Q = some i := by
    rw [show afterP Q = colour Q by
      exact recolor_ne G colour (some d) hPQ.symm]
    simpa [Q] using hQ
  have hafterS : afterP S ≠ none := by
    rw [show afterP S = colour S by
      exact recolor_ne G colour (some d) hPS.symm]
    simpa [S] using hS
  have noAtU (f : G.edgeSet) (hfT : f ≠ T)
      (huf : u ∈ (f : Sym2 V)) (hcf : afterP f = none) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hf := f.2
      rw [hfa] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      have hfalse : some d = none :=
        hafterP.symm.trans (by simpa [hfP] using hcf)
      simp at hfalse
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hfalse : some i = none :=
        hafterQ.symm.trans (by simpa [hfQ] using hcf)
      simp at hfalse
    · exact hfT (Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa))
  have noAtX₁ (f : G.edgeSet) (hfT : f ≠ T)
      (hxf : x₁ ∈ (f : Sym2 V)) (hcf : afterP f = none) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT'
    · have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
      exact hafterS (by simpa [hfS'] using hcf)
    · exact hfT (Subtype.ext (by simpa [T] using hfT'))
  apply (colorAvailableOn_none_iff G Dset afterP T).mpr
  intro f _hfD hfT hcf a ha haf
  have hacase : a = x₁ ∨ a = u := by simpa [T] using ha
  exact hacase.elim
    (fun hax ↦ noAtX₁ f hfT (by simpa [hax] using haf) hcf)
    (fun hau ↦ noAtU f hfT (by simpa [hau] using haf) hcf)

/-- External centre data after the 2-thread first edge has become matching;
the remaining third arm is a 1-thread. -/
theorem longPair_twoThreadFirst_external_data_twoOne
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4) (d i : Fin 4)
    (hT : colour (threadFirstEdge G q hq) = none)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = some d)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i) :
    ExternalEdgesInduced G colour u (threadFirstEdge G q hq) ∧
      ExternalInducedColors G colour u (threadFirstEdge G q hq) = {d, i} := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G g.first_adj
        hq.first_step_adj hwq
  have classify (f : G.edgeSet) (huf : u ∈ (f : Sym2 V)) :
      f = P ∨ f = Q ∨ f = T := by
    obtain ⟨x, hfx⟩ := Sym2.mem_iff_exists.mp huf
    have hux : G.Adj u x := by
      have hf := f.2
      rw [hfx] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj hq.first_step_adj hvw hvq hwq hux with rfl | rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa [P, Sym2.eq_swap] using hfx))
    · exact Or.inr (Or.inl
        (Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfx)))
    · exact Or.inr (Or.inr
        (Subtype.ext (by simpa [T, threadFirstEdge] using hfx)))
  constructor
  · intro f hfext
    rcases classify f hfext.1 with rfl | rfl | rfl
    · exact ⟨d, by simpa [P] using hP⟩
    · exact ⟨i, by simpa [Q] using hQ⟩
    · exact False.elim (hfext.2 rfl)
  · ext a
    constructor
    · rintro ⟨f, hfext, hfa⟩
      rcases classify f hfext.1 with rfl | rfl | rfl
      · have hfaP : colour P = some a := by simpa [P] using hfa
        have had : a = d := Option.some.inj
          (hfaP.symm.trans (by simpa [P] using hP))
        simp [had]
      · have hfaQ : colour Q = some a := by simpa [Q] using hfa
        have hai : a = i := Option.some.inj
          (hfaQ.symm.trans (by simpa [Q] using hQ))
        simp [hai]
      · exact False.elim (hfext.2 rfl)
    · intro ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact ⟨P, ⟨by simp [P], hPT⟩, by simpa [P] using hP⟩
      · exact ⟨Q, ⟨by simp [Q], hQT⟩, by simpa [Q] using hQ⟩

/-- Replacing the old target-arm colour on the selected outer edge by a
colour outside the two centre colours breaks the unique two-thread
Condition-3 obstruction. -/
theorem longPair_conditionThreeAtTwoThread_alt_of_critical_twoOne
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (base : G.edgeSet → OneTwoColor 4) (i j d : Fin 4)
    (hP : base (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : base (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : base (threadFirstEdge G q hq) = some j)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G base P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let T : G.edgeSet := threadFirstEdge G q hq
    let alt := recolor G (recolor G base P (some d)) T none
    ConditionThreeAtTwoThread G q hq alt := by
  dsimp only
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let U : G.edgeSet := threadLastEdge G q hq
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G base P (some j)) T none
  let alt : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G base P (some d)) T none
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne
      G h.first_adj g.first_adj hvw
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G g.first_adj
        hq.first_step_adj hwq
  have hcriticalP : critical P = some j := by simp [critical, hPT]
  have hcriticalQ : critical Q = some i := by
    simp [critical, hPQ.symm, hQT, Q, hQ]
  have hcriticalT : critical T = none := by simp [critical]
  have haltP : alt P = some d := by simp [alt, hPT]
  have haltQ : alt Q = some i := by simp [alt, hPQ.symm, hQT, Q, hQ]
  have haltT : alt T = none := by simp [alt]
  have hcriticalStart := longPair_twoThreadFirst_external_data_twoOne
    G h g q hq hvw hvq hwq critical j i hcriticalT hcriticalP hcriticalQ
  have haltStart := longPair_twoThreadFirst_external_data_twoOne
    G h g q hq hvw hvq hwq alt d i haltT haltP haltQ
  have htP : t ∉ (P : Sym2 V) := by
    intro hmem
    have hcase : t = v₁ ∨ t = u := by simpa [P] using hmem
    rcases hcase with htv₁ | htu
    · exact (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two) htv₁
    · exact (IsKThread.endpoints_ne G hq) htu.symm
  have hagree : ColoringsAgreeOff G ({P} : Set G.edgeSet) critical alt := by
    intro e he
    have heP : e ≠ P := by simpa using he
    by_cases heT : e = T
    · subst e
      simp [critical, alt]
    · simp [critical, alt, heP, heT]
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
    exact hcriticalStart.2
  change ConditionThreeAtTwoThread G q hq alt
  intro _hleft _hright
  rw [haltStart.2, hfarAlt]
  intro heq
  have hdmem : d ∈ ({j, i} : Set (Fin 4)) := by
    rw [← heq]
    simp
  simpa [hdj, hdi] using hdmem

/-- Condition 2 for the alternate selected/2-thread-first swap.  All
affected degree-two vertices are discharged by two visible matching edges,
except the sole vertex on the 1-thread; for it we expose exactly one missing
induced colour as a premise. -/
theorem longPair_conditionTwo_selectedFresh_twoThreadFirstMatching_twoOne
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (hsat : OneSaturated G colour)
    (d j k : Fin 4)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hUP : (⟨s(x₂, y), r.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hmissW : ¬ VertexSeesInduced G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) w₁ k) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let U : G.edgeSet := ⟨s(x₂, y), r.last_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) T none
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
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
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hTne : colour T ≠ none := by simpa [T, hT]
  have hU : colour U = none := by
    exact longPair_twoThread_last_matching_of_first_two_induced G r colour hsat
      hTne (by simpa using hS)
  have hnewT : new T = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBT, B, hB]
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
      r.middle_adj.symm r.first_two T U hUT.symm hnewT hnewU
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
      exact hmissW (hall k)
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub r.first_two
        r.middle_adj r.second_two T U hUT.symm hnewT hnewU
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [T]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [U]) (Or.inr r.middle_adj)
      · exact hall

/-- Condition 2 when the matching role is moved to the 1-thread first
edge and the first two edges of the auxiliary 2-thread stay induced.  At
the auxiliary first vertex both incident edges are induced, so the
Condition-2 antecedent is false there. -/
theorem longPair_conditionTwo_selectedFresh_oneThreadFirstMatching_twoOne
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (hold : ConditionTwo G colour)
    (k j : Fin 4) (hkj : k ≠ j)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hGfirst : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ≠ none)
    (hGmiddle : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some k))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some k)) T none
  have hPD' : P ∈ D := by simpa [D, P] using hPD
  have hTD' : T ∈ D := by simpa [D, T] using hTD
  have hAP : A ≠ P := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      h.start_three h.left_adj h.first_adj.symm
  have hAT : A ≠ T := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      h.start_three h.left_adj r.first_adj.symm
  have hBP : B ≠ P := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      h.start_three h.right_adj.symm h.first_adj.symm
  have hBT : B ≠ T := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      h.start_three h.right_adj.symm r.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hQP : Q ≠ P := by
    simpa [Q, P] using
      (longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw).symm
  have hQT : Q ≠ T := by
    simpa [Q, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G g.first_adj r.first_adj hwx
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj h.first_adj.symm
  have hCT : C ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj r.first_adj.symm
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBT, B, hB]
  have hnewT : new T = none := by simp [new]
  have hnewQ : new Q ≠ none := by simpa [new, hQP, hQT, Q] using hGfirst
  have hnewC : new C ≠ none := by simpa [new, hCP, hCT, C] using hGmiddle
  have hagree : ColoringsAgreeOff G ({P, T} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ T := by simpa using he
    simp [new, hne.1, hne.2]
  have hNu : G.neighborFinset u = {v₁, w₁, x₁} :=
    longPair_neighborFinset_eq_three G h.start_three h.first_adj
      g.first_adj r.first_adj hvw hvx hwx
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases longPair_twoVertex_paletteAffectedBy_selected_oneThread_cases G h r
      hq (by simpa [P, T] using haffect) with hqv₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  · have hqmem : q ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u q).mpr hqu.symm
    rw [hNu] at hqmem
    have hqcase : q = v₁ ∨ q = w₁ ∨ q = x₁ := by simpa using hqmem
    rcases hqcase with hqv₁ | hqw₁ | hqx₁
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub h.first_two
        h.left_adj h.middle_two A B hAB hnewA hnewB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [B]) (Or.inr h.left_adj)
      · exact hall
    · subst q
      obtain ⟨e, he, hwe⟩ := (vertexSeesMatching_iff G new w₁).mp hmatch
      rcases edge_eq_left_or_right_of_incident_two G g.first_two
          g.left_adj g.first_adj.symm g.middle_ne_start e hwe with heC | heQ
      · exact hnewC (by
          have heq : e = C := Subtype.ext (by simpa [C] using heC)
          simpa [heq] using he)
      · exact hnewQ (by
          have heq : e = Q := Subtype.ext (by simpa [Q] using heQ)
          simpa [heq] using he)
    · subst q
      exact (not_vertexSeesInduced_oneThread_oldFirstColor_after_move G h r
        colour (by simpa [D] using hvalid) k j hkj hT hA hB hPD hTD hvx)
        (hall j)

/-- Prepared-gap preservation for the useful Claim-1 subcase in which
both the 2-thread middle edge and the 1-thread continuation are induced.
Matching is moved from the selected outer edge to the 1-thread first edge. -/
theorem longPair_prepared_selectedFresh_oneThreadFirstMatching_twoOne
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ y x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ y)
    (r : OneThreadCore G u x₁ x₂)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j : Fin 4) (hdi : d ≠ i) (hdj : d ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hGfirst : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hGmiddle : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ none)
    (hGd : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ some d)
    (hC : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) ≠ none)
    (hCd : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) ≠ some d)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    PreparedThreeThreadGap G h
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some d)
  let new : G.edgeSet → OneTwoColor 4 := recolor G afterP T none
  let g₂ : ForkTwoStepCore G u w₁ w₂ :=
    ⟨g.first_two, g.second_two, g.first_adj, g.middle_adj, g.second_ne_start⟩
  have havailP : ColorAvailableOn G D colour P (some d) := by
    exact longPair_selectedFirst_fresh_available_twoOne G h r g
      hvx hvw hwx.symm colour D d j i hP hT hGfirst hCd hGd hdj hdi
      (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalidP : IsOneTwoColoringOn G D afterP := by
    apply (isOneTwoColoringOn_recolor_iff G (D := D) (colour := colour)
      (e := P) (a := some d) (by simpa [D, P] using hPD)).mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G)
      (by simpa [D] using hprepared.1) Set.diff_subset, havailP⟩
  have havailT : ColorAvailableOn G D afterP T none := by
    exact longPair_oneThreadFirst_matching_available_after_selectedFresh G h r
      colour D (by simpa [D] using hprepared.1) d hP hC hPD hvx
  have hvalidNew : IsOneTwoColoringOn G D new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := D) (colour := afterP)
      (e := T) (a := none) (by simpa [D, T] using hTD)).mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G) hvalidP Set.diff_subset, havailT⟩
  refine ⟨by simpa [D, new, afterP, P, T] using hvalidNew, ?_, ?_, ?_⟩
  · exact longPair_oneSaturated_selectedFresh_oneThreadFirstMatching G h r
      colour hprepared.2.1 d (by simpa [hT]) hA hvx
  · exact longPair_conditionTwo_selectedFresh_oneThreadFirstMatching_twoOne
      G hsub h g₂ r hvw hvx hwx colour hprepared.1 hprepared.2.2.1
        d j hdj hT (by simpa [g₂, hGfirst])
        (by simpa [g₂] using hGmiddle) hA hB hPD hTD
  · exact longPair_conditionThree_selectedFresh_oneThreadFirstMatching
      G h r colour hprepared.2.2.2 d hvx

/-- If both nonselected continuations are induced and a colour is absent
from the two centre colours and both continuations, the preceding move
extends the retained colouring to all of `G`. -/
theorem longPair_hasGoodFour_of_twoThreadMiddle_and_oneContinuation_induced
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ y x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ y)
    (r : OneThreadCore G u x₁ x₂)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j : Fin 4) (hdi : d ≠ i) (hdj : d ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hGfirst : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hGmiddle : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ none)
    (hGd : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ some d)
    (hC : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) ≠ none)
    (hCd : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) ≠ some d)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRT : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet)) :
    HasGoodFour G := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) T none
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  have hpreparedNew : PreparedThreeThreadGap G h new := by
    exact longPair_prepared_selectedFresh_oneThreadFirstMatching_twoOne
      G hsub h g r hvw hvx hwx colour hprepared d i j hdi hdj hP
        hGfirst hT hGmiddle hGd hC hCd hA hB hPD hTD
  have hAD : A ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [B] using right_chain_edge_not_retained G h.right_adj
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD)
  have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ hTD)
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD)
  have hRP' : R ≠ P := by simpa [R, P] using hRP
  have hRT' : R ≠ T := by simpa [R, T] using hRT
  have hnewP : new P ≠ none := by simp [new, hPT]
  have hnewR : new R = none := by simp [new, hRP', hRT', R, hR]
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBT, B, hB]
  have hnewT : new T = none := by simp [new]
  exact longPair_hasGoodFour_of_prepared_left_outer_induced G hsub h new
    hpreparedNew (by simpa [P] using hnewP) (by simpa [R] using hnewR)
      (by simpa [A] using hnewA) (by simpa [B] using hnewB)
      T hnewT (by simp [T]) hAT.symm hBT.symm

/-- The equal-colour induced/induced subcase of Claim 1.  Outside the two
distinct centre colours and the common continuation colour, `Fin 4`
contains a fresh colour for the selected outer edge. -/
theorem longPair_hasGoodFour_of_twoThreadMiddle_oneContinuation_same
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ y x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ y)
    (r : OneThreadCore G u x₁ x₂)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j c : Fin 4) (hij : i ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hGfirst : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hGmiddle : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = some c)
    (hC : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRT : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet)) :
    HasGoodFour G := by
  have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by simp [hij]
  obtain ⟨d, hdPair, hcd⟩ :=
    longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
      hpairCard (some c)
  have hdData : d ≠ i ∧ d ≠ j := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hdPair
  exact longPair_hasGoodFour_of_twoThreadMiddle_and_oneContinuation_induced
    G hsub h g r hvw hvx hwx colour hprepared d i j hdData.1 hdData.2
      hP hR hGfirst hT (by simpa [hGmiddle])
      (by simpa [hGmiddle] using hcd) (by simpa [hC])
      (by simpa [hC] using hcd) hA hB hPD hTD hRP hRT

/-! ## The distinct induced-continuation subcase -/

/-- Availability of the other continuation colour on the 2-thread middle
edge.  The proof only needs the first adjacency of the third arm, so here
that arm may be a 1-thread. -/
theorem longPair_twoThreadMiddle_otherColour_available_twoOne
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (i j c e : Fin 4) (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) = some c)
    (hU : colour (⟨s(x₂, y), r.last_adj⟩ : G.edgeSet) = none)
    (hfar : ExternalInducedColors G colour y
      (⟨s(x₂, y), r.last_adj⟩ : G.edgeSet) = {i, j}) :
    ColorAvailableOn G Dset colour
      (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) (some e) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  let U : G.edgeSet := ⟨s(x₂, y), r.last_adj⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hQ' : colour Q = some i := by simpa [Q] using hQ
  have hT' : colour T = some j := by simpa [T] using hT
  have hS' : colour S = some c := by simpa [S] using hS
  have hU' : colour U = none := by simpa [U] using hU
  have noAtU (f : G.edgeSet) (huf : u ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hf := f.2
      rw [hfa] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      have hfalse : none = some e := hP'.symm.trans (by simpa [hfP] using hcf)
      simp at hfalse
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hie : i = e := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ] using hcf))
      exact hei hie.symm
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      have hje : j = e := Option.some.inj
        (hT'.symm.trans (by simpa [hfT] using hcf))
      exact hej hje.symm
  have noAtX₁ (f : G.edgeSet) (hxf : x₁ ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT
    · have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
      have hce : c = e := Option.some.inj
        (hS'.symm.trans (by simpa [hfS'] using hcf))
      exact hec hce.symm
    · have hfT' : f = T := Subtype.ext (by simpa [T] using hfT)
      have hje : j = e := Option.some.inj
        (hT'.symm.trans (by simpa [hfT'] using hcf))
      exact hej hje.symm
  have noAtX₂ (f : G.edgeSet) (hxf : x₂ ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.second_two
        r.middle_adj.symm r.last_adj r.first_ne_end f hxf with hfS | hfU
    · have hfS' : f = S :=
        Subtype.ext (by simpa [S, Sym2.eq_swap] using hfS)
      have hce : c = e := Option.some.inj
        (hS'.symm.trans (by simpa [hfS'] using hcf))
      exact hec hce.symm
    · have hfU' : f = U := Subtype.ext (by simpa [U] using hfU)
      have hfalse : none = some e := hU'.symm.trans (by simpa [hfU'] using hcf)
      simp at hfalse
  have noAtY (f : G.edgeSet) (hyf : y ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    by_cases hfU : f = U
    · subst f
      have hfalse : none = some e := hU'.symm.trans hcf
      simp at hfalse
    · have hemem : e ∈ ExternalInducedColors G colour y U :=
        ⟨f, ⟨hyf, hfU⟩, hcf⟩
      rw [hfar] at hemem
      simpa [hei, hej] using hemem
  apply (colorAvailableOn_some_iff G Dset colour S e).mpr
  intro f _hfD hfS hcf
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = x₁ ∨ a = x₂ := by simpa [S] using ha
  rcases hacase with hax₁ | hax₂
  · constructor
    · intro hab
      have hxb : x₁ = b := hax₁.symm.trans hab
      exact noAtX₁ f (by rw [hxb]; exact hbf) hcf
    · intro hab
      have hxb : G.Adj x₁ b := by simpa [hax₁] using hab
      have hbN : b ∈ G.neighborFinset x₁ :=
        (G.mem_neighborFinset x₁ b).mpr hxb
      rw [neighborFinset_eq_pair_of_isTwoVertex G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start] at hbN
      have hbcase : b = x₂ ∨ b = u := by simpa using hbN
      exact hbcase.elim
        (fun hbx ↦ noAtX₂ f (by simpa [hbx] using hbf) hcf)
        (fun hbu ↦ noAtU f (by simpa [hbu] using hbf) hcf)
  · constructor
    · intro hab
      have hxb : x₂ = b := hax₂.symm.trans hab
      exact noAtX₂ f (by rw [hxb]; exact hbf) hcf
    · intro hab
      have hxb : G.Adj x₂ b := by simpa [hax₂] using hab
      have hbN : b ∈ G.neighborFinset x₂ :=
        (G.mem_neighborFinset x₂ b).mpr hxb
      rw [neighborFinset_eq_pair_of_isTwoVertex G r.second_two
        r.middle_adj.symm r.last_adj r.first_ne_end] at hbN
      have hbcase : b = x₁ ∨ b = y := by simpa using hbN
      exact hbcase.elim
        (fun hbx ↦ noAtX₁ f (by simpa [hbx] using hbf) hcf)
        (fun hby ↦ noAtY f (by simpa [hby] using hbf) hcf)

/-- Recolouring the 2-thread middle edge with the colour of the 1-thread
continuation preserves every prepared-gap invariant.  The critical normal
form determines the far palette needed for validity. -/
theorem longPair_prepared_recolor_twoThreadMiddle_twoOne
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j c e : Fin 4) (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hSD : (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    let S : G.edgeSet :=
      ⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩
    PreparedThreeThreadGap G h (recolor G colour S (some e)) := by
  dsimp only
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let S : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2),
      q.adj_getVert_succ (i := 1) (by
        have hlen : q.length = 3 := by simpa using hq.length
        omega)⟩
  let U : G.edgeSet := threadLastEdge G q hq
  let r := hq.twoThreadCoreData G
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some j)) T none
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour S (some e)
  have hSD' : S ∈ Dset := by simpa [S, Dset] using hSD
  have hTcore : colour (⟨s(q.getVert 1, u), r.first_adj.symm⟩ : G.edgeSet) =
      some j := by simpa [r, T, threadFirstEdge, Sym2.eq_swap] using hT
  have hScore : colour (⟨s(q.getVert 1, q.getVert 2), r.middle_adj⟩ :
      G.edgeSet) = some c := by simpa [r, S] using hS
  have hU : colour U = none := by
    exact longPair_twoThread_last_matching_of_first_two_induced G r colour
      hprepared.2.1
        (by
          have : colour T ≠ none := by rw [hT]; simp
          simpa [T, r, threadFirstEdge, Sym2.eq_swap] using this)
        (by
          have : colour S ≠ none := by rw [hS]; simp
          simpa [S, r] using this)
  have hcriticalP : critical P = some j := by
    have hPT : P ≠ T := by
      simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
        longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
          hq.first_step_adj hvq
    simp [critical, hPT]
  have hcriticalQ : critical Q = some i := by
    have hPQ : P ≠ Q := by
      simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne
        G h.first_adj g.first_adj hvw
    have hQT : Q ≠ T := by
      simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
        longPair_firstEdges_ne_of_firstVertices_ne G g.first_adj
          hq.first_step_adj hwq
    simp [critical, hPQ.symm, hQT, Q, hQ]
  have hcriticalT : critical T = none := by simp [critical]
  have hcriticalStart := longPair_twoThreadFirst_external_data_twoOne
    G h g q hq hvw hvq hwq critical j i hcriticalT hcriticalP hcriticalQ
  have htP : t ∉ (P : Sym2 V) := by
    intro hmem
    have hcase : t = v₁ ∨ t = u := by simpa [P] using hmem
    rcases hcase with htv₁ | htu
    · exact (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two) htv₁
    · exact (IsKThread.endpoints_ne G hq) htu.symm
  have htT : t ∉ (T : Sym2 V) := by
    intro hmem
    have hcase : t = u ∨ t = q.getVert 1 := by
      simpa [T, threadFirstEdge] using hmem
    rcases hcase with htu | htx₁
    · exact (IsKThread.endpoints_ne G hq) htu.symm
    · have hx₁two : IsTwoVertex G (q.getVert 1) :=
        IsKThread.internal_two G hq (by omega) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)
      exact (isThreeVertex_ne_isTwoVertex G hq.end_three hx₁two) htx₁
  have hagreeCritical : ColoringsAgreeOff G ({P, T} : Set G.edgeSet)
      colour critical := by
    intro f hf
    have hne : f ≠ P ∧ f ≠ T := by simpa using hf
    simp [critical, hne.1, hne.2]
  have hmissFar : ∀ f, IsExternalAt G t U f →
      f ∉ ({P, T} : Set G.edgeSet) := by
    intro f hfext hfset
    have hfcase : f = P ∨ f = T := by simpa using hfset
    exact hfcase.elim
      (fun hf ↦ htP (by simpa [hf] using hfext.1))
      (fun hf ↦ htT (by simpa [hf] using hfext.1))
  have hfarEq : ExternalInducedColors G colour t U =
      ExternalInducedColors G critical t U :=
    externalInducedColors_eq_of_agreeOff G hagreeCritical hmissFar
  have hfar : ExternalInducedColors G colour t U = {i, j} := by
    rw [hfarEq, ← hcritical.2.2]
    simpa [Set.pair_comm] using hcriticalStart.2
  have havail : ColorAvailableOn G Dset colour S (some e) := by
    simpa [S, U, r, threadFirstEdge, threadLastEdge, Sym2.eq_swap] using
      longPair_twoThreadMiddle_otherColour_available_twoOne G h g r
        hvw hvq hwq colour Dset i j c e hei hej hec hP hQ hTcore hScore
          (by simpa [U, r, threadLastEdge, Sym2.eq_swap] using hU)
          (by simpa [U, r, threadLastEdge, Sym2.eq_swap] using hfar)
  have hvalid : IsOneTwoColoringOn G Dset new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := S) (a := some e) hSD').mpr
    refine ⟨?_, havail⟩
    exact IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.diff_subset
  have hsat : OneSaturated G new := by
    simpa [new] using oneSaturated_recolor_induced_to_induced
      G hprepared.2.1 S c e (by simpa [S] using hS)
  have htwo : ConditionTwo G new := by
    simpa [new, S, U, r, threadFirstEdge, threadLastEdge, Sym2.eq_swap] using
      conditionTwo_recolor_twoThreadMiddle_to_induced G hsub h r colour
        hprepared.2.2.1 (by simpa [Dset] using hprepared.1) c e hec hP
        hScore (by simpa [U, r, threadLastEdge, Sym2.eq_swap] using hU)
        hA hB (by simpa [S, Dset, r] using hSD')
        (by simpa [P, U, r, threadLastEdge, Sym2.eq_swap] using hUP)
  have hthree : ConditionThree G new := by
    simpa [new, S, r] using
      conditionThree_recolor_edge_between_two_vertices G r.first_two
        r.second_two r.middle_adj colour hprepared.2.2.2 e
  exact ⟨by simpa [Dset, new] using hvalid,
    by simpa [new] using hsat, by simpa [new] using htwo,
    by simpa [new] using hthree⟩

/-- If the two induced continuations use the two distinct colours outside
the centre pair, recolour the 2-thread middle edge with the 1-thread
continuation colour and reduce to the equal-colour case. -/
theorem longPair_hasGoodFour_of_twoThreadMiddle_oneContinuation_distinct
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j c e : Fin 4)
    (hij : i ≠ j)
    (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c)
    (hci : c ≠ i) (hcj : c ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hC : colour (⟨s(w₁, w₂), g.last_adj⟩ : G.edgeSet) = some e)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hSD : (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    HasGoodFour G := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let C : G.edgeSet := ⟨s(w₁, w₂), g.last_adj⟩
  let S : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2),
      q.adj_getVert_succ (i := 1) (by
        have hlen : q.length = 3 := by simpa using hq.length
        omega)⟩
  let changed : G.edgeSet → OneTwoColor 4 := recolor G colour S (some e)
  let r₂ := hq.twoThreadCoreData G
  have hpreparedChanged : PreparedThreeThreadGap G h changed := by
    exact longPair_prepared_recolor_twoThreadMiddle_twoOne G hsub h g q hq
      hvw hvq hwq colour hprepared i j c e hei hej hec hP hQ hT hS hA hB
        hSD hUP (by simpa [P, T] using hcritical)
  have hPS : P ≠ S := by
    intro hEq
    have hf : none = some c := hP.symm.trans (by simpa [P, S, hEq] using hS)
    simp at hf
  have hRS : R ≠ S := by
    intro hEq
    have hf : none = some c := hR.symm.trans (by simpa [R, S, hEq] using hS)
    simp at hf
  have hQS : Q ≠ S := by
    intro hEq
    have hf : some i = some c := hQ.symm.trans (by simpa [Q, S, hEq] using hS)
    exact hci (Option.some.inj hf).symm
  have hTS : T ≠ S := by
    intro hEq
    have hf : some j = some c := hT.symm.trans (by simpa [T, S, hEq] using hS)
    exact hcj (Option.some.inj hf).symm
  have hCS : C ≠ S := by
    intro hEq
    have hf : some e = some c := hC.symm.trans (by simpa [C, S, hEq] using hS)
    exact hec (Option.some.inj hf)
  have hchangedP : changed P = none := by simp [changed, hPS, P, hP]
  have hchangedR : changed R = none := by simp [changed, hRS, R, hR]
  have hchangedQ : changed Q = some i := by simp [changed, hQS, Q, hQ]
  have hchangedT : changed T = some j := by simp [changed, hTS, T, hT]
  have hchangedC : changed C = some e := by simp [changed, hCS, C, hC]
  have hchangedS : changed S = some e := by simp [changed]
  have hAD : (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) ∉
      RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa using left_chain_edge_not_retained G h.left_adj
  have hBD : (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) ∉
      RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa using right_chain_edge_not_retained G h.right_adj
  have hAS : (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) ≠ S :=
    fun hEq ↦ hAD (hEq ▸ hSD)
  have hBS : (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) ≠ S :=
    fun hEq ↦ hBD (hEq ▸ hSD)
  exact longPair_hasGoodFour_of_twoThreadMiddle_oneContinuation_same
    G hsub h r₂ g hvq hvw hwq.symm changed hpreparedChanged j i e
      hij.symm (by simpa [P] using hchangedP)
      (by simpa [R] using hchangedR)
      (by simpa [r₂, T, threadFirstEdge, Sym2.eq_swap] using hchangedT)
      (by simpa [Q] using hchangedQ)
      (by simpa [r₂, S] using hchangedS)
      (by simpa [C] using hchangedC)
      (by simp [changed, hAS, hA]) (by simp [changed, hBS, hB])
      hPD hQD hRP hRQ

/-! ## The matching 1-thread-continuation subcase -/

/-- Prepared-gap preservation for the alternate swap that makes the
2-thread first edge matching.  Condition 2 is exposed exactly as one
missing colour at the first vertex of the 1-thread. -/
theorem longPair_prepared_selectedFresh_twoThreadFirstMatching_twoOne
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hCd : colour (⟨s(w₁, w₂), g.last_adj⟩ : G.edgeSet) ≠ some d)
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
    (hmissW : ¬ VertexSeesInduced G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (threadFirstEdge G q hq) none) w₁ k)
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
    exact longPair_selectedFirst_fresh_available_twoOne G h g r
      hvw hvq hwq colour Dset d i j hP hQ
      (by simpa [r, T, threadFirstEdge, Sym2.eq_swap] using hT)
      hCd (by simpa [r] using hSd) hdi hdj
      (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalidAfterP : IsOneTwoColoringOn G Dset afterP := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := P) (a := some d) hPD').mpr
    refine ⟨?_, havailP⟩
    exact IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.diff_subset
  have havailT : ColorAvailableOn G Dset afterP T none := by
    simpa [afterP, P, T, r, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoThreadFirst_matching_available_after_selectedFresh_twoOne
        G h g r hvw hvq hwq colour Dset d i j hQ
        (by simpa [r, threadFirstEdge, Sym2.eq_swap] using hT)
        (by simpa [r] using hS)
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
      longPair_conditionTwo_selectedFresh_twoThreadFirstMatching_twoOne
        G hsub h g r hvw hvq hwq colour hprepared.2.2.1
          hprepared.2.1 d j k
          (by simpa [r, threadFirstEdge, Sym2.eq_swap] using hT)
          (by simpa [r] using hS) hA hB
          (by simpa [r, threadLastEdge, Sym2.eq_swap] using hUP)
          (by simpa [P, T, alt, afterP, r, threadFirstEdge,
            Sym2.eq_swap] using hmissW)
  have hcriticalAlt : ConditionThreeAtTwoThread G q hq alt := by
    exact longPair_conditionThreeAtTwoThread_alt_of_critical_twoOne
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

/-- The alternate 2-thread-first swap completes the selected gap whenever
its sole one-thread palette obligation has a missing induced colour. -/
theorem longPair_hasGoodFour_of_twoThreadFirstMatching_twoOne
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hCd : colour (⟨s(w₁, w₂), g.last_adj⟩ : G.edgeSet) ≠ some d)
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
    (hmissW : ¬ VertexSeesInduced G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (threadFirstEdge G q hq) none) w₁ k)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    HasGoodFour G := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let alt : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) T none
  have hpreparedAlt : PreparedThreeThreadGap G h alt := by
    exact longPair_prepared_selectedFresh_twoThreadFirstMatching_twoOne
      G hsub h g q hq hvw hvq hwq colour hprepared d i j k hP hQ hT
        hCd hS hSd hA hB hPD hTD hUP hdi hdj
        (by simpa [P, T, alt] using hmissW)
        (by simpa [P, T, alt] using hcritical)
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hAD : A ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [B] using right_chain_edge_not_retained G h.right_adj
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD)
  have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ hTD)
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD)
  have hRP' : R ≠ P := by simpa [R, P] using hRP
  have hRT' : R ≠ T := by simpa [R, T] using hRT
  have hAltP : alt P ≠ none := by simp [alt, hPT]
  have hAltR : alt R = none := by simp [alt, hRP', hRT', R, hR]
  have hAltA : alt A = none := by simp [alt, hAP, hAT, A, hA]
  have hAltB : alt B = none := by simp [alt, hBP, hBT, B, hB]
  have hAltT : alt T = none := by simp [alt]
  exact longPair_hasGoodFour_of_prepared_left_outer_induced G hsub h alt
    hpreparedAlt (by simpa [P] using hAltP) (by simpa [R] using hAltR)
      (by simpa [A] using hAltA) (by simpa [B] using hAltB)
      T hAltT (by simp [T, threadFirstEdge]) hAT.symm hBT.symm

/-- Two visible matching edges, all four induced colours, and a second
visible edge carrying one of those induced colours require seven distinct
visible edges. -/
theorem longPair_seven_le_card_visible_of_duplicate_induced
    {colour : G.edgeSet → OneTwoColor 4} {q : V}
    (m n p f : G.edgeSet) (c : Fin 4)
    (hmn : m ≠ n) (hfp : f ≠ p)
    (hm : colour m = none) (hn : colour n = none)
    (hp : colour p = some c) (hf : colour f = some c)
    (hmvis : (m : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hnvis : (n : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hpvis : (p : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hfvis : (f : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hall : ∀ i : Fin 4, VertexSeesInduced G colour q i) :
    7 ≤ (vertexVisibleEdgeFinset G q).card := by
  classical
  choose e hecolour v hv hclose using fun i ↦
    (vertexSeesInduced_iff G colour q i).mp (hall i)
  have hevis (i : Fin 4) :
      (e i : Sym2 V) ∈ vertexVisibleEdgeFinset G q :=
    mem_vertexVisibleEdgeFinset_of_endpoint_close G (hv i) (hclose i)
  let colourWitness : Fin 4 → G.edgeSet := fun i ↦ if i = c then p else e i
  have hcColour (i : Fin 4) : colour (colourWitness i) = some i := by
    by_cases hic : i = c
    · subst i
      simpa [colourWitness] using hp
    · simp [colourWitness, hic, hecolour i]
  have hcVis (i : Fin 4) :
      (colourWitness i : Sym2 V) ∈ vertexVisibleEdgeFinset G q := by
    by_cases hic : i = c
    · subst i
      simpa [colourWitness] using hpvis
    · simpa [colourWitness, hic] using hevis i
  have hfc (i : Fin 4) : f ≠ colourWitness i := by
    intro heq
    by_cases hic : i = c
    · subst i
      exact hfp (by simpa [colourWitness] using heq)
    · have hci : c = i := Option.some.inj
        (hf.symm.trans ((congrArg colour heq).trans (hcColour i)))
      exact hic hci.symm
  let witness : Bool ⊕ Option (Fin 4) →
      {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q}
    | Sum.inl false => ⟨m, hmvis⟩
    | Sum.inl true => ⟨n, hnvis⟩
    | Sum.inr none => ⟨f, hfvis⟩
    | Sum.inr (some i) => ⟨colourWitness i, hcVis i⟩
  have hinj : Function.Injective witness := by
    intro a b hab
    have habv := congrArg
      (fun x : {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} => x.1) hab
    cases a with
    | inl ba =>
        cases b with
        | inl bb =>
            cases ba
            · cases bb
              · rfl
              · exfalso
                simp only [witness] at habv
                apply hmn
                apply Subtype.ext
                exact habv
            · cases bb
              · exfalso
                simp only [witness] at habv
                apply hmn
                apply Subtype.ext
                exact habv.symm
              · rfl
        | inr ob =>
            cases ba
            · cases ob with
              | none =>
                  exfalso
                  simp only [witness] at habv
                  have hedge : m = f := Subtype.ext habv
                  have hfalse := hm.symm.trans ((congrArg colour hedge).trans hf)
                  simp at hfalse
              | some i =>
                  exfalso
                  simp only [witness] at habv
                  have hedge : m = colourWitness i :=
                    Subtype.ext habv
                  have hfalse := hm.symm.trans
                    ((congrArg colour hedge).trans (hcColour i))
                  simp at hfalse
            · cases ob with
              | none =>
                  exfalso
                  simp only [witness] at habv
                  have hedge : n = f := Subtype.ext habv
                  have hfalse := hn.symm.trans ((congrArg colour hedge).trans hf)
                  simp at hfalse
              | some i =>
                  exfalso
                  simp only [witness] at habv
                  have hedge : n = colourWitness i :=
                    Subtype.ext habv
                  have hfalse := hn.symm.trans
                    ((congrArg colour hedge).trans (hcColour i))
                  simp at hfalse
    | inr oa =>
        cases b with
        | inl bb =>
            cases oa with
            | none =>
                cases bb
                · exfalso
                  simp only [witness] at habv
                  have hedge : f = m := Subtype.ext habv
                  have hfalse := hf.symm.trans ((congrArg colour hedge).trans hm)
                  simp at hfalse
                · exfalso
                  simp only [witness] at habv
                  have hedge : f = n := Subtype.ext habv
                  have hfalse := hf.symm.trans ((congrArg colour hedge).trans hn)
                  simp at hfalse
            | some i =>
                cases bb
                · exfalso
                  simp only [witness] at habv
                  have hedge : colourWitness i = m :=
                    Subtype.ext habv
                  have hfalse := (hcColour i).symm.trans
                    ((congrArg colour hedge).trans hm)
                  simp at hfalse
                · exfalso
                  simp only [witness] at habv
                  have hedge : colourWitness i = n :=
                    Subtype.ext habv
                  have hfalse := (hcColour i).symm.trans
                    ((congrArg colour hedge).trans hn)
                  simp at hfalse
        | inr ob =>
            cases oa with
            | none =>
                cases ob with
                | none => rfl
                | some i =>
                    exfalso
                    simp only [witness] at habv
                    exact hfc i (Subtype.ext habv)
            | some i =>
                cases ob with
                | none =>
                    exfalso
                    simp only [witness] at habv
                    exact hfc i (Subtype.ext habv).symm
                | some j =>
                    simp only [witness] at habv
                    have hedge : colourWitness i = colourWitness j :=
                      Subtype.ext habv
                    have hij : i = j := Option.some.inj
                      ((hcColour i).symm.trans
                        ((congrArg colour hedge).trans (hcColour j)))
                    subst j
                    rfl
  have hcard := Fintype.card_le_of_injective witness hinj
  simpa using hcard

/-- The middle edge of a 2-thread starting at `u` is not visible from the
first internal vertex of a different 1-thread starting at `u`.  Otherwise
the two arms close a cycle of length at most four. -/
theorem longPair_twoThreadMiddle_not_visible_from_oneThreadFirst
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u w₁ w₂ t : V} (g : OneThreadCore G u w₁ w₂)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hwq : w₁ ≠ q.getVert 1) :
    let S : G.edgeSet :=
      ⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩
    (S : Sym2 V) ∉ vertexVisibleEdgeFinset G w₁ := by
  dsimp only
  let r := hq.twoThreadCoreData G
  let p₁ : G.Walk w₁ (q.getVert 1) :=
    .cons g.first_adj.symm (.cons hq.first_step_adj .nil)
  have hp₁ : p₁.IsPath := by
    apply (Walk.IsPath.of_adj hq.first_step_adj).cons
    simp [p₁, g.first_adj.ne.symm, hwq]
  have hnot₁ : ¬ G.Adj w₁ (q.getVert 1) := by
    intro hadj
    exact longPair_not_adj_endpoints_of_short_path G hgirth hp₁
      (by simp [p₁]) (by simp [p₁]) hadj.symm
  have hwq₂ : w₁ ≠ q.getVert 2 := by
    intro heq
    apply hnot₁
    simpa [heq] using r.middle_adj.symm
  let p₂ : G.Walk w₁ (q.getVert 2) :=
    .cons g.first_adj.symm
      (.cons hq.first_step_adj (.cons r.middle_adj .nil))
  have hp₂ : p₂.IsPath := by
    have htail :
        (Walk.cons hq.first_step_adj
          (Walk.cons r.middle_adj (.nil : G.Walk (q.getVert 2)
            (q.getVert 2)))).IsPath := by
      apply (Walk.IsPath.of_adj r.middle_adj).cons
      simpa using And.intro hq.first_step_adj.ne r.second_ne_start.symm
    apply htail.cons
    simp [p₂, g.first_adj.ne.symm, hwq, hwq₂]
  have hnot₂ : ¬ G.Adj w₁ (q.getVert 2) := by
    intro hadj
    exact longPair_not_adj_endpoints_of_short_path G hgirth hp₂
      (by simp [p₂]) (by simp [p₂]) hadj.symm
  intro hvis
  rw [vertexVisibleEdgeFinset] at hvis
  obtain ⟨a, hawa, haS⟩ := Finset.mem_biUnion.mp hvis
  have hwa : G.Adj w₁ a := (G.mem_neighborFinset w₁ a).mp hawa
  rw [G.mem_incidenceFinset] at haS
  have haMem : a ∈ (s(q.getVert 1, q.getVert 2) : Sym2 V) :=
    haS.2
  have hacase : a = q.getVert 1 ∨ a = q.getVert 2 := by
    simpa using haMem
  exact hacase.elim (fun ha ↦ hnot₁ (ha ▸ hwa))
    (fun ha ↦ hnot₂ (ha ▸ hwa))

/-- If the alternate swap fills the entire palette at the 1-thread vertex,
move the target middle colour first.  Any remaining witness of the moved
colour would give seven visible edges, contradicting subcubicity. -/
theorem longPair_hasGoodFour_of_twoThreadFirstMatching_full_twoOne
    (hgirth : (16 : ℕ∞) ≤ G.egirth) (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j c : Fin 4)
    (hdi : d ≠ i) (hdj : d ≠ j) (hdc : d ≠ c)
    (hci : c ≠ i) (hcj : c ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hC : colour (⟨s(w₁, w₂), g.last_adj⟩ : G.edgeSet) = none)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hSD : (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRT : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq))
    (hall : ∀ a : Fin 4, VertexSeesInduced G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (threadFirstEdge G q hq) none) w₁ a) :
    HasGoodFour G := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.last_adj⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let S : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2),
      q.adj_getVert_succ (i := 1) (by
        have hlen : q.length = 3 := by simpa using hq.length
        omega)⟩
  let U : G.edgeSet := threadLastEdge G q hq
  let changed : G.edgeSet → OneTwoColor 4 := recolor G colour S (some d)
  let alt : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) T none
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G changed P (some c)) T none
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some j)) T none
  let changedCritical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G changed P (some j)) T none
  let r := hq.twoThreadCoreData G
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPS : P ≠ S := by
    intro heq
    have hf : none = some c := hP.symm.trans (by simpa [P, S, heq] using hS)
    simp at hf
  have hRS : R ≠ S := by
    intro heq
    have hf : none = some c := hR.symm.trans (by simpa [R, S, heq] using hS)
    simp at hf
  have hQS : Q ≠ S := by
    intro heq
    have hf : some i = some c := hQ.symm.trans (by simpa [Q, S, heq] using hS)
    exact hci (Option.some.inj hf).symm
  have hTS : T ≠ S := by
    intro heq
    have hf : some j = some c := hT.symm.trans (by simpa [T, S, heq] using hS)
    exact hcj (Option.some.inj hf).symm
  have hCS : C ≠ S := by
    intro heq
    have hf : none = some c := hC.symm.trans (by simpa [C, S, heq] using hS)
    simp at hf
  have hCP : C ≠ P := by
    intro heq
    have hval : s(w₁, w₂) = s(v₁, u) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hvw hval.1.symm
    · exact g.first_adj.ne hval.1.symm
  have hCT : C ≠ T := by
    intro heq
    have hf : none = some j := hC.symm.trans (by simpa [C, T, heq] using hT)
    simp at hf
  have hpreparedChanged : PreparedThreeThreadGap G h changed := by
    exact longPair_prepared_recolor_twoThreadMiddle_twoOne G hsub h g q hq
      hvw hvq hwq colour hprepared i j c d hdi hdj hdc hP hQ hT hS hA hB
        hSD hUP (by simpa [P, T] using hcritical)
  have hchangedP : changed P = none := by simp [changed, hPS, P, hP]
  have hchangedR : changed R = none := by simp [changed, hRS, R, hR]
  have hchangedQ : changed Q = some i := by simp [changed, hQS, Q, hQ]
  have hchangedC : changed C = none := by simp [changed, hCS, C, hC]
  have hchangedT : changed T = some j := by simp [changed, hTS, T, hT]
  have hchangedS : changed S = some d := by simp [changed]
  have hAS : (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) ≠ S := by
    intro heq
    have hf : none = some c := hA.symm.trans (by simpa [S, heq] using hS)
    simp at hf
  have hBS : (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) ≠ S := by
    intro heq
    have hf : none = some c := hB.symm.trans (by simpa [S, heq] using hS)
    simp at hf
  have hcriticalBase :
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t U ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t U := by
    simpa [critical, P, T, U] using hcritical
  have hcritEq : changedCritical = recolor G critical S (some d) := by
    funext f
    by_cases hfP : f = P
    · subst f
      simp [changedCritical, changed, critical, hPS, hPS.symm,
        hPT, hPT.symm]
    · by_cases hfT : f = T
      · subst f
        simp [changedCritical, changed, critical, hPT, hPT.symm,
          hTS, hTS.symm]
      · by_cases hfS : f = S
        · subst f
          simp [changedCritical, changed, critical, hPS, hPS.symm,
            hTS, hTS.symm]
        · simp [changedCritical, changed, critical, hfP, hfT, hfS]
  have huS : u ∉ (S : Sym2 V) := by
    intro hmem
    have hcase : u = q.getVert 1 ∨ u = q.getVert 2 := by simpa [S] using hmem
    rcases hcase with hux₁ | hux₂
    · exact hq.first_step_adj.ne hux₁
    · exact r.second_ne_start hux₂.symm
  have htS : t ∉ (S : Sym2 V) := by
    intro hmem
    have hcase : t = q.getVert 1 ∨ t = q.getVert 2 := by simpa [S] using hmem
    rcases hcase with htx₁ | htx₂
    · exact r.first_ne_end htx₁.symm
    · exact r.last_adj.ne htx₂.symm
  have hagreeCrit : ColoringsAgreeOff G ({S} : Set G.edgeSet)
      critical changedCritical := by
    rw [hcritEq]
    simpa using coloringsAgreeOff_recolor G critical S (some d)
  have hmissStart : ∀ f, IsExternalAt G u T f →
      f ∉ ({S} : Set G.edgeSet) := by
    intro f hfext hfset
    have hf : f = S := by simpa using hfset
    subst f
    exact huS hfext.1
  have hmissFar : ∀ f, IsExternalAt G t U f →
      f ∉ ({S} : Set G.edgeSet) := by
    intro f hfext hfset
    have hf : f = S := by simpa using hfset
    subst f
    exact htS hfext.1
  have hcriticalChanged :
      ExternalEdgesInduced G changedCritical u T ∧
        ExternalEdgesInduced G changedCritical t U ∧
        ExternalInducedColors G changedCritical u T =
          ExternalInducedColors G changedCritical t U := by
    have hstart := externalEdgesInduced_of_agreeOff G hagreeCrit
      hmissStart hcriticalBase.1
    have hfar := externalEdgesInduced_of_agreeOff G hagreeCrit
      hmissFar hcriticalBase.2.1
    have hstartEq := externalInducedColors_eq_of_agreeOff G hagreeCrit hmissStart
    have hfarEq := externalInducedColors_eq_of_agreeOff G hagreeCrit hmissFar
    refine ⟨hstart, hfar, ?_⟩
    calc
      ExternalInducedColors G changedCritical u T =
          ExternalInducedColors G critical u T := hstartEq.symm
      _ = ExternalInducedColors G critical t U := hcriticalBase.2.2
      _ = ExternalInducedColors G changedCritical t U := hfarEq
  have hmissW : ¬ VertexSeesInduced G final w₁ d := by
    intro hseen
    obtain ⟨f, hfinalF, x, hxf, hclose⟩ :=
      (vertexSeesInduced_iff G final w₁ d).mp hseen
    have hfvis : (f : Sym2 V) ∈ vertexVisibleEdgeFinset G w₁ :=
      mem_vertexVisibleEdgeFinset_of_endpoint_close G hxf hclose
    have hSnotvis : (S : Sym2 V) ∉ vertexVisibleEdgeFinset G w₁ := by
      simpa [S] using
        longPair_twoThreadMiddle_not_visible_from_oneThreadFirst
          G hgirth g q hq hwq
    have hfS : f ≠ S := by
      intro heq
      subst f
      exact hSnotvis hfvis
    have hfinalP : final P = some c := by
      simp [final, changed, hPT, hPS, hPS.symm]
    have hfinalT : final T = none := by simp [final]
    have hfP : f ≠ P := by
      intro heq
      subst f
      have hcd : c = d := Option.some.inj (hfinalP.symm.trans hfinalF)
      exact hdc hcd.symm
    have hfT : f ≠ T := by
      intro heq
      subst f
      have hfalse : none = some d := hfinalT.symm.trans hfinalF
      simp at hfalse
    have hcolourF : colour f = some d := by
      simpa [final, changed, hfS, hfP, hfT] using hfinalF
    have haltF : alt f = some d := by
      simp [alt, hfP, hfT, hcolourF]
    have haltP : alt P = some d := by simp [alt, hPT]
    have haltC : alt C = none := by simp [alt, hCP, hCT, C, hC]
    have haltT : alt T = none := by simp [alt]
    have hPvis : (P : Sym2 V) ∈ vertexVisibleEdgeFinset G w₁ :=
      mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [P]) (Or.inr g.first_adj.symm)
    have hCvis : (C : Sym2 V) ∈ vertexVisibleEdgeFinset G w₁ :=
      mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [C]) (Or.inl rfl)
    have hTvis : (T : Sym2 V) ∈ vertexVisibleEdgeFinset G w₁ :=
      mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [T, threadFirstEdge]) (Or.inr g.first_adj.symm)
    have hseven : 7 ≤ (vertexVisibleEdgeFinset G w₁).card :=
      longPair_seven_le_card_visible_of_duplicate_induced G C T P f d
        hCT (by exact hfP) haltC haltT haltP haltF hCvis hTvis hPvis hfvis
          (by simpa [alt, P, T] using hall)
    have hsix := card_vertexVisibleEdgeFinset_le_six G hsub g.first_two
    omega
  apply longPair_hasGoodFour_of_twoThreadFirstMatching_twoOne
    G hsub h g q hq hvw hvq hwq changed hpreparedChanged c i j d
  · exact hchangedP
  · exact hchangedR
  · exact hchangedQ
  · exact hchangedT
  · rw [show changed (⟨s(w₁, w₂), g.last_adj⟩ : G.edgeSet) = none by
      simpa [C] using hchangedC]
    simp
  · rw [hchangedS]
    simp
  · rw [hchangedS]
    simpa using hdc
  · simp [changed, hAS, hA]
  · simp [changed, hBS, hB]
  · exact hPD
  · exact hTD
  · exact hUP
  · exact hRP
  · exact hRT
  · exact hci
  · exact hcj
  · simpa [final, changed, P, T] using hmissW
  · simpa [changedCritical, P, T] using hcriticalChanged

/-- The matching continuation of the 1-thread also closes Claim 1.  A
missing colour permits the direct swap; a full palette invokes the
seven-visible-edge escape above. -/
theorem longPair_hasGoodFour_of_oneContinuation_matching_twoOne
    (hgirth : (16 : ℕ∞) ≤ G.egirth) (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : OneThreadCore G u w₁ w₂)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j c : Fin 4) (hij : i ≠ j) (hci : c ≠ i) (hcj : c ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hC : colour (⟨s(w₁, w₂), g.last_adj⟩ : G.edgeSet) = none)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hSD : (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRT : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
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
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let C : G.edgeSet := ⟨s(w₁, w₂), g.last_adj⟩
  let S : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2),
      q.adj_getVert_succ (i := 1) (by
        have hlen : q.length = 3 := by simpa using hq.length
        omega)⟩
  have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by simp [hij]
  obtain ⟨d, hdPair, hcd⟩ :=
    longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
      hpairCard (some c)
  have hdData : d ≠ i ∧ d ≠ j := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hdPair
  have hdc : d ≠ c := by
    intro hdc'
    apply hcd
    exact congrArg some hdc'.symm
  let alt : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) T none
  by_cases hfull : ∀ a : Fin 4, VertexSeesInduced G alt w₁ a
  · exact longPair_hasGoodFour_of_twoThreadFirstMatching_full_twoOne
      G hgirth hsub h g q hq hvw hvq hwq colour hprepared d i j c
        hdData.1 hdData.2 hdc hci hcj hP hR hQ hT hC hS hA hB
        hPD hTD hSD hUP hRP hRT (by simpa [P, T] using hcritical)
        (by simpa [alt, P, T] using hfull)
  · push_neg at hfull
    obtain ⟨k, hk⟩ := hfull
    apply longPair_hasGoodFour_of_twoThreadFirstMatching_twoOne
      G hsub h g q hq hvw hvq hwq colour hprepared d i j k
    · exact hP
    · exact hR
    · exact hQ
    · exact hT
    · rw [hC]
      simp
    · rw [hS]
      simp
    · rw [hS]
      simpa using hcd
    · exact hA
    · exact hB
    · exact hPD
    · exact hTD
    · exact hUP
    · exact hRP
    · exact hRT
    · exact hdData.1
    · exact hdData.2
    · simpa [alt, P, T] using hk
    · exact hcritical

/-! ## Claim 1 and the complete local `(3,2,1)` reduction -/

/- In a bad graph, the middle edge of the displayed 2-thread in a
`(3,2,1)` configuration is matching-coloured. -/
set_option maxHeartbeats 2400000 in
theorem longPair_twoThread_middle_matching_in_bad_graph_twoOne
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u y}
    (hp : IsKThread G p 3) (hq : IsKThread G q 2)
    (hr : IsKThread G r 1)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) :
    (transportColoringToSupergraph
        (G.deleteIncidenceSet_le (p.getVert 2)) small)
      (⟨s(q.getVert 1, q.getVert 2),
        (hq.twoThreadCoreData G).middle_adj⟩ : G.edgeSet) = none := by
  classical
  let h := hp.threeThreadCore G
  let g := hr.oneThreadCore G
  let rr := hq.twoThreadCoreData G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le (p.getVert 2)) small
  let Dset : Set G.edgeSet :=
    RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
  let P : G.edgeSet := threadFirstEdge G p hp
  let R : G.edgeSet := threadLastEdge G p hp
  let Q : G.edgeSet := threadFirstEdge G r hr
  let C : G.edgeSet := threadLastEdge G r hr
  let T : G.edgeSet := threadFirstEdge G q hq
  let S : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2), rr.middle_adj⟩
  let U : G.edgeSet := threadLastEdge G q hq
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
      (show b ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using hb)
      heq
    exact hab hinj
  have hqGetNe (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (hab : a ≠ b) :
      q.getVert a ≠ q.getVert b := by
    intro heq
    have hinj := hq.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ q.length} by simpa [hqLen] using ha)
      (show b ∈ {n : ℕ | n ≤ q.length} by simpa [hqLen] using hb)
      heq
    exact hab hinj
  have hpEnd : p.getVert 4 = z := by
    rw [← hpLen]
    exact p.getVert_length
  have hqEnd : q.getVert 3 = t := by
    rw [← hqLen]
    exact q.getVert_length
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
  have hSD : S ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = q.getVert 1 ∨
        p.getVert 2 = q.getVert 2 := by simpa [S] using hmem
    rcases hcase with hcase | hcase
    · exact (twoThread_vertex_far_from_threeThread_middle G hq h
        (q.getVert_mem_support 1)).1 hcase.symm
    · exact (twoThread_vertex_far_from_threeThread_middle G hq h
        (q.getVert_mem_support 2)).1 hcase.symm
  have hCD : C ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = r.getVert 1 ∨ p.getVert 2 = y := by
      simpa [C, threadLastEdge, hr.length] using hmem
    rcases hcase with hcase | hcase
    · apply hnotU₂
      simpa [hcase] using g.first_adj
    · exact (isThreeVertex_ne_isTwoVertex G g.end_three h.middle_two)
        hcase.symm
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hr.first_step_adj hpr
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hpq
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hr.first_step_adj
        hq.first_step_adj hqr.symm
  have hQC : Q ≠ C := by
    intro heq
    have hval : s(r.getVert 1, u) = s(r.getVert 1, y) := by
      simpa [Q, C, threadFirstEdge, threadLastEdge, hr.length,
        Sym2.eq_swap] using congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact g.end_ne_start hval.2.symm
    · exact (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two)
        hval.1.symm
  have hTS : T ≠ S := by
    intro heq
    have hval : s(u, q.getVert 1) =
        s(q.getVert 1, q.getVert 2) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hq.first_step_adj.ne hval.1
    · exact hqGetNe 0 2 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
  have hQS : Q ≠ S := by
    intro heq
    have hval : s(r.getVert 1, u) =
        s(q.getVert 1, q.getVert 2) := by
      simpa [Q, S, rr, threadFirstEdge, Sym2.eq_swap] using
        congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hqr hval.1.symm
    · exact hq.first_step_adj.ne hval.2
  have hCT : C ≠ T := by
    intro heq
    have hval : s(r.getVert 1, y) = s(u, q.getVert 1) := by
      simpa [C, T, threadFirstEdge, threadLastEdge, hr.length,
        Sym2.eq_swap] using congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact g.first_adj.ne hval.1.symm
    · exact hqr hval.1.symm
  have hUP : U ≠ P := by
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
    have hval : s(p.getVert 3, z) = s(r.getVert 1, u) := by
      simpa [R, Q, threadFirstEdge, threadLastEdge, Sym2.eq_swap] using
        congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hpGetNe 4 0 (by omega) (by omega) (by omega)
        (by simpa [hpEnd] using hval.2)
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
  have hRT : R ≠ T := by
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
  by_contra hSne
  have hSnon : base S ≠ none := by simpa [S, rr, base] using hSne
  obtain ⟨j, hTval, hcritical⟩ :=
    longPair_twoThread_second_induced_critical_normal_form
      G hp hq hpq small hsmall hsub
        (by simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP)
        (by simpa [h, base, R, threadLastEdge] using hR)
        (by simpa [S, rr, base] using hSnon) hbad
  have hPval : base P = none := by
    simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP
  have hRval : base R = none := by
    simpa [h, base, R, threadLastEdge] using hR
  have hTval' : base T = some j := by simpa [base, T] using hTval
  have hvalid : IsOneTwoColoringOn G Dset base := by
    simpa [Dset] using hprepared.1
  have hQne : base Q ≠ none := by
    intro hQnone
    have hcompat := hvalid P hPD Q hQD hPQ
    have hdisj : EndpointDisjoint G P Q := by
      simpa [hPval, hQnone] using hcompat
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
      cases hSval : base S with
      | none => exact False.elim (hSnon hSval)
      | some c =>
          have hci : c ≠ i := by
            intro hci
            subst c
            have hcompat := hvalid Q hQD S hSD hQS
            have hsep : InducedSeparated G Q S := by
              simpa [hQval, hSval] using hcompat
            exact hsep.2 ⟨u, by simp [Q, threadFirstEdge], q.getVert 1,
              by simp [S], hq.first_step_adj⟩
          have hcj : c ≠ j := by
            intro hcj
            subst c
            have hcompat := hvalid T hTD S hSD hTS
            have hsep : InducedSeparated G T S := by
              simpa [hTval', hSval] using hcompat
            exact hsep.1 (q.getVert 1)
              (by simp [T, threadFirstEdge]) (by simp [S])
          cases hCval : base C with
          | none =>
              apply hbad
              exact longPair_hasGoodFour_of_oneContinuation_matching_twoOne
                G hgirth hsub h g q hq hpr hpq hqr.symm base hprepared
                  i j c hij hci hcj
                  (by simpa [P, threadFirstEdge, Sym2.eq_swap] using hPval)
                  hRval
                  (by simpa [base, Q, g, threadFirstEdge, Sym2.eq_swap]
                    using hQval)
                  (by simpa [base, T] using hTval')
                  (by simpa [base, C, g, threadLastEdge, hr.length]
                    using hCval)
                  (by simpa [base, S, rr] using hSval)
                  (by simpa [h, base, A] using hA)
                  (by simpa [h, base, B] using hB)
                  (by simpa [h, P, Dset, threadFirstEdge, Sym2.eq_swap]
                    using hPD)
                  (by simpa [T, Dset] using hTD)
                  (by simpa [S, rr, Dset] using hSD)
                  (by simpa [h, P, U, threadFirstEdge, threadLastEdge,
                    Sym2.eq_swap] using hUP)
                  (by simpa [h, P, R, threadFirstEdge, threadLastEdge,
                    Sym2.eq_swap] using hRP)
                  (by simpa [h, R, T, threadFirstEdge, threadLastEdge,
                    Sym2.eq_swap] using hRT)
                  (by simpa [base, P, T, threadFirstEdge, Sym2.eq_swap]
                    using hcritical)
          | some e =>
              have hei : e ≠ i := by
                intro hei
                subst e
                have hcompat := hvalid Q hQD C hCD hQC
                have hsep : InducedSeparated G Q C := by
                  simpa [hQval, hCval] using hcompat
                exact hsep.1 (r.getVert 1)
                  (by simp [Q, threadFirstEdge])
                  (by simp [C, threadLastEdge, hr.length])
              have hej : e ≠ j := by
                intro hej
                subst e
                have hcompat := hvalid C hCD T hTD hCT
                have hsep : InducedSeparated G C T := by
                  simpa [hCval, hTval'] using hcompat
                exact hsep.2 ⟨r.getVert 1,
                  by simp [C, threadLastEdge, hr.length], u,
                  by simp [T, threadFirstEdge], g.first_adj.symm⟩
              by_cases hec : e = c
              · subst e
                apply hbad
                exact longPair_hasGoodFour_of_twoThreadMiddle_oneContinuation_same
                  G hsub h rr g hpq hpr hqr base hprepared j i c hij.symm
                    (by simpa [P, threadFirstEdge, Sym2.eq_swap] using hPval)
                    hRval
                    (by simpa [base, T, rr, threadFirstEdge, Sym2.eq_swap]
                      using hTval')
                    (by simpa [base, Q, g, threadFirstEdge, Sym2.eq_swap]
                      using hQval)
                    (by simpa [base, S, rr] using hSval)
                    (by simpa [base, C, g, threadLastEdge, hr.length]
                      using hCval)
                    (by simpa [h, base, A] using hA)
                    (by simpa [h, base, B] using hB)
                    (by simpa [h, P, Dset, threadFirstEdge, Sym2.eq_swap]
                      using hPD)
                    (by simpa [Q, Dset, threadFirstEdge, Sym2.eq_swap]
                      using hQD)
                    (by simpa [h, P, R, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hRP)
                    (by simpa [h, R, Q, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hRQ)
              · apply hbad
                exact longPair_hasGoodFour_of_twoThreadMiddle_oneContinuation_distinct
                  G hsub h g q hq hpr hpq hqr.symm base hprepared i j c e
                    hij hei hej hec hci hcj
                    (by simpa [P, threadFirstEdge, Sym2.eq_swap] using hPval)
                    hRval
                    (by simpa [base, Q, g, threadFirstEdge, Sym2.eq_swap]
                      using hQval)
                    (by simpa [base, T] using hTval')
                    (by simpa [base, C, g, threadLastEdge, hr.length]
                      using hCval)
                    (by simpa [base, S, rr] using hSval)
                    (by simpa [h, base, A] using hA)
                    (by simpa [h, base, B] using hB)
                    (by simpa [h, P, Dset, threadFirstEdge, Sym2.eq_swap]
                      using hPD)
                    (by simpa [Q, Dset, threadFirstEdge, Sym2.eq_swap]
                      using hQD)
                    (by simpa [S, rr, Dset] using hSD)
                    (by simpa [h, P, U, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hUP)
                    (by simpa [h, P, R, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hRP)
                    (by simpa [h, R, Q, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hRQ)
                    (by simpa [base, P, T, threadFirstEdge, Sym2.eq_swap]
                      using hcritical)

/- Kernel-level reduction of the paper's `(3,2,1)` configuration. -/
set_option maxHeartbeats 3000000 in
theorem longPair_no_threeTwoOne_of_smaller_good
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u y}
    (hp : IsKThread G p 3) (hq : IsKThread G q 2)
    (hr : IsKThread G r 1)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) : False := by
  have hmiddle := longPair_twoThread_middle_matching_in_bad_graph_twoOne
    G hgirth hp hq hr hpq hpr hqr small hsmall hsub hbad
  exact longPair_no_threeTwoOne_of_smaller_good_of_second_matching
    G hgirth hp hq hr hpq hpr hqr small hsmall hsub hbad
      (by simpa using hmiddle)

end Finite

end

end LeanCo.PackingEdgeColoring
