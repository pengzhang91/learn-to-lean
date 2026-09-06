import LeanCo.PackingEdgeColoring.SectionFourZeroThread
import LeanCo.PackingEdgeColoring.SectionFourLongPreparedOuter

/-!
# The zero-thread third-arm reduction for Section 4

This module treats the local core of the paper's `no330` configuration.
The selected and second arms are 3-threads and the third arm is the edge
between two degree-three vertices.  The first branch below is the paper's
swap when both other edges at the far end of that 0-thread are induced.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Below girth sixteen, two paths with the same endpoints and total
length less than sixteen coincide. -/
theorem longPair_short_paths_eq_of_girth_sixteen
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {a b : V} {p q : G.Walk a b} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < 16) : p = q := by
  by_contra hne
  obtain ⟨w, _hwp, _hwq, c, hc, hcle⟩ :=
    hp.exists_isCycle_length_le_add_of_ne hq hne
  have hboundE : (16 : ℕ∞) ≤ (c.length : ℕ∞) :=
    (le_egirth.mp hgirth) w c hc
  have hbound : 16 ≤ c.length := by exact_mod_cast hboundE
  omega

/-- The endpoint of any path of length at most four leaving along a
different first edge is different from, and nonadjacent to, the middle
vertex of a selected 3-thread.  This packages the girth geometry needed to
show that all edges on the other arms survive the incidence deletion. -/
theorem longPair_short_path_endpoint_far_from_threeThread_middle
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z y : V} {p : G.Walk u z} {q : G.Walk u y}
    (hp : IsKThread G p 3) (hq : q.IsPath) (hqLen : q.length ≤ 4)
    (hfirst : p.getVert 1 ≠ q.getVert 1) :
    y ≠ p.getVert 2 ∧ ¬ G.Adj y (p.getVert 2) := by
  have hpLen : p.length = 4 := by simpa using hp.length
  let pL : G.Walk u (p.getVert 2) := p.take 2
  have hpL : pL.IsPath := hp.1.take 2
  have hpLlen : pL.length = 2 := by simp [pL, hpLen]
  have hu₂ : u ≠ p.getVert 2 := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show 0 ∈ {n : ℕ | n ≤ p.length} by simp)
      (show 2 ∈ {n : ℕ | n ≤ p.length} by simp [hpLen])
      (by simpa using heq)
    omega
  have hnotU₂ : ¬ G.Adj u (p.getVert 2) := by
    intro hadj
    exact longPair_not_adj_endpoints_of_short_path G hgirth hpL
      (by simp [hpLlen]) (by simp [hpLlen]) hadj.symm
  have first_contra
      (q' : G.Walk u (p.getVert 2)) (hq'snd : q'.snd = q.snd)
      (heq : pL = q') : False := by
    have hsnd := congrArg
      (fun w : G.Walk u (p.getVert 2) ↦ w.snd) heq
    apply hfirst
    simpa [pL, hq'snd] using hsnd
  have hv₂q : p.getVert 2 ∉ q.support := by
    intro hv₂q
    let q₀ : G.Walk u (p.getVert 2) := q.takeUntil (p.getVert 2) hv₂q
    have hq₀p : q₀.IsPath := hq.takeUntil hv₂q
    have hq₀len : q₀.length ≤ 4 := by
      exact (q.length_takeUntil_le_length hv₂q).trans hqLen
    have heq : pL = q₀ :=
      longPair_short_paths_eq_of_girth_sixteen G hgirth hpL hq₀p (by omega)
    apply first_contra q₀
    · exact q.snd_takeUntil hu₂.symm hv₂q
    · exact heq
  constructor
  · intro hy₂
    subst y
    exact hv₂q q.end_mem_support
  · intro hyv₂
    by_cases hyu : y = u
    · subst y
      exact hnotU₂ hyv₂
    let qplus : G.Walk u (p.getVert 2) := q.concat hyv₂
    have hqplusP : qplus.IsPath := by
      change (q.concat hyv₂).IsPath
      exact (hq.concat hv₂q) hyv₂
    have hqplusLen : qplus.length ≤ 5 := by
      simp [qplus, Walk.length_concat]
      omega
    have heq : pL = qplus :=
      longPair_short_paths_eq_of_girth_sixteen G hgirth hpL hqplusP (by omega)
    apply first_contra qplus
    · unfold qplus
      cases q <;> simp_all [Walk.concat]
    · exact heq

/-- The first edge of a 2-thread cannot be a zero-thread edge: its internal
endpoint has degree two, whereas both endpoints of the zero-thread have
degree three. -/
theorem longPair_twoThread_firstEdge_ne_zeroThread
    {a b u x : V} (p : G.Walk a b) (hp : IsKThread G p 2)
    (r : ZeroThreadCore G u x) :
    threadFirstEdge G p hp ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) := by
  intro heq
  have hval : s(a, p.getVert 1) = s(x, u) := congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hval
  have hpTwo : IsTwoVertex G (p.getVert 1) :=
    IsKThread.internal_two G hp (by omega) (by
      have hlen : p.length = 3 := by simpa using hp.length
      omega)
  rcases hval with hcase | hcase
  · exact (isThreeVertex_ne_isTwoVertex G r.start_three hpTwo) hcase.2.symm
  · exact (isThreeVertex_ne_isTwoVertex G r.end_three hpTwo) hcase.2.symm

/-- The endpoint-symmetric version for the last edge of a 2-thread. -/
theorem longPair_twoThread_lastEdge_ne_zeroThread
    {a b u x : V} (p : G.Walk a b) (hp : IsKThread G p 2)
    (r : ZeroThreadCore G u x) :
    threadLastEdge G p hp ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) := by
  intro heq
  have hval : s(p.getVert 2, b) = s(x, u) := congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hval
  have hpTwo : IsTwoVertex G (p.getVert 2) :=
    IsKThread.internal_two G hp (by omega) (by
      have hlen : p.length = 3 := by simpa using hp.length
      omega)
  rcases hval with hcase | hcase
  · exact (isThreeVertex_ne_isTwoVertex G r.end_three hpTwo) hcase.1.symm
  · exact (isThreeVertex_ne_isTwoVertex G r.start_three hpTwo) hcase.1.symm

/-- Simultaneously moving an induced colour from a zero-thread edge onto
the selected matching outer edge, and moving matching onto the zero-thread,
preserves retained-edge validity when the other two far-end edges are
induced. -/
theorem longPair_validOn_swap_selectedOuter_zeroThread
    {u v₁ v₂ v₃ z x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : ZeroThreadCore G u x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hN : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) ≠ none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ none)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPT : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet)) :
    IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G)
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some j))
        (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) none) := by
  classical
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let W : G.edgeSet := ⟨s(x, b), hb⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some j)) T none
  have hPT' : P ≠ T := by simpa [P, T] using hPT
  have hPD : P ∈ D := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hTD' : T ∈ D := by simpa [D, T] using hTD
  have hnewP : new P = some j := by simp [new, hPT']
  have hnewT : new T = none := by simp [new]
  have hnewOff (f : G.edgeSet) (hfP : f ≠ P) (hfT : f ≠ T) :
      new f = colour f := by simp [new, hfP, hfT]
  have hPcross (f : G.edgeSet) (hfD : f ∈ D)
      (hfP : f ≠ P) (hfT : f ≠ T) :
      PairCompatible G P f (some j) (colour f) := by
    cases hcf : colour f with
    | none => exact pairCompatible_of_ne G (by simp)
    | some k =>
        by_cases hjk : j = k
        · subst k
          have hp := hvalid T hTD' f hfD hfT.symm
          have hsepT : InducedSeparated G T f := by
            simpa [T, hT, hcf] using hp
          have hsepP := longPair_inducedSeparated_selectedOuter_of_fork G h T f
            (by simp [T]) (by simpa [D] using hfD)
            (by simpa [P] using hfP) hsepT
          simpa [P, hcf] using hsepP
        · exact pairCompatible_of_ne G (by simp [hcf, hjk])
  have hTcross (f : G.edgeSet) (hfD : f ∈ D)
      (hfP : f ≠ P) (hfT : f ≠ T) :
      PairCompatible G T f none (colour f) := by
    cases hcf : colour f with
    | some k => exact pairCompatible_of_ne G (by simp [hcf])
    | none =>
        have hPcompat := hvalid P hPD f hfD hfP.symm
        have hPdisj : EndpointDisjoint G P f := by
          simpa [P, hP, hcf] using hPcompat
        have hdisj : EndpointDisjoint G T f := by
          intro y hyT hyf
          have hycase : y = x ∨ y = u := by simpa [T] using hyT
          rcases hycase with hyx | hyu
          · have hxf : x ∈ (f : Sym2 V) := by simpa [hyx] using hyf
            obtain ⟨q, hfq⟩ := Sym2.mem_iff_exists.mp hxf
            have hxq : G.Adj x q := by
              have hadj := f.2
              rw [hfq] at hadj
              simpa using hadj
            have hqN : q ∈ G.neighborFinset x :=
              (G.mem_neighborFinset x q).mpr hxq
            rw [hN] at hqN
            have hqcase : q = u ∨ q = a ∨ q = b := by simpa using hqN
            rcases hqcase with rfl | rfl | rfl
            · exact hfT (Subtype.ext (by simpa [T, Sym2.eq_swap] using hfq))
            · have hfU : f = U :=
                Subtype.ext (by simpa [U, Sym2.eq_swap] using hfq)
              exact hU (by simpa [U, hfU] using hcf)
            · have hfW : f = W :=
                Subtype.ext (by simpa [W, Sym2.eq_swap] using hfq)
              exact hV (by simpa [W, hfW] using hcf)
          · exact hPdisj u (by simp [P]) (by simpa [hyu] using hyf)
        simpa [T, hcf] using hdisj
  change IsOneTwoColoringOn G D new
  intro e heD f hfD hef
  by_cases heP : e = P
  · subst e
    by_cases hfT : f = T
    · subst f
      rw [hnewP, hnewT]
      exact pairCompatible_of_ne G (by simp)
    · have hfP : f ≠ P := by simpa using hef.symm
      rw [hnewP, hnewOff f hfP hfT]
      exact hPcross f hfD hfP hfT
  · by_cases heT : e = T
    · subst e
      by_cases hfP : f = P
      · subst f
        rw [hnewT, hnewP]
        exact pairCompatible_of_ne G (by simp)
      · have hfT : f ≠ T := by simpa using hef.symm
        rw [hnewT, hnewOff f hfP hfT]
        exact hTcross f hfD hfP hfT
    · by_cases hfP : f = P
      · subst f
        have hp := hPcross e heD heP heT
        rw [hnewOff e heP heT, hnewP]
        exact (pairCompatible_comm G).mpr hp
      · by_cases hfT : f = T
        · subst f
          have hp := hTcross e heD heP heT
          rw [hnewOff e heP heT, hnewT]
          exact (pairCompatible_comm G).mpr hp
        · rw [hnewOff e heP heT, hnewOff f hfP hfT]
          exact hvalid e heD f hfD hef

/-- Saturation is preserved by the selected-edge/zero-thread swap.  Any
edge formerly saturated by the selected matching edge is now saturated by
the zero-thread at `u`, or by the still-missing gap edge at `v₁`. -/
theorem longPair_oneSaturated_swap_selectedOuter_zeroThread
    {u v₁ v₂ v₃ z x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : ZeroThreadCore G u x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour) (j : Fin 4)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPT : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet)) :
    OneSaturated G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some j))
        (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) none) := by
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
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
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD')
  have hnewP : new P = some j := by simp [new, hPT']
  have hnewT : new T = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewOff (e : G.edgeSet) (heP : e ≠ P) (heT : e ≠ T) :
      new e = colour e := by simp [new, heP, heT]
  change OneSaturated G new
  intro e he
  by_cases heP : e = P
  · subst e
    exact ⟨T, hnewT, u, by simp [P], by simp [T]⟩
  by_cases heT : e = T
  · subst e
    exact False.elim (he hnewT)
  have heOld : colour e ≠ none := by
    intro heNone
    exact he ((hnewOff e heP heT).trans heNone)
  obtain ⟨f, hf, y, hye, hyf⟩ := hsat e heOld
  by_cases hfP : f = P
  · subst f
    have hycase : y = v₁ ∨ y = u := by simpa [P] using hyf
    rcases hycase with hyv₁ | hyu
    · exact ⟨A, hnewA, y, hye, by simpa [A, hyv₁]⟩
    · exact ⟨T, hnewT, y, hye, by simpa [T, hyu]⟩
  · have hfT : f ≠ T := by
      intro hfT
      subst f
      have hTsome : colour T = some j := by simpa [T] using hT
      have hTnone : colour T = none := by simpa [T] using hf
      have hfalse : some j = none := hTsome.symm.trans hTnone
      simp at hfalse
    exact ⟨f, (hnewOff f hfP hfT).trans hf, y, hye, hyf⟩

/-- Condition 3 survives the selected-edge/zero-thread swap.  At an
affected endpoint, the now-matching zero-thread is itself an external edge;
it cannot be a 2-thread's end edge because both of its endpoints have
degree three. -/
theorem longPair_conditionThree_swap_selectedOuter_zeroThread
    {u v₁ v₂ v₃ z x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : ZeroThreadCore G u x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (j : Fin 4)
    (hPT : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet)) :
    ConditionThree G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some j))
        (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) none) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some j)) T none
  have hPT' : P ≠ T := by simpa [P, T] using hPT
  have hnewT : new T = none := by simp [new]
  have hagree : ColoringsAgreeOff G ({P, T} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ T := by simpa using he
    simp [new, hne.1, hne.2]
  change ConditionThree G new
  apply hold.of_agreeOff G hagree
  intro a b p hp haffect hleft hright
  rcases haffect with haffect | haffect
  · obtain ⟨e, heS, hext⟩ := haffect
    have hecase : e = P ∨ e = T := by simpa using heS
    rcases hecase with rfl | rfl
    · have hau : a = u :=
        longPair_start_eq_three_of_external_selectedOuter G p hp h
          (by simpa [P] using hext)
      subst a
      have hfirstT : threadFirstEdge G p hp ≠ T := by
        simpa [T] using longPair_twoThread_firstEdge_ne_zeroThread G p hp r
      obtain ⟨i, hi⟩ := hleft T ⟨by simp [T], hfirstT.symm⟩
      rw [hnewT] at hi
      simp at hi
    · obtain ⟨i, hi⟩ := hleft T (by simpa [T] using hext)
      rw [hnewT] at hi
      simp at hi
  · obtain ⟨e, heS, hext⟩ := haffect
    have hecase : e = P ∨ e = T := by simpa using heS
    rcases hecase with rfl | rfl
    · have hbu : b = u :=
        longPair_end_eq_three_of_external_selectedOuter G p hp h
          (by simpa [P] using hext)
      subst b
      have hlastT : threadLastEdge G p hp ≠ T := by
        simpa [T] using longPair_twoThread_lastEdge_ne_zeroThread G p hp r
      obtain ⟨i, hi⟩ := hright T ⟨by simp [T], hlastT.symm⟩
      rw [hnewT] at hi
      simp at hi
    · obtain ⟨i, hi⟩ := hright T (by simpa [T] using hext)
      rw [hnewT] at hi
      simp at hi

/-- A degree-two vertex whose induced palette is affected by the two-edge
zero-thread swap is either the deleted middle vertex, adjacent to the common
centre, or adjacent to the far endpoint of the zero-thread. -/
theorem longPair_twoVertex_paletteAffectedBy_zeroSwap_cases
    {u v₁ v₂ v₃ z x q : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : ZeroThreadCore G u x) (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet),
        (⟨s(x, u), r.adj.symm⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = v₂ ∨ G.Adj q u ∨ G.Adj q x := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, heS, y, hye, hqy⟩ := haffect
  have hecase : e = (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∨
      e = (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) := by
    simpa using heS
  have hqu : q ≠ u := by
    exact (isThreeVertex_ne_isTwoVertex G h.start_three hq).symm
  have hqx : q ≠ x := by
    exact (isThreeVertex_ne_isTwoVertex G r.end_three hq).symm
  rcases hecase with rfl | rfl
  · have hycase : y = v₁ ∨ y = u := by simpa using hye
    rcases hycase with hyv₁ | hyu
    · subst y
      rcases hqy with hqv₁ | hqv₁
      · exact Or.inr (Or.inl (by simpa [hqv₁] using h.first_adj.symm))
      · have hqN : q ∈ G.neighborFinset v₁ :=
          (G.mem_neighborFinset v₁ q).mpr hqv₁.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
          h.left_adj h.first_adj.symm h.middle_ne_start] at hqN
        have hqcase : q = v₂ ∨ q = u := by simpa using hqN
        exact hqcase.elim Or.inl (fun hEq ↦ False.elim (hqu hEq))
    · subst y
      rcases hqy with hEq | hadj
      · exact False.elim (hqu hEq)
      · exact Or.inr (Or.inl hadj)
  · have hycase : y = x ∨ y = u := by simpa using hye
    rcases hycase with hyx | hyu
    · subst y
      rcases hqy with hEq | hadj
      · exact False.elim (hqx hEq)
      · exact Or.inr (Or.inr hadj)
    · subst y
      rcases hqy with hEq | hadj
      · exact False.elim (hqu hEq)
      · exact Or.inr (Or.inl hadj)

/-- If all three edges at a degree-three vertex are induced, saturation of
one displayed edge supplies a matching edge at its other endpoint. -/
theorem exists_matching_incident_zero_far_neighbor_of_all_induced
    {u x a b : V} (r : ZeroThreadCore G u x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hN : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ≠ none)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) ≠ none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ none) :
    ∃ m : G.edgeSet, colour m = none ∧ a ∈ (m : Sym2 V) := by
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let W : G.edgeSet := ⟨s(x, b), hb⟩
  obtain ⟨m, hm, y, hyU, hym⟩ := hsat U (by simpa [U] using hU)
  have hycase : y = x ∨ y = a := by simpa [U] using hyU
  rcases hycase with hyx | hya
  · have hxm : x ∈ (m : Sym2 V) := by simpa [hyx] using hym
    obtain ⟨q, hmq⟩ := Sym2.mem_iff_exists.mp hxm
    have hxq : G.Adj x q := by
      have hadj := m.2
      rw [hmq] at hadj
      simpa using hadj
    have hqN : q ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x q).mpr hxq
    rw [hN] at hqN
    have hqcase : q = u ∨ q = a ∨ q = b := by simpa using hqN
    rcases hqcase with rfl | rfl | rfl
    · have hmT : m = T :=
        Subtype.ext (by simpa [T, Sym2.eq_swap] using hmq)
      exact False.elim (hT (by simpa [T, hmT] using hm))
    · have hmU : m = U :=
        Subtype.ext (by simpa [U, Sym2.eq_swap] using hmq)
      exact False.elim (hU (by simpa [U, hmU] using hm))
    · have hmW : m = W :=
        Subtype.ext (by simpa [W, Sym2.eq_swap] using hmq)
      exact False.elim (hV (by simpa [W, hmW] using hm))
  · exact ⟨m, hm, by simpa [hya] using hym⟩

/-- Condition 2 is preserved by the zero-thread swap in the all-induced
far-end branch.  Near the far endpoint, saturation supplies an unchanged
matching witness; a hypothetical full new palette transports back to the
old palette, with the old zero-thread supplying its displaced colour. -/
theorem longPair_conditionTwo_swap_selectedOuter_zeroThread
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
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
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPT : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet)) :
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
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
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
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj h.first_adj.symm
  have hCT : C ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      r.start_three g.left_adj r.adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hnewP : new P = some j := by simp [new, hPT']
  have hnewT : new T = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBT, B, hB]
  have hnewC : new C = none := by simp [new, hCP, hCT, C, hC]
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
      apply longPair_paletteCondition_at_two_visible_matching G hsub g.first_two
        g.left_adj g.middle_two C T hCT hnewC hnewT
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
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

/-- The complete prepared-gap package for the first far-end subcase of
`no330`: both noncentral edges at the other endpoint of the zero-thread are
induced, so matching can be moved from the selected outer edge to the
zero-thread. -/
theorem longPair_prepared_swap_selectedOuter_zeroThread
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
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
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPT : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet)) :
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
    longPair_conditionTwo_swap_selectedOuter_zeroThread G hsub h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour hprepared.2.2.1
      hprepared.2.1 j hP hT hU hV hA hB hC hTD hPT,
    longPair_conditionThree_swap_selectedOuter_zeroThread G h r colour
      hprepared.2.2.2 j hPT⟩

/-- The paper's first `no330` far-endpoint subcase.  If neither of the two
other edges at the far endpoint of the zero-thread is matching, the
selected outer matching edge and the zero-thread are swapped, after which
the generic prepared-gap completion restores the two deleted edges. -/
theorem longPair_hasGoodFour_of_zeroThread_hard_of_far_both_induced
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
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
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPT : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(x, u), r.adj.symm⟩ : G.edgeSet)) :
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
    exact longPair_prepared_swap_selectedOuter_zeroThread G hsub h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour hprepared j hP hT hU hV
      hA hB hC hTD hPT
  have hnewP : new P = some j := by simp [new, afterP, hPT']
  have hnewT : new T = none := by simp [new]
  have hnewR : new R = none := by
    simp [new, afterP, hRP, hRT, R, hR]
  have hnewA : new A = none := by
    simp [new, afterP, hAP, hAT, A, hA]
  have hnewB : new B = none := by
    simp [new, afterP, hBP, hBT, B, hB]
  exact longPair_hasGoodFour_of_prepared_left_outer_induced G hsub h new
    hpreparedNew (by change new P ≠ none; simp [hnewP]) hnewR hnewA hnewB
    T hnewT (by simp [T]) hAT.symm hBT.symm

/-! ## Recolouring the second 3-thread in the far-matching branch -/

/-- When one far edge of the zero-thread is matching, a colour absent from
the centre palette, the other far edge, and the next induced edge of the
second 3-thread is available on that thread's first edge. -/
theorem longPair_forkFirst_fresh_available_zeroThird
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hVk : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ some k)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDk : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ≠ some k)
    (hretained : ∀ f : G.edgeSet, f ∈ Dset → v₂ ∉ (f : Sym2 V)) :
    ColorAvailableOn G Dset colour
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
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
        g.left_adj g.first_adj.symm g.middle_ne_start f hwf with hfC | hfQ'
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
    have hcN : c ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x c).mpr hxc
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
    rcases edge_eq_left_or_right_of_incident_two G g.middle_two
        g.left_adj.symm g.right_adj g.first_ne_third f hwf with hfC | hfD
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
        g.left_adj g.first_adj.symm g.middle_ne_start] at hdN
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

/-- Condition 2 survives recolouring the first edge of the second long arm
in the zero-thread configuration.  The zero-thread endpoint itself has
degree three, so the only affected degree-two neighbours of the centre are
the first vertices of the two long arms. -/
theorem longPair_conditionTwo_recolor_forkFirst_zeroThird
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none) :
    ConditionTwo G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hv₁w₁
  have hCQ : C ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      g.start_three g.left_adj g.first_adj.symm
  have hAQ : A ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      g.start_three h.left_adj g.first_adj.symm
  have hBQ : B ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      g.start_three h.right_adj.symm g.first_adj.symm
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj h.first_adj.symm
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
  rcases longThreeFork_twoVertex_paletteAffectedBy_forkFirst_cases G g hq
      (by simpa [Q] using haffect) with hqw₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G g.middle_two
      g.left_adj.symm g.right_adj g.first_ne_third g.first_two g.third_two
      hmatch) hall
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
        g.left_adj g.middle_two C P hCP hnewC hnewP
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [P]) (Or.inr g.first_adj.symm)
      · exact hall
    · subst q
      exact False.elim ((isThreeVertex_ne_isTwoVertex G r.end_three hq) rfl)

/-- Prepared-gap preservation for the fresh recolouring of the second
3-thread in the far-matching branch. -/
theorem longPair_prepared_recolor_forkFirst_fresh_zeroThird
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hVk : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ some k)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDk : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ≠ some k)
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
    exact longPair_forkFirst_fresh_available_zeroThird G h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour Dset k hP hC hU hVk hk hDk
      (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalid : IsOneTwoColoringOn G Dset new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := Q) (a := some k)
      (by simpa [Dset, Q] using hQD)).mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.diff_subset, havail⟩
  have hsat : OneSaturated G new :=
    longPair_oneSaturated_recolor_forkFirst_induced G g colour
      hprepared.2.1 i k hQ hC
  have htwo : ConditionTwo G new :=
    longPair_conditionTwo_recolor_forkFirst_zeroThird G hsub h g r
      hv₁w₁ hv₁x hw₁x colour hprepared.2.2.1 k hP hC hA hB
  have hthree : ConditionThree G new :=
    longThreeFork_conditionThree_recolor_forkFirst_induced G h g colour
      hprepared.2.2.2 k hP (by simpa [P, Q] using hPQ)
  exact ⟨hvalid, hsat, htwo, hthree⟩

/-- In the far-matching branch, the fourth colour can be put on the first
edge of the second long arm unless that colour already occurs on its middle
edge.  The two gap edges are then filled by the crossed endpoint palettes. -/
theorem longPair_hasGoodFour_of_zeroThread_far_matching_of_middle_avoids
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b) (hbu : b ≠ u)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
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
    (hDavoid : ∀ l : Fin 4,
      l ∉ ({i, j} : Set (Fin 4)) → l ≠ m →
      colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ≠ some l) :
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
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hQD' : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hTD' : T ∈ Dset := by simpa [Dset, T] using hTD
  have hVD' : Vedge ∈ Dset := by simpa [Dset, Vedge] using hVD
  have hvalid : IsOneTwoColoringOn G Dset colour := by
    simpa [Dset] using hprepared.1
  have hij : i ≠ j := by
    intro hij
    subst j
    have hp := hvalid Q hQD' T hTD' hQT
    have hsep : InducedSeparated G Q T := by
      simpa [Q, T, hQ, hT] using hp
    exact hsep.1 u (by simp [Q]) (by simp [T])
  have hLold : ExternalInducedColors G colour u P = {i, j} := by
    simpa [P, Q, T] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        h.first_adj g.first_adj r.adj hv₁w₁ hv₁x hw₁x colour i j
        hP hQ hT
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
    have hsep := hvalid T hTD' Vedge hVD' hTV
    have hind : InducedSeparated G T Vedge := by
      simpa [T, Vedge, hT, hV] using hsep
    exact hind.1 x (by simp [T]) (by simp [Vedge])
  have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by simp [hij]
  obtain ⟨l, hlPair, hlmOpt⟩ :=
    longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
      hpairCard (some m)
  have hlm : l ≠ m := by
    intro hEq
    apply hlmOpt
    simp [hEq]
  have hlData : l ≠ i ∧ l ≠ j := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hlPair
  have hlOld : l ∉ ExternalInducedColors G colour u P := by
    rw [hLold]
    exact hlPair
  let fresh : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some l)
  have hpreparedFresh : PreparedThreeThreadGap G h fresh := by
    exact longPair_prepared_recolor_forkFirst_fresh_zeroThird G hsub h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour hprepared i l hP hQ hC hU
      (by simpa [Vedge, hV] using hlmOpt) hA hB (by simpa [P] using hlOld)
      (hDavoid l hlPair hlm) hQD
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
        (by simpa [P] using hfreshP) (by simpa [Q] using hfreshQ)
        (by simpa [T] using hfreshT)
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

/-! ## The terminal shift in the remaining far-end branch -/

/-- If the third edge of the neighbouring 3-thread has induced colour `l`,
then that colour can be moved one step towards the common centre.  The only
new distance-two issue is through `w₁`; it is excluded by the external
palette at `u` and by the colour of the first edge of this arm. -/
theorem longPair_forkSecond_shift_induced_available
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (l : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQl : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ≠ some l)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) = some l)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hl : l ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    ColorAvailableOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G \
        {(⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet),
          (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet)})
      colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) (some l) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let D₀ : Set G.edgeSet := Dset \ {C, D}
  have hDD' : D ∈ Dset := by simpa [Dset, D] using hDD
  have hD' : colour D = some l := by simpa [D] using hD
  have hP' : colour P = none := by simpa [P] using hP
  have hQl' : colour Q ≠ some l := by simpa [Q] using hQl
  change ColorAvailableOn G D₀ colour C (some l)
  apply (colorAvailableOn_some_iff G D₀ colour C l).mpr
  intro f hf₀ hfC hfl
  have hfDset : f ∈ Dset := hf₀.1
  have hfne : f ≠ C ∧ f ≠ D := by
    simpa [D₀] using hf₀.2
  have hsepD : InducedSeparated G D f := by
    have hp := hvalid D hDD' f hfDset (Ne.symm hfne.2)
    simpa [hD', hfl] using hp
  have noAtW₁ (hw₁f : w₁ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.first_adj.symm g.left_adj g.middle_ne_start.symm f hw₁f with
      hfQ | hfC'
    · have hEq : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfQ)
      apply hQl'
      simpa [hEq] using hfl
    · exact hfne.1 (Subtype.ext (by simpa [C] using hfC'))
  have noAtU (huf : u ∈ (f : Sym2 V)) : False := by
    have hfP : f ≠ P := by
      intro hEq
      subst f
      have hfalse : none = some l := hP'.symm.trans hfl
      simp at hfalse
    apply hl
    exact ⟨f, ⟨huf, hfP⟩, hfl⟩
  rw [inducedSeparated_iff_forall_endpoints] at hsepD ⊢
  intro a ha b hbf
  have hacase : a = w₁ ∨ a = w₂ := by simpa [C] using ha
  rcases hacase with haw₁ | haw₂
  · constructor
    · intro hEq
      apply noAtW₁
      rw [← haw₁, hEq]
      exact hbf
    · intro hadj
      have hbN : b ∈ G.neighborFinset w₁ :=
        (G.mem_neighborFinset w₁ b).mpr (by simpa [haw₁] using hadj)
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.left_adj g.first_adj.symm g.middle_ne_start] at hbN
      have hbcase : b = w₂ ∨ b = u := by simpa using hbN
      rcases hbcase with hbw₂ | hbu
      · exact (hsepD w₂ (by simp [D]) w₂
          (by simpa [hbw₂] using hbf)).1 rfl
      · exact noAtU (by simpa [hbu] using hbf)
  · simpa [haw₂] using hsepD w₂ (by simp [D]) b hbf

/-- After the preceding induced-colour move, the vacated third edge can
receive the matching colour.  At w₂ compatibility is inherited from the
old matching edge C; at w₃ the only other incident edge is the assumed
induced-coloured outer edge. -/
theorem longPair_forkThird_shift_matching_available
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (l : Fin 4)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) ≠ none)
    (hCD : (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    ColorAvailableOn G
      (insert (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet)
        (RetainedEdges (G.deleteIncidenceSet v₂) G \
          {(⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet),
            (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet)}))
      (recolor G colour
        (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) (some l))
      (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) none := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let E : G.edgeSet := ⟨s(w₃, t), g.last_adj⟩
  let D₀ : Set G.edgeSet := Dset \ {C, D}
  let afterC : G.edgeSet → OneTwoColor 4 := recolor G colour C (some l)
  have hCD' : C ∈ Dset := by simpa [C, Dset] using hCD
  have hC' : colour C = none := by simpa [C] using hC
  have hE' : colour E ≠ none := by simpa [E] using hE
  change ColorAvailableOn G (insert C D₀) afterC D none
  apply (colorAvailableOn_none_iff G (insert C D₀) afterC D).mpr
  intro f hfIns hfD hfnew
  rcases hfIns with hEq | hf₀
  · subst f
    have hfalse : some l = none := by simpa [afterC] using hfnew
    simp at hfalse
  · have hfDset : f ∈ Dset := hf₀.1
    have hfne : f ≠ C ∧ f ≠ D := by simpa [D₀] using hf₀.2
    have hfold : colour f = none := by
      simpa [afterC, hfne.1] using hfnew
    have hCdisj : EndpointDisjoint G C f := by
      have hp := hvalid C hCD' f hfDset (Ne.symm hfne.1)
      simpa [hC', hfold] using hp
    intro y hyD hyf
    have hycase : y = w₂ ∨ y = w₃ := by simpa [D] using hyD
    rcases hycase with hyw₂ | hyw₃
    · exact hCdisj w₂ (by simp [C]) (by simpa [hyw₂] using hyf)
    · have hw₃f : w₃ ∈ (f : Sym2 V) := by simpa [hyw₃] using hyf
      rcases edge_eq_left_or_right_of_incident_two G g.third_two
          g.right_adj.symm g.last_adj g.middle_ne_end f hw₃f with
        hfD' | hfE
      · exact hfne.2 (Subtype.ext (by simpa [D, Sym2.eq_swap] using hfD'))
      · apply hE'
        have hEqE : f = E := Subtype.ext (by simpa [E] using hfE)
        simpa [hEqE] using hfold

/-- Packing validity of the internal two-edge shift from
C matching and D induced to C induced and D matching. -/
theorem longPair_validOn_shift_forkMiddle
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (l : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQl : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ≠ some l)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) = some l)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) ≠ none)
    (hCD : (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hl : l ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G)
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) (some l))
        (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) none) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let D₀ : Set G.edgeSet := Dset \ {C, D}
  let afterC : G.edgeSet → OneTwoColor 4 := recolor G colour C (some l)
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterC D none
  have hCD' : C ∈ Dset := by simpa [C, Dset] using hCD
  have hDD' : D ∈ Dset := by simpa [D, Dset] using hDD
  have hCDne : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.left_adj g.right_adj g.first_ne_third
  have hvalid₀ : IsOneTwoColoringOn G D₀ colour :=
    hvalid.mono G (by exact Set.sdiff_subset)
  have hCfresh : C ∉ D₀ := by simp [D₀]
  have havailC : ColorAvailableOn G D₀ colour C (some l) := by
    simpa [Dset, D₀, C, D] using
      longPair_forkSecond_shift_induced_available G h g colour hvalid l
        hP hQl hD hDD hl
  have hvalidC : IsOneTwoColoringOn G (insert C D₀) afterC := by
    simpa [afterC] using hvalid₀.extend_one G hCfresh havailC
  have hDfresh : D ∉ insert C D₀ := by simp [D₀, hCDne.symm]
  have havailD : ColorAvailableOn G (insert C D₀) afterC D none := by
    simpa [Dset, D₀, C, D, afterC] using
      longPair_forkThird_shift_matching_available G (v₁ := v₁)
        (v₂ := v₂) (v₃ := v₃) (z := z) g colour hvalid l hC hE hCD
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

/-- Matching saturation is preserved by the internal shift.  The new
induced edge C is saturated by D.  If an old induced edge used C as its
matching witness at w₁, it is the first edge Q and is instead witnessed by
the selected matching edge P at the common centre. -/
theorem longPair_oneSaturated_shift_forkMiddle
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour)
    (l : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) = some l) :
    OneSaturated G
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) (some l))
        (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) none) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some l)) D none
  have hCD : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.left_adj g.right_adj g.first_ne_third
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj h.first_adj.symm
  have hDP : D ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.middle_two g.third_two
      h.start_three g.right_adj h.first_adj.symm
  have hfinalC : final C = some l := by simp [final, hCD]
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
          g.first_adj.symm g.left_adj g.middle_ne_start.symm e hw₁e with
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
      have hDsome : colour D = some l := by simpa [D] using hD
      have hDnone : colour D = none := by simpa [D] using hf
      have hfalse : some l = none := hDsome.symm.trans hDnone
      simp at hfalse
    exact ⟨f, (hfinalOff f hfC hfD).trans hf, y, hye, hyf⟩

/-- Condition 2 for the internal shift.  At w₁ and w₂ the old matching
edge C still supplies the premise of the old condition, while the moved
induced colour is transported back to D.  At w₃ two visible matching edges,
D and a matching edge incident with the far endpoint t, give the five-edge
capacity contradiction directly. -/
theorem longPair_conditionTwo_shift_forkMiddle
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour)
    (l : Fin 4)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) = some l)
    (M : G.edgeSet) (hM : colour M = none) (htM : t ∈ (M : Sym2 V))
    (hMC : M ≠ (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet))
    (hMD : M ≠ (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet)) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) (some l))
        (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) none) := by
  classical
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some l)) D none
  have hCD : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.left_adj g.right_adj g.first_ne_third
  have hC' : colour C = none := by simpa [C] using hC
  have hD' : colour D = some l := by simpa [D] using hD
  have hMC' : M ≠ C := by simpa [C] using hMC
  have hMD' : M ≠ D := by simpa [D] using hMD
  have hfinalC : final C = some l := by simp [final, hCD]
  have hfinalD : final D = none := by simp [final]
  have hfinalM : final M = none := by simp [final, hMC', hMD', hM]
  have hfinalOff (e : G.edgeSet) (heC : e ≠ C) (heD : e ≠ D) :
      final e = colour e := by simp [final, heC, heD]
  have hagree : ColoringsAgreeOff G ({C, D} : Set G.edgeSet) colour final := by
    intro e he
    have hne : e ≠ C ∧ e ≠ D := by simpa using he
    exact (hfinalOff e hne.1 hne.2).symm
  have oldAll (q : V) (hcloseD : q = w₂ ∨ G.Adj q w₂)
      (hall : ∀ i : Fin 4, VertexSeesInduced G final q i) :
      ∀ i : Fin 4, VertexSeesInduced G colour q i := by
    intro k
    by_cases hkl : k = l
    · subst k
      apply (vertexSeesInduced_iff G colour q l).mpr
      exact ⟨D, hD', w₂, by simp [D], hcloseD⟩
    · obtain ⟨e, he, y, hye, hqy⟩ :=
        (vertexSeesInduced_iff G final q k).mp (hall k)
      have heC : e ≠ C := by
        intro hEq
        subst e
        have hEqColour : some l = some k := hfinalC.symm.trans he
        exact hkl (Option.some.inj hEqColour).symm
      have heD : e ≠ D := by
        intro hEq
        subst e
        have hfalse : none = some k := hfinalD.symm.trans he
        simp at hfalse
      apply (vertexSeesInduced_iff G colour q k).mpr
      exact ⟨e, by simpa [hfinalOff e heC heD] using he, y, hye, hqy⟩
  change ConditionTwo G final
  apply hold.of_agreeOff G hagree
  intro q hq haffect _hmatch hall
  have hqcase : q = w₁ ∨ q = w₂ ∨ q = w₃ := by
    apply twoVertex_paletteAffectedBy_threeThread_gap G g hq
    simpa [C, D, Sym2.eq_swap] using haffect
  rcases hqcase with hqw₁ | hqw₂ | hqw₃
  · subst q
    apply hold w₁ g.first_two
    · exact (vertexSeesMatching_iff G colour w₁).mpr
        ⟨C, hC', by simp [C]⟩
    · exact oldAll w₁ (Or.inr g.left_adj) hall
  · subst q
    apply hold w₂ g.middle_two
    · exact (vertexSeesMatching_iff G colour w₂).mpr
        ⟨C, hC', by simp [C]⟩
    · exact oldAll w₂ (Or.inl rfl) hall
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub
      g.third_two g.right_adj.symm g.middle_two D M hMD'.symm
      hfinalD hfinalM
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [D]) (Or.inl rfl)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        htM (Or.inr g.last_adj)
    · exact hall

/-- Condition 3 is automatic for the internal shift because both changed
edges have only degree-two endpoints and hence cannot be external at an
endpoint of any certified 2-thread. -/
theorem longPair_conditionThree_shift_forkMiddle
    {u w₁ w₂ w₃ t : V}
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (l : Fin 4) :
    ConditionThree G
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) (some l))
        (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) none) := by
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some l)) D none
  have hagree : ColoringsAgreeOff G ({C, D} : Set G.edgeSet) colour final := by
    intro e he
    have hne : e ≠ C ∧ e ≠ D := by simpa using he
    simp [final, hne.1, hne.2]
  change ConditionThree G final
  apply hold.of_agreeOff G hagree
  intro a b p hp haffect
  exfalso
  apply not_threadConditionAffectedBy_threeThread_gap G g p hp
  simpa [C, D, Sym2.eq_swap] using haffect

/-- The complete prepared-gap package for the internal shift used in the
last no330 subcase. -/
theorem longPair_prepared_shift_forkMiddle
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (l : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQl : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ≠ some l)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) = some l)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) ≠ none)
    (hCD : (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hl : l ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (M : G.edgeSet) (hM : colour M = none) (htM : t ∈ (M : Sym2 V))
    (hMC : M ≠ (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet))
    (hMD : M ≠ (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet)) :
    PreparedThreeThreadGap G h
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) (some l))
        (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) none) := by
  exact ⟨
    longPair_validOn_shift_forkMiddle G h g colour hprepared.1 l
      hP hQl hC hD hE hCD hDD hl,
    longPair_oneSaturated_shift_forkMiddle G h g colour hprepared.2.1 l hP hD,
    longPair_conditionTwo_shift_forkMiddle G hsub (v₁ := v₁) (v₂ := v₂)
      (v₃ := v₃) (z := z) g colour hprepared.2.2.1 l hC hD
      M hM htM hMC hMD,
    longPair_conditionThree_shift_forkMiddle G g colour hprepared.2.2.2 l⟩

/-- If the two edges incident with w₃ along its 3-thread are induced,
saturation of the last edge must be witnessed at the far degree-three
endpoint t. -/
theorem exists_matching_incident_threeThread_far_of_last_induced
    {u w₁ w₂ w₃ t : V}
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ≠ none)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) ≠ none) :
    ∃ M : G.edgeSet, colour M = none ∧ t ∈ (M : Sym2 V) := by
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let E : G.edgeSet := ⟨s(w₃, t), g.last_adj⟩
  obtain ⟨M, hM, y, hyE, hyM⟩ := hsat E (by simpa [E] using hE)
  have hycase : y = w₃ ∨ y = t := by simpa [E] using hyE
  rcases hycase with hyw₃ | hyt
  · have hw₃M : w₃ ∈ (M : Sym2 V) := by simpa [hyw₃] using hyM
    rcases edge_eq_left_or_right_of_incident_two G g.third_two
        g.right_adj.symm g.last_adj g.middle_ne_end M hw₃M with
      hMD | hME
    · have hEqD : M = D :=
        Subtype.ext (by simpa [D, Sym2.eq_swap] using hMD)
      exact False.elim (hD (by simpa [hEqD, D] using hM))
    · have hEqE : M = E := Subtype.ext (by simpa [E] using hME)
      exact False.elim (hE (by simpa [hEqE, E] using hM))
  · exact ⟨M, hM, by simpa [hyt] using hyM⟩

/-- Complete the terminal paper shift.  First move colour l from D to C,
then use the already established neighbouring-arm swap to move colour i
from Q to P.  The resulting matching edge Q guards the left endpoint of
the selected gap. -/
theorem longPair_hasGoodFour_of_forkMiddle_terminal_shift
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i l : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) = some l)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hl : l ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let E : G.edgeSet := ⟨s(w₃, t), g.last_adj⟩
  have hPDset : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hRDset : R ∈ Dset := by
    change R ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [R, h.right_adj.ne, h.middle_ne_end]
  have hQDset : Q ∈ Dset := by simpa [Q, Dset] using hQD
  have hCDset : C ∈ Dset := by simpa [C, Dset] using hCD
  have hDDset : D ∈ Dset := by simpa [D, Dset] using hDD
  have hAD : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [B, Dset] using right_chain_edge_not_retained G h.right_adj
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hRP' : R ≠ P := by simpa [R, P] using hRP
  have hRQ' : R ≠ Q := by simpa [R, Q] using hRQ
  have hPC : P ≠ C := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.first_two g.middle_two h.start_three g.left_adj h.first_adj.symm).symm
  have hPD : P ≠ D := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.middle_two g.third_two h.start_three g.right_adj h.first_adj.symm).symm
  have hQC : Q ≠ C := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.first_two g.middle_two g.start_three g.left_adj g.first_adj.symm).symm
  have hQD' : Q ≠ D := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.middle_two g.third_two g.start_three g.right_adj g.first_adj.symm).symm
  have hRC : R ≠ C := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.first_two g.middle_two h.end_three g.left_adj h.last_adj).symm
  have hRD : R ≠ D := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.middle_two g.third_two h.end_three g.right_adj h.last_adj).symm
  have hQl : colour Q ≠ some l := by
    intro hQl
    apply hl
    exact ⟨Q, ⟨by simp [Q], hPQ'.symm⟩, hQl⟩
  obtain ⟨M, hM, htM⟩ :=
    exists_matching_incident_threeThread_far_of_last_induced G g colour
      hprepared.2.1 (by simpa [D, hD]) (by simpa [E] using hE)
  have hMC : M ≠ C := by
    intro hEq
    subst M
    have htcase : t = w₁ ∨ t = w₂ := by simpa [C] using htM
    exact htcase.elim
      (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two)
      (isThreeVertex_ne_isTwoVertex G g.end_three g.middle_two)
  have hMD : M ≠ D := by
    intro hEq
    subst M
    have hMnone : colour D = none := by simpa [D] using hM
    have hDsome : colour D = some l := by simpa [D] using hD
    have hfalse : some l = none := hDsome.symm.trans hMnone
    simp at hfalse
  let inner : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some l)) D none
  have hpreparedInner : PreparedThreeThreadGap G h inner := by
    exact longPair_prepared_shift_forkMiddle G hsub h g colour hprepared l
      hP (by simpa [Q] using hQl) hC hD hE hCD hDD hl M hM htM
      (by simpa [C] using hMC) (by simpa [D] using hMD)
  have hinnerP : inner P = none := by simp [inner, hPC, hPD, P, hP]
  have hinnerR : inner R = none := by simp [inner, hRC, hRD, R, hR]
  have hinnerQ : inner Q = some i := by simp [inner, hQC, hQD', Q, hQ]
  have hinnerC : inner C = some l := by
    have hCDne : C ≠ D := by
      simpa [C, D, Sym2.eq_swap] using
        chain_edges_ne G g.left_adj g.right_adj g.first_ne_third
    simp [inner, hCDne]
  have hAP : A ≠ P := fun hEq ↦ hAD (hEq ▸ hPDset)
  have hAQ : A ≠ Q := fun hEq ↦ hAD (hEq ▸ hQDset)
  have hAC : A ≠ C := fun hEq ↦ hAD (hEq ▸ hCDset)
  have hADedge : A ≠ D := fun hEq ↦ hAD (hEq ▸ hDDset)
  have hBP : B ≠ P := fun hEq ↦ hBD (hEq ▸ hPDset)
  have hBQ : B ≠ Q := fun hEq ↦ hBD (hEq ▸ hQDset)
  have hBC : B ≠ C := fun hEq ↦ hBD (hEq ▸ hCDset)
  have hBDedge : B ≠ D := fun hEq ↦ hBD (hEq ▸ hDDset)
  have hinnerA : inner A = none := by
    simp [inner, hAC, hADedge, A, hA]
  have hinnerB : inner B = none := by
    simp [inner, hBC, hBDedge, B, hB]
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G inner P (some i)) Q none
  have hpreparedFinal : PreparedThreeThreadGap G h final := by
    exact longPair_preparedThreeThreadGap_swap_selectedOuter_forkFirst G
      hsub h g inner hpreparedInner i
      (by simpa [P] using hinnerP) (by simpa [Q] using hinnerQ)
      (by simpa [C] using (show inner C ≠ none by simp [hinnerC]))
      (by simpa [A] using hinnerA) (by simpa [B] using hinnerB)
      hQD (by simpa [P, Q] using hPQ')
  have hfinalP : final P ≠ none := by simp [final, hPQ']
  have hfinalQ : final Q = none := by simp [final]
  have hfinalR : final R = none := by
    simp [final, hRP', hRQ', hinnerR]
  have hfinalA : final A = none := by
    simp [final, hAP, hAQ, hinnerA]
  have hfinalB : final B = none := by
    simp [final, hBP, hBQ, hinnerB]
  apply longPair_hasGoodFour_of_prepared_left_outer_induced G hsub h final
    hpreparedFinal hfinalP hfinalR hfinalA hfinalB Q hfinalQ
    (by simp [Q])
  · simpa [A] using hAQ.symm
  · simpa [B] using hBQ.symm

/-! ## The matching-last-edge subcase -/

/-- Once Q and D are temporarily removed, a colour missing from the far
external palette at t is available on D.  The two matching neighbours C
and E shield all other endpoints at distance at most two. -/
theorem longPair_forkThird_available_off_first_of_far_missing
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4) (c : Fin 4)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) = none)
    (hc : c ∉ ExternalInducedColors G colour t
      (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet)) :
    ColorAvailableOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G \
        {(⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet),
          (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet)})
      colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) (some c) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let E : G.edgeSet := ⟨s(w₃, t), g.last_adj⟩
  let D₀ : Set G.edgeSet := Dset \ {Q, D}
  have hC' : colour C = none := by simpa [C] using hC
  have hE' : colour E = none := by simpa [E] using hE
  change ColorAvailableOn G D₀ colour D (some c)
  apply (colorAvailableOn_some_iff G D₀ colour D c).mpr
  intro f hf₀ hfD hfc
  have hfne : f ≠ Q ∧ f ≠ D := by simpa [D₀] using hf₀.2
  have noAtW₁ (hw₁f : w₁ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.first_adj.symm g.left_adj g.middle_ne_start.symm f hw₁f with
      hfQ | hfC
    · exact hfne.1 (Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfQ))
    · have hEqC : f = C := Subtype.ext (by simpa [C] using hfC)
      have hfalse : none = some c := hC'.symm.trans (by simpa [hEqC] using hfc)
      simp at hfalse
  have noAtW₂ (hw₂f : w₂ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.middle_two
        g.left_adj.symm g.right_adj g.first_ne_third f hw₂f with
      hfC | hfD'
    · have hEqC : f = C :=
        Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC)
      have hfalse : none = some c := hC'.symm.trans (by simpa [hEqC] using hfc)
      simp at hfalse
    · exact hfne.2 (Subtype.ext (by simpa [D] using hfD'))
  have noAtW₃ (hw₃f : w₃ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.third_two
        g.right_adj.symm g.last_adj g.middle_ne_end f hw₃f with
      hfD' | hfE
    · exact hfne.2
        (Subtype.ext (by simpa [D, Sym2.eq_swap] using hfD'))
    · have hEqE : f = E := Subtype.ext (by simpa [E] using hfE)
      have hfalse : none = some c := hE'.symm.trans (by simpa [hEqE] using hfc)
      simp at hfalse
  have noAtT (htf : t ∈ (f : Sym2 V)) : False := by
    have hfE : f ≠ E := by
      intro hEq
      subst f
      have hfalse : none = some c := hE'.symm.trans hfc
      simp at hfalse
    apply hc
    exact ⟨f, ⟨htf, hfE⟩, hfc⟩
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = w₂ ∨ a = w₃ := by simpa [D] using ha
  rcases hacase with haw₂ | haw₃
  · constructor
    · intro hab
      apply noAtW₂
      rw [← haw₂, hab]
      exact hbf
    · intro hab
      have hbN : b ∈ G.neighborFinset w₂ :=
        (G.mem_neighborFinset w₂ b).mpr (by simpa [haw₂] using hab)
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.middle_two
        g.left_adj.symm g.right_adj g.first_ne_third] at hbN
      have hbcase : b = w₁ ∨ b = w₃ := by simpa using hbN
      exact hbcase.elim
        (fun hb ↦ noAtW₁ (by simpa [hb] using hbf))
        (fun hb ↦ noAtW₃ (by simpa [hb] using hbf))
  · constructor
    · intro hab
      apply noAtW₃
      rw [← haw₃, hab]
      exact hbf
    · intro hab
      have hbN : b ∈ G.neighborFinset w₃ :=
        (G.mem_neighborFinset w₃ b).mpr (by simpa [haw₃] using hab)
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.third_two
        g.right_adj.symm g.last_adj g.middle_ne_end] at hbN
      have hbcase : b = w₂ ∨ b = t := by simpa using hbN
      exact hbcase.elim
        (fun hb ↦ noAtW₂ (by simpa [hb] using hbf))
        (fun hb ↦ noAtT (by simpa [hb] using hbf))

/-- Packing validity for the simultaneous induced recolouring
Q : i to l and D : l to c in the matching-last-edge branch. -/
theorem longPair_validOn_recolor_forkFirstThird
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (c l : Fin 4) (hcl : c ≠ l)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) = none)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hVl : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ some l)
    (hl : l ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hc : c ∉ ExternalInducedColors G colour t
      (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet))
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G)
      (recolor G
        (recolor G colour
          (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) (some c))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some l)) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let E : G.edgeSet := ⟨s(w₃, t), g.last_adj⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let W : G.edgeSet := ⟨s(x, b), hb⟩
  let D₀ : Set G.edgeSet := Dset \ {Q, D}
  let afterD : G.edgeSet → OneTwoColor 4 := recolor G colour D (some c)
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterD Q (some l)
  have hQDset : Q ∈ Dset := by simpa [Q, Dset] using hQD
  have hDDset : D ∈ Dset := by simpa [D, Dset] using hDD
  have hDQ : D ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.middle_two g.third_two
      g.start_three g.right_adj g.first_adj.symm
  have hDP : D ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.middle_two g.third_two
      h.start_three g.right_adj h.first_adj.symm
  have hDC : D ≠ C := by
    simpa [D, C, Sym2.eq_swap] using
      (chain_edges_ne G g.left_adj g.right_adj g.first_ne_third).symm
  have hDU : D ≠ U := by
    simpa [D, U, Sym2.eq_swap] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.middle_two g.third_two
        r.end_three g.right_adj ha.symm
  have hDW : D ≠ W := by
    simpa [D, W, Sym2.eq_swap] using
      longPair_twoTwoEdge_ne_edgeEndingAtThree G g.middle_two g.third_two
        r.end_three g.right_adj hb.symm
  have hvalid₀ : IsOneTwoColoringOn G D₀ colour :=
    hvalid.mono G Set.sdiff_subset
  have hDfresh : D ∉ D₀ := by simp [D₀]
  have havailD : ColorAvailableOn G D₀ colour D (some c) := by
    simpa [Dset, D₀, Q, C, D, E] using
      longPair_forkThird_available_off_first_of_far_missing G
        (v₁ := v₁) (v₂ := v₂) (v₃ := v₃) (z := z)
        g colour c hC hE hc
  have hvalidD : IsOneTwoColoringOn G (insert D D₀) afterD := by
    simpa [afterD] using hvalid₀.extend_one G hDfresh havailD
  have hagreeD : ColoringsAgreeOff G ({D} : Set G.edgeSet) colour afterD := by
    simpa [afterD] using coloringsAgreeOff_recolor G colour D (some c)
  have huD : u ∉ (D : Sym2 V) := by
    intro hu
    have hcase : u = w₂ ∨ u = w₃ := by simpa [D] using hu
    exact hcase.elim
      (isThreeVertex_ne_isTwoVertex G h.start_three g.middle_two)
      (isThreeVertex_ne_isTwoVertex G h.start_three g.third_two)
  have hpalEq : ExternalInducedColors G colour u P =
      ExternalInducedColors G afterD u P := by
    apply externalInducedColors_eq_of_agreeOff G hagreeD
    intro e hext heS
    have hEq : e = D := by simpa using heS
    subst e
    exact huD hext.1
  have hlAfter : l ∉ ExternalInducedColors G afterD u P := by
    rw [← hpalEq]
    exact hl
  have hafterP : afterD P = none := by simp [afterD, hDP.symm, P, hP]
  have hafterC : afterD C = none := by simp [afterD, hDC.symm, C, hC]
  have hafterU : afterD U = none := by simp [afterD, hDU.symm, U, hU]
  have hafterW : afterD W ≠ some l := by
    simpa [afterD, hDW.symm, W] using hVl
  have hafterDavoid : afterD D ≠ some l := by simp [afterD, hcl]
  have havailQall : ColorAvailableOn G Dset afterD Q (some l) := by
    exact longPair_forkFirst_fresh_available_zeroThird G h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar afterD Dset l
      (by simpa [P] using hafterP) (by simpa [C] using hafterC)
      (by simpa [U] using hafterU) (by simpa [W] using hafterW)
      (by simpa [P] using hlAfter) (by simpa [D] using hafterDavoid)
      (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hsubset : insert D D₀ ⊆ Dset := by
    intro f hf
    rcases hf with rfl | hf₀
    · exact hDDset
    · exact hf₀.1
  have havailQ : ColorAvailableOn G (insert D D₀) afterD Q (some l) :=
    fun f hf hne ↦ havailQall f (hsubset hf) hne
  have hQfresh : Q ∉ insert D D₀ := by
    simp [D₀, hDQ.symm]
  have hvalidFinal : IsOneTwoColoringOn G (insert Q (insert D D₀)) final := by
    simpa [final] using hvalidD.extend_one G hQfresh havailQ
  have hcover : insert Q (insert D D₀) = Dset := by
    ext f
    constructor
    · intro hf
      rcases hf with rfl | rfl | hf₀
      · exact hQDset
      · exact hDDset
      · exact hf₀.1
    · intro hf
      by_cases hfQ : f = Q
      · exact Or.inl hfQ
      by_cases hfD : f = D
      · exact Or.inr (Or.inl hfD)
      · exact Or.inr (Or.inr ⟨hf, by simp [hfQ, hfD]⟩)
  rw [hcover] at hvalidFinal
  simpa [Dset, final, afterD] using hvalidFinal

/-- Saturation is unchanged when the two induced edges Q and D are given
new induced colours: both are witnessed by the unchanged matching edge C,
and no old matching witness can be Q or D. -/
theorem longPair_oneSaturated_recolor_forkFirstThird
    {u w₁ w₂ w₃ t : V}
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour) (c l : Fin 4)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ≠ none)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ≠ none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none) :
    OneSaturated G
      (recolor G
        (recolor G colour
          (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) (some c))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some l)) := by
  classical
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour D (some c)) Q (some l)
  have hDQ : D ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.middle_two g.third_two
      g.start_three g.right_adj g.first_adj.symm
  have hDC : D ≠ C := by
    simpa [D, C, Sym2.eq_swap] using
      (chain_edges_ne G g.left_adj g.right_adj g.first_ne_third).symm
  have hQC : Q ≠ C := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.first_two g.middle_two g.start_three g.left_adj g.first_adj.symm).symm
  have hfinalQ : final Q = some l := by simp [final]
  have hfinalD : final D = some c := by simp [final, hDQ]
  have hfinalC : final C = none := by
    simp [final, hDC.symm, hQC.symm, C, hC]
  have hfinalOff (e : G.edgeSet) (heD : e ≠ D) (heQ : e ≠ Q) :
      final e = colour e := by simp [final, heD, heQ]
  change OneSaturated G final
  intro e he
  by_cases heQ : e = Q
  · subst e
    exact ⟨C, hfinalC, w₁, by simp [Q], by simp [C]⟩
  by_cases heD : e = D
  · subst e
    exact ⟨C, hfinalC, w₂, by simp [D], by simp [C]⟩
  have heOld : colour e ≠ none := by
    intro heNone
    exact he ((hfinalOff e heD heQ).trans heNone)
  obtain ⟨f, hf, y, hye, hyf⟩ := hsat e heOld
  have hfQ : f ≠ Q := by
    intro hEq
    subst f
    exact hQ (by simpa [Q] using hf)
  have hfD : f ≠ D := by
    intro hEq
    subst f
    exact hD (by simpa [D] using hf)
  exact ⟨f, (hfinalOff f hfD hfQ).trans hf, y, hye, hyf⟩

/-- The only degree-two vertices whose induced palettes can change when Q
and D are recoloured are the four displayed internal vertices v₁,w₁,w₂,w₃. -/
theorem longPair_twoVertex_paletteAffectedBy_forkFirstThird_cases
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x q : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet),
        (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = v₁ ∨ q = w₁ ∨ q = w₂ ∨ q = w₃ := by
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, heS, y, hye, hqy⟩ := haffect
  have hecase : e = Q ∨ e = D := by simpa [Q, D] using heS
  rcases hecase with heQ | heD
  · subst e
    have haffectQ : PaletteAffectedBy G ({Q} : Set G.edgeSet) q := by
      rw [paletteAffectedBy_iff_inducedAffectedBy]
      exact ⟨Q, by simp, y, hye, hqy⟩
    rcases longThreeFork_twoVertex_paletteAffectedBy_forkFirst_cases G g hq
        (by simpa [Q] using haffectQ) with hqw₂ | hqu
    · exact Or.inr (Or.inr (Or.inl hqw₂))
    · have hqN : q ∈ G.neighborFinset u :=
        (G.mem_neighborFinset u q).mpr hqu.symm
      rw [longPair_neighborFinset_eq_three G h.start_three h.first_adj
        g.first_adj r.adj hv₁w₁ hv₁x hw₁x] at hqN
      have hqcase : q = v₁ ∨ q = w₁ ∨ q = x := by simpa using hqN
      rcases hqcase with hqv₁ | hqw₁ | hqx
      · exact Or.inl hqv₁
      · exact Or.inr (Or.inl hqw₁)
      · exact False.elim
          ((isThreeVertex_ne_isTwoVertex G r.end_three hq) hqx.symm)
  · subst e
    have haffectGap : PaletteAffectedBy G ({C, D} : Set G.edgeSet) q := by
      rw [paletteAffectedBy_iff_inducedAffectedBy]
      exact ⟨D, by simp, y, hye, hqy⟩
    rcases twoVertex_paletteAffectedBy_threeThread_gap G g hq
        (by simpa [C, D, Sym2.eq_swap] using haffectGap) with
      hqw₁ | hqw₂ | hqw₃
    · exact Or.inr (Or.inl hqw₁)
    · exact Or.inr (Or.inr (Or.inl hqw₂))
    · exact Or.inr (Or.inr (Or.inr hqw₃))

/-- Condition 2 for the simultaneous Q,D induced recolouring follows from
two unchanged visible matching edges at each of the four affected
degree-two vertices. -/
theorem longPair_conditionTwo_recolor_forkFirstThird
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (c l : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) (some c))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some l)) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let E : G.edgeSet := ⟨s(w₃, t), g.last_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour D (some c)) Q (some l)
  have hPDset : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hQDset : Q ∈ Dset := by simpa [Q, Dset] using hQD
  have hDDset : D ∈ Dset := by simpa [D, Dset] using hDD
  have hAD : A ∉ Dset := by
    simpa [A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hAP : A ≠ P := fun hEq ↦ hAD (hEq ▸ hPDset)
  have hAQ : A ≠ Q := fun hEq ↦ hAD (hEq ▸ hQDset)
  have hADedge : A ≠ D := fun hEq ↦ hAD (hEq ▸ hDDset)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hv₁w₁
  have hPD : P ≠ D := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.middle_two g.third_two h.start_three g.right_adj h.first_adj.symm).symm
  have hCQ : C ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      g.start_three g.left_adj g.first_adj.symm
  have hCD : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.left_adj g.right_adj g.first_ne_third
  have hED : E ≠ D := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.middle_two g.third_two g.end_three g.right_adj g.last_adj).symm
  have hEQ : E ≠ Q := by
    intro hEq
    have hval : s(w₃, t) = s(w₁, u) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hcase | hcase
    · exact g.first_ne_third hcase.1.symm
    · exact (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two)
        hcase.2
  have hCE : C ≠ E :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      g.end_three g.left_adj g.last_adj
  have hfinalP : final P = none := by simp [final, hPD, hPQ, P, hP]
  have hfinalA : final A = none := by
    simp [final, hADedge, hAQ, A, hA]
  have hfinalC : final C = none := by
    simp [final, hCD, hCQ, C, hC]
  have hfinalE : final E = none := by
    simp [final, hED, hEQ, E, hE]
  have hagree : ColoringsAgreeOff G ({Q, D} : Set G.edgeSet) colour final := by
    intro e he
    have hne : e ≠ Q ∧ e ≠ D := by simpa using he
    simp [final, hne.1, hne.2]
  change ConditionTwo G final
  apply hold.of_agreeOff G hagree
  intro q hq haffect _hmatch hall
  rcases longPair_twoVertex_paletteAffectedBy_forkFirstThird_cases G h g r
      hv₁w₁ hv₁x hw₁x hq (by simpa [Q, D] using haffect) with
    hqv₁ | hqw₁ | hqw₂ | hqw₃
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub
      h.first_two h.left_adj h.middle_two A P hAP
      hfinalA hfinalP
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [A]) (Or.inl rfl)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [P]) (Or.inl rfl)
    · exact hall

  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub
      g.first_two g.left_adj g.middle_two C P
      (by exact (longPair_twoTwoEdge_ne_edgeEndingAtThree G
        g.first_two g.middle_two h.start_three g.left_adj h.first_adj.symm))
      hfinalC hfinalP
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [C]) (Or.inl rfl)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [P]) (Or.inr g.first_adj.symm)
    · exact hall
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub
      g.middle_two g.left_adj.symm g.first_two C E hCE
      hfinalC hfinalE
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [C]) (Or.inl rfl)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [E]) (Or.inr g.right_adj)
    · exact hall
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub
      g.third_two g.right_adj.symm g.middle_two C E hCE
      hfinalC hfinalE
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [C]) (Or.inr g.right_adj.symm)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [E]) (Or.inl rfl)
    · exact hall

/-- Condition 3 for the simultaneous induced recolouring.  Recolour Q
using the established first-edge lemma; the additional change on internal
edge D cannot be external to a 2-thread endpoint. -/
theorem longPair_conditionThree_recolor_forkFirstThird
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (c l : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    ConditionThree G
      (recolor G
        (recolor G colour
          (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) (some c))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some l)) := by
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let afterQ : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some l)
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour D (some c)) Q (some l)
  have hDQ : D ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.middle_two g.third_two
      g.start_three g.right_adj g.first_adj.symm
  have hthreeQ : ConditionThree G afterQ := by
    exact longThreeFork_conditionThree_recolor_forkFirst_induced G h g
      colour hold l hP hPQ
  have hagree : ColoringsAgreeOff G ({D} : Set G.edgeSet) afterQ final := by
    intro e he
    have heD : e ≠ D := by simpa using he
    by_cases heQ : e = Q
    · subst e
      simp [afterQ, final]
    · simp [afterQ, final, heD, heQ, hDQ]
  change ConditionThree G final
  apply hthreeQ.of_agreeOff G hagree
  intro a b p hp haffect
  exfalso
  apply not_threadConditionAffectedBy_threeThread_gap G g p hp
  rcases haffect with haffect | haffect
  · left
    obtain ⟨e, heD, hext⟩ := haffect
    refine ⟨e, ?_, hext⟩
    have heq : e = D := by simpa using heD
    subst e
    simp [D, Sym2.eq_swap]
  · right
    obtain ⟨e, heD, hext⟩ := haffect
    refine ⟨e, ?_, hext⟩
    have heq : e = D := by simpa using heD
    subst e
    simp [D, Sym2.eq_swap]

/-- The complete prepared-gap package for the paper's last-edge matching
subcase.  The first edge Q receives the fresh colour `l`, while the third
edge D receives a colour `c` missing at the far endpoint. -/
theorem longPair_prepared_recolor_forkFirstThird
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (c l : Fin 4) (hcl : c ≠ l)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ≠ none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ≠ none)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) = none)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hVl : colour (⟨s(x, b), hb⟩ : G.edgeSet) ≠ some l)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hl : l ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hc : c ∉ ExternalInducedColors G colour t
      (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet))
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    PreparedThreeThreadGap G h
      (recolor G
        (recolor G colour
          (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) (some c))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some l)) := by
  exact ⟨
    longPair_validOn_recolor_forkFirstThird G h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour hprepared.1 c l hcl
      hP hC hE hU hVl hl hc hQD hDD,
    longPair_oneSaturated_recolor_forkFirstThird G g colour
      hprepared.2.1 c l hQ hD hC,
    longPair_conditionTwo_recolor_forkFirstThird G hsub h g r
      hv₁w₁ hv₁x hw₁x colour hprepared.2.2.1 c l hP hA hC hE hQD hDD,
    longPair_conditionThree_recolor_forkFirstThird G h g colour
      hprepared.2.2.2 c l hP hPQ⟩

/-- Three distinct colours cannot all lie in a palette of size at most two. -/
theorem exists_mem_three_not_mem_of_ncard_le_two
    (i j m : Fin 4) (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m)
    (S : Set (Fin 4)) (hS : S.ncard ≤ 2) :
    ∃ c : Fin 4, c ∈ ({i, j, m} : Set (Fin 4)) ∧ c ∉ S := by
  classical
  by_contra hn
  push_neg at hn
  have hsub : ({i, j, m} : Set (Fin 4)) ⊆ S := by
    intro c hc
    exact hn c hc
  have hcard := Set.ncard_le_ncard hsub
  have hthree : ({i, j, m} : Set (Fin 4)).ncard = 3 := by
    simp [hij, him, hjm]
  rw [hthree] at hcard
  omega

/-- Close the last-edge matching branch of no330 once the colour `c`
missing at the far endpoint has been chosen.  This is the paper's
simultaneous recolouring `Q : i ↦ l`, `D : l ↦ c`, followed by the
crossed filling of the selected gap. -/
theorem longPair_hasGoodFour_of_zeroThread_last_matching_of_far_choice
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b) (hbu : b ≠ u)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m l c : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) = some l)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hVD : (⟨s(x, b), hb⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzQ : z ∉ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet).1)
    (hlPair : l ∉ ({i, j} : Set (Fin 4))) (hlm : l ≠ m)
    (hcl : c ≠ l)
    (hc : c ∉ ExternalInducedColors G colour t
      (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet)) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let Vedge : G.edgeSet := ⟨s(x, b), hb⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let E : G.edgeSet := ⟨s(w₃, t), g.last_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour D (some c)) Q (some l)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hv₁w₁
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hv₁x
  have hQT : Q ≠ T := by
    simpa [Q, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      g.first_adj r.adj hw₁x
  have hPDset : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hQDset : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hTDset : T ∈ Dset := by simpa [Dset, T] using hTD
  have hVDset : Vedge ∈ Dset := by simpa [Dset, Vedge] using hVD
  have hDDset : D ∈ Dset := by simpa [Dset, D] using hDD
  have hvalid : IsOneTwoColoringOn G Dset colour := by
    simpa [Dset] using hprepared.1
  have hij : i ≠ j := by
    intro hij
    subst j
    have hp := hvalid Q hQDset T hTDset hQT
    have hsep : InducedSeparated G Q T := by
      simpa [Q, T, hQ, hT] using hp
    exact hsep.1 u (by simp [Q]) (by simp [T])
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
    have hp := hvalid Q hQDset Vedge hVDset hQV
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
    have hp := hvalid T hTDset Vedge hVDset hTV
    have hsep : InducedSeparated G T Vedge := by
      simpa [T, Vedge, hT, hV] using hp
    exact hsep.1 x (by simp [T]) (by simp [Vedge])
  have hLold : ExternalInducedColors G colour u P = {i, j} := by
    simpa [P, Q, T] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        h.first_adj g.first_adj r.adj hv₁w₁ hv₁x hw₁x colour i j
        hP hQ hT
  have hlOld : l ∉ ExternalInducedColors G colour u P := by
    rw [hLold]
    exact hlPair
  have hlData : l ≠ i ∧ l ≠ j := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hlPair
  have hVl : colour Vedge ≠ some l := by
    simpa [Vedge, hV] using hlm.symm
  have hpreparedFinal : PreparedThreeThreadGap G h final := by
    exact longPair_prepared_recolor_forkFirstThird G hsub h g r
      hv₁w₁ hv₁x hw₁x ha hb hNfar colour hprepared c l hcl
      hP (by simpa [Q, hQ]) hC (by simpa [D, hD]) hE hU
      (by simpa [Vedge] using hVl) hA (by simpa [P] using hlOld) hc hQD hDD
      (by simpa [P, Q] using hPQ)
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAQ : A ≠ Q := fun heq ↦ hAD (heq ▸ hQDset)
  have hADedge : A ≠ D := fun heq ↦ hAD (heq ▸ hDDset)
  have hBQ : B ≠ Q := fun heq ↦ hBD (heq ▸ hQDset)
  have hBDedge : B ≠ D := fun heq ↦ hBD (heq ▸ hDDset)
  have hPD : P ≠ D := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.middle_two g.third_two h.start_three g.right_adj h.first_adj.symm).symm
  have hRD : R ≠ D := (longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.middle_two g.third_two h.end_three g.right_adj h.last_adj).symm
  have hDT : D ≠ T := longPair_twoTwoEdge_ne_edgeEndingAtThree G
    g.middle_two g.third_two r.start_three g.right_adj r.adj.symm
  have hRQ : R ≠ Q := by
    intro heq
    apply hzQ
    have hzR : z ∈ (R : Sym2 V) := by simp [R]
    rw [heq] at hzR
    exact hzR
  have hfinalP : final P = none := by simp [final, hPD, hPQ, P, hP]
  have hfinalR : final R = none := by simp [final, hRD, hRQ, R, hR]
  have hfinalA : final A = none := by
    simp [final, hADedge, hAQ, A, hA]
  have hfinalB : final B = none := by
    simp [final, hBDedge, hBQ, B, hB]
  have hfinalQ : final Q = some l := by simp [final]
  have hfinalT : final T = some j := by
    simp [final, hDT.symm, hQT.symm, T, hT]
  have hLfinal : ExternalInducedColors G final u P = {l, j} := by
    simpa [P, Q, T] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        h.first_adj g.first_adj r.adj hv₁w₁ hv₁x hw₁x final l j
        (by simpa [P] using hfinalP) (by simpa [Q] using hfinalQ)
        (by simpa [T] using hfinalT)
  have hagree : ColoringsAgreeOff G ({Q, D} : Set G.edgeSet) colour final := by
    intro e he
    have hne : e ≠ Q ∧ e ≠ D := by simpa using he
    simp [final, hne.1, hne.2]
  have hzD : z ∉ (D : Sym2 V) := by
    intro hz
    have hzcase : z = w₂ ∨ z = w₃ := by simpa [D] using hz
    exact hzcase.elim
      (isThreeVertex_ne_isTwoVertex G h.end_three g.middle_two)
      (isThreeVertex_ne_isTwoVertex G h.end_three g.third_two)
  have hRunchanged : ExternalInducedColors G colour z R =
      ExternalInducedColors G final z R := by
    apply externalInducedColors_eq_of_agreeOff G hagree
    intro e hext heS
    have hcase : e = Q ∨ e = D := by simpa using heS
    exact hcase.elim
      (fun heq ↦ by subst e; exact hzQ hext.1)
      (fun heq ↦ by subst e; exact hzD hext.1)
  have hRfinal : ExternalInducedColors G final z R = {i, j} := by
    calc
      ExternalInducedColors G final z R =
          ExternalInducedColors G colour z R := hRunchanged.symm
      _ = ExternalInducedColors G colour u P := hpal.symm
      _ = {i, j} := hLold
  apply longPair_hasGoodFour_of_prepared_cross_fill G hsub h final
    hpreparedFinal i l m hfinalA hfinalB hfinalP hfinalR
  · rw [hLfinal]
    simp [hlData.1.symm, hij]
  · rw [hRfinal]
    exact hlPair
  · rw [hRfinal]
    simp
  · rw [hLfinal]
    simp
  · rw [hLfinal]
    simp [hmi, hmj, hlm.symm]
  · rw [hRfinal]
    simp [hmi, hmj, hlm.symm]

/-- The self-contained last-edge matching branch.  The required replacement
colour on D is selected by pigeonhole from the three already displayed
colours `i,j,m`; the far palette at t has exactly two colours. -/
theorem longPair_hasGoodFour_of_zeroThread_last_matching
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
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
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) = some l)
    (hE : colour (⟨s(w₃, t), g.last_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hVD : (⟨s(x, b), hb⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hincT : ∀ e : G.edgeSet, t ∈ (e : Sym2 V) →
      e ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzQ : z ∉ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet).1)
    (hlPair : l ∉ ({i, j} : Set (Fin 4))) (hlm : l ≠ m) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let Vedge : G.edgeSet := ⟨s(x, b), hb⟩
  let E : G.edgeSet := ⟨s(w₃, t), g.last_adj⟩
  have hQDset : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hTDset : T ∈ Dset := by simpa [Dset, T] using hTD
  have hVDset : Vedge ∈ Dset := by simpa [Dset, Vedge] using hVD
  have hvalid : IsOneTwoColoringOn G Dset colour := by
    simpa [Dset] using hprepared.1
  have hQT : Q ≠ T := by
    simpa [Q, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      g.first_adj r.adj hw₁x
  have hij : i ≠ j := by
    intro hij
    subst j
    have hp := hvalid Q hQDset T hTDset hQT
    have hsep : InducedSeparated G Q T := by
      simpa [Q, T, hQ, hT] using hp
    exact hsep.1 u (by simp [Q]) (by simp [T])
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
    have hp := hvalid Q hQDset Vedge hVDset hQV
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
    have hp := hvalid T hTDset Vedge hVDset hTV
    have hsep : InducedSeparated G T Vedge := by
      simpa [T, Vedge, hT, hV] using hp
    exact hsep.1 x (by simp [T]) (by simp [Vedge])
  have hfarCard : (ExternalInducedColors G colour t E).ncard = 2 := by
    exact longPair_externalInducedColors_ncard_eq_two_of_validOn_matching G
      Dset g.end_three colour hvalid
      (by simpa [Dset] using hincT) E (by simp [E]) (by simpa [E] using hE)
  obtain ⟨c, hcTriple, hcFar⟩ :=
    exists_mem_three_not_mem_of_ncard_le_two i j m hij hmi.symm hmj.symm
      (ExternalInducedColors G colour t E) (by omega)
  have hcl : c ≠ l := by
    intro hEq
    subst c
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcTriple
    rcases hcTriple with hli | hlj | hlm'
    · exact hlPair (by simp [hli])
    · exact hlPair (by simp [hlj])
    · exact hlm hlm'
  exact longPair_hasGoodFour_of_zeroThread_last_matching_of_far_choice G hsub h g r
    hv₁w₁ hv₁x hw₁x ha hb hbu hNfar colour hprepared i j m l c
    hP hR hQ hT hU hV hA hB hC hD hE hQD hTD hVD hDD hpal hzQ
    hlPair hlm hcl (by simpa [E] using hcFar)

/-- Complete the entire branch in which exactly one displayed far edge of
the zero-thread is matching.  If D avoids the fourth colour we use the
one-edge recolouring; otherwise D carries that colour and the final edge E
is split into the matching and induced paper subcases. -/
theorem longPair_hasGoodFour_of_zeroThread_far_matching
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b) (hbu : b ≠ u)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hVD : (⟨s(x, b), hb⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hincT : ∀ e : G.edgeSet, t ∈ (e : Sym2 V) →
      e ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzQ : z ∉ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet).1) :
    HasGoodFour G := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let E : G.edgeSet := ⟨s(w₃, t), g.last_adj⟩
  by_cases hDavoid : ∀ l : Fin 4,
      l ∉ ({i, j} : Set (Fin 4)) → l ≠ m → colour D ≠ some l
  · exact longPair_hasGoodFour_of_zeroThread_far_matching_of_middle_avoids G
      hsub h g r hv₁w₁ hv₁x hw₁x ha hb hbu hNfar colour hprepared
      i j m hP hR hQ hT hU hV hA hB hC hQD hTD hVD hpal hzQ
      (by simpa [D] using hDavoid)
  · push_neg at hDavoid
    obtain ⟨l, hlPair, hlm, hD⟩ := hDavoid
    have hPQ : P ≠ Q := by
      simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
        h.first_adj g.first_adj hv₁w₁
    have hRP : R ≠ P := by
      intro heq
      have hval : s(v₃, z) = s(v₁, u) := congrArg Subtype.val heq
      simp only [Sym2.eq_iff] at hval
      rcases hval with hsame | hswap
      · exact h.first_ne_third hsame.1.symm
      · exact (isThreeVertex_ne_isTwoVertex G h.start_three h.third_two)
          hswap.1.symm
    have hRQ : R ≠ Q := by
      intro heq
      apply hzQ
      have hzR : z ∈ (R : Sym2 V) := by simp [R]
      rw [heq] at hzR
      exact hzR
    have hLold : ExternalInducedColors G colour u P = {i, j} := by
      simpa [P, Q, T] using
        longPair_externalPalette_eq_pair_three_neighbors G h.start_three
          h.first_adj g.first_adj r.adj hv₁w₁ hv₁x hw₁x colour i j
          hP hQ hT
    have hlOld : l ∉ ExternalInducedColors G colour u P := by
      rw [hLold]
      exact hlPair
    by_cases hEmatch : colour E = none
    · exact longPair_hasGoodFour_of_zeroThread_last_matching G hsub h g r
        hv₁w₁ hv₁x hw₁x ha hb hbu hNfar colour hprepared i j m l
        hP hR hQ hT hU hV hA hB hC (by simpa [D] using hD)
        (by simpa [E] using hEmatch) hQD hTD hVD hDD hincT hpal hzQ
        hlPair hlm
    · exact longPair_hasGoodFour_of_forkMiddle_terminal_shift G hsub h g
        colour hprepared i l hP hR hQ hC (by simpa [D] using hD)
        (by simpa [E] using hEmatch) hA hB hQD hCD hDD
        (by simpa [P, Q] using hPQ) (by simpa [R, P] using hRP)
        (by simpa [R, Q] using hRQ) (by simpa [P] using hlOld)

/-- The full local hard completion for no330.  It classifies the two far
edges of the zero-thread.  Two induced edges give the direct swap; exactly
one matching edge is oriented and sent to
`longPair_hasGoodFour_of_zeroThread_far_matching`; two matching edges
contradict packing validity at their common endpoint. -/
theorem longPair_hasGoodFour_of_zeroThread_hard
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ZeroThreadCore G u x)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x : v₁ ≠ x) (hw₁x : w₁ ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUD : (⟨s(x, a), ha⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hVD : (⟨s(x, b), hb⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hincT : ∀ e : G.edgeSet, t ∈ (e : Sym2 V) →
      e ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzQ : z ∉ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet).1) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let Vedge : G.edgeSet := ⟨s(x, b), hb⟩
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hv₁x
  cases hUc : colour U with
  | none =>
      cases hVc : colour Vedge with
      | none =>
          have hUV : U ≠ Vedge := by
            intro heq
            have hval : s(x, a) = s(x, b) := congrArg Subtype.val heq
            simp only [Sym2.eq_iff] at hval
            rcases hval with hsame | hswap
            · exact hab hsame.2
            · exact hb.ne hswap.1
          have hvalid : IsOneTwoColoringOn G Dset colour := by
            simpa [Dset] using hprepared.1
          have hp := hvalid U (by simpa [Dset, U] using hUD)
            Vedge (by simpa [Dset, Vedge] using hVD) hUV
          have hsep : EndpointDisjoint G U Vedge := by
            simpa [hUc, hVc] using hp
          exact False.elim (hsep x (by simp [U]) (by simp [Vedge]))
      | some m =>
          exact longPair_hasGoodFour_of_zeroThread_far_matching G hsub h g r
            hv₁w₁ hv₁x hw₁x ha hb hbu hNfar colour hprepared i j m
            hP hR hQ hT (by simpa [U] using hUc) (by simpa [Vedge] using hVc)
            hA hB hC hQD hTD hVD hCD hDD hincT hpal hzQ
  | some m =>
      cases hVc : colour Vedge with
      | none =>
          have hNswap : G.neighborFinset x = {u, b, a} := by
            simpa [Finset.pair_comm] using hNfar
          exact longPair_hasGoodFour_of_zeroThread_far_matching G hsub h g r
            hv₁w₁ hv₁x hw₁x hb ha hau hNswap colour hprepared i j m
            hP hR hQ hT (by simpa [Vedge] using hVc) (by simpa [U] using hUc)
            hA hB hC hQD hTD hUD hCD hDD hincT hpal hzQ
      | some n =>
          exact longPair_hasGoodFour_of_zeroThread_hard_of_far_both_induced G
            hsub h g r hv₁w₁ hv₁x hw₁x ha hb hNfar colour hprepared j
            hP hR hT (by simp [U, hUc]) (by simp [Vedge, hVc])
            hA hB hC hTD (by simpa [P, T] using hPT)

/-- Kernel-level reduction of the paper's `no330` configuration.  A good
colouring after deleting the middle vertex of the selected 3-thread extends
to the original graph, contradicting badness, whenever a distinct 3-thread
and a distinct 0-thread form the other two arms. -/
theorem longPair_no_threeThreeZero_of_smaller_good
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t x : V} {p : G.Walk u z} {q : G.Walk u t}
    {r : G.Walk u x}
    (hp : IsKThread G p 3) (hq : IsKThread G q 3)
    (hr : IsKThread G r 0)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) : False := by
  classical
  let h := hp.threeThreadCore G
  let g := hq.threeThreadCore G
  let rCore := hr.zeroThreadCore G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le (p.getVert 2)) small
  let Dset : Set G.edgeSet :=
    RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
  let P : G.edgeSet := ⟨s(p.getVert 1, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(p.getVert 3, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(q.getVert 1, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x, u), rCore.adj.symm⟩
  let A : G.edgeSet := ⟨s(p.getVert 1, p.getVert 2), h.left_adj⟩
  let B : G.edgeSet := ⟨s(p.getVert 3, p.getVert 2), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(q.getVert 1, q.getVert 2), g.left_adj⟩
  let D : G.edgeSet := ⟨s(q.getVert 2, q.getVert 3), g.right_adj⟩
  have hpLen : p.length = 4 := by simpa using hp.length
  have hqLen : q.length = 4 := by simpa using hq.length
  have hrLen : r.length = 1 := by simpa using hr.length
  have hrEnd : r.getVert 1 = x := by
    rw [← hrLen]
    exact r.getVert_length
  have hv₁x : p.getVert 1 ≠ x := by simpa [hrEnd] using hpr
  have hw₁x : q.getVert 1 ≠ x := by simpa [hrEnd] using hqr
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
  have hqFar₁ : q.getVert 1 ≠ p.getVert 2 ∧
      ¬ G.Adj (q.getVert 1) (p.getVert 2) := by
    simpa [hqLen] using
      (longPair_short_path_endpoint_far_from_threeThread_middle G hgirth hp
        (hq.1.take 1) (by simp [hqLen]) (by simpa [hqLen] using hpq))
  have hqFar₂ : q.getVert 2 ≠ p.getVert 2 ∧
      ¬ G.Adj (q.getVert 2) (p.getVert 2) := by
    simpa [hqLen] using
      (longPair_short_path_endpoint_far_from_threeThread_middle G hgirth hp
        (hq.1.take 2) (by simp [hqLen]) (by simpa [hqLen] using hpq))
  have hqFar₃ : q.getVert 3 ≠ p.getVert 2 ∧
      ¬ G.Adj (q.getVert 3) (p.getVert 2) := by
    simpa [hqLen] using
      (longPair_short_path_endpoint_far_from_threeThread_middle G hgirth hp
        (hq.1.take 3) (by simp [hqLen]) (by simpa [hqLen] using hpq))
  have htFar : t ≠ p.getVert 2 ∧ ¬ G.Adj t (p.getVert 2) := by
    simpa [hqLen] using
      (longPair_short_path_endpoint_far_from_threeThread_middle G hgirth hp
        hq.1 (by omega) hpq)
  have hxFar : x ≠ p.getVert 2 ∧ ¬ G.Adj x (p.getVert 2) := by
    simpa [hrEnd, hrLen] using
      (longPair_short_path_endpoint_far_from_threeThread_middle G hgirth hp
        hr.1 (by omega) hpr)
  obtain ⟨a, b, hab, hau, hbu, hxa, hxb, hNfar⟩ :=
    ZeroThreadCore.exists_far_neighbors G rCore
  let ra : G.Walk u a := .cons rCore.adj (.cons hxa .nil)
  have hra : ra.IsPath := by
    apply (Walk.IsPath.of_adj hxa).cons
    simp [rCore.adj.ne, hau.symm]
  let rb : G.Walk u b := .cons rCore.adj (.cons hxb .nil)
  have hrb : rb.IsPath := by
    apply (Walk.IsPath.of_adj hxb).cons
    simp [rCore.adj.ne, hbu.symm]
  have haFar : a ≠ p.getVert 2 ∧ ¬ G.Adj a (p.getVert 2) := by
    exact longPair_short_path_endpoint_far_from_threeThread_middle G hgirth hp
      hra (by simp [ra]) (by simpa [ra] using hv₁x)
  have hbFar : b ≠ p.getVert 2 ∧ ¬ G.Adj b (p.getVert 2) := by
    exact longPair_short_path_endpoint_far_from_threeThread_middle G hgirth hp
      hrb (by simp [rb]) (by simpa [rb] using hv₁x)
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, hpGetNe 2 1 (by omega) (by omega) (by omega), hu₂.symm]
  have hQD : Q ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      hu₂ hnotU₂ Q (by simp [Q])
  have hTD : T ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      hu₂ hnotU₂ T (by simp [T])
  have hCD : C ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = q.getVert 1 ∨
        p.getVert 2 = q.getVert 2 := by simpa [C] using hmem
    exact hcase.elim (fun he ↦ hqFar₁.1 he.symm)
      (fun he ↦ hqFar₂.1 he.symm)
  have hDD : D ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = q.getVert 2 ∨
        p.getVert 2 = q.getVert 3 := by simpa [D] using hmem
    exact hcase.elim (fun he ↦ hqFar₂.1 he.symm)
      (fun he ↦ hqFar₃.1 he.symm)
  let U : G.edgeSet := ⟨s(x, a), hxa⟩
  let Vedge : G.edgeSet := ⟨s(x, b), hxb⟩
  have hUD : U ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = x ∨ p.getVert 2 = a := by
      simpa [U] using hmem
    exact hcase.elim (fun he ↦ hxFar.1 he.symm)
      (fun he ↦ haFar.1 he.symm)
  have hVD : Vedge ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = x ∨ p.getVert 2 = b := by
      simpa [Vedge] using hmem
    exact hcase.elim (fun he ↦ hxFar.1 he.symm)
      (fun he ↦ hbFar.1 he.symm)
  have hincT : ∀ e : G.edgeSet, t ∈ (e : Sym2 V) → e ∈ Dset := by
    intro e hte
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      htFar.1 htFar.2 e hte
  obtain ⟨hP, hR, hpal⟩ :=
    longPair_threeThread_hard_normal_form_of_no_goodFour G hgirth h small
      hsmall hsub hbad
  have hC := longPair_fork_second_matching_in_bad_graph G hgirth hp hq hpq
    small hsmall hsub hbad
  have hprepared : PreparedThreeThreadGap G h base := by
    exact preparedThreeThreadGap_of_goodFour G hsub h small hsmall
  have hAD : A ∉ Dset := by
    simpa [Dset, A, h] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B, h, Sym2.eq_swap] using
      right_chain_edge_not_retained G h.right_adj
  have hA : base A = none := by
    have hAe : A.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [RetainedEdges, Dset] using hAD
    simp [base, transportColoringToSupergraph, hAe]
  have hB : base B = none := by
    have hBe : B.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [RetainedEdges, Dset] using hBD
    simp [base, transportColoringToSupergraph, hBe]
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hpq
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj rCore.adj hv₁x
  have hQT : Q ≠ T := by
    simpa [Q, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      g.first_adj rCore.adj hw₁x
  have hvalid : IsOneTwoColoringOn G Dset base := by
    simpa [Dset] using hprepared.1
  have hQne : base Q ≠ none := by
    intro hQnone
    have hpqValid := hvalid P hPD Q hQD hPQ
    have hdisj : EndpointDisjoint G P Q := by
      simpa [P, Q, base, hP, hQnone] using hpqValid
    exact hdisj u (by simp [P]) (by simp [Q])
  have hTne : base T ≠ none := by
    intro hTnone
    have hptValid := hvalid P hPD T hTD hPT
    have hdisj : EndpointDisjoint G P T := by
      simpa [P, T, base, hP, hTnone] using hptValid
    exact hdisj u (by simp [P]) (by simp [T])
  have hzQ : z ∉ (Q : Sym2 V) := by
    intro hz
    have hzcase : z = q.getVert 1 ∨ z = u := by simpa [Q] using hz
    rcases hzcase with hzq | hzu
    · exact (isThreeVertex_ne_isTwoVertex G hp.end_three g.first_two) hzq
    · apply hpGetNe 4 0 (by omega) (by omega) (by omega)
      simpa [hpEnd] using hzu
  cases hQval : base Q with
  | none => exact False.elim (hQne hQval)
  | some i =>
      cases hTval : base T with
      | none => exact False.elim (hTne hTval)
      | some j =>
          apply hbad
          exact longPair_hasGoodFour_of_zeroThread_hard G hsub h g rCore
            hpq hv₁x hw₁x hxa hxb hab hau hbu hNfar base hprepared i j
            (by simpa [h, base, P] using hP)
            (by simpa [h, base, R] using hR)
            (by simpa [g, Q] using hQval)
            (by simpa [rCore, T] using hTval)
            (by simpa [h, A] using hA) (by simpa [h, B] using hB)
            (by simpa [g, base, C] using hC)
            (by simpa [g, Q, Dset] using hQD)
            (by simpa [rCore, T, Dset] using hTD)
            (by simpa [U, Dset] using hUD)
            (by simpa [Vedge, Dset] using hVD)
            (by simpa [g, C, Dset] using hCD)
            (by simpa [g, D, Dset] using hDD)
            (by simpa [g, Dset] using hincT)
            (by simpa [h, base, P, R] using hpal)
            (by simpa [g, Q] using hzQ)

end Finite

end

end LeanCo.PackingEdgeColoring
