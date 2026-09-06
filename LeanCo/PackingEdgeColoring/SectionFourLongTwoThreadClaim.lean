import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeThree
import LeanCo.PackingEdgeColoring.SectionFourLeafC3Choice

/-!
# The two-thread part of Claim 4.5

This file isolates the neighbour-arm swap used when the selected
three-thread `u-v₁-v₂-v₃-z` is accompanied by a two-thread
`u-w₁-w₂-t`.  The first layer proves that moving the induced colour of
`uw₁` to `uv₁`, and making `uw₁` matching, preserves validity,
maximality of the matching class, and Condition 2.  For Condition 3 there
is exactly one possible obstruction: the two orientations of the displayed
two-thread itself.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Ordered data carried by a two-thread `u-w₁-w₂-t`. -/
structure TwoThreadCoreData (u w₁ w₂ t : V) : Prop where
  start_three : IsThreeVertex G u
  end_three : IsThreeVertex G t
  first_two : IsTwoVertex G w₁
  second_two : IsTwoVertex G w₂
  first_adj : G.Adj u w₁
  middle_adj : G.Adj w₁ w₂
  last_adj : G.Adj w₂ t
  second_ne_start : w₂ ≠ u
  first_ne_end : w₁ ≠ t

/-- Extract the ordered four-vertex core from a certified two-thread. -/
theorem IsKThread.twoThreadCoreData {u t : V} {q : G.Walk u t}
    (hq : IsKThread G q 2) :
    TwoThreadCoreData G u (q.getVert 1) (q.getVert 2) t := by
  have hlen : q.length = 3 := by simpa using hq.length
  have hget (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 3) (hij : i ≠ j) :
      q.getVert i ≠ q.getVert j := by
    intro heq
    have hinj := hq.1.getVert_injOn
      (show i ∈ {r : ℕ | r ≤ q.length} by simpa [hlen] using hi)
      (show j ∈ {r : ℕ | r ≤ q.length} by simpa [hlen] using hj)
      heq
    exact hij hinj
  have hend : q.getVert 3 = t := by
    rw [← hlen]
    exact q.getVert_length
  refine ⟨hq.start_three, hq.end_three,
    IsKThread.internal_two G hq (by omega) (by omega),
    IsKThread.internal_two G hq (by omega) (by omega),
    hq.first_step_adj, q.adj_getVert_succ (i := 1) (by omega),
    ?_, ?_, ?_⟩
  · simpa [hend] using q.adj_getVert_succ (i := 2) (by omega)
  · simpa using hget 2 0 (by omega) (by omega) (by omega)
  · simpa [hend] using hget 1 3 (by omega) (by omega) (by omega)

/-- Saturation makes the last edge of a two-thread matching if its first
two edges are induced-coloured. -/
theorem longPair_twoThread_last_matching_of_first_two_induced
    {u w₁ w₂ t : V} (g : TwoThreadCoreData G u w₁ w₂ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ≠ none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ none) :
    colour (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) = none := by
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, t), g.last_adj⟩
  obtain ⟨f, hf, y, hyC, hyf⟩ := hsat C (by simpa [C] using hC)
  have hycase : y = w₁ ∨ y = w₂ := by simpa [C] using hyC
  rcases hycase with hyw₁ | hyw₂
  · have hw₁f : w₁ ∈ (f : Sym2 V) := by simpa [hyw₁] using hyf
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start f hw₁f with hfC | hfQ
    · have hfeq : f = C := Subtype.ext (by simpa [C] using hfC)
      exact False.elim (hC (by simpa [C, hfeq] using hf))
    · have hfeq : f = Q := Subtype.ext (by simpa [Q] using hfQ)
      exact False.elim (hQ (by simpa [Q, hfeq] using hf))
  · have hw₂f : w₂ ∈ (f : Sym2 V) := by simpa [hyw₂] using hyf
    rcases edge_eq_left_or_right_of_incident_two G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end f hw₂f with hfC | hfD
    · have hfeq : f = C := Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC)
      exact False.elim (hC (by simpa [C, hfeq] using hf))
    · have hfeq : f = D := Subtype.ext (by simpa [D] using hfD)
      simpa [D, hfeq] using hf

/-- The new matching edge on the two-thread arm is disjoint from every
unchanged retained matching edge. -/
theorem longPair_endpointDisjoint_twoThreadFirst_of_selectedOuter
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ none)
    (f : G.edgeSet)
    (hfD : f ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hfP : f ≠ (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hfQ : f ≠ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hf : colour f = none) :
    EndpointDisjoint G
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) f := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  have hPD : P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hPf := hvalid P hPD f hfD (by simpa [P] using hfP.symm)
  have hPdisj : EndpointDisjoint G P f := by
    simpa [P, hP, hf] using hPf
  intro x hx hxf
  have hxcase : x = w₁ ∨ x = u := by simpa [Q] using hx
  rcases hxcase with hxw₁ | hxu
  · rcases edge_eq_left_or_right_of_incident_two G g.first_two
      g.first_adj.symm g.middle_adj g.second_ne_start.symm f
      (by simpa [hxw₁] using hxf) with hfQ' | hfC
    · exact hfQ (Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfQ'))
    · apply hC
      have hfeq : f = C := Subtype.ext (by simpa [C] using hfC)
      simpa [hfeq] using hf
  · exact hPdisj u (by simp [P]) (by simpa [hxu] using hxf)

/-- The selected-outer/two-thread-first swap preserves pairwise colour
compatibility on the retained edge set. -/
theorem longPair_validOn_swap_selectedOuter_twoThreadFirst
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (a : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G)
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hnewP : new P = some a := by simp [new, hPQ']
  have hnewQ : new Q = none := by simp [new]
  have hnewOff (f : G.edgeSet) (hfP : f ≠ P) (hfQ : f ≠ Q) :
      new f = colour f := by simp [new, hfP, hfQ]
  have hPD : P ∈ D := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hPcross (f : G.edgeSet) (hfD : f ∈ D)
      (hfP : f ≠ P) (hfQ : f ≠ Q) :
      PairCompatible G P f (some a) (colour f) := by
    cases hcf : colour f with
    | none => exact pairCompatible_of_ne G (by simp)
    | some j =>
        by_cases haj : a = j
        · subst j
          have hp := hvalid Q (by simpa [D, Q] using hQD) f hfD hfQ.symm
          have hsepQ : InducedSeparated G Q f := by
            simpa [Q, hQ, hcf] using hp
          have hsepP := longPair_inducedSeparated_selectedOuter_of_fork G h Q f
            (by simp [Q]) (by simpa [D] using hfD) (by simpa [P] using hfP)
            hsepQ
          simpa [P, hcf] using hsepP
        · exact pairCompatible_of_ne G (by simp [hcf, haj])
  have hQcross (f : G.edgeSet) (hfD : f ∈ D)
      (hfP : f ≠ P) (hfQ : f ≠ Q) :
      PairCompatible G Q f none (colour f) := by
    cases hcf : colour f with
    | none =>
        have hdisj := longPair_endpointDisjoint_twoThreadFirst_of_selectedOuter
          G h g colour (by simpa [D] using hvalid) (by simpa [P] using hP)
          hC f (by simpa [D] using hfD) (by simpa [P] using hfP)
          (by simpa [Q] using hfQ) hcf
        simpa [Q, hcf] using hdisj
    | some j => exact pairCompatible_of_ne G (by simp [hcf])
  change IsOneTwoColoringOn G D new
  intro e heD f hfD hef
  by_cases heP : e = P
  · subst e
    by_cases hfQ : f = Q
    · subst f
      rw [hnewP, hnewQ]
      exact pairCompatible_of_ne G (by simp)
    · have hfP : f ≠ P := by simpa using hef.symm
      rw [hnewP, hnewOff f hfP hfQ]
      exact hPcross f hfD hfP hfQ
  · by_cases heQ : e = Q
    · subst e
      by_cases hfP : f = P
      · subst f
        rw [hnewQ, hnewP]
        exact pairCompatible_of_ne G (by simp)
      · have hfQ : f ≠ Q := by simpa using hef.symm
        rw [hnewQ, hnewOff f hfP hfQ]
        exact hQcross f hfD hfP hfQ
    · by_cases hfP : f = P
      · subst f
        have hp := (pairCompatible_comm G).mpr (hPcross e heD heP heQ)
        rw [hnewOff e heP heQ, hnewP]
        exact hp
      · by_cases hfQ : f = Q
        · subst f
          have hp := (pairCompatible_comm G).mpr (hQcross e heD heP heQ)
          rw [hnewOff e heP heQ, hnewQ]
          exact hp
        · rw [hnewOff e heP heQ, hnewOff f hfP hfQ]
          exact hvalid e heD f hfD hef

/-- The same swap preserves inclusion-maximality of the matching colour. -/
theorem longPair_oneSaturated_swap_selectedOuter_twoThreadFirst
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour) (a : Fin 4)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    OneSaturated G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hPD : P ∈ D := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hAP : A ≠ P := fun heq => hAD (heq ▸ hPD)
  have hAQ : A ≠ Q := fun heq => hAD (heq ▸ (by simpa [D, Q] using hQD))
  have hnewP : new P = some a := by simp [new, hPQ']
  have hnewQ : new Q = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAQ, A, hA]
  have hnewOff (e : G.edgeSet) (heP : e ≠ P) (heQ : e ≠ Q) :
      new e = colour e := by simp [new, heP, heQ]
  change OneSaturated G new
  intro e he
  by_cases heP : e = P
  · subst e
    exact ⟨Q, hnewQ, u, by simp [P], by simp [Q]⟩
  · by_cases heQ : e = Q
    · subst e
      exact False.elim (he hnewQ)
    · have heOld : colour e ≠ none := by
        intro heNone
        exact he ((hnewOff e heP heQ).trans heNone)
      obtain ⟨f, hf, y, hye, hyf⟩ := hsat e heOld
      by_cases hfP : f = P
      · subst f
        have hycase : y = v₁ ∨ y = u := by simpa [P] using hyf
        rcases hycase with hyv₁ | hyu
        · exact ⟨A, hnewA, y, hye, by simpa [A, hyv₁]⟩
        · exact ⟨Q, hnewQ, y, hye, by simpa [Q, hyu]⟩
      · have hfQ : f ≠ Q := by
          intro hfQ
          subst f
          have hfalse : some a = none := hQ.symm.trans (by simpa [Q] using hf)
          simp at hfalse
        exact ⟨f, (hnewOff f hfP hfQ).trans hf, y, hye, hyf⟩

/-- A degree-two vertex whose visible palette can change under the swap is
the selected middle vertex, the second vertex of the two-thread arm, or is
adjacent to the common centre. -/
theorem longPair_twoVertex_paletteAffectedBy_twoThreadFirst_swap_cases
    {u v₁ v₂ v₃ z w₁ w₂ t q : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet),
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = v₂ ∨ q = w₂ ∨ G.Adj q u := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, heS, x, hxe, hqx⟩ := haffect
  have hecase : e = (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∨
      e = (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) := by
    simpa using heS
  have hqne : q ≠ u := by
    intro hqu
    have hthree := h.start_three
    have htwo := hq
    unfold IsThreeVertex at hthree
    unfold IsTwoVertex at htwo
    rw [hqu] at htwo
    omega
  rcases hecase with rfl | rfl
  · have hxcase : x = v₁ ∨ x = u := by simpa using hxe
    rcases hxcase with hxv₁ | hxu
    · subst x
      rcases hqx with hqv₁ | hqv₁
      · right; right
        simpa [hqv₁] using h.first_adj.symm
      · have hqN : q ∈ G.neighborFinset v₁ :=
          (G.mem_neighborFinset v₁ q).mpr hqv₁.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
          h.left_adj h.first_adj.symm h.middle_ne_start] at hqN
        have hqcase : q = v₂ ∨ q = u := by simpa using hqN
        exact hqcase.elim Or.inl (fun hqu' => False.elim (hqne hqu'))
    · subst x
      rcases hqx with hqu | hqu
      · exact False.elim (hqne hqu)
      · exact Or.inr (Or.inr hqu)
  · have hxcase : x = w₁ ∨ x = u := by simpa using hxe
    rcases hxcase with hxw₁ | hxu
    · subst x
      rcases hqx with hqw₁ | hqw₁
      · right; right
        simpa [hqw₁] using g.first_adj.symm
      · have hqN : q ∈ G.neighborFinset w₁ :=
          (G.mem_neighborFinset w₁ q).mpr hqw₁.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
          g.middle_adj g.first_adj.symm g.second_ne_start] at hqN
        have hqcase : q = w₂ ∨ q = u := by simpa using hqN
        exact hqcase.elim (fun hw => Or.inr (Or.inl hw))
          (fun hqu' => False.elim (hqne hqu'))
    · subst x
      rcases hqx with hqu | hqu
      · exact False.elim (hqne hqu)
      · exact Or.inr (Or.inr hqu)

theorem longPair_vertexSeesInduced_old_of_twoThreadFirst_swap
    {u v₁ v₂ v₃ z w₁ w₂ t q : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (colour : G.edgeSet → OneTwoColor 4) (a : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hqu : G.Adj q u)
    (hall : ∀ i : Fin 4, VertexSeesInduced G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) q i) :
    ∀ i : Fin 4, VertexSeesInduced G colour q i := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hnewP : new P = some a := by simp [new, hPQ']
  have hnewQ : new Q = none := by simp [new]
  intro i
  by_cases hia : i = a
  · subst i
    apply (vertexSeesInduced_iff G colour q a).mpr
    exact ⟨Q, by simpa [Q] using hQ, u, by simp [Q], Or.inr hqu⟩
  · obtain ⟨e, he, x, hxe, hqx⟩ :=
      (vertexSeesInduced_iff G new q i).mp (by simpa [new] using hall i)
    have heP : e ≠ P := by
      intro heq
      subst e
      have hc : some a = some i := hnewP.symm.trans he
      exact hia (Option.some.inj hc).symm
    have heQ : e ≠ Q := by
      intro heq
      subst e
      have hc : none = some i := hnewQ.symm.trans he
      simp at hc
    apply (vertexSeesInduced_iff G colour q i).mpr
    refine ⟨e, ?_, x, hxe, hqx⟩
    simpa [new, heP, heQ] using he

theorem twoThreadCore_firstEdge_ne_lastEdge
    {u w₁ w₂ t : V} (g : TwoThreadCoreData G u w₁ w₂ t) :
    (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₂, t), g.last_adj⟩ : G.edgeSet) := by
  intro heq
  have hval : s(w₁, u) = s(w₂, t) := congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hval
  rcases hval with hsame | hswap
  · exact g.middle_adj.ne hsame.1
  · exact (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two) hswap.1.symm

/-- Condition 2 is preserved by the selected-outer/two-thread-first swap.
The explicit inequality `D ≠ P` is the only nonlocal geometric input; it
is automatic for the actual two-thread in girth at least sixteen. -/
theorem longPair_conditionTwo_swap_selectedOuter_twoThreadFirst
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (hsat : OneSaturated G colour)
    (a : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
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
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, t), g.last_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hQDne : Q ≠ D := by
    simpa [Q, D] using twoThreadCore_firstEdge_ne_lastEdge G g
  have hDP' : D ≠ P := by simpa [D, P] using hDP
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hQD' : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq => hAD (heq ▸ hPD)
  have hAQ : A ≠ Q := fun heq => hAD (heq ▸ hQD')
  have hBP : B ≠ P := fun heq => hBD (heq ▸ hPD)
  have hBQ : B ≠ Q := fun heq => hBD (heq ▸ hQD')
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hD : colour D = none := by
    exact longPair_twoThread_last_matching_of_first_two_induced G g colour hsat
      (by simpa [Q, hQ]) (by simpa [C, hC])
  have hnewQ : new Q = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAQ, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBQ, B, hB]
  have hnewD : new D = none := by
    simp [new, hDP', hQDne.symm, D, hD]
  have hagree : ColoringsAgreeOff G ({P, Q} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ Q := by simpa using he
    simp [new, hne.1, hne.2]
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  have hcases := longPair_twoVertex_paletteAffectedBy_twoThreadFirst_swap_cases
    G h g hq (by simpa [P, Q] using haffect)
  rcases hcases with hqv₂ | hqw₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub g.second_two
      g.middle_adj.symm g.first_two Q D hQDne hnewQ hnewD
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [Q])
        (Or.inr g.middle_adj.symm)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [D])
        (Or.inl rfl)
    · exact hall
  · by_cases hqv₁ : q = v₁
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub h.first_two
        h.left_adj h.middle_two A B hAB hnewA hnewB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [A])
          (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
          (Or.inr h.left_adj)
      · exact hall
    · by_cases hqw₁ : q = w₁
      · subst q
        apply longPair_paletteCondition_at_two_visible_matching G hsub g.first_two
          g.middle_adj g.second_two Q D hQDne hnewQ hnewD
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [Q])
            (Or.inl rfl)
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [D])
            (Or.inr g.middle_adj)
        · exact hall
      · have hqu' : q ≠ u := by
          intro hEq
          have hthree := h.start_three
          have htwo := hq
          unfold IsThreeVertex at hthree
          unfold IsTwoVertex at htwo
          rw [hEq] at htwo
          omega
        have hnotAffected : ¬ MatchingAffectedBy G
            ({P, Q} : Set G.edgeSet) q := by
          rintro ⟨e, heS, hqe⟩
          have hecase : e = P ∨ e = Q := by simpa using heS
          rcases hecase with rfl | rfl
          · have hqcase : q = v₁ ∨ q = u := by simpa [P] using hqe
            exact hqcase.elim hqv₁ hqu'
          · have hqcase : q = w₁ ∨ q = u := by simpa [Q] using hqe
            exact hqcase.elim hqw₁ hqu'
        apply hold q hq
        · exact (vertexSeesMatching_iff_of_not_affected G hagree
            hnotAffected).mpr hmatch
        · exact longPair_vertexSeesInduced_old_of_twoThreadFirst_swap
            G h g colour a hP hQ hPQ hqu (by simpa [new] using hall)

/-- The single directed Condition-3 obligation attached to a certified
two-thread. -/
def ConditionThreeAtTwoThread {u t : V} (q : G.Walk u t)
    (hq : IsKThread G q 2) (colour : G.edgeSet → OneTwoColor 4) : Prop :=
  ExternalEdgesInduced G colour u (threadFirstEdge G q hq) →
    ExternalEdgesInduced G colour t (threadLastEdge G q hq) →
    ExternalInducedColors G colour u (threadFirstEdge G q hq) ≠
      ExternalInducedColors G colour t (threadLastEdge G q hq)

/-- For the selected-outer/two-thread-first swap, global Condition 3 is
equivalent to its obligation on the displayed two-thread.  Thus the swap
has no hidden Condition-3 obstruction. -/
theorem longPair_conditionThree_swap_selectedOuter_twoThreadFirst_iff
    {u v₁ v₂ v₃ z t : V} (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (colour : G.edgeSet → OneTwoColor 4) (hold : ConditionThree G colour)
    (a : Fin 4) :
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q : G.edgeSet := threadFirstEdge G q hq
    let new := recolor G (recolor G colour P (some a)) Q none
    ConditionThree G new ↔ ConditionThreeAtTwoThread G q hq new := by
  dsimp only
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hnewQ : new Q = none := by simp [new]
  have hagree : ColoringsAgreeOff G ({P, Q} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ Q := by simpa using he
    simp [new, hne.1, hne.2]
  constructor
  · intro hnew
    exact hnew u t q hq
  · intro hcritical
    change ConditionThree G new
    apply hold.of_agreeOff G hagree
    intro r s p hp haffect hleft hright
    rcases haffect with haffect | haffect
    · obtain ⟨e, heS, hext⟩ := haffect
      have hecase : e = P ∨ e = Q := by simpa using heS
      rcases hecase with rfl | rfl
      · have hru : r = u :=
          longPair_start_eq_three_of_external_selectedOuter G p hp h
            (by simpa [P] using hext)
        subst r
        by_cases hfirst : threadFirstEdge G p hp = Q
        · have hone : p.getVert 1 = q.getVert 1 :=
            getVert_one_eq_of_threadFirstEdge_eq G hq.first_step_adj p hp
              (by simpa only [Q, threadFirstEdge] using hfirst)
          obtain ⟨htwo, hst⟩ := twoThread_tail_eq_of_getVert_one_eq
            G p q hp hq hone
          have hlast : threadLastEdge G p hp = threadLastEdge G q hq :=
            twoThread_lastEdge_eq_of_getVert_one_eq G p q hp hq hone
          subst s
          simpa only [new, hfirst, hlast] using hcritical
            (by simpa only [hfirst] using hleft)
            (by simpa only [hlast] using hright)
        · obtain ⟨i, hi⟩ := hleft Q
            ⟨by simp [Q, threadFirstEdge], Ne.symm hfirst⟩
          have hfalse := hnewQ.symm.trans hi
          simp at hfalse
      · obtain ⟨i, hi⟩ := hleft Q (by simpa [Q] using hext)
        have hfalse := hnewQ.symm.trans hi
        simp at hfalse
    · obtain ⟨e, heS, hext⟩ := haffect
      have hecase : e = P ∨ e = Q := by simpa using heS
      rcases hecase with rfl | rfl
      · have hsu : s = u :=
          longPair_end_eq_three_of_external_selectedOuter G p hp h
            (by simpa [P] using hext)
        subst s
        by_cases hlastQ : threadLastEdge G p hp = Q
        · have hfirstRev : threadFirstEdge G p.reverse hp.reverse = Q := by
            simpa [threadFirstEdge_reverse_two G p hp] using hlastQ
          have hone : p.reverse.getVert 1 = q.getVert 1 :=
            getVert_one_eq_of_threadFirstEdge_eq G hq.first_step_adj
              p.reverse hp.reverse
                (by simpa only [Q, threadFirstEdge] using hfirstRev)
          obtain ⟨htwo, hrt⟩ := twoThread_tail_eq_of_getVert_one_eq
            G p.reverse q hp.reverse hq hone
          have hfirstP : threadFirstEdge G p hp = threadLastEdge G q hq := by
            rw [← threadLastEdge_reverse_two G p hp]
            exact twoThread_lastEdge_eq_of_getVert_one_eq
              G p.reverse q hp.reverse hq hone
          subst r
          simpa only [new, hlastQ, hfirstP] using (hcritical
            (by simpa [hlastQ] using hright)
            (by simpa [hfirstP] using hleft)).symm
        · obtain ⟨i, hi⟩ := hright Q
            ⟨by simp [Q, threadFirstEdge], Ne.symm hlastQ⟩
          have hfalse := hnewQ.symm.trans hi
          simp at hfalse
      · obtain ⟨i, hi⟩ := hright Q (by simpa [Q] using hext)
        have hfalse := hnewQ.symm.trans hi
        simp at hfalse

/-- Package the three unconditional preservation results with the single
remaining Condition-3 obligation. -/
theorem longPair_preparedThreeThreadGap_swap_selectedOuter_twoThreadFirst
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t : V} (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour) (a : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some a)
    (hC : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let Q : G.edgeSet := threadFirstEdge G q hq
      let new := recolor G (recolor G colour P (some a)) Q none
      ConditionThreeAtTwoThread G q hq new) :
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q : G.edgeSet := threadFirstEdge G q hq
    PreparedThreeThreadGap G h
      (recolor G (recolor G colour P (some a)) Q none) := by
  dsimp only
  let g := hq.twoThreadCoreData G
  have hC' : colour
      (⟨s(q.getVert 1, q.getVert 2), g.middle_adj⟩ : G.edgeSet) ≠ none := by
    simpa [g] using hC
  have hQ' : colour
      (⟨s(q.getVert 1, u), g.first_adj.symm⟩ : G.edgeSet) = some a := by
    simpa [g, threadFirstEdge, Sym2.eq_swap] using hQ
  have hQD' : (⟨s(q.getVert 1, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [g, threadFirstEdge, Sym2.eq_swap] using hQD
  have hPQ' : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(q.getVert 1, u), g.first_adj.symm⟩ : G.edgeSet) := by
    simpa [g, threadFirstEdge, Sym2.eq_swap] using hPQ
  have hDP' : (⟨s(q.getVert 2, t), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) := by
    simpa [g, threadLastEdge] using hDP
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [g, threadFirstEdge, Sym2.eq_swap] using
      longPair_validOn_swap_selectedOuter_twoThreadFirst G h g colour
        hprepared.1 a hP hQ' hC' hQD' hPQ'
  · simpa [g, threadFirstEdge, Sym2.eq_swap] using
      longPair_oneSaturated_swap_selectedOuter_twoThreadFirst G h g colour
        hprepared.2.1 a hQ' hA hQD' hPQ'
  · simpa [g, threadFirstEdge, Sym2.eq_swap] using
      longPair_conditionTwo_swap_selectedOuter_twoThreadFirst G hsub h g colour
        hprepared.2.2.1 hprepared.2.1 a hP hQ' hC' hA hB hQD' hPQ' hDP'
  · exact (longPair_conditionThree_swap_selectedOuter_twoThreadFirst_iff
      G h q hq colour hprepared.2.2.2 a).2 hcritical

/-- If the neighbour two-thread's second edge is induced and its unique
Condition-3 obligation survives the arm swap, the selected three-thread
gap can be restored to a good colouring of the whole graph. -/
theorem longPair_hasGoodFour_of_twoThread_second_induced_of_critical
    {u v₁ v₂ v₃ z t : V} (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G) (a : Fin 4)
    (hP : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (threadFirstEdge G q hq) = some a)
    (hC : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ none)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hcritical :
      let base := transportColoringToSupergraph
        (G.deleteIncidenceSet_le v₂) small
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let Q : G.edgeSet := threadFirstEdge G q hq
      ConditionThreeAtTwoThread G q hq
        (recolor G (recolor G base P (some a)) Q none)) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let swap : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G base P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hRP' : R ≠ P := by simpa [R, P] using hRP
  have hRQ' : R ≠ Q := by simpa [R, Q] using hRQ
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hRD : R ∈ Dset := by
    change R ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [R, h.right_adj.ne, h.middle_ne_end]
  have hQD' : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq => hAD (heq ▸ hPD)
  have hAQ : A ≠ Q := fun heq => hAD (heq ▸ hQD')
  have hAR : A ≠ R := fun heq => hAD (heq ▸ hRD)
  have hBP : B ≠ P := fun heq => hBD (heq ▸ hPD)
  have hBQ : B ≠ Q := fun heq => hBD (heq ▸ hQD')
  have hBR : B ≠ R := fun heq => hBD (heq ▸ hRD)
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hAedge : A.1 ∉ (G.deleteIncidenceSet v₂).edgeSet := by
    simpa [Dset, RetainedEdges] using hAD
  have hBedge : B.1 ∉ (G.deleteIncidenceSet v₂).edgeSet := by
    simpa [Dset, RetainedEdges] using hBD
  have hbaseA : base A = none := by
    simp [base, transportColoringToSupergraph, hAedge]
  have hbaseB : base B = none := by
    simp [base, transportColoringToSupergraph, hBedge]
  have hswapA : swap A = none := by simp [swap, hAP, hAQ, hbaseA]
  have hswapB : swap B = none := by simp [swap, hBP, hBQ, hbaseB]
  have hswapP : swap P = some a := by simp [swap, hPQ']
  have hswapQ : swap Q = none := by simp [swap]
  have hswapR : swap R = none := by
    simp [swap, hRP', hRQ', R, base, hR]
  have hpreparedBase : PreparedThreeThreadGap G h base :=
    preparedThreeThreadGap_of_goodFour G hsub h small hsmall
  have hpreparedSwap : PreparedThreeThreadGap G h swap := by
    exact longPair_preparedThreeThreadGap_swap_selectedOuter_twoThreadFirst
      G hsub h q hq base hpreparedBase a (by simpa [base, P] using hP)
      (by simpa [base, Q] using hQ) (by simpa [base] using hC)
      (by simpa [base, A] using hbaseA) (by simpa [base, B] using hbaseB)
      (by simpa [Q] using hQD) (by simpa [P, Q] using hPQ)
      (by simpa [P] using hDP) (by simpa [base, P, Q, swap] using hcritical)
  have havailA : ColorAvailableOn G Dset swap A none := by
    exact matching_available_left_gap_of_outer_nonmatching G h swap
      (by simpa [P] using (show swap P ≠ none by simp [hswapP]))
  let afterA : G.edgeSet → OneTwoColor 4 := recolor G swap A none
  have hafterAOn : IsOneTwoColoringOn G (insert A Dset) afterA :=
    hpreparedSwap.1.extend_one G hAD havailA
  have hafterAA : afterA A = none := by simp [afterA]
  have hafterAR : afterA R = none := by
    rw [show afterA R = swap R by
      exact recolor_ne G swap none hAR.symm]
    exact hswapR
  obtain ⟨b, hb⟩ := exists_available_right_gap_after_left_matching G h
    afterA (by simpa [A] using hafterAA) R
      (by simpa [R] using hafterAR) (by simp [R])
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterA B (some b)
  have hBfresh : B ∉ insert A Dset := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨hAB.symm, hBD⟩
  have hfinalOn : IsOneTwoColoringOn G (insert B (insert A Dset)) final :=
    hafterAOn.extend_one G hBfresh hb
  have hvalid : IsOneTwoColoring G final := by
    simpa [IsOneTwoColoring, Dset, A, B,
      insert_threeThread_gap_retained_eq_univ G h] using hfinalOn
  have hagree : ColoringsAgreeOff G ({A, B} : Set G.edgeSet) swap final := by
    intro e he
    have hne : e ≠ A ∧ e ≠ B := by simpa using he
    simp [final, afterA, hne.1, hne.2]
  have hfinalA : final A = none := by simp [final, afterA, hAB]
  have hfinalB : final B = some b := by simp [final]
  have hfinalQ : final Q = none := by
    simp [final, afterA, hAQ.symm, hBQ.symm, hswapQ]
  have hfinalR : final R = none := by
    simp [final, afterA, hAR.symm, hBR.symm, hswapR]
  have hsaturated : OneSaturated G final := by
    intro e he
    by_cases heA : e = A
    · subst e
      exact False.elim (he hfinalA)
    by_cases heB : e = B
    · subst e
      exact ⟨A, hfinalA, v₂, by simp [B], by simp [A]⟩
    have heSwap : swap e ≠ none := by
      intro heNone
      apply he
      exact (hagree e (by simpa [heA, heB])).symm.trans heNone
    obtain ⟨f, hf, y, hye, hyf⟩ := hpreparedSwap.2.1 e heSwap
    by_cases hfB : f = B
    · subst f
      have hycase : y = v₃ ∨ y = v₂ := by simpa [B] using hyf
      rcases hycase with hyv₃ | hyv₂
      · exact ⟨R, hfinalR, y, hye, by simpa [R, hyv₃]⟩
      · exact ⟨A, hfinalA, y, hye, by simpa [A, hyv₂]⟩
    · by_cases hfA : f = A
      · subst f
        exact ⟨A, hfinalA, y, hye, hyf⟩
      · refine ⟨f, ?_, y, hye, hyf⟩
        exact (hagree f (by simpa [hfA, hfB])).symm.trans hf
  have hpalette : ∀ x : V, x = v₁ ∨ x = v₂ ∨ x = v₃ →
      VertexSeesMatching G final x →
      ¬ ∀ i : Fin 4, VertexSeesInduced G final x i := by
    intro x hxcase hmatch hall
    rcases hxcase with rfl | rfl | rfl
    · apply longPair_paletteCondition_at_two_visible_matching G hsub
        h.first_two h.left_adj h.middle_two A Q
      · exact fun heq => hAD (heq ▸ hQD')
      · exact hfinalA
      · exact hfinalQ
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [Q, threadFirstEdge]) (Or.inr h.first_adj.symm)
      · exact hall
    · exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
        h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
        hmatch) hall
    · apply longPair_paletteCondition_at_two_visible_matching G hsub
        h.third_two h.right_adj.symm h.middle_two A R hAR hfinalA hfinalR
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inr h.right_adj.symm)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [R]) (Or.inl rfl)
      · exact hall
  have hgood : GoodFour G final :=
    longPair_goodFour_of_preparedThreeThreadGap_recolour G h swap final
      hpreparedSwap hvalid hsaturated
      (by simpa [A, B] using hagree) hpalette
  let d : DecidableRel G.Adj := inferInstance
  rw [HasGoodFour]
  exact ⟨final, goodFour_change_decidableRel d (Classical.decRel _) final hgood⟩

/-- Hence, in a bad graph, the displayed two-thread is exactly the
Condition-3 obstruction to the swap. -/
theorem longPair_twoThread_swap_critical_failure_of_noGoodFour
    {u v₁ v₂ v₃ z t : V} (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G) (a : Fin 4)
    (hP : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (threadFirstEdge G q hq) = some a)
    (hC : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ none)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hbad : ¬ HasGoodFour G) :
    let base := transportColoringToSupergraph
      (G.deleteIncidenceSet_le v₂) small
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q : G.edgeSet := threadFirstEdge G q hq
    ¬ ConditionThreeAtTwoThread G q hq
      (recolor G (recolor G base P (some a)) Q none) := by
  dsimp only
  intro hcritical
  exact hbad (longPair_hasGoodFour_of_twoThread_second_induced_of_critical
    G h q hq small hsmall hsub a hP hR hQ hC hQD hPQ hDP hRP hRQ
    hcritical)

/-- Expanded form of the unique obstruction: both external pairs remain
induced and their induced-colour sets become equal. -/
theorem longPair_twoThread_swap_critical_normal_form_of_noGoodFour
    {u v₁ v₂ v₃ z t : V} (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G) (a : Fin 4)
    (hP : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (threadFirstEdge G q hq) = some a)
    (hC : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ none)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hbad : ¬ HasGoodFour G) :
    let base := transportColoringToSupergraph
      (G.deleteIncidenceSet_le v₂) small
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let Q : G.edgeSet := threadFirstEdge G q hq
    let swap := recolor G (recolor G base P (some a)) Q none
    ExternalEdgesInduced G swap u (threadFirstEdge G q hq) ∧
      ExternalEdgesInduced G swap t (threadLastEdge G q hq) ∧
      ExternalInducedColors G swap u (threadFirstEdge G q hq) =
        ExternalInducedColors G swap t (threadLastEdge G q hq) := by
  dsimp only
  have hfail := longPair_twoThread_swap_critical_failure_of_noGoodFour
    G h q hq small hsmall hsub a hP hR hQ hC hQD hPQ hDP hRP hRQ hbad
  simp only [ConditionThreeAtTwoThread] at hfail
  push_neg at hfail
  exact hfail

/-- Path-level form of the exact remaining blocker.  If the second edge of
the neighbouring two-thread is induced in a bad graph, then swapping its
first edge with the selected outer matching edge necessarily leaves both
external pairs induced and makes their palettes equal. -/
theorem longPair_twoThread_second_induced_critical_normal_form
    {u z t : V} {p : G.Walk u z} {q : G.Walk u t}
    (hp : IsKThread G p 3) (hq : IsKThread G q 2)
    (hdist : p.getVert 1 ≠ q.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G)
    (hP : transportColoringToSupergraph
      (G.deleteIncidenceSet_le (p.getVert 2)) small
      (threadFirstEdge G p hp) = none)
    (hR : transportColoringToSupergraph
      (G.deleteIncidenceSet_le (p.getVert 2)) small
      (threadLastEdge G p hp) = none)
    (hC : transportColoringToSupergraph
      (G.deleteIncidenceSet_le (p.getVert 2)) small
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ none)
    (hbad : ¬ HasGoodFour G) :
    let base := transportColoringToSupergraph
      (G.deleteIncidenceSet_le (p.getVert 2)) small
    let P : G.edgeSet := threadFirstEdge G p hp
    let Q : G.edgeSet := threadFirstEdge G q hq
    ∃ a : Fin 4,
      base Q = some a ∧
      let swap := recolor G (recolor G base P (some a)) Q none
      ExternalEdgesInduced G swap u Q ∧
        ExternalEdgesInduced G swap t (threadLastEdge G q hq) ∧
        ExternalInducedColors G swap u Q =
          ExternalInducedColors G swap t (threadLastEdge G q hq) := by
  dsimp only
  let h := hp.threeThreadCore G
  let Dset : Set G.edgeSet :=
    RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le (p.getVert 2)) small
  let P : G.edgeSet := threadFirstEdge G p hp
  let R : G.edgeSet := threadLastEdge G p hp
  let Q : G.edgeSet := threadFirstEdge G q hq
  have hpLen : p.length = 4 := by simpa using hp.length
  have hqLen : q.length = 3 := by simpa using hq.length
  have hpGetNe (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) (hij : i ≠ j) :
      p.getVert i ≠ p.getVert j := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show i ∈ {r : ℕ | r ≤ p.length} by simpa [hpLen] using hi)
      (show j ∈ {r : ℕ | r ≤ p.length} by simpa [hpLen] using hj)
      heq
    exact hij hinj
  have hqGetNe (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 3) (hij : i ≠ j) :
      q.getVert i ≠ q.getVert j := by
    intro heq
    have hinj := hq.1.getVert_injOn
      (show i ∈ {r : ℕ | r ≤ q.length} by simpa [hqLen] using hi)
      (show j ∈ {r : ℕ | r ≤ q.length} by simpa [hqLen] using hj)
      heq
    exact hij hinj
  have hpEnd : p.getVert 4 = z := by
    rw [← hpLen]
    exact p.getVert_length
  have hqEnd : q.getVert 3 = t := by
    rw [← hqLen]
    exact q.getVert_length
  have hQD : Q ∈ Dset := by
    have hfar := twoThread_vertex_far_from_threeThread_middle G hq h
      q.start_mem_support
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      hfar.1 hfar.2 Q (by simp [Q, threadFirstEdge])
  have hPQ : P ≠ Q := by
    intro heq
    have hval : s(u, p.getVert 1) = s(u, q.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hloop
    · exact hdist hsame.2
    · exact hp.first_step_adj.ne hloop.2.symm
  have hDP : threadLastEdge G q hq ≠ P := by
    intro heq
    have hval : s(q.getVert 2, t) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hswap
    · exact hqGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hsame.1)
    · exact hqGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa [hqEnd] using hswap.2)
  have hRP : R ≠ P := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hcase | hcase
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hcase.1)
    · exact hpGetNe 3 1 (by omega) (by omega) (by omega) hcase.1
  have hRQ : R ≠ Q := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, q.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hcase | hcase
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hcase.1)
    · exact hpGetNe 4 0 (by omega) (by omega) (by omega)
        (by simpa [hpEnd] using hcase.2)
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = u ∨ p.getVert 2 = p.getVert 1 := by
      simpa [P, threadFirstEdge] using hmem
    exact hcase.elim
      (fun he => hpGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using he))
      (hpGetNe 2 1 (by omega) (by omega) (by omega))
  have hvalid : IsOneTwoColoringOn G Dset base := by
    simpa [Dset, base] using transport_deleteThreeThreadMiddle_valid G h
      hsmall.valid
  have hQne : base Q ≠ none := by
    intro hQnone
    have hpq := hvalid P hPD Q hQD hPQ
    have hdisj : EndpointDisjoint G P Q := by
      simpa [base, P, Q, hP, hQnone] using hpq
    exact hdisj u (by simp [P, threadFirstEdge])
      (by simp [Q, threadFirstEdge])
  cases hQval : base Q with
  | none => exact False.elim (hQne hQval)
  | some a =>
      refine ⟨a, hQval, ?_⟩
      have hnormal := longPair_twoThread_swap_critical_normal_form_of_noGoodFour
        G h q hq small hsmall hsub a
        (by simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP)
        (by simpa [h, base, R, threadLastEdge] using hR)
        (by simpa [base, Q] using hQval) (by simpa [base] using hC)
        (by simpa [Dset, Q] using hQD)
        (by simpa [h, P, Q, threadFirstEdge, Sym2.eq_swap] using hPQ)
        (by simpa [h, P, threadFirstEdge, Sym2.eq_swap] using hDP)
        (by simpa [h, P, R, threadFirstEdge, threadLastEdge,
          Sym2.eq_swap] using hRP)
        (by simpa [h, R, Q, threadFirstEdge, threadLastEdge,
          Sym2.eq_swap] using hRQ) hbad
      simpa [base, P, Q, threadFirstEdge, Sym2.eq_swap] using hnormal

/-! ## Escaping the unique blocker with a fresh selected-outer colour -/

/-- At a degree-three centre with the displayed three arms, once the
two-thread first edge is matching its external palette is exactly the
colours on the other two first edges.  The statement also records that all
those external edges are induced. -/
theorem longPair_twoThreadFirst_external_data
    {u v₁ v₂ v₃ z w₁ w₂ w₃ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ s)
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
        have had : a = d := Option.some.inj (hfaP.symm.trans (by simpa [P] using hP))
        simp [had]
      · have hfaQ : colour Q = some a := by simpa [Q] using hfa
        have hai : a = i := Option.some.inj (hfaQ.symm.trans (by simpa [Q] using hQ))
        simp [hai]
      · exact False.elim (hfext.2 rfl)
    · intro ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact ⟨P, ⟨by simp [P], hPT⟩, by simpa [P] using hP⟩
      · exact ⟨Q, ⟨by simp [Q], hQT⟩, by simpa [Q] using hQ⟩

/-- The critical swap with colour `j` completely determines the far
palette.  Replacing `j` on the selected outer edge by a colour `d` outside
`{i,j}` therefore makes the two palettes different, while changing no far
external edge. -/
theorem longPair_conditionThreeAtTwoThread_alt_of_critical
    {u v₁ v₂ v₃ z w₁ w₂ w₃ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ s)
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
  have hcriticalStart := longPair_twoThreadFirst_external_data G h g q hq
    hvw hvq hwq critical j i hcriticalT hcriticalP hcriticalQ
  have haltStart := longPair_twoThreadFirst_external_data G h g q hq
    hvw hvq hwq alt d i haltT haltP haltQ
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
  have hfarInduced : ExternalEdgesInduced G alt t U :=
    externalEdgesInduced_of_agreeOff G hagree hmiss hcritical.2.1
  change ConditionThreeAtTwoThread G q hq alt
  intro _hleft _hright
  rw [haltStart.2, hfarAlt]
  intro heq
  have hdmem : d ∈ ({j, i} : Set (Fin 4)) := by
    rw [← heq]
    simp
  simpa [hdj, hdi] using hdmem

end Finite

end

end LeanCo.PackingEdgeColoring
