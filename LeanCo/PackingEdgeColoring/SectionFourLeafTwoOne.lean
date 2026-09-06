import LeanCo.PackingEdgeColoring.SectionFourLeafHard

/-!
# The matching-two / leaf branch of the Section 4 leaf reduction

This file treats the genuine two-thread core of Case 1.1: the retained
matching edge from the neighbour of the deleted leaf runs through two
successive degree-two vertices, while the other branch ends in a leaf.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The five displayed edges exhaust all edges visible at `a` in the
local path `u-v-a-r-t`, with the third branch `v-b`. -/
theorem leafTwoOne_visible_edge_cases
    {u v a b r t x : V}
    (huv : G.Adj u v) (hva : G.Adj v a) (hvb : G.Adj v b)
    (ha : IsTwoVertex G a) (har : G.Adj a r) (hrv : r ≠ v)
    (hr : IsTwoVertex G r) (hrt : G.Adj r t) (hta : t ≠ a)
    (hN : G.neighborFinset v = {u, a, b})
    (f : G.edgeSet) (hxf : x ∈ (f : Sym2 V))
    (hclose : a = x ∨ G.Adj a x) :
    f = (⟨s(u, v), huv⟩ : G.edgeSet) ∨
      f = (⟨s(v, a), hva⟩ : G.edgeSet) ∨
      f = (⟨s(v, b), hvb⟩ : G.edgeSet) ∨
      f = (⟨s(a, r), har⟩ : G.edgeSet) ∨
      f = (⟨s(r, t), hrt⟩ : G.edgeSet) := by
  rcases hclose with hax | hax
  · subst x
    rcases edge_eq_left_or_right_of_incident_two G ha hva.symm har
        hrv.symm f hxf with hfA | hfC
    · right; left
      apply Subtype.ext
      simpa [Sym2.eq_swap] using hfA
    · right; right; right; left
      exact Subtype.ext hfC
  · have hxmem : x ∈ ({v, r} : Finset V) := by
      rw [← neighborFinset_eq_pair_of_isTwoVertex G ha hva.symm har hrv.symm]
      exact (G.mem_neighborFinset a x).mpr hax
    have hxcases : x = v ∨ x = r := by simpa using hxmem
    rcases hxcases with hxv | hxr
    · subst x
      rcases edge_eq_leaf_or_first_or_second_of_incident_three G huv hva hvb
          hN f hxf with hfE | hfA | hfB
      · exact Or.inl hfE
      · exact Or.inr (Or.inl hfA)
      · exact Or.inr (Or.inr (Or.inl hfB))
    · subst x
      rcases edge_eq_left_or_right_of_incident_two G hr har.symm hrt
          hta.symm f hxf with hfC | hfD
      · right; right; right; left
        apply Subtype.ext
        simpa [Sym2.eq_swap] using hfC
      · right; right; right; right
        exact Subtype.ext hfD

/-- If assigning `c` to the leaf edge completes all four induced colours
at `a`, then every different available colour `d` must already occur on
the far continuation edge `r-t`.  Availability excludes the three nearer
induced candidates, and the retained matching guard excludes `v-a`. -/
theorem leafTwoOne_continuation_colour_of_full_palette
    {u v a b r t : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u)
    (ha : IsTwoVertex G a) (har : G.Adj a r) (hrv : r ≠ v)
    (hr : IsTwoVertex G r) (hrt : G.Adj r t) (hta : t ≠ a)
    (hN : G.neighborFinset v = {u, a, b})
    (old : G.edgeSet → OneTwoColor 4) {c d : Fin 4} (hcd : c ≠ d)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hd : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old
      (⟨s(u, v), huv⟩ : G.edgeSet) (some d))
    (hall : ∀ j : Fin 4, VertexSeesInduced G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some c)) a j) :
    old (⟨s(r, t), hrt⟩ : G.edgeSet) = some d := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let B : G.edgeSet := ⟨s(v, b), hvb⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let D : G.edgeSet := ⟨s(r, t), hrt⟩
  let final : G.edgeSet → OneTwoColor 4 := recolor G old E (some c)
  have hAE : A ≠ E := by
    intro heq
    have hua : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hcases : u = v ∨ u = a := by simpa [A] using hua
    exact hcases.elim huv.ne hau.symm
  have hBE : B ≠ E := by
    intro heq
    have hub : u ∈ (B : Sym2 V) := by rw [heq]; simp [E]
    have hcases : u = v ∨ u = b := by simpa [B] using hub
    exact hcases.elim huv.ne hbu.symm
  have hCE : C ≠ E := by
    intro heq
    have haE : a ∈ (E : Sym2 V) := by rw [← heq]; simp [C]
    have hcases : a = u ∨ a = v := by simpa [E] using haE
    exact hcases.elim hau (fun hav ↦ hva.ne hav.symm)
  have hru : r ≠ u := by
    intro hru
    have hav : a = v := eq_neighbor_of_degree_eq_one G hu huv
      (by simpa [hru] using har.symm)
    exact hva.ne hav.symm
  have hDE : D ≠ E := by
    intro heq
    have hrE : r ∈ (E : Sym2 V) := by rw [← heq]; simp [D]
    have hcases : r = u ∨ r = v := by simpa [E] using hrE
    exact hcases.elim hru hrv
  have hBD : B ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv B).mpr hBE
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hfinalA : final A = none := by
    rw [show final A = old A by exact recolor_ne G old (some c) hAE]
    simpa [A] using hA
  obtain ⟨f, hfcolour, x, hxf, hclose⟩ :=
    (vertexSeesInduced_iff G final a d).mp (hall d)
  rcases leafTwoOne_visible_edge_cases G huv hva hvb ha har hrv hr hrt hta
      hN f hxf hclose with rfl | rfl | rfl | rfl | rfl
  · have hsome : some c = some d := by simpa [final, E] using hfcolour
    exact False.elim (hcd (Option.some.inj hsome))
  · rw [hfinalA] at hfcolour
    simp at hfcolour
  · have hBold : old B = some d := by
      change final B = some d at hfcolour
      rw [show final B = old B by exact recolor_ne G old (some c) hBE]
        at hfcolour
      exact hfcolour
    have hsep := (colorAvailableOn_some_iff G
      (RetainedEdges (deleteLeafEdge G huv) G) old E d).mp hd
        B hBD hBE hBold
    exact False.elim (hsep.1 v (by simp [E]) (by simp [B]))
  · have hCold : old C = some d := by
      change final C = some d at hfcolour
      rw [show final C = old C by exact recolor_ne G old (some c) hCE]
        at hfcolour
      exact hfcolour
    have hsep := (colorAvailableOn_some_iff G
      (RetainedEdges (deleteLeafEdge G huv) G) old E d).mp hd
        C hCD hCE hCold
    exact False.elim (hsep.2 ⟨v, by simp [E], a, by simp [C], hva⟩)
  · simpa [final, hDE, D] using hfcolour

/-- If the far continuation edge has the same induced colour assigned to
the leaf edge, saturation supplies a matching edge external at the far
endpoint.  Hence the only potentially new Condition-3 thread cannot have
all external edges induced. -/
theorem ConditionThree.recolor_leafEdge_of_matching_two_two_far_colour
    {u v a r t : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (ha : IsTwoVertex G a) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (har : G.Adj a r) (hrv : r ≠ v)
    (hrt : G.Adj r t) (hta : t ≠ a) (hau : a ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (d : Fin 4)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hC : old (⟨s(a, r), har⟩ : G.edgeSet) ≠ none)
    (hD : old (⟨s(r, t), hrt⟩ : G.edgeSet) = some d)
    (hsat : OneSaturated G old) (hold : ConditionThree G old) :
    ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some d)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let D : G.edgeSet := ⟨s(r, t), hrt⟩
  let final : G.edgeSet → OneTwoColor 4 := recolor G old E (some d)
  by_contra hfail
  obtain ⟨y, p, hp, hfirst, _hleft, hright, _heq⟩ :=
    leafC3CriticalFailure_of_not_conditionThree G hu huv hva hau old d hA
      hold (by simpa [final, E] using hfail)
  have htwo : p.getVert 2 = r :=
    twoThread_getVert_two_eq_of_firstEdge_and_two G ha hva har hrv p hp hfirst
  have hyt : y = t :=
    twoThread_endpoint_eq_of_firstEdge_and_two_two G ha hr hva har hrv hrt hta
      p hp hfirst
  have hlast : threadLastEdge G p hp = D := by
    apply Subtype.ext
    simp [threadLastEdge, D, htwo, hyt]
  have hfar := twoThread_far_endpoint_ne_leaf_ends G hu p hp
  have htu : t ≠ u := by simpa [hyt] using hfar.1
  have htv : t ≠ v := by simpa [hyt] using hfar.2
  obtain ⟨f, hfnone, x, hxD, hxf⟩ := hsat D (by simp [D, hD])
  have hxcases : x = r ∨ x = t := by simpa [D] using hxD
  rcases hxcases with hxr | hxt
  · subst x
    rcases edge_eq_left_or_right_of_incident_two G hr har.symm hrt hta.symm
        f hxf with hfC | hfD
    · have hfeq : f = C := by
        apply Subtype.ext
        simpa [C, Sym2.eq_swap] using hfC
      subst f
      exact hC hfnone
    · have hfeq : f = D := Subtype.ext hfD
      subst f
      rw [hD] at hfnone
      simp at hfnone
  · subst x
    have hfD : f ≠ D := by
      intro hEq
      subst f
      rw [hD] at hfnone
      simp at hfnone
    have hfE : f ≠ E := by
      intro hEq
      subst f
      have htmem : t ∈ (E : Sym2 V) := hxf
      have htcases : t = u ∨ t = v := by simpa [E] using htmem
      exact htcases.elim htu htv
    have hfinalf : final f = none := by
      rw [show final f = old f by exact recolor_ne G old (some d) hfE]
      exact hfnone
    have hExternal : IsExternalAt G y (threadLastEdge G p hp) f := by
      refine ⟨?_, ?_⟩
      · simpa [hyt] using hxf
      · intro hEq
        apply hfD
        exact hEq.trans hlast
    obtain ⟨j, hj⟩ := hright f hExternal
    rw [show recolor G old E (some d) f = none by
      simpa [final] using hfinalf] at hj
    simp at hj

/-- The hard Case 1.1 core: the matching arm has two consecutive
degree-two vertices.  Two available leaf colours suffice.  If a colour
which is safe for Condition 3 is the unique colour completing the
forbidden palette at `a`, the other available colour is forced onto the
far edge.  The preceding saturation lemma then makes that other colour
safe for Condition 3 as well. -/
theorem exists_goodFour_leaf_three_matching_two_other_leaf_of_continuation_two
    (hsub : IsSubcubic G)
    {u v a b r t : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : G.degree b = 1) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v)
    (hrt : G.Adj r t) (hta : t ≠ a)
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
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let D : G.edgeSet := ⟨s(r, t), hrt⟩
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hcases : u = v ∨ u = a := by simpa [A] using huA
    exact hcases.elim huv.ne hau.symm
  have hCE : C ≠ E := by
    intro heq
    have haE : a ∈ (E : Sym2 V) := by rw [← heq]; simp [C]
    have hcases : a = u ∨ a = v := by simpa [E] using haE
    exact hcases.elim hau (fun hav ↦ hva.ne hav.symm)
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hcases : v = a ∨ v = r := by simpa [C] using hvC
    exact hcases.elim hva.ne (fun hvr ↦ hrv hvr.symm)
  have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base := by
    simpa [base] using transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hCne : base C ≠ none := by
    intro hC
    have hpairs := hvalidD A hAD C hCD hAC
    have hdisj : EndpointDisjoint G A C := by
      simpa [A, C, base, hA, hC] using hpairs
    exact hdisj a (by simp [A]) (by simp [C])
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
  have hsat : OneSaturated G base :=
    oneSaturated_leafBaseFour G huv small hsmall.oneSaturated
  let Bad (c : Fin 4) : Prop :=
    VertexSeesMatching G (recolor G base E (some c)) a ∧
      ∀ x : Fin 4, VertexSeesInduced G (recolor G base E (some c)) a x
  have bad_exclusive {c d : Fin 4} (hcd : c ≠ d)
      (hc : Bad c) (hd : Bad d) : False := by
    exact full_palette_leaf_colour_unique_at_two_four G huv base hbaseTwo ha hcd
      (by simpa [Bad, base, E] using hc.1)
      (by simpa [Bad, base, E] using hc.2)
      (by simpa [Bad, base, E] using hd.1)
      (by simpa [Bad, base, E] using hd.2)
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
  have bad_forces_c3_other {c d : Fin 4} (hcd : c ≠ d)
      (hc : Bad c)
      (hd : ColorAvailableOn G
        (RetainedEdges (deleteLeafEdge G huv) G) base E (some d)) :
      ConditionThree G (recolor G base E (some d)) := by
    have hDcolour : base D = some d := by
      simpa [base, D] using
        leafTwoOne_continuation_colour_of_full_palette G hu huv hva hvb hau hbu
          ha har hrv hr hrt hta hN base hcd (by simpa [base, A] using hA)
          (by simpa [base, E] using hd) (by simpa [Bad, base, E] using hc.2)
    simpa [base, E, C, D] using
      ConditionThree.recolor_leafEdge_of_matching_two_two_far_colour G hu huv
        ha hr hva har hrv hrt hta hau base d (by simpa [base, A] using hA)
        (by simpa [base, C] using hCne) hDcolour hsat hbaseThree
  have makeGood (c : Fin 4)
      (hc : ColorAvailableOn G
        (RetainedEdges (deleteLeafEdge G huv) G) base E (some c))
      (hbad : ¬ Bad c)
      (hthree : ConditionThree G (recolor G base E (some c))) :
      GoodFour G (recolor G base E (some c)) := by
    exact goodFour_leaf_three_matching_two_of_available_safe G hsub hu huv hv
      ha hva hvb hau hbNot hN small hsmall c (by simpa [base, E] using hc)
      (by simpa [base] using hA) (by simpa [Bad, base, E] using hbad)
      (by simpa [base, E] using hthree)
  by_cases h3i : ConditionThree G (recolor G base E (some i))
  · by_cases hbi : Bad i
    · have h3j : ConditionThree G (recolor G base E (some j)) :=
        bad_forces_c3_other hij hbi (by simpa [base, E] using hj)
      have hbj : ¬ Bad j := by
        intro hbadJ
        exact bad_exclusive hij hbi hbadJ
      exact ⟨recolor G base E (some j), makeGood j
        (by simpa [base, E] using hj) hbj h3j⟩
    · exact ⟨recolor G base E (some i), makeGood i
        (by simpa [base, E] using hi) hbi h3i⟩
  · have h3j : ConditionThree G (recolor G base E (some j)) :=
      (c3_pair hij (by simpa [base, E] using hi)
        (by simpa [base, E] using hj)).resolve_left h3i
    have hbj : ¬ Bad j := by
      intro hbadJ
      apply h3i
      exact bad_forces_c3_other hij.symm hbadJ
        (by simpa [base, E] using hi)
    exact ⟨recolor G base E (some j), makeGood j
      (by simpa [base, E] using hj) hbj h3j⟩

/-- Complete matching-two / other-leaf branch.  The continuation of the
matching arm is either another two-vertex, handled by the hard core above,
or a non-two-vertex, handled by the generic two-available-colour lemma. -/
theorem exists_goodFour_leaf_three_matching_two_other_leaf
    (hsub : IsSubcubic G)
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
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  obtain ⟨r, hrv, har⟩ := exists_other_neighbor_of_isTwoVertex G ha hva.symm
  by_cases hrTwo : IsTwoVertex G r
  · obtain ⟨t, hta, hrt⟩ := exists_other_neighbor_of_isTwoVertex G hrTwo har.symm
    exact exists_goodFour_leaf_three_matching_two_other_leaf_of_continuation_two
      G hsub hu huv hv ha hb hrTwo hva hvb hau hbu hab hN har hrv hrt hta
      small hsmall beta hA hB
  · exact
      exists_goodFour_leaf_three_matching_two_other_leaf_of_continuation_not_two
        G hsub hu huv hv ha hb hva hvb hau hbu hab hN har hrv hrTwo small
        hsmall beta hA hB

end Finite

end

end LeanCo.PackingEdgeColoring
