import LeanCo.PackingEdgeColoring.SectionThreeDeleteEdge

/-!
# The four easy outer-colour cases for a deleted two-thread

This module restores the middle edge of a two-thread whenever its two
surviving outer edges do not carry the same induced colour.  It is shared by
the `(2,1,1)` and `(2,2,0)` reductions.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If neither outer edge has the matching colour, the matching colour is
available on the missing middle edge. -/
theorem matching_available_middle_of_outer_nonmatching
    {u a x z : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    (colour : G.edgeSet → OneTwoColor 5)
    (hleft : colour (⟨s(u, a), hua⟩ : G.edgeSet) ≠ none)
    (hright : colour (⟨s(x, z), hxz⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G (RetainedEdges (deleteMiddleEdge G hax) G) colour
      (⟨s(a, x), hax⟩ : G.edgeSet) none := by
  apply (colorAvailableOn_none_iff G _ _ _).mpr
  intro f hfD _ hfnone q hqe hqf
  have hq : q = a ∨ q = x := by simpa using hqe
  rcases hq with hqa | hqx
  · have hfa := retained_edge_eq_leftOuter_of_incident G ha hua hax hux
      f hfD (hqa ▸ hqf)
    exact hleft (by simpa [hfa] using hfnone)
  · have hfr := retained_edge_eq_rightOuter_of_incident G hx hax hxz haz
      f hfD (hqx ▸ hqf)
    exact hright (by simpa [hfr] using hfnone)

/-- If no other retained matching edge is incident with the right terminal,
the matching colour can be moved onto the right outer edge. -/
theorem matching_available_rightOuter_of_no_other_terminal_matching
    {a x z : V}
    (hx : IsTwoVertex G x)
    (hax : G.Adj a x) (hxz : G.Adj x z) (haz : a ≠ z)
    (colour : G.edgeSet → OneTwoColor 5)
    (hno : ∀ f, f ∈ RetainedEdges (deleteMiddleEdge G hax) G →
      f ≠ (⟨s(x, z), hxz⟩ : G.edgeSet) → z ∈ (f : Sym2 V) →
      colour f ≠ none) :
    ColorAvailableOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(x, z), hxz⟩ : G.edgeSet)})
      colour (⟨s(x, z), hxz⟩ : G.edgeSet) none := by
  apply (colorAvailableOn_none_iff G _ _ _).mpr
  intro f hfD hfr hfnone q hqR hqf
  have hq : q = x ∨ q = z := by simpa using hqR
  rcases hq with hqx | hqz
  · have hfeq := retained_edge_eq_rightOuter_of_incident G hx hax hxz haz
      f hfD.1 (hqx ▸ hqf)
    exact hfD.2 (by simpa [hfeq])
  · exact hno f hfD.1 hfr (hqz ▸ hqf) hfnone

/-- Symmetric matching-colour move on the left outer edge. -/
theorem matching_available_leftOuter_of_no_other_terminal_matching
    {u a x : V}
    (ha : IsTwoVertex G a)
    (hua : G.Adj u a) (hax : G.Adj a x) (hux : u ≠ x)
    (colour : G.edgeSet → OneTwoColor 5)
    (hno : ∀ f, f ∈ RetainedEdges (deleteMiddleEdge G hax) G →
      f ≠ (⟨s(u, a), hua⟩ : G.edgeSet) → u ∈ (f : Sym2 V) →
      colour f ≠ none) :
    ColorAvailableOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(u, a), hua⟩ : G.edgeSet)})
      colour (⟨s(u, a), hua⟩ : G.edgeSet) none := by
  apply (colorAvailableOn_none_iff G _ _ _).mpr
  intro f hfD hfl hfnone q hqL hqf
  have hq : q = u ∨ q = a := by simpa using hqL
  rcases hq with hqu | hqa
  · exact hno f hfD.1 hfl (hqu ▸ hqf) hfnone
  · have hfeq := retained_edge_eq_leftOuter_of_incident G ha hua hax hux
      f hfD.1 (hqa ▸ hqf)
    exact hfD.2 (by simpa [hfeq])

set_option maxHeartbeats 1200000 in
/-- The common four-case extension theorem.  Its input is an ambient
colouring which is valid on all retained edges and satisfies Condition I;
the deleted middle edge has its transport default `none`.  Unless the two
outer edges carry the same induced colour, the colouring extends to a good
colouring of the whole graph. -/
theorem exists_goodFive_extension_middle_of_outer_not_same_induced
    {u a x z : V}
    (hsub : IsSubcubic G)
    (hu : IsThreeVertex G u) (hz : IsThreeVertex G z)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    (base : G.edgeSet → OneTwoColor 5)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G) base)
    (hcondition : ConditionI G base)
    (hmiddle : base (⟨s(a, x), hax⟩ : G.edgeSet) = none)
    (hnotSame : ¬ ∃ i : Fin 5,
      base (⟨s(u, a), hua⟩ : G.edgeSet) = some i ∧
      base (⟨s(x, z), hxz⟩ : G.edgeSet) = some i) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  classical
  let D : Set G.edgeSet := RetainedEdges (deleteMiddleEdge G hax) G
  let E : G.edgeSet := ⟨s(a, x), hax⟩
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  have hvalidD : IsOneTwoColoringOn G D base := by
    simpa [D] using hvalid
  have hED : E ∉ D := by
    intro he
    exact ((mem_retained_deleteMiddleEdge_iff G hax E).mp he) rfl
  have hLD : L ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax L).mpr
    exact (middleEdge_ne_leftOuter G hua hax hux).symm
  have hRD : R ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax R).mpr
    exact (middleEdge_ne_rightOuter G hax hxz haz).symm
  have hLR : L ≠ R := leftOuter_ne_rightOuter G hua hax hxz hux
  have hEL : E ≠ L := middleEdge_ne_leftOuter G hua hax hux
  have hER : E ≠ R := middleEdge_ne_rightOuter G hax hxz haz
  have hwhole : insert E D = Set.univ := by
    simpa [E, D] using insert_middle_retained_deleteMiddleEdge_eq_univ G hax
  have whole_of_insert {colour : G.edgeSet → OneTwoColor 5}
      (h : IsOneTwoColoringOn G (insert E D) colour) :
      IsOneTwoColoring G colour := by
    unfold IsOneTwoColoring
    rw [← hwhole]
    exact h
  have finish (colour : G.edgeSet → OneTwoColor 5)
      (hpacking : IsOneTwoColoring G colour)
      (hmatching : ∀ f, colour f = none → base f = none ∨ f = L ∨ f = R)
      (hinduced : ∀ f i, colour f = some i → base f = some i ∨ f = E) :
      GoodFive G colour := by
    refine ⟨hpacking, ?_⟩
    exact ConditionI.of_middle_new_support G hsub hu hz ha hx hua hax hxz
      hux haz hcondition
      (by simpa [L, R] using hmatching)
      (by simpa [E] using hinduced)
  have hLmem : L ∈ incidentEdgeFinset G u := by
    apply (mem_incidentEdgeFinset (G := G)).mpr
    simp [L]
  have hRmem : R ∈ incidentEdgeFinset G z := by
    apply (mem_incidentEdgeFinset (G := G)).mpr
    simp [R]
  cases hL : base L with
  | none =>
      cases hR : base R with
      | none =>
          obtain ⟨i, hi⟩ :=
            exists_available_middle_of_two_matching_terminal_edges G hu hz ha hx
              hua hax hxz hux haz D base L R hLR
              (Finset.mem_union_left _ hLmem)
              (Finset.mem_union_right _ hRmem) hL hR
          let final := recolor G base E (some i)
          have hfinalOn : IsOneTwoColoringOn G (insert E D) final :=
            hvalidD.extend_one G hED hi
          refine ⟨final, finish final (whole_of_insert hfinalOn) ?_ ?_⟩
          · intro f hf
            by_cases hfE : f = E
            · subst f
              simp [final] at hf
            · exact Or.inl (by simpa [final, hfE] using hf)
          · intro f j hf
            by_cases hfE : f = E
            · exact Or.inr hfE
            · exact Or.inl (by simpa [final, hfE] using hf)
      | some j =>
          by_cases hextra : ∃ f : G.edgeSet,
              f ∈ D ∧ f ≠ R ∧ z ∈ (f : Sym2 V) ∧ base f = none
          · obtain ⟨f, hfD, hfR, hzf, hfnone⟩ := hextra
            have hi : ∃ i : Fin 5, ColorAvailableOn G D base E (some i) := by
              by_cases hfL : f = L
              · subst f
                have hzu : z = u := by
                  have hzua : z = u ∨ z = a := by simpa [L] using hzf
                  rcases hzua with hzu | hza
                  · exact hzu
                  · have hz' : G.degree z = 3 := hz
                    have ha' : G.degree a = 2 := ha
                    rw [hza] at hz'
                    omega
                exact exists_available_middle_of_coincident_terminals G hu ha hx
                  hua hax (by simpa [hzu] using hxz) hux hua.ne.symm D base L
                  hLmem hL
              · apply exists_available_middle_of_two_matching_terminal_edges G
                  hu hz ha hx hua hax hxz hux haz D base L f (Ne.symm hfL)
                · exact Finset.mem_union_left _ hLmem
                · exact Finset.mem_union_right _
                    ((mem_incidentEdgeFinset (G := G)).mpr hzf)
                · exact hL
                · exact hfnone
            obtain ⟨i, hi⟩ := hi
            let final := recolor G base E (some i)
            have hfinalOn : IsOneTwoColoringOn G (insert E D) final :=
              hvalidD.extend_one G hED hi
            refine ⟨final, finish final (whole_of_insert hfinalOn) ?_ ?_⟩
            · intro f' hf'
              by_cases hf'E : f' = E
              · subst f'
                simp [final] at hf'
              · exact Or.inl (by simpa [final, hf'E] using hf')
            · intro f' k hf'
              by_cases hf'E : f' = E
              · exact Or.inr hf'E
              · exact Or.inl (by simpa [final, hf'E] using hf')
          · have hno : ∀ f, f ∈ D → f ≠ R → z ∈ (f : Sym2 V) →
                base f ≠ none := by
              intro f hfD hfR hzf hfnone
              exact hextra ⟨f, hfD, hfR, hzf, hfnone⟩
            have havailR : ColorAvailableOn G (D \ {R}) base R none := by
              simpa [D, R] using
                matching_available_rightOuter_of_no_other_terminal_matching G
                  hx hax hxz haz base (by simpa [D, R] using hno)
            let after := recolor G base R none
            have hdomainR : insert R (D \ {R}) = D := by
              ext f
              by_cases hfR : f = R
              · subst f
                simp [hRD]
              · simp [hfR]
            have hafter : IsOneTwoColoringOn G D after := by
              have hwithout : IsOneTwoColoringOn G (D \ {R}) base :=
                IsOneTwoColoringOn.mono (G := G) hvalidD Set.diff_subset
              have hsmall := hwithout.extend_one G (by simp) havailR
              rw [hdomainR] at hsmall
              exact hsmall
            have hafterL : after L = none := by simp [after, hLR, hL]
            have hafterR : after R = none := by simp [after]
            obtain ⟨i, hi⟩ :=
              exists_available_middle_of_two_matching_terminal_edges G hu hz ha hx
                hua hax hxz hux haz D after L R hLR
                (Finset.mem_union_left _ hLmem)
                (Finset.mem_union_right _ hRmem) hafterL hafterR
            let final := recolor G after E (some i)
            have hfinalOn : IsOneTwoColoringOn G (insert E D) final :=
              hafter.extend_one G hED hi
            refine ⟨final, finish final (whole_of_insert hfinalOn) ?_ ?_⟩
            · intro f hf
              by_cases hfE : f = E
              · subst f
                simp [final] at hf
              by_cases hfR : f = R
              · exact Or.inr (Or.inr hfR)
              · exact Or.inl (by simpa [final, after, hfE, hfR] using hf)
            · intro f k hf
              by_cases hfE : f = E
              · exact Or.inr hfE
              by_cases hfR : f = R
              · subst f
                simp [final, after, hfE] at hf
              · exact Or.inl (by simpa [final, after, hfE, hfR] using hf)
  | some i =>
      cases hR : base R with
      | none =>
          by_cases hextra : ∃ f : G.edgeSet,
              f ∈ D ∧ f ≠ L ∧ u ∈ (f : Sym2 V) ∧ base f = none
          · obtain ⟨f, hfD, hfL, huf, hfnone⟩ := hextra
            have hi : ∃ j : Fin 5, ColorAvailableOn G D base E (some j) := by
              by_cases hfR : f = R
              · subst f
                have huz : u = z := by
                  have huxz : u = x ∨ u = z := by simpa [R] using huf
                  rcases huxz with hux' | huz
                  · exact False.elim (hux hux')
                  · exact huz
                exact exists_available_middle_of_coincident_terminals G hu ha hx
                  hua hax (by simpa [huz] using hxz) hux hua.ne.symm D base R
                  ((mem_incidentEdgeFinset (G := G)).mpr huf) hR
              · apply exists_available_middle_of_two_matching_terminal_edges G
                  hu hz ha hx hua hax hxz hux haz D base f R hfR
                · exact Finset.mem_union_left _
                    ((mem_incidentEdgeFinset (G := G)).mpr huf)
                · exact Finset.mem_union_right _ hRmem
                · exact hfnone
                · exact hR
            obtain ⟨j, hj⟩ := hi
            let final := recolor G base E (some j)
            have hfinalOn : IsOneTwoColoringOn G (insert E D) final :=
              hvalidD.extend_one G hED hj
            refine ⟨final, finish final (whole_of_insert hfinalOn) ?_ ?_⟩
            · intro f' hf'
              by_cases hf'E : f' = E
              · subst f'
                simp [final] at hf'
              · exact Or.inl (by simpa [final, hf'E] using hf')
            · intro f' k hf'
              by_cases hf'E : f' = E
              · exact Or.inr hf'E
              · exact Or.inl (by simpa [final, hf'E] using hf')
          · have hno : ∀ f, f ∈ D → f ≠ L → u ∈ (f : Sym2 V) →
                base f ≠ none := by
              intro f hfD hfL huf hfnone
              exact hextra ⟨f, hfD, hfL, huf, hfnone⟩
            have havailL : ColorAvailableOn G (D \ {L}) base L none := by
              simpa [D, L] using
                matching_available_leftOuter_of_no_other_terminal_matching G
                  ha hua hax hux base (by simpa [D, L] using hno)
            let after := recolor G base L none
            have hdomainL : insert L (D \ {L}) = D := by
              ext f
              by_cases hfL : f = L
              · subst f
                simp [hLD]
              · simp [hfL]
            have hafter : IsOneTwoColoringOn G D after := by
              have hwithout : IsOneTwoColoringOn G (D \ {L}) base :=
                IsOneTwoColoringOn.mono (G := G) hvalidD Set.diff_subset
              have hsmall := hwithout.extend_one G (by simp) havailL
              rw [hdomainL] at hsmall
              exact hsmall
            have hafterL : after L = none := by simp [after]
            have hafterR : after R = none := by simp [after, hLR.symm, hR]
            obtain ⟨j, hj⟩ :=
              exists_available_middle_of_two_matching_terminal_edges G hu hz ha hx
                hua hax hxz hux haz D after L R hLR
                (Finset.mem_union_left _ hLmem)
                (Finset.mem_union_right _ hRmem) hafterL hafterR
            let final := recolor G after E (some j)
            have hfinalOn : IsOneTwoColoringOn G (insert E D) final :=
              hafter.extend_one G hED hj
            refine ⟨final, finish final (whole_of_insert hfinalOn) ?_ ?_⟩
            · intro f hf
              by_cases hfE : f = E
              · subst f
                simp [final] at hf
              by_cases hfL : f = L
              · exact Or.inr (Or.inl hfL)
              · exact Or.inl (by simpa [final, after, hfE, hfL] using hf)
            · intro f k hf
              by_cases hfE : f = E
              · exact Or.inr hfE
              by_cases hfL : f = L
              · subst f
                simp [final, after, hfE] at hf
              · exact Or.inl (by simpa [final, after, hfE, hfL] using hf)
      | some j =>
          have hij : i ≠ j := by
            intro hij
            subst j
            exact hnotSame ⟨i, hL, hR⟩
          have havail : ColorAvailableOn G D base E none := by
            exact matching_available_middle_of_outer_nonmatching G ha hx hua hax
              hxz hux haz base
              (by change base L ≠ none; simp [hL])
              (by change base R ≠ none; simp [hR])
          let final := recolor G base E none
          have hfinalOn : IsOneTwoColoringOn G (insert E D) final :=
            hvalidD.extend_one G hED havail
          have hfinalEq : final = base := by
            funext f
            by_cases hfE : f = E
            · subst f
              simpa [final] using hmiddle.symm
            · simp [final, hfE]
          refine ⟨final, ?_⟩
          rw [hfinalEq]
          exact ⟨by
            rw [← hfinalEq]
            exact whole_of_insert hfinalOn, hcondition⟩

end Finite

end

end LeanCo.PackingEdgeColoring
