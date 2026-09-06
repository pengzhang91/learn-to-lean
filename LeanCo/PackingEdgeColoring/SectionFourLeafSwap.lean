import LeanCo.PackingEdgeColoring.SectionFourLeafTwoOne
import LeanCo.PackingEdgeColoring.SectionFourLeafShiftC3

/-!
# Matching shift for the hard Section 4 leaf branch

This module isolates the preservation facts for the paper's local swap on
`u-v-a-r`: the missing leaf edge `E = uv` stays matching, the old matching
edge `A = va` becomes induced, and `C = ar` becomes matching.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Moving the matching colour from `A = va` to `C = ar` preserves
inclusion-saturation when the leaf edge `E = uv` is also matching.  An
induced edge formerly saturated by `A` is still saturated by `E` on the
`v` side or by `C` on the `a` side. -/
theorem OneSaturated.shift_matching_along_leaf_arm
    {u v a r : V} (huv : G.Adj u v) (hva : G.Adj v a)
    (har : G.Adj a r) (hau : a ≠ u) (hrv : r ≠ v) (hru : r ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (gamma i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hC : old (⟨s(a, r), har⟩ : G.edgeSet) = some gamma)
    (hold : OneSaturated G old) :
    OneSaturated G
      (recolor G
        (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let afterC := recolor G old C none
  let final := recolor G afterC A (some i)
  have hEA : E ≠ A := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [← heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hEC : E ≠ C := by
    intro heq
    have huC : u ∈ (C : Sym2 V) := by rw [← heq]; simp [E]
    have hc : u = a ∨ u = r := by simpa [C] using huC
    exact hc.elim hau.symm hru.symm
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne hrv.symm
  have hfinalE : final E = none := by
    change recolor G (recolor G old C none) A (some i) E = none
    rw [recolor_ne G afterC (some i) hEA]
    change recolor G old C none E = none
    rw [recolor_ne G old none hEC]
    simpa [E] using hE
  have hfinalC : final C = none := by
    change recolor G (recolor G old C none) A (some i) C = none
    rw [recolor_ne G afterC (some i) hAC.symm]
    change recolor G old C none C = none
    simp
  intro e he
  by_cases heA : e = A
  · subst e
    refine ⟨C, hfinalC, a, by simp [A], by simp [C]⟩
  by_cases heC : e = C
  · subst e
    exact False.elim (he hfinalC)
  have heOld : old e ≠ none := by
    change recolor G (recolor G old C none) A (some i) e ≠ none at he
    rw [recolor_ne G afterC (some i) heA] at he
    change recolor G old C none e ≠ none at he
    rw [recolor_ne G old none heC] at he
    exact he
  obtain ⟨f, hf, z, hze, hzf⟩ := hold e heOld
  by_cases hfA : f = A
  · subst f
    have hz : z = v ∨ z = a := by simpa [A] using hzf
    rcases hz with hzv | hza
    · exact ⟨E, hfinalE, z, hze, by simpa [E, hzv]⟩
    · exact ⟨C, hfinalC, z, hze, by simpa [C, hza]⟩
  · have hfC : f ≠ C := by
      intro hfC
      rw [hfC, hC] at hf
      simp at hf
    refine ⟨f, ?_, z, hze, hzf⟩
    change recolor G (recolor G old C none) A (some i) f = none
    rw [recolor_ne G afterC (some i) hfA]
    change recolor G old C none f = none
    rw [recolor_ne G old none hfC]
    exact hf

/-- Assembly endpoint for the hard swap.  Once validity and Conditions 2
and 3 have been checked locally, saturation follows automatically from the
preceding matching-shift theorem and the good colouring of the leaf-deleted
graph. -/
theorem goodFour_leaf_arm_shift_of_valid_conditions
    {u v a r : V} (huv : G.Adj u v) (hva : G.Adj v a)
    (har : G.Adj a r) (hau : a ≠ u) (hrv : r ≠ v) (hru : r ≠ u)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (gamma i : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hC : leafBaseFour G huv small
      (⟨s(a, r), har⟩ : G.edgeSet) = some gamma)
    (hvalid : IsOneTwoColoring G
      (recolor G
        (recolor G (leafBaseFour G huv small)
          (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)))
    (htwo : ConditionTwo G
      (recolor G
        (recolor G (leafBaseFour G huv small)
          (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)))
    (hthree : ConditionThree G
      (recolor G
        (recolor G (leafBaseFour G huv small)
          (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i))) :
    GoodFour G
      (recolor G
        (recolor G (leafBaseFour G huv small)
          (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let base := leafBaseFour G huv small
  have hE : base (⟨s(u, v), huv⟩ : G.edgeSet) = none := by
    simp [base, leafBaseFour, transportColoringToSupergraph]
  have hsatBase : OneSaturated G base :=
    oneSaturated_leafBaseFour G huv small hsmall.oneSaturated
  have hsat : OneSaturated G
      (recolor G
        (recolor G base (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) :=
    OneSaturated.shift_matching_along_leaf_arm G huv hva har hau hrv hru
      base gamma i hE (by simpa [base] using hA) (by simpa [base] using hC)
      hsatBase
  exact ⟨hvalid, by simpa [base] using hsat, htwo, hthree⟩

/-- After the matching shift, the old colour of `C = ar` is absent from
the visibility palette of `a`.  Validity makes `C` the unique edge of that
colour in the entire visibility ball of `a`; the swap removes it, while the
new colour placed on `A` is assumed different. -/
theorem not_vertexSeesInduced_old_arm_colour_after_shift
    {u v a r : V} (huv : G.Adj u v) (hva : G.Adj v a)
    (har : G.Adj a r) (hau : a ≠ u) (hrv : r ≠ v) (hru : r ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (gamma i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hC : old (⟨s(a, r), har⟩ : G.edgeSet) = some gamma)
    (hig : i ≠ gamma)
    (hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old) :
    ¬ VertexSeesInduced G
      (recolor G
        (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) a gamma := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let afterC := recolor G old C none
  let final := recolor G afterC A (some i)
  have hEA : E ≠ A := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [← heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hEC : E ≠ C := by
    intro heq
    have huC : u ∈ (C : Sym2 V) := by rw [← heq]; simp [E]
    have hc : u = a ∨ u = r := by simpa [C] using huC
    exact hc.elim hau.symm hru.symm
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne hrv.symm
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hEC.symm
  intro hseen
  obtain ⟨f, hfgamma, z, hzf, haz⟩ :=
    (vertexSeesInduced_iff G final a gamma).mp hseen
  by_cases hfA : f = A
  · subst f
    have heq : some i = some gamma := by simpa [final] using hfgamma
    exact hig (Option.some.inj heq)
  by_cases hfC : f = C
  · subst f
    have : final C = none := by
      simp [final, afterC, hAC.symm]
    rw [this] at hfgamma
    simp at hfgamma
  have hfbase : old f = some gamma := by
    simpa [final, afterC, hfA, hfC] using hfgamma
  have hfE : f ≠ E := by
    intro hfE
    subst f
    rw [show old E = none by simpa [E] using hE] at hfbase
    simp at hfbase
  have hfD : f ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv f).mpr hfE
  have hpair := hvalidD C hCD f hfD (fun h ↦ hfC h.symm)
  have hCgamma : old C = some gamma := by
    simpa [C] using hC
  have hsep : InducedSeparated G C f := by
    exact (pairCompatible_some_self (G := G) gamma).mp (by
      simpa [hCgamma, hfbase] using hpair)
  rcases haz with rfl | haz
  · exact hsep.1 a (by simp [C]) hzf
  · exact hsep.2 ⟨a, by simp [C], z, hzf, haz⟩

/-- The same old arm colour is absent at the far endpoint `r`.  This is
the endpoint-symmetric form needed when the shifted matching edge `C`
makes `r` subject to Condition 2. -/
theorem not_vertexSeesInduced_old_arm_colour_at_far_after_shift
    {u v a r : V} (huv : G.Adj u v) (hva : G.Adj v a)
    (har : G.Adj a r) (hau : a ≠ u) (hrv : r ≠ v) (hru : r ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (gamma i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hC : old (⟨s(a, r), har⟩ : G.edgeSet) = some gamma)
    (hig : i ≠ gamma)
    (hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old) :
    ¬ VertexSeesInduced G
      (recolor G
        (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) r gamma := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let afterC := recolor G old C none
  let final := recolor G afterC A (some i)
  have hEC : E ≠ C := by
    intro heq
    have huC : u ∈ (C : Sym2 V) := by rw [← heq]; simp [E]
    have hc : u = a ∨ u = r := by simpa [C] using huC
    exact hc.elim hau.symm hru.symm
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne hrv.symm
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hEC.symm
  intro hseen
  obtain ⟨f, hfgamma, z, hzf, hrz⟩ :=
    (vertexSeesInduced_iff G final r gamma).mp hseen
  by_cases hfA : f = A
  · subst f
    have heq : some i = some gamma := by simpa [final] using hfgamma
    exact hig (Option.some.inj heq)
  by_cases hfC : f = C
  · subst f
    have : final C = none := by
      simp [final, afterC, hAC.symm]
    rw [this] at hfgamma
    simp at hfgamma
  have hfbase : old f = some gamma := by
    simpa [final, afterC, hfA, hfC] using hfgamma
  have hfE : f ≠ E := by
    intro hfE
    subst f
    rw [show old E = none by simpa [E] using hE] at hfbase
    simp at hfbase
  have hfD : f ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv f).mpr hfE
  have hpair := hvalidD C hCD f hfD (fun h ↦ hfC h.symm)
  have hCgamma : old C = some gamma := by
    simpa [C] using hC
  have hsep : InducedSeparated G C f := by
    exact (pairCompatible_some_self (G := G) gamma).mp (by
      simpa [hCgamma, hfbase] using hpair)
  rcases hrz with rfl | hrz
  · exact hsep.1 r (by simp [C]) hzf
  · exact hsep.2 ⟨r, by simp [C], z, hzf, hrz⟩

/-- Condition 2 is preserved by the leaf-arm matching shift whenever the
other branch at `v` ends at a three-vertex.  The old colour of `C` is a
missing colour at each newly matching two-vertex (`a`, and possibly `r`).
At every other affected two-vertex, a hypothetical full final palette
transports back to a forbidden full old palette. -/
theorem ConditionTwo.shift_matching_along_leaf_arm
    {u v a b r : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsThreeVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (har : G.Adj a r) (hau : a ≠ u) (hrv : r ≠ v) (hru : r ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (old : G.edgeSet → OneTwoColor 4) (gamma i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hC : old (⟨s(a, r), har⟩ : G.edgeSet) = some gamma)
    (hig : i ≠ gamma)
    (hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old)
    (hold : ConditionTwo G old) :
    ConditionTwo G
      (recolor G
        (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let afterC := recolor G old C none
  let final := recolor G afterC A (some i)
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne hrv.symm
  have hagree : ColoringsAgreeOff G ({A, C} : Set G.edgeSet) old final := by
    intro e he
    have hne : e ≠ A ∧ e ≠ C := by simpa using he
    simp [final, afterC, hne.1, hne.2]
  have hmissA : ¬ VertexSeesInduced G final a gamma := by
    simpa [final, afterC, A, C] using
      not_vertexSeesInduced_old_arm_colour_after_shift G huv hva har hau hrv
        hru old gamma i hE hC hig hvalidD
  have hmissR : ¬ VertexSeesInduced G final r gamma := by
    simpa [final, afterC, A, C] using
      not_vertexSeesInduced_old_arm_colour_at_far_after_shift G huv hva har hau
        hrv hru old gamma i hE hC hig hvalidD
  apply hold.of_agreeOff G hagree
  intro q hq _ hmatch hall
  by_cases hqa : q = a
  · subst q
    exact hmissA (hall gamma)
  by_cases hqr : q = r
  · subst q
    exact hmissR (hall gamma)
  have hmatchOld : VertexSeesMatching G old q := by
    rw [vertexSeesMatching_iff] at hmatch ⊢
    obtain ⟨f, hf, hqf⟩ := hmatch
    by_cases hfA : f = A
    · subst f
      simp [final] at hf
    by_cases hfC : f = C
    · subst f
      have hqc : q = a ∨ q = r := by simpa [C] using hqf
      exact False.elim (hqc.elim hqa hqr)
    exact ⟨f, by simpa [final, afterC, hfA, hfC] using hf, hqf⟩
  apply hold q hq hmatchOld
  intro j
  obtain ⟨f, hf, z, hzf, hqz⟩ :=
    (vertexSeesInduced_iff G final q j).mp (hall j)
  by_cases hfA : f = A
  · subst f
    have hji : j = i := by
      have hs : some i = some j := by simpa [final] using hf
      exact (Option.some.inj hs).symm
    subst j
    have hz : z = v ∨ z = a := by simpa [A] using hzf
    rcases hz with hzv | hza
    · have hqv : q = v ∨ G.Adj q v := by simpa [hzv] using hqz
      rcases hqv with hqv | hqv
      · subst q
        unfold IsTwoVertex at hq
        unfold IsThreeVertex at hv
        omega
      · have hqN : q ∈ ({u, a, b} : Finset V) := by
          rw [← hN]
          exact (G.mem_neighborFinset v q).mpr hqv.symm
        have hcases : q = u ∨ q = a ∨ q = b := by simpa using hqN
        rcases hcases with hqu | hqa' | hqb
        · subst q
          unfold IsTwoVertex at hq
          omega
        · exact False.elim (hqa hqa')
        · subst q
          unfold IsTwoVertex at hq
          unfold IsThreeVertex at hb
          omega
    · have hqaClose : q = a ∨ G.Adj q a := by simpa [hza] using hqz
      rcases hqaClose with hqa' | hqaAdj
      · exact False.elim (hqa hqa')
      · have hqN : q ∈ ({v, r} : Finset V) := by
          rw [← neighborFinset_eq_pair_of_isTwoVertex G ha hva.symm har hrv.symm]
          exact (G.mem_neighborFinset a q).mpr hqaAdj.symm
        have hcases : q = v ∨ q = r := by simpa using hqN
        rcases hcases with hqv | hqr'
        · subst q
          unfold IsTwoVertex at hq
          unfold IsThreeVertex at hv
          omega
        · exact False.elim (hqr hqr')
  by_cases hfC : f = C
  · subst f
    have : final C = none := by simp [final, afterC, hAC.symm]
    rw [this] at hf
    simp at hf
  exact (vertexSeesInduced_iff G old q j).mpr
    ⟨f, by simpa [final, afterC, hfA, hfC] using hf, z, hzf, hqz⟩

/-- Validity of the matching shift from two semantic local hypotheses.
The new induced colour on `A = va` must be absent from the old visibility
ball of `a`, while `r` must have no old incident matching edge.  Availability
at the leaf edge supplies separation on the `v` side of `A`. -/
theorem isOneTwoColoring_leaf_arm_shift_of_available
    {u v a r : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (ha : IsTwoVertex G a) (hva : G.Adj v a) (har : G.Adj a r)
    (hau : a ≠ u) (hrv : r ≠ v) (hru : r ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hmissing : ¬ VertexSeesInduced G old a i)
    (hnoMatchingR : ∀ f : G.edgeSet,
      old f = none → r ∈ (f : Sym2 V) → False)
    (hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old) :
    IsOneTwoColoring G
      (recolor G
        (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let D0 : Set G.edgeSet := D \ ({A, C} : Set G.edgeSet)
  let afterC := recolor G old C none
  let D1 : Set G.edgeSet := insert C D0
  let final := recolor G afterC A (some i)
  let D2 : Set G.edgeSet := insert A D1
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hCE : C ≠ E := by
    intro heq
    have huC : u ∈ (C : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = a ∨ u = r := by simpa [C] using huC
    exact hc.elim hau.symm hru.symm
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne hrv.symm
  have hEnone : old E = none := by simpa [E] using hE
  have hAnone : old A = none := by simpa [A] using hA
  have hAD : A ∈ D := by
    simpa [D, E] using
      (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have havailC : ColorAvailableOn G D0 old C none := by
    apply (colorAvailableOn_none_iff G D0 old C).mpr
    intro f hfD0 hfC hfnone
    intro p hpC hpf
    have hp : p = a ∨ p = r := by simpa [C] using hpC
    rcases hp with hpa | hpr
    · have hfA : f ≠ A := by
        intro hEq
        apply hfD0.2
        simp [hEq]
      have hpAF := hvalidD A hAD f hfD0.1 hfA.symm
      have hdisj : EndpointDisjoint G A f := by
        simpa [hAnone, hfnone] using hpAF
      exact hdisj a (by simp [A]) (hpa ▸ hpf)
    · exact hnoMatchingR f hfnone (hpr ▸ hpf)
  have havailA : ColorAvailableOn G D1 afterC A (some i) := by
    apply (colorAvailableOn_some_iff G D1 afterC A i).mpr
    intro f hfD1 hfA hfi
    have hfCases : f = C ∨ f ∈ D0 := by simpa [D1] using hfD1
    rcases hfCases with rfl | hfD0
    · simp [afterC] at hfi
    · have hfC : f ≠ C := by
        intro hEq
        apply hfD0.2
        simp [hEq]
      have hfiOld : old f = some i := by
        simpa [afterC, hfC] using hfi
      have hfE : f ≠ E := by
        intro hEq
        subst f
        rw [show old E = none by simpa [E] using hE] at hfiOld
        simp at hfiOld
      have hsepEf : InducedSeparated G E f :=
        (colorAvailableOn_some_iff G D old E i).mp
          (by simpa [D, E] using hi) f hfD0.1 hfE hfiOld
      apply (inducedSeparated_iff_forall_endpoints G).mpr
      intro p hpA q hqf
      have hp : p = v ∨ p = a := by simpa [A] using hpA
      rcases hp with hpv | hpa
      · simpa [hpv] using
          ((inducedSeparated_iff_forall_endpoints G).mp hsepEf v
            (by simp [E]) q hqf)
      · constructor
        · intro haq
          apply hmissing
          apply (vertexSeesInduced_iff G old a i).mpr
          exact ⟨f, hfiOld, q, hqf, Or.inl (by simpa [hpa] using haq)⟩
        · intro haq
          apply hmissing
          apply (vertexSeesInduced_iff G old a i).mpr
          exact ⟨f, hfiOld, q, hqf, Or.inr (by simpa [hpa] using haq)⟩
  have hvalid0 : IsOneTwoColoringOn G D0 old :=
    hvalidD.mono G (fun (_ : G.edgeSet) (hf : _ ∈ D0) ↦ hf.1)
  have hCnotD0 : C ∉ D0 := by simp [D0]
  have hvalid1 : IsOneTwoColoringOn G D1 afterC := by
    simpa [D1, afterC] using hvalid0.extend_one G hCnotD0 havailC
  have hAnotD1 : A ∉ D1 := by simp [D1, D0, hAC]
  have hvalid2 : IsOneTwoColoringOn G D2 final := by
    simpa [D2, final] using hvalid1.extend_one G hAnotD1 havailA
  have hECdisjoint : EndpointDisjoint G E C := by
    intro p hpE hpC
    have hp' : p = u ∨ p = v := by simpa [E] using hpE
    have hp'' : p = a ∨ p = r := by simpa [C] using hpC
    rcases hp' with rfl | rfl <;> rcases hp'' with h | h
    · exact hau h.symm
    · exact hru h.symm
    · exact hva.ne h
    · exact hrv h.symm
  have havailE : ColorAvailableOn G D2 final E none := by
    apply (colorAvailableOn_none_iff G D2 final E).mpr
    intro f hfD2 hfE hfnone
    have hfCases : f = A ∨ f = C ∨ f ∈ D0 := by
      simpa [D2, D1] using hfD2
    rcases hfCases with rfl | rfl | hfD0
    · simp [final] at hfnone
    · exact hECdisjoint
    · have hfA : f ≠ A := by
        intro hEq
        apply hfD0.2
        simp [hEq]
      have hfC : f ≠ C := by
        intro hEq
        apply hfD0.2
        simp [hEq]
      have hfOld : old f = none := by
        simpa [final, afterC, hfA, hfC] using hfnone
      have hdisjAf : EndpointDisjoint G A f := by
        have hp := hvalidD A hAD f hfD0.1 hfA.symm
        simpa [hAnone, hfOld] using hp
      intro p hpE hpf
      have hp : p = u ∨ p = v := by simpa [E] using hpE
      rcases hp with hpu | hpv
      · let fH : (deleteLeafEdge G huv).edgeSet := ⟨f.1, hfD0.1⟩
        exact no_retained_edge_incident_leaf G hu huv fH (hpu ▸ hpf)
      · exact hdisjAf v (by simp [A]) (hpv ▸ hpf)
  have hEnotD2 : E ∉ D2 := by
    intro hmem
    have hcases : E = A ∨ E = C ∨ E ∈ D0 := by
      simpa [D2, D1] using hmem
    rcases hcases with h | h | h
    · exact hAE h.symm
    · exact hCE h.symm
    · exact ((mem_retained_deleteLeafEdge_iff G huv E).mp
        (by simpa [D] using h.1)) rfl
  have hvalid3 := hvalid2.extend_one G hEnotD2 havailE
  have hdomain : insert E D2 = Set.univ := by
    ext f
    simp only [Set.mem_insert_iff, Set.mem_univ, iff_true]
    by_cases hfE : f = E
    · exact Or.inl hfE
    right
    by_cases hfA : f = A
    · exact Or.inl hfA
    right
    by_cases hfC : f = C
    · exact Or.inl hfC
    right
    refine ⟨?_, ?_⟩
    · simpa [D] using
        (mem_retained_deleteLeafEdge_iff G huv f).mpr (by simpa [E] using hfE)
    · simp [hfA, hfC]
  have hfinalE : final E = none := by
    change recolor G (recolor G old C none) A (some i) E = none
    rw [recolor_ne G afterC (some i) hAE.symm]
    change recolor G old C none E = none
    rw [recolor_ne G old none hCE.symm]
    exact hEnone
  have hrecolorE : recolor G final E none = final := by
    funext f
    by_cases hfE : f = E
    · subst f
      simp [hfinalE]
    · simp [hfE]
  rw [hdomain, hrecolorE] at hvalid3
  simpa [IsOneTwoColoring, final, afterC, A, C] using hvalid3

/-- Validity when only the first matching arm edge is changed to an
available induced colour.  Separation at `v` comes from availability at
the missing leaf edge, while absence at `a` supplies the other half. -/
theorem isOneTwoColoring_recolor_leaf_arm_first_of_available
    {u v a : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hau : a ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hmissing : ¬ VertexSeesInduced G old a i)
    (hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old) :
    IsOneTwoColoring G
      (recolor G old (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let D0 : Set G.edgeSet := D \ {A}
  let final := recolor G old A (some i)
  let D1 : Set G.edgeSet := insert A D0
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hAD : A ∈ D := by
    simpa [D, E] using
      (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hEnone : old E = none := by simpa [E] using hE
  have hAnone : old A = none := by simpa [A] using hA
  have havailA : ColorAvailableOn G D0 old A (some i) := by
    apply (colorAvailableOn_some_iff G D0 old A i).mpr
    intro f hfD0 hfA hfi
    have hfE : f ≠ E := by
      intro hEq
      subst f
      rw [hEnone] at hfi
      simp at hfi
    have hsepEf : InducedSeparated G E f :=
      (colorAvailableOn_some_iff G D old E i).mp
        (by simpa [D, E] using hi) f hfD0.1 hfE hfi
    apply (inducedSeparated_iff_forall_endpoints G).mpr
    intro p hpA q hqf
    have hp : p = v ∨ p = a := by simpa [A] using hpA
    rcases hp with hpv | hpa
    · simpa [hpv] using
        ((inducedSeparated_iff_forall_endpoints G).mp hsepEf v
          (by simp [E]) q hqf)
    · constructor
      · intro haq
        apply hmissing
        exact (vertexSeesInduced_iff G old a i).mpr
          ⟨f, hfi, q, hqf, Or.inl (by simpa [hpa] using haq)⟩
      · intro haq
        apply hmissing
        exact (vertexSeesInduced_iff G old a i).mpr
          ⟨f, hfi, q, hqf, Or.inr (by simpa [hpa] using haq)⟩
  have hvalid0 : IsOneTwoColoringOn G D0 old :=
    hvalidD.mono G (fun (_ : G.edgeSet) (hf : _ ∈ D0) ↦ hf.1)
  have hAnotD0 : A ∉ D0 := by simp [D0]
  have hvalid1 : IsOneTwoColoringOn G D1 final := by
    simpa [D1, final] using hvalid0.extend_one G hAnotD0 havailA
  have havailE : ColorAvailableOn G D1 final E none := by
    apply (colorAvailableOn_none_iff G D1 final E).mpr
    intro f hfD1 hfE hfnone
    have hfCases : f = A ∨ f ∈ D0 := by simpa [D1] using hfD1
    rcases hfCases with rfl | hfD0
    · simp [final] at hfnone
    · have hfA : f ≠ A := by
        intro hEq
        exact hfD0.2 (by simp [hEq])
      have hfOld : old f = none := by simpa [final, hfA] using hfnone
      have hdisjAf : EndpointDisjoint G A f := by
        have hp := hvalidD A hAD f hfD0.1 hfA.symm
        simpa [hAnone, hfOld] using hp
      intro p hpE hpf
      have hp : p = u ∨ p = v := by simpa [E] using hpE
      rcases hp with hpu | hpv
      · let fH : (deleteLeafEdge G huv).edgeSet := ⟨f.1, hfD0.1⟩
        exact no_retained_edge_incident_leaf G hu huv fH (hpu ▸ hpf)
      · exact hdisjAf v (by simp [A]) (hpv ▸ hpf)
  have hEnotD1 : E ∉ D1 := by
    intro hmem
    have hcases : E = A ∨ E ∈ D0 := by simpa [D1] using hmem
    rcases hcases with h | h
    · exact hAE h.symm
    · exact ((mem_retained_deleteLeafEdge_iff G huv E).mp
        (by simpa [D] using h.1)) rfl
  have hvalid2 := hvalid1.extend_one G hEnotD1 havailE
  have hdomain : insert E D1 = Set.univ := by
    ext f
    simp only [Set.mem_insert_iff, Set.mem_univ, iff_true]
    by_cases hfE : f = E
    · exact Or.inl hfE
    right
    by_cases hfA : f = A
    · exact Or.inl hfA
    right
    exact ⟨by simpa [D] using
      (mem_retained_deleteLeafEdge_iff G huv f).mpr (by simpa [E] using hfE),
      by simp [hfA]⟩
  have hfinalE : final E = none := by
    change recolor G old A (some i) E = none
    rw [recolor_ne G old (some i) hAE.symm]
    exact hEnone
  have hrecolorE : recolor G final E none = final := by
    funext f
    by_cases hfE : f = E
    · subst f
      simp [hfinalE]
    · simp [hfE]
  rw [hdomain, hrecolorE] at hvalid2
  simpa [IsOneTwoColoring, final, A] using hvalid2

/-- If an available leaf colour completes the full forbidden palette at
`a` and the next vertex `r` on the matching arm has degree two, shifting
the matching edge from `A` to `C` repairs the colouring.  Fullness forces
the chosen induced colour to have been absent at `a`, and also forbids any
old matching edge at `r`; these are exactly the two hypotheses of the
validity lemma above. -/
theorem exists_goodFour_leaf_shift_of_full_at_two_continuation
    (hsub : IsSubcubic G)
    {u v a b r : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsThreeVertex G b) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hrv : r ≠ v)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (i : Fin 4)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hall : ∀ j : Fin 4, VertexSeesInduced G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let afterI := recolor G base E (some i)
  have hru : r ≠ u := by
    intro hru
    subst r
    have hav : a = v := eq_neighbor_of_degree_eq_one G hu huv har.symm
    exact hva.ne hav.symm
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hCE : C ≠ E := by
    intro heq
    have huC : u ∈ (C : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = a ∨ u = r := by simpa [C] using huC
    exact hc.elim hau.symm hru.symm
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne hrv.symm
  have hAD : A ∈ D := by
    simpa [D, E] using
      (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hCD : C ∈ D := by
    simpa [D, E] using
      (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hvalidD : IsOneTwoColoringOn G D base := by
    simpa [D, base] using transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hCne : base C ≠ none := by
    intro hCnone
    have hp := hvalidD A hAD C hCD hAC
    have hdisj : EndpointDisjoint G A C := by
      simpa [show base A = none by simpa [base, A] using hA, hCnone] using hp
    exact hdisj a (by simp [A]) (by simp [C])
  obtain ⟨gamma, hCgamma⟩ := Option.ne_none_iff_exists'.mp hCne
  have hECnotSeparated : ¬ InducedSeparated G E C := by
    intro hsep
    apply hsep.2
    exact ⟨v, by simp [E], a, by simp [C], hva⟩
  have hig : i ≠ gamma := by
    intro hig
    subst gamma
    have hsep := (colorAvailableOn_some_iff G D base E i).mp
      (by simpa [D, base, E] using hi) C hCD hCE
      (by simpa [base, C] using hCgamma)
    exact hECnotSeparated hsep
  have hEnone : base E = none := by
    simp [base, E, leafBaseFour, transportColoringToSupergraph]
  have hAnone : base A = none := by simpa [base, A] using hA
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hmatchAfter : VertexSeesMatching G afterI a := by
    rw [vertexSeesMatching_iff]
    exact ⟨A, by simpa [afterI, hAE] using hAnone, by simp [A]⟩
  have hiMissing : ¬ VertexSeesInduced G base a i :=
    not_seen_base_of_full_after_leaf_colour_four G huv base hbaseTwo ha i
      (by simpa [afterI, base, E] using hmatchAfter)
      (by simpa [afterI, base, E] using hall)
  have hnoMatchingR : ∀ f : G.edgeSet,
      base f = none → r ∈ (f : Sym2 V) → False := by
    intro f hfnone hrf
    have hfE : f ≠ E := by
      intro hEq
      have hrmem : r ∈ (E : Sym2 V) := hEq ▸ hrf
      have hr' : r = u ∨ r = v := by simpa [E] using hrmem
      exact hr'.elim hru hrv
    have hfAfter : afterI f = none := by
      simpa [afterI, hfE] using hfnone
    have hAf : A ≠ f := by
      intro hEq
      have hrmem : r ∈ (A : Sym2 V) := hEq ▸ hrf
      have hr' : r = v ∨ r = a := by simpa [A] using hrmem
      exact hr'.elim hrv (fun h ↦ har.ne h.symm)
    exact (paletteCondition_at_of_two_visible_matching_four G hsub ha har hr
      A f hAf
      (by simpa [afterI, hAE] using hAnone) hfAfter
      (mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (show a ∈ (A : Sym2 V) by simp [A]) (Or.inl rfl))
      (mem_vertexVisibleEdgeFinset_of_endpoint_close G hrf (Or.inr har)))
      (by simpa [afterI, base, E] using hall)
  let final := recolor G (recolor G base C none) A (some i)
  have hvalid : IsOneTwoColoring G final := by
    simpa [final, base, A, C] using
      isOneTwoColoring_leaf_arm_shift_of_available G hu huv ha hva har hau hrv
        hru base i hEnone hAnone (by simpa [D, base, E] using hi) hiMissing
        hnoMatchingR (by simpa [D] using hvalidD)
  have htwo : ConditionTwo G final := by
    simpa [final, base, A, C] using
      ConditionTwo.shift_matching_along_leaf_arm G hu huv hv ha hb hva hvb har
        hau hrv hru hN base gamma i hEnone
        (by simpa [base, C] using hCgamma) hig (by simpa [D] using hvalidD)
        hbaseTwo
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hthree : ConditionThree G final := by
    simpa [final, base, A, C] using
      ConditionThree.shift_matching_along_leaf_two_arm G hu huv ha hr hva har
        hau hrv hru base i hEnone hbaseThree
  refine ⟨final, ?_⟩
  exact goodFour_leaf_arm_shift_of_valid_conditions G huv hva har hau hrv hru
    small hsmall gamma i hA (by simpa [base, C] using hCgamma)
    (by simpa [final] using hvalid) (by simpa [final] using htwo)
    (by simpa [final] using hthree)

/-- Complete extension when the matching arm has two consecutive
two-vertices and its far endpoint is not a three-vertex.  If the available
leaf colour is palette-safe, use it directly; if it completes the full
palette at `a`, the preceding matching shift repairs the colouring. -/
theorem exists_goodFour_leaf_three_matching_two_other_three_of_available_two_two_endpoint_not_three
    (hsub : IsSubcubic G)
    {u v a b r t : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsThreeVertex G b) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hrv : r ≠ v)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrt : G.Adj r t) (hta : t ≠ a)
    (htNot : ¬ IsThreeVertex G t)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (i : Fin 4)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let direct := recolor G base E (some i)
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hthree : ConditionThree G direct := by
    simpa [direct, base, E] using
      ConditionThree.recolor_leafEdge_of_matching_two_two_endpoint_not_three
        G hu huv ha hr hva har hrv hrt hta hau htNot base i
        (by simpa [base] using hA) hbaseThree
  by_cases hall : ∀ j : Fin 4, VertexSeesInduced G direct a j
  · exact exists_goodFour_leaf_shift_of_full_at_two_continuation G hsub hu huv
      hv ha hb hr hva hvb hau hrv hN har small hsmall hA i
      (by simpa [base, E] using hi) (by simpa [direct, base, E] using hall)
  · have hbNot : ¬ IsTwoVertex G b := by
      intro hbTwo
      unfold IsTwoVertex at hbTwo
      unfold IsThreeVertex at hb
      omega
    refine ⟨direct, ?_⟩
    exact goodFour_leaf_three_matching_two_of_available_safe G hsub hu huv hv
      ha hva hvb hau hbNot hN small hsmall i (by simpa [base, E] using hi)
      (by simpa [base] using hA)
      (by
        intro hbad
        exact hall (by simpa [direct, base, E] using hbad.2))
      (by simpa [direct] using hthree)

/-- The two-colour argument from the leaf-other-arm case only uses that
the second arm is not a two-vertex once the two available colours are
given.  In particular it applies when that arm ends at a three-vertex.
The continuation-colour and saturation lemmas force the colour rejected by
Condition 2 to be safe for Condition 3. -/
theorem exists_goodFour_leaf_three_matching_two_other_three_of_two_available_continuation_two
    (hsub : IsSubcubic G)
    {u v a b r t : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsThreeVertex G b) (hr : IsTwoVertex G r)
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
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let D : G.edgeSet := ⟨s(r, t), hrt⟩
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hCE : C ≠ E := by
    intro heq
    have haE : a ∈ (E : Sym2 V) := by rw [← heq]; simp [C]
    have hc : a = u ∨ a = v := by simpa [E] using haE
    exact hc.elim hau (fun hav ↦ hva.ne hav.symm)
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne (fun hvr ↦ hrv hvr.symm)
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
  have hbNot : ¬ IsTwoVertex G b := by
    intro hbTwo
    unfold IsThreeVertex at hb
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

/-- Therefore, in the matching-two / other-three branch, any two distinct
available leaf colours already suffice, independently of the degree of the
continuation of the matching arm. -/
theorem exists_goodFour_leaf_three_matching_two_other_three_of_two_available
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsThreeVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
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
  obtain ⟨r, hrv, har⟩ :=
    exists_other_neighbor_of_isTwoVertex G ha hva.symm
  have hbNot : ¬ IsTwoVertex G b := by
    intro hbTwo
    unfold IsThreeVertex at hb
    unfold IsTwoVertex at hbTwo
    omega
  by_cases hrTwo : IsTwoVertex G r
  · obtain ⟨t, hta, hrt⟩ :=
      exists_other_neighbor_of_isTwoVertex G hrTwo har.symm
    exact
      exists_goodFour_leaf_three_matching_two_other_three_of_two_available_continuation_two
        G hsub hu huv hv ha hb hrTwo hva hvb hau hbu hab hN har hrv hrt hta
        small hsmall beta hA hB i j hij hi hj
  · exact
      exists_goodFour_leaf_three_matching_two_continuation_not_two_of_two_available
        G hsub hu huv hv ha hva hvb hau hbu hab hbNot hN har hrv hrTwo small
        hsmall beta hA hB i j hij hi hj

/-- Exact reduction of the matching-two / other-three branch.  All states
with two available leaf colours extend; hence the only remaining state has
a unique available induced colour. -/
theorem leaf_three_matching_two_other_three_unique_available_reduction
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsThreeVertex G b)
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
      ∃ i : Fin 4,
        ColorAvailableOn G
          (RetainedEdges (deleteLeafEdge G huv) G)
          (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i) ∧
        ∀ j : Fin 4,
          ColorAvailableOn G
            (RetainedEdges (deleteLeafEdge G huv) G)
            (leafBaseFour G huv small)
            (⟨s(u, v), huv⟩ : G.edgeSet) (some j) → j = i := by
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
  by_cases hsecond : ∃ j : Fin 4,
      ColorAvailableOn G
        (RetainedEdges H G) (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some j) ∧ j ≠ i
  · obtain ⟨j, hj, hji⟩ := hsecond
    left
    exact exists_goodFour_leaf_three_matching_two_other_three_of_two_available
      G hsub hu huv hv ha hb hva hvb hau hbu hab hN small hsmall beta hA hB
      i j hji.symm hi (by simpa [H] using hj)
  · right
    refine ⟨i, hi, ?_⟩
    intro j hj
    by_contra hji
    exact hsecond ⟨j, by simpa [H] using hj, hji⟩

end Finite

end

end LeanCo.PackingEdgeColoring
