import LeanCo.PackingEdgeColoring.SectionFourLeafReduction

/-!
# Closing the remaining Section 4 leaf branches

This module packages one more local move used in the difficult leaf
configuration.  The deleted leaf edge remains matching, while the old
matching edge on one arm is changed to an induced colour.  A matching edge
at the far end of that arm replaces the lost saturation witness.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If the edge beyond `a` is already incident with a matching edge at its
far endpoint, changing `A = va` from matching to induced preserves
inclusion-saturation.  Old witnesses through `v` are replaced by the leaf
edge, and old witnesses through `a` are replaced by the far matching edge. -/
theorem OneSaturated.recolor_leaf_arm_first_of_far_matching
    {u v a r : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (ha : IsTwoVertex G a)
    (hva : G.Adj v a) (har : G.Adj a r) (hrv : r ≠ v)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (m : G.edgeSet) (hm : old m = none) (hrm : r ∈ (m : Sym2 V))
    (hold : OneSaturated G old) :
    OneSaturated G
      (recolor G old (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let final := recolor G old A (some i)
  have hEA : E ≠ A := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [← heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    rcases hc with huv' | hua
    · exact huv.ne huv'
    · unfold IsTwoVertex at ha
      rw [← hua, hu] at ha
      omega
  have hmA : m ≠ A := by
    intro hma
    have hrA : r ∈ (A : Sym2 V) := hma ▸ hrm
    have hc : r = v ∨ r = a := by simpa [A] using hrA
    exact hc.elim hrv (fun h ↦ har.ne h.symm)
  have hfinalE : final E = none := by
    rw [show final E = old E by exact recolor_ne G old (some i) hEA]
    exact hE
  have hfinalM : final m = none := by
    rw [show final m = old m by exact recolor_ne G old (some i) hmA]
    exact hm
  intro e he
  by_cases heA : e = A
  · subst e
    exact ⟨E, hfinalE, v, by simp [A], by simp [E]⟩
  have heOld : old e ≠ none := by
    change recolor G old A (some i) e ≠ none at he
    rw [recolor_ne G old (some i) heA] at he
    exact he
  obtain ⟨f, hf, z, hze, hzf⟩ := hold e heOld
  by_cases hfA : f = A
  · subst f
    have hz : z = v ∨ z = a := by simpa [A] using hzf
    rcases hz with hzv | hza
    · exact ⟨E, hfinalE, z, hze, by simpa [E, hzv]⟩
    · have hae : a ∈ (e : Sym2 V) := hza ▸ hze
      rcases edge_eq_left_or_right_of_incident_two G ha hva.symm har hrv.symm
          e hae with heA' | heC
      · have : e = A := by
          apply Subtype.ext
          simpa [A, Sym2.eq_swap] using heA'
        exact False.elim (heA this)
      · have heq : e = C := by exact Subtype.ext heC
        subst e
        exact ⟨m, hfinalM, r, by simp [C], hrm⟩
  · refine ⟨f, ?_, z, hze, hzf⟩
    change recolor G old A (some i) f = none
    rw [recolor_ne G old (some i) hfA]
    exact hf

/-- Recolouring the matching arm edge `va` while leaving the leaf edge
matching cannot create a Condition-3 obstruction.  At endpoint `v` the
leaf edge violates the external-induced premise, and `a` cannot be an
endpoint of a certified two-thread. -/
theorem ConditionThree.recolor_leaf_arm_first_with_leaf_matching
    {u v a : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (ha : IsTwoVertex G a) (hva : G.Adj v a)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hold : ConditionThree G old) :
    ConditionThree G
      (recolor G old (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let final := recolor G old A (some i)
  have hEA : E ≠ A := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [← heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    rcases hc with huv' | hua
    · exact huv.ne huv'
    · subst a
      unfold IsTwoVertex at ha
      rw [hu] at ha
      omega
  have hfinalE : final E = none := by
    rw [show final E = old E by exact recolor_ne G old (some i) hEA]
    exact hE
  have hagree : ColoringsAgreeOff G ({A} : Set G.edgeSet) old final := by
    intro e he
    have heA : e ≠ A := by simpa using he
    simp [final, heA]
  apply ConditionThree.of_agreeOff G hold hagree
  intro x y p hp haffect hleft hright
  rcases haffect with ⟨e, heS, hex⟩ | ⟨e, heS, hey⟩
  · have heA : e = A := by simpa using heS
    subst e
    have hx : x = v ∨ x = a := by simpa [A] using hex.1
    rcases hx with hxv | hxa
    · subst x
      obtain ⟨j, hj⟩ := hleft E
        (by simpa [E] using leafEdge_externalAt_thread_start G hu huv p hp)
      rw [hfinalE] at hj
      simp at hj
    · have hxThree := hp.start_three
      unfold IsThreeVertex at hxThree
      unfold IsTwoVertex at ha
      rw [hxa] at hxThree
      omega
  · have heA : e = A := by simpa using heS
    subst e
    have hy : y = v ∨ y = a := by simpa [A] using hey.1
    rcases hy with hyv | hya
    · subst y
      obtain ⟨j, hj⟩ := hright E
        (by simpa [E] using leafEdge_externalAt_thread_end G hu huv p hp)
      rw [hfinalE] at hj
      simp at hj
    · have hyThree := hp.end_three
      unfold IsThreeVertex at hyThree
      unfold IsTwoVertex at ha
      rw [hya] at hyThree
      omega

/-- Condition 2 for the same move.  Apart from `a`, every affected
two-vertex is forced to be the continuation `r`; at `a` the move removes
its only possible incident matching edge.  It therefore suffices that the
new colour was already visible at `r` whenever `r` is a two-vertex. -/
theorem ConditionTwo.recolor_leaf_arm_first_of_other_three
    {u v a b r : V} (hu : G.degree u = 1) (hv : IsThreeVertex G v)
    (ha : IsTwoVertex G a) (hb : IsThreeVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b) (har : G.Adj a r)
    (hrv : r ≠ v) (hN : G.neighborFinset v = {u, a, b})
    (old : G.edgeSet → OneTwoColor 4) (gamma i : Fin 4)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hC : old (⟨s(a, r), har⟩ : G.edgeSet) = some gamma)
    (hrSeen : IsTwoVertex G r → VertexSeesInduced G old r i)
    (hold : ConditionTwo G old) :
    ConditionTwo G
      (recolor G old (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let final := recolor G old A (some i)
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne (fun h ↦ hrv h.symm)
  have hfinalA : final A = some i := by simp [final]
  have hfinalC : final C = some gamma := by
    change recolor G old A (some i) C = some gamma
    rw [recolor_ne G old (some i) hAC.symm]
    exact hC
  have hagree : ColoringsAgreeOff G ({A} : Set G.edgeSet) old final := by
    intro e he
    have heA : e ≠ A := by simpa using he
    simp [final, heA]
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  have hqa : q ≠ a := by
    intro hqa
    subst q
    obtain ⟨f, hf, haf⟩ := (vertexSeesMatching_iff G final a).mp hmatch
    rcases edge_eq_left_or_right_of_incident_two G ha hva.symm har hrv.symm
        f haf with hfA | hfC
    · have hfeq : f = A := by
        apply Subtype.ext
        simpa [A, Sym2.eq_swap] using hfA
      subst f
      rw [hfinalA] at hf
      simp at hf
    · have hfeq : f = C := Subtype.ext hfC
      subst f
      rw [hfinalC] at hf
      simp at hf
  have hmatchOld : VertexSeesMatching G old q := by
    obtain ⟨f, hf, hqf⟩ := (vertexSeesMatching_iff G final q).mp hmatch
    have hfA : f ≠ A := by
      intro hfa
      subst f
      rw [hfinalA] at hf
      simp at hf
    refine (vertexSeesMatching_iff G old q).mpr ⟨f, ?_, hqf⟩
    change recolor G old A (some i) f = none at hf
    rw [recolor_ne G old (some i) hfA] at hf
    exact hf
  have hqr : q = r := by
    rw [paletteAffectedBy_iff_inducedAffectedBy,
      inducedAffectedBy_singleton] at haffect
    obtain ⟨z, hzA, hqz⟩ := haffect
    have hz : z = v ∨ z = a := by simpa [A] using hzA
    rcases hz with hzv | hza
    · rcases hqz with hqv | hqv
      · have hqv' : q = v := hqv.trans hzv
        unfold IsTwoVertex at hq
        unfold IsThreeVertex at hv
        rw [hqv'] at hq
        omega
      · have hqN : q ∈ ({u, a, b} : Finset V) := by
          rw [← hN]
          exact (G.mem_neighborFinset v q).mpr (by simpa [hzv] using hqv.symm)
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
    · rcases hqz with hqa' | hqaAdj
      · exact False.elim (hqa (hqa'.trans hza))
      · have hqN : q ∈ ({v, r} : Finset V) := by
          rw [← neighborFinset_eq_pair_of_isTwoVertex G ha hva.symm har
            hrv.symm]
          exact (G.mem_neighborFinset a q).mpr (by simpa [hza] using hqaAdj.symm)
        have hcases : q = v ∨ q = r := by simpa using hqN
        rcases hcases with hqv | hqr
        · subst q
          unfold IsTwoVertex at hq
          unfold IsThreeVertex at hv
          omega
        · exact hqr
  apply hold q hq hmatchOld
  intro j
  by_cases hji : j = i
  · subst j
    simpa [hqr] using hrSeen (hqr ▸ hq)
  · exact vertexSeesInduced_of_recolor_leafEdge_other_four G hva old hji
      (by simpa [final, A] using hall j)

/-- Variant of the preceding lemma when the other branch vertex `b` is
also a two-vertex.  Its one additional local obligation is exposed as the
explicit safety hypothesis `hsafeB`. -/
theorem ConditionTwo.recolor_leaf_arm_first_of_other_two
    {u v a b r : V} (hu : G.degree u = 1) (hv : IsThreeVertex G v)
    (ha : IsTwoVertex G a) (hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b) (har : G.Adj a r)
    (hrv : r ≠ v) (hN : G.neighborFinset v = {u, a, b})
    (old : G.edgeSet → OneTwoColor 4) (gamma i : Fin 4)
    (hC : old (⟨s(a, r), har⟩ : G.edgeSet) = some gamma)
    (hrSeen : IsTwoVertex G r → VertexSeesInduced G old r i)
    (hold : ConditionTwo G old)
    (hsafeB : ¬ (VertexSeesMatching G
        (recolor G old (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G old (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) b j)) :
    ConditionTwo G
      (recolor G old (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let final := recolor G old A (some i)
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne (fun h ↦ hrv h.symm)
  have hfinalA : final A = some i := by simp [final]
  have hfinalC : final C = some gamma := by
    change recolor G old A (some i) C = some gamma
    rw [recolor_ne G old (some i) hAC.symm]
    exact hC
  have hagree : ColoringsAgreeOff G ({A} : Set G.edgeSet) old final := by
    intro e he
    have heA : e ≠ A := by simpa using he
    simp [final, heA]
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  by_cases hqb : q = b
  · subst q
    exact hsafeB ⟨by simpa [final, A] using hmatch,
      by simpa [final, A] using hall⟩
  have hqa : q ≠ a := by
    intro hqa
    subst q
    obtain ⟨f, hf, haf⟩ := (vertexSeesMatching_iff G final a).mp hmatch
    rcases edge_eq_left_or_right_of_incident_two G ha hva.symm har hrv.symm
        f haf with hfA | hfC
    · have hfeq : f = A := by
        apply Subtype.ext
        simpa [A, Sym2.eq_swap] using hfA
      subst f
      rw [hfinalA] at hf
      simp at hf
    · have hfeq : f = C := Subtype.ext hfC
      subst f
      rw [hfinalC] at hf
      simp at hf
  have hmatchOld : VertexSeesMatching G old q := by
    obtain ⟨f, hf, hqf⟩ := (vertexSeesMatching_iff G final q).mp hmatch
    have hfA : f ≠ A := by
      intro hfa
      subst f
      rw [hfinalA] at hf
      simp at hf
    refine (vertexSeesMatching_iff G old q).mpr ⟨f, ?_, hqf⟩
    change recolor G old A (some i) f = none at hf
    rw [recolor_ne G old (some i) hfA] at hf
    exact hf
  have hqr : q = r := by
    rw [paletteAffectedBy_iff_inducedAffectedBy,
      inducedAffectedBy_singleton] at haffect
    obtain ⟨z, hzA, hqz⟩ := haffect
    have hz : z = v ∨ z = a := by simpa [A] using hzA
    rcases hz with hzv | hza
    · rcases hqz with hqv | hqv
      · have hqv' : q = v := hqv.trans hzv
        unfold IsTwoVertex at hq
        unfold IsThreeVertex at hv
        rw [hqv'] at hq
        omega
      · have hqN : q ∈ ({u, a, b} : Finset V) := by
          rw [← hN]
          exact (G.mem_neighborFinset v q).mpr (by simpa [hzv] using hqv.symm)
        have hcases : q = u ∨ q = a ∨ q = b := by simpa using hqN
        rcases hcases with hqu | hqa' | hqb'
        · subst q
          unfold IsTwoVertex at hq
          omega
        · exact False.elim (hqa hqa')
        · exact False.elim (hqb hqb')
    · rcases hqz with hqa' | hqaAdj
      · exact False.elim (hqa (hqa'.trans hza))
      · have hqN : q ∈ ({v, r} : Finset V) := by
          rw [← neighborFinset_eq_pair_of_isTwoVertex G ha hva.symm har
            hrv.symm]
          exact (G.mem_neighborFinset a q).mpr (by simpa [hza] using hqaAdj.symm)
        have hcases : q = v ∨ q = r := by simpa using hqN
        rcases hcases with hqv | hqr
        · subst q
          unfold IsTwoVertex at hq
          unfold IsThreeVertex at hv
          omega
        · exact hqr
  apply hold q hq hmatchOld
  intro j
  by_cases hji : j = i
  · subst j
    simpa [hqr] using hrSeen (hqr ▸ hq)
  · exact vertexSeesInduced_of_recolor_leafEdge_other_four G hva old hji
      (by simpa [final, A] using hall j)

/-- At the other branch vertex `b`, moving colour `i` from the leaf edge
to the guard edge has the same local effect: both edges have endpoint `v`
at distance one from `b`, and neither is incident with `b`.  Thus safety
of the direct extension implies safety of the guard recolouring. -/
theorem guard_safe_at_other_arm_of_direct_safe
    {u v a b : V} (huv : G.Adj u v) (hva : G.Adj v a)
    (hvb : G.Adj v b) (hbu : b ≠ u) (hab : a ≠ b)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hsafe : ¬ (VertexSeesMatching G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j)) :
    ¬ (VertexSeesMatching G
        (recolor G old (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G old (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) b j) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let direct := recolor G old E (some i)
  let guard := recolor G old A (some i)
  have hbE : b ∉ (E : Sym2 V) := by
    intro hbE
    have hc : b = u ∨ b = v := by simpa [E] using hbE
    exact hc.elim hbu hvb.ne.symm
  have hbA : b ∉ (A : Sym2 V) := by
    intro hbA
    have hc : b = v ∨ b = a := by simpa [A] using hbA
    exact hc.elim hvb.ne.symm (fun h ↦ hab h.symm)
  rintro ⟨hmatch, hall⟩
  apply hsafe
  constructor
  · obtain ⟨f, hf, hbf⟩ := (vertexSeesMatching_iff G guard b).mp hmatch
    have hfA : f ≠ A := by
      intro hfa
      subst f
      simp [guard] at hf
    have hfOld : old f = none := by
      change recolor G old A (some i) f = none at hf
      rw [recolor_ne G old (some i) hfA] at hf
      exact hf
    have hfE : f ≠ E := by
      intro hfe
      subst f
      exact hbE hbf
    apply (vertexSeesMatching_iff G direct b).mpr
    refine ⟨f, ?_, hbf⟩
    change recolor G old E (some i) f = none
    rw [recolor_ne G old (some i) hfE]
    exact hfOld
  · intro j
    obtain ⟨f, hf, z, hzf, hbz⟩ :=
      (vertexSeesInduced_iff G guard b j).mp (hall j)
    by_cases hfA : f = A
    · subst f
      have hji : j = i := by
        have hs : some i = some j := by simpa [guard] using hf
        exact (Option.some.inj hs).symm
      subst j
      apply (vertexSeesInduced_iff G direct b i).mpr
      exact ⟨E, by simp [direct], v, by simp [E], Or.inr hvb.symm⟩
    · have hfOld : old f = some j := by
        change recolor G old A (some i) f = some j at hf
        rw [recolor_ne G old (some i) hfA] at hf
        exact hf
      have hfE : f ≠ E := by
        intro hfe
        subst f
        rw [show old E = none by simpa [E] using hE] at hfOld
        simp at hfOld
      apply (vertexSeesInduced_iff G direct b j).mpr
      refine ⟨f, ?_, z, hzf, hbz⟩
      change recolor G old E (some i) f = some j
      rw [recolor_ne G old (some i) hfE]
      exact hfOld

/-- Condition 2 for the matching shift when the other branch vertex is a
two-vertex.  The proof is the same locality argument as the three-vertex
version, with the one possible check at `b` supplied explicitly. -/
theorem ConditionTwo.shift_matching_along_leaf_arm_other_two
    {u v a b r : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (_hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (har : G.Adj a r) (hau : a ≠ u) (hrv : r ≠ v) (hru : r ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (old : G.edgeSet → OneTwoColor 4) (gamma i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hC : old (⟨s(a, r), har⟩ : G.edgeSet) = some gamma)
    (hig : i ≠ gamma)
    (hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old)
    (hold : ConditionTwo G old)
    (hsafeB : ¬ (VertexSeesMatching G
        (recolor G
          (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
          (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G
          (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
          (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) b j)) :
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
    exact hc.elim hva.ne (fun h ↦ hrv h.symm)
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
  by_cases hqb : q = b
  · subst q
    exact hsafeB ⟨by simpa [final, afterC, A, C] using hmatch,
      by simpa [final, afterC, A, C] using hall⟩
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
        rcases hcases with hqu | hqa' | hqb'
        · subst q
          unfold IsTwoVertex at hq
          omega
        · exact False.elim (hqa hqa')
        · exact False.elim (hqb hqb')
    · have hqaClose : q = a ∨ G.Adj q a := by simpa [hza] using hqz
      rcases hqaClose with hqa' | hqaAdj
      · exact False.elim (hqa hqa')
      · have hqN : q ∈ ({v, r} : Finset V) := by
          rw [← neighborFinset_eq_pair_of_isTwoVertex G ha hva.symm har
            hrv.symm]
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

/-- Safety at the other arm transfers from the direct leaf extension to
the matching shift, provided `b` is not incident with any shifted edge.
The shift only replaces the visible occurrence of `i` on `E` by one on
`A`, and removes (rather than adds) the induced colour on `C`. -/
theorem shift_safe_at_other_arm_of_direct_safe
    {u v a b r : V} (huv : G.Adj u v) (hva : G.Adj v a)
    (hvb : G.Adj v b) (har : G.Adj a r)
    (hbE : b ∉ (s(u, v) : Sym2 V))
    (hbA : b ∉ (s(v, a) : Sym2 V))
    (hbC : b ∉ (s(a, r) : Sym2 V))
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hsafe : ¬ (VertexSeesMatching G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j)) :
    ¬ (VertexSeesMatching G
        (recolor G
          (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
          (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G
          (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
          (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) b j) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let direct := recolor G old E (some i)
  let shift := recolor G (recolor G old C none) A (some i)
  have hbE' : b ∉ (E : Sym2 V) := by simpa [E] using hbE
  have hbA' : b ∉ (A : Sym2 V) := by simpa [A] using hbA
  have hbC' : b ∉ (C : Sym2 V) := by simpa [C] using hbC
  rintro ⟨hmatch, hall⟩
  apply hsafe
  constructor
  · obtain ⟨f, hf, hbf⟩ := (vertexSeesMatching_iff G shift b).mp hmatch
    have hfA : f ≠ A := by
      intro hfa
      subst f
      simp [shift] at hf
    have hfC : f ≠ C := by
      intro hfc
      subst f
      exact hbC' hbf
    have hfOld : old f = none := by
      change recolor G (recolor G old C none) A (some i) f = none at hf
      rw [recolor_ne G (recolor G old C none) (some i) hfA] at hf
      rw [recolor_ne G old none hfC] at hf
      exact hf
    have hfE : f ≠ E := by
      intro hfe
      subst f
      exact hbE' hbf
    apply (vertexSeesMatching_iff G direct b).mpr
    refine ⟨f, ?_, hbf⟩
    change recolor G old E (some i) f = none
    rw [recolor_ne G old (some i) hfE]
    exact hfOld
  · intro j
    obtain ⟨f, hf, z, hzf, hbz⟩ :=
      (vertexSeesInduced_iff G shift b j).mp (hall j)
    by_cases hfA : f = A
    · subst f
      have hji : j = i := by
        have hs : some i = some j := by simpa [shift] using hf
        exact (Option.some.inj hs).symm
      subst j
      apply (vertexSeesInduced_iff G direct b i).mpr
      exact ⟨E, by simp [direct], v, by simp [E], Or.inr hvb.symm⟩
    · have hfAfter : recolor G old C none f = some j := by
        change recolor G (recolor G old C none) A (some i) f = some j at hf
        rw [recolor_ne G (recolor G old C none) (some i) hfA] at hf
        exact hf
      have hfC : f ≠ C := by
        intro hfc
        subst f
        simp at hfAfter
      have hfOld : old f = some j := by
        rw [recolor_ne G old none hfC] at hfAfter
        exact hfAfter
      have hfE : f ≠ E := by
        intro hfe
        subst f
        rw [show old E = none by simpa [E] using hE] at hfOld
        simp at hfOld
      apply (vertexSeesInduced_iff G direct b j).mpr
      refine ⟨f, ?_, z, hzf, hbz⟩
      change recolor G old E (some i) f = some j
      rw [recolor_ne G old (some i) hfE]
      exact hfOld

/-- In the displayed two-thread `v-a-r-t`, if its last edge is matching,
an available colour for the missing leaf edge is absent from the old
visibility palette of `a`.  The five possible visible edges are exhausted
by the local path computation. -/
theorem not_seen_at_matching_arm_of_available_last_matching
    {u v a b r t : V}
    (huv : G.Adj u v) (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u)
    (ha : IsTwoVertex G a) (har : G.Adj a r) (hrv : r ≠ v)
    (hr : IsTwoVertex G r) (hrt : G.Adj r t) (hta : t ≠ a)
    (hN : G.neighborFinset v = {u, a, b})
    (old : G.edgeSet → OneTwoColor 4) (beta i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : old (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (hD : old (⟨s(r, t), hrt⟩ : G.edgeSet) = none)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) :
    ¬ VertexSeesInduced G old a i := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let B : G.edgeSet := ⟨s(v, b), hvb⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let D : G.edgeSet := ⟨s(r, t), hrt⟩
  have hCE : C ≠ E := by
    intro heq
    have haE : a ∈ (E : Sym2 V) := by rw [← heq]; simp [C]
    have hc : a = u ∨ a = v := by simpa [E] using haE
    exact hc.elim hau (fun hav ↦ hva.ne hav.symm)
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hiBeta : i ≠ beta :=
    available_leaf_colour_ne_other_branch_colour G huv hvb hbu old beta i
      (by simpa [B] using hB) (by simpa [E] using hi)
  intro hseen
  obtain ⟨f, hf, x, hxf, hax⟩ :=
    (vertexSeesInduced_iff G old a i).mp hseen
  rcases leafTwoOne_visible_edge_cases G huv hva hvb ha har hrv hr hrt hta
      hN f hxf hax with rfl | rfl | rfl | rfl | rfl
  · rw [show old E = none by simpa [E] using hE] at hf
    simp at hf
  · rw [show old A = none by simpa [A] using hA] at hf
    simp at hf
  · have hEq : some beta = some i := by simpa [B] using hB.symm.trans hf
    exact hiBeta (Option.some.inj hEq.symm)
  · have hsep := (colorAvailableOn_some_iff G
        (RetainedEdges (deleteLeafEdge G huv) G) old E i).mp
        (by simpa [E] using hi) C hCD hCE (by simpa [C] using hf)
    exact hsep.2 ⟨v, by simp [E], a, by simp [C], hva⟩
  · rw [show old D = none by simpa [D] using hD] at hf
    simp at hf

/-- A genuine Condition-3 failure on the displayed two-thread forces its
last edge to be matching.  Moreover the new leaf colour already occurs on
an external edge at the far endpoint, so it was visible at `r` before the
recolouring. -/
theorem leaf_c3_failure_two_two_forces_last_matching_and_seen
    {u v a b r t : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (ha : IsTwoVertex G a) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v)
    (hrt : G.Adj r t) (hta : t ≠ a)
    (old : G.edgeSet → OneTwoColor 4) (beta i : Fin 4)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : old (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (hC : old (⟨s(a, r), har⟩ : G.edgeSet) ≠ none)
    (hsat : OneSaturated G old) (hthree : ConditionThree G old)
    (hfail : ¬ ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i))) :
    old (⟨s(r, t), hrt⟩ : G.edgeSet) = none ∧
      VertexSeesInduced G old r i := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let D : G.edgeSet := ⟨s(r, t), hrt⟩
  let final := recolor G old E (some i)
  obtain ⟨y, p, hp, hfirst, hleft, hright, heq⟩ :=
    leafC3CriticalFailure_of_not_conditionThree G hu huv hva hau old i hA
      hthree (by simpa [final, E] using hfail)
  have htwo : p.getVert 2 = r :=
    twoThread_getVert_two_eq_of_firstEdge_and_two G ha hva har hrv p hp hfirst
  have hyt : y = t :=
    twoThread_endpoint_eq_of_firstEdge_and_two_two G ha hr hva har hrv hrt hta
      p hp hfirst
  have hlast : threadLastEdge G p hp = D := by
    apply Subtype.ext
    simp [threadLastEdge, D, htwo, hyt]
  have hfar := twoThread_far_endpoint_ne_leaf_ends G hu p hp
  have hyu : y ≠ u := hfar.1
  have hyv : y ≠ v := hfar.2
  have hDnone : old D = none := by
    by_contra hDn
    obtain ⟨d, hDd⟩ := Option.ne_none_iff_exists'.mp hDn
    obtain ⟨f, hfnone, x, hxD, hxf⟩ := hsat D hDn
    have hx : x = r ∨ x = t := by simpa [D] using hxD
    rcases hx with hxr | hxt
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
        rw [hDd] at hfnone
        simp at hfnone
    · have hxy : x = y := hxt.trans hyt.symm
      subst x
      have hfD : f ≠ D := by
        intro hfd
        subst f
        rw [hDd] at hfnone
        simp at hfnone
      have hfE : f ≠ E := by
        intro hfe
        subst f
        have hymem : y ∈ (E : Sym2 V) := by simpa [hyt] using hxf
        have hy : y = u ∨ y = v := by simpa [E] using hymem
        exact hy.elim hyu hyv
      have hfinalf : final f = none := by
        change recolor G old E (some i) f = none
        rw [recolor_ne G old (some i) hfE]
        exact hfnone
      have hext : IsExternalAt G y (threadLastEdge G p hp) f := by
        refine ⟨by simpa [hyt] using hxf, ?_⟩
        intro hEq
        exact hfD (hEq.trans hlast)
      obtain ⟨j, hj⟩ := hright f hext
      have hj' : final f = some j := by simpa [final, E] using hj
      rw [hfinalf] at hj'
      simp at hj'
  refine ⟨by simpa [D] using hDnone, ?_⟩
  have hpalette : ExternalInducedColors G final v A =
      ({i, beta} : Set (Fin 4)) := by
    simpa [final, E, A] using
      externalInducedColors_recolor_leaf_at_matching_guard G huv hva hvb hau
        hbu hab hN old beta i hB
  have hiFar : i ∈ ExternalInducedColors G final y
      (threadLastEdge G p hp) := by
    rw [← heq, hfirst, hpalette]
    simp
  obtain ⟨f, hext, hfi⟩ := hiFar
  have hfE : f ≠ E := by
    intro hfe
    subst f
    have hymem : y ∈ (E : Sym2 V) := hext.1
    have hy : y = u ∨ y = v := by simpa [E] using hymem
    exact hy.elim hyu hyv
  have hfold : old f = some i := by
    change recolor G old E (some i) f = some i at hfi
    rw [recolor_ne G old (some i) hfE] at hfi
    exact hfi
  apply (vertexSeesInduced_iff G old r i).mpr
  exact ⟨f, hfold, y, hext.1, Or.inr (by simpa [hyt] using hrt)⟩

/-- The critical two-thread subcase of the unique-colour branch.  Rather
than placing `i` on the leaf edge, leave that edge matching and move `i`
onto the old matching guard `va`.  The Condition-3 failure itself supplies
the far matching edge and the visibility fact needed by Condition 2. -/
theorem exists_goodFour_leaf_recolor_guard_of_c3_failure
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
    (beta i : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hfail : ¬ ConditionThree G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i))) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let D : G.edgeSet := ⟨s(r, t), hrt⟩
  let final := recolor G base A (some i)
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
    have haE : a ∈ (E : Sym2 V) := by rw [← heq]; simp [C]
    have hc : a = u ∨ a = v := by simpa [E] using haE
    exact hc.elim hau (fun hav ↦ hva.ne hav.symm)
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne (fun h ↦ hrv h.symm)
  have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base := by
    simpa [base] using transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hCne : base C ≠ none := by
    intro hCnone
    have hp := hvalidD A hAD C hCD hAC
    have hdisj : EndpointDisjoint G A C := by
      simpa [base, A, C, hA, hCnone] using hp
    exact hdisj a (by simp [A]) (by simp [C])
  obtain ⟨gamma, hCgamma⟩ := Option.ne_none_iff_exists'.mp hCne
  have hEnone : base E = none := by
    simp [base, E, leafBaseFour, transportColoringToSupergraph]
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hsatBase : OneSaturated G base :=
    oneSaturated_leafBaseFour G huv small hsmall.oneSaturated
  obtain ⟨hDnone, hseenR⟩ :=
    leaf_c3_failure_two_two_forces_last_matching_and_seen G hu huv ha hr hva
      hvb hau hbu hab hN har hrv hrt hta base beta i
      (by simpa [base, A] using hA) (by simpa [base] using hB)
      (by simpa [C] using hCne) hsatBase hbaseThree
      (by simpa [base, E] using hfail)
  have hmissing : ¬ VertexSeesInduced G base a i :=
    not_seen_at_matching_arm_of_available_last_matching G huv hva hvb hau hbu
      ha har hrv hr hrt hta hN base beta i hEnone
      (by simpa [base, A] using hA) (by simpa [base] using hB)
      (by simpa [base, D] using hDnone) (by simpa [base, E] using hi)
  have hvalid : IsOneTwoColoring G final := by
    simpa [final, base, A] using
      isOneTwoColoring_recolor_leaf_arm_first_of_available G hu huv hva hau
        base i hEnone (by simpa [base, A] using hA)
        (by simpa [base, E] using hi) hmissing hvalidD
  have hsat : OneSaturated G final := by
    simpa [final, base, A] using
      OneSaturated.recolor_leaf_arm_first_of_far_matching G hu huv ha hva har
        hrv base i hEnone (by simpa [base, A] using hA) D
        (by simpa [base, D] using hDnone) (by simp [D]) hsatBase
  have htwo : ConditionTwo G final := by
    simpa [final, base, A, C] using
      ConditionTwo.recolor_leaf_arm_first_of_other_three G hu hv ha hb hva hvb
        har hrv hN base gamma i (by simpa [base, A] using hA)
        (by simpa [base, C] using hCgamma) (fun _ ↦ hseenR) hbaseTwo
  have hthree : ConditionThree G final := by
    simpa [final, base, A] using
      ConditionThree.recolor_leaf_arm_first_with_leaf_matching G hu huv ha hva
        base i hEnone hbaseThree
  exact ⟨final, hvalid, hsat, htwo, hthree⟩

/-- The guard-recolouring repair with a two-vertex on the other arm.  Its
only extra premise is that the chosen direct leaf colour is safe at that
other two-vertex. -/
theorem exists_goodFour_leaf_recolor_guard_of_c3_failure_other_two
    (hsub : IsSubcubic G)
    {u v a b r t : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsTwoVertex G b) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v)
    (hrt : G.Adj r t) (hta : t ≠ a)
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
    (hsafeB : ¬ (VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j))
    (hfail : ¬ ConditionThree G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i))) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let D : G.edgeSet := ⟨s(r, t), hrt⟩
  let final := recolor G base A (some i)
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
    exact hc.elim hva.ne (fun h ↦ hrv h.symm)
  have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base := by
    simpa [base] using transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hCne : base C ≠ none := by
    intro hCnone
    have hp := hvalidD A hAD C hCD hAC
    have hdisj : EndpointDisjoint G A C := by
      simpa [base, A, C, hA, hCnone] using hp
    exact hdisj a (by simp [A]) (by simp [C])
  obtain ⟨gamma, hCgamma⟩ := Option.ne_none_iff_exists'.mp hCne
  have hEnone : base E = none := by
    simp [base, E, leafBaseFour, transportColoringToSupergraph]
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hsatBase : OneSaturated G base :=
    oneSaturated_leafBaseFour G huv small hsmall.oneSaturated
  obtain ⟨hDnone, hseenR⟩ :=
    leaf_c3_failure_two_two_forces_last_matching_and_seen G hu huv ha hr hva
      hvb hau hbu hab hN har hrv hrt hta base beta i
      (by simpa [base, A] using hA) (by simpa [base] using hB)
      (by simpa [C] using hCne) hsatBase hbaseThree
      (by simpa [base, E] using hfail)
  have hmissing : ¬ VertexSeesInduced G base a i :=
    not_seen_at_matching_arm_of_available_last_matching G huv hva hvb hau hbu
      ha har hrv hr hrt hta hN base beta i hEnone
      (by simpa [base, A] using hA) (by simpa [base] using hB)
      (by simpa [base, D] using hDnone) (by simpa [base, E] using hi)
  have hsafeGuard := guard_safe_at_other_arm_of_direct_safe G huv hva hvb hbu
    hab base i hEnone (by simpa [base, E] using hsafeB)
  have hvalid : IsOneTwoColoring G final := by
    simpa [final, base, A] using
      isOneTwoColoring_recolor_leaf_arm_first_of_available G hu huv hva hau
        base i hEnone (by simpa [base, A] using hA)
        (by simpa [base, E] using hi) hmissing hvalidD
  have hsat : OneSaturated G final := by
    simpa [final, base, A] using
      OneSaturated.recolor_leaf_arm_first_of_far_matching G hu huv ha hva har
        hrv base i hEnone (by simpa [base, A] using hA) D
        (by simpa [base, D] using hDnone) (by simp [D]) hsatBase
  have htwo : ConditionTwo G final := by
    simpa [final, base, A, C] using
      ConditionTwo.recolor_leaf_arm_first_of_other_two G hu hv ha hb hva hvb
        har hrv hN base gamma i (by simpa [base, C] using hCgamma)
        (fun _ ↦ hseenR) hbaseTwo (by simpa [base, A] using hsafeGuard)
  have hthree : ConditionThree G final := by
    simpa [final, base, A] using
      ConditionThree.recolor_leaf_arm_first_with_leaf_matching G hu huv ha hva
        base i hEnone hbaseThree
  exact ⟨final, hvalid, hsat, htwo, hthree⟩

/-- Direct assembly for two degree-two branch vertices once their two
local palette obligations and Condition 3 are known. -/
theorem goodFour_leaf_three_both_two_of_available_safe
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (i : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hsafeA : ¬ (VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j))
    (hsafeB : ¬ (VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j))
    (hthree : ConditionThree G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i))) :
    GoodFour G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    rcases hc with huv' | hua
    · exact huv.ne huv'
    · unfold IsTwoVertex at ha
      rw [← hua, hu] at ha
      omega
  have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have htwo : ConditionTwo G (recolor G base E (some i)) := by
    apply conditionTwo_recolor_leafEdge_at_three_neighbor_four G hu huv hv hva
      hvb hN base hbaseTwo i
    · intro _ hmatch hall
      exact hsafeA ⟨by simpa [base, E] using hmatch,
        by simpa [base, E] using hall⟩
    · intro _ hmatch hall
      exact hsafeB ⟨by simpa [base, E] using hmatch,
        by simpa [base, E] using hall⟩
  exact goodFour_recolor_leafEdge_of_available G hu huv small hsmall A hAD
    (by simpa [base, A] using hA) (by simp [A]) i
    (by simpa [base, E] using hi) (by simpa [base, E] using htwo)
    (by simpa [base, E] using hthree)

/-- Generic matching-shift assembly for the two/two branch.  The caller
supplies the two semantic facts which depend on the continuation: the new
guard colour is absent at `a`, and no old matching edge meets `r`. -/
theorem exists_goodFour_leaf_shift_other_two
    (hsub : IsSubcubic G)
    {u v a b r : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b) (hbr : b ≠ r)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (i : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hmissing : ¬ VertexSeesInduced G (leafBaseFour G huv small) a i)
    (hnoMatchingR : ∀ f : G.edgeSet,
      leafBaseFour G huv small f = none → r ∈ (f : Sym2 V) → False)
    (hsafeB : ¬ (VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j))
    (hthreeShift : ConditionThree G
      (recolor G
        (recolor G (leafBaseFour G huv small)
          (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i))) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let final := recolor G (recolor G base C none) A (some i)
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
    have haE : a ∈ (E : Sym2 V) := by rw [← heq]; simp [C]
    have hc : a = u ∨ a = v := by simpa [E] using haE
    exact hc.elim hau (fun hav ↦ hva.ne hav.symm)
  have hAC : A ≠ C := by
    intro heq
    have hvC : v ∈ (C : Sym2 V) := by rw [← heq]; simp [A]
    have hc : v = a ∨ v = r := by simpa [C] using hvC
    exact hc.elim hva.ne (fun h ↦ hrv h.symm)
  have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base := by
    simpa [base] using transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hCne : base C ≠ none := by
    intro hCnone
    have hp := hvalidD A hAD C hCD hAC
    have hdisj : EndpointDisjoint G A C := by
      simpa [base, A, C, hA, hCnone] using hp
    exact hdisj a (by simp [A]) (by simp [C])
  obtain ⟨gamma, hCgamma⟩ := Option.ne_none_iff_exists'.mp hCne
  have hEnone : base E = none := by
    simp [base, E, leafBaseFour, transportColoringToSupergraph]
  have higamma : i ≠ gamma := by
    intro hig
    subst gamma
    apply hmissing
    apply (vertexSeesInduced_iff G base a i).mpr
    exact ⟨C, by simpa [C] using hCgamma, a, by simp [C], Or.inl rfl⟩
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hsafeShift : ¬ (VertexSeesMatching G final b ∧
      ∀ j : Fin 4, VertexSeesInduced G final b j) := by
    have hbE : b ∉ (s(u, v) : Sym2 V) := by
      simp only [Sym2.mem_iff]
      rintro (h | h)
      · exact hbu h
      · exact hvb.ne.symm h
    have hbA : b ∉ (s(v, a) : Sym2 V) := by
      simp only [Sym2.mem_iff]
      rintro (h | h)
      · exact hvb.ne.symm h
      · exact hab h.symm
    have hbC : b ∉ (s(a, r) : Sym2 V) := by
      simp only [Sym2.mem_iff]
      rintro (h | h)
      · exact hab h.symm
      · exact hbr h
    simpa [final, base, E, A, C] using
      shift_safe_at_other_arm_of_direct_safe G huv hva hvb har hbE hbA hbC
        base i hEnone (by simpa [base, E] using hsafeB)
  have hvalid : IsOneTwoColoring G final := by
    simpa [final, base, A, C] using
      isOneTwoColoring_leaf_arm_shift_of_available G hu huv ha hva har hau hrv
        hru base i hEnone (by simpa [base, A] using hA)
        (by simpa [base, E] using hi) hmissing hnoMatchingR hvalidD
  have htwo : ConditionTwo G final := by
    simpa [final, base, A, C] using
      ConditionTwo.shift_matching_along_leaf_arm_other_two G hu huv hv ha hb
        hva hvb har hau hrv hru hN base gamma i hEnone
        (by simpa [base, C] using hCgamma) higamma hvalidD hbaseTwo
        (by simpa [final] using hsafeShift)
  refine ⟨final, ?_⟩
  exact goodFour_leaf_arm_shift_of_valid_conditions G huv hva har hau hrv hru
    small hsmall gamma i hA (by simpa [base, C] using hCgamma)
    (by simpa [final] using hvalid) (by simpa [final] using htwo)
    (by simpa [final, base, A, C] using hthreeShift)

/-- Generic guard-recolouring assembly for the two/two branch.  A matching
edge visible at the far endpoint preserves matching saturation, while the
explicit local safety premise controls the other two-vertex. -/
theorem exists_goodFour_leaf_guard_other_two
    (hsub : IsSubcubic G)
    {u v a b r : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (i : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hmissing : ¬ VertexSeesInduced G (leafBaseFour G huv small) a i)
    (m : G.edgeSet)
    (hm : leafBaseFour G huv small m = none)
    (hrm : r ∈ (m : Sym2 V))
    (hseenR : IsTwoVertex G r →
      VertexSeesInduced G (leafBaseFour G huv small) r i)
    (hsafeB : ¬ (VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let final := recolor G base A (some i)
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
    exact hc.elim hva.ne (fun h ↦ hrv h.symm)
  have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base := by
    simpa [base] using transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hCne : base C ≠ none := by
    intro hCnone
    have hp := hvalidD A hAD C hCD hAC
    have hdisj : EndpointDisjoint G A C := by
      simpa [base, A, C, hA, hCnone] using hp
    exact hdisj a (by simp [A]) (by simp [C])
  obtain ⟨gamma, hCgamma⟩ := Option.ne_none_iff_exists'.mp hCne
  have hEnone : base E = none := by
    simp [base, E, leafBaseFour, transportColoringToSupergraph]
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hsatBase : OneSaturated G base :=
    oneSaturated_leafBaseFour G huv small hsmall.oneSaturated
  have hsafeGuard := guard_safe_at_other_arm_of_direct_safe G huv hva hvb hbu
    hab base i hEnone (by simpa [base, E] using hsafeB)
  have hvalid : IsOneTwoColoring G final := by
    simpa [final, base, A] using
      isOneTwoColoring_recolor_leaf_arm_first_of_available G hu huv hva hau
        base i hEnone (by simpa [base, A] using hA)
        (by simpa [base, E] using hi) hmissing hvalidD
  have hsat : OneSaturated G final := by
    simpa [final, base, A] using
      OneSaturated.recolor_leaf_arm_first_of_far_matching G hu huv ha hva har
        hrv base i hEnone (by simpa [base, A] using hA) m
        (by simpa [base] using hm) hrm hsatBase
  have htwo : ConditionTwo G final := by
    simpa [final, base, A, C] using
      ConditionTwo.recolor_leaf_arm_first_of_other_two G hu hv ha hb hva hvb
        har hrv hN base gamma i (by simpa [base, C] using hCgamma)
        hseenR hbaseTwo (by simpa [base, A] using hsafeGuard)
  have hthree : ConditionThree G final := by
    simpa [final, base, A] using
      ConditionThree.recolor_leaf_arm_first_with_leaf_matching G hu huv ha hva
        base i hEnone hbaseThree
  exact ⟨final, hvalid, hsat, htwo, hthree⟩

/-- Two known matching edges, one on each of the two nonleaf arms, remove
two elements from the complete support of active leaf-edge blockers. -/
theorem card_activeBlockers_leafEdge_add_two_le_three_four
    {u v a b s : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hbs : G.Adj b s)
    (hN : G.neighborFinset v = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hAnone : colour (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hFnone : colour (⟨s(b, s), hbs⟩ : G.edgeSet) = none)
    (hAF : (⟨s(v, a), hva⟩ : G.edgeSet) ≠
      (⟨s(b, s), hbs⟩ : G.edgeSet)) :
    (activeInducedBlockerEdgesOn G
        (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet)).card + 2 ≤
      G.degree a + G.degree b := by
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let F : G.edgeSet := ⟨s(b, s), hbs⟩
  let S : Finset G.edgeSet :=
    incidentEdgeFinset G a ∪ incidentEdgeFinset G b
  have hsub : activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) ⊆ S := by
    simpa [S] using
      activeBlockers_leafEdge_subset_other_incidence_three_four G hu huv hva
        hvb hN (colour := colour)
  have hsubErase : activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) ⊆ (S.erase A).erase F := by
    intro f hf
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hsub hf⟩⟩
    · intro hfF
      subst f
      exact ((mem_activeInducedBlockerEdgesOn G
        (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet) F).mp hf).2.2.2
          (by simpa [F] using hFnone)
    · intro hfA
      subst f
      exact ((mem_activeInducedBlockerEdgesOn G
        (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet) A).mp hf).2.2.2
          (by simpa [A] using hAnone)
  have hAmem : A ∈ S := by
    apply Finset.mem_union_left
    exact (mem_incidentEdgeFinset (G := G)).mpr (by simp [A])
  have hFmem : F ∈ S := by
    apply Finset.mem_union_right
    exact (mem_incidentEdgeFinset (G := G)).mpr (by simp [F])
  have hFmemErase : F ∈ S.erase A := by
    exact Finset.mem_erase.mpr ⟨by simpa [A, F] using hAF.symm, hFmem⟩
  have hScard : S.card ≤ G.degree a + G.degree b := by
    calc
      S.card ≤ (incidentEdgeFinset G a).card +
          (incidentEdgeFinset G b).card := Finset.card_union_le _ _
      _ = G.degree a + G.degree b := by
        rw [card_incidentEdgeFinset, card_incidentEdgeFinset]
  have hcardErase : ((S.erase A).erase F).card + 2 = S.card := by
    have hEraseF : ((S.erase A).erase F).card + 1 =
        (S.erase A).card := by
      rw [Finset.card_erase_of_mem hFmemErase]
      have hpos : 0 < (S.erase A).card :=
        Finset.card_pos.mpr ⟨F, hFmemErase⟩
      omega
    have hEraseA : (S.erase A).card + 1 = S.card := by
      rw [Finset.card_erase_of_mem hAmem]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨A, hAmem⟩
      omega
    omega
  calc
    (activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet)).card + 2 ≤
        ((S.erase A).erase F).card + 2 := Nat.add_le_add_right
          (Finset.card_le_card hsubErase) 2
    _ = S.card := hcardErase
    _ ≤ G.degree a + G.degree b := hScard

/-- A single available colour suffices when the matching arm continues
through a second two-vertex and the other branch ends at a three-vertex.
The direct extension works unless it violates Condition 2 or 3; fullness
is repaired by the matching shift, and a Condition-3 failure is repaired
by moving the colour to the matching guard. -/
theorem exists_goodFour_leaf_three_matching_two_other_three_at_two_continuation
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
    (beta i : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let direct := recolor G base E (some i)
  by_cases hthree : ConditionThree G direct
  · by_cases hall : ∀ j : Fin 4, VertexSeesInduced G direct a j
    · exact exists_goodFour_leaf_shift_of_full_at_two_continuation G hsub
        hu huv hv ha hb hr hva hvb hau hrv hN har small hsmall hA i
        (by simpa [base, E] using hi) (by simpa [direct, base, E] using hall)
    · have hbNot : ¬ IsTwoVertex G b := by
        intro hbTwo
        unfold IsTwoVertex at hbTwo
        unfold IsThreeVertex at hb
        omega
      refine ⟨direct, ?_⟩
      exact goodFour_leaf_three_matching_two_of_available_safe G hsub hu huv hv
        ha hva hvb hau hbNot hN small hsmall i
        (by simpa [base, E] using hi) (by simpa [base] using hA)
        (by
          rintro ⟨_, hall'⟩
          exact hall (by simpa [direct, base, E] using hall'))
        (by simpa [direct] using hthree)
  · exact exists_goodFour_leaf_recolor_guard_of_c3_failure G hsub hu huv hv
      ha hb hr hva hvb hau hbu hab hN har hrv hrt hta small hsmall beta i hA
      hB (by simpa [base, E] using hi) (by simpa [direct, base, E] using hthree)

/-- A single available colour also suffices when the continuation of the
matching arm is a three-vertex.  The direct extension is Condition-3 safe.
If it fills the palette at `a`, either an existing matching edge at `r`
supports the guard recolouring, or its absence permits the matching shift
from `va` to `ar`. -/
theorem exists_goodFour_leaf_three_matching_two_other_three_at_three_continuation
    (hsub : IsSubcubic G)
    {u v a b r : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsThreeVertex G b) (hr : IsThreeVertex G r)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hN : G.neighborFinset v = {u, a, b})
    (har : G.Adj a r) (hrv : r ≠ v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (i : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let direct := recolor G base E (some i)
  have hru : r ≠ u := by
    intro hru
    subst r
    unfold IsThreeVertex at hr
    rw [hu] at hr
    omega
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
    exact hc.elim hva.ne (fun h ↦ hrv h.symm)
  have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hCD : C ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hvalidD : IsOneTwoColoringOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base := by
    simpa [base] using transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hCne : base C ≠ none := by
    intro hCnone
    have hp := hvalidD A hAD C hCD hAC
    have hdisj : EndpointDisjoint G A C := by
      simpa [base, A, C, hA, hCnone] using hp
    exact hdisj a (by simp [A]) (by simp [C])
  obtain ⟨gamma, hCgamma⟩ := Option.ne_none_iff_exists'.mp hCne
  have hEnone : base E = none := by
    simp [base, E, leafBaseFour, transportColoringToSupergraph]
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hsatBase : OneSaturated G base :=
    oneSaturated_leafBaseFour G huv small hsmall.oneSaturated
  have hrNotTwo : ¬ IsTwoVertex G r := by
    intro hrTwo
    unfold IsTwoVertex at hrTwo
    unfold IsThreeVertex at hr
    omega
  have hthreeDirect : ConditionThree G direct := by
    simpa [direct, base, E] using
      ConditionThree.recolor_leafEdge_of_matching_two_continuation_not_two G
        hu huv ha hva har hrv hau hrNotTwo base i
        (by simpa [base, A] using hA) hbaseThree
  by_cases hall : ∀ j : Fin 4, VertexSeesInduced G direct a j
  · have hmatchA : VertexSeesMatching G direct a := by
      apply (vertexSeesMatching_iff G direct a).mpr
      refine ⟨A, ?_, by simp [A]⟩
      change recolor G base E (some i) A = none
      rw [recolor_ne G base (some i) hAE]
      simpa [base, A] using hA
    have hmissing : ¬ VertexSeesInduced G base a i :=
      not_seen_base_of_full_after_leaf_colour_four G huv base hbaseTwo ha i
        (by simpa [direct, base, E] using hmatchA)
        (by simpa [direct, base, E] using hall)
    have higamma : i ≠ gamma := by
      intro hig
      subst gamma
      apply hmissing
      apply (vertexSeesInduced_iff G base a i).mpr
      exact ⟨C, by simpa [C] using hCgamma, a, by simp [C], Or.inl rfl⟩
    by_cases hmatchR : VertexSeesMatching G base r
    · obtain ⟨m, hm, hrm⟩ := (vertexSeesMatching_iff G base r).mp hmatchR
      let final := recolor G base A (some i)
      have hvalid : IsOneTwoColoring G final := by
        simpa [final, base, A] using
          isOneTwoColoring_recolor_leaf_arm_first_of_available G hu huv hva hau
            base i hEnone (by simpa [base, A] using hA)
            (by simpa [base, E] using hi) hmissing hvalidD
      have hsat : OneSaturated G final := by
        simpa [final, base, A] using
          OneSaturated.recolor_leaf_arm_first_of_far_matching G hu huv ha hva
            har hrv base i hEnone (by simpa [base, A] using hA) m hm hrm
            hsatBase
      have htwo : ConditionTwo G final := by
        simpa [final, base, A, C] using
          ConditionTwo.recolor_leaf_arm_first_of_other_three G hu hv ha hb hva
            hvb har hrv hN base gamma i (by simpa [base, A] using hA)
            (by simpa [base, C] using hCgamma)
            (fun hrTwo ↦ False.elim (hrNotTwo hrTwo)) hbaseTwo
      have hthree : ConditionThree G final := by
        simpa [final, base, A] using
          ConditionThree.recolor_leaf_arm_first_with_leaf_matching G hu huv ha
            hva base i hEnone hbaseThree
      exact ⟨final, hvalid, hsat, htwo, hthree⟩
    · have hnoMatchingR : ∀ f : G.edgeSet,
          base f = none → r ∈ (f : Sym2 V) → False := by
        intro f hf hrf
        exact hmatchR ((vertexSeesMatching_iff G base r).mpr ⟨f, hf, hrf⟩)
      let final := recolor G (recolor G base C none) A (some i)
      have hvalid : IsOneTwoColoring G final := by
        simpa [final, base, A, C] using
          isOneTwoColoring_leaf_arm_shift_of_available G hu huv ha hva har hau
            hrv hru base i hEnone (by simpa [base, A] using hA)
            (by simpa [base, E] using hi) hmissing hnoMatchingR hvalidD
      have htwo : ConditionTwo G final := by
        simpa [final, base, A, C] using
          ConditionTwo.shift_matching_along_leaf_arm G hu huv hv ha hb hva hvb
            har hau hrv hru hN base gamma i hEnone
            (by simpa [base, C] using hCgamma) higamma hvalidD hbaseTwo
      have hthree : ConditionThree G final := by
        simpa [final, base, A, C] using
          ConditionThree.shift_matching_along_leaf_arm_three_end G hu huv ha hr
            hva har hau hrv hru base i hEnone hbaseThree
      refine ⟨final, ?_⟩
      exact goodFour_leaf_arm_shift_of_valid_conditions G huv hva har hau hrv
        hru small hsmall gamma i hA (by simpa [base, C] using hCgamma)
        (by simpa [final] using hvalid) (by simpa [final] using htwo)
        (by simpa [final] using hthree)
  · have hbNot : ¬ IsTwoVertex G b := by
      intro hbTwo
      unfold IsTwoVertex at hbTwo
      unfold IsThreeVertex at hb
      omega
    refine ⟨direct, ?_⟩
    exact goodFour_leaf_three_matching_two_of_available_safe G hsub hu huv hv ha
      hva hvb hau hbNot hN small hsmall i (by simpa [base, E] using hi)
      (by simpa [base, A] using hA)
      (by
        rintro ⟨_, hall'⟩
        exact hall (by simpa [direct, base, E] using hall'))
      (by simpa [direct] using hthreeDirect)

/-- Complete the formerly unique-available-colour branch when the other
arm ends at a three-vertex.  The continuation of the matching arm has
degree one, two, or three, and the preceding local theorems cover all
three possibilities. -/
theorem exists_goodFour_leaf_three_matching_two_other_three_of_available
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
    (beta i : Fin 4)
    (hA : leafBaseFour G huv small
      (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : leafBaseFour G huv small
      (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  obtain ⟨r, hrv, har⟩ := exists_other_neighbor_of_isTwoVertex G ha hva.symm
  have hrPos : 0 < G.degree r := by
    rw [G.degree_pos_iff_exists_adj r]
    exact ⟨a, har.symm⟩
  have hrLe : G.degree r ≤ 3 := hsub r
  have hrCases : G.degree r = 1 ∨ G.degree r = 2 ∨ G.degree r = 3 := by
    omega
  have hbNot : ¬ IsTwoVertex G b := by
    intro hbTwo
    unfold IsTwoVertex at hbTwo
    unfold IsThreeVertex at hb
    omega
  rcases hrCases with hrOne | hrTwo | hrThree
  · exact exists_goodFour_leaf_three_matching_two_continuation_leaf G hsub
      hu huv hv ha hva hvb hab hau hbu hbNot hN har hrv hrOne small hsmall hA
  · have hrTwo' : IsTwoVertex G r := hrTwo
    obtain ⟨t, hta, hrt⟩ :=
      exists_other_neighbor_of_isTwoVertex G hrTwo' har.symm
    exact
      exists_goodFour_leaf_three_matching_two_other_three_at_two_continuation
        G hsub hu huv hv ha hb hrTwo' hva hvb hau hbu hab hN har hrv hrt hta
        small hsmall beta i hA hB hi
  · exact
      exists_goodFour_leaf_three_matching_two_other_three_at_three_continuation
        G hsub hu huv hv ha hb hrThree hva hvb hau hN har hrv small hsmall i
        hA hi

/-- If an available colour is palette-safe on the second two-vertex, it
extends across the leaf.  The matching-arm continuation is split by its
degree.  At degree two fullness is repaired by the matching shift; at
degree three either a far matching edge supports the guard recolouring or
its absence again supports the shift. -/
theorem exists_goodFour_leaf_three_both_two_of_available_safe_at_other
    (hsub : IsSubcubic G) (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsTwoVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
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
    (hsafeB : ¬ (VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let direct := recolor G base E (some i)
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G base :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  have hAE : A ≠ E := by
    intro heq
    have huA : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  obtain ⟨r, hrv, har⟩ := exists_other_neighbor_of_isTwoVertex G ha hva.symm
  have hru : r ≠ u := by
    intro hru
    subst r
    have hav : a = v := eq_neighbor_of_degree_eq_one G hu huv har.symm
    exact hva.ne hav.symm
  have hvrNot : ¬ G.Adj v r :=
    not_adj_other_neighbors_of_girth_sixteen G hgirth hva.symm har hrv.symm
  have hbr : b ≠ r := by
    intro hbr
    subst r
    exact hvrNot hvb
  have hrPos : 0 < G.degree r := by
    rw [G.degree_pos_iff_exists_adj r]
    exact ⟨a, har.symm⟩
  have hrLe : G.degree r ≤ 3 := hsub r
  have hrCases : G.degree r = 1 ∨ G.degree r = 2 ∨ G.degree r = 3 := by
    omega
  rcases hrCases with hrOne | hrTwo | hrThree
  · have hrNot : ¬ IsTwoVertex G r := by
      intro hrTwo'
      unfold IsTwoVertex at hrTwo'
      omega
    have hthree : ConditionThree G direct := by
      simpa [direct, base, E] using
        ConditionThree.recolor_leafEdge_of_matching_two_continuation_not_two G
          hu huv ha hva har hrv hau hrNot base i
          (by simpa [base, A] using hA) hbaseThree
    have hsafeA : ¬ (VertexSeesMatching G direct a ∧
        ∀ j : Fin 4, VertexSeesInduced G direct a j) := by
      rintro ⟨hmatch, hall⟩
      exact (conditionTwo_at_adjacent_leaf G hsub ha har hrOne hmatch) hall
    refine ⟨direct, ?_⟩
    exact goodFour_leaf_three_both_two_of_available_safe G hsub hu huv hv ha hb
      hva hvb hN small hsmall i hA (by simpa [base, E] using hi)
      (by simpa [direct, base, E] using hsafeA)
      (by simpa [direct, base, E] using hsafeB)
      (by simpa [direct] using hthree)
  · have hrTwo' : IsTwoVertex G r := hrTwo
    obtain ⟨t, hta, hrt⟩ :=
      exists_other_neighbor_of_isTwoVertex G hrTwo' har.symm
    by_cases hthree : ConditionThree G direct
    · by_cases hbadA : VertexSeesMatching G direct a ∧
          ∀ j : Fin 4, VertexSeesInduced G direct a j
      · have hmissing : ¬ VertexSeesInduced G base a i :=
          not_seen_base_of_full_after_leaf_colour_four G huv base hbaseTwo ha i
            (by simpa [direct, base, E] using hbadA.1)
            (by simpa [direct, base, E] using hbadA.2)
        have hAnone : base A = none := by simpa [base, A] using hA
        have hnoMatchingR : ∀ f : G.edgeSet,
            base f = none → r ∈ (f : Sym2 V) → False := by
          intro f hfnone hrf
          have hfE : f ≠ E := by
            intro hEq
            have hrmem : r ∈ (E : Sym2 V) := hEq ▸ hrf
            have hr' : r = u ∨ r = v := by simpa [E] using hrmem
            exact hr'.elim hru hrv
          have hfAfter : direct f = none := by
            simpa [direct, hfE] using hfnone
          have hAf : A ≠ f := by
            intro hEq
            have hrmem : r ∈ (A : Sym2 V) := hEq ▸ hrf
            have hr' : r = v ∨ r = a := by simpa [A] using hrmem
            exact hr'.elim hrv (fun h ↦ har.ne h.symm)
          exact (paletteCondition_at_of_two_visible_matching_four G hsub ha har
            hrTwo' A f hAf
            (by simpa [direct, hAE] using hAnone) hfAfter
            (mem_vertexVisibleEdgeFinset_of_endpoint_close G
              (show a ∈ (A : Sym2 V) by simp [A]) (Or.inl rfl))
            (mem_vertexVisibleEdgeFinset_of_endpoint_close G hrf (Or.inr har)))
            hbadA.2
        have hthreeShift : ConditionThree G
            (recolor G
              (recolor G base (⟨s(a, r), har⟩ : G.edgeSet) none)
              A (some i)) := by
          simpa [base, A] using
            ConditionThree.shift_matching_along_leaf_two_arm G hu huv ha hrTwo'
              hva har hau hrv hru base i
              (by simp [base, E, leafBaseFour, transportColoringToSupergraph])
              hbaseThree
        exact exists_goodFour_leaf_shift_other_two G hsub hu huv hv ha hb hva
          hvb hau hbu hab hbr hN har hrv small hsmall i hA hi hmissing
          hnoMatchingR hsafeB (by simpa [base, A] using hthreeShift)
      · refine ⟨direct, ?_⟩
        exact goodFour_leaf_three_both_two_of_available_safe G hsub hu huv hv ha
          hb hva hvb hN small hsmall i hA (by simpa [base, E] using hi)
          (by simpa [direct, base, E] using hbadA)
          (by simpa [direct, base, E] using hsafeB)
          (by simpa [direct] using hthree)
    · exact exists_goodFour_leaf_recolor_guard_of_c3_failure_other_two G hsub
        hu huv hv ha hb hrTwo' hva hvb hau hbu hab hN har hrv hrt hta small
        hsmall beta i hA hB hi hsafeB
        (by simpa [direct, base, E] using hthree)
  · have hrThree' : IsThreeVertex G r := hrThree
    have hrNot : ¬ IsTwoVertex G r := by
      intro hrTwo'
      unfold IsTwoVertex at hrTwo'
      unfold IsThreeVertex at hrThree'
      omega
    have hthreeDirect : ConditionThree G direct := by
      simpa [direct, base, E] using
        ConditionThree.recolor_leafEdge_of_matching_two_continuation_not_two G
          hu huv ha hva har hrv hau hrNot base i
          (by simpa [base, A] using hA) hbaseThree
    by_cases hbadA : VertexSeesMatching G direct a ∧
        ∀ j : Fin 4, VertexSeesInduced G direct a j
    · have hmissing : ¬ VertexSeesInduced G base a i :=
        not_seen_base_of_full_after_leaf_colour_four G huv base hbaseTwo ha i
          (by simpa [direct, base, E] using hbadA.1)
          (by simpa [direct, base, E] using hbadA.2)
      by_cases hmatchR : VertexSeesMatching G base r
      · obtain ⟨m, hm, hrm⟩ := (vertexSeesMatching_iff G base r).mp hmatchR
        exact exists_goodFour_leaf_guard_other_two G hsub hu huv hv ha hb hva
          hvb hau hbu hab hN har hrv small hsmall i hA hi hmissing m hm hrm
          (fun hrTwo ↦ False.elim (hrNot hrTwo)) hsafeB
      · have hnoMatchingR : ∀ f : G.edgeSet,
            base f = none → r ∈ (f : Sym2 V) → False := by
          intro f hf hrf
          exact hmatchR ((vertexSeesMatching_iff G base r).mpr ⟨f, hf, hrf⟩)
        have hthreeShift : ConditionThree G
            (recolor G
              (recolor G base (⟨s(a, r), har⟩ : G.edgeSet) none)
              A (some i)) := by
          simpa [base, A] using
            ConditionThree.shift_matching_along_leaf_arm_three_end G hu huv ha
              hrThree' hva har hau hrv hru base i
              (by simp [base, E, leafBaseFour, transportColoringToSupergraph])
              hbaseThree
        exact exists_goodFour_leaf_shift_other_two G hsub hu huv hv ha hb hva
          hvb hau hbu hab hbr hN har hrv small hsmall i hA hi hmissing
          hnoMatchingR hsafeB (by simpa [base, A] using hthreeShift)
    · refine ⟨direct, ?_⟩
      exact goodFour_leaf_three_both_two_of_available_safe G hsub hu huv hv ha hb
        hva hvb hN small hsmall i hA (by simpa [base, E] using hi)
        (by simpa [direct, base, E] using hbadA)
        (by simpa [direct, base, E] using hsafeB)
        (by simpa [direct] using hthreeDirect)

/-- Complete the two/two normal-form branch.  Start with one available
colour.  If it fills the palette at `b`, the other edge at `b` must be
matching; together with the matching edge `va` this removes two active
blockers and yields two available colours.  At most one can fill the fixed
two-vertex palette, so one is safe and the preceding theorem applies. -/
theorem exists_goodFour_leaf_three_both_two
    (hsub : IsSubcubic G) (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v) (ha : IsTwoVertex G a)
    (hb : IsTwoVertex G b)
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
  let H := deleteLeafEdge G huv
  let base := leafBaseFour G huv small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
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
  have hbaseTwo : ConditionTwo G base :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  let Bad (c : Fin 4) : Prop :=
    VertexSeesMatching G (recolor G base E (some c)) b ∧
      ∀ j : Fin 4, VertexSeesInduced G (recolor G base E (some c)) b j
  by_cases hbadI : Bad i
  · obtain ⟨s', hsv, hbs⟩ :=
      exists_other_neighbor_of_isTwoVertex G hb hvb.symm
    let F : G.edgeSet := ⟨s(b, s'), hbs⟩
    have hmatchBase : VertexSeesMatching G base b :=
      vertexSeesMatching_of_recolor_leafEdge_induced_four G huv base i
        (by simpa [Bad, base, E] using hbadI.1)
    have hFnone : base F = none := by
      simpa [F] using other_edge_matching_of_two_vertex G hb hvb hbs hsv base
        beta (by simpa [base] using hB) hmatchBase
    have hAF : A ≠ F := by
      intro heq
      have hvF : v ∈ (F : Sym2 V) := by rw [← heq]; simp [A]
      have hc : v = b ∨ v = s' := by simpa [F] using hvF
      exact hc.elim hvb.ne hsv.symm
    have hactive : (activeInducedBlockerEdgesOn G
        (RetainedEdges H G) base E).card ≤ 2 := by
      have hcount := card_activeBlockers_leafEdge_add_two_le_three_four G hu huv
        hva hvb hbs hN base (by simpa [base, A] using hA)
        (by simpa [base, F] using hFnone) (by simpa [A, F] using hAF)
      have haeq : G.degree a = 2 := ha
      have hbeq : G.degree b = 2 := hb
      change (activeInducedBlockerEdgesOn G
        (RetainedEdges H G) base E).card + 2 ≤ G.degree a + G.degree b at hcount
      rw [haeq, hbeq] at hcount
      omega
    have hblocked : (blockedInducedColorsOn G
        (RetainedEdges H G) base E).card ≤ 2 :=
      (card_blockedInducedColorsOn_le_card_activeBlockers G
        (RetainedEdges H G) base E).trans hactive
    obtain ⟨j, k, hjk, hj, hk⟩ :=
      exists_two_distinct_available_induced_of_card_blocked_add_two_le G
        (RetainedEdges H G) base E (by omega)
    by_cases hbadJ : Bad j
    · have hsafeK : ¬ Bad k := by
        intro hbadK
        exact full_palette_leaf_colour_unique_at_two_four G huv base hbaseTwo hb
          hjk hbadJ.1 hbadJ.2 hbadK.1 hbadK.2
      exact exists_goodFour_leaf_three_both_two_of_available_safe_at_other G
        hsub hgirth hu huv hv ha hb hva hvb hau hbu hab hN small hsmall beta k
        (by simpa [base, A] using hA) (by simpa [base] using hB)
        (by simpa [H, base, E] using hk)
        (by simpa [Bad, base, E] using hsafeK)
    · exact exists_goodFour_leaf_three_both_two_of_available_safe_at_other G
        hsub hgirth hu huv hv ha hb hva hvb hau hbu hab hN small hsmall beta j
        (by simpa [base, A] using hA) (by simpa [base] using hB)
        (by simpa [H, base, E] using hj)
        (by simpa [Bad, base, E] using hbadJ)
  · exact exists_goodFour_leaf_three_both_two_of_available_safe_at_other G hsub
      hgirth hu huv hv ha hb hva hvb hau hbu hab hN small hsmall beta i
      (by simpa [base, A] using hA) (by simpa [base] using hB)
      (by simpa [H, base, E] using hi)
      (by simpa [Bad, base, E] using hbadI)

/-- Closed degree-three-neighbour leaf extension.  The consolidated normal
form has exactly two residual branches, both discharged above. -/
theorem exists_goodFour_leaf_three_extension_closed
    (hsub : IsSubcubic G) (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (m : G.edgeSet)
    (hmD : m ∈ RetainedEdges (deleteLeafEdge G huv) G)
    (hm : leafBaseFour G huv small m = none)
    (hvm : v ∈ (m : Sym2 V)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  rcases leaf_three_extension_or_remaining_two_two_or_unique_two_three G hsub
      hgirth hu huv hv small hsmall m hmD hm hvm with hgood | hremaining
  · exact hgood
  · obtain ⟨a, b, hva, hvb, beta, hab, hau, hbu, hN, ha, hA, hB,
        hbTwo | ⟨hbThree, i, hi, _hunique⟩⟩ := hremaining
    · exact exists_goodFour_leaf_three_both_two G hsub hgirth hu huv hv ha
        hbTwo hva hvb hau hbu hab hN small hsmall beta hA hB
    · exact exists_goodFour_leaf_three_matching_two_other_three_of_available G
        hsub hu huv hv ha hbThree hva hvb hau hbu hab hN small hsmall beta i
        hA hB hi

/-- A Section Four edge-minimal counterexample has active minimum degree
at least two. -/
theorem IsEdgeMinimalBad.active_min_degree_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G) :
    ∀ u, 0 < G.degree u → 2 ≤ G.degree u := by
  apply hmin.active_min_degree_sectionFour_of_three_extension G
  intro u v hu huv hv small hsmall m hmD hm hvm
  have hEligibleG :
      @IsSubcubic V G _ (Classical.decRel G.Adj) ∧
        IsCombinatoriallyPlanar G ∧ (16 : ℕ∞) ≤ G.egirth := by
    simpa [SectionFourEligible] using hmin.eligible
  have hsub : IsSubcubic G :=
    isSubcubic_change_decidableRel_fourChain G
      (Classical.decRel G.Adj) inferInstance hEligibleG.1
  exact exists_goodFour_leaf_three_extension_closed G hsub hEligibleG.2.2 hu
    huv hv small hsmall m hmD hm hvm

end Finite

end

end LeanCo.PackingEdgeColoring
