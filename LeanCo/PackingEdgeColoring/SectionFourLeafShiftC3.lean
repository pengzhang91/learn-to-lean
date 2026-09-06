import LeanCo.PackingEdgeColoring.SectionFourLeafTwoOne

/-!
# Condition 3 for the Section 4 leaf-arm matching shift

This is the locality argument for changing `va` from matching to induced
and `ar` from induced to matching while the leaf edge `uv` stays matching.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Condition 3 is automatic for the leaf-arm matching shift when both
noncentral vertices on the shifted arm have degree two.  Any affected
2-thread would have to end at `v`; its external edge set then contains the
still-matching leaf edge. -/
theorem ConditionThree.shift_matching_along_leaf_two_arm
    {u v a r : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (ha : IsTwoVertex G a) (hr : IsTwoVertex G r)
    (hva : G.Adj v a) (har : G.Adj a r)
    (hau : a ≠ u) (hrv : r ≠ v) (hru : r ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hold : ConditionThree G old) :
    ConditionThree G
      (recolor G
        (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let afterC : G.edgeSet → OneTwoColor 4 := recolor G old C none
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterC A (some i)
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
  have hfinalE : final E = none := by
    change recolor G (recolor G old C none) A (some i) E = none
    rw [recolor_ne G afterC (some i) hEA]
    change recolor G old C none E = none
    rw [recolor_ne G old none hEC]
    simpa [E] using hE
  have hagree : ColoringsAgreeOff G ({A, C} : Set G.edgeSet) old final := by
    intro e he
    have hne : e ≠ A ∧ e ≠ C := by simpa using he
    simp [final, afterC, hne.1, hne.2]
  apply ConditionThree.of_agreeOff G hold hagree
  intro x y p hp haffect hleft hright
  rcases haffect with ⟨e, heS, hex⟩ | ⟨e, heS, hey⟩
  · have hev : x = v := by
      have hecase : e = A ∨ e = C := by simpa using heS
      rcases hecase with rfl | rfl
      · have hxcase : x = v ∨ x = a := by simpa [A] using hex.1
        rcases hxcase with hxv | hxa
        · exact hxv
        · exfalso
          have hxThree := hp.start_three
          unfold IsThreeVertex at hxThree
          unfold IsTwoVertex at ha
          rw [hxa] at hxThree
          omega
      · have hxcase : x = a ∨ x = r := by simpa [C] using hex.1
        rcases hxcase with hxa | hxr
        · exfalso
          have hxThree := hp.start_three
          unfold IsThreeVertex at hxThree
          unfold IsTwoVertex at ha
          rw [hxa] at hxThree
          omega
        · exfalso
          have hxThree := hp.start_three
          unfold IsThreeVertex at hxThree
          unfold IsTwoVertex at hr
          rw [hxr] at hxThree
          omega
    subst x
    obtain ⟨j, hj⟩ := hleft E
      (by simpa [E] using leafEdge_externalAt_thread_start G hu huv p hp)
    rw [hfinalE] at hj
    simp at hj
  · have heyv : y = v := by
      have hecase : e = A ∨ e = C := by simpa using heS
      rcases hecase with rfl | rfl
      · have hycase : y = v ∨ y = a := by simpa [A] using hey.1
        rcases hycase with hyv | hya
        · exact hyv
        · exfalso
          have hyThree := hp.end_three
          unfold IsThreeVertex at hyThree
          unfold IsTwoVertex at ha
          rw [hya] at hyThree
          omega
      · have hycase : y = a ∨ y = r := by simpa [C] using hey.1
        rcases hycase with hya | hyr
        · exfalso
          have hyThree := hp.end_three
          unfold IsThreeVertex at hyThree
          unfold IsTwoVertex at ha
          rw [hya] at hyThree
          omega
        · exfalso
          have hyThree := hp.end_three
          unfold IsThreeVertex at hyThree
          unfold IsTwoVertex at hr
          rw [hyr] at hyThree
          omega
    subst y
    obtain ⟨j, hj⟩ := hright E
      (by simpa [E] using leafEdge_externalAt_thread_end G hu huv p hp)
    rw [hfinalE] at hj
    simp at hj

/-- The same shift when the continuation endpoint `r` is a three-vertex.
If an affected 2-thread has endpoint `r`, the newly matching edge `C`
itself is external and immediately contradicts its external-induced
premise. -/
theorem ConditionThree.shift_matching_along_leaf_arm_three_end
    {u v a r : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (ha : IsTwoVertex G a) (_hr : IsThreeVertex G r)
    (hva : G.Adj v a) (har : G.Adj a r)
    (hau : a ≠ u) (hrv : r ≠ v) (hru : r ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hE : old (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (hold : ConditionThree G old) :
    ConditionThree G
      (recolor G
        (recolor G old (⟨s(a, r), har⟩ : G.edgeSet) none)
        (⟨s(v, a), hva⟩ : G.edgeSet) (some i)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let C : G.edgeSet := ⟨s(a, r), har⟩
  let afterC : G.edgeSet → OneTwoColor 4 := recolor G old C none
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterC A (some i)
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
    simp [afterC]
  have hagree : ColoringsAgreeOff G ({A, C} : Set G.edgeSet) old final := by
    intro e he
    have hne : e ≠ A ∧ e ≠ C := by simpa using he
    simp [final, afterC, hne.1, hne.2]
  apply ConditionThree.of_agreeOff G hold hagree
  intro x y p hp haffect hleft hright
  rcases haffect with ⟨e, heS, hex⟩ | ⟨e, heS, hey⟩
  · have hecase : e = A ∨ e = C := by simpa using heS
    rcases hecase with rfl | rfl
    · have hxcase : x = v ∨ x = a := by simpa [A] using hex.1
      rcases hxcase with hxv | hxa
      · subst x
        obtain ⟨j, hj⟩ := hleft E
          (by simpa [E] using leafEdge_externalAt_thread_start G hu huv p hp)
        rw [hfinalE] at hj
        simp at hj
      · exfalso
        have hxThree := hp.start_three
        unfold IsThreeVertex at hxThree
        unfold IsTwoVertex at ha
        rw [hxa] at hxThree
        omega
    · obtain ⟨j, hj⟩ := hleft C (by simpa [C] using hex)
      rw [hfinalC] at hj
      simp at hj
  · have hecase : e = A ∨ e = C := by simpa using heS
    rcases hecase with rfl | rfl
    · have hycase : y = v ∨ y = a := by simpa [A] using hey.1
      rcases hycase with hyv | hya
      · subst y
        obtain ⟨j, hj⟩ := hright E
          (by simpa [E] using leafEdge_externalAt_thread_end G hu huv p hp)
        rw [hfinalE] at hj
        simp at hj
      · exfalso
        have hyThree := hp.end_three
        unfold IsThreeVertex at hyThree
        unfold IsTwoVertex at ha
        rw [hya] at hyThree
        omega
    · obtain ⟨j, hj⟩ := hright C (by simpa [C] using hey)
      rw [hfinalC] at hj
      simp at hj

end Finite

end

end LeanCo.PackingEdgeColoring
