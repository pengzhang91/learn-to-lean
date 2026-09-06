import LeanCo.PackingEdgeColoring.SectionFourNoFourChain
import LeanCo.PackingEdgeColoring.LeafDeletion
import LeanCo.PackingEdgeColoring.GoodExtension

/-!
# The Condition-3 part of the Section 4 leaf reduction

This module isolates the only Condition-3 case that can survive when the
leaf edge is changed from the matching colour to an induced colour.  A
second matching edge at the degree-three neighbour rules out every affected
2-thread except the two orientations in which that matching edge itself is
the designated thread edge.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If changing a leaf edge can affect Condition 3 for a certified 2-thread,
the nonleaf end of that edge is one of the two endpoints of the thread. -/
theorem threadConditionAffectedBy_leafEdge_endpoint_c3
    {u v r t : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (p : G.Walk r t) (hp : IsKThread G p 2)
    (haffect : ThreadConditionAffectedBy G
      ({(⟨s(u, v), huv⟩ : G.edgeSet)} : Set G.edgeSet) p hp) :
    r = v ∨ t = v := by
  rcases haffect with ⟨e, he, her⟩ | ⟨e, he, het⟩
  · simp only [Set.mem_singleton_iff] at he
    subst e
    have hr : r = u ∨ r = v := by simpa using her.1
    rcases hr with hru | hrv
    · have hrThree := hp.start_three
      unfold IsThreeVertex at hrThree
      rw [hru, hu] at hrThree
      omega
    · exact Or.inl hrv
  · simp only [Set.mem_singleton_iff] at he
    subst e
    have ht : t = u ∨ t = v := by simpa using het.1
    rcases ht with htu | htv
    · have htThree := hp.end_three
      unfold IsThreeVertex at htThree
      rw [htu, hu] at htThree
      omega
    · exact Or.inr htv

/-- Condition 3 survives recolouring a leaf edge when a matching edge `A`
at the nonleaf endpoint guards all noncritical 2-threads.  The only local
obligations left to the caller are the two orientations in which `A` is the
designated thread edge.

The hypothesis `hA` is deliberately about the final colouring.  In the
degree-three application it follows from `old A = none` and `A` being a
different edge from the recoloured leaf edge. -/
theorem ConditionThree.recolor_leafEdge_of_matching_guard
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (A : G.edgeSet) (hvA : v ∈ (A : Sym2 V))
    (hA : recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i) A = none)
    (hold : ConditionThree G old)
    (hcritical : ∀ (r t : V) (p : G.Walk r t)
        (hp : IsKThread G p 2),
      (r = v ∧ threadFirstEdge G p hp = A) ∨
        (t = v ∧ threadLastEdge G p hp = A) →
      ExternalEdgesInduced G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
          (threadFirstEdge G p hp) →
      ExternalEdgesInduced G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) t
          (threadLastEdge G p hp) →
      ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
          (threadFirstEdge G p hp) ≠
        ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) t
          (threadLastEdge G p hp)) :
    ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  apply ConditionThree.of_agreeOff G hold
    (coloringsAgreeOff_recolor G old
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
  intro r t p hp haffect hleft hright
  rcases threadConditionAffectedBy_leafEdge_endpoint_c3 G hu huv p hp haffect with
    hr | ht
  · by_cases hfirst : threadFirstEdge G p hp = A
    · exact hcritical r t p hp (Or.inl ⟨hr, hfirst⟩) hleft hright
    · exfalso
      have hAexternal :
          IsExternalAt G r (threadFirstEdge G p hp) A := by
        refine ⟨?_, fun hEq ↦ hfirst hEq.symm⟩
        simpa only [hr] using hvA
      obtain ⟨j, hj⟩ := hleft A hAexternal
      rw [hA] at hj
      simp at hj
  · by_cases hlast : threadLastEdge G p hp = A
    · exact hcritical r t p hp (Or.inr ⟨ht, hlast⟩) hleft hright
    · exfalso
      have hAexternal :
          IsExternalAt G t (threadLastEdge G p hp) A := by
        refine ⟨?_, fun hEq ↦ hlast hEq.symm⟩
        simpa only [ht] using hvA
      obtain ⟨j, hj⟩ := hright A hAexternal
      rw [hA] at hj
      simp at hj

/-- Concrete guard for the edge `v-a`: if it is matching before the leaf
edge recolouring and `a` is not the leaf, it is matching afterwards as
required by `recolor_leafEdge_of_matching_guard`. -/
theorem ConditionThree.recolor_leafEdge_of_matching_otherNeighbor
    {u v a : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hau : a ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hAold : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hold : ConditionThree G old)
    (hcritical : ∀ (r t : V) (p : G.Walk r t)
        (hp : IsKThread G p 2),
      (r = v ∧ threadFirstEdge G p hp =
          (⟨s(v, a), hva⟩ : G.edgeSet)) ∨
        (t = v ∧ threadLastEdge G p hp =
          (⟨s(v, a), hva⟩ : G.edgeSet)) →
      ExternalEdgesInduced G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
          (threadFirstEdge G p hp) →
      ExternalEdgesInduced G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) t
          (threadLastEdge G p hp) →
      ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
          (threadFirstEdge G p hp) ≠
        ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) t
          (threadLastEdge G p hp)) :
    ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  have hAE : A ≠ E := by
    intro hEq
    have haE : a ∈ (E : Sym2 V) := by
      rw [← hEq]
      simp [A]
    have haCases : a = u ∨ a = v := by
      simpa [E] using haE
    exact haCases.elim hau (fun hav ↦ hva.ne hav.symm)
  have hAfinal : recolor G old E (some i) A = none := by
    rw [recolor_ne G old (some i) hAE]
    exact hAold
  exact ConditionThree.recolor_leafEdge_of_matching_guard G hu huv old i A
    (by simp [A]) (by simpa only [E, A] using hAfinal) hold
    (by simpa only [A, E] using hcritical)

/-- If the other endpoint `a` of the matching guard edge is not a
two-vertex, even the nominally critical cases are impossible: a designated
first or last edge `v-a` would put `a` at an internal position of a certified
2-thread. -/
theorem ConditionThree.recolor_leafEdge_of_matching_otherNeighbor_not_two
    {u v a : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hau : a ≠ u) (haNot : ¬ IsTwoVertex G a)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hAold : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hold : ConditionThree G old) :
    ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  apply ConditionThree.recolor_leafEdge_of_matching_otherNeighbor G
    hu huv hva hau old i hAold hold
  intro r t p hp hcritical _hleft _hright
  rcases hcritical with ⟨hr, hfirst⟩ | ⟨ht, hlast⟩
  · exfalso
    subst r
    have hedge : s(v, p.getVert 1) = s(v, a) := by
      exact congrArg Subtype.val hfirst
    have hget : p.getVert 1 = a := by
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact h.2
      · exact False.elim (hva.ne h.1)
    apply haNot
    have hlen : p.length = 3 := by simpa using hp.length
    have htwo := IsKThread.internal_two G hp (i := 1)
      (by omega) (by omega)
    rw [hget] at htwo
    exact htwo
  · exfalso
    subst t
    have hedge : s(p.getVert 2, v) = s(v, a) := by
      exact congrArg Subtype.val hlast
    have hget : p.getVert 2 = a := by
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact False.elim (hva.ne h.2)
      · exact h.1
    apply haNot
    have hlen : p.length = 3 := by simpa using hp.length
    have htwo := IsKThread.internal_two G hp (i := 2)
      (by omega) (by omega)
    rw [hget] at htwo
    exact htwo

end Finite

end

end LeanCo.PackingEdgeColoring
