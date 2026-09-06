import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeThree
import LeanCo.PackingEdgeColoring.SectionFourNoFourChain
import LeanCo.PackingEdgeColoring.PlanarHeredity

/-!
# Minimal-counterexample wrappers for the Section 4 long-thread reductions

Every long-thread reduction deletes the middle vertex of a certified
3-thread.  This file discharges the common eligibility and minimality
bookkeeping once, separately from the local recolouring arguments.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Deleting all edges incident with one vertex preserves the three
Section 4 eligibility hypotheses. -/
theorem sectionFourEligible_deleteIncidenceSet
    (hEligible : SectionFourEligible G) (x : V) :
    SectionFourEligible (G.deleteIncidenceSet x) := by
  let H := G.deleteIncidenceSet x
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hEligibleG :
      @IsSubcubic V G _ (Classical.decRel G.Adj) ∧
        IsCombinatoriallyPlanar G ∧ (16 : ℕ∞) ≤ G.egirth := by
    simpa [SectionFourEligible] using hEligible
  have hsubCurrent : IsSubcubic G :=
    isSubcubic_change_decidableRel_fourChain G
      (Classical.decRel G.Adj) inferInstance hEligibleG.1
  rw [SectionFourEligible]
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact (H.degree_le_of_le (G.deleteIncidenceSet_le x)).trans
      (hsubCurrent q)
  · exact hEligibleG.2.1.mono (G.deleteIncidenceSet_le x)
  · exact hEligibleG.2.2.trans
      (SimpleGraph.egirth_anti (G.deleteIncidenceSet_le x))

end Finite

section ClassicalMinimal

variable [Fintype V] [DecidableEq V]

/-- Minimality supplies a good colouring after deleting the middle vertex
of any certified 3-thread.  The result is converted to the decidability
instance inherited by `deleteIncidenceSet`, which is the instance used by
all local long-thread extension theorems. -/
theorem IsEdgeMinimalBad.exists_good_deleteThreeThreadMiddle
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G)
    {u z : V} {p : G.Walk u z}
    (hp : @IsKThread V G _ (Classical.decRel G.Adj) u z p 3) :
    ∃ small : (G.deleteIncidenceSet (p.getVert 2)).edgeSet →
        OneTwoColor 4,
      @GoodFour V (G.deleteIncidenceSet (p.getVert 2)) _ _
        (@SimpleGraph.instDecidableRelAdjDeleteIncidenceSet
          V _ G (Classical.decRel G.Adj) (p.getVert 2)) small := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let x : V := p.getVert 2
  have hcore := hp.threeThreadCore G
  have hxIncident : ∃ e : G.edgeSet, x ∈ (e : Sym2 V) :=
    ⟨⟨s(p.getVert 1, x), hcore.left_adj⟩, by simp⟩
  have hEligibleDelete : SectionFourEligible (G.deleteIncidenceSet x) :=
    sectionFourEligible_deleteIncidenceSet (G := G) hmin.eligible x
  have hgoodDelete : HasGoodFour (G.deleteIncidenceSet x) :=
    hmin.good_deleteIncidenceSet hxIncident hEligibleDelete
  rw [HasGoodFour] at hgoodDelete
  obtain ⟨small, hsmallClassical⟩ := hgoodDelete
  refine ⟨small, ?_⟩
  exact goodFour_change_decidableRel (G := G.deleteIncidenceSet x)
    (Classical.decRel (G.deleteIncidenceSet x).Adj)
    (@SimpleGraph.instDecidableRelAdjDeleteIncidenceSet
      V _ G (Classical.decRel G.Adj) x)
    small hsmallClassical

/- Minimal-counterexample form of the `3-3-3` long-thread reduction.
The smaller colouring is obtained by deleting the middle vertex of the
selected first arm. -/
set_option maxHeartbeats 1600000 in
theorem IsEdgeMinimalBad.no_threeThreeThree_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t}
    {r : G.Walk u y}
    (hp : @IsKThread V G _ (Classical.decRel G.Adj) u z p 3)
    (hq : @IsKThread V G _ (Classical.decRel G.Adj) u t q 3)
    (hr : @IsKThread V G _ (Classical.decRel G.Adj) u y r 3)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1) : False := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨small, hsmall⟩ :=
    hmin.exists_good_deleteThreeThreadMiddle (G := G) hp
  have hEligibleG :
      @IsSubcubic V G _ (Classical.decRel G.Adj) ∧
        IsCombinatoriallyPlanar G ∧ (16 : ℕ∞) ≤ G.egirth := by
    simpa [SectionFourEligible] using hmin.eligible
  exact longPair_no_threeThreeThree_of_smaller_good G hEligibleG.2.2
    hp hq hr hpq hpr hqr small hsmall hEligibleG.1 hmin.not_good

end ClassicalMinimal

end

end LeanCo.PackingEdgeColoring
