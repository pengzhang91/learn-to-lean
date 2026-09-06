import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoZeroComplete
import LeanCo.PackingEdgeColoring.SectionFourLongMinimal

/-!
# Minimal-counterexample wrapper for the no-`(3,2,0)` reduction

This module connects the complete local no320 recolouring theorem to
Section 4 edge-minimality.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

section ClassicalMinimal

variable [Fintype V] [DecidableEq V]

/- A Section 4 edge-minimal bad graph contains no degree-three vertex
incident with distinct 3-, 2-, and 0-threads. -/
set_option maxHeartbeats 3000000 in
theorem IsEdgeMinimalBad.no_threeTwoZero_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G)
    {u z t x : V} {p : G.Walk u z} {q : G.Walk u t}
    {r : G.Walk u x}
    (hp : @IsKThread V G _ (Classical.decRel G.Adj) u z p 3)
    (hq : @IsKThread V G _ (Classical.decRel G.Adj) u t q 2)
    (hr : @IsKThread V G _ (Classical.decRel G.Adj) u x r 0)
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
  exact longPair_no_threeTwoZero_of_smaller_good G hEligibleG.2.2
    hp hq hr hpq hpr hqr small hsmall hEligibleG.1 hmin.not_good

end ClassicalMinimal

end

end LeanCo.PackingEdgeColoring
