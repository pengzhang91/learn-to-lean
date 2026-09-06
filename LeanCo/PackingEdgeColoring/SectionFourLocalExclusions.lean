import LeanCo.PackingEdgeColoring.SectionFourLongTwoThreadSecondMatching
import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeOneMinimal
import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeZeroMinimal
import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoTwoMinimal
import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoOneMinimal
import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoZeroMinimal
import LeanCo.PackingEdgeColoring.SectionFourForbiddenAssembly

/-!
# Local-exclusion interface for a Section 4 minimal counterexample

This module converts the concrete path-wise reducibility theorems into the
uniform triple-length predicates consumed by the final structural assembly.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The completed `no333` reduction in uniform triple-exclusion form. -/
theorem IsEdgeMinimalBad.forbids_three_three_three_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G) :
    ForbidsThreadTripleLengths G 3 3 3 := by
  intro u z t y p q r hp hq hr hpq hpr hqr
  let d : DecidableRel G.Adj := inferInstance
  exact hmin.no_threeThreeThree_sectionFour
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hp)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hq)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hr)
    hpq hpr hqr

/-- The completed `no332` reduction in uniform triple-exclusion form. -/
theorem IsEdgeMinimalBad.forbids_three_three_two_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G) :
    ForbidsThreadTripleLengths G 3 3 2 := by
  intro u z t y p q r hp hq hr hpq hpr hqr
  let d : DecidableRel G.Adj := inferInstance
  exact IsEdgeMinimalBad.no_threeThreeTwo_sectionFour (G := G) hmin
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hp)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hq)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hr)
    hpq hpr hqr

/-- The completed `no331` reduction in uniform triple-exclusion form. -/
theorem IsEdgeMinimalBad.forbids_three_three_one_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G) :
    ForbidsThreadTripleLengths G 3 3 1 := by
  intro u z t y p q r hp hq hr hpq hpr hqr
  let d : DecidableRel G.Adj := inferInstance
  exact IsEdgeMinimalBad.no_threeThreeOne_sectionFour (G := G) hmin
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hp)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hq)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hr)
    hpq hpr hqr

/-- The completed `no330` reduction in uniform triple-exclusion form. -/
theorem IsEdgeMinimalBad.forbids_three_three_zero_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G) :
    ForbidsThreadTripleLengths G 3 3 0 := by
  intro u z t y p q r hp hq hr hpq hpr hqr
  let d : DecidableRel G.Adj := inferInstance
  exact IsEdgeMinimalBad.no_threeThreeZero_sectionFour (G := G) hmin
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hp)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hq)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hr)
    hpq hpr hqr

/-- The completed `no322` reduction in uniform triple-exclusion form. -/
theorem IsEdgeMinimalBad.forbids_three_two_two_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G) :
    ForbidsThreadTripleLengths G 3 2 2 := by
  intro u z t y p q r hp hq hr hpq hpr hqr
  let d : DecidableRel G.Adj := inferInstance
  exact IsEdgeMinimalBad.no_threeTwoTwo_sectionFour (G := G) hmin
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hp)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hq)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hr)
    hpq hpr hqr

/-- The completed `no321` reduction in uniform triple-exclusion form. -/
theorem IsEdgeMinimalBad.forbids_three_two_one_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G) :
    ForbidsThreadTripleLengths G 3 2 1 := by
  intro u z t y p q r hp hq hr hpq hpr hqr
  let d : DecidableRel G.Adj := inferInstance
  exact IsEdgeMinimalBad.no_threeTwoOne_sectionFour (G := G) hmin
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hp)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hq)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hr)
    hpq hpr hqr

/-- The completed `no320` reduction in uniform triple-exclusion form. -/
theorem IsEdgeMinimalBad.forbids_three_two_zero_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G) :
    ForbidsThreadTripleLengths G 3 2 0 := by
  intro u z t y p q r hp hq hr hpq hpr hqr
  let d : DecidableRel G.Adj := inferInstance
  exact IsEdgeMinimalBad.no_threeTwoZero_sectionFour (G := G) hmin
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hp)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hq)
    (isKThread_change_decidableRel d (Classical.decRel G.Adj) hr)
    hpq hpr hqr

end Finite

end

end LeanCo.PackingEdgeColoring
