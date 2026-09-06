import LeanCo.PackingEdgeColoring.SectionFourComponentStructure
import LeanCo.PackingEdgeColoring.SectionFourLocalExclusions
import LeanCo.PackingEdgeColoring.SectionFourLeafClose

/-!
# Final assembly boundary for Section 4

All global topology, facial discharging, component transport, the no-four-
chain lemma, and the `333`/`332` reductions are already closed.  This module
packages the exact remaining local obligations and proves that they imply a
good four-colouring for every eligible graph.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*}

section Finite

variable [Fintype V] [DecidableEq V]

/-- The still-local part of the Section 4 minimal-counterexample argument.
The `333`, `332`, and `331` fields are deliberately absent because they are
already theorems. -/
structure SectionFourRemainingLocalFacts (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop where
  no330 : ForbidsThreadTripleLengths G 3 3 0
  no322 : ForbidsThreadTripleLengths G 3 2 2
  no321 : ForbidsThreadTripleLengths G 3 2 1
  no320 : ForbidsThreadTripleLengths G 3 2 0

/-- Once the four remaining local facts are supplied for every minimal bad
graph, the closed discharging argument gives a good four-colouring for every
subcubic planar graph of girth at least sixteen. -/
theorem hasGoodFour_of_remaining_sectionFour_local_facts
    (hremaining : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      IsEdgeMinimalBad SectionFourEligible HasGoodFour G →
        SectionFourRemainingLocalFacts G) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      SectionFourEligible G → HasGoodFour G := by
  apply hasGoodFour_of_minimal_forbidden_configurations
  intro G d hmin
  let current : DecidableRel G.Adj := inferInstance
  have hfacts : SectionFourRemainingLocalFacts G := hremaining G hmin
  have heligClassical :
      @IsSubcubic V G _ (Classical.decRel G.Adj) ∧
        IsCombinatoriallyPlanar G ∧
      (16 : ℕ∞) ≤ G.egirth := by
    simpa [SectionFourEligible] using hmin.eligible
  have hsub : IsSubcubic G :=
    isSubcubic_change_decidableRel_fourChain G
      (Classical.decRel G.Adj) current heligClassical.1
  have hmindeg : ∀ v, 0 < G.degree v → 2 ≤ G.degree v :=
    hmin.active_min_degree_sectionFour G
  have hno4 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 4 := by
    intro u v p hp
    exact IsEdgeMinimalBad.no_four_chain_sectionFour (G := G) hmin p
      (isKChain_change_decidableRel G current (Classical.decRel G.Adj) hp)
  have hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v := by
    intro v hv
    have hlo := hmindeg v hv
    have hhi := hsub v
    simp only [IsTwoVertex, IsThreeVertex]
    omega
  have h333 : ForbidsThreadTripleLengths G 3 3 3 :=
    hmin.forbids_three_three_three_sectionFour G
  have h332 : ForbidsThreadTripleLengths G 3 3 2 :=
    hmin.forbids_three_three_two_sectionFour G
  have h331 : ForbidsThreadTripleLengths G 3 3 1 :=
    hmin.forbids_three_three_one_sectionFour G
  have hforbid : ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u :=
    no_threeAndLongThread_of_local_triples G heligClassical.2.2 hdeg hno4
      h333 h332 h331 hfacts.no330
      hfacts.no322 hfacts.no321 hfacts.no320
  exact ⟨hmindeg, hno4, hforbid⟩

/-- All Section 4 local reductions except `no320` are now closed.  Thus a
uniform minimal-counterexample proof of that final configuration alone is
enough to obtain the strengthened girth-sixteen theorem. -/
theorem hasGoodFour_of_no_threeTwoZero_sectionFour
    (h320 : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      IsEdgeMinimalBad SectionFourEligible HasGoodFour G →
        ForbidsThreadTripleLengths G 3 2 0) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      SectionFourEligible G → HasGoodFour G := by
  apply hasGoodFour_of_remaining_sectionFour_local_facts
  intro G d hmin
  exact
    { no330 := hmin.forbids_three_three_zero_sectionFour G
      no322 := hmin.forbids_three_two_two_sectionFour G
      no321 := hmin.forbids_three_two_one_sectionFour G
      no320 := h320 G hmin }

/-- Every finite Section 4 eligible graph has a good four-colouring.  All
seven local configurations required by the discharging argument are now
closed by kernel-checked minimal-counterexample reductions. -/
theorem hasGoodFour_of_sectionFourEligible
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : SectionFourEligible G) :
    HasGoodFour G :=
  hasGoodFour_of_no_threeTwoZero_sectionFour
    (fun H _ hmin => hmin.forbids_three_two_zero_sectionFour H)
    G hG

end Finite

end

end LeanCo.PackingEdgeColoring
