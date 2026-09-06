import LeanCo.PackingEdgeColoring.SectionThreeStructure
import LeanCo.PackingEdgeColoring.MinimalCounterexample
import LeanCo.PackingEdgeColoring.GoodColoring

/-!
# Exact reduction of the Section 3 theorem to its three colouring lemmas

This file packages the minimal-counterexample logic without hiding any of the
paper's difficult work.  The only hypotheses left to a colouring module are
precisely the three reducibility conclusions: minimum degree two, no
three-chain, and exclusion of the `(2,1,1)` and `(2,2,0)` configurations.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Eligibility for the stronger Section 3 theorem.  The finite decidability
instances are chosen internally so this is an honest predicate on graphs. -/
def SectionThreeEligible (G : SimpleGraph V) : Prop := by
  classical
  exact IsSubcubic G ∧ MaximumAverageDegreeLT G 12 5

/-- The stronger conclusion used in Section 3. -/
def HasGoodFive (G : SimpleGraph V) : Prop := by
  classical
  exact ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour

/-- The edgeless graph has the unique vacuous good colouring. -/
theorem hasGoodFive_bot : HasGoodFive (⊥ : SimpleGraph V) := by
  classical
  let colour : (⊥ : SimpleGraph V).edgeSet → OneTwoColor 5 :=
    fun e ↦ False.elim (by simpa using e.2)
  refine ⟨colour, ?_, ?_⟩
  · intro e _
    exact False.elim (by simpa using e.2)
  · intro u hu
    simp [IsTwoVertex] at hu

/-- A good semantic colouring immediately gives the paper's original
`(1,2^5)` packing edge-colouring. -/
theorem HasGoodFive.hasOneTwoPackingEdgeColoring {G : SimpleGraph V}
    (h : HasGoodFive G) : HasOneTwoPackingEdgeColoring G 5 := by
  classical
  rw [hasOneTwoPackingEdgeColoring_iff_exists_local]
  obtain ⟨colour, hgood⟩ := h
  exact ⟨colour, hgood.valid⟩

/-- The honest end of the minimal-counterexample reduction for Section 3.

The callback contains exactly the still-required local colouring arguments;
the global thread count and maximum-average-degree contradiction are fully
discharged here. -/
theorem hasGoodFive_of_minimal_forbidden_configurations [Nonempty V]
    (hreducible : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      IsEdgeMinimalBad SectionThreeEligible HasGoodFive G →
      (∀ v, 0 < G.degree v → 2 ≤ G.degree v) ∧
      (∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 3) ∧
      ¬ HasTwoOneOneConfiguration G ∧
      ¬ HasTwoTwoZeroConfiguration G) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      SectionThreeEligible G → HasGoodFive G := by
  intro G _ hEligible
  by_contra hbad
  obtain ⟨H, hmin⟩ :=
    exists_edgeMinimalBad (V := V) (Eligible := SectionThreeEligible)
      (Good := HasGoodFive) ⟨G, hEligible, hbad⟩
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨hdegree, hno3, hno211, hno220⟩ := hreducible H hmin
  have hEdge : H.edgeFinset.Nonempty := by
    rw [SimpleGraph.edgeFinset_nonempty]
    intro hbot
    apply hmin.not_good
    simpa [hbot] using (hasGoodFive_bot (V := V))
  have hnotMad :=
    not_maximumAverageDegreeLT_twelve_five_of_forbidden_sectionThree_configurations
      H hEdge hdegree hmin.eligible.1 hno3 hno211 hno220
  exact hnotMad hmin.eligible.2

/-- Original-colouring form of the same exact reduction. -/
theorem hasOneTwoPackingEdgeColoring_five_of_minimal_forbidden_configurations
    [Nonempty V]
    (hreducible : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      IsEdgeMinimalBad SectionThreeEligible HasGoodFive G →
      (∀ v, 0 < G.degree v → 2 ≤ G.degree v) ∧
      (∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 3) ∧
      ¬ HasTwoOneOneConfiguration G ∧
      ¬ HasTwoTwoZeroConfiguration G) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      SectionThreeEligible G → HasOneTwoPackingEdgeColoring G 5 := by
  intro G _ hEligible
  exact (hasGoodFive_of_minimal_forbidden_configurations hreducible G
    hEligible).hasOneTwoPackingEdgeColoring

end


end LeanCo.PackingEdgeColoring
