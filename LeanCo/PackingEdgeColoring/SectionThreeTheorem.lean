import LeanCo.PackingEdgeColoring.SectionThreeLeafHard
import LeanCo.PackingEdgeColoring.SectionThreeNoThreeChain
import LeanCo.PackingEdgeColoring.SectionThreeTwoOneOneReduction
import LeanCo.PackingEdgeColoring.SectionThreeTwoTwoZero

/-!
# The Section 3 theorem

This file closes the stronger theorem from Section 3 of Kim--Liu--Xu.  The
four local reducibility results are assembled into the forbidden-configuration
callback of `SectionThreeReduction`; its maximum-average-degree argument then
rules out an edge-minimal counterexample.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All four local conclusions needed by the Section 3 minimal-counterexample
reduction hold in an edge-minimal bad graph. -/
theorem IsEdgeMinimalBad.sectionThree_forbidden_configurations
    (G : SimpleGraph V) [d : DecidableRel G.Adj]
    (hmin : IsEdgeMinimalBad SectionThreeEligible HasGoodFive G) :
    (forall v, 0 < G.degree v -> 2 <= G.degree v) ∧
      (forall {u v : V} (p : G.Walk u v), ¬ IsKChain G p 3) ∧
      ¬ HasTwoOneOneConfiguration G ∧
      ¬ HasTwoTwoZeroConfiguration G := by
  have hd : d = Classical.decRel G.Adj := Subsingleton.elim _ _
  subst d
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  refine ⟨hmin.active_min_degree_sectionThree G, ?_, ?_, ?_⟩
  · intro u v p
    exact hmin.no_three_chain_sectionThree G p
  · exact hmin.no_twoOneOne_sectionThree G
  · exact hmin.no_twoTwoZero_sectionThree G

/-- Stronger Section 3 theorem: every finite subcubic graph of maximum
average degree strictly less than `12 / 5` has a good `(1,2^5)` colouring.

`HasGoodFive` includes the auxiliary two-vertex condition used by the local
extension proofs, so this is strictly stronger than the packing-colouring
statement itself. -/
theorem hasGoodFive_of_subcubic_of_maximumAverageDegreeLT_twelve_five
    (G : SimpleGraph V) [d : DecidableRel G.Adj]
    (hsub : IsSubcubic G)
    (hmad : MaximumAverageDegreeLT G 12 5) :
    HasGoodFive G := by
  have hd : d = Classical.decRel G.Adj := Subsingleton.elim _ _
  subst d
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  cases isEmpty_or_nonempty V with
  | inl hEmpty =>
      letI : IsEmpty V := hEmpty
      have hG : G = (⊥ : SimpleGraph V) := Subsingleton.elim _ _
      simpa [hG] using (hasGoodFive_bot (V := V))
  | inr hNonempty =>
      letI : Nonempty V := hNonempty
      apply hasGoodFive_of_minimal_forbidden_configurations
        (fun H _ hmin => hmin.sectionThree_forbidden_configurations H)
        G
      rw [SectionThreeEligible]
      exact ⟨isSubcubic_change_decidableRel G inferInstance
        (Classical.decRel G.Adj) hsub, hmad⟩

/-- Theorem 1.4, maximum-average-degree form: every finite subcubic graph
with maximum average degree less than `12 / 5` admits a `(1,2^5)` packing
edge-colouring. -/
theorem hasOneTwoPackingEdgeColoring_five_of_subcubic_of_maximumAverageDegreeLT_twelve_five
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsub : IsSubcubic G)
    (hmad : MaximumAverageDegreeLT G 12 5) :
    HasOneTwoPackingEdgeColoring G 5 :=
  (hasGoodFive_of_subcubic_of_maximumAverageDegreeLT_twelve_five G hsub hmad).hasOneTwoPackingEdgeColoring

end

end LeanCo.PackingEdgeColoring
