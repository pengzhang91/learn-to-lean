import LeanCo.PackingEdgeColoring.SectionFourFinalAssembly

/-!
# The planar girth-sixteen theorem

This module combines the completed Section 4 minimal-counterexample and
discharging argument with the definition of Section 4 eligibility.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Strengthened planar form: a finite subcubic combinatorially planar graph
of girth at least sixteen has a good four-colouring. -/
theorem hasGoodFour_of_subcubic_planar_girth_sixteen
    (G : SimpleGraph V) [d : DecidableRel G.Adj]
    (hsub : IsSubcubic G)
    (hplan : IsCombinatoriallyPlanar G)
    (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    HasGoodFour G := by
  have hd : d = Classical.decRel G.Adj := Subsingleton.elim _ _
  subst d
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  apply hasGoodFour_of_sectionFourEligible G
  rw [SectionFourEligible]
  exact ⟨hsub, hplan, hgirth⟩

/-- Main girth-sixteen result: every finite subcubic combinatorially planar
graph of girth at least sixteen admits a `(1,2^4)` packing edge-colouring. -/
theorem hasOneTwoPackingEdgeColoring_four_of_subcubic_planar_girth_sixteen
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsub : IsSubcubic G)
    (hplan : IsCombinatoriallyPlanar G)
    (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    HasOneTwoPackingEdgeColoring G 4 :=
  (hasGoodFour_of_subcubic_planar_girth_sixteen
    G hsub hplan hgirth).hasOneTwoPackingEdgeColoring

end

end LeanCo.PackingEdgeColoring
