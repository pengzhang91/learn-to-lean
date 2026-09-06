import LeanCo.PackingEdgeColoring.PlanarGirthDensity
import LeanCo.PackingEdgeColoring.SectionThreeTheorem

/-!
# The planar girth-twelve theorem

This module combines the Section 3 maximum-average-degree theorem with the
Euler density bound for planar graphs of girth at least twelve.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Strengthened planar form: a finite subcubic combinatorially planar graph
of girth at least twelve has a good five-colouring. -/
theorem hasGoodFive_of_subcubic_planar_girth_twelve
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsub : IsSubcubic G)
    (hplan : IsCombinatoriallyPlanar G)
    (hgirth : (12 : ℕ∞) ≤ G.egirth) :
    HasGoodFive G := by
  apply hasGoodFive_of_subcubic_of_maximumAverageDegreeLT_twelve_five
    G hsub
  exact maximumAverageDegreeLT_twelve_five_of_planar_girth_twelve
    (G := G) hplan hgirth

/-- Main girth-twelve result: every finite subcubic combinatorially planar
graph of girth at least twelve admits a `(1,2^5)` packing edge-colouring. -/
theorem hasOneTwoPackingEdgeColoring_five_of_subcubic_planar_girth_twelve
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsub : IsSubcubic G)
    (hplan : IsCombinatoriallyPlanar G)
    (hgirth : (12 : ℕ∞) ≤ G.egirth) :
    HasOneTwoPackingEdgeColoring G 5 :=
  (hasGoodFive_of_subcubic_planar_girth_twelve G hsub hplan hgirth).hasOneTwoPackingEdgeColoring

end

end LeanCo.PackingEdgeColoring
