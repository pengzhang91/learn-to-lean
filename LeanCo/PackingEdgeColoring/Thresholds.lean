import LeanCo.PackingEdgeColoring.SectionThreePlanarTheorem
import LeanCo.PackingEdgeColoring.SectionFourPlanarTheorem
import LeanCo.PackingEdgeColoring.Sharpness

/-!
# Universal girth-threshold statements

The paper phrases its main numerical conclusion using the least girth at
which every finite subcubic planar graph has the requested packing
edge-colouring.  `UniversalPackingAboveGirth k g` is the underlying universal
property.  Thus truth at `g = 12` and failure at `g = 4` encode
`5 ≤ k₁ ≤ 12`; the analogous `k = 4` facts encode `6 ≤ k₂ ≤ 16` once the
Section 4 upper bound is assembled.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

/-- Every finite subcubic combinatorially planar graph of girth at least `g`
admits one matching colour and `k` induced-matching colours.  `Type` fixes a
small universe for the numerical threshold; the headline theorems themselves
remain universe-polymorphic. -/
def UniversalPackingAboveGirth (k g : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
      IsSubcubic G →
      IsCombinatoriallyPlanar G →
      (g : ℕ∞) ≤ G.egirth →
      HasOneTwoPackingEdgeColoring G k

/-- The upper-bound half `k₁ ≤ 12`. -/
theorem universalPacking_five_above_girth_twelve :
    UniversalPackingAboveGirth 5 12 := by
  intro V _ _ G _ hsub hplan hgirth
  exact hasOneTwoPackingEdgeColoring_five_of_subcubic_planar_girth_twelve
    G hsub hplan hgirth

/-- The upper-bound half `k₂ ≤ 16`. -/
theorem universalPacking_four_above_girth_sixteen :
    UniversalPackingAboveGirth 4 16 := by
  intro V _ _ G _ hsub hplan hgirth
  exact hasOneTwoPackingEdgeColoring_four_of_subcubic_planar_girth_sixteen
    G hsub hplan hgirth

/-- The Figure 1(a) witness shows that girth four is below the universal
five-induced-colour threshold; equivalently, `5 ≤ k₁`. -/
theorem not_universalPacking_five_above_girth_four :
    ¬ UniversalPackingAboveGirth 5 4 := by
  intro hall
  apply Counterexamples.G₁_not_hasOneTwoPackingEdgeColoring
  exact hall Counterexamples.G₁Vertex Counterexamples.G₁
    Counterexamples.G₁_subcubic Counterexamples.G₁_planar (by
      rw [Counterexamples.G₁_egirth_eq_four]
      norm_num)

/-- The Figure 1(b) witness shows that girth five is below the universal
four-induced-colour threshold; equivalently, `6 ≤ k₂`. -/
theorem not_universalPacking_four_above_girth_five :
    ¬ UniversalPackingAboveGirth 4 5 := by
  intro hall
  apply Counterexamples.G₂_not_hasOneTwoPackingEdgeColoring
  exact hall Counterexamples.G₂Vertex Counterexamples.G₂
    Counterexamples.G₂_subcubic Counterexamples.G₂_planar (by
      rw [Counterexamples.G₂_egirth_eq_five]
      norm_num)

end LeanCo.PackingEdgeColoring
