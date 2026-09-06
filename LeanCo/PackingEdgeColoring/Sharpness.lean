import LeanCo.PackingEdgeColoring.CounterexamplePlanarity
import LeanCo.PackingEdgeColoring.G2Search

/-!
# Sharpness witnesses

This module packages every property asserted of the two lower-bound graphs in
Figure 1: finiteness is built into their vertex types, and subcubicity,
planarity, exact girth, and failure of the claimed packing edge-colouring are
all kernel-checked.
-/

namespace LeanCo.PackingEdgeColoring.Counterexamples

/-- Complete lower-bound certificate supplied by Figure 1(a). -/
theorem G₁_sharpness_certificate :
    IsSubcubic G₁ ∧
      IsCombinatoriallyPlanar G₁ ∧
      G₁.egirth = 4 ∧
      ¬ HasOneTwoPackingEdgeColoring G₁ 5 :=
  ⟨G₁_subcubic, G₁_planar, G₁_egirth_eq_four,
    G₁_not_hasOneTwoPackingEdgeColoring⟩

/-- Complete lower-bound certificate supplied by Figure 1(b). -/
theorem G₂_sharpness_certificate :
    IsSubcubic G₂ ∧
      IsCombinatoriallyPlanar G₂ ∧
      G₂.egirth = 5 ∧
      ¬ HasOneTwoPackingEdgeColoring G₂ 4 :=
  ⟨G₂_subcubic, G₂_planar, G₂_egirth_eq_five,
    G₂_not_hasOneTwoPackingEdgeColoring⟩

end LeanCo.PackingEdgeColoring.Counterexamples
