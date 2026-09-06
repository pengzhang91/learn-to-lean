import LeanCo.PackingEdgeColoring.Thresholds

/-!
# End-to-end formalization of arXiv:2608.29163

The declarations below expose the two headline upper bounds and the two
sharpness witnesses through a compact public interface.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Kim--Liu--Xu, Theorem 1.1. -/
theorem kim_liu_xu_theorem_1_1
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsub : IsSubcubic G)
    (hplan : IsCombinatoriallyPlanar G)
    (hgirth : (12 : ℕ∞) ≤ G.egirth) :
    HasOneTwoPackingEdgeColoring G 5 :=
  hasOneTwoPackingEdgeColoring_five_of_subcubic_planar_girth_twelve
    G hsub hplan hgirth

/-- Kim--Liu--Xu, Theorem 1.2. -/
theorem kim_liu_xu_theorem_1_2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hsub : IsSubcubic G)
    (hplan : IsCombinatoriallyPlanar G)
    (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    HasOneTwoPackingEdgeColoring G 4 :=
  hasOneTwoPackingEdgeColoring_four_of_subcubic_planar_girth_sixteen
    G hsub hplan hgirth

/-- The numerical upper and lower bounds stated in the paper. -/
theorem kim_liu_xu_threshold_bounds :
    (¬ UniversalPackingAboveGirth 5 4 ∧
      UniversalPackingAboveGirth 5 12) ∧
    (¬ UniversalPackingAboveGirth 4 5 ∧
      UniversalPackingAboveGirth 4 16) :=
  ⟨⟨not_universalPacking_five_above_girth_four,
      universalPacking_five_above_girth_twelve⟩,
    ⟨not_universalPacking_four_above_girth_five,
      universalPacking_four_above_girth_sixteen⟩⟩

/-- Complete certificate for the paper's Figure 1(a) lower-bound graph. -/
theorem kim_liu_xu_figure_1a_sharpness :
    IsSubcubic Counterexamples.G₁ ∧
      IsCombinatoriallyPlanar Counterexamples.G₁ ∧
      Counterexamples.G₁.egirth = 4 ∧
      ¬ HasOneTwoPackingEdgeColoring Counterexamples.G₁ 5 :=
  Counterexamples.G₁_sharpness_certificate

/-- Complete certificate for the paper's Figure 1(b) lower-bound graph. -/
theorem kim_liu_xu_figure_1b_sharpness :
    IsSubcubic Counterexamples.G₂ ∧
      IsCombinatoriallyPlanar Counterexamples.G₂ ∧
      Counterexamples.G₂.egirth = 5 ∧
      ¬ HasOneTwoPackingEdgeColoring Counterexamples.G₂ 4 :=
  Counterexamples.G₂_sharpness_certificate

end

end LeanCo.PackingEdgeColoring
