import LeanCo.SizeRamsey.AvoidingColoringGlue

/-!
# Gluing colourings across an exact graph split

The lower-bound construction repeatedly colours `G \ R` and leaves the
subgraph `R` for a later round.  This module packages the elementary final
step: avoiding colourings of both parts combine into an avoiding colouring
of `G`, with the palette sizes added.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- The two members of the cover associated with `R ≤ G`. -/
def graphSplitCover (G R : SimpleGraph V) : Bool → SimpleGraph V
  | false => G \ R
  | true => R

/-- Palette sizes for the two sides of `graphSplitCover`. -/
def graphSplitBudget (a b : ℕ) : Bool → ℕ
  | false => a
  | true => b

@[simp]
theorem sum_graphSplitBudget (a b : ℕ) :
    ∑ i, graphSplitBudget a b i = a + b := by
  simp [graphSplitBudget, Nat.add_comm]

theorem graphSplitCover_le (G R : SimpleGraph V) (hR : R ≤ G) :
    ∀ i, graphSplitCover G R i ≤ G := by
  intro i
  cases i <;> simp [graphSplitCover, hR]

theorem graphSplitCover_covers (G R : SimpleGraph V) (_hR : R ≤ G) :
    EdgesCoveredBy G (graphSplitCover G R) := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hG : G.Adj x y := by
        simpa only [mem_edgeSet] using he
      by_cases hxy : R.Adj x y
      · refine ⟨true, ?_⟩
        simpa only [graphSplitCover, mem_edgeSet] using hxy
      · refine ⟨false, ?_⟩
        have : (G \ R).Adj x y := (sdiff_adj G R x y).mpr ⟨hG, hxy⟩
        simpa only [graphSplitCover, mem_edgeSet] using this

/-- Avoiding colourings of `G \ R` and `R` glue into an avoiding colouring
of `G`; unused target colours are permitted by the final inequality. -/
theorem exists_path_avoidingColoring_of_split
    {G R : SimpleGraph V} (hR : R ≤ G)
    {a b n r : ℕ} (hn : 2 ≤ n)
    (Cleft : (G \ R).EdgeLabeling (Fin a))
    (hleft : AvoidsMonochromaticCopy (pathGraph n) Cleft)
    (Cright : R.EdgeLabeling (Fin b))
    (hright : AvoidsMonochromaticCopy (pathGraph n) Cright)
    (hbudget : a + b ≤ r) :
    ∃ C : G.EdgeLabeling (Fin r),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  apply exists_fin_path_avoidingColoring_of_cover
    G (graphSplitCover G R) (graphSplitBudget a b) hn
  · exact graphSplitCover_le G R hR
  · exact graphSplitCover_covers G R hR
  · intro i
    cases i
    · exact ⟨Cleft, hleft⟩
    · exact ⟨Cright, hright⟩
  · simpa only [sum_graphSplitBudget] using hbudget

/-! ## Nested residuals -/

/-- The two differences between three nested graphs `R₂ ≤ R₁ ≤ G`. -/
def nestedSdiffCover (G R₁ R₂ : SimpleGraph V) : Bool → SimpleGraph V
  | false => G \ R₁
  | true => R₁ \ R₂

theorem nestedSdiffCover_le
    (G R₁ R₂ : SimpleGraph V) (h₁ : R₁ ≤ G) (h₂ : R₂ ≤ R₁) :
    ∀ i, nestedSdiffCover G R₁ R₂ i ≤ G \ R₂ := by
  intro i x y hxy
  cases i with
  | false =>
      have hout : G.Adj x y ∧ ¬ R₁.Adj x y :=
        (sdiff_adj G R₁ x y).mp hxy
      exact (sdiff_adj G R₂ x y).mpr
        ⟨hout.1, fun hR₂ ↦ hout.2 (h₂ hR₂)⟩
  | true =>
      have hin : R₁.Adj x y ∧ ¬ R₂.Adj x y :=
        (sdiff_adj R₁ R₂ x y).mp hxy
      exact (sdiff_adj G R₂ x y).mpr ⟨h₁ hin.1, hin.2⟩

theorem nestedSdiffCover_covers
    (G R₁ R₂ : SimpleGraph V) (_h₁ : R₁ ≤ G) (_h₂ : R₂ ≤ R₁) :
    EdgesCoveredBy (G \ R₂) (nestedSdiffCover G R₁ R₂) := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have htarget : G.Adj x y ∧ ¬ R₂.Adj x y := by
        apply (sdiff_adj G R₂ x y).mp
        simpa only [mem_edgeSet] using he
      by_cases hxy : R₁.Adj x y
      · refine ⟨true, ?_⟩
        have : (R₁ \ R₂).Adj x y :=
          (sdiff_adj R₁ R₂ x y).mpr ⟨hxy, htarget.2⟩
        simpa only [nestedSdiffCover, mem_edgeSet] using this
      · refine ⟨false, ?_⟩
        have : (G \ R₁).Adj x y :=
          (sdiff_adj G R₁ x y).mpr ⟨htarget.1, hxy⟩
        simpa only [nestedSdiffCover, mem_edgeSet] using this

/-- Colourings produced in two consecutive stages combine on their total
difference. -/
theorem exists_path_avoidingColoring_of_nested_sdiff
    {G R₁ R₂ : SimpleGraph V} (h₁ : R₁ ≤ G) (h₂ : R₂ ≤ R₁)
    {a b n r : ℕ} (hn : 2 ≤ n)
    (Couter : (G \ R₁).EdgeLabeling (Fin a))
    (houter : AvoidsMonochromaticCopy (pathGraph n) Couter)
    (Cinner : (R₁ \ R₂).EdgeLabeling (Fin b))
    (hinner : AvoidsMonochromaticCopy (pathGraph n) Cinner)
    (hbudget : a + b ≤ r) :
    ∃ C : (G \ R₂).EdgeLabeling (Fin r),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  apply exists_fin_path_avoidingColoring_of_cover
    (G \ R₂) (nestedSdiffCover G R₁ R₂)
      (graphSplitBudget a b) hn
  · exact nestedSdiffCover_le G R₁ R₂ h₁ h₂
  · exact nestedSdiffCover_covers G R₁ R₂ h₁ h₂
  · intro i
    cases i
    · exact ⟨Couter, houter⟩
    · exact ⟨Cinner, hinner⟩
  · simpa only [sum_graphSplitBudget] using hbudget

end

end LeanCo.SizeRamsey
