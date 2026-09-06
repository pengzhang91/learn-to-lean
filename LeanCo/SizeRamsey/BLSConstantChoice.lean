import Mathlib.Tactic

/-!
# The final absolute constant in the BLS path lower bound

This file isolates the one small real constant needed by the final
quantifier assembly.  It has no dependency on the still-open Key-Lemma or
round-iteration modules.
-/

namespace LeanCo.SizeRamsey

noncomputable section

/-- A conservative absolute lower-bound constant chosen from the eventual
Key-Lemma parameter `beta0`. -/
def blsLowerConstant (beta0 : ℝ) : ℝ :=
  min ((1 : ℝ) / 10000) (beta0 / 20000)

/-- The chosen constant is positive whenever the Key-Lemma parameter is. -/
theorem blsLowerConstant_pos {beta0 : ℝ} (hbeta0 : 0 < beta0) :
    0 < blsLowerConstant beta0 := by
  unfold blsLowerConstant
  exact lt_min (by norm_num) (div_pos hbeta0 (by norm_num))

/-- The first branch of the minimum gives the coarse absolute upper bound. -/
theorem blsLowerConstant_le_one {beta0 : ℝ} :
    blsLowerConstant beta0 ≤ 1 := by
  calc
    blsLowerConstant beta0 ≤ (1 : ℝ) / 10000 := by
      exact min_le_left _ _
    _ ≤ 1 := by norm_num

/-- The constant leaves the factor `10000` of slack used in the initial
edge-mass normalization. -/
theorem ten_thousand_mul_blsLowerConstant_le_one (beta0 : ℝ) :
    10000 * blsLowerConstant beta0 ≤ 1 := by
  have hmin : blsLowerConstant beta0 ≤ (1 : ℝ) / 10000 := by
    exact min_le_left _ _
  nlinarith

/-- The second branch of the minimum leaves a factor `20000` below
`beta0`. -/
theorem twenty_thousand_mul_blsLowerConstant_le_beta0 (beta0 : ℝ) :
    20000 * blsLowerConstant beta0 ≤ beta0 := by
  have hmin : blsLowerConstant beta0 ≤ beta0 / 20000 := by
    exact min_le_right _ _
  nlinarith

/-- A weaker form convenient at call sites that spend only a factor `100`. -/
theorem hundred_mul_blsLowerConstant_le_beta0
    {beta0 : ℝ} (hbeta0 : 0 < beta0) :
    100 * blsLowerConstant beta0 ≤ beta0 := by
  have hpos : 0 < blsLowerConstant beta0 :=
    blsLowerConstant_pos hbeta0
  have hlarge := twenty_thousand_mul_blsLowerConstant_le_beta0 beta0
  nlinarith

/-- All inequalities normally consumed by the final quantifier assembly. -/
theorem blsLowerConstant_spec {beta0 : ℝ}
    (hbeta0 : 0 < beta0) (hbeta0One : beta0 ≤ 1) :
    0 < blsLowerConstant beta0 ∧
      blsLowerConstant beta0 ≤ 1 ∧
      10000 * blsLowerConstant beta0 ≤ 1 ∧
      20000 * blsLowerConstant beta0 ≤ beta0 ∧
      100 * blsLowerConstant beta0 ≤ beta0 := by
  have hconstantOne : blsLowerConstant beta0 ≤ 1 := by
    calc
      blsLowerConstant beta0 ≤ beta0 / 20000 := min_le_right _ _
      _ ≤ 1 := by nlinarith
  exact ⟨blsLowerConstant_pos hbeta0,
    hconstantOne,
    ten_thousand_mul_blsLowerConstant_le_one beta0,
    twenty_thousand_mul_blsLowerConstant_le_beta0 beta0,
    hundred_mul_blsLowerConstant_le_beta0 hbeta0⟩

/-! ## Aggregating eventual thresholds -/

/-- One natural threshold dominating the five independent eventual
thresholds used by the lower-bound closure. -/
def blsFinalThreshold
    (keyLemma denseWeight residualWeight roundSchedule terminal : ℕ) : ℕ :=
  max keyLemma (max denseWeight (max residualWeight (max roundSchedule terminal)))

theorem keyLemma_le_blsFinalThreshold
    (keyLemma denseWeight residualWeight roundSchedule terminal : ℕ) :
    keyLemma ≤
      blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal := by
  unfold blsFinalThreshold
  omega

theorem denseWeight_le_blsFinalThreshold
    (keyLemma denseWeight residualWeight roundSchedule terminal : ℕ) :
    denseWeight ≤
      blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal := by
  unfold blsFinalThreshold
  omega

theorem residualWeight_le_blsFinalThreshold
    (keyLemma denseWeight residualWeight roundSchedule terminal : ℕ) :
    residualWeight ≤
      blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal := by
  unfold blsFinalThreshold
  omega

theorem roundSchedule_le_blsFinalThreshold
    (keyLemma denseWeight residualWeight roundSchedule terminal : ℕ) :
    roundSchedule ≤
      blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal := by
  unfold blsFinalThreshold
  omega

theorem terminal_le_blsFinalThreshold
    (keyLemma denseWeight residualWeight roundSchedule terminal : ℕ) :
    terminal ≤
      blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal := by
  unfold blsFinalThreshold
  omega

/-- Bundled projection form for consumers that immediately need every
component threshold. -/
theorem blsFinalThreshold_spec
    (keyLemma denseWeight residualWeight roundSchedule terminal : ℕ) :
    keyLemma ≤
        blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal ∧
      denseWeight ≤
        blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal ∧
      residualWeight ≤
        blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal ∧
      roundSchedule ≤
        blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal ∧
      terminal ≤
        blsFinalThreshold keyLemma denseWeight residualWeight roundSchedule terminal := by
  exact ⟨keyLemma_le_blsFinalThreshold _ _ _ _ _,
    denseWeight_le_blsFinalThreshold _ _ _ _ _,
    residualWeight_le_blsFinalThreshold _ _ _ _ _,
    roundSchedule_le_blsFinalThreshold _ _ _ _ _,
    terminal_le_blsFinalThreshold _ _ _ _ _⟩

end

end LeanCo.SizeRamsey
