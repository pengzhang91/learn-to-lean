import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Geometric-decay numerics for a BLS colouring round

This file isolates the elementary estimate which turns a per-step fractional
gain into a factor-ten reduction after finitely many extractions.
-/

namespace LeanCo.SizeRamsey

noncomputable section

/-- The standard estimate `(1-a)^T ≤ exp(-aT)`, with the only necessary
base-side hypothesis made explicit. -/
theorem one_sub_pow_le_exp_neg_mul {a : ℝ} (ha : a ≤ 1) (T : ℕ) :
    (1 - a) ^ T ≤ Real.exp (-a * T) := by
  have hbase : 0 ≤ 1 - a := sub_nonneg.mpr ha
  calc
    (1 - a) ^ T ≤ (Real.exp (-a)) ^ T :=
      pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg a) T
    _ = Real.exp (-a * T) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- If the accumulated exponent is at least `log 10`, the residual factor
is at most one tenth. -/
theorem one_sub_pow_le_one_tenth {a : ℝ} (ha : a ≤ 1) (T : ℕ)
    (hAT : Real.log 10 ≤ a * T) :
    (1 - a) ^ T ≤ (1 : ℝ) / 10 := by
  have hexp := one_sub_pow_le_exp_neg_mul ha T
  have hneg : -a * (T : ℝ) ≤ -Real.log 10 := by
    nlinarith
  calc
    (1 - a) ^ T ≤ Real.exp (-a * T) := hexp
    _ ≤ Real.exp (-Real.log 10) := Real.exp_monotone hneg
    _ = (1 : ℝ) / 10 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      norm_num

/-- Multiplicative form consumed directly by
`freeExtractionResidual_edgeCount_le_threshold`. -/
theorem one_sub_pow_mul_le_tenth {a E : ℝ} (ha : a ≤ 1) (T : ℕ)
    (hAT : Real.log 10 ≤ a * T) (hE : 0 ≤ E) :
    (1 - a) ^ T * E ≤ E / 10 := by
  have hfactor := one_sub_pow_le_one_tenth ha T hAT
  calc
    (1 - a) ^ T * E ≤ ((1 : ℝ) / 10) * E :=
      mul_le_mul_of_nonneg_right hfactor hE
    _ = E / 10 := by ring

end

end LeanCo.SizeRamsey
