import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Weighted Chebyshev inequality for oppositely varying functions

The occupancy proof conditions on the load of one bin.  The indicator of a
large load is increasing in that load, while the conditional upper-tail
count for a second bin is decreasing.  This file supplies the finite
weighted covariance inequality needed to turn those two facts into a
negative-correlation estimate.  Natural weights are represented literally
by repeating each index `w i` times in a sigma type.
-/

namespace LeanCo.SizeRamsey

open Finset Function

/-- Weighted Chebyshev inequality for a monotone/antitone pair.  This is the
finite counting form of non-positive covariance; no probability or measure
theory is involved. -/
theorem weighted_antivary_sum
    {I : Type*} [Fintype I] [LinearOrder I]
    (w : I → ℕ) (f g : I → ℝ)
    (hf : Monotone f) (hg : Antitone g) :
    (∑ i, (w i : ℝ)) * (∑ i, (w i : ℝ) * (f i * g i)) ≤
      (∑ i, (w i : ℝ) * f i) * (∑ i, (w i : ℝ) * g i) := by
  let f' : (Σ i, Fin (w i)) → ℝ := fun x ↦ f x.1
  let g' : (Σ i, Fin (w i)) → ℝ := fun x ↦ g x.1
  have hanti : Antivary f' g' := by
    exact (hf.antivary hg).comp_right Sigma.fst
  have h := hanti.card_mul_sum_le_sum_mul_sum
  simpa only [f', g', Fintype.card_sigma, Fintype.card_fin,
    Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_sum, Nat.cast_id, mul_assoc] using h

/-- Indicator specialization: an upper set is negatively correlated with
any nonnegative antitone statistic under arbitrary natural weights. -/
theorem weighted_upperIndicator_mul_antitone
    {I : Type*} [Fintype I] [LinearOrder I]
    (w : I → ℕ) (g : I → ℝ) (t : I) (hg : Antitone g) :
    (∑ i, (w i : ℝ)) *
        (∑ i, (w i : ℝ) * ((if t ≤ i then 1 else 0) * g i)) ≤
      (∑ i, (w i : ℝ) * (if t ≤ i then 1 else 0)) *
        (∑ i, (w i : ℝ) * g i) := by
  apply weighted_antivary_sum w
      (fun i ↦ (if t ≤ i then (1 : ℝ) else 0)) g
  · intro i j hij
    by_cases hi : t ≤ i
    · have hj : t ≤ j := hi.trans hij
      simp [hi, hj]
    · by_cases hj : t ≤ j <;> simp [hi, hj]
  · exact hg

end LeanCo.SizeRamsey
