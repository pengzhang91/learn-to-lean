import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic

/-!
# A dyadic colour budget for the BLS rounds

Using `r / 2^(i+4)` colours for extraction and the same number for star
cleanup in round `i` leaves a particularly simple global budget.  The sum of
all such two-sided round budgets is at most `r/4`, with no floors of real
numbers in the definition.
-/

namespace LeanCo.SizeRamsey

open Finset

noncomputable section

/-- Half of the colour budget in round `i`; the other half is reserved for
the star cleanup. -/
def roundHalfBudget (r i : ℕ) : ℕ :=
  r / 2 ^ (i + 4)

/-- The finite geometric sum with ratio one half is at most two. -/
theorem geom_sum_half_le_two (T : ℕ) :
    (∑ i ∈ Finset.range T, ((1 : ℝ) / 2) ^ i) ≤ 2 := by
  have hgeom := geom_sum_mul_of_le_one
    (x := (1 : ℝ) / 2) (by norm_num) T
  have hpow : 0 ≤ ((1 : ℝ) / 2) ^ T := by positivity
  have hsum : 0 ≤ ∑ i ∈ Finset.range T, ((1 : ℝ) / 2) ^ i := by
    positivity
  norm_num at hgeom
  nlinarith

/-- The sum of the half-budgets is at most `r/8`, expressed without natural
division as `8 * sum ≤ r`. -/
theorem eight_mul_sum_roundHalfBudget_le (r T : ℕ) :
    8 * (∑ i ∈ Finset.range T, roundHalfBudget r i) ≤ r := by
  have hterm : ∀ i ∈ Finset.range T,
      ((roundHalfBudget r i : ℕ) : ℝ) ≤
        (r : ℝ) / ((2 : ℝ) ^ (i + 4)) := by
    intro i _hi
    simpa only [roundHalfBudget, Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_div_le (m := r) (n := 2 ^ (i + 4)) :
        ((r / 2 ^ (i + 4) : ℕ) : ℝ) ≤
          (r : ℝ) / (2 ^ (i + 4) : ℕ))
  have hsumCast :
      ((∑ i ∈ Finset.range T, roundHalfBudget r i : ℕ) : ℝ) ≤
        ∑ i ∈ Finset.range T,
          (r : ℝ) / ((2 : ℝ) ^ (i + 4)) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum hterm
  have hrewrite :
      (∑ i ∈ Finset.range T,
          (r : ℝ) / ((2 : ℝ) ^ (i + 4))) =
        ((r : ℝ) / 16) *
          ∑ i ∈ Finset.range T, ((1 : ℝ) / 2) ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow]
    field_simp
    ring_nf
  rw [hrewrite] at hsumCast
  have hgeom := geom_sum_half_le_two T
  have hr : 0 ≤ (r : ℝ) / 16 := by positivity
  have hreal :
      ((∑ i ∈ Finset.range T, roundHalfBudget r i : ℕ) : ℝ) ≤
        (r : ℝ) / 8 := by
    calc
      ((∑ i ∈ Finset.range T, roundHalfBudget r i : ℕ) : ℝ) ≤
          ((r : ℝ) / 16) *
            ∑ i ∈ Finset.range T, ((1 : ℝ) / 2) ^ i := hsumCast
      _ ≤ ((r : ℝ) / 16) * 2 :=
        mul_le_mul_of_nonneg_left hgeom hr
      _ = (r : ℝ) / 8 := by ring
  exact_mod_cast (show
    (8 : ℝ) * (∑ i ∈ Finset.range T, roundHalfBudget r i : ℕ) ≤
      (r : ℝ) by nlinarith)

/-- Both halves of all rounds use at most one quarter of the final palette. -/
theorem four_mul_sum_two_roundHalfBudget_le (r T : ℕ) :
    4 * (∑ i ∈ Finset.range T, 2 * roundHalfBudget r i) ≤ r := by
  calc
    4 * (∑ i ∈ Finset.range T, 2 * roundHalfBudget r i) =
        8 * (∑ i ∈ Finset.range T, roundHalfBudget r i) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ r := eight_mul_sum_roundHalfBudget_le r T

end

end LeanCo.SizeRamsey
