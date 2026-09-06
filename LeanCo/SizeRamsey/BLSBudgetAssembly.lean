import LeanCo.SizeRamsey.BLSTerminalNumerics

/-!
# Palette-budget assembly for the BLS iteration

This module identifies the recursive budget used by the combinatorial
iteration with the corresponding finite sum, then combines the geometric
wide-round estimate with the uniform terminal palette.
-/

namespace LeanCo.SizeRamsey

open scoped BigOperators

/-- The recursively defined budget is the ordinary sum over the next
`T` indices. -/
theorem iteratedRoundBudget_eq_sum_range
    (budget : ℕ → ℕ) (i T : ℕ) :
    iteratedRoundBudget budget i T =
      ∑ j ∈ Finset.range T, budget (i + j) := by
  induction T generalizing i with
  | zero => simp
  | succ T ih =>
      calc
        iteratedRoundBudget budget i (T + 1) =
            budget i + iteratedRoundBudget budget (i + 1) T := rfl
        _ = budget i +
              ∑ j ∈ Finset.range T, budget ((i + 1) + j) := by
            rw [ih]
        _ = budget i +
              ∑ j ∈ Finset.range T, budget (i + (j + 1)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            omega
        _ = ∑ j ∈ Finset.range (T + 1), budget (i + j) := by
            rw [Finset.sum_range_succ']
            simp only [Nat.add_zero]
            omega

/-- The recursively accumulated two-sided wide-round palette is at most
half of the ambient `r` colours. -/
theorem two_mul_iterated_wideRoundBudget_le (r T : ℕ) :
    2 * iteratedRoundBudget
        (fun i ↦ 2 * wideRoundHalfBudget r i) 0 T ≤ r := by
  rw [iteratedRoundBudget_eq_sum_range]
  simpa using two_halves_wideRound_total_budget_le r T

/-- Wide rounds followed by the terminal phase use at most `11r/12`
colours, leaving `r/12` for the initial high-core reduction. -/
theorem iterated_wideRound_add_terminal_le_eleven_twelfths
    (r T : ℕ) :
    iteratedRoundBudget (fun i ↦ 2 * wideRoundHalfBudget r i) 0 T +
        blsTerminalPalette r ≤ 11 * r / 12 := by
  have htwo := two_mul_iterated_wideRoundBudget_le r T
  have hhalf :
      iteratedRoundBudget (fun i ↦ 2 * wideRoundHalfBudget r i) 0 T ≤
        r / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    omega
  unfold blsTerminalPalette
  omega

end LeanCo.SizeRamsey
