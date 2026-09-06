import LeanCo.SizeRamsey.RoundBudget
import LeanCo.SizeRamsey.RoundNumerics

/-!
# Dyadic round budgets and geometric gain

This file joins the integer dyadic budget used by a BLS round to the real
geometric-decay estimates.  Besides the exact `log 10` interface, it exposes
a slightly stronger rational interface with the constant `3`, so callers do
not need to manipulate a transcendental constant.
-/

namespace LeanCo.SizeRamsey

noncomputable section

/-- Once the next dyadic scale still fits in `r`, flooring the current-scale
budget loses at most a factor two. -/
theorem div_dyadic_le_roundHalfBudget {r i : ℕ}
    (hr : 2 ^ (i + 5) ≤ r) :
    (r : ℝ) / (2 : ℝ) ^ (i + 5) ≤ (roundHalfBudget r i : ℝ) := by
  have hpow : (2 : ℕ) ^ (i + 5) =
      2 * (2 : ℕ) ^ (i + 4) := by
    rw [show i + 5 = (i + 4) + 1 by omega, pow_succ]
    omega
  have hdpos : 0 < (2 : ℕ) ^ (i + 4) := by positivity
  have hdle : (2 : ℕ) ^ (i + 4) ≤ r := by
    calc
      (2 : ℕ) ^ (i + 4) ≤ 2 * (2 : ℕ) ^ (i + 4) := by
        omega
      _ = 2 ^ (i + 5) := hpow.symm
      _ ≤ r := hr
  have hquotient : 1 ≤ r / (2 : ℕ) ^ (i + 4) := by
    rw [Nat.le_div_iff_mul_le hdpos]
    simpa only [one_mul] using hdle
  have hdivision : r < (2 : ℕ) ^ (i + 4) *
      (r / (2 : ℕ) ^ (i + 4) + 1) :=
    Nat.lt_mul_div_succ r hdpos
  have hnat : r ≤
      (r / (2 : ℕ) ^ (i + 4)) * (2 : ℕ) ^ (i + 5) := by
    calc
      r ≤ (2 : ℕ) ^ (i + 4) *
          (r / (2 : ℕ) ^ (i + 4) + 1) := Nat.le_of_lt hdivision
      _ ≤ (2 : ℕ) ^ (i + 4) *
          (2 * (r / (2 : ℕ) ^ (i + 4))) := by
        exact Nat.mul_le_mul_left _ (by omega)
      _ = (r / (2 : ℕ) ^ (i + 4)) * (2 : ℕ) ^ (i + 5) := by
        rw [hpow]
        ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (i + 5))]
  exact_mod_cast (by simpa only [roundHalfBudget] using hnat)

/-- Positive-gain wrapper around the generic accumulated-exponent estimate
from `RoundNumerics`. -/
theorem one_sub_pow_le_one_tenth_of_pos {a : ℝ}
    (_ha0 : 0 < a) (ha1 : a ≤ 1) (T : ℕ)
    (hAT : Real.log 10 ≤ a * T) :
    (1 - a) ^ T ≤ (1 : ℝ) / 10 := by
  exact one_sub_pow_le_one_tenth ha1 T hAT

/-- General multiplication interface for the dyadic budget.  It is often
more convenient to establish the cross-multiplied lower bound on `a` shown
here than to reason about a quotient. -/
theorem scale_le_mul_roundHalfBudget_of_mul_le
    {r i : ℕ} {a c : ℝ}
    (hr : 2 ^ (i + 5) ≤ r)
    (ha0 : 0 ≤ a)
    (hscale : c * (2 : ℝ) ^ (i + 5) ≤ a * r) :
    c ≤ a * roundHalfBudget r i := by
  have hbudget := div_dyadic_le_roundHalfBudget hr
  have hdpos : (0 : ℝ) < (2 : ℝ) ^ (i + 5) := by positivity
  have hcdiv : c ≤ a * ((r : ℝ) / (2 : ℝ) ^ (i + 5)) := by
    have hdiv : c ≤ (a * (r : ℝ)) / (2 : ℝ) ^ (i + 5) :=
      (le_div_iff₀ hdpos).2 hscale
    simpa only [mul_div_assoc] using hdiv
  exact hcdiv.trans (mul_le_mul_of_nonneg_left hbudget ha0)

/-- A small rational upper bound for the only logarithmic constant used in
the factor-ten decay estimate. -/
theorem log_ten_le_three : Real.log 10 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10)]
  have hseries : (10 : ℝ) ≤
      ∑ k ∈ Finset.range 4, (3 : ℝ) ^ k / (k.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hseries.trans (Real.sum_le_exp_of_nonneg (by norm_num) 4)

/-- Exact accumulated-exponent bridge for a dyadic half-budget. -/
theorem log_ten_le_mul_roundHalfBudget
    {r i : ℕ} {a : ℝ}
    (hr : 2 ^ (i + 5) ≤ r)
    (ha0 : 0 ≤ a)
    (hgain : Real.log 10 * (2 : ℝ) ^ (i + 5) ≤ a * r) :
    Real.log 10 ≤ a * roundHalfBudget r i :=
  scale_le_mul_roundHalfBudget_of_mul_le hr ha0 hgain

/-- The same bridge with no transcendental constant in its hypotheses. -/
theorem log_ten_le_mul_roundHalfBudget_of_three
    {r i : ℕ} {a : ℝ}
    (hr : 2 ^ (i + 5) ≤ r)
    (ha0 : 0 ≤ a)
    (hgain : 3 * (2 : ℝ) ^ (i + 5) ≤ a * r) :
    Real.log 10 ≤ a * roundHalfBudget r i := by
  exact log_ten_le_three.trans
    (scale_le_mul_roundHalfBudget_of_mul_le hr ha0 hgain)

/-- Direct factor-ten decay for the dyadic half-budget, using the exact
`log 10` cross-multiplied gain condition. -/
theorem one_sub_pow_roundHalfBudget_le_one_tenth
    {r i : ℕ} {a : ℝ}
    (hr : 2 ^ (i + 5) ≤ r)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hgain : Real.log 10 * (2 : ℝ) ^ (i + 5) ≤ a * r) :
    (1 - a) ^ roundHalfBudget r i ≤ (1 : ℝ) / 10 := by
  exact one_sub_pow_le_one_tenth_of_pos ha0 ha1 _
    (log_ten_le_mul_roundHalfBudget hr ha0.le hgain)

/-- Paper-facing, transcendental-free version: the explicit real lower bound
`3 * 2^(i+5) / r ≤ a` suffices for factor-ten decay. -/
theorem one_sub_pow_roundHalfBudget_le_one_tenth_of_lower
    {r i : ℕ} {a : ℝ}
    (hr : 2 ^ (i + 5) ≤ r)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hgain : 3 * (2 : ℝ) ^ (i + 5) / r ≤ a) :
    (1 - a) ^ roundHalfBudget r i ≤ (1 : ℝ) / 10 := by
  have hrNat : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hrNat
  have hcross : 3 * (2 : ℝ) ^ (i + 5) ≤ a * r := by
    exact (div_le_iff₀ hrReal).1 hgain
  exact one_sub_pow_le_one_tenth_of_pos ha0 ha1 _
    (log_ten_le_mul_roundHalfBudget_of_three hr ha0.le hcross)

end

end LeanCo.SizeRamsey
