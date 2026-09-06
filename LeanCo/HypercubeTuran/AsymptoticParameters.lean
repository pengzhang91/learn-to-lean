import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# A reusable polynomial-versus-exponential parameter lemma

The random construction only needs the existence of a sufficiently large
natural average-degree parameter.  These lemmas package the standard fact
that a fixed polynomial is eventually dominated by every positive
exponential, including after restriction from reals to natural numbers.
-/

open Filter
open scoped Topology

namespace LeanCo.HypercubeTuran

noncomputable section

/-- A positive constant times a fixed natural power is eventually bounded by
`exp (b*x)` for every `b > 0`. -/
theorem eventually_const_mul_pow_le_exp
    (K : ℝ) (hK : 0 < K) (n : ℕ) (b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, K * x ^ n ≤ Real.exp (b * x) := by
  have hsmall :=
    (isLittleO_pow_exp_pos_mul_atTop n hb).bound
      (show (0 : ℝ) < 1 / K by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hx' : x ^ n ≤ (1 / K) * Real.exp (b * x) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx0 n),
      abs_of_nonneg hx0, abs_of_pos (Real.exp_pos _)] using hx
  calc
    K * x ^ n ≤ K * ((1 / K) * Real.exp (b * x)) :=
      mul_le_mul_of_nonneg_left hx' hK.le
    _ = Real.exp (b * x) := by field_simp

/-- Natural-number form, with an arbitrary prescribed lower bound. -/
theorem exists_nat_ge_const_mul_pow_le_exp
    (K : ℝ) (hK : 0 < K) (n M : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ d : ℕ, M ≤ d ∧ K * (d : ℝ) ^ n ≤ Real.exp (b * d) := by
  have hreal := eventually_const_mul_pow_le_exp K hK n b hb
  have hnat : ∀ᶠ d : ℕ in atTop,
      K * (d : ℝ) ^ n ≤ Real.exp (b * d) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  have hlarge : ∀ᶠ d : ℕ in atTop, M ≤ d := eventually_ge_atTop M
  obtain ⟨d, hd, hMd⟩ := (hnat.and hlarge).exists
  exact ⟨d, hMd, hd⟩

end

end LeanCo.HypercubeTuran
