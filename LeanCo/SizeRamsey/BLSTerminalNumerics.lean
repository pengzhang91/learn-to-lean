import LeanCo.SizeRamsey.BLSRoundScheduleNumerics
import LeanCo.SizeRamsey.BLSRoundRecursion

/-!
# Explicit numerical parameters for the BLS terminal phase

The small-edge terminal graph is star-cleaned with `r/32` colours.  A coarse
degree cap `ceil (5120 r^(3/4))` then finishes the remainder.  Once
`r^(1/4) ≥ 50000`, this entire terminal phase and the low-degree alternative
both fit in the uniform palette `floor (5r/12)`.
-/

namespace LeanCo.SizeRamsey

noncomputable section

/-- Star colours reserved for the small-edge terminal case. -/
def blsTerminalStarBudget (r : ℕ) : ℕ := r / 32

/-- Degree cap after terminal star cleanup. -/
def blsTerminalDegreeCap (r : ℕ) : ℕ :=
  ⌈5120 * Real.rpow (r : ℝ) (3 / 4 : ℝ)⌉₊

/-- Uniform terminal palette, also large enough for the degree-side stop. -/
def blsTerminalPalette (r : ℕ) : ℕ := 5 * r / 12

theorem blsTerminalStarBudget_pos {r : ℕ} (hr : 32 ≤ r) :
    0 < blsTerminalStarBudget r := by
  unfold blsTerminalStarBudget
  exact Nat.div_pos hr (by omega)

/-- The natural quotient returned by star cleanup is bounded by the explicit
three-quarter-power cap. -/
theorem blsTerminal_quotient_le_degreeCap
    {r n m : ℕ} (hr : 64 ≤ r) (hn : 0 < n)
    (hm : (m : ℝ) <
      10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n)) :
    8 * m / (n * blsTerminalStarBudget r) ≤
      blsTerminalDegreeCap r := by
  let T := blsTerminalStarBudget r
  have hTtwo : 2 ≤ T := by
    dsimp only [T, blsTerminalStarBudget]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 32)).2
    omega
  have hTpos : 0 < T := by omega
  have hrlt : r < 32 * (r / 32 + 1) := Nat.lt_mul_div_succ r (by omega)
  have hrTnat : r ≤ 64 * T := by
    dsimp only [T, blsTerminalStarBudget]
    omega
  have hrT : (r : ℝ) ≤ 64 * T := by exact_mod_cast hrTnat
  have hrpos : (0 : ℝ) < r := by positivity
  have hthreeQuarter : 0 ≤ Real.rpow (r : ℝ) (3 / 4 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hpow : Real.rpow (r : ℝ) (7 / 4 : ℝ) =
      Real.rpow (r : ℝ) (3 / 4 : ℝ) * r := by
    calc
      Real.rpow (r : ℝ) (7 / 4 : ℝ) =
          Real.rpow (r : ℝ) (3 / 4 + 1 : ℝ) := by norm_num
      _ = Real.rpow (r : ℝ) (3 / 4 : ℝ) *
          Real.rpow (r : ℝ) 1 := Real.rpow_add hrpos _ _
      _ = Real.rpow (r : ℝ) (3 / 4 : ℝ) * r := by
        simp
  have hdenNat : 0 < n * T := Nat.mul_pos hn hTpos
  have hcastDiv :
      ((8 * m / (n * T) : ℕ) : ℝ) ≤
        (8 * m : ℝ) / (n * T : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_div_le (m := 8 * m) (n := n * T) :
        ((8 * m / (n * T) : ℕ) : ℝ) ≤
          ((8 * m : ℕ) : ℝ) / ((n * T : ℕ) : ℝ))
  have hdenReal : (0 : ℝ) < (n * T : ℕ) := by exact_mod_cast hdenNat
  have hreal : (8 * m : ℝ) / (n * T : ℕ) <
      5120 * Real.rpow (r : ℝ) (3 / 4 : ℝ) := by
    apply (div_lt_iff₀ hdenReal).2
    calc
      (8 * m : ℝ) <
          8 * (10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n)) := by
        exact mul_lt_mul_of_pos_left hm (by norm_num)
      _ = 80 * Real.rpow (r : ℝ) (3 / 4 : ℝ) * r * n := by
        rw [hpow]
        ring
      _ ≤ 80 * Real.rpow (r : ℝ) (3 / 4 : ℝ) * (64 * T) * n := by
        gcongr
      _ = 5120 * Real.rpow (r : ℝ) (3 / 4 : ℝ) * (n * T : ℕ) := by
        push_cast
        ring
  have hceil : 5120 * Real.rpow (r : ℝ) (3 / 4 : ℝ) ≤
      (blsTerminalDegreeCap r : ℕ) := by
    unfold blsTerminalDegreeCap
    exact Nat.le_ceil _
  exact_mod_cast hcastDiv.trans (hreal.le.trans hceil)

/-- A fourth-power natural threshold implies the convenient quarter-power
lower bound. -/
theorem fifty_thousand_le_rpow_quarter {r : ℕ}
    (hr : 50000 ^ 4 ≤ r) :
    (50000 : ℝ) ≤ Real.rpow (r : ℝ) (1 / 4 : ℝ) := by
  have hcast : ((50000 : ℝ) ^ 4) ≤ (r : ℝ) := by
    exact_mod_cast hr
  have hmono := Real.rpow_le_rpow (show (0 : ℝ) ≤ (50000 : ℝ) ^ 4 by positivity)
    hcast (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hroot : Real.rpow ((50000 : ℝ) ^ 4) (1 / 4 : ℝ) = 50000 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast
      (by norm_num : (0 : ℝ) ≤ 50000) (by norm_num : (4 : ℕ) ≠ 0)
  calc
    (50000 : ℝ) = Real.rpow ((50000 : ℝ) ^ 4) (1 / 4 : ℝ) := hroot.symm
    _ ≤ Real.rpow (r : ℝ) (1 / 4 : ℝ) := hmono

/-- At the explicit large-`r` threshold the terminal degree cap is at most
`r/8`. -/
theorem blsTerminalDegreeCap_le_div_eight {r : ℕ}
    (hr : 50000 ^ 4 ≤ r) :
    blsTerminalDegreeCap r ≤ r / 8 := by
  have hrOne : (1 : ℝ) ≤ r := by
    exact_mod_cast (show 1 ≤ r by omega)
  have hAone : (1 : ℝ) ≤ Real.rpow (r : ℝ) (3 / 4 : ℝ) :=
    Real.one_le_rpow hrOne (by norm_num)
  have hquarter := fifty_thousand_le_rpow_quarter hr
  have hrpos : (0 : ℝ) < r := by positivity
  have hsplit : Real.rpow (r : ℝ) (3 / 4 : ℝ) *
      Real.rpow (r : ℝ) (1 / 4 : ℝ) = r := by
    calc
      Real.rpow (r : ℝ) (3 / 4 : ℝ) *
          Real.rpow (r : ℝ) (1 / 4 : ℝ) =
          Real.rpow (r : ℝ) (3 / 4 + 1 / 4 : ℝ) :=
        (Real.rpow_add hrpos _ _).symm
      _ = Real.rpow (r : ℝ) 1 := by norm_num
      _ = r := Real.rpow_one _
  have hmass : 50000 * Real.rpow (r : ℝ) (3 / 4 : ℝ) ≤ r := by
    calc
      50000 * Real.rpow (r : ℝ) (3 / 4 : ℝ) ≤
          Real.rpow (r : ℝ) (1 / 4 : ℝ) *
            Real.rpow (r : ℝ) (3 / 4 : ℝ) := by gcongr
      _ = r := by rw [mul_comm, hsplit]
  have hceil : (blsTerminalDegreeCap r : ℝ) <
      5120 * Real.rpow (r : ℝ) (3 / 4 : ℝ) + 1 := by
    unfold blsTerminalDegreeCap
    exact Nat.ceil_lt_add_one (by positivity)
  have h8real : ((8 * blsTerminalDegreeCap r : ℕ) : ℝ) ≤ (r : ℝ) := by
    push_cast
    nlinarith
  have h8nat : 8 * blsTerminalDegreeCap r ≤ r := by exact_mod_cast h8real
  omega

theorem wideRoundHalfBudget_le_div_eight (r i : ℕ) :
    wideRoundHalfBudget r i ≤ r / 8 := by
  unfold wideRoundHalfBudget
  have hden : 8 ≤ 2 ^ (i + 3) := by
    rw [pow_add]
    norm_num
    exact Nat.one_le_pow i 2 (by omega)
  exact (Nat.div_le_div (Nat.le_refl r) hden) (by omega)

/-- The low-degree stop, including the current extraction block, fits in the
uniform terminal palette. -/
theorem wideRound_lowDegree_budget_le_terminalPalette
    {r i : ℕ} (hr : 168 ≤ r) :
    wideRoundHalfBudget r i + (2 * (r / 7) + 1) ≤
      blsTerminalPalette r := by
  have hwide := wideRoundHalfBudget_le_div_eight r i
  unfold blsTerminalPalette
  omega

/-- The star-cleanup terminal palette also fits in the same uniform budget. -/
theorem blsTerminal_cleanup_budget_le_palette {r : ℕ}
    (hr : 50000 ^ 4 ≤ r) :
    blsTerminalStarBudget r + (2 * blsTerminalDegreeCap r + 1) ≤
      blsTerminalPalette r := by
  have hdegree := blsTerminalDegreeCap_le_div_eight hr
  unfold blsTerminalStarBudget blsTerminalPalette
  omega

end

end LeanCo.SizeRamsey
