import LeanCo.SizeRamsey.BLSRoundScheduleNumerics
import Mathlib.Tactic

/-!
# Edge and degree bookkeeping for the BLS star-cleanup schedule

This file supplies the floor-sensitive numerical estimates that connect the
geometric edge caps with the integer colour budgets of the wide rounds.
-/

namespace LeanCo.SizeRamsey

noncomputable section

/-- The edge cap at round `i`. -/
def roundEdgeCap (C : ℝ) (r n i : ℕ) : ℝ :=
  C * (r : ℝ) ^ 2 * Real.log (r : ℝ) * (n : ℝ) / (10 : ℝ) ^ i

/-- Dividing a round cap by ten gives the next cap. -/
theorem roundEdgeCap_div_ten (C : ℝ) (r n i : ℕ) :
    roundEdgeCap C r n i / 10 = roundEdgeCap C r n (i + 1) := by
  unfold roundEdgeCap
  rw [pow_succ]
  ring

/-- Natural logarithms of natural numbers are nonnegative (including zero,
where mathlib defines `log 0 = 0`). -/
private theorem log_natCast_nonneg (r : ℕ) :
    0 ≤ Real.log (r : ℝ) := by
  cases r with
  | zero => simp
  | succ r =>
      apply Real.log_nonneg
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)

/-- A nonnegative coefficient gives a nonnegative round cap. -/
theorem roundEdgeCap_nonneg {C : ℝ} (hC : 0 ≤ C) (r n i : ℕ) :
    0 ≤ roundEdgeCap C r n i := by
  unfold roundEdgeCap
  positivity

/-- If the leading constant is at most one, every round cap is bounded by
the unscaled global edge expression. -/
theorem roundEdgeCap_le_global {C : ℝ} (hC : 0 ≤ C) (hCOne : C ≤ 1)
    (r n i : ℕ) :
    roundEdgeCap C r n i ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * (n : ℝ) := by
  have hbase :
      0 ≤ (r : ℝ) ^ 2 * Real.log (r : ℝ) * (n : ℝ) := by
    positivity
  calc
    roundEdgeCap C r n i =
        C * ((r : ℝ) ^ 2 * Real.log (r : ℝ) * (n : ℝ)) /
          (10 : ℝ) ^ i := by
      unfold roundEdgeCap
      ring
    _ ≤ C * ((r : ℝ) ^ 2 * Real.log (r : ℝ) * (n : ℝ)) :=
      div_le_self (mul_nonneg hC hbase) (one_le_pow₀ (by norm_num))
    _ ≤ 1 * ((r : ℝ) ^ 2 * Real.log (r : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hCOne hbase
    _ = (r : ℝ) ^ 2 * Real.log (r : ℝ) * (n : ℝ) := by ring

/-! ## The integer floor estimate -/

/-- The loss from flooring the half-budget is absorbed by a factor `3/2`.
The hypothesis ensures that the quotient is at least two. -/
theorem two_mul_le_three_mul_pow_mul_wideRoundHalfBudget
    {r i : ℕ} (hr : 2 ^ (i + 4) ≤ r) :
    2 * r ≤
      3 * 2 ^ (i + 3) * wideRoundHalfBudget r i := by
  let q : ℕ := 2 ^ (i + 3)
  have hqpos : 0 < q := by simp [q]
  have hTtwo : 2 ≤ r / q := by
    apply (Nat.le_div_iff_mul_le hqpos).2
    simpa [q, show i + 4 = (i + 3) + 1 by omega, pow_succ,
      Nat.mul_comm] using hr
  have hrlt : r < q * (r / q + 1) := Nat.lt_mul_div_succ r hqpos
  calc
    2 * r ≤ 2 * (q * (r / q + 1)) := Nat.mul_le_mul_left 2 hrlt.le
    _ = q * (2 * (r / q + 1)) := by ring
    _ ≤ q * (3 * (r / q)) := by
      apply Nat.mul_le_mul_left
      omega
    _ = 3 * q * (r / q) := by ring
    _ = 3 * 2 ^ (i + 3) * wideRoundHalfBudget r i := by
      simp [q, wideRoundHalfBudget]

/-! ## The geometric coefficient -/

/-- The elementary integer estimate behind the interaction of the binary,
ternary, and decimal schedules. -/
private theorem round_schedule_coefficient_nat (i : ℕ) :
    12 * 2 ^ (i + 3) * 3 ^ (i + 1) ≤ 100 * 10 ^ (i + 1) := by
  have hp : 6 ^ i ≤ 10 ^ i := Nat.pow_le_pow_left (by omega) i
  calc
    12 * 2 ^ (i + 3) * 3 ^ (i + 1) = 288 * (2 ^ i * 3 ^ i) := by
      rw [pow_add, pow_succ]
      ring
    _ = 288 * 6 ^ i := by
      rw [← mul_pow]
      norm_num
    _ ≤ 288 * 10 ^ i := Nat.mul_le_mul_left 288 hp
    _ ≤ 1000 * 10 ^ i := Nat.mul_le_mul_right (10 ^ i) (by omega)
    _ = 100 * 10 ^ (i + 1) := by
      rw [pow_succ]
      ring

/-- `100 C ≤ β₀` leaves enough room for all three geometric schedules. -/
theorem round_schedule_coefficient_le
    {C β₀ : ℝ} (hC : 0 < C) (hCβ : 100 * C ≤ β₀) (i : ℕ) :
    12 * C * (2 : ℝ) ^ (i + 3) / (10 : ℝ) ^ (i + 1) ≤
      roundBeta β₀ (i + 1) := by
  have hconst :
      (12 : ℝ) * (2 : ℝ) ^ (i + 3) * (3 : ℝ) ^ (i + 1) ≤
        100 * (10 : ℝ) ^ (i + 1) := by
    exact_mod_cast round_schedule_coefficient_nat i
  unfold roundBeta
  apply (div_le_div_iff₀ (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)).2
  calc
    12 * C * (2 : ℝ) ^ (i + 3) * (3 : ℝ) ^ (i + 1) =
        C * (12 * (2 : ℝ) ^ (i + 3) * (3 : ℝ) ^ (i + 1)) := by ring
    _ ≤ C * (100 * (10 : ℝ) ^ (i + 1)) :=
      mul_le_mul_of_nonneg_left hconst hC.le
    _ = (100 * C) * (10 : ℝ) ^ (i + 1) := by ring
    _ ≤ β₀ * (10 : ℝ) ^ (i + 1) :=
      mul_le_mul_of_nonneg_right hCβ (by positivity)

/-! ## Recursive and initial star-cleanup bounds -/

/-- If the remaining edge count has fallen below one tenth of round `i`'s
cap, the integer star-cleanup quotient fits under the next beta threshold. -/
theorem star_quotient_le_roundBeta_succ
    {C β₀ : ℝ} {r n i m : ℕ}
    (hC : 0 < C) (hCβ : 100 * C ≤ β₀)
    (hr : 2 ^ (i + 4) ≤ r) (hn : 12 ≤ n)
    (hm : (m : ℝ) ≤ roundEdgeCap C r n i / 10) :
    (((8 * m) / (n * wideRoundHalfBudget r i) : ℕ) : ℝ) ≤
      roundBeta β₀ (i + 1) * (r : ℝ) * Real.log (r : ℝ) := by
  let T : ℕ := wideRoundHalfBudget r i
  have hrpos : 0 < r :=
    lt_of_lt_of_le (pow_pos (by omega) (i + 4)) hr
  have hTtwo : 2 ≤ T := by
    dsimp only [T, wideRoundHalfBudget]
    apply (Nat.le_div_iff_mul_le (pow_pos (by omega) (i + 3))).2
    simpa [show i + 4 = (i + 3) + 1 by omega, pow_succ,
      Nat.mul_comm] using hr
  have hnpos : 0 < n := lt_of_lt_of_le (by omega) hn
  have hTpos : 0 < T := lt_of_lt_of_le (by omega) hTtwo
  have hlog : 0 ≤ Real.log (r : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hrpos
  have hfloor :
      (2 : ℝ) * (r : ℝ) ≤
        3 * (2 : ℝ) ^ (i + 3) * (T : ℝ) := by
    exact_mod_cast
      (two_mul_le_three_mul_pow_mul_wideRoundHalfBudget hr)
  have hcoef :
      12 * C * (2 : ℝ) ^ (i + 3) / (10 : ℝ) ^ (i + 1) ≤
        roundBeta β₀ (i + 1) :=
    round_schedule_coefficient_le hC hCβ i
  have hmNext : (m : ℝ) ≤ roundEdgeCap C r n (i + 1) := by
    simpa only [roundEdgeCap_div_ten] using hm
  have hfactor :
      0 ≤ 4 * C * (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) /
        (10 : ℝ) ^ (i + 1) := by
    positivity
  have htail :
      0 ≤ (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) * (T : ℝ) := by
    positivity
  have hcross :
      (8 : ℝ) * (m : ℝ) ≤
        roundBeta β₀ (i + 1) * (r : ℝ) * Real.log (r : ℝ) *
          ((n : ℝ) * (T : ℝ)) := by
    calc
      (8 : ℝ) * (m : ℝ) ≤
          8 * roundEdgeCap C r n (i + 1) :=
        mul_le_mul_of_nonneg_left hmNext (by norm_num)
      _ =
          (4 * C * (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) /
              (10 : ℝ) ^ (i + 1)) * (2 * (r : ℝ)) := by
        unfold roundEdgeCap
        ring
      _ ≤
          (4 * C * (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) /
              (10 : ℝ) ^ (i + 1)) *
            (3 * (2 : ℝ) ^ (i + 3) * (T : ℝ)) :=
        mul_le_mul_of_nonneg_left hfloor hfactor
      _ =
          (12 * C * (2 : ℝ) ^ (i + 3) / (10 : ℝ) ^ (i + 1)) *
            ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) * (T : ℝ)) := by
        ring
      _ ≤ roundBeta β₀ (i + 1) *
            ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) * (T : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef htail
      _ = roundBeta β₀ (i + 1) * (r : ℝ) * Real.log (r : ℝ) *
            ((n : ℝ) * (T : ℝ)) := by ring
  calc
    (((8 * m) / (n * wideRoundHalfBudget r i) : ℕ) : ℝ) =
        (((8 * m) / (n * T) : ℕ) : ℝ) := by rfl
    _ ≤ ((8 * m : ℕ) : ℝ) / ((n * T : ℕ) : ℝ) :=
      Nat.cast_div_le
    _ ≤ roundBeta β₀ (i + 1) * (r : ℝ) * Real.log (r : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((n * T : ℕ) : ℝ))).2
      push_cast
      simpa only [mul_assoc] using hcross

/-- The initial cleanup, before a factor-ten reduction has occurred, fits
under the original beta threshold. -/
theorem initial_star_quotient_le_beta
    {C β₀ : ℝ} {r n e : ℕ}
    (hC : 0 < C) (hCβ : 100 * C ≤ β₀)
    (hr : 16 ≤ r) (hn : 12 ≤ n)
    (he : (e : ℝ) ≤ roundEdgeCap C r n 0) :
    (((8 * e) / (n * wideRoundHalfBudget r 0) : ℕ) : ℝ) ≤
      β₀ * (r : ℝ) * Real.log (r : ℝ) := by
  let T : ℕ := wideRoundHalfBudget r 0
  have hrpow : 2 ^ (0 + 4) ≤ r := by simpa using hr
  have hrpos : 0 < r := lt_of_lt_of_le (by omega) hr
  have hTtwo : 2 ≤ T := by
    dsimp only [T, wideRoundHalfBudget]
    norm_num
    exact (Nat.le_div_iff_mul_le (by omega)).2 hr
  have hnpos : 0 < n := lt_of_lt_of_le (by omega) hn
  have hTpos : 0 < T := lt_of_lt_of_le (by omega) hTtwo
  have hlog : 0 ≤ Real.log (r : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hrpos
  have hfloor :
      (2 : ℝ) * (r : ℝ) ≤ 24 * (T : ℝ) := by
    have h := two_mul_le_three_mul_pow_mul_wideRoundHalfBudget hrpow
    norm_num at h ⊢
    exact_mod_cast h
  have h96 : 96 * C ≤ β₀ := by
    calc
      96 * C ≤ 100 * C := by nlinarith [hC.le]
      _ ≤ β₀ := hCβ
  have hfactor :
      0 ≤ 4 * C * (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) := by
    positivity
  have htail :
      0 ≤ (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) * (T : ℝ) := by
    positivity
  have hcross :
      (8 : ℝ) * (e : ℝ) ≤
        β₀ * (r : ℝ) * Real.log (r : ℝ) * ((n : ℝ) * (T : ℝ)) := by
    calc
      (8 : ℝ) * (e : ℝ) ≤ 8 * roundEdgeCap C r n 0 :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ = (4 * C * (r : ℝ) * Real.log (r : ℝ) * (n : ℝ)) *
            (2 * (r : ℝ)) := by
        unfold roundEdgeCap
        norm_num
        ring
      _ ≤ (4 * C * (r : ℝ) * Real.log (r : ℝ) * (n : ℝ)) *
            (24 * (T : ℝ)) :=
        mul_le_mul_of_nonneg_left hfloor hfactor
      _ = (96 * C) *
            ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) * (T : ℝ)) := by
        ring
      _ ≤ β₀ *
            ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) * (T : ℝ)) :=
        mul_le_mul_of_nonneg_right h96 htail
      _ = β₀ * (r : ℝ) * Real.log (r : ℝ) *
            ((n : ℝ) * (T : ℝ)) := by ring
  calc
    (((8 * e) / (n * wideRoundHalfBudget r 0) : ℕ) : ℝ) =
        (((8 * e) / (n * T) : ℕ) : ℝ) := by rfl
    _ ≤ ((8 * e : ℕ) : ℝ) / ((n * T : ℕ) : ℝ) :=
      Nat.cast_div_le
    _ ≤ β₀ * (r : ℝ) * Real.log (r : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((n * T : ℕ) : ℝ))).2
      push_cast
      simpa only [mul_assoc] using hcross

end

end LeanCo.SizeRamsey
