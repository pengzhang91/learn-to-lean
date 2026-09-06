import LeanCo.SizeRamsey.BLSStarScheduleNumerics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Edge caps and the base-ten horizon in the BLS iteration

The BLS lower-bound iteration reduces the residual edge mass by a factor ten
in every round.  Thus its natural horizon is `Nat.log 10 r`, rather than a
binary logarithm.  This file records both the exact edge-cap arithmetic and
the comparison with the dyadic colour budget used inside each round.
-/

namespace LeanCo.SizeRamsey

open Filter

noncomputable section

/-- The edge-mass target after `i` factor-ten reductions. -/
def baseTenEdgeCap (E : ℝ) (i : ℕ) : ℝ :=
  E / (10 : ℝ) ^ i

/-- The number of complete factor-ten scales below `r`. -/
def roundHorizon (r : ℕ) : ℕ :=
  Nat.log 10 r

/-- The literal fractional extraction rate occurring with `roundBeta`. -/
def scheduledExtractionRate (beta0 : ℝ) (r i : ℕ) : ℝ :=
  60 / (roundBeta beta0 i ^ (9 / 10 : ℝ) * r)

@[simp] theorem scheduledExtractionRate_eq_blsExtractionRate
    (beta0 : ℝ) (r i : ℕ) :
    scheduledExtractionRate beta0 r i =
      blsExtractionRate r (roundBeta beta0 i) := rfl

@[simp] theorem baseTenEdgeCap_zero (E : ℝ) :
    baseTenEdgeCap E 0 = E := by
  simp [baseTenEdgeCap]

/-- Passing to the next cap is exactly division by ten. -/
theorem baseTenEdgeCap_div_ten (E : ℝ) (i : ℕ) :
    baseTenEdgeCap E i / 10 = baseTenEdgeCap E (i + 1) := by
  simp only [baseTenEdgeCap, pow_succ]
  ring

/-- Every later cap is at most the initial nonnegative edge mass. -/
theorem baseTenEdgeCap_le_initial {E : ℝ} (hE : 0 ≤ E) (i : ℕ) :
    baseTenEdgeCap E i ≤ E := by
  unfold baseTenEdgeCap
  exact div_le_self hE (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 10))

/-- The lower endpoint supplied by the defining property of `Nat.log`. -/
theorem ten_pow_roundHorizon_le {r : ℕ} (hr : 0 < r) :
    10 ^ roundHorizon r ≤ r := by
  exact Nat.pow_log_le_self 10 hr.ne'

/-- The corresponding strict upper endpoint of the base-ten block. -/
theorem lt_ten_pow_roundHorizon_succ (r : ℕ) :
    r < 10 ^ (roundHorizon r + 1) := by
  simpa [roundHorizon, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (by omega : 1 < (10 : ℕ)) r

/-- For horizons of length at least two, the base-ten scale dominates the
shifted binary scale required by the dyadic colour budget. -/
theorem eight_mul_two_pow_le_ten_pow {J : ℕ} (hJ : 2 ≤ J) :
    8 * 2 ^ J ≤ 10 ^ J := by
  have hfive : 8 ≤ 5 ^ J := by
    calc
      8 ≤ 5 ^ 2 := by norm_num
      _ ≤ 5 ^ J := Nat.pow_le_pow_right (by omega) hJ
  rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
  nlinarith [Nat.zero_le (2 ^ J)]

/-- A round strictly before the base-ten horizon fits in its dyadic budget:
`2^(i+4)` is no larger than `r`. -/
theorem two_pow_round_add_four_le {r i : ℕ}
    (horizon_ge_two : 2 ≤ roundHorizon r)
    (hi : i < roundHorizon r) :
    2 ^ (i + 4) ≤ r := by
  let J := roundHorizon r
  have hr : 0 < r := by
    by_contra hr0
    have : r = 0 := Nat.eq_zero_of_not_pos hr0
    subst r
    simp [roundHorizon] at horizon_ge_two
  have hexponent : i + 4 ≤ J + 3 := by
    dsimp [J]
    omega
  have hbinary : 2 ^ (i + 4) ≤ 8 * 2 ^ J := by
    calc
      2 ^ (i + 4) ≤ 2 ^ (J + 3) :=
        Nat.pow_le_pow_right (by omega) hexponent
      _ = 8 * 2 ^ J := by ring
  exact hbinary.trans ((eight_mul_two_pow_le_ten_pow horizon_ge_two).trans
    (ten_pow_roundHorizon_le hr))

/-- The preceding comparison with an explicit, paper-usable threshold. -/
theorem two_pow_round_add_four_le_of_hundred_le {r i : ℕ}
    (hr : 100 ≤ r) (hi : i < roundHorizon r) :
    2 ^ (i + 4) ≤ r := by
  apply two_pow_round_add_four_le _ hi
  exact Nat.le_log_of_pow_le (by omega)
    (by simpa using hr : 10 ^ 2 ≤ r)

/-! ## The terminal edge cap -/

/-- Uniformly for fixed `c ≤ 1`, the logarithmic factor is eventually
strictly smaller than the three-quarter power.  (Allowing negative `c` only
strengthens the conclusion.)  The threshold is stated over natural numbers
because that is the form used by the iteration. -/
theorem exists_mul_log_lt_rpow_three_quarters_nat {c : ℝ}
    (hc1 : c ≤ 1) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      c * Real.log (r : ℝ) < (r : ℝ) ^ (3 / 4 : ℝ) := by
  have hsmall : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ (1 / 2 : ℝ) * ‖x ^ (3 / 4 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).bound
      (by norm_num)
  have hreal : ∀ᶠ x : ℝ in atTop,
      c * Real.log x < x ^ (3 / 4 : ℝ) := by
    filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hrpow : 0 < x ^ (3 / 4 : ℝ) :=
      Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _
    have hx' : Real.log x ≤ (1 / 2 : ℝ) * x ^ (3 / 4 : ℝ) := by
      simpa [Real.norm_eq_abs, abs_of_pos hlog, abs_of_pos hrpow] using hx
    have hcLog : c * Real.log x ≤ Real.log x :=
      mul_le_of_le_one_left hlog.le hc1
    exact hcLog.trans_lt (hx'.trans_lt (by nlinarith))
  exact eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually hreal)

/-- The exact deterministic calculation behind the terminal cap.  Its only
asymptotic input is exposed as the inequality `c log r < r^(3/4)`. -/
theorem baseTenEdgeCap_lt_terminal_of_log_bound
    {c E : ℝ} {r n : ℕ}
    (hr : 0 < r) (hn : 0 < n) (hc : 0 ≤ c)
    (hlog : c * Real.log (r : ℝ) < (r : ℝ) ^ (3 / 4 : ℝ))
    (hEupper : E ≤ c * (r : ℝ) ^ 2 * Real.log (r : ℝ) * n) :
    baseTenEdgeCap E (roundHorizon r) <
      10 * (r : ℝ) ^ (7 / 4 : ℝ) * n := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlogNonneg : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hrOne
  have hdenom : (0 : ℝ) < (10 : ℝ) ^ roundHorizon r := by positivity
  have hblockNat := lt_ten_pow_roundHorizon_succ r
  have hblockReal : (r : ℝ) < (10 : ℝ) ^ (roundHorizon r + 1) := by
    exact_mod_cast hblockNat
  have hrDiv : (r : ℝ) / (10 : ℝ) ^ roundHorizon r < 10 := by
    apply (div_lt_iff₀ hdenom).2
    simpa [pow_succ, mul_comm] using hblockReal
  have hinner :
      c * (r : ℝ) * Real.log (r : ℝ) * n <
        (r : ℝ) ^ (7 / 4 : ℝ) * n := by
    have hmulR := mul_lt_mul_of_pos_right hlog hrReal
    have hmulN := mul_lt_mul_of_pos_right hmulR hnReal
    calc
      c * (r : ℝ) * Real.log (r : ℝ) * n =
          (c * Real.log (r : ℝ)) * r * n := by ring
      _ < ((r : ℝ) ^ (3 / 4 : ℝ)) * r * n := hmulN
      _ = (r : ℝ) ^ (7 / 4 : ℝ) * n := by
        have hpow :
            (r : ℝ) ^ (3 / 4 : ℝ) * r =
              (r : ℝ) ^ (7 / 4 : ℝ) := by
          calc
            (r : ℝ) ^ (3 / 4 : ℝ) * r =
                (r : ℝ) ^ (3 / 4 : ℝ) * (r : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
            _ = (r : ℝ) ^ ((3 / 4 : ℝ) + 1) :=
              (Real.rpow_add hrReal _ _).symm
            _ = (r : ℝ) ^ (7 / 4 : ℝ) := by norm_num
        rw [hpow]
  have hinnerNonneg :
      0 ≤ c * (r : ℝ) * Real.log (r : ℝ) * n := by
    positivity
  have hcap :
      baseTenEdgeCap E (roundHorizon r) ≤
        (c * (r : ℝ) ^ 2 * Real.log (r : ℝ) * n) /
          (10 : ℝ) ^ roundHorizon r := by
    unfold baseTenEdgeCap
    exact (div_le_div_iff_of_pos_right hdenom).2 hEupper
  calc
    baseTenEdgeCap E (roundHorizon r) ≤
        (c * (r : ℝ) ^ 2 * Real.log (r : ℝ) * n) /
          (10 : ℝ) ^ roundHorizon r := hcap
    _ = ((r : ℝ) / (10 : ℝ) ^ roundHorizon r) *
          (c * r * Real.log (r : ℝ) * n) := by ring
    _ ≤ 10 * (c * r * Real.log (r : ℝ) * n) :=
      mul_le_mul_of_nonneg_right hrDiv.le hinnerNonneg
    _ < 10 * ((r : ℝ) ^ (7 / 4 : ℝ) * n) :=
      mul_lt_mul_of_pos_left hinner (by norm_num)
    _ = 10 * (r : ℝ) ^ (7 / 4 : ℝ) * n := by ring

/-- The paper-facing terminal-cap estimate.  The assumption `n > 0` is
necessary for a strict conclusion: the requested right-hand side is zero
when `n = 0`. -/
theorem exists_baseTenEdgeCap_terminal_threshold {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ R : ℕ, ∀ {r n : ℕ} {E : ℝ}, R ≤ r → 0 < n →
      E ≤ c * (r : ℝ) ^ 2 * Real.log (r : ℝ) * n →
      baseTenEdgeCap E (roundHorizon r) <
        10 * (r : ℝ) ^ (7 / 4 : ℝ) * n := by
  obtain ⟨R, hR⟩ := exists_mul_log_lt_rpow_three_quarters_nat hc1
  refine ⟨max R 1, ?_⟩
  intro r n E hr hn hEupper
  have hrR : R ≤ r := (le_max_left R 1).trans hr
  have hrPos : 0 < r := (Nat.zero_lt_one.trans_le ((le_max_right R 1).trans hr))
  exact baseTenEdgeCap_lt_terminal_of_log_bound hrPos hn hc0
    (hR r hrR) hEupper

/-- The generic base-ten cap agrees with the concrete four-parameter cap
used by the BLS recursion. -/
theorem roundEdgeCap_eq_baseTenEdgeCap
    (C : ℝ) (r n i : ℕ) :
    roundEdgeCap C r n i =
      baseTenEdgeCap (roundEdgeCap C r n 0) i := by
  simp [roundEdgeCap, baseTenEdgeCap]

/-- Eventual terminal estimate, specialized to the concrete recursion
schedule. -/
theorem exists_roundEdgeCap_schedule_terminal_threshold
    {C : ℝ} (hC0 : 0 ≤ C) (hC1 : C ≤ 1) :
    ∃ R : ℕ, ∀ {r n : ℕ}, R ≤ r → 0 < n →
      roundEdgeCap C r n (roundHorizon r) <
        10 * (r : ℝ) ^ (7 / 4 : ℝ) * n := by
  obtain ⟨R, hR⟩ := exists_baseTenEdgeCap_terminal_threshold hC0 hC1
  refine ⟨R, ?_⟩
  intro r n hr hn
  rw [roundEdgeCap_eq_baseTenEdgeCap]
  exact hR (r := r) (n := n)
    (E := roundEdgeCap C r n 0) hr hn (by simp [roundEdgeCap])

/-! ## The extraction-rate schedule -/

/-- Raising the denominator of `roundBeta` to the exponent `9/10` loses at
most the crude factor `3^i`.  This deliberately avoids a transcendental
constant in the later round calculation. -/
theorem roundBeta_rpow_lower {beta0 : ℝ} (hbeta0 : 0 < beta0) (i : ℕ) :
    beta0 ^ (9 / 10 : ℝ) / (3 : ℝ) ^ i ≤
      roundBeta beta0 i ^ (9 / 10 : ℝ) := by
  have hpowPos : 0 < beta0 ^ (9 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hbeta0 _
  have hthreePos : 0 < (3 : ℝ) ^ i := by positivity
  have hthreeOne : 1 ≤ (3 : ℝ) ^ i :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hdenomLe : ((3 : ℝ) ^ i) ^ (9 / 10 : ℝ) ≤ (3 : ℝ) ^ i :=
    Real.rpow_le_self_of_one_le hthreeOne (by norm_num)
  rw [roundBeta, Real.div_rpow hbeta0.le hthreePos.le]
  exact (div_le_div_iff_of_pos_left hpowPos hthreePos
    (Real.rpow_pos_of_pos hthreePos _)).2 hdenomLe

/-- The literal extraction rate is bounded by a rational-power-free
expression. -/
theorem scheduledExtractionRate_le_coarse
    {beta0 : ℝ} (hbeta0 : 0 < beta0)
    {r : ℕ} (hr : 0 < r) (i : ℕ) :
    scheduledExtractionRate beta0 r i ≤
      60 * (3 : ℝ) ^ i /
        (beta0 ^ (9 / 10 : ℝ) * r) := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hbetaPow : 0 < beta0 ^ (9 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hbeta0 _
  have hthree : 0 < (3 : ℝ) ^ i := by positivity
  have hlower := roundBeta_rpow_lower hbeta0 i
  have hsmallDenom :
      0 < (beta0 ^ (9 / 10 : ℝ) / (3 : ℝ) ^ i) * r :=
    mul_pos (div_pos hbetaPow hthree) hrReal
  have hactualDenom :
      0 < roundBeta beta0 i ^ (9 / 10 : ℝ) * r := by
    exact mul_pos (Real.rpow_pos_of_pos (div_pos hbeta0 hthree) _) hrReal
  have hdenomLe :
      (beta0 ^ (9 / 10 : ℝ) / (3 : ℝ) ^ i) * r ≤
        roundBeta beta0 i ^ (9 / 10 : ℝ) * r :=
    mul_le_mul_of_nonneg_right hlower hrReal.le
  calc
    scheduledExtractionRate beta0 r i =
        60 / (roundBeta beta0 i ^ (9 / 10 : ℝ) * r) := rfl
    _ ≤ 60 /
        ((beta0 ^ (9 / 10 : ℝ) / (3 : ℝ) ^ i) * r) :=
      (div_le_div_iff_of_pos_left (by norm_num) hactualDenom hsmallDenom).2
        hdenomLe
    _ = 60 * (3 : ℝ) ^ i /
        (beta0 ^ (9 / 10 : ℝ) * r) := by
      field_simp

/-- Before the horizon, the actual rate is bounded by a geometric sequence
with ratio `3/10`, indexed by the horizon rather than the round. -/
theorem scheduledExtractionRate_le_horizon_geometric
    {beta0 : ℝ} (hbeta0 : 0 < beta0) {r i : ℕ}
    (hr : 0 < r) (hi : i < roundHorizon r) :
    scheduledExtractionRate beta0 r i ≤
      (60 / beta0 ^ (9 / 10 : ℝ)) *
        ((3 : ℝ) / 10) ^ roundHorizon r := by
  let J := roundHorizon r
  have hbetaPow : 0 < beta0 ^ (9 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hbeta0 _
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hthreePow : (3 : ℝ) ^ i ≤ (3 : ℝ) ^ J :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hi.le
  have htenPowNat : 10 ^ J ≤ r := ten_pow_roundHorizon_le hr
  have htenPow : (10 : ℝ) ^ J ≤ r := by exact_mod_cast htenPowNat
  have hdenomR : 0 < beta0 ^ (9 / 10 : ℝ) * r :=
    mul_pos hbetaPow hrReal
  have hdenomTen : 0 < beta0 ^ (9 / 10 : ℝ) * (10 : ℝ) ^ J := by
    positivity
  have hnumPos : 0 < 60 * (3 : ℝ) ^ J := by positivity
  calc
    scheduledExtractionRate beta0 r i ≤
        60 * (3 : ℝ) ^ i /
          (beta0 ^ (9 / 10 : ℝ) * r) :=
      scheduledExtractionRate_le_coarse hbeta0 hr i
    _ ≤ 60 * (3 : ℝ) ^ J /
          (beta0 ^ (9 / 10 : ℝ) * r) :=
      (div_le_div_iff_of_pos_right hdenomR).2
        (mul_le_mul_of_nonneg_left hthreePow (by norm_num))
    _ ≤ 60 * (3 : ℝ) ^ J /
          (beta0 ^ (9 / 10 : ℝ) * (10 : ℝ) ^ J) :=
      (div_le_div_iff_of_pos_left hnumPos hdenomR hdenomTen).2
        (mul_le_mul_of_nonneg_left htenPow hbetaPow.le)
    _ = (60 / beta0 ^ (9 / 10 : ℝ)) *
          ((3 : ℝ) / 10) ^ J := by
      rw [div_pow]
      field_simp

/-- For every fixed positive initial parameter, every actual extraction rate
before the base-ten horizon is at most one once `r` is large enough. -/
theorem exists_scheduledExtractionRate_le_one_threshold
    {beta0 : ℝ} (hbeta0 : 0 < beta0) :
    ∃ R : ℕ, ∀ {r i : ℕ}, R ≤ r → i < roundHorizon r →
      scheduledExtractionRate beta0 r i ≤ 1 := by
  let C : ℝ := 60 / beta0 ^ (9 / 10 : ℝ)
  have hpow :
      Tendsto (fun J : ℕ => ((3 : ℝ) / 10) ^ J) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (3 : ℝ) / 10) (by norm_num) (by norm_num)
  have hgeometric :
      Tendsto (fun J : ℕ => C * ((3 : ℝ) / 10) ^ J) atTop (nhds 0) :=
    by simpa using (tendsto_const_nhds.mul hpow :
      Tendsto (fun J : ℕ => C * ((3 : ℝ) / 10) ^ J) atTop (nhds (C * 0)))
  have hevent : ∀ᶠ J : ℕ in atTop,
      C * ((3 : ℝ) / 10) ^ J < 1 :=
    hgeometric.eventually_lt_const zero_lt_one
  obtain ⟨J0, hJ0⟩ := eventually_atTop.1 hevent
  refine ⟨10 ^ J0, ?_⟩
  intro r i hr hi
  have hrPos : 0 < r := (by positivity : 0 < 10 ^ J0).trans_le hr
  have hJ : J0 ≤ roundHorizon r :=
    Nat.le_log_of_pow_le (by omega) hr
  exact (scheduledExtractionRate_le_horizon_geometric hbeta0 hrPos hi).trans
    (hJ0 (roundHorizon r) hJ).le

/-- Eventual rate bound in exactly the notation expected by the recursive
colouring theorem. -/
theorem exists_blsExtractionRate_roundBeta_le_one_threshold
    {beta0 : ℝ} (hbeta0 : 0 < beta0) :
    ∃ R : ℕ, ∀ {r i : ℕ}, R ≤ r → i < roundHorizon r →
      blsExtractionRate r (roundBeta beta0 i) ≤ 1 := by
  simpa only [scheduledExtractionRate_eq_blsExtractionRate] using
    exists_scheduledExtractionRate_le_one_threshold hbeta0

end

end LeanCo.SizeRamsey
