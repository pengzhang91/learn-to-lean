import LeanCo.SizeRamsey.BLSConditionalRound
import Mathlib.Tactic

/-!
# Numerical bookkeeping for the wide BLS rounds

This file verifies the geometric colour budget and the decay estimate for
the schedule used in the wide rounds.  The only explicit side condition on
the final contraction theorem is `blsExtractionRate r β ≤ 1`; it cannot be
deduced uniformly from `0 < β₀ ≤ 1`, since arbitrarily small `β₀` makes the
rate arbitrarily large.
-/

namespace LeanCo.SizeRamsey

open scoped BigOperators

noncomputable section

/-- Half of the colour budget allocated to wide round `i`. -/
def wideRoundHalfBudget (r i : ℕ) : ℕ :=
  r / 2 ^ (i + 3)

/-- The geometric small parameter used in round `i`. -/
def roundBeta (β₀ : ℝ) (i : ℕ) : ℝ :=
  β₀ / (3 : ℝ) ^ i

/-! ## Geometric natural-number budget -/

/-- Consecutive half-budgets shrink by at least a factor of two. -/
theorem two_mul_wideRoundHalfBudget_succ_le (r i : ℕ) :
    2 * wideRoundHalfBudget r (i + 1) ≤ wideRoundHalfBudget r i := by
  unfold wideRoundHalfBudget
  rw [show i + 1 + 3 = (i + 3) + 1 by omega, pow_succ]
  rw [← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

/-- Every finite tail of the half-budget schedule is bounded by twice its
first term. -/
theorem sum_wideRoundHalfBudget_tail_le (r k T : ℕ) :
    ∑ j ∈ Finset.range T, wideRoundHalfBudget r (k + j) ≤
      2 * wideRoundHalfBudget r k := by
  induction T generalizing k with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ']
      have htail :
          ∑ j ∈ Finset.range T, wideRoundHalfBudget r (k + (j + 1)) ≤
            2 * wideRoundHalfBudget r (k + 1) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1] using ih (k + 1)
      have hhalf :
          2 * wideRoundHalfBudget r (k + 1) ≤
            wideRoundHalfBudget r k :=
        two_mul_wideRoundHalfBudget_succ_le r k
      simp only [Nat.add_zero]
      omega

/-- Both halves of every wide round, with the outer factor two appearing in
the BLS bookkeeping, consume at most the total palette `r`. -/
theorem two_halves_wideRound_total_budget_le (r T : ℕ) :
    2 * (∑ i ∈ Finset.range T, 2 * wideRoundHalfBudget r i) ≤ r := by
  have hsum :
      ∑ i ∈ Finset.range T, wideRoundHalfBudget r i ≤
        2 * wideRoundHalfBudget r 0 := by
    simpa using sum_wideRoundHalfBudget_tail_le r 0 T
  calc
    2 * (∑ i ∈ Finset.range T, 2 * wideRoundHalfBudget r i) =
        4 * (∑ i ∈ Finset.range T, wideRoundHalfBudget r i) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 4 * (2 * wideRoundHalfBudget r 0) := Nat.mul_le_mul_left 4 hsum
    _ = 8 * (r / 8) := by simp [wideRoundHalfBudget]; ring
    _ ≤ r := Nat.mul_div_le r 8

/-! ## The beta schedule -/

theorem roundBeta_pos {β₀ : ℝ} (hβ₀ : 0 < β₀) (i : ℕ) :
    0 < roundBeta β₀ i := by
  unfold roundBeta
  positivity

theorem roundBeta_le {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (i : ℕ) :
    roundBeta β₀ i ≤ β₀ := by
  unfold roundBeta
  exact div_le_self hβ₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))

theorem roundBeta_mem_Ioc {β₀ : ℝ} (hβ₀ : 0 < β₀) (i : ℕ) :
    roundBeta β₀ i ∈ Set.Ioc 0 β₀ :=
  ⟨roundBeta_pos hβ₀ i, roundBeta_le hβ₀.le i⟩

/-! ## The `0.9` power versus the binary schedule -/

/-- The elementary logarithmic comparison behind the growth estimate. -/
theorem log_two_le_nine_tenths_log_three :
    Real.log 2 ≤ (9 / 10 : ℝ) * Real.log 3 := by
  have hp : (2 : ℝ) ^ 10 ≤ (3 : ℝ) ^ 9 := by norm_num
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ 10) hp
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog ⊢
  linarith

/-- A coarse rational upper bound sufficient for the contraction constant. -/
theorem log_ten_le_five : Real.log 10 ≤ (5 : ℝ) := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h5 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
  norm_num at h2 h5 ⊢
  linarith

/-- The exact `0.9` estimate: the decay of `(β₀/3^i)^0.9` dominates the
binary growth `2^i`. -/
theorem two_pow_mul_roundBeta_rpow_le_one
    {β₀ : ℝ} (hβ₀ : 0 < β₀) (hβ₀One : β₀ ≤ 1) (i : ℕ) :
    (2 : ℝ) ^ i *
        Real.rpow (roundBeta β₀ i) (9 / 10 : ℝ) ≤ 1 := by
  have hβi : 0 < roundBeta β₀ i := roundBeta_pos hβ₀ i
  have hprod :
      0 < (2 : ℝ) ^ i *
        Real.rpow (roundBeta β₀ i) (9 / 10 : ℝ) :=
    mul_pos (pow_pos (by norm_num) _) (Real.rpow_pos_of_pos hβi _)
  rw [Real.rpow_eq_pow] at hprod ⊢
  rw [← Real.log_le_log_iff hprod zero_lt_one]
  rw [Real.log_mul (x := (2 : ℝ) ^ i)
      (y := (roundBeta β₀ i) ^ (9 / 10 : ℝ))
      (pow_ne_zero _ (by norm_num))
      ((Real.rpow_ne_zero hβi.le (by norm_num)).2 hβi.ne'),
    Real.log_pow,
    Real.log_rpow (x := roundBeta β₀ i) hβi (9 / 10 : ℝ),
    Real.log_one]
  have hlogβ₀ : Real.log β₀ ≤ 0 := Real.log_nonpos hβ₀.le hβ₀One
  have hlogβi :
      Real.log (roundBeta β₀ i) =
        Real.log β₀ - (i : ℝ) * Real.log 3 := by
    rw [roundBeta, Real.log_div hβ₀.ne' (pow_ne_zero _ (by norm_num)),
      Real.log_pow]
  rw [hlogβi]
  have hi : (0 : ℝ) ≤ i := by positivity
  nlinarith [log_two_le_nine_tenths_log_three]

/-! ## Rate times budget and contraction -/

/-- Under the minimal nonzero-round condition, the extraction rate times the
integer half-budget is at least `log 10`.  This is the floor-sensitive core
estimate used by the final power bound. -/
theorem log_ten_le_blsExtractionRate_mul_wideRoundHalfBudget
    {r i : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀) (hβ₀One : β₀ ≤ 1)
    (hr : 2 ^ (i + 4) ≤ r) :
    Real.log 10 ≤ blsExtractionRate r (roundBeta β₀ i) *
      (wideRoundHalfBudget r i : ℝ) := by
  let q : ℕ := 2 ^ (i + 3)
  let T : ℕ := wideRoundHalfBudget r i
  let B : ℝ := Real.rpow (roundBeta β₀ i) (9 / 10 : ℝ)
  have hqpos : 0 < q := by simp [q]
  have hrpos : 0 < r := lt_of_lt_of_le (pow_pos (by omega) _) hr
  have hTtwo : 2 ≤ T := by
    dsimp only [T, wideRoundHalfBudget, q]
    apply (Nat.le_div_iff_mul_le (pow_pos (by omega) _)).2
    simpa [show i + 4 = (i + 3) + 1 by omega, pow_succ,
      Nat.mul_comm] using hr
  have hrlt : r < q * (r / q + 1) := Nat.lt_mul_div_succ r hqpos
  have hTdef : T = r / q := by simp [T, wideRoundHalfBudget, q]
  have hrTwo : 2 * r ≤ 3 * q * T := by
    rw [hTdef]
    calc
      2 * r ≤ 2 * (q * (r / q + 1)) := Nat.mul_le_mul_left 2 hrlt.le
      _ = q * (2 * (r / q + 1)) := by ring
      _ ≤ q * (3 * (r / q)) := by
        apply Nat.mul_le_mul_left
        omega
      _ = 3 * q * (r / q) := by ring
  have hprod := two_pow_mul_roundBeta_rpow_le_one hβ₀ hβ₀One i
  have hBpos : 0 < B := by
    dsimp only [B]
    exact Real.rpow_pos_of_pos (roundBeta_pos hβ₀ i) _
  have hBq : B * (q : ℝ) ≤ 8 := by
    calc
      B * (q : ℝ) =
          8 * ((2 : ℝ) ^ i *
            Real.rpow (roundBeta β₀ i) (9 / 10 : ℝ)) := by
        dsimp only [B, q]
        push_cast
        rw [pow_add]
        norm_num
        ring
      _ ≤ 8 * 1 := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 8 := by norm_num
  have hlog0 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  have hLBq : Real.log 10 * B * (q : ℝ) ≤ 40 := by
    calc
      Real.log 10 * B * (q : ℝ) = Real.log 10 * (B * q) := by ring
      _ ≤ 5 * (B * q) :=
        mul_le_mul_of_nonneg_right log_ten_le_five
          (mul_nonneg hBpos.le (by positivity))
      _ ≤ 5 * 8 := mul_le_mul_of_nonneg_left hBq (by norm_num)
      _ = 40 := by norm_num
  have hrTwoR : (2 : ℝ) * r ≤ 3 * q * T := by exact_mod_cast hrTwo
  have htwice :
      2 * (Real.log 10 * B * r) ≤
        3 * (Real.log 10 * B * q) * T := by
    calc
      2 * (Real.log 10 * B * r) = (Real.log 10 * B) * (2 * r) := by ring
      _ ≤ (Real.log 10 * B) * (3 * q * T) :=
        mul_le_mul_of_nonneg_left hrTwoR (mul_nonneg hlog0 hBpos.le)
      _ = 3 * (Real.log 10 * B * q) * T := by ring
  have hrhs : 3 * (Real.log 10 * B * q) * (T : ℝ) ≤ 120 * T := by
    apply mul_le_mul_of_nonneg_right
    · nlinarith
    · positivity
  have hcross : Real.log 10 * (B * r) ≤ 60 * T := by
    ring_nf at htwice hrhs ⊢
    linarith
  have hden : 0 < B * (r : ℝ) := mul_pos hBpos (by exact_mod_cast hrpos)
  calc
    Real.log 10 ≤ 60 * (T : ℝ) / (B * r) :=
      (le_div_iff₀ hden).2 (by simpa [mul_assoc] using hcross)
    _ = blsExtractionRate r (roundBeta β₀ i) *
        (wideRoundHalfBudget r i : ℝ) := by
      rw [blsExtractionRate]
      simp only [B, T, Real.rpow_eq_pow]
      ring

/-- Exponential domination turns a rate-times-time lower bound into the
desired tenth contraction. -/
theorem one_sub_pow_le_one_tenth_of_log_ten_le_mul
    {a : ℝ} {T : ℕ} (haOne : a ≤ 1)
    (hlarge : Real.log 10 ≤ a * T) :
    (1 - a) ^ T ≤ (1 : ℝ) / 10 := by
  have hbase0 : 0 ≤ 1 - a := sub_nonneg.mpr haOne
  calc
    (1 - a) ^ T ≤ (Real.exp (-a)) ^ T :=
      pow_le_pow_left₀ hbase0 (Real.one_sub_le_exp_neg a) T
    _ = Real.exp (-(a * (T : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log 10) := by
      apply Real.exp_monotone
      linarith
    _ = (1 : ℝ) / 10 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      norm_num

/-- Final wide-round contraction.  The rate upper bound is explicit because
it is not uniform in an arbitrarily small positive `β₀`. -/
theorem wideRound_contraction_le_one_tenth
    {r i : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀) (hβ₀One : β₀ ≤ 1)
    (hr : 2 ^ (i + 4) ≤ r)
    (hrateOne : blsExtractionRate r (roundBeta β₀ i) ≤ 1) :
    (1 - blsExtractionRate r (roundBeta β₀ i)) ^
        wideRoundHalfBudget r i ≤ (1 : ℝ) / 10 := by
  apply one_sub_pow_le_one_tenth_of_log_ten_le_mul hrateOne
  exact log_ten_le_blsExtractionRate_mul_wideRoundHalfBudget hβ₀ hβ₀One hr

end

end LeanCo.SizeRamsey
