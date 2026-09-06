import LeanCo.HypercubeTuran.NontrivialCuts
import LeanCo.HypercubeTuran.AsymptoticParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Numerical parameters for the random base graph

This file closes the numerical part of the binomial-graph construction.  We
use reciprocal edge probabilities; separating the denominator from the target
average degree keeps all rounding out of the probabilistic estimates.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset ProbabilityTheory SimpleGraph unitInterval

namespace LeanCo.HypercubeTuran

noncomputable section

namespace RB

theorem choose_two_twice_mul (d q : ℕ) :
    (2 * d * q).choose 2 = d * q * (2 * d * q - 1) := by
  rw [Nat.choose_two_right]
  have hfactor : 2 * d * q * (2 * d * q - 1) =
      2 * (d * q * (2 * d * q - 1)) := by ring
  rw [hfactor]
  exact Nat.mul_div_cancel_left _ (by omega)

/-- The point of the unit interval represented by `1 / q`. -/
def reciprocalProbability (q : ℕ) (hq : 0 < q) : unitInterval :=
  ⟨1 / (q : ℝ), by positivity, by
    rw [div_le_one (by positivity)]
    exact_mod_cast hq⟩

@[simp]
theorem coe_reciprocalProbability (q : ℕ) (hq : 0 < q) :
    (reciprocalProbability q hq : ℝ) = 1 / (q : ℝ) := rfl

/-- A rational upper estimate for `exp (1/5)`. -/
theorem exp_one_fifth_le : Real.exp ((1 : ℝ) / 5) ≤ 49 / 40 := by
  have h := Real.exp_bound' (x := (1 : ℝ) / 5)
    (by norm_num) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- A rational upper estimate for `exp (-1/4)`. -/
theorem exp_neg_quarter_le : Real.exp (-(1 : ℝ) / 4) ≤ 79 / 100 := by
  have hseries := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 1 / 4 by norm_num) 3
  have hexppos : 0 < Real.exp ((1 : ℝ) / 4) := Real.exp_pos _
  have hlower : (100 : ℝ) / 79 ≤ Real.exp ((1 : ℝ) / 4) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith
  rw [show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring, Real.exp_neg]
  have hinv := (inv_le_inv₀ hexppos
    (by positivity : (0 : ℝ) < 100 / 79)).2 hlower
  norm_num at hinv ⊢
  exact hinv

/-- The elementary exponential majorant used for binomial moment factors. -/
theorem one_add_mul_le_exp_mul (p c : ℝ) :
    1 + p * c ≤ Real.exp (p * c) := by
  simpa [add_comm] using Real.add_one_le_exp (p * c)

/-! ## Two fixed-ratio Chernoff estimates -/

/-- The upper binomial tail at `5/4` of the mean.  The deliberately weak
constant `1/40` makes the proof use only rational estimates for `exp (1/5)`.
-/
theorem binomial_five_four_mean_upper_le_exp
    (trials : ℕ) (p : unitInterval) :
    Bin(trials, p).real
        {x : ℕ | 5 * (((trials : ℝ) * (p : ℝ))) / 4 ≤ x} ≤
      Real.exp (-((trials : ℝ) * (p : ℝ)) / 40) := by
  let μ : ℝ := (trials : ℝ) * (p : ℝ)
  have ht : (0 : ℝ) < 1 / 5 := by norm_num
  have hchern := binomial_chernoff_upper
    trials p ht (5 * μ / 4)
  have hbase0 : 0 ≤ 1 - (p : ℝ) + (p : ℝ) * Real.exp ((1 : ℝ) / 5) := by
    exact add_nonneg (sub_nonneg.mpr p.property.2)
      (mul_nonneg p.property.1 (Real.exp_pos _).le)
  have hbase :
      1 - (p : ℝ) + (p : ℝ) * Real.exp ((1 : ℝ) / 5) ≤
        Real.exp ((p : ℝ) * (9 / 40 : ℝ)) := by
    calc
      1 - (p : ℝ) + (p : ℝ) * Real.exp ((1 : ℝ) / 5) ≤
          1 + (p : ℝ) * (9 / 40 : ℝ) := by
        have hp := p.property.1
        nlinarith [exp_one_fifth_le]
      _ ≤ Real.exp ((p : ℝ) * (9 / 40 : ℝ)) :=
        one_add_mul_le_exp_mul _ _
  have hpow :
      (1 - (p : ℝ) + (p : ℝ) * Real.exp ((1 : ℝ) / 5)) ^ trials ≤
        Real.exp ((p : ℝ) * (9 / 40 : ℝ)) ^ trials :=
    pow_le_pow_left₀ hbase0 hbase trials
  calc
    Bin(trials, p).real {x : ℕ | 5 * μ / 4 ≤ x} ≤
        Real.exp (-((1 : ℝ) / 5) * (5 * μ / 4)) *
          (1 - (p : ℝ) + (p : ℝ) * Real.exp ((1 : ℝ) / 5)) ^ trials :=
      hchern
    _ ≤ Real.exp (-((1 : ℝ) / 5) * (5 * μ / 4)) *
          Real.exp ((p : ℝ) * (9 / 40 : ℝ)) ^ trials := by
      exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-μ / 40) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp only [μ]
      ring
    _ = Real.exp (-((trials : ℝ) * (p : ℝ)) / 40) := rfl

/-- The lower binomial tail at `4/5` of the mean. -/
theorem binomial_four_five_mean_lower_le_exp
    (trials : ℕ) (p : unitInterval) :
    Bin(trials, p).real
        {x : ℕ | (x : ℝ) ≤ 4 * (((trials : ℝ) * (p : ℝ))) / 5} ≤
      Real.exp (-((trials : ℝ) * (p : ℝ)) / 100) := by
  let μ : ℝ := (trials : ℝ) * (p : ℝ)
  have ht : -(1 : ℝ) / 4 < 0 := by norm_num
  have hchern := binomial_chernoff_lower
    trials p ht (4 * μ / 5)
  have hbase0 : 0 ≤
      1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4) := by
    exact add_nonneg (sub_nonneg.mpr p.property.2)
      (mul_nonneg p.property.1 (Real.exp_pos _).le)
  have hbase :
      1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4) ≤
        Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) := by
    calc
      1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4) ≤
          1 - (p : ℝ) * (21 / 100 : ℝ) := by
        have hp := p.property.1
        nlinarith [exp_neg_quarter_le]
      _ ≤ Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) := by
        convert Real.add_one_le_exp (-(p : ℝ) * (21 / 100 : ℝ)) using 1 <;>
          ring
  have hpow :
      (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^ trials ≤
        Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) ^ trials :=
    pow_le_pow_left₀ hbase0 hbase trials
  calc
    Bin(trials, p).real {x : ℕ | (x : ℝ) ≤ 4 * μ / 5} ≤
        Real.exp (-(-(1 : ℝ) / 4) * (4 * μ / 5)) *
          (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^ trials :=
      hchern
    _ ≤ Real.exp (-(-(1 : ℝ) / 4) * (4 * μ / 5)) *
          Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) ^ trials := by
      exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-μ / 100) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp only [μ]
      ring
    _ = Real.exp (-((trials : ℝ) * (p : ℝ)) / 100) := rfl

/-- The numerical estimate on the Chernoff expression itself, exposed for
finite union bounds which have already applied Chernoff pointwise. -/
theorem four_five_chernoff_expression_le_exp
    (trials : ℕ) (p : unitInterval) :
    Real.exp (-(-(1 : ℝ) / 4) *
        (4 * (((trials : ℝ) * (p : ℝ))) / 5)) *
      (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^ trials ≤
        Real.exp (-((trials : ℝ) * (p : ℝ)) / 100) := by
  let μ : ℝ := (trials : ℝ) * (p : ℝ)
  have hbase0 : 0 ≤
      1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4) :=
    add_nonneg (sub_nonneg.mpr p.property.2)
      (mul_nonneg p.property.1 (Real.exp_pos _).le)
  have hbase :
      1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4) ≤
        Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) := by
    calc
      1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4) ≤
          1 - (p : ℝ) * (21 / 100 : ℝ) := by
        have hp := p.property.1
        nlinarith [exp_neg_quarter_le]
      _ ≤ Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) := by
        convert Real.add_one_le_exp (-(p : ℝ) * (21 / 100 : ℝ)) using 1 <;>
          ring
  have hpow :
      (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^ trials ≤
        Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) ^ trials :=
    pow_le_pow_left₀ hbase0 hbase trials
  calc
    Real.exp (-(-(1 : ℝ) / 4) * (4 * μ / 5)) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^ trials ≤
      Real.exp (-(-(1 : ℝ) / 4) * (4 * μ / 5)) *
        Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) ^ trials := by
      exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-μ / 100) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp only [μ]
      ring
    _ = Real.exp (-((trials : ℝ) * (p : ℝ)) / 100) := rfl

/-! ## Reciprocal-probability consequences -/

theorem reciprocal_choose_two_mean (d q : ℕ) (hq : 0 < q) :
    ((((2 * d * q).choose 2 : ℕ) : ℝ) *
        (reciprocalProbability q hq : ℝ)) =
      (d : ℝ) * ((2 * d * q : ℕ) - 1) := by
  rcases d.eq_zero_or_pos with rfl | hd
  · simp
  · rw [choose_two_twice_mul, coe_reciprocalProbability]
    norm_num only [Nat.cast_mul]
    have hN : 1 ≤ 2 * d * q := by
      have hdq : 0 < d * q := Nat.mul_pos hd hq
      nlinarith
    rw [Nat.cast_sub hN]
    norm_num only [Nat.cast_one]
    field_simp
    norm_num only [Nat.cast_mul]
    ring

/-- The total-edge bad event is exponentially unlikely for the reciprocal
parameterization `N = 2dq`. -/
theorem measureReal_badEdgeEvent_reciprocal_le
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) :
    (randomEdgeMeasure (2 * d * q) (reciprocalProbability q hq)).real
        (badEdgeEvent (2 * d * q) d) ≤
      Real.exp (-((d : ℝ) * (2 * d * q : ℕ)) / 80) := by
  let N := 2 * d * q
  let p := reciprocalProbability q hq
  let μ : ℝ := ((N.choose 2 : ℕ) : ℝ) * (p : ℝ)
  have hN : 2 ≤ N := by
    dsimp only [N]
    have hdq : 0 < d * q := Nat.mul_pos hd hq
    nlinarith
  have hmean : μ = (d : ℝ) * (N - 1) := by
    dsimp only [μ, N, p]
    exact reciprocal_choose_two_mean d q hq
  have hmean_le : μ ≤ (d : ℝ) * N := by
    rw [hmean]
    have hdR : (0 : ℝ) ≤ (d : ℝ) := by positivity
    nlinarith
  have hmean_lower : (d : ℝ) * N / 2 ≤ μ := by
    rw [hmean]
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hdR : (0 : ℝ) ≤ (d : ℝ) := by positivity
    nlinarith
  calc
    (randomEdgeMeasure N p).real (badEdgeEvent N d) =
        Bin(N.choose 2, p).real {k : ℕ | 5 * d * N < 4 * k} :=
      measureReal_badEdgeEvent_eq_binomial N d p
    _ ≤ Bin(N.choose 2, p).real {k : ℕ | 5 * μ / 4 ≤ k} := by
      apply measureReal_mono
      · intro k hk
        norm_num only [Set.mem_setOf_eq]
        have hkR : ((5 * d * N : ℕ) : ℝ) < 4 * (k : ℝ) := by
          exact_mod_cast hk
        norm_num only [Nat.cast_mul] at hkR
        nlinarith
      · finiteness
    _ ≤ Real.exp (-μ / 40) :=
      binomial_five_four_mean_upper_le_exp (N.choose 2) p
    _ ≤ Real.exp (-((d : ℝ) * N) / 80) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (-((d : ℝ) * (2 * d * q : ℕ)) / 80) := rfl

/-! ## Parameters dictated by local sparsity -/

def localRadius (g : ℕ) : ℕ := 2 * g + 1

def localScale (g d : ℕ) : ℕ :=
  (2 * d * (localRadius g) ^ 2) ^ (localRadius g)

/-- This denominator is chosen so that the entire local-sparsity union bound
is at most `1/100`. -/
def localDenominator (g d : ℕ) : ℕ :=
  100 * localRadius g * localScale g d

def randomParameterN (g d : ℕ) : ℕ :=
  2 * d * localDenominator g d

theorem localRadius_pos (g : ℕ) : 0 < localRadius g := by
  simp [localRadius]

theorem localScale_pos (g : ℕ) {d : ℕ} (hd : 0 < d) :
    0 < localScale g d := by
  unfold localScale
  have hr : 0 < localRadius g := localRadius_pos g
  have hbase : 0 < 2 * d * localRadius g ^ 2 := by positivity
  exact pow_pos hbase _

theorem localDenominator_pos (g : ℕ) {d : ℕ} (hd : 0 < d) :
    0 < localDenominator g d := by
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (localRadius_pos g))
    (localScale_pos g hd)

private theorem local_fixed_size_term_le
    (g d u : ℕ) (hd : 0 < d) (hu : u < localRadius g) :
    let q := localDenominator g d
    let N := 2 * d * q
    (N.choose u : ℝ) *
        (((u.choose 2).choose (u + 1) : ℕ) : ℝ) *
          (reciprocalProbability q (localDenominator_pos g hd) : ℝ) ^ (u + 1) ≤
      1 / (100 * (localRadius g : ℝ)) := by
  dsimp only
  let r := localRadius g
  let C := localScale g d
  let q := localDenominator g d
  have hr : 0 < r := localRadius_pos g
  have hC : 0 < C := localScale_pos g hd
  have hq : 0 < q := localDenominator_pos g hd
  have hchooseN : (((2 * d * q).choose u : ℕ) : ℝ) ≤
      ((2 * d * q : ℕ) : ℝ) ^ u := by
    exact_mod_cast Nat.choose_le_pow (2 * d * q) u
  have hchooseU : ((((u.choose 2).choose (u + 1) : ℕ) : ℝ)) ≤
      ((u : ℝ) ^ 2) ^ (u + 1) := by
    have h₁ : (u.choose 2).choose (u + 1) ≤ (u.choose 2) ^ (u + 1) :=
      Nat.choose_le_pow _ _
    have h₂ : u.choose 2 ≤ u ^ 2 := Nat.choose_le_pow _ _
    exact_mod_cast h₁.trans (Nat.pow_le_pow_left h₂ _)
  have hb : (1 : ℝ) ≤ (2 * d : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * d by omega)
  have hur : (u : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg u) (by exact_mod_cast hu.le) 2
  have hbase : (1 : ℝ) ≤ (2 * d : ℕ) * (r : ℝ) ^ 2 := by
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hrSq : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hnumerator :
      ((2 * d : ℕ) : ℝ) ^ u * (((u : ℝ) ^ 2) ^ (u + 1)) ≤
        (C : ℝ) := by
    calc
      ((2 * d : ℕ) : ℝ) ^ u * (((u : ℝ) ^ 2) ^ (u + 1)) ≤
          ((2 * d : ℕ) : ℝ) ^ (u + 1) *
            (((r : ℝ) ^ 2) ^ (u + 1)) := by
        exact mul_le_mul
          (pow_le_pow_right₀ hb (Nat.le_succ u))
          (pow_le_pow_left₀ (sq_nonneg (u : ℝ)) hur (u + 1))
          (pow_nonneg (sq_nonneg (u : ℝ)) _)
          (pow_nonneg (Nat.cast_nonneg (2 * d)) _)
      _ = (((2 * d : ℕ) : ℝ) * (r : ℝ) ^ 2) ^ (u + 1) := by
        rw [mul_pow]
      _ ≤ (((2 * d : ℕ) : ℝ) * (r : ℝ) ^ 2) ^ r := by
        exact pow_le_pow_right₀ hbase (Nat.succ_le_iff.mpr hu)
      _ = (C : ℝ) := by
        simp only [C, localScale]
        norm_cast
  calc
    (((2 * d * q).choose u : ℕ) : ℝ) *
          (((u.choose 2).choose (u + 1) : ℕ) : ℝ) *
          (reciprocalProbability q hq : ℝ) ^ (u + 1) ≤
        (((2 * d * q : ℕ) : ℝ) ^ u) *
          (((u : ℝ) ^ 2) ^ (u + 1)) *
          (1 / (q : ℝ)) ^ (u + 1) := by
      rw [coe_reciprocalProbability]
      gcongr
    _ = (((2 * d : ℕ) : ℝ) ^ u *
          (((u : ℝ) ^ 2) ^ (u + 1))) / q := by
      have hqR : (q : ℝ) ≠ 0 := by positivity
      norm_num only [Nat.cast_mul]
      rw [one_div, inv_pow]
      field_simp
      ring
    _ ≤ (C : ℝ) / q := by
      exact div_le_div_of_nonneg_right hnumerator (Nat.cast_nonneg q)
    _ = 1 / (100 * (r : ℝ)) := by
      have hCR : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      have hqeq : (q : ℝ) = 100 * (r : ℝ) * (C : ℝ) := by
        dsimp only [q, r, C, localDenominator]
        norm_num only [Nat.cast_mul]
      rw [hqeq]
      field_simp [hCR, hrR]
    _ = 1 / (100 * (localRadius g : ℝ)) := rfl

/-- With `localDenominator`, all forbidden small dense sets together cost at
most one percent of probability. -/
theorem measureReal_badLocalSparsityEvent_parameters_le
    (g d : ℕ) (hd : 0 < d) :
    let q := localDenominator g d
    let N := randomParameterN g d
    (randomEdgeMeasure N (reciprocalProbability q (localDenominator_pos g hd))).real
        (badLocalSparsityEvent N g) ≤ 1 / 100 := by
  dsimp only [randomParameterN]
  let q := localDenominator g d
  let p := reciprocalProbability q (localDenominator_pos g hd)
  have hr : 0 < localRadius g := localRadius_pos g
  calc
    (randomEdgeMeasure (2 * d * q) p).real
        (badLocalSparsityEvent (2 * d * q) g) ≤
      ∑ u ∈ Finset.range (2 * g + 1),
        ((2 * d * q).choose u : ℝ) *
          ((((u.choose 2).choose (u + 1) : ℕ) : ℝ) *
            (p : ℝ) ^ (u + 1)) :=
      measureReal_badLocalSparsityEvent_le_size_sum _ _ _
    _ ≤ ∑ _u ∈ Finset.range (2 * g + 1),
        1 / (100 * (localRadius g : ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [Finset.mem_range] at hu
      simpa only [q, p, mul_assoc] using local_fixed_size_term_le g d u hd hu
    _ = 1 / 100 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
      simp only [localRadius]
      field_simp

/-! ## The cut union bound -/

private theorem cut_chernoff_inner_reciprocal_le
    (d q u : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hu : 2 * u ≤ 2 * d * q) :
    let N := 2 * d * q
    let p := reciprocalProbability q hq
    Real.exp (-(-(1 : ℝ) / 4) *
        (((8 * d * u * (N - u) : ℕ) : ℝ) /
          ((5 * N : ℕ) : ℝ))) *
      (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^
        (u * (N - u)) ≤
      Real.exp (-((d : ℝ) * u) / 100) := by
  dsimp only
  let N := 2 * d * q
  let p := reciprocalProbability q hq
  let M := u * (N - u)
  have hNpos : 0 < N := by
    dsimp only [N]
    positivity
  have hthreshold :
      (((8 * d * u * (N - u) : ℕ) : ℝ) /
          ((5 * N : ℕ) : ℝ)) =
        4 * (((M : ℕ) : ℝ) * (p : ℝ)) / 5 := by
    dsimp only [N, M, p]
    rw [coe_reciprocalProbability]
    norm_num only [Nat.cast_mul]
    field_simp
    ring
  have hcomplement : d * q ≤ N - u := by
    have hu' : 2 * u ≤ 2 * (d * q) := by
      simpa only [mul_assoc] using hu
    have hudq : u ≤ d * q := by omega
    dsimp only [N]
    apply Nat.le_sub_of_add_le
    calc
      d * q + u ≤ d * q + d * q := Nat.add_le_add_left hudq _
      _ = 2 * d * q := by ring
  have hM : u * (d * q) ≤ M := by
    exact Nat.mul_le_mul_left u hcomplement
  have hmeanlower : (d : ℝ) * u ≤ ((M : ℕ) : ℝ) * (p : ℝ) := by
    rw [coe_reciprocalProbability]
    have hqR : (0 : ℝ) < q := by positivity
    have hMR : ((u * (d * q) : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hM
    norm_num only [Nat.cast_mul] at hMR
    rw [div_eq_mul_inv]
    have hcore : (d : ℝ) * u ≤ (M : ℝ) * (q : ℝ)⁻¹ := by
      calc
        (d : ℝ) * u = ((u : ℝ) * ((d : ℝ) * q)) * (q : ℝ)⁻¹ := by
          field_simp
        _ ≤ (M : ℝ) * (q : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hMR (inv_nonneg.mpr hqR.le)
    simpa only [one_mul] using hcore
  calc
    Real.exp (-(-(1 : ℝ) / 4) *
          (((8 * d * u * (N - u) : ℕ) : ℝ) /
            ((5 * N : ℕ) : ℝ))) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^
          (u * (N - u)) =
      Real.exp (-(-(1 : ℝ) / 4) *
          (4 * (((M : ℕ) : ℝ) * (p : ℝ)) / 5)) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^ M := by
      rw [hthreshold]
    _ ≤ Real.exp (-(((M : ℕ) : ℝ) * (p : ℝ)) / 100) :=
      four_five_chernoff_expression_le_exp M p
    _ ≤ Real.exp (-((d : ℝ) * u) / 100) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Provided the one-shore ratio is at most one, the union of all sparse-cut
events is bounded by a single polynomial times `exp (-d/100)`. -/
theorem measureReal_badCutEvent_reciprocal_le
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hratio :
      ((2 * d * q : ℕ) : ℝ) * Real.exp (-(d : ℝ) / 100) ≤ 1) :
    let N := 2 * d * q
    let p := reciprocalProbability q hq
    (randomEdgeMeasure N p).real (badCutEvent N d) ≤
      ((N + 1 : ℕ) : ℝ) * (N : ℝ) * Real.exp (-(d : ℝ) / 100) := by
  dsimp only
  let N := 2 * d * q
  let p := reciprocalProbability q hq
  let x : ℝ := (N : ℝ) * Real.exp (-(d : ℝ) / 100)
  have hN : 0 < N := by
    dsimp only [N]
    positivity
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by simpa only [x, N] using hratio
  have hcard : #(smallShoreSizes N) ≤ N + 1 := by
    simpa only [smallShoreSizes, Finset.card_range] using
      Finset.card_filter_le (Finset.range (N + 1))
        (fun u => 0 < u ∧ 2 * u ≤ N)
  calc
    (randomEdgeMeasure N p).real (badCutEvent N d) ≤
      ∑ u ∈ smallShoreSizes N,
        (N.choose u : ℝ) *
          (Real.exp (-(-(1 : ℝ) / 4) *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^
              (u * (N - u))) :=
      measureReal_badCutEvent_le_chernoff_smallShore_size_sum
        hN d p (by norm_num : -(1 : ℝ) / 4 < 0)
    _ ≤ ∑ _u ∈ smallShoreSizes N, x := by
      apply Finset.sum_le_sum
      intro u hu
      have husmall := (mem_smallShoreSizes.mp hu).2
      have hupos := (mem_smallShoreSizes.mp hu).1
      have hchoose : (N.choose u : ℝ) ≤ (N : ℝ) ^ u := by
        exact_mod_cast Nat.choose_le_pow N u
      have hinner := cut_chernoff_inner_reciprocal_le d q u hd hq (by
        simpa only [N] using husmall)
      have hraw0 : 0 ≤
          Real.exp (-(-(1 : ℝ) / 4) *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^
              (u * (N - u)) := by
        have hbase0 : 0 ≤
            1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4) :=
          add_nonneg (sub_nonneg.mpr p.property.2)
            (mul_nonneg p.property.1 (Real.exp_pos _).le)
        exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hbase0 _)
      have hexppow : Real.exp (-((d : ℝ) * u) / 100) =
          Real.exp (-(d : ℝ) / 100) ^ u := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hterm :
          (N.choose u : ℝ) *
              (Real.exp (-(-(1 : ℝ) / 4) *
                  (((8 * d * u * (N - u) : ℕ) : ℝ) /
                    ((5 * N : ℕ) : ℝ))) *
                (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^
                  (u * (N - u))) ≤ x ^ u := by
        calc
          _ ≤ (N : ℝ) ^ u * Real.exp (-((d : ℝ) * u) / 100) :=
            mul_le_mul hchoose hinner hraw0 (pow_nonneg (Nat.cast_nonneg N) _)
          _ = x ^ u := by rw [hexppow, ← mul_pow]
      obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hupos.ne'
      calc
        _ ≤ x ^ (v + 1) := hterm
        _ = x ^ v * x := by rw [pow_succ]
        _ ≤ 1 * x := mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 hx1) hx0
        _ = x := one_mul x
    _ = (#(smallShoreSizes N) : ℝ) * x := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((N + 1 : ℕ) : ℝ) * x := by
      gcongr
    _ = ((N + 1 : ℕ) : ℝ) * (N : ℝ) *
        Real.exp (-(d : ℝ) / 100) := by
      dsimp only [x]
      ring

/-! ## Independent sets -/

theorem sq_div_four_le_choose_two {u : ℕ} (hu : 2 ≤ u) :
    (u : ℝ) ^ 2 / 4 ≤ (u.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two ℝ]
  have huR : (2 : ℝ) ≤ u := by exact_mod_cast hu
  nlinarith

theorem nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      omega

/-- For average-degree parameter at least `720000`, the union bound for all
independent sets of order at least `N/300` is at most `1/9`. -/
theorem measureReal_badIndependentEvent_reciprocal_le
    (d q : ℕ) (hd : 720000 ≤ d) (hq : 0 < q) :
    let N := 2 * d * q
    let p := reciprocalProbability q hq
    (randomEdgeMeasure N p).real (badIndependentEvent N) ≤ 1 / 9 := by
  dsimp only
  let N := 2 * d * q
  let p := reciprocalProbability q hq
  have hdpos : 0 < d := by omega
  have hNlarge : 600 ≤ N := by
    have hq1 : 1 ≤ q := hq
    dsimp only [N]
    calc
      600 ≤ 2 * d := by omega
      _ = 2 * d * 1 := by omega
      _ ≤ 2 * d * q := Nat.mul_le_mul_left (2 * d) hq1
  have hNpos : 0 < N := by omega
  have hsizecard : #(largeVertexSizes N) ≤ N + 1 := by
    simpa only [largeVertexSizes, Finset.card_range] using
      Finset.card_filter_le (Finset.range (N + 1)) (fun u => N ≤ 300 * u)
  have hindividual (u : ℕ) (hu : u ∈ largeVertexSizes N) :
      (N.choose u : ℝ) * Real.exp (-(p : ℝ) * (u.choose 2)) ≤
        ((1 : ℝ) / 18) ^ N := by
    have hNu := (mem_largeVertexSizes.mp hu).2
    have hu2 : 2 ≤ u := by omega
    have hchooseLower := sq_div_four_le_choose_two hu2
    have hNuR : (N : ℝ) ≤ 300 * (u : ℝ) := by exact_mod_cast hNu
    have hNsq : (N : ℝ) ^ 2 ≤ 90000 * (u : ℝ) ^ 2 := by
      calc
        (N : ℝ) ^ 2 ≤ (300 * (u : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg N) hNuR 2
        _ = 90000 * (u : ℝ) ^ 2 := by ring
    have hqR : (0 : ℝ) < q := by positivity
    have hNformula : (N : ℝ) = 2 * (d : ℝ) * q := by
      dsimp only [N]
      norm_num
    have hexponent : (d : ℝ) * N / 180000 ≤
        (p : ℝ) * (u.choose 2) := by
      rw [coe_reciprocalProbability]
      have hmiddle : (N : ℝ) ^ 2 / (360000 * q) ≤
          (u : ℝ) ^ 2 / (4 * q) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc
        (d : ℝ) * N / 180000 = (N : ℝ) ^ 2 / (360000 * q) := by
          rw [hNformula]
          field_simp
          ring
        _ ≤ (u : ℝ) ^ 2 / (4 * q) := hmiddle
        _ ≤ (u.choose 2 : ℝ) / q := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        _ = (1 / (q : ℝ)) * (u.choose 2 : ℝ) := by ring
    have hchooseUpper : (N.choose u : ℝ) ≤ (2 : ℝ) ^ N := by
      exact_mod_cast Nat.choose_le_two_pow N u
    have hdR : (720000 : ℝ) ≤ d := by exact_mod_cast hd
    have hexp : Real.exp (-(p : ℝ) * (u.choose 2)) ≤
        Real.exp (-4 * (N : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hN0 : (0 : ℝ) ≤ N := by positivity
      have hprod : 720000 * (N : ℝ) ≤ (d : ℝ) * N :=
        mul_le_mul_of_nonneg_right hdR hN0
      nlinarith
    have hNne : N ≠ 0 := hNpos.ne'
    have hexp4 : Real.exp (-4 * (N : ℝ)) ≤ ((1 : ℝ) / 36) ^ N := by
      have hrewrite : Real.exp (-4 * (N : ℝ)) =
          (Real.exp (-2)) ^ (2 * N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num only [Nat.cast_mul]
        ring
      rw [hrewrite, pow_mul]
      have hb : Real.exp (-2) ^ 2 ≤ ((1 : ℝ) / 6) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le
          (exp_neg_two_lt_one_six.le) 2
      norm_num at hb ⊢
      exact pow_le_pow_left₀ (by positivity) hb N
    calc
      (N.choose u : ℝ) * Real.exp (-(p : ℝ) * (u.choose 2)) ≤
          (2 : ℝ) ^ N * ((1 : ℝ) / 36) ^ N :=
        mul_le_mul hchooseUpper (hexp.trans hexp4) (by positivity) (by positivity)
      _ = ((1 : ℝ) / 18) ^ N := by rw [← mul_pow]; congr 1 <;> norm_num
  calc
    (randomEdgeMeasure N p).real (badIndependentEvent N) ≤
        ∑ u ∈ largeVertexSizes N,
          (N.choose u : ℝ) * Real.exp (-(p : ℝ) * (u.choose 2)) :=
      measureReal_badIndependentEvent_le_exp_size_sum N p
    _ ≤ ∑ _u ∈ largeVertexSizes N, ((1 : ℝ) / 18) ^ N := by
      apply Finset.sum_le_sum
      intro u hu
      exact hindividual u hu
    _ = (#(largeVertexSizes N) : ℝ) * ((1 : ℝ) / 18) ^ N := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((N + 1 : ℕ) : ℝ) * ((1 : ℝ) / 18) ^ N := by
      gcongr
    _ ≤ ((2 : ℝ) ^ N) * ((1 : ℝ) / 18) ^ N := by
      gcongr
      exact_mod_cast nat_succ_le_two_pow N
    _ = ((1 : ℝ) / 9) ^ N := by rw [← mul_pow]; congr 1 <;> norm_num
    _ ≤ 1 / 9 := by
      obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
      rw [hv]
      rw [pow_succ]
      have hpow : ((0 : ℝ) ≤ (1 / 9 : ℝ) ^ v) := by positivity
      have hpow1 : ((1 / 9 : ℝ) ^ v ≤ 1) := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith

/-! ## Closing the parameters -/

/-- The coefficient which makes the vertex number a monomial in `d`. -/
def parameterCoefficient (g : ℕ) : ℕ :=
  200 * localRadius g * (2 * (localRadius g) ^ 2) ^ (localRadius g)

theorem parameterCoefficient_pos (g : ℕ) : 0 < parameterCoefficient g := by
  unfold parameterCoefficient
  have hr := localRadius_pos g
  positivity

theorem randomParameterN_eq_monomial (g d : ℕ) :
    randomParameterN g d =
      parameterCoefficient g * d ^ (localRadius g + 1) := by
  simp only [randomParameterN, localDenominator, localScale,
    parameterCoefficient, pow_succ, mul_pow]
  ring

/-- For every girth scale, the displayed reciprocal-probability parameters
give a deterministic source graph satisfying all four strengthened random
properties. -/
theorem exists_isGoodSource_explicit_parameters (g : ℕ) :
    ∃ N d : ℕ, ∃ p : unitInterval, ∃ E : Set (RandomEdge N),
      10 ≤ N ∧ 10 ≤ d ∧ IsGoodSource E d g := by
  let r := localRadius g
  let C := parameterCoefficient g
  have hCposNat : 0 < C := parameterCoefficient_pos g
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hCposNat
  have hKpos : (0 : ℝ) < 8 * (C : ℝ) ^ 2 := by positivity
  obtain ⟨d, hd, hdom⟩ := exists_nat_ge_const_mul_pow_le_exp
    (8 * (C : ℝ) ^ 2) hKpos (2 * (r + 1)) 720000
      ((1 : ℝ) / 100) (by norm_num)
  have hdpos : 0 < d := by omega
  let q := localDenominator g d
  have hq : 0 < q := localDenominator_pos g hdpos
  let N := randomParameterN g d
  let p := reciprocalProbability q hq
  have hNdef : N = 2 * d * q := by
    rfl
  have hNpos : 0 < N := by
    rw [hNdef]
    positivity
  have hNten : 10 ≤ N := by
    have hq1 : 1 ≤ q := hq
    rw [hNdef]
    calc
      10 ≤ 2 * d := by omega
      _ = 2 * d * 1 := by omega
      _ ≤ 2 * d * q := Nat.mul_le_mul_left (2 * d) hq1
  have hNformula : (N : ℝ) = (C : ℝ) * (d : ℝ) ^ (r + 1) := by
    rw [show N = randomParameterN g d by rfl,
      randomParameterN_eq_monomial]
    dsimp only [C, r]
    norm_num
  have hdomN : 8 * (N : ℝ) ^ 2 ≤ Real.exp ((d : ℝ) / 100) := by
    have hpowrewrite : (d : ℝ) ^ (2 * (r + 1)) =
        ((d : ℝ) ^ (r + 1)) ^ 2 := by
      rw [show 2 * (r + 1) = (r + 1) * 2 by omega, pow_mul]
    rw [hpowrewrite] at hdom
    rw [hNformula]
    convert hdom using 1 <;> ring
  have hcancel : Real.exp ((d : ℝ) / 100) *
      Real.exp (-(d : ℝ) / 100) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hdomCancel : 8 * (N : ℝ) ^ 2 *
      Real.exp (-(d : ℝ) / 100) ≤ 1 := by
    calc
      8 * (N : ℝ) ^ 2 * Real.exp (-(d : ℝ) / 100) ≤
          Real.exp ((d : ℝ) / 100) * Real.exp (-(d : ℝ) / 100) :=
        mul_le_mul_of_nonneg_right hdomN (Real.exp_pos _).le
      _ = 1 := hcancel
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hratio : (N : ℝ) * Real.exp (-(d : ℝ) / 100) ≤ 1 := by
    have hpoly : (N : ℝ) ≤ 8 * (N : ℝ) ^ 2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le).trans hdomCancel
  have hcutBudget : ((N + 1 : ℕ) : ℝ) * (N : ℝ) *
      Real.exp (-(d : ℝ) / 100) ≤ 1 / 4 := by
    have hpoly : 4 * ((N + 1 : ℕ) : ℝ) * (N : ℝ) ≤
        8 * (N : ℝ) ^ 2 := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hmul :
        (4 * ((N + 1 : ℕ) : ℝ) * (N : ℝ)) *
            Real.exp (-(d : ℝ) / 100) ≤
          (8 * (N : ℝ) ^ 2) * Real.exp (-(d : ℝ) / 100) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    nlinarith [hmul, hdomCancel]
  have hedge :
      (randomEdgeMeasure N p).real (badEdgeEvent N d) ≤ 1 / 6 := by
    have h := measureReal_badEdgeEvent_reciprocal_le d q hdpos hq
    rw [← hNdef] at h
    have hdR : (720000 : ℝ) ≤ d := by exact_mod_cast hd
    calc
      (randomEdgeMeasure N p).real (badEdgeEvent N d) ≤
          Real.exp (-((d : ℝ) * N) / 80) := h
      _ ≤ Real.exp (-2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ 1 / 6 := exp_neg_two_lt_one_six.le
  have hcut :
      (randomEdgeMeasure N p).real (badCutEvent N d) ≤ 1 / 4 := by
    exact (measureReal_badCutEvent_reciprocal_le d q hdpos hq (by
      simpa only [hNdef] using hratio)).trans (by
        simpa only [hNdef] using hcutBudget)
  have hind :
      (randomEdgeMeasure N p).real (badIndependentEvent N) ≤ 1 / 9 := by
    have h := measureReal_badIndependentEvent_reciprocal_le d q hd hq
    rw [hNdef]
    simpa only [p] using h
  have hlocal :
      (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) ≤ 1 / 100 := by
    exact measureReal_badLocalSparsityEvent_parameters_le g d hdpos
  obtain ⟨E, hE⟩ := exists_isGoodSource_of_component_sum_lt_one
    (N := N) (d := d) (g := g) (p := p) (by
      calc
        (randomEdgeMeasure N p).real (badEdgeEvent N d) +
            (randomEdgeMeasure N p).real (badCutEvent N d) +
            (randomEdgeMeasure N p).real (badIndependentEvent N) +
            (randomEdgeMeasure N p).real (badLocalSparsityEvent N g) ≤
          1 / 6 + 1 / 4 + 1 / 9 + 1 / 100 := by gcongr
        _ < 1 := by norm_num)
  exact ⟨N, d, p, E, hNten, by omega, hE⟩

end RB

end

end LeanCo.HypercubeTuran
