import LeanCo.HypercubeTuran.NontrivialCuts
import LeanCo.HypercubeTuran.AsymptoticParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Backup numerical estimates for the random source graph

This module is intentionally independent of `RandomParameters`.  It develops
coarse reciprocal-probability estimates on top of the endpoint-free cut union
bound from `NontrivialCuts`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset ProbabilityTheory SimpleGraph unitInterval

namespace LeanCo.HypercubeTuran

noncomputable section

namespace RB

/-- The point of the unit interval represented by `1/q`.  This backup name
avoids coupling this file to the concurrently developed parameter module. -/
def backupReciprocalProbability (q : ℕ) (hq : 0 < q) : unitInterval :=
  ⟨1 / (q : ℝ), by positivity, by
    rw [div_le_one (by positivity)]
    exact_mod_cast hq⟩

@[simp]
theorem coe_backupReciprocalProbability (q : ℕ) (hq : 0 < q) :
    (backupReciprocalProbability q hq : ℝ) = 1 / (q : ℝ) := rfl

/-- A rational estimate sufficient for the fixed lower-tail transform. -/
theorem backup_exp_neg_quarter_le :
    Real.exp (-(1 : ℝ) / 4) ≤ 79 / 100 := by
  have hseries := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 1 / 4 by norm_num) 3
  have hlower : (100 : ℝ) / 79 ≤ Real.exp ((1 : ℝ) / 4) := by
    norm_num [Finset.sum_range_succ] at hseries ⊢
    linarith
  rw [show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring, Real.exp_neg]
  have hinv : (Real.exp ((1 : ℝ) / 4))⁻¹ ≤ ((100 : ℝ) / 79)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) (by positivity)).2 hlower
  norm_num at hinv ⊢
  exact hinv

/-- A deliberately weak but convenient lower-tail estimate. -/
theorem backup_binomial_four_five_mean_lower_le_exp
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
        nlinarith [backup_exp_neg_quarter_le]
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

/-- At `N = 2dq` and `p = 1/q`, a fixed-cardinality family of bad cuts has
the expected exponential cost. -/
theorem measureReal_badCutEventAtSize_backup_reciprocal_le
    (d q u : ℕ) (hd : 0 < d) (hq : 0 < q) :
    let N := 2 * d * q
    let p := backupReciprocalProbability q hq
    (randomEdgeMeasure N p).real (badCutEventAtSize N d u) ≤
      (N.choose u : ℝ) *
        Real.exp (-(((u * (N - u) : ℕ) : ℝ) / (q : ℝ)) / 100) := by
  dsimp only
  let N : ℕ := 2 * d * q
  let p : unitInterval := backupReciprocalProbability q hq
  let m : ℕ := u * (N - u)
  have hN : 0 < N := by
    dsimp only [N]
    positivity
  have ht : -(1 : ℝ) / 4 < 0 := by norm_num
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
        nlinarith [backup_exp_neg_quarter_le]
      _ ≤ Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) := by
        convert Real.add_one_le_exp (-(p : ℝ) * (21 / 100 : ℝ)) using 1 <;>
          ring
  have hpow :
      (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^ m ≤
        Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) ^ m :=
    pow_le_pow_left₀ hbase0 hbase m
  calc
    (randomEdgeMeasure N p).real (badCutEventAtSize N d u) ≤
        (N.choose u : ℝ) *
          (Real.exp (-(-(1 : ℝ) / 4) *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            (1 - (p : ℝ) + (p : ℝ) * Real.exp (-(1 : ℝ) / 4)) ^
              (u * (N - u))) :=
      measureReal_badCutEventAtSize_le_chernoff hN d u p ht
    _ ≤ (N.choose u : ℝ) *
          (Real.exp (-(-(1 : ℝ) / 4) *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            Real.exp (-(p : ℝ) * (21 / 100 : ℝ)) ^
              (u * (N - u))) := by
      gcongr
    _ = (N.choose u : ℝ) *
        Real.exp (-(((u * (N - u) : ℕ) : ℝ) / (q : ℝ)) / 100) := by
      congr 1
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp only [m, p, N]
      rw [coe_backupReciprocalProbability]
      norm_num only [Nat.cast_mul]
      field_simp
      ring

/-- Endpoint-free and complement-compressed reciprocal cut bound. -/
theorem measureReal_badCutEvent_backup_reciprocal_le_sum
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) :
    let N := 2 * d * q
    let p := backupReciprocalProbability q hq
    (randomEdgeMeasure N p).real (badCutEvent N d) ≤
      ∑ u ∈ smallShoreSizes N,
        (N.choose u : ℝ) *
          Real.exp (-(((u * (N - u) : ℕ) : ℝ) / (q : ℝ)) / 100) := by
  dsimp only
  rw [badCutEvent_eq_iUnion_smallShore_size]
  calc
    (randomEdgeMeasure (2 * d * q) (backupReciprocalProbability q hq)).real
        {E | ∃ u ∈ smallShoreSizes (2 * d * q),
          E ∈ badCutEventAtSize (2 * d * q) d u} ≤
        ∑ u ∈ smallShoreSizes (2 * d * q),
          (randomEdgeMeasure (2 * d * q)
            (backupReciprocalProbability q hq)).real
              (badCutEventAtSize (2 * d * q) d u) :=
      measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ u ∈ smallShoreSizes (2 * d * q),
        ((2 * d * q).choose u : ℝ) *
          Real.exp (-(((u * (2 * d * q - u) : ℕ) : ℝ) /
            (q : ℝ)) / 100) := by
      apply Finset.sum_le_sum
      intro u _
      exact measureReal_badCutEventAtSize_backup_reciprocal_le d q u hd hq

/-- A term in the small-shore sum is bounded by a power of the single
geometric base `N * exp (-d/100)`. -/
theorem backup_cut_term_le_geometric
    (d q u : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hu : u ∈ smallShoreSizes (2 * d * q)) :
    (((2 * d * q).choose u : ℕ) : ℝ) *
          Real.exp (-(((u * (2 * d * q - u) : ℕ) : ℝ) /
            (q : ℝ)) / 100) ≤
      (((2 * d * q : ℕ) : ℝ) *
        Real.exp (-(d : ℝ) / 100)) ^ u := by
  have huSmall := (mem_smallShoreSizes.mp hu).2
  have huHalf : u ≤ d * q := by
    exact Nat.le_of_mul_le_mul_left
      (by simpa only [Nat.mul_assoc] using huSmall) (by norm_num)
  have hrest : d * q ≤ 2 * d * q - u := by
    have hsplit : 2 * d * q = d * q + d * q := by ring
    rw [hsplit]
    omega
  have hmqNat : d * u * q ≤ u * (2 * d * q - u) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left u hrest
  have hmq : (d : ℝ) * u ≤
      (((u * (2 * d * q - u) : ℕ) : ℝ) / (q : ℝ)) := by
    rw [le_div_iff₀ (by exact_mod_cast hq)]
    norm_num only [Nat.cast_mul]
    exact_mod_cast hmqNat
  have hexp :
      Real.exp (-(((u * (2 * d * q - u) : ℕ) : ℝ) /
          (q : ℝ)) / 100) ≤
        Real.exp (-((d : ℝ) * u) / 100) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hchoose : (((2 * d * q).choose u : ℕ) : ℝ) ≤
      (((2 * d * q : ℕ) : ℝ) ^ u) := by
    exact_mod_cast Nat.choose_le_pow (2 * d * q) u
  calc
    (((2 * d * q).choose u : ℕ) : ℝ) *
          Real.exp (-(((u * (2 * d * q - u) : ℕ) : ℝ) /
            (q : ℝ)) / 100) ≤
        (((2 * d * q : ℕ) : ℝ) ^ u) *
          Real.exp (-((d : ℝ) * u) / 100) :=
      mul_le_mul hchoose hexp (Real.exp_pos _).le (by positivity)
    _ = (((2 * d * q : ℕ) : ℝ) *
        Real.exp (-(d : ℝ) / 100)) ^ u := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

/-- A simple numerical side condition makes all cut failures cost at most
one percent.  It is intentionally stated separately so asymptotic or explicit
integer parameter choices can discharge it without reopening probability. -/
theorem measureReal_badCutEvent_backup_reciprocal_le_one_hundredth
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hnum : (((2 * d * q + 1 : ℕ) : ℝ) *
        ((2 * d * q : ℕ) : ℝ)) *
          Real.exp (-(d : ℝ) / 100) ≤ 1 / 100) :
    (randomEdgeMeasure (2 * d * q) (backupReciprocalProbability q hq)).real
        (badCutEvent (2 * d * q) d) ≤ 1 / 100 := by
  let N : ℕ := 2 * d * q
  let a : ℝ := (N : ℝ) * Real.exp (-(d : ℝ) / 100)
  have hN : 0 < N := by
    dsimp only [N]
    positivity
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    positivity
  have ha1 : a ≤ 1 := by
    have hfac : (1 : ℝ) ≤ (N + 1 : ℕ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))
    have hsmall : ((N + 1 : ℕ) : ℝ) * a ≤ 1 / 100 := by
      simpa only [N, a, mul_assoc] using hnum
    nlinarith [mul_le_mul_of_nonneg_right hfac ha0]
  have hcard : #(smallShoreSizes N) ≤ N + 1 := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  calc
    (randomEdgeMeasure N (backupReciprocalProbability q hq)).real
        (badCutEvent N d) ≤
        ∑ u ∈ smallShoreSizes N,
          (N.choose u : ℝ) *
            Real.exp (-(((u * (N - u) : ℕ) : ℝ) / (q : ℝ)) / 100) := by
      simpa only [N] using
        measureReal_badCutEvent_backup_reciprocal_le_sum d q hd hq
    _ ≤ ∑ _u ∈ smallShoreSizes N, a := by
      apply Finset.sum_le_sum
      intro u hu
      calc
        (N.choose u : ℝ) *
            Real.exp (-(((u * (N - u) : ℕ) : ℝ) / (q : ℝ)) / 100) ≤
            a ^ u := by
          simpa only [N, a] using backup_cut_term_le_geometric d q u hd hq hu
        _ ≤ a := pow_le_of_le_one ha0 ha1 (by
          exact Nat.ne_of_gt (mem_smallShoreSizes.mp hu).1)
    _ = (#(smallShoreSizes N) : ℝ) * a := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((N + 1 : ℕ) : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ha0
    _ ≤ 1 / 100 := by
      simpa only [N, a, mul_assoc] using hnum

/-! ## Purely numerical closure -/

/-- A uniform polynomial-versus-exponential selector tailored to the cut
condition.  The constant and exponent are natural numbers so this lemma can
be used after rewriting a graph order as `K * d^n`. -/
theorem exists_nat_ge_polynomial_cut_condition
    (K n M : ℕ) (hK : 0 < K) (hM : 19800 ≤ M) :
    ∃ d : ℕ, M ≤ d ∧
      ((((K * d ^ n + 1 : ℕ) : ℝ) * ((K * d ^ n : ℕ) : ℝ)) *
        Real.exp (-(d : ℝ) / 100) ≤ 1 / 100) := by
  have hconst : (0 : ℝ) < 2 * (K : ℝ) ^ 2 := by positivity
  obtain ⟨d, hdM, hdom⟩ :=
    exists_nat_ge_const_mul_pow_le_exp
      (2 * (K : ℝ) ^ 2) hconst (2 * n) M (1 / 200) (by norm_num)
  refine ⟨d, hdM, ?_⟩
  let X : ℕ := K * d ^ n
  have hdpos : 0 < d := lt_of_lt_of_le (by omega : 0 < 19800) (hM.trans hdM)
  have hXpos : 0 < X := by
    dsimp only [X]
    positivity
  have hpoweq : (d : ℝ) ^ (2 * n) = ((d : ℝ) ^ n) ^ 2 := by
    rw [mul_comm 2 n, pow_mul]
  have hdom' : 2 * (X : ℝ) ^ 2 ≤ Real.exp ((d : ℝ) / 200) := by
    calc
      2 * (X : ℝ) ^ 2 =
          2 * (K : ℝ) ^ 2 * (d : ℝ) ^ (2 * n) := by
        dsimp only [X]
        norm_num only [Nat.cast_mul, Nat.cast_pow]
        rw [hpoweq]
        ring
      _ ≤ Real.exp ((1 / 200 : ℝ) * d) := hdom
      _ = Real.exp ((d : ℝ) / 200) := by congr 1 <;> ring
  have hsucc : ((X + 1 : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hXone : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
    linarith
  have hexpSmall : Real.exp (-(d : ℝ) / 200) ≤ 1 / 100 := by
    have hdlarge : (19800 : ℝ) ≤ d := by exact_mod_cast hM.trans hdM
    have hExp : (100 : ℝ) ≤ Real.exp ((d : ℝ) / 200) := by
      calc
        (100 : ℝ) ≤ (d : ℝ) / 200 + 1 := by nlinarith
        _ ≤ Real.exp ((d : ℝ) / 200) := Real.add_one_le_exp _
    rw [show -(d : ℝ) / 200 = -((d : ℝ) / 200) by ring,
      Real.exp_neg]
    have hinv : (Real.exp ((d : ℝ) / 200))⁻¹ ≤ (100 : ℝ)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).2 hExp
    norm_num at hinv ⊢
    exact hinv
  change (((X + 1 : ℕ) : ℝ) * (X : ℝ)) *
    Real.exp (-(d : ℝ) / 100) ≤ 1 / 100
  calc
    (((X + 1 : ℕ) : ℝ) * (X : ℝ)) *
        Real.exp (-(d : ℝ) / 100) ≤
      (2 * (X : ℝ) ^ 2) * Real.exp (-(d : ℝ) / 100) := by
        have hXR : (0 : ℝ) ≤ X := by positivity
        have heR : (0 : ℝ) ≤ Real.exp (-(d : ℝ) / 100) :=
          (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_right ?_ heR
        calc
          (((X + 1 : ℕ) : ℝ) * (X : ℝ)) ≤
              (2 * (X : ℝ)) * (X : ℝ) :=
            mul_le_mul_of_nonneg_right hsucc hXR
          _ = 2 * (X : ℝ) ^ 2 := by ring
    _ ≤ Real.exp ((d : ℝ) / 200) *
        Real.exp (-(d : ℝ) / 100) :=
      mul_le_mul_of_nonneg_right hdom' (Real.exp_pos _).le
    _ = Real.exp (-(d : ℝ) / 200) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ 1 / 100 := hexpSmall

end RB

end

end LeanCo.HypercubeTuran
