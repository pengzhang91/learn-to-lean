import Mathlib

/-!
# Numerical parameters in Wang--Wang's even-cycle size--Ramsey argument

This file isolates the real-arithmetic normalizations used for the random
bipartite host.  Keeping these identities separate avoids hiding coercion or
division assumptions in the later graph-theoretic proof.
-/

namespace LeanCo.SizeRamsey

noncomputable section

/-- The size of each side of the bipartite host in Lemma 2.1. -/
def hostPartSize (k n : ℕ) : ℕ := 10 ^ 5 * k * n

/-- The edge probability in Lemma 2.1. -/
def hostProbability (k n : ℕ) : ℝ := Real.log (k : ℝ) / n

/-- The explicit upper-bound scale in Theorem 1.1. -/
def cycleUpperScale (k n : ℕ) : ℝ :=
  2 * 10 ^ 10 * (k : ℝ) ^ 2 * Real.log (k : ℝ) * n

/-- The integer minimum-degree threshold used throughout the host argument. -/
def localDegreeThreshold (k : ℕ) : ℕ :=
  ⌈1000 * Real.log (k : ℝ)⌉₊

/-- Integer edge-per-vertex threshold in the local-sparsity conclusion of
Lemma 2.1. -/
def localSparsityFactor (k : ℕ) : ℕ :=
  ⌈100 * Real.log (k : ℝ)⌉₊

theorem log_natCast_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < Real.log (k : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < k by omega)

theorem hostPartSize_pos {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    0 < hostPartSize k n := by
  simp [hostPartSize, hk, hn]

theorem hostProbability_pos {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    0 < hostProbability k n := by
  exact div_pos (log_natCast_pos hk) (by exact_mod_cast hn)

theorem two_le_localDegreeThreshold {k : ℕ} (hk : 2 ≤ k) :
    2 ≤ localDegreeThreshold k := by
  have hceil : 1000 * Real.log (k : ℝ) ≤
      (localDegreeThreshold k : ℝ) := Nat.le_ceil _
  have hlog := log_natCast_pos hk
  have htwo := Real.log_two_gt_d9
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hmono : Real.log 2 ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) hkreal
  have hreal : (2 : ℝ) ≤ localDegreeThreshold k := by nlinarith
  exact_mod_cast hreal

/-- The precise rounding inequality required by the deterministic expansion
step: `6⌈100 log k⌉ < ⌈1000 log k⌉`. -/
theorem six_mul_localSparsityFactor_lt_localDegreeThreshold
    {k : ℕ} (hk : 2 ≤ k) :
    6 * localSparsityFactor k < localDegreeThreshold k := by
  have hlog0 : 0 ≤ Real.log (k : ℝ) := (log_natCast_pos hk).le
  have hsceil : (localSparsityFactor k : ℝ) <
      100 * Real.log (k : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hlog0)
  have hdceil : 1000 * Real.log (k : ℝ) ≤
      (localDegreeThreshold k : ℝ) := Nat.le_ceil _
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hmono : Real.log 2 ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) hkreal
  have htwo := Real.log_two_gt_d9
  have hreal : (6 : ℝ) * localSparsityFactor k <
      localDegreeThreshold k := by
    calc
      (6 : ℝ) * localSparsityFactor k <
          6 * (100 * Real.log (k : ℝ) + 1) := by nlinarith
      _ < 1000 * Real.log (k : ℝ) := by nlinarith
      _ ≤ localDegreeThreshold k := hdceil
  exact_mod_cast hreal

/-- The numerical slack used after selecting the majority colour:
`16 ⌈1000 log k⌉ ≤ 50000 log k` for `k ≥ 2`. -/
theorem sixteen_mul_localDegreeThreshold_le {k : ℕ} (hk : 2 ≤ k) :
    16 * (localDegreeThreshold k : ℝ) ≤ 50000 * Real.log (k : ℝ) := by
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlog_mono : Real.log 2 ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) hk_real
  have hlog_nonneg : 0 ≤ Real.log (k : ℝ) :=
    (log_natCast_pos hk).le
  have hceil : (localDegreeThreshold k : ℝ) <
      1000 * Real.log (k : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hlog_nonneg)
  have hunit : (16 : ℝ) ≤ 34000 * Real.log (k : ℝ) := by
    have htwo := Real.log_two_gt_d9
    nlinarith
  calc
    16 * (localDegreeThreshold k : ℝ) ≤
        16 * (1000 * Real.log (k : ℝ) + 1) := by nlinarith
    _ ≤ 50000 * Real.log (k : ℝ) := by nlinarith

theorem log_seventy_lt_five : Real.log 70 < 5 := by
  have h70 : (70 : ℝ) < 2 ^ (7 : ℕ) := by norm_num
  have hmono : Real.log 70 < Real.log (2 ^ (7 : ℕ)) :=
    Real.log_lt_log (by norm_num) h70
  rw [Real.log_pow] at hmono
  have htwo := Real.log_two_lt_d9
  norm_num at hmono ⊢
  nlinarith

theorem log_two_hundred_thousand_lt_thirteen : Real.log 200000 < 13 := by
  have hconst : (200000 : ℝ) < 2 ^ (18 : ℕ) := by norm_num
  have hmono : Real.log 200000 < Real.log (2 ^ (18 : ℕ)) :=
    Real.log_lt_log (by norm_num) hconst
  rw [Real.log_pow] at hmono
  have htwo := Real.log_two_lt_d9
  norm_num at hmono ⊢
  nlinarith

/-- A convenient linear bound for the logarithm in the range relevant to the
BFS-depth calculation. -/
theorem log_natCast_le_div_fourteen {n : ℕ} (hn : 70 ≤ n) :
    Real.log (n : ℝ) ≤ (n : ℝ) / 14 := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hratio : (0 : ℝ) < (n : ℝ) / 70 := div_pos hnpos (by norm_num)
  have hlog_ratio := Real.log_le_sub_one_of_pos hratio
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have h70ne : (70 : ℝ) ≠ 0 := by norm_num
  rw [Real.log_div hn0 h70ne] at hlog_ratio
  have h70 := log_seventy_lt_five
  have hnreal : (70 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- The paper's lower admissibility condition already forces `n ≥ 70`. -/
theorem seventy_le_of_hundred_log_le {k n : ℕ} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n) : 70 ≤ n := by
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogmono : Real.log 2 ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by norm_num) hkreal
  have htwo := Real.log_two_gt_d9
  have hn69 : (69 : ℝ) < n := by nlinarith
  exact_mod_cast hn69

/-- The explicit depth inequality used to make the interval of even cycle
lengths cross `n`.  Here `logb 2` is mathlib's base-two logarithm. -/
theorem bfs_depth_numerical_bound {k n : ℕ} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n) :
    4 + 2 * Real.logb 2 (2 * 10 ^ 5 * (k : ℝ) * n) < n := by
  have hn70 : 70 ≤ n := seventy_le_of_hundred_log_le hk hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hkpos : (0 : ℝ) < k := by positivity
  have hlogn := log_natCast_le_div_fourteen hn70
  have hlogconst := log_two_hundred_thousand_lt_thirteen
  have harg : (2 : ℝ) * 10 ^ 5 * k * n = 200000 * k * n := by norm_num
  have hlogarg :
      Real.log ((2 : ℝ) * 10 ^ 5 * k * n) =
        Real.log 200000 + Real.log (k : ℝ) + Real.log (n : ℝ) := by
    rw [harg, Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hkpos))
      (ne_of_gt hnpos), Real.log_mul (by norm_num) (ne_of_gt hkpos)]
  have hlogarg_nonneg :
      0 ≤ Real.log ((2 : ℝ) * 10 ^ 5 * k * n) := by
    apply Real.log_nonneg
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    norm_num only [pow_succ, pow_zero, mul_one]
    have hfirst : (200000 : ℝ) ≤ 200000 * k := by
      nlinarith
    have hk0 : (0 : ℝ) ≤ k := zero_le_one.trans hkone
    have hfactor0 : (0 : ℝ) ≤ 200000 * k :=
      mul_nonneg (by norm_num) hk0
    have hsecond : (200000 : ℝ) * k ≤ 200000 * k * n := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hnone hfactor0
    calc
      (1 : ℝ) ≤ 200000 := by norm_num
      _ ≤ 200000 * (k : ℝ) := hfirst
      _ ≤ 200000 * (k : ℝ) * n := hsecond
  have hlogarg_upper :
      Real.log ((2 : ℝ) * 10 ^ 5 * k * n) ≤
        13 + (n : ℝ) / 100 + (n : ℝ) / 14 := by
    rw [hlogarg]
    nlinarith
  have hlogtwo_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 2 / Real.log 2 < 3 := by
    have htwo := Real.log_two_gt_d9
    rw [div_lt_iff₀ hlogtwo_pos]
    nlinarith
  have hnreal : (70 : ℝ) ≤ n := by exact_mod_cast hn70
  rw [Real.logb]
  calc
    4 + 2 * (Real.log ((2 : ℝ) * 10 ^ 5 * k * n) / Real.log 2)
        = 4 + (2 / Real.log 2) *
            Real.log ((2 : ℝ) * 10 ^ 5 * k * n) := by ring
    _ ≤ 4 + 3 * Real.log ((2 : ℝ) * 10 ^ 5 * k * n) := by
      gcongr
    _ ≤ 4 + 3 * (13 + (n : ℝ) / 100 + (n : ℝ) / 14) := by
      gcongr
    _ < n := by nlinarith

/-- Expanding `2 p M²` gives the explicit edge bound in the paper. -/
theorem two_mul_probability_mul_partSize_sq {k n : ℕ} (hn : 0 < n) :
    2 * hostProbability k n * (hostPartSize k n : ℝ) ^ 2 =
      cycleUpperScale k n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [hostProbability, hostPartSize, cycleUpperScale, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  field_simp

/-- The same normalization without the leading factor two. -/
theorem probability_mul_partSize_sq {k n : ℕ} (hn : 0 < n) :
    hostProbability k n * (hostPartSize k n : ℝ) ^ 2 =
      10 ^ 10 * (k : ℝ) ^ 2 * Real.log (k : ℝ) * n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [hostProbability, hostPartSize, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

end

end LeanCo.SizeRamsey
