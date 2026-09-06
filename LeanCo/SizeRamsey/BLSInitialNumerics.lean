import LeanCo.SizeRamsey.BLSStarScheduleNumerics
import LeanCo.SizeRamsey.HighCoreRestriction
import Mathlib.Tactic

/-!
# Numerical bookkeeping for the initial BLS cleanup

The initial low-degree threshold and the initial star palette both use one
thousandth of the total colour budget.  This file verifies their palette
cost, the size of the resulting restricted high core, and the floor-sensitive
degree estimate for the first star cleanup.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

noncomputable section

universe u

/-- Degree threshold used by the initial low-degree decomposition. -/
def initialDegreeThreshold (r : ℕ) : ℕ :=
  r / 1000

/-- Number of colours reserved for the initial star cleanup. -/
def initialStarBudget (r : ℕ) : ℕ :=
  r / 1000

/-! ## Positivity and palette cost -/

theorem initialDegreeThreshold_pos {r : ℕ} (hr : 1000 ≤ r) :
    0 < initialDegreeThreshold r := by
  unfold initialDegreeThreshold
  exact Nat.div_pos (by omega) (by omega)

theorem initialStarBudget_pos {r : ℕ} (hr : 1000 ≤ r) :
    0 < initialStarBudget r := by
  unfold initialStarBudget
  exact Nat.div_pos (by omega) (by omega)

/-- The low-degree palette and the star palette together use at most one
twelfth of the total palette.  The conservative lower bound `2000 ≤ r`
also ensures that both integer budgets are at least two. -/
theorem initial_thresholds_pos_and_palette
    {r : ℕ} (hr : 2000 ≤ r) :
    0 < initialDegreeThreshold r ∧
      0 < initialStarBudget r ∧
      (3 * initialDegreeThreshold r + 2) + initialStarBudget r ≤ r / 12 := by
  let T : ℕ := r / 1000
  have hTtwo : 2 ≤ T := by
    dsimp only [T]
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by simpa using hr)
  have hmul : 1000 * T ≤ r := by
    dsimp only [T]
    exact Nat.mul_div_le r 1000
  have hpalette : 12 * ((3 * T + 2) + T) ≤ r := by
    calc
      12 * ((3 * T + 2) + T) ≤ 1000 * T := by omega
      _ ≤ r := hmul
  refine ⟨?_, ?_, ?_⟩
  · simpa [initialDegreeThreshold, T] using
      (lt_of_lt_of_le (by omega : 0 < 2) hTtwo)
  · simpa [initialStarBudget, T] using
      (lt_of_lt_of_le (by omega : 0 < 2) hTtwo)
  · apply (Nat.le_div_iff_mul_le (by omega)).2
    simpa [initialDegreeThreshold, initialStarBudget, T, Nat.mul_comm] using hpalette

/-! ## Size of the initial restricted high core -/

private theorem log_natCast_nonneg (r : ℕ) :
    0 ≤ Real.log (r : ℝ) := by
  cases r with
  | zero => simp
  | succ r =>
      apply Real.log_nonneg
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)

/-- Handshaking plus the initial edge cap bounds the number of high vertices.
The conclusion is stated for the explicit high-vertex finset. -/
theorem initial_highCoreVertexFinset_card_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : ℝ} {r n : ℕ}
    (hC : 0 ≤ C) (hCsmall : 10000 * C ≤ 1)
    (hedges : (edgeCount G : ℝ) ≤ roundEdgeCap C r n 0) :
    ((highCoreVertexFinset G (initialDegreeThreshold r)).card : ℝ) ≤
      (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) / 4 := by
  let Δ : ℕ := initialDegreeThreshold r
  let K : ℕ := (highCoreVertexFinset G Δ).card
  have hhandNat : (Δ + 1) * K ≤ 2 * edgeCount G := by
    simpa only [K] using highCoreVertexFinset_card_bound G Δ
  have hhand :
      ((Δ + 1 : ℕ) : ℝ) * (K : ℝ) ≤ 2 * (edgeCount G : ℝ) := by
    exact_mod_cast hhandNat
  have hruppNat : r ≤ 1000 * (Δ + 1) := by
    have hlt : r < 1000 * (r / 1000 + 1) :=
      Nat.lt_mul_div_succ r (by omega)
    simpa [Δ, initialDegreeThreshold] using hlt.le
  have hrupp : (r : ℝ) ≤ 1000 * ((Δ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hruppNat
  have h8000 : 8000 * C ≤ 1 := by nlinarith
  have hcoeff : 8 * C * (r : ℝ) ≤ ((Δ + 1 : ℕ) : ℝ) := by
    calc
      8 * C * (r : ℝ) ≤
          8 * C * (1000 * ((Δ + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hrupp (mul_nonneg (by norm_num) hC)
      _ = (8000 * C) * ((Δ + 1 : ℕ) : ℝ) := by ring
      _ ≤ 1 * ((Δ + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right h8000 (by positivity)
      _ = ((Δ + 1 : ℕ) : ℝ) := by ring
  have hscale :
      0 ≤ (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) / 4 := by
    have := log_natCast_nonneg r
    positivity
  have hcap :
      2 * roundEdgeCap C r n 0 ≤
        ((Δ + 1 : ℕ) : ℝ) *
          ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) / 4) := by
    calc
      2 * roundEdgeCap C r n 0 =
          (8 * C * (r : ℝ)) *
            ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) / 4) := by
        unfold roundEdgeCap
        norm_num
        ring
      _ ≤ ((Δ + 1 : ℕ) : ℝ) *
            ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hcoeff hscale
  have hcross :
      ((Δ + 1 : ℕ) : ℝ) * (K : ℝ) ≤
        ((Δ + 1 : ℕ) : ℝ) *
          ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) / 4) := by
    exact hhand.trans ((mul_le_mul_of_nonneg_left hedges (by norm_num)).trans hcap)
  have hΔpos : (0 : ℝ) < ((Δ + 1 : ℕ) : ℝ) := by positivity
  have hK :
      (K : ℝ) ≤ (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) / 4 :=
    le_of_mul_le_mul_left hcross hΔpos
  simpa only [K, Δ] using hK

/-- The nonnegativity assumption on `C` can be discharged from the public
interface.  If `C < 0`, the cap hypothesis forces the graph to have no
edges, so the high core is empty. -/
theorem initial_highCoreVertexFinset_card_le_of_small
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : ℝ} {r n : ℕ}
    (hCsmall : 10000 * C ≤ 1)
    (hedges : (edgeCount G : ℝ) ≤ roundEdgeCap C r n 0) :
    ((highCoreVertexFinset G (initialDegreeThreshold r)).card : ℝ) ≤
      (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) / 4 := by
  by_cases hC : 0 ≤ C
  · exact initial_highCoreVertexFinset_card_le G hC hCsmall hedges
  · have hscale :
        0 ≤ (r : ℝ) ^ 2 * Real.log (r : ℝ) * (n : ℝ) := by
      have := log_natCast_nonneg r
      positivity
    have hcap : roundEdgeCap C r n 0 ≤ 0 := by
      rw [show roundEdgeCap C r n 0 =
          C * ((r : ℝ) ^ 2 * Real.log (r : ℝ) * (n : ℝ)) by
        unfold roundEdgeCap
        norm_num
        ring]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hscale
    have hedgeReal : (edgeCount G : ℝ) = 0 :=
      le_antisymm (hedges.trans hcap) (by positivity)
    have hedgeZero : edgeCount G = 0 := by exact_mod_cast hedgeReal
    have hhand :=
      highCoreVertexFinset_card_bound G (initialDegreeThreshold r)
    rw [hedgeZero] at hhand
    have hcard :
        (highCoreVertexFinset G (initialDegreeThreshold r)).card = 0 := by
      have hprod :
          (initialDegreeThreshold r + 1) *
              (highCoreVertexFinset G (initialDegreeThreshold r)).card = 0 := by
        omega
      rcases Nat.mul_eq_zero.mp hprod with hfalse | hzero
      · omega
      · exact hzero
    rw [hcard]
    norm_num only [Nat.cast_zero]
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hnum :
        (0 : ℝ) ≤ (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) :=
      mul_nonneg (mul_nonneg hr0 (log_natCast_nonneg r)) hn0
    exact div_nonneg hnum (by norm_num : (0 : ℝ) ≤ 4)

/-- The same cardinal estimate in the vertex type used by the restricted
high core. -/
theorem initial_highCoreRestriction_card_le
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : ℝ} {r n : ℕ}
    (hCsmall : 10000 * C ≤ 1)
    (hedges : (edgeCount G : ℝ) ≤ roundEdgeCap C r n 0) :
    (Fintype.card ↥(highCoreVertexFinset G (initialDegreeThreshold r)) : ℝ) ≤
      (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) / 4 := by
  simpa only [Fintype.card_coe] using
    initial_highCoreVertexFinset_card_le_of_small G hCsmall hedges

/-! ## Initial star quotient -/

/-- Flooring the initial one-thousandth palette costs at most a factor
`3/2`: once the budget is at least two, `r ≤ 1500 ⋅ ⌊r/1000⌋`. -/
theorem le_1500_mul_initialStarBudget {r : ℕ} (hr : 2000 ≤ r) :
    r ≤ 1500 * initialStarBudget r := by
  let T : ℕ := r / 1000
  have hTtwo : 2 ≤ T := by
    dsimp only [T]
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by simpa using hr)
  have hlt : r < 1000 * (r / 1000 + 1) :=
    Nat.lt_mul_div_succ r (by omega)
  calc
    r ≤ 1000 * (T + 1) := by simpa [T] using hlt.le
    _ ≤ 1500 * T := by omega
    _ = 1500 * initialStarBudget r := by simp [T, initialStarBudget]

/-- Under the initial edge cap, the integer maximum-degree quotient produced
by the star cleanup lies below the initial beta threshold. -/
theorem initialStarBudget_quotient_le_beta
    {C β₀ : ℝ} {r n e : ℕ}
    (hC : 0 < C) (hCβ : 20000 * C ≤ β₀)
    (hr : 2000 ≤ r) (hn : 12 ≤ n)
    (he : (e : ℝ) ≤ roundEdgeCap C r n 0) :
    (((8 * e) / (n * initialStarBudget r) : ℕ) : ℝ) ≤
      β₀ * (r : ℝ) * Real.log (r : ℝ) := by
  let T : ℕ := initialStarBudget r
  have hTpos : 0 < T := by
    dsimp only [T]
    exact initialStarBudget_pos (by omega)
  have hnpos : 0 < n := lt_of_lt_of_le (by omega) hn
  have hrpos : 0 < r := lt_of_lt_of_le (by omega) hr
  have hlog : 0 ≤ Real.log (r : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hrpos
  have hfloor : (r : ℝ) ≤ 1500 * (T : ℝ) := by
    exact_mod_cast le_1500_mul_initialStarBudget hr
  have h12000 : 12000 * C ≤ β₀ := by
    calc
      12000 * C ≤ 20000 * C := by nlinarith [hC.le]
      _ ≤ β₀ := hCβ
  have hfactor :
      0 ≤ 8 * C * (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) := by
    positivity
  have htail :
      0 ≤ (r : ℝ) * Real.log (r : ℝ) * (n : ℝ) * (T : ℝ) := by
    positivity
  have hcross :
      (8 : ℝ) * (e : ℝ) ≤
        β₀ * (r : ℝ) * Real.log (r : ℝ) *
          ((n : ℝ) * (T : ℝ)) := by
    calc
      (8 : ℝ) * (e : ℝ) ≤ 8 * roundEdgeCap C r n 0 :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ = (8 * C * (r : ℝ) * Real.log (r : ℝ) * (n : ℝ)) *
            (r : ℝ) := by
        unfold roundEdgeCap
        norm_num
        ring
      _ ≤ (8 * C * (r : ℝ) * Real.log (r : ℝ) * (n : ℝ)) *
            (1500 * (T : ℝ)) :=
        mul_le_mul_of_nonneg_left hfloor hfactor
      _ = (12000 * C) *
            ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) * (T : ℝ)) := by
        ring
      _ ≤ β₀ *
            ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ) * (T : ℝ)) :=
        mul_le_mul_of_nonneg_right h12000 htail
      _ = β₀ * (r : ℝ) * Real.log (r : ℝ) *
            ((n : ℝ) * (T : ℝ)) := by ring
  calc
    (((8 * e) / (n * initialStarBudget r) : ℕ) : ℝ) =
        (((8 * e) / (n * T) : ℕ) : ℝ) := by rfl
    _ ≤ ((8 * e : ℕ) : ℝ) / ((n * T : ℕ) : ℝ) :=
      Nat.cast_div_le
    _ ≤ β₀ * (r : ℝ) * Real.log (r : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((n * T : ℕ) : ℝ))).2
      push_cast
      simpa only [mul_assoc] using hcross

end

end LeanCo.SizeRamsey
