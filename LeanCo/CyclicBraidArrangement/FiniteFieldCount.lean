import LeanCo.CyclicBraidArrangement.FiniteFieldGaps
import Mathlib.Data.Nat.Factorial.BigOperators

/-! Summing fixed-cycle gap counts and evaluating the cyclic formula. -/

namespace CyclicBraidArrangement

open scoped BigOperators

/-- At a natural argument large enough for all factors, the polynomial
binomial agrees with the ordinary natural binomial coefficient. -/
theorem generalizedChoose_natCast (a k : ℕ) (hk : k ≤ a) :
    generalizedChoose (a : ℚ) k = (a.choose k : ℚ) := by
  unfold generalizedChoose
  have hprod : (∏ i ∈ Finset.range k, ((a : ℚ) - i)) =
      (a.descFactorial k : ℚ) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub]
    exact (Finset.mem_range.mp hi).le.trans hk
  rw [hprod, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

namespace DeformationMatrix

/-- The adjacent-gap candidate count, presented through normalized cyclic
orders and remainder multisets.  It is identified with the genuinely
all-pairs-safe complement count only under cyclic compatibility in
`FiniteFieldPlacementCount`. -/
noncomputable def adjacentGapOrbitCount {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) : ℕ :=
  ∑ w : NormalizedCycle n, Fintype.card (M.FixedCycleGaps q w.1)

/-- Summing the fixed-cycle stars-and-bars counts gives the finite-field
orbit count used in the main theorem. -/
theorem adjacentGapOrbitCount_eq_cycle_sum {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (q : ℕ)
    (hfit : ∀ w : NormalizedCycle n, n + M.cycleWeight w.1 ≤ q) :
    adjacentGapOrbitCount M q =
      ∑ w : NormalizedCycle n,
        (q - M.cycleWeight w.1 - 1).choose (n - 1) := by
  classical
  unfold adjacentGapOrbitCount
  apply Finset.sum_congr rfl
  intro w hw
  exact card_fixedCycleGaps M q w.1 (hfit w)

/-- The finite-field orbit count is the cyclic polynomial expression evaluated
at `q`, once `q` is large enough for all lower bounds. -/
theorem adjacentGapOrbitCount_eq_cycleFormula {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (q : ℕ)
    (hfit : ∀ w : NormalizedCycle n, n + M.cycleWeight w.1 ≤ q) :
    (adjacentGapOrbitCount M q : ℚ) = cycleFormula M q := by
  classical
  rw [adjacentGapOrbitCount_eq_cycle_sum M q hfit]
  push_cast
  unfold cycleFormula
  apply Finset.sum_congr rfl
  intro w hw
  have hsub : q - M.cycleWeight w.1 - 1 =
      q - (M.cycleWeight w.1 + 1) := by omega
  have hk : n - 1 ≤ q - M.cycleWeight w.1 - 1 := by
    have := hfit w
    omega
  have hq : M.cycleWeight w.1 ≤ q := by
    have := hfit w
    omega
  have h1 : 1 ≤ q - M.cycleWeight w.1 := by
    have := hfit w
    omega
  have harg : ((q - M.cycleWeight w.1 - 1 : ℕ) : ℚ) =
      (q : ℚ) - M.cycleWeight w.1 - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_sub hq]
    norm_num
  rw [← harg, generalizedChoose_natCast _ _ hk]

end DeformationMatrix

end CyclicBraidArrangement
