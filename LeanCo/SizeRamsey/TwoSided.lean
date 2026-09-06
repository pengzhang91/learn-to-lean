import LeanCo.SizeRamsey.UpperBound
import LeanCo.SizeRamsey.PathLowerBound
import LeanCo.SizeRamsey.PathToCycleLower

/-!
# The literal two-sided target for even cycles

This module records the exact proposition that remains after the explicit
upper proof: one absolute positive lower constant, outside the quantifiers
over the number of colours and the cycle order, together with the explicit
Wang--Wang upper scale.  The assembly theorem below is intentionally named
as conditional on the BLS path theorem; closing that premise locally is the
remaining substantive lower-bound task.
-/

namespace LeanCo.SizeRamsey

/-- Literal predicate corresponding to the two-sided assertion in Theorem
1.1, with the v1 threshold `n ≥ 100 log k` and the paper's explicit upper
constant retained through `cycleUpperNat`. -/
def WangWangEvenCycleTwoSidedV1 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ k n : ℕ, 2 ≤ k →
      100 * Real.log (k : ℝ) ≤ (n : ℝ) → Even n →
        IsCycleSizeRamseyLowerBound k n (pathLowerScale c k n) ∧
        IsCycleSizeRamseyUpperBound k n (cycleUpperNat k n)

/-- Once the locally formalized BLS-v1 path lower theorem is closed, the
path-to-cycle transfer and the already unconditional exact upper theorem
assemble the selected paper's complete two-sided statement immediately. -/
theorem wangWang_evenCycle_twoSided_of_BLSPathLowerBoundV1
    (hBLS : BLSPathLowerBoundV1) :
    WangWangEvenCycleTwoSidedV1 := by
  obtain ⟨c, hc, hlower⟩ := hBLS
  refine ⟨c, hc, ?_⟩
  intro k n hk hn hnEven
  refine ⟨?_, wangWang_cycle_upper_bound hk hn hnEven⟩
  exact cycleSizeRamseyLowerBound_of_pathSizeRamseyLowerBound
    (hlower k n hk hn)

end LeanCo.SizeRamsey
