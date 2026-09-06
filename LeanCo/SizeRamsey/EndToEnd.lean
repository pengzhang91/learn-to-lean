import LeanCo.SizeRamsey.KeyLemmaWeightFinal
import LeanCo.SizeRamsey.BLSLargePathLower
import LeanCo.SizeRamsey.TwoSided

/-!
# Unconditional end-to-end theorem

This is the final assembly for Wang--Wang, *The Multicolour Size--Ramsey
Number of an Even Cycle* (arXiv:2608.30481v1).  The lower half is proved
locally through the Beke--Li--Sahasrabudhe path theorem; the upper half is
the explicit probabilistic construction formalized in the upper modules.
-/

namespace LeanCo.SizeRamsey

/-- Unconditional closure of the path lower bound used by Wang--Wang. -/
theorem BLSPathLowerBoundV1_closed : BLSPathLowerBoundV1 :=
  BLSPathLowerBoundV1_of_BLSKeyLemmaV1 BLSKeyLemmaV1_closed

/-- Unconditional two-sided theorem for even cycles, in the exact bundled
predicate used throughout the development. -/
theorem wangWang_evenCycle_twoSided_v1 :
    WangWangEvenCycleTwoSidedV1 :=
  wangWang_evenCycle_twoSided_of_BLSPathLowerBoundV1
    BLSPathLowerBoundV1_closed

/-- Literal expanded form of the selected paper's main theorem. -/
theorem wangWang_evenCycle_twoSided :
    ∃ c : ℝ, 0 < c ∧
      ∀ k n : ℕ, 2 ≤ k →
        100 * Real.log (k : ℝ) ≤ (n : ℝ) → Even n →
          IsCycleSizeRamseyLowerBound k n (pathLowerScale c k n) ∧
          IsCycleSizeRamseyUpperBound k n (cycleUpperNat k n) := by
  exact wangWang_evenCycle_twoSided_v1

end LeanCo.SizeRamsey
