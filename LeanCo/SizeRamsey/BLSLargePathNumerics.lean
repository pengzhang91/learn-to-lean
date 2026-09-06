import LeanCo.SizeRamsey.BLSStarScheduleNumerics
import LeanCo.SizeRamsey.Numerics

/-!
# Entry arithmetic for the eventual BLS path lower bound

This file converts the strict natural edge threshold in
`IsPathSizeRamseyLowerBound` into the real-valued index-zero cap used by the
round recursion.
-/

namespace LeanCo.SizeRamsey

noncomputable section

universe u

/-- A host with fewer than the floored lower-bound scale satisfies the
real-valued initial edge cap. -/
theorem edgeCount_le_initialRoundEdgeCap_of_lt_pathLowerScale
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    {C : ℝ} {r n : ℕ} (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hedges : edgeCount G < pathLowerScale C r n) :
    (edgeCount G : ℝ) ≤ roundEdgeCap C r n 0 := by
  let x : ℝ := C * (r : ℝ) ^ 2 * Real.log (r : ℝ) * n
  have hlog : 0 ≤ Real.log (r : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hr
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hcast : (edgeCount G : ℝ) ≤
      (pathLowerScale C r n : ℕ) := by
    exact_mod_cast hedges.le
  have hfloor : ((pathLowerScale C r n : ℕ) : ℝ) ≤ x := by
    change ((⌊x⌋₊ : ℕ) : ℝ) ≤ x
    exact Nat.floor_le hx
  calc
    (edgeCount G : ℝ) ≤ (pathLowerScale C r n : ℕ) := hcast
    _ ≤ x := hfloor
    _ = roundEdgeCap C r n 0 := by
      unfold x roundEdgeCap
      norm_num

/-- The paper's admissibility hypothesis is much stronger than the path
length lower bound required by the colouring machinery. -/
theorem twelve_le_of_hundred_log_le
    {r n : ℕ} (hr : 2 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ)) :
    12 ≤ n := by
  exact (by omega : 12 ≤ 70).trans
    (seventy_le_of_hundred_log_le hr hn)

end

end LeanCo.SizeRamsey
