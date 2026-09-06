import LeanCo.SizeRamsey.Numerics
import LeanCo.SizeRamsey.ParityInterval
import LeanCo.SizeRamsey.GraphBasics

/-!
# Final arithmetic bridge for the even-cycle upper bound

The graph-theoretic part of the argument produces all cycle lengths
`2 * r + s` for even offsets `s` in a prescribed interval.  This file uses
the BFS-depth estimate and the host vertex bound to show that the target
offset `n - 2 * r` lies in that interval.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

universe u

/-- The abstract final step in the upper-bound argument.  The hypotheses on
`i` and `q` are the integer BFS-depth data; `cycleLength` is the long even
cycle furnishing the interval of available even offsets. -/
theorem containsCycleLength_target_of_even_interval
    {V : Type u} [Fintype V] (H : SimpleGraph V)
    {k n q i r cycleLength : ℕ}
    (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : ℝ) ≤ n)
    (hnEven : Even n)
    (hcard : Fintype.card V ≤ 2 * hostPartSize k n)
    (hi : 1 ≤ i)
    (hiq : i < q)
    (hqDepth : (q : ℝ) < 1 + Real.logb 2 (Fintype.card V))
    (hr : 1 ≤ r)
    (hri : r ≤ i)
    (hcycleEven : Even cycleLength)
    (hcycleLong : n + 2 ≤ cycleLength)
    (hfamily : ∀ s : ℕ, Even s → 2 ≤ s → s ≤ cycleLength - 2 →
      ContainsCycleLength H (2 * r + s)) :
    ContainsCycleLength H n := by
  have hqTwo : 2 ≤ q := by omega
  have hcardPos : 0 < Fintype.card V := by
    by_contra hnot
    have hzero : Fintype.card V = 0 := Nat.eq_zero_of_not_pos hnot
    have hqLtOne : (q : ℝ) < 1 := by
      simpa only [hzero, Nat.cast_zero, Real.logb_zero, add_zero] using hqDepth
    have hqTwoR : (2 : ℝ) ≤ q := by exact_mod_cast hqTwo
    linarith
  have hcardR : (Fintype.card V : ℝ) ≤
      (2 * hostPartSize k n : ℕ) := by
    exact_mod_cast hcard
  have hlogbMono :
      Real.logb 2 (Fintype.card V) ≤
        Real.logb 2 (2 * hostPartSize k n : ℕ) := by
    exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hcardPos) hcardR
  have hhostArgument :
      ((2 * hostPartSize k n : ℕ) : ℝ) =
        2 * 10 ^ 5 * (k : ℝ) * n := by
    simp only [hostPartSize, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hbfs :
      4 + 2 * Real.logb 2 (2 * hostPartSize k n : ℕ) < n := by
    rw [hhostArgument]
    exact bfs_depth_numerical_bound hk hn
  have hrLowerStrict : 2 * r + 2 < n := by
    have hriq : 2 * r + 2 ≤ 2 * q := by omega
    have hriqR : (2 * r + 2 : ℕ) ≤ (2 * q : ℕ) := hriq
    have hriqR' : (2 * r + 2 : ℝ) ≤ 2 * (q : ℝ) := by
      exact_mod_cast hriqR
    have hqUpper : 2 * (q : ℝ) <
        2 + 2 * Real.logb 2 (Fintype.card V) := by
      nlinarith
    have htargetR : (2 * r + 2 : ℝ) < n := by
      nlinarith
    exact_mod_cast htargetR
  have hupperStrict : n < 2 * r + cycleLength := by omega
  obtain ⟨s, hsEven, hsTwo, hsUpper, hnEq⟩ :=
    exists_even_cycle_offset_of_strict hnEven hcycleEven
      hrLowerStrict hupperStrict
  rw [hnEq]
  exact hfamily s hsEven hsTwo hsUpper

end LeanCo.SizeRamsey
