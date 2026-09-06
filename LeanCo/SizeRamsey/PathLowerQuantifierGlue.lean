import LeanCo.SizeRamsey.SmallColorPathLower

/-!
# Closing the colour-count quantifiers in the BLS path lower bound

An eventual large-colour theorem does not by itself prove the paper-facing
statement, whose quantifier starts at two colours.  This file combines such
an eventual result with `SmallColorPathLower`, using the minimum of the two
positive constants and the downward closure of a size--Ramsey lower bound in
its edge threshold.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

noncomputable section

universe u v

variable {K : Type u} {W : Type v}

/-- The integer lower-bound scale is monotone in its real constant.  The
nonnegativity hypothesis records the regime in which the scale is used; the
monotonicity itself only needs the nonnegative natural/logarithmic factor. -/
theorem pathLowerScale_mono_constant {c C : ℝ}
    (_hc0 : 0 ≤ c) (hcC : c ≤ C) (r n : ℕ) :
    pathLowerScale c r n ≤ pathLowerScale C r n := by
  unfold pathLowerScale
  apply Nat.floor_mono
  have hlog : 0 ≤ Real.log (r : ℝ) := by
    by_cases hr : r = 0
    · simp [hr]
    · exact Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr))
  have hfactor : 0 ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * n := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcC hfactor
  convert hmul using 1 <;> ring

/-- A size--Ramsey lower bound remains true after decreasing its numerical
edge threshold. -/
theorem isSizeRamseyLowerBound_of_le
    {H : SimpleGraph W} {m M : ℕ} (hm : m ≤ M)
    (hM : IsSizeRamseyLowerBound K H M) :
    IsSizeRamseyLowerBound K H m := by
  intro N G hG
  exact hM N G (hG.trans_le hm)

/-- Path-specific form of threshold downward closure. -/
theorem isPathSizeRamseyLowerBound_of_le
    {r n m M : ℕ} (hm : m ≤ M)
    (hM : IsPathSizeRamseyLowerBound r n M) :
    IsPathSizeRamseyLowerBound r n m :=
  isSizeRamseyLowerBound_of_le hm hM

/-- Glue an eventual large-colour result to the elementary bounded-colour
result.  The split is exhaustive even when `R < 2`: in the large branch,
`2 ≤ r` and `R ≤ r` combine to exactly `max 2 R ≤ r`. -/
theorem BLSPathLowerBoundV1_of_large
    {C : ℝ} {R : ℕ} (hC : 0 < C)
    (hlarge : ∀ r n : ℕ, max 2 R ≤ r →
      100 * Real.log (r : ℝ) ≤ (n : ℝ) →
      IsPathSizeRamseyLowerBound r n (pathLowerScale C r n)) :
    BLSPathLowerBoundV1 := by
  obtain ⟨cSmall, hcSmall, hsmall⟩ :=
    exists_boundedColor_pathSizeRamseyLowerBound R
  let c : ℝ := min cSmall C
  have hc : 0 < c := by
    exact lt_min hcSmall hC
  refine ⟨c, hc, ?_⟩
  intro r n hr hn
  by_cases hrR : r ≤ R
  · have hbase := hsmall r n hr hrR
    have hscale : pathLowerScale c r n ≤
        pathLowerScale cSmall r n := by
      exact pathLowerScale_mono_constant hc.le
        (by exact min_le_left cSmall C) r n
    exact isPathSizeRamseyLowerBound_of_le hscale hbase
  · have hRr : R ≤ r := by omega
    have hbase := hlarge r n (max_le hr hRr) hn
    have hscale : pathLowerScale c r n ≤ pathLowerScale C r n := by
      exact pathLowerScale_mono_constant hc.le
        (by exact min_le_right cSmall C) r n
    exact isPathSizeRamseyLowerBound_of_le hscale hbase

/-- Existentially packaged version, convenient when the eventual theorem
already supplies both its constant and its colour threshold. -/
theorem BLSPathLowerBoundV1_of_exists_large
    (hlarge : ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ,
      ∀ r n : ℕ, max 2 R ≤ r →
        100 * Real.log (r : ℝ) ≤ (n : ℝ) →
        IsPathSizeRamseyLowerBound r n (pathLowerScale C r n)) :
    BLSPathLowerBoundV1 := by
  obtain ⟨C, hC, R, hlarge⟩ := hlarge
  exact BLSPathLowerBoundV1_of_large hC hlarge

end

end LeanCo.SizeRamsey
