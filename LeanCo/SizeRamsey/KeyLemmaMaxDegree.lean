import LeanCo.SizeRamsey.PathLowerBound

/-!
# Applying the Key Lemma under a maximum-degree upper bound

The printed Key Lemma is stated with the equality
`Delta(G) = beta * r * log r`.  During a colouring round, edge deletion only
preserves an upper bound by the round parameter.  The paper notes this as a
technical issue.  Here it is discharged explicitly: use the residual's own
normalised maximum degree `gamma`, apply the literal equality-form lemma at
`gamma`, and use monotonicity of `x ^ 0.9` to recover the (weaker) gain at the
round parameter `beta`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- Equality-form BLS Key Lemma upgraded to the upper-bound form actually
needed after deleting earlier colour classes in a round. -/
theorem exists_pathFree_of_BLSKeyLemma_maxDegree_le
    [Fintype V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    {r n : ℕ} {β β₀ : ℝ}
    (hr : 21 ≤ r)
    (hββ₀ : β ≤ β₀)
    (hmaxLower : (r : ℝ) ≤ 7 * (R.maxDegree : ℝ))
    (hmaxUpper : (R.maxDegree : ℝ) ≤
      β * r * Real.log (r : ℝ))
    (hcard : (Fintype.card V : ℝ) ≤
      (r * Real.log (r : ℝ) * n) / 4)
    (hedgeLower : Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
      (edgeCount R : ℝ))
    (hedgeUpper : (edgeCount R : ℝ) ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * n)
    (hkey : ∀ γ : ℝ, BLSKeyLemmaAt R r n γ β₀) :
    ∃ H : SimpleGraph V,
      H ≤ R ∧ (pathGraph n).Free H ∧
        60 * edgeCount R /
            (Real.rpow β (9 / 10 : ℝ) * r) ≤ (edgeCount H : ℝ) := by
  have hrReal : (0 : ℝ) < r := by positivity
  have hlogOne : (1 : ℝ) < Real.log (r : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hrReal).mpr
    exact Real.exp_one_lt_three.trans_le
      (by exact_mod_cast (show 3 ≤ r by omega))
  have hlog : 0 < Real.log (r : ℝ) := lt_trans zero_lt_one hlogOne
  have hrlog : 0 < (r : ℝ) * Real.log (r : ℝ) := mul_pos hrReal hlog
  let γ : ℝ := (R.maxDegree : ℝ) /
    ((r : ℝ) * Real.log (r : ℝ))
  have hmaxPos : 0 < (R.maxDegree : ℝ) := by
    nlinarith
  have hγ : 0 < γ := by
    exact div_pos hmaxPos hrlog
  have hγβ : γ ≤ β := by
    dsimp only [γ]
    rw [div_le_iff₀ hrlog]
    simpa only [Nat.cast_ofNat, Nat.cast_mul, mul_assoc] using hmaxUpper
  have hγβ₀ : γ ≤ β₀ := hγβ.trans hββ₀
  have hγLower : (7 * Real.log (r : ℝ))⁻¹ ≤ γ := by
    dsimp only [γ]
    rw [le_div_iff₀ hrlog]
    have hcancel :
        (7 * Real.log (r : ℝ))⁻¹ *
            ((r : ℝ) * Real.log (r : ℝ)) = (r : ℝ) / 7 := by
      field_simp
    rw [hcancel]
    nlinarith
  have hγEquality : (R.maxDegree : ℝ) =
      γ * r * Real.log (r : ℝ) := by
    dsimp only [γ]
    field_simp
  obtain ⟨H, hHle, hHfree, hHgain⟩ :=
    hkey γ hγLower hγβ₀ hγEquality hcard hedgeLower hedgeUpper
  have hexponent : (0 : ℝ) ≤ 9 / 10 := by norm_num
  have hrpow : Real.rpow γ (9 / 10 : ℝ) ≤
      Real.rpow β (9 / 10 : ℝ) := by
    exact Real.rpow_le_rpow hγ.le hγβ hexponent
  have hdenom :
      Real.rpow γ (9 / 10 : ℝ) * (r : ℝ) ≤
        Real.rpow β (9 / 10 : ℝ) * (r : ℝ) :=
    mul_le_mul_of_nonneg_right hrpow hrReal.le
  have hdenomGamma : 0 <
      Real.rpow γ (9 / 10 : ℝ) * (r : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hγ _) hrReal
  have hnumerator : 0 ≤ 60 * (edgeCount R : ℝ) := by positivity
  have htarget :
      60 * (edgeCount R : ℝ) /
          (Real.rpow β (9 / 10 : ℝ) * (r : ℝ)) ≤
        60 * (edgeCount R : ℝ) /
          (Real.rpow γ (9 / 10 : ℝ) * (r : ℝ)) := by
    exact div_le_div_of_nonneg_left hnumerator hdenomGamma hdenom
  exact ⟨H, hHle, hHfree, htarget.trans hHgain⟩

end

end LeanCo.SizeRamsey
