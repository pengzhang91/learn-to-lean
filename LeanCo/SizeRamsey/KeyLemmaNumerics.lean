import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Numerical constants for the BLS key lemma

This file isolates the real-analysis estimates used on pages 11--12 of the
v1 proof of the key lemma.  In particular, it chooses the small parameter
`β₀` required in the dense-layer branch; no asymptotic assertion is left as
a hypothesis of the final theorem.
-/

namespace LeanCo.SizeRamsey

open Filter Set Topology

noncomputable section

/-- The fixed multiplicative constant in the dense-layer calculation.

The printed v1 proof loses one factor of `e` when rewriting
`c₁ (c₂/c₁)^j = exp (j-2)` as a multiple of the target.  Retaining
that factor gives the valid constant `2 e² · 360 · 60`; the subsequent
small-`β₀` argument is unchanged. -/
def keyLemmaDenseConstant : ℝ :=
  2 * Real.exp 2 * 360 * 60

/-- Exponential growth with exponent `t / 10` eventually dominates the
specific affine logarithmic expression which appears after writing
`t = -log β`. -/
theorem exists_threshold_exp_tenth_dominates_linear (K : ℝ) (hK : 0 ≤ K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t : ℝ, M ≤ t →
      K * (4 + Real.log 5 + 2 * t) ≤ Real.exp (t / 10) := by
  have htenth : (0 : ℝ) < 1 / 10 := by norm_num
  have htend :
      Tendsto (fun t : ℝ => Real.exp ((1 / 10) * t) / t ^ (1 : ℝ))
        atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop 1 (1 / 10) htenth
  have hevent : ∀ᶠ t : ℝ in atTop,
      10 * K ≤ Real.exp ((1 / 10) * t) / t ^ (1 : ℝ) :=
    htend.eventually (eventually_ge_atTop (10 * K))
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hevent
  let M := max 1 M₀
  refine ⟨M, le_max_left 1 M₀, ?_⟩
  intro t hMt
  have htOne : (1 : ℝ) ≤ t := (le_max_left 1 M₀).trans hMt
  have htM₀ : M₀ ≤ t := (le_max_right 1 M₀).trans hMt
  have hquotient := hM₀ t htM₀
  simp only [Real.rpow_one] at hquotient
  have hexpLower : 10 * K * t ≤ Real.exp ((1 / 10) * t) := by
    exact (le_div_iff₀ (zero_lt_one.trans_le htOne)).mp hquotient
  have hlogFive : Real.log 5 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    norm_num at h ⊢
    exact h
  have haffine : 4 + Real.log 5 + 2 * t ≤ 10 * t := by
    linarith
  calc
    K * (4 + Real.log 5 + 2 * t) ≤ K * (10 * t) :=
      mul_le_mul_of_nonneg_left haffine hK
    _ = 10 * K * t := by ring
    _ ≤ Real.exp ((1 / 10) * t) := hexpLower
    _ = Real.exp (t / 10) := by congr 1; ring

/-- A small positive `β₀ ≤ 1` for which the negative tenth power of `β`
dominates the complete logarithmic factor in the dense-layer branch. -/
theorem exists_keyLemmaDense_beta0_core :
    ∃ β₀ : ℝ, β₀ ∈ Set.Ioc 0 1 ∧
      ∀ β : ℝ, 0 < β → β ≤ β₀ →
        keyLemmaDenseConstant * (4 + Real.log (5 / β ^ 2)) ≤
          (1 / β) ^ (1 / 10 : ℝ) := by
  have hK : 0 ≤ keyLemmaDenseConstant := by
    unfold keyLemmaDenseConstant
    positivity
  obtain ⟨M, hMOne, hM⟩ :=
    exists_threshold_exp_tenth_dominates_linear keyLemmaDenseConstant hK
  let β₀ : ℝ := Real.exp (-M)
  have hβ₀Pos : 0 < β₀ := by
    dsimp only [β₀]
    positivity
  have hβ₀One : β₀ ≤ 1 := by
    dsimp only [β₀]
    have hneg : -M ≤ (0 : ℝ) := by linarith
    simpa using Real.exp_monotone hneg
  refine ⟨β₀, ⟨hβ₀Pos, hβ₀One⟩, ?_⟩
  intro β hβPos hββ₀
  let t : ℝ := -Real.log β
  have hlogβ : Real.log β ≤ -M := by
    calc
      Real.log β ≤ Real.log β₀ := Real.log_le_log hβPos hββ₀
      _ = -M := by simp [β₀]
  have hMt : M ≤ t := by
    dsimp only [t]
    linarith
  have hlogPiece :
      Real.log (5 / β ^ 2) = Real.log 5 + 2 * t := by
    rw [Real.log_div (by norm_num) (pow_ne_zero 2 hβPos.ne'),
      Real.log_pow]
    dsimp only [t]
    norm_num
    ring
  have hpow :
      (1 / β) ^ (1 / 10 : ℝ) = Real.exp (t / 10) := by
    rw [Real.rpow_def_of_pos (div_pos zero_lt_one hβPos)]
    congr 1
    rw [Real.log_div one_ne_zero hβPos.ne', Real.log_one]
    dsimp only [t]
    ring
  calc
    keyLemmaDenseConstant * (4 + Real.log (5 / β ^ 2)) =
        keyLemmaDenseConstant * (4 + Real.log 5 + 2 * t) := by
      rw [hlogPiece]
      ring
    _ ≤ Real.exp (t / 10) := hM t hMt
    _ = (1 / β) ^ (1 / 10 : ℝ) := hpow.symm

/-- Exact quantified small-`β` choice required in the dense-layer branch of
the v1 key lemma.  The layer index is a natural number, and the conclusion
retains the paper's constants and non-strict inequality verbatim. -/
theorem exists_keyLemmaDense_beta0 :
    ∃ β₀ : ℝ, β₀ ∈ Set.Ioc 0 1 ∧
      ∀ β : ℝ, 0 < β → β ≤ β₀ →
        ∀ j : ℕ, 1 ≤ j →
          Real.exp (j : ℝ) * (1 / β) ^ (1 / 10 : ℝ) ≥
            2 * Real.exp 2 * 360 * 60 *
              (4 * (j : ℝ) + Real.log (5 / β ^ 2)) := by
  obtain ⟨β₀, hβ₀, hcore⟩ := exists_keyLemmaDense_beta0_core
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβPos hββ₀ j _hj
  have hβOne : β ≤ 1 := hββ₀.trans hβ₀.2
  have hlogNonneg : 0 ≤ Real.log (5 / β ^ 2) := by
    apply Real.log_nonneg
    have hβSq : β ^ 2 ≤ 1 := by nlinarith [sq_nonneg β]
    have hβSqPos : 0 < β ^ 2 := pow_pos hβPos _
    rw [le_div_iff₀ hβSqPos]
    nlinarith
  have hjExp : (j : ℝ) ≤ Real.exp (j : ℝ) := by
    have := Real.add_one_le_exp (j : ℝ)
    linarith
  have hExpOne : (1 : ℝ) ≤ Real.exp (j : ℝ) :=
    Real.one_le_exp (by positivity)
  have hlogScale :
      Real.log (5 / β ^ 2) ≤
        Real.exp (j : ℝ) * Real.log (5 / β ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hExpOne) hlogNonneg]
  have hbracket :
      4 * (j : ℝ) + Real.log (5 / β ^ 2) ≤
        Real.exp (j : ℝ) * (4 + Real.log (5 / β ^ 2)) := by
    nlinarith
  have hKNonneg : 0 ≤ keyLemmaDenseConstant := by
    unfold keyLemmaDenseConstant
    positivity
  have hcoreβ := hcore β hβPos hββ₀
  change keyLemmaDenseConstant *
      (4 * (j : ℝ) + Real.log (5 / β ^ 2)) ≤
        Real.exp (j : ℝ) * (1 / β) ^ (1 / 10 : ℝ)
  calc
    keyLemmaDenseConstant *
          (4 * (j : ℝ) + Real.log (5 / β ^ 2)) ≤
        keyLemmaDenseConstant *
          (Real.exp (j : ℝ) * (4 + Real.log (5 / β ^ 2))) :=
      mul_le_mul_of_nonneg_left hbracket hKNonneg
    _ = Real.exp (j : ℝ) *
        (keyLemmaDenseConstant * (4 + Real.log (5 / β ^ 2))) := by ring
    _ ≤ Real.exp (j : ℝ) * (1 / β) ^ (1 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_left hcoreβ (Real.exp_pos _).le

/-! ## The logarithmic ratio in the remainder branch -/

/-- Every positive real power dominates the logarithm strongly enough that
their quotient tends to infinity. -/
theorem tendsto_rpow_div_log_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => x ^ a / Real.log x) atTop atTop := by
  have hzero :
      Tendsto (fun x : ℝ => Real.log x / x ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have hpositive : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x ^ a := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _)
  have hright :
      Tendsto (fun x : ℝ => Real.log x / x ^ a) atTop (𝓝[>] 0) :=
    tendsto_inf.2 ⟨hzero, tendsto_principal.2 hpositive⟩
  have hinv := hright.inv_tendsto_nhdsGT_zero
  refine hinv.congr' ?_
  filter_upwards with x
  simp only [Pi.inv_apply, inv_div]

/-- The precise remainder-branch asymptotic asserted in the paper:
`(log r)^0.07 / log log r → ∞`.  The decimal exponent is represented exactly
as `7/100`. -/
theorem tendsto_keyLemmaRemainder_log_ratio :
    Tendsto
      (fun r : ℝ =>
        (Real.log r) ^ (7 / 100 : ℝ) / Real.log (Real.log r))
      atTop atTop := by
  exact (tendsto_rpow_div_log_atTop (show (0 : ℝ) < 7 / 100 by norm_num)).comp
    Real.tendsto_log_atTop

/-- Directly usable natural-number threshold extracted from the preceding
limit: the logarithmic ratio eventually exceeds any fixed real constant. -/
theorem exists_keyLemmaRemainder_nat_threshold (C : ℝ) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      C ≤ (Real.log (r : ℝ)) ^ (7 / 100 : ℝ) /
        Real.log (Real.log (r : ℝ)) := by
  have htendNat :
      Tendsto
        (fun r : ℕ =>
          (Real.log (r : ℝ)) ^ (7 / 100 : ℝ) /
            Real.log (Real.log (r : ℝ)))
        atTop atTop :=
    tendsto_keyLemmaRemainder_log_ratio.comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.1
    (htendNat.eventually (eventually_ge_atTop C))

end

end LeanCo.SizeRamsey
