import LeanCo.SizeRamsey.KeyLemmaAssembly

/-!
# Bridge from the generic assembly to the literal BLS Key Lemma

This file fixes one global dense-layer constant `β₀`, independent of every
graph and of `D`, `r`, and `n`, and connects `KeyLemmaAssembly` to the exact
definitions `BLSKeyLemmaAt` and `BLSKeyLemmaV1`.

The sole conditional input is the eventual validity of the two explicitly
named balls-and-bins weight interfaces.  All graph-theoretic degree facts and
all positivity/floor side conditions are derived here from the hypotheses of
`BLSKeyLemmaAt`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-! ## A single global dense constant -/

/-- A fixed witness supplied once and for all by `KeyLemmaNumerics`. -/
noncomputable def keyLemmaGlobalBeta0 : ℝ :=
  Classical.choose exists_keyLemmaDense_beta0

theorem keyLemmaGlobalBeta0_spec :
    keyLemmaGlobalBeta0 ∈ Set.Ioc (0 : ℝ) 1 ∧
      ∀ β : ℝ, 0 < β → β ≤ keyLemmaGlobalBeta0 →
        ∀ j : ℕ, 1 ≤ j →
          Real.exp (j : ℝ) * (1 / β) ^ (1 / 10 : ℝ) ≥
            2 * Real.exp 2 * 360 * 60 *
              (4 * (j : ℝ) + Real.log (5 / β ^ 2)) := by
  exact Classical.choose_spec exists_keyLemmaDense_beta0

theorem keyLemmaGlobalBeta0_mem :
    keyLemmaGlobalBeta0 ∈ Set.Ioc (0 : ℝ) 1 :=
  keyLemmaGlobalBeta0_spec.1

theorem keyLemmaGlobalBeta0_denseNumerical {β : ℝ}
    (hβ : 0 < β) (hβ₀ : β ≤ keyLemmaGlobalBeta0)
    (j : ℕ) (hj : 1 ≤ j) :
    keyLemmaDenseDenominator β j ≤ keyLemmaDenseNumerator β j := by
  simpa only [keyLemmaDenseDenominator, keyLemmaDenseNumerator,
    keyLemmaDenseConstant] using
      keyLemmaGlobalBeta0_spec.2 β hβ hβ₀ j hj

/-! ## The sole remaining conditional interface -/

/-- At one legal instance of the literal Key Lemma, the two remaining
analytic weight estimates hold.  Its premises are exactly those of
`BLSKeyLemmaAt`; its conclusion contains only the two named weight bounds. -/
def BLSKeyLemmaWeightInterfacesAt [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r n : ℕ) (β β₀ : ℝ) : Prop :=
  (7 * Real.log (r : ℝ))⁻¹ ≤ β →
  β ≤ β₀ →
  (G.maxDegree : ℝ) = β * r * Real.log (r : ℝ) →
  (Fintype.card V : ℝ) ≤ (r * Real.log (r : ℝ) * n) / 4 →
  Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤ (edgeCount G : ℝ) →
  (edgeCount G : ℝ) ≤ (r : ℝ) ^ 2 * Real.log (r : ℝ) * n →
  KeyLemmaDenseRawWeightBound G G.maxDegree r n β
      (keyLemmaAssemblyTarget G r β) ∧
    KeyLemmaResidualWeightBound G r n
      (keyLemmaAssemblyTarget G r β)

/-- Eventual, graph-uniform closure of the two weight interfaces.  This is
the only hypothesis of the bridge theorem below. -/
def BLSKeyLemmaWeightInterfacesEventually (β₀ : ℝ) : Prop :=
  ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
    ∀ n : ℕ, 100 * Real.log (r : ℝ) ≤ (n : ℝ) →
      ∀ N : ℕ, ∀ G : SimpleGraph (Fin N), ∀ β : ℝ,
        @BLSKeyLemmaWeightInterfacesAt (Fin N) inferInstance G
          (Classical.decRel _) r n β β₀

end


end LeanCo.SizeRamsey

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

/-! ## The bridge theorem -/

/-- Once the two weight interfaces are eventually valid, the literal v1 Key
Lemma follows.  No positivity, maximum-degree, or floor hypothesis is added:
each is derived below from the original `BLSKeyLemmaAt` assumptions. -/
theorem BLSKeyLemmaV1_of_weightInterfaces
    (hweights :
      BLSKeyLemmaWeightInterfacesEventually keyLemmaGlobalBeta0) :
    BLSKeyLemmaV1 := by
  obtain ⟨rWeight, hweights⟩ := hweights
  refine ⟨keyLemmaGlobalBeta0, keyLemmaGlobalBeta0_mem,
    max rWeight 21, ?_⟩
  intro r hrLarge n hn N G β
  letI : DecidableRel G.Adj := Classical.decRel _
  unfold BLSKeyLemmaAt
  intro hβLower hβUpper hmaxDegree hcard hedgeLower hedgeUpper
  have hrWeight : rWeight ≤ r := (le_max_left rWeight 21).trans hrLarge
  have hr : 21 ≤ r := (le_max_right rWeight 21).trans hrLarge
  have hrPos : 0 < r := by omega
  have hrReal : 0 < (r : ℝ) := by exact_mod_cast hrPos
  have hlogPos : 0 < Real.log (r : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < r by omega))
  have hβPos : 0 < β := by
    have hinvPos : 0 < (7 * Real.log (r : ℝ))⁻¹ := by
      exact inv_pos.mpr (mul_pos (by norm_num) hlogPos)
    exact hinvPos.trans_le hβLower
  have hβOne : β ≤ 1 := hβUpper.trans keyLemmaGlobalBeta0_mem.2
  have hDRealPos : 0 < (G.maxDegree : ℝ) := by
    rw [hmaxDegree]
    positivity
  have hD : 0 < G.maxDegree := by
    exact_mod_cast hDRealPos
  have hdegree : ∀ v, G.degree v ≤ G.maxDegree := by
    exact fun v ↦ G.degree_le_maxDegree v
  have hrlogNonneg :
      0 ≤ (r : ℝ) * Real.log (r : ℝ) :=
    mul_nonneg hrReal.le hlogPos.le
  have hDRealLe :
      (G.maxDegree : ℝ) ≤ (r : ℝ) * Real.log (r : ℝ) := by
    calc
      (G.maxDegree : ℝ) = β * r * Real.log (r : ℝ) := hmaxDegree
      _ = β * ((r : ℝ) * Real.log (r : ℝ)) := by ring
      _ ≤ 1 * ((r : ℝ) * Real.log (r : ℝ)) :=
        mul_le_mul_of_nonneg_right hβOne hrlogNonneg
      _ = (r : ℝ) * Real.log (r : ℝ) := one_mul _
  have hDfloor :
      G.maxDegree ≤ ⌊(r : ℝ) * Real.log (r : ℝ)⌋₊ :=
    Nat.le_floor hDRealLe
  have hweightAt := hweights r hrWeight n hn N G β
  obtain ⟨hDenseWeight, hResidualWeight⟩ :=
    hweightAt hβLower hβUpper hmaxDegree hcard hedgeLower hedgeUpper
  have htarget : 0 ≤ keyLemmaAssemblyTarget G r β :=
    keyLemmaAssemblyTarget_nonneg G r hβPos hrPos
  obtain ⟨H, hHG, hfree, htargetH⟩ :=
    keyLemmaAssembly_of_denseRaw G hr hn hD hdegree hcard hDfloor
      hβPos hβOne htarget
      (fun j hj ↦ keyLemmaGlobalBeta0_denseNumerical
        hβPos hβUpper j hj)
      hDenseWeight hResidualWeight
  refine ⟨H, hHG, hfree, ?_⟩
  simpa only [keyLemmaAssemblyTarget] using htargetH

end

end LeanCo.SizeRamsey
