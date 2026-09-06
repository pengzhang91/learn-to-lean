import LeanCo.SizeRamsey.KeyLemmaWeightClosure

/-!
# Final closure of the BLS Key-Lemma weight interfaces

This module packages the fixed-parameter dense estimate, discharges its two
eventual growth conditions, combines it with the already closed residual
branch, and feeds the resulting unconditional interface to `KeyLemmaBridge`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Filter SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-! ## Fixed-parameter dense closure -/

/-- Public fixed-parameter form of the dense raw weight bound. -/
theorem keyLemmaDenseRawWeightBound_fixed
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D r n : ℕ} {β : ℝ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hβ : 0 < β) (hβOne : β ≤ 1)
    (hmax : (D : ℝ) = β * r * Real.log (r : ℝ))
    (hedgeLower : Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
      (edgeCount G : ℝ))
    (hedgeUpper : (edgeCount G : ℝ) ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * n)
    (hdegreeGrowth : 3 * ((r : ℝ) * Real.log (r : ℝ)) ≤
      Real.rpow (r : ℝ) (7 / 4 : ℝ))
    (hreferenceGrowth :
      16 * Real.exp 2 * Real.log (r : ℝ) ≤ (r : ℝ) ^ 2) :
    KeyLemmaDenseRawWeightBound G D r n β
      (keyLemmaAssemblyTarget G r β) := by
  exact keyLemmaDenseRawWeightBound_of_keyLemma_hypotheses G hr hn hβ hβOne
    hmax hedgeLower hedgeUpper hdegreeGrowth hreferenceGrowth

/-! ## Eventual dense and combined interfaces -/

/-- Graph-uniform eventual closure of the dense raw branch. -/
theorem exists_keyLemmaDenseRawWeightBound_eventually_final :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      ∀ n : ℕ, 100 * Real.log (r : ℝ) ≤ (n : ℝ) →
        ∀ N : ℕ, ∀ G : SimpleGraph (Fin N), ∀ β : ℝ,
          (7 * Real.log (r : ℝ))⁻¹ ≤ β →
          β ≤ keyLemmaGlobalBeta0 →
          ((@SimpleGraph.maxDegree (Fin N) G inferInstance
              (Classical.decRel _)) : ℝ) =
            β * r * Real.log (r : ℝ) →
          Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
            (edgeCount G : ℝ) →
          (edgeCount G : ℝ) ≤
            (r : ℝ) ^ 2 * Real.log (r : ℝ) * n →
          KeyLemmaDenseRawWeightBound G
            (@SimpleGraph.maxDegree (Fin N) G inferInstance
              (Classical.decRel _)) r n β
            (keyLemmaAssemblyTarget G r β) :=
  exists_keyLemmaDenseRawWeightBound_eventually

/-- The two weight branches satisfy the sole eventual interface required by
`KeyLemmaBridge`. -/
theorem keyLemmaWeightInterfacesEventually_closed :
    BLSKeyLemmaWeightInterfacesEventually keyLemmaGlobalBeta0 := by
  obtain ⟨rDense, hDense⟩ :=
    exists_keyLemmaDenseRawWeightBound_eventually_final
  obtain ⟨rResidual, hResidual⟩ :=
    exists_keyLemmaResidualWeightBound_eventually
  refine ⟨max rDense rResidual, ?_⟩
  intro r hrLarge n hn N G β
  letI : DecidableRel G.Adj := Classical.decRel _
  unfold BLSKeyLemmaWeightInterfacesAt
  intro hβLower hβUpper hmax hcard hedgeLower hedgeUpper
  have hrDense : rDense ≤ r := (le_max_left _ _).trans hrLarge
  have hrResidual : rResidual ≤ r := (le_max_right _ _).trans hrLarge
  constructor
  · exact hDense r hrDense n hn N G β hβLower hβUpper hmax
      hedgeLower hedgeUpper
  · have hcard' : (N : ℝ) ≤
        ((r : ℝ) * Real.log (r : ℝ) * n) / 4 := by
      simpa using hcard
    exact hResidual r hrResidual n hn N G β hβLower hβUpper hmax
      hcard' hedgeLower

/-- Unconditional closure of the literal BLS v1 Key Lemma. -/
theorem BLSKeyLemmaV1_closed : BLSKeyLemmaV1 :=
  BLSKeyLemmaV1_of_weightInterfaces keyLemmaWeightInterfacesEventually_closed

end

end LeanCo.SizeRamsey
