import LeanCo.SizeRamsey.FreeExtractionIteration

/-!
# Conditional termination of free-subgraph extraction

The BLS Key Lemma is applicable while both an edge-mass lower bound and a
maximum-degree lower bound hold.  If the latter fails during a fixed block of
extractions, that failure is itself a valid terminal condition.  The lemmas
below make this alternative explicit instead of assuming the gain after the
process has already entered its low-degree terminal regime.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- Geometric decay when the final residual satisfies an upward-closed
admissibility predicate. -/
theorem freeExtractionResidual_edgeCount_le_pow_of_final_good
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R)
    (Good : SimpleGraph V → Prop)
    (hGoodUp : ∀ {A B : SimpleGraph V}, A ≤ B → Good A → Good B)
    {a threshold : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hgain : ∀ t, Good (freeExtractionResidual G pick t) →
      threshold < (edgeCount (freeExtractionResidual G pick t) : ℝ) →
        a * (edgeCount (freeExtractionResidual G pick t) : ℝ) ≤
          (edgeCount (freeExtractionPiece G pick t) : ℝ))
    (T : ℕ)
    (hfinalGood : Good (freeExtractionResidual G pick T))
    (hfinal : threshold <
      (edgeCount (freeExtractionResidual G pick T) : ℝ)) :
    (edgeCount (freeExtractionResidual G pick T) : ℝ) ≤
      (1 - a) ^ T * (edgeCount G : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hstepNat := freeExtractionResidual_edgeCount_step G pick hsub T
      have hstep :
          (edgeCount (freeExtractionResidual G pick T) : ℝ) =
            (edgeCount (freeExtractionPiece G pick T) : ℝ) +
              (edgeCount (freeExtractionResidual G pick (T + 1)) : ℝ) := by
        exact_mod_cast hstepNat
      have hresidualLe : freeExtractionResidual G pick (T + 1) ≤
          freeExtractionResidual G pick T :=
        freeExtractionResidual_succ_le G pick T
      have hcurrentGood : Good (freeExtractionResidual G pick T) :=
        hGoodUp hresidualLe hfinalGood
      have hmonoNat :
          edgeCount (freeExtractionResidual G pick (T + 1)) ≤
            edgeCount (freeExtractionResidual G pick T) :=
        edgeCount_mono hresidualLe
      have hmono :
          (edgeCount (freeExtractionResidual G pick (T + 1)) : ℝ) ≤
            (edgeCount (freeExtractionResidual G pick T) : ℝ) := by
        exact_mod_cast hmonoNat
      have hcurrent : threshold <
          (edgeCount (freeExtractionResidual G pick T) : ℝ) :=
        hfinal.trans_le hmono
      have hprevious := ih hcurrentGood hcurrent
      have hgainT := hgain T hcurrentGood hcurrent
      have hdecay :
          (edgeCount (freeExtractionResidual G pick (T + 1)) : ℝ) ≤
            (1 - a) *
              (edgeCount (freeExtractionResidual G pick T) : ℝ) := by
        nlinarith
      have honeMinus : 0 ≤ 1 - a := sub_nonneg.mpr ha1
      calc
        (edgeCount (freeExtractionResidual G pick (T + 1)) : ℝ) ≤
            (1 - a) *
              (edgeCount (freeExtractionResidual G pick T) : ℝ) := hdecay
        _ ≤ (1 - a) * ((1 - a) ^ T * (edgeCount G : ℝ)) :=
          mul_le_mul_of_nonneg_left hprevious honeMinus
        _ = (1 - a) ^ (T + 1) * (edgeCount G : ℝ) := by
          rw [pow_succ]
          ring

/-- After `T` steps, either the edge threshold has been reached or the
upward-closed admissibility predicate has failed. -/
theorem freeExtractionResidual_small_or_not_good
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R)
    (Good : SimpleGraph V → Prop)
    (hGoodUp : ∀ {A B : SimpleGraph V}, A ≤ B → Good A → Good B)
    {a threshold : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hgain : ∀ t, Good (freeExtractionResidual G pick t) →
      threshold < (edgeCount (freeExtractionResidual G pick t) : ℝ) →
        a * (edgeCount (freeExtractionResidual G pick t) : ℝ) ≤
          (edgeCount (freeExtractionPiece G pick t) : ℝ))
    (T : ℕ)
    (hpower : (1 - a) ^ T * (edgeCount G : ℝ) ≤ threshold) :
    (edgeCount (freeExtractionResidual G pick T) : ℝ) ≤ threshold ∨
      ¬ Good (freeExtractionResidual G pick T) := by
  by_cases hGood : Good (freeExtractionResidual G pick T)
  · left
    by_contra hnot
    have hfinal : threshold <
        (edgeCount (freeExtractionResidual G pick T) : ℝ) :=
      lt_of_not_ge hnot
    have hdecay := freeExtractionResidual_edgeCount_le_pow_of_final_good
      G pick hsub Good hGoodUp ha0 ha1 hgain T hGood hfinal
    linarith
  · exact Or.inr hGood

end

end LeanCo.SizeRamsey
