import LeanCo.SizeRamsey.BLSRoundRecursion
import LeanCo.SizeRamsey.BLSStarScheduleNumerics
import LeanCo.SizeRamsey.BLSEdgeScheduleNumerics
import LeanCo.SizeRamsey.BLSTerminalNumerics

/-!
# Instantiating the BLS recursion with the explicit schedules

All per-round analytic and integer-arithmetic obligations are discharged
here.  The remaining inputs are the Key-Lemma extractor family, the two
eventual estimates, and an index-zero invariant.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

/-- The finite BLS recursion with the concrete beta, edge-cap, round-budget,
and terminal schedules. -/
theorem exists_scheduled_BLSRoundRecursionColoring
    {β₀ C : ℝ} {r n N : ℕ}
    (hβ₀ : 0 < β₀) (hβ₀One : β₀ ≤ 1)
    (hC : 0 < C) (hCOne : C ≤ 1) (hCβ : 100 * C ≤ β₀)
    (hr : 50000 ^ 4 ≤ r) (hn : 12 ≤ n)
    (hterminal :
      roundEdgeCap C r n (roundHorizon r) <
        10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n))
    (hrate : ∀ i, i < roundHorizon r →
      blsExtractionRate r (roundBeta β₀ i) ≤ 1)
    (hextractor : ∀ β : ℝ, β ≤ β₀ →
      ∃ pick : SimpleGraph (Fin N) → SimpleGraph (Fin N),
        (∀ Q, pick Q ≤ Q) ∧
        (∀ Q, (pathGraph n).Free (pick Q)) ∧
        (∀ Q,
          @BLSRoundAdmissible (Fin N) inferInstance Q
              (Classical.decRel _) r n β →
            BLSRoundGain r β Q (pick Q)))
    (G : SimpleGraph (Fin N))
    (hInv : BLSIterationInvariant r n (roundBeta β₀)
      (roundEdgeCap C r n) 0 G) :
    ∃ D : G.EdgeLabeling
        (Fin (iteratedRoundBudget
          (fun i ↦ 2 * wideRoundHalfBudget r i) 0 (roundHorizon r) +
            blsTerminalPalette r)),
      AvoidsMonochromaticCopy (pathGraph n) D := by
  have hrHundred : 100 ≤ r := by omega
  have hrSixtyFour : 64 ≤ r := by omega
  have hrOneSixtyEight : 168 ≤ r := by omega
  have hterminalStarPos : 0 < blsTerminalStarBudget r :=
    blsTerminalStarBudget_pos (by omega)
  have hterminalBudget :
      blsTerminalStarBudget r +
          (2 * blsTerminalDegreeCap r + 1) ≤
        blsTerminalPalette r :=
    blsTerminal_cleanup_budget_le_palette hr
  have hC0 : 0 ≤ C := hC.le
  have hCβ' : 100 * C ≤ β₀ := hCβ
  apply exists_BLSRoundRecursionColoring
    r n (roundHorizon r) (blsTerminalStarBudget r)
      (blsTerminalDegreeCap r) (blsTerminalPalette r)
      (roundBeta β₀) (roundEdgeCap C r n)
      (wideRoundHalfBudget r) hn hterminalStarPos
  · intro m hm
    exact blsTerminal_quotient_le_degreeCap hrSixtyFour (by omega) hm
  · exact hterminalBudget
  · exact hterminal
  · intro i hi
    unfold wideRoundHalfBudget
    have hpow := two_pow_round_add_four_le_of_hundred_le hrHundred hi
    have hden : 2 ^ (i + 3) ≤ r := by
      have hmono : 2 ^ (i + 3) ≤ 2 ^ (i + 4) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact hmono.trans hpow
    exact Nat.div_pos hden (pow_pos (by omega) _)
  · intro i hi
    exact roundBeta_pos hβ₀ i
  · intro i hi
    exact roundEdgeCap_le_global hC0 hCOne r n i
  · intro i hi
    exact hextractor (roundBeta β₀ i) (roundBeta_le hβ₀.le i)
  · exact hrate
  · intro i hi
    exact wideRound_contraction_le_one_tenth hβ₀ hβ₀One
      (two_pow_round_add_four_le_of_hundred_le hrHundred hi)
      (hrate i hi)
  · intro i hi
    exact (roundEdgeCap_div_ten C r n i).le
  · intro i hi m hm
    exact star_quotient_le_roundBeta_succ hC hCβ'
      (two_pow_round_add_four_le_of_hundred_le hrHundred hi) hn hm
  · intro i hi
    exact wideRound_lowDegree_budget_le_terminalPalette hrOneSixtyEight
  · exact hInv

end

end LeanCo.SizeRamsey
