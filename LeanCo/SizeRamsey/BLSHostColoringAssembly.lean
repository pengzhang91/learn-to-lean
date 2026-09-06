import LeanCo.SizeRamsey.BLSInitialInvariant
import LeanCo.SizeRamsey.BLSFiniteRelabel
import LeanCo.SizeRamsey.BLSScheduledRecursion
import LeanCo.SizeRamsey.BLSBudgetAssembly
import Mathlib.Tactic

/-!
# Assembly of the finite BLS host colouring

This file joins the initial high-core cleanup, canonical finite relabelling,
scheduled recursion, and the two final palette embeddings.  Its public theorem
is the structural host-colouring conclusion needed before the paper-specific
choice of constants and Key-Lemma extractor.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

/-- Complete assembly of the BLS host colouring.  The extractor input is
uniform in the finite vertex count because the initial high-core restriction
has a data-dependent vertex type before it is canonically relabelled. -/
theorem exists_BLSHostPathAvoidingColoring
    {β₀ C : ℝ} {r n M : ℕ}
    (hβ₀ : 0 < β₀) (hβ₀One : β₀ ≤ 1)
    (hC : 0 < C) (hCOne : C ≤ 1)
    (hCsmall : 10000 * C ≤ 1)
    (hCβ : 20000 * C ≤ β₀)
    (hr : 50000 ^ 4 ≤ r) (hn : 12 ≤ n)
    (hterminal :
      roundEdgeCap C r n (roundHorizon r) <
        10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n))
    (hrate : ∀ i, i < roundHorizon r →
      blsExtractionRate r (roundBeta β₀ i) ≤ 1)
    (hextractor : ∀ (N : ℕ) (β : ℝ), β ≤ β₀ →
      ∃ pick : SimpleGraph (Fin N) → SimpleGraph (Fin N),
        (∀ Q, pick Q ≤ Q) ∧
        (∀ Q, (pathGraph n).Free (pick Q)) ∧
        (∀ Q,
          @BLSRoundAdmissible (Fin N) inferInstance Q
              (Classical.decRel _) r n β →
            BLSRoundGain r β Q (pick Q)))
    (G : SimpleGraph (Fin M))
    (hedges : (edgeCount G : ℝ) ≤ roundEdgeCap C r n 0) :
    ∃ D : G.EdgeLabeling (Fin r),
      AvoidsMonochromaticCopy (pathGraph n) D := by
  letI : DecidableRel G.Adj := Classical.decRel _
  have hrInitial : 2000 ≤ r := by omega
  have hCβHundred : 100 * C ≤ β₀ := by
    nlinarith [hC.le]
  obtain ⟨R, hRcore, hRInv, Cclean, hCclean, hcard,
      hRedges, hcoreEdges⟩ :=
    exists_initialBLSInvariant G hC hCsmall hCβ hrInitial hn hedges
  letI : DecidableRel R.Adj := Classical.decRel _
  have hRInvFin :
      BLSIterationInvariant r n (roundBeta β₀) (roundEdgeCap C r n) 0
        (finiteRelabel R) :=
    BLSIterationInvariant_finiteRelabel hRInv
  let k : ℕ :=
    iteratedRoundBudget (fun i ↦ 2 * wideRoundHalfBudget r i) 0
        (roundHorizon r) + blsTerminalPalette r
  obtain ⟨Dfinite, hDfinite⟩ :
      ∃ D : (finiteRelabel R).EdgeLabeling (Fin k),
        AvoidsMonochromaticCopy (pathGraph n) D := by
    dsimp only [k]
    exact exists_scheduled_BLSRoundRecursionColoring
      hβ₀ hβ₀One hC hCOne hCβHundred hr hn hterminal hrate
        (hextractor (Fintype.card
          ↥(highCoreVertexFinset G (initialDegreeThreshold r))))
        (finiteRelabel R) hRInvFin
  let Dresidual : R.EdgeLabeling (Fin k) :=
    Dfinite.pullback (finiteRelabelIso R).toHom
  have hDresidual :
      AvoidsMonochromaticCopy (pathGraph n) Dresidual := by
    exact finiteRelabel_pullback_avoids_pathGraph R Dfinite hDfinite
  obtain ⟨Dassembled, hDassembled⟩ :=
    exists_path_avoidingColoring_of_completed_initialCoreCleanup
      G (initialDegreeThreshold r) hn R hRcore Cclean hCclean
        Dresidual hDresidual
  have hinitial := initial_thresholds_pos_and_palette hrInitial
  have hk : k ≤ 11 * r / 12 := by
    dsimp only [k]
    exact iterated_wideRound_add_terminal_le_eleven_twelfths
      r (roundHorizon r)
  have htotal :
      (3 * initialDegreeThreshold r + 2) +
          (initialStarBudget r + k) ≤ r := by
    omega
  exact exists_path_avoidingColoring_fin_mono
    (by omega) htotal Dassembled hDassembled

end

end LeanCo.SizeRamsey
