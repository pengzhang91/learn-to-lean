import LeanCo.SizeRamsey.BLSConditionalRound
import LeanCo.SizeRamsey.TerminalPathColoring
import LeanCo.SizeRamsey.RoundUntilTerminal

/-!
# A complete recursive BLS step

This module turns the conditional extraction round into the exact alternative
needed by the outer recursion.  A graph below the edge threshold is finished
by a supplied terminal routine.  Otherwise Key-Lemma extraction either hits
the low-degree terminal condition, or star cleanup produces the next graph
with one-tenth the edge cap and the scheduled maximum-degree cap.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- Invariant tracked between recursive rounds.  The classical adjacency
instance makes the predicate usable for graphs chosen during recursion. -/
def BLSIterationInvariant [Fintype V]
    (r n : ℕ) (β edgeCap : ℕ → ℝ)
    (i : ℕ) (G : SimpleGraph V) : Prop := by
  letI : DecidableRel G.Adj := Classical.decRel _
  exact
    (Fintype.card V : ℝ) ≤ (r * Real.log (r : ℝ) * n) / 4 ∧
    (edgeCount G : ℝ) ≤ edgeCap i ∧
    (G.maxDegree : ℝ) ≤ β i * r * Real.log (r : ℝ)

/-- One recursive step, including both terminal branches. -/
theorem exists_BLSIterationStep
    [Fintype V] [DecidableEq V]
    (r n terminalBudget : ℕ) (β edgeCap : ℕ → ℝ)
    (roundBudget : ℕ → ℕ)
    (i : ℕ) (G : SimpleGraph V)
    (hInv : BLSIterationInvariant r n β edgeCap i G)
    (hn : 12 ≤ n)
    (hroundPos : 0 < roundBudget i)
    (hβPos : 0 < β i)
    (hcapGlobal : edgeCap i ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * n)
    (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ Q, pick Q ≤ Q)
    (hfree : ∀ Q, (pathGraph n).Free (pick Q))
    (hpick : ∀ R,
      @BLSRoundAdmissible V inferInstance R (Classical.decRel _) r n (β i) →
        BLSRoundGain r (β i) R (pick R))
    (hrateOne : blsExtractionRate r (β i) ≤ 1)
    (hdecay : (1 - blsExtractionRate r (β i)) ^ roundBudget i ≤
      (1 : ℝ) / 10)
    (hcapNext : edgeCap i / 10 ≤ edgeCap (i + 1))
    (hstarNext : ∀ m : ℕ, (m : ℝ) ≤ edgeCap i / 10 →
      ((8 * m / (n * roundBudget i) : ℕ) : ℝ) ≤
        β (i + 1) * r * Real.log (r : ℝ))
    (hsmallTerminal :
      (edgeCount G : ℝ) <
          10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n) →
        ∃ C : G.EdgeLabeling (Fin terminalBudget),
          AvoidsMonochromaticCopy (pathGraph n) C)
    (hlowBudget : roundBudget i + (2 * (r / 7) + 1) ≤ terminalBudget) :
    (∃ C : G.EdgeLabeling (Fin terminalBudget),
      AvoidsMonochromaticCopy (pathGraph n) C) ∨
    ∃ R : SimpleGraph V, R ≤ G ∧
      BLSIterationInvariant r n β edgeCap (i + 1) R ∧
      ∃ C : (G \ R).EdgeLabeling (Fin (2 * roundBudget i)),
        AvoidsMonochromaticCopy (pathGraph n) C := by
  letI : DecidableRel G.Adj := Classical.decRel _
  change
    (Fintype.card V : ℝ) ≤ (r * Real.log (r : ℝ) * n) / 4 ∧
    (edgeCount G : ℝ) ≤ edgeCap i ∧
    (G.maxDegree : ℝ) ≤ β i * r * Real.log (r : ℝ) at hInv
  rcases hInv with ⟨hvertex, hedgeCap, hmax⟩
  let keyThreshold : ℝ :=
    Real.rpow (r : ℝ) (7 / 4 : ℝ) * n
  by_cases hedgeHigh : 10 * keyThreshold ≤ (edgeCount G : ℝ)
  · have hkey : keyThreshold ≤ (edgeCount G : ℝ) / 10 := by
      linarith
    have hedgeUpper : (edgeCount G : ℝ) ≤
        (r : ℝ) ^ 2 * Real.log (r : ℝ) * n :=
      hedgeCap.trans hcapGlobal
    have hpower :
        (1 - blsExtractionRate r (β i)) ^ roundBudget i *
            (edgeCount G : ℝ) ≤
          (edgeCount G : ℝ) / 10 := by
      have hedgeNonneg : 0 ≤ (edgeCount G : ℝ) := by positivity
      calc
        (1 - blsExtractionRate r (β i)) ^ roundBudget i *
              (edgeCount G : ℝ) ≤
            ((1 : ℝ) / 10) * edgeCount G :=
          mul_le_mul_of_nonneg_right hdecay hedgeNonneg
        _ = (edgeCount G : ℝ) / 10 := by ring
    have hround := exists_BLSConditionalRound
      G pick hsub hroundPos hn hβPos hfree hpick hvertex hedgeUpper hmax
        hrateOne (by simpa only [keyThreshold] using hkey) hpower
    rcases hround with hcontinue | hlow
    · right
      obtain ⟨hFsmall, H, R, hHF, hRF, hRG, hsplit,
        hRdegree, Cdiff, hCdiff⟩ := hcontinue
      letI : DecidableRel R.Adj := Classical.decRel _
      have hFcap :
          (edgeCount (freeExtractionResidual G pick (roundBudget i)) : ℝ) ≤
            edgeCap i / 10 := hFsmall.trans
        (div_le_div_of_nonneg_right hedgeCap (by norm_num))
      have hRedgeNat : edgeCount R ≤
          edgeCount (freeExtractionResidual G pick (roundBudget i)) :=
        edgeCount_mono hRF
      have hRedge : (edgeCount R : ℝ) ≤ edgeCap (i + 1) := by
        have hcast : (edgeCount R : ℝ) ≤
            edgeCount (freeExtractionResidual G pick (roundBudget i)) := by
          exact_mod_cast hRedgeNat
        exact (hcast.trans hFcap).trans hcapNext
      have hdegreeQuotient : ∀ v, R.degree v ≤
          8 * edgeCount (freeExtractionResidual G pick (roundBudget i)) /
            (n * roundBudget i) := by
        intro v
        have hv := hRdegree v
        rw [Nat.card_eq_fintype_card, R.card_neighborSet_eq_degree] at hv
        exact hv
      have hmaxNat : R.maxDegree ≤
          8 * edgeCount (freeExtractionResidual G pick (roundBudget i)) /
            (n * roundBudget i) :=
        R.maxDegree_le_of_forall_degree_le _ hdegreeQuotient
      have hmaxCast : (R.maxDegree : ℝ) ≤
          ((8 * edgeCount (freeExtractionResidual G pick (roundBudget i)) /
            (n * roundBudget i) : ℕ) : ℝ) := by
        exact_mod_cast hmaxNat
      have hnextMax : (R.maxDegree : ℝ) ≤
          β (i + 1) * r * Real.log (r : ℝ) :=
        hmaxCast.trans (hstarNext _ hFcap)
      refine ⟨R, hRG, ?_, ?_⟩
      · change
          (Fintype.card V : ℝ) ≤
              (r * Real.log (r : ℝ) * n) / 4 ∧
          (edgeCount R : ℝ) ≤ edgeCap (i + 1) ∧
          (R.maxDegree : ℝ) ≤
            β (i + 1) * r * Real.log (r : ℝ)
        exact ⟨hvertex, hRedge, hnextMax⟩
      · have hbudgetEq : roundBudget i + roundBudget i =
            2 * roundBudget i := by omega
        rw [← hbudgetEq]
        exact ⟨Cdiff, hCdiff⟩
    · left
      obtain ⟨hnotLarge, Cdiff, hCdiff⟩ := hlow
      let F := freeExtractionResidual G pick (roundBudget i)
      letI : DecidableRel F.Adj := Classical.decRel _
      have hFdegree : F.maxDegree ≤ r / 7 := by
        exact maxDegree_le_div_seven_of_not_BLSLargeDegree F r hnotLarge
      obtain ⟨Cterminal, hCterminal⟩ :=
        exists_terminalPathColoring_of_maxDegree_le
          F (r / 7) n (by omega) hFdegree
      exact exists_path_avoidingColoring_of_split
        (freeExtractionResidual_le G pick (roundBudget i)) (by omega)
        Cdiff hCdiff Cterminal hCterminal hlowBudget
  · left
    apply hsmallTerminal
    simpa only [keyThreshold] using lt_of_not_ge hedgeHigh

end

end LeanCo.SizeRamsey
