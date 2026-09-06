import LeanCo.SizeRamsey.BLSRoundStep

/-!
# Finite BLS round recursion

This module iterates `exists_BLSIterationStep` for a scheduled finite horizon.
All graph theory and colour bookkeeping are closed here.  The remaining
inputs are explicit numerical inequalities for the chosen schedules and the
eventual Key-Lemma extractors.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- A graph below the global small-edge threshold is terminally colourable
once the star-cleanup quotient and palette inequalities are supplied. -/
theorem exists_BLS_smallEdge_terminalColoring
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r n terminalS terminalD terminalBudget : ℕ)
    (hn : 12 ≤ n) (hterminalS : 0 < terminalS)
    (hsmall : (edgeCount G : ℝ) <
      10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n))
    (hquotient : ∀ m : ℕ,
      (m : ℝ) < 10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n) →
        8 * m / (n * terminalS) ≤ terminalD)
    (hbudget : terminalS + (2 * terminalD + 1) ≤ terminalBudget) :
    ∃ C : G.EdgeLabeling (Fin terminalBudget),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨C, hC⟩ := exists_terminalPathColoring_after_star_cleanup
    G hterminalS hn (hquotient (edgeCount G) hsmall)
  exact exists_path_avoidingColoring_fin_mono (by omega) hbudget C hC

/-- Complete finite recursive colouring on a fixed restricted vertex type. -/
theorem exists_BLSRoundRecursionColoring
    [Fintype V] [DecidableEq V]
    (r n horizon terminalS terminalD terminalBudget : ℕ)
    (β edgeCap : ℕ → ℝ) (roundBudget : ℕ → ℕ)
    (hn : 12 ≤ n)
    (hterminalS : 0 < terminalS)
    (hterminalQuotient : ∀ m : ℕ,
      (m : ℝ) < 10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n) →
        8 * m / (n * terminalS) ≤ terminalD)
    (hterminalBudget : terminalS + (2 * terminalD + 1) ≤ terminalBudget)
    (horizonSmall : edgeCap horizon <
      10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n))
    (hroundPos : ∀ i, i < horizon → 0 < roundBudget i)
    (hβPos : ∀ i, i < horizon → 0 < β i)
    (hcapGlobal : ∀ i, i < horizon → edgeCap i ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * n)
    (hextractor : ∀ i, i < horizon →
      ∃ pick : SimpleGraph V → SimpleGraph V,
        (∀ Q, pick Q ≤ Q) ∧
        (∀ Q, (pathGraph n).Free (pick Q)) ∧
        (∀ R,
          @BLSRoundAdmissible V inferInstance R (Classical.decRel _)
              r n (β i) →
            BLSRoundGain r (β i) R (pick R)))
    (hrateOne : ∀ i, i < horizon → blsExtractionRate r (β i) ≤ 1)
    (hdecay : ∀ i, i < horizon →
      (1 - blsExtractionRate r (β i)) ^ roundBudget i ≤ (1 : ℝ) / 10)
    (hcapNext : ∀ i, i < horizon →
      edgeCap i / 10 ≤ edgeCap (i + 1))
    (hstarNext : ∀ i, i < horizon → ∀ m : ℕ,
      (m : ℝ) ≤ edgeCap i / 10 →
        ((8 * m / (n * roundBudget i) : ℕ) : ℝ) ≤
          β (i + 1) * r * Real.log (r : ℝ))
    (hlowBudget : ∀ i, i < horizon →
      roundBudget i + (2 * (r / 7) + 1) ≤ terminalBudget)
    (G : SimpleGraph V)
    (hInv : BLSIterationInvariant r n β edgeCap 0 G) :
    ∃ C : G.EdgeLabeling
        (Fin (iteratedRoundBudget (fun i ↦ 2 * roundBudget i) 0 horizon +
          terminalBudget)),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  let Invariant : ℕ → SimpleGraph V → Prop := fun i Q =>
    i ≤ horizon ∧ BLSIterationInvariant r n β edgeCap i Q
  have hstep : ∀ i (Q : SimpleGraph V), Invariant i Q →
      (∃ C : Q.EdgeLabeling (Fin terminalBudget),
        AvoidsMonochromaticCopy (pathGraph n) C) ∨
      ∃ R : SimpleGraph V, R ≤ Q ∧ Invariant (i + 1) R ∧
        ∃ C : (Q \ R).EdgeLabeling (Fin (2 * roundBudget i)),
          AvoidsMonochromaticCopy (pathGraph n) C := by
    intro i Q hQ
    rcases hQ with ⟨hi, hQInv⟩
    by_cases hit : i < horizon
    · obtain ⟨pick, hsub, hfree, hpick⟩ := hextractor i hit
      have hsmallTerminal :
          (edgeCount Q : ℝ) <
              10 * (Real.rpow (r : ℝ) (7 / 4 : ℝ) * n) →
            ∃ C : Q.EdgeLabeling (Fin terminalBudget),
              AvoidsMonochromaticCopy (pathGraph n) C := by
        exact fun hsmall ↦ exists_BLS_smallEdge_terminalColoring
          Q r n terminalS terminalD terminalBudget hn hterminalS hsmall
            hterminalQuotient hterminalBudget
      rcases exists_BLSIterationStep
        r n terminalBudget β edgeCap roundBudget i Q hQInv hn
          (hroundPos i hit) (hβPos i hit) (hcapGlobal i hit)
          pick hsub hfree hpick (hrateOne i hit) (hdecay i hit)
          (hcapNext i hit) (hstarNext i hit) hsmallTerminal
          (hlowBudget i hit) with hterminal | hcontinue
      · exact Or.inl hterminal
      · right
        obtain ⟨R, hRQ, hRInv, C, hC⟩ := hcontinue
        exact ⟨R, hRQ, ⟨by omega, hRInv⟩, C, hC⟩
    · have hieq : i = horizon := by omega
      left
      subst i
      change BLSIterationInvariant r n β edgeCap horizon Q at hQInv
      letI : DecidableRel Q.Adj := Classical.decRel _
      change
        (Fintype.card V : ℝ) ≤ (r * Real.log (r : ℝ) * n) / 4 ∧
        (edgeCount Q : ℝ) ≤ edgeCap horizon ∧
        (Q.maxDegree : ℝ) ≤
          β horizon * r * Real.log (r : ℝ) at hQInv
      exact exists_BLS_smallEdge_terminalColoring
        Q r n terminalS terminalD terminalBudget hn hterminalS
          (hQInv.2.1.trans_lt horizonSmall)
          hterminalQuotient hterminalBudget
  have hstart : Invariant 0 G := ⟨Nat.zero_le _, hInv⟩
  rcases exists_path_coloring_or_iterated_residual
      Invariant (fun i ↦ 2 * roundBudget i) terminalBudget
      (by omega) hstep horizon 0 G hstart with hcolored | hresidual
  · exact hcolored
  · obtain ⟨R, hRG, hRInv, Cdiff, hCdiff⟩ := hresidual
    have hindex : 0 + horizon = horizon := by omega
    rw [hindex] at hRInv
    letI : DecidableRel R.Adj := Classical.decRel _
    change
      horizon ≤ horizon ∧
      ((Fintype.card V : ℝ) ≤ (r * Real.log (r : ℝ) * n) / 4 ∧
       (edgeCount R : ℝ) ≤ edgeCap horizon ∧
       (R.maxDegree : ℝ) ≤
          β horizon * r * Real.log (r : ℝ)) at hRInv
    obtain ⟨Cterminal, hCterminal⟩ :=
      exists_BLS_smallEdge_terminalColoring
        R r n terminalS terminalD terminalBudget hn hterminalS
          (hRInv.2.2.1.trans_lt horizonSmall)
          hterminalQuotient hterminalBudget
    exact exists_path_avoidingColoring_of_split
      hRG (by omega) Cdiff hCdiff Cterminal hCterminal le_rfl

end

end LeanCo.SizeRamsey
