import LeanCo.SizeRamsey.KeyLemmaRoundExtractor
import LeanCo.SizeRamsey.PathLowerConditionalRound

/-!
# Instantiating a conditional round with the BLS Key Lemma

This module verifies that every extraction residual satisfying the two
terminal lower bounds also satisfies all four structural hypotheses of
`BLSRoundAdmissible`.  Vertex count, edge upper bound, and maximum-degree
upper bound are inherited from the initial graph; the other two hypotheses
are precisely the edge-mass and low-degree stopping tests.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- The degree-side condition under which Key-Lemma extraction continues. -/
def BLSLargeDegree [Fintype V] (r : ℕ) (G : SimpleGraph V) : Prop := by
  letI : DecidableRel G.Adj := Classical.decRel _
  exact (r : ℝ) ≤ 7 * (G.maxDegree : ℝ)

/-- Large degree is inherited when edges are added. -/
theorem BLSLargeDegree_mono [Fintype V] {r : ℕ}
    {A B : SimpleGraph V} (hAB : A ≤ B)
    (hA : BLSLargeDegree r A) : BLSLargeDegree r B := by
  letI : DecidableRel A.Adj := Classical.decRel _
  letI : DecidableRel B.Adj := Classical.decRel _
  change (r : ℝ) ≤ 7 * (A.maxDegree : ℝ) at hA
  change (r : ℝ) ≤ 7 * (B.maxDegree : ℝ)
  have hmaxNat : A.maxDegree ≤ B.maxDegree :=
    SimpleGraph.maxDegree_mono hAB
  have hmax : (A.maxDegree : ℝ) ≤ B.maxDegree := by
    exact_mod_cast hmaxNat
  linarith

/-- Failure of the continuation test gives the natural degree cap used by
the terminal edge colouring. -/
theorem maxDegree_le_div_seven_of_not_BLSLargeDegree
    [Fintype V] (G : SimpleGraph V) (r : ℕ)
    (h : ¬ BLSLargeDegree r G) :
    @SimpleGraph.maxDegree V G inferInstance (Classical.decRel _) ≤ r / 7 := by
  letI : DecidableRel G.Adj := Classical.decRel _
  change ¬ (r : ℝ) ≤ 7 * (G.maxDegree : ℝ) at h
  have hltReal : 7 * (G.maxDegree : ℝ) < r := lt_of_not_ge h
  have hltNat : 7 * G.maxDegree < r := by
    exact_mod_cast hltReal
  omega

/-- Fraction of the current edge mass removed by one Key-Lemma extraction. -/
def blsExtractionRate (r : ℕ) (β : ℝ) : ℝ :=
  60 / (Real.rpow β (9 / 10 : ℝ) * r)

theorem blsExtractionRate_nonneg {r : ℕ} {β : ℝ} (hβ : 0 < β) :
    0 ≤ blsExtractionRate r β := by
  unfold blsExtractionRate
  exact div_nonneg (by norm_num)
    (mul_nonneg (Real.rpow_nonneg hβ.le _) (Nat.cast_nonneg _))

/-- A total extractor carrying the Key-Lemma guarantee yields one complete
conditional round. -/
theorem exists_BLSConditionalRound
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ Q, pick Q ≤ Q)
    {r n s T : ℕ} {β roundThreshold : ℝ}
    (hs : 0 < s) (hn : 12 ≤ n) (hβ : 0 < β)
    (hfree : ∀ Q, (pathGraph n).Free (pick Q))
    (hpick : ∀ R,
      @BLSRoundAdmissible V inferInstance R (Classical.decRel _) r n β →
        BLSRoundGain r β R (pick R))
    (hvertex : (Fintype.card V : ℝ) ≤
      (r * Real.log (r : ℝ) * n) / 4)
    (hedgeUpper : (edgeCount G : ℝ) ≤
      (r : ℝ) ^ 2 * Real.log (r : ℝ) * n)
    (hmaxUpper : (G.maxDegree : ℝ) ≤
      β * r * Real.log (r : ℝ))
    (hrateOne : blsExtractionRate r β ≤ 1)
    (hkeyThreshold : Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
      roundThreshold)
    (hpower : (1 - blsExtractionRate r β) ^ T *
        (edgeCount G : ℝ) ≤ roundThreshold) :
    let F := freeExtractionResidual G pick T
    ((edgeCount F : ℝ) ≤ roundThreshold ∧
      ∃ H R : SimpleGraph V,
        H ≤ F ∧ R ≤ F ∧ R ≤ G ∧ F = H ⊔ R ∧
        (∀ v, Nat.card (R.neighborSet v) ≤
          8 * edgeCount F / (n * s)) ∧
        ∃ C : (G \ R).EdgeLabeling (Fin (T + s)),
          AvoidsMonochromaticCopy (pathGraph n) C) ∨
    (¬ BLSLargeDegree r F ∧
      ∃ C : (G \ F).EdgeLabeling (Fin T),
        AvoidsMonochromaticCopy (pathGraph n) C) := by
  apply exists_pathLowerConditionalRound
    G pick hsub (BLSLargeDegree r) (fun h ↦ BLSLargeDegree_mono h)
      hs hn hfree (blsExtractionRate_nonneg hβ) hrateOne
  · intro t hlarge hedge
    let R := freeExtractionResidual G pick t
    letI : DecidableRel R.Adj := Classical.decRel _
    have hRG : R ≤ G := freeExtractionResidual_le G pick t
    have hedgeUpperNat : edgeCount R ≤ edgeCount G := edgeCount_mono hRG
    have hedgeUpperR : (edgeCount R : ℝ) ≤
        (r : ℝ) ^ 2 * Real.log (r : ℝ) * n := by
      have : (edgeCount R : ℝ) ≤ edgeCount G := by
        exact_mod_cast hedgeUpperNat
      exact this.trans hedgeUpper
    have hmaxNat : R.maxDegree ≤ G.maxDegree :=
      SimpleGraph.maxDegree_mono hRG
    have hmaxR : (R.maxDegree : ℝ) ≤
        β * r * Real.log (r : ℝ) := by
      have : (R.maxDegree : ℝ) ≤ G.maxDegree := by
        exact_mod_cast hmaxNat
      exact this.trans hmaxUpper
    have hadmissible : BLSRoundAdmissible R r n β := by
      refine ⟨hvertex, ?_, hedgeUpperR, ?_, hmaxR⟩
      · exact hkeyThreshold.trans (by simpa only [R] using hedge.le)
      · change (r : ℝ) ≤
          7 * ((freeExtractionResidual G pick t).maxDegree : ℝ) at hlarge
        simpa only [R] using hlarge
    have h := hpick R hadmissible
    have hRgain : blsExtractionRate r β * (edgeCount R : ℝ) ≤
        (edgeCount (pick R) : ℝ) := by
      calc
        blsExtractionRate r β * (edgeCount R : ℝ) =
            60 * edgeCount R /
              (Real.rpow β (9 / 10 : ℝ) * r) := by
                unfold blsExtractionRate
                ring
        _ ≤ (edgeCount (pick R) : ℝ) := by
          simpa only [BLSRoundGain] using h
    simpa only [R, freeExtractionPiece] using hRgain
  · exact hpower

end

end LeanCo.SizeRamsey
