import LeanCo.SizeRamsey.KeyLemmaMaxDegree
import LeanCo.SizeRamsey.FreeExtractorChoice

/-!
# A total one-round extractor from the BLS Key Lemma

The literal Key Lemma is stated at a graph's exact normalised maximum
degree.  A colouring round, however, carries only an upper bound using the
round parameter `β`.  `KeyLemmaMaxDegree` already performs that
normalisation.  This file packages its output as a total choice function:
on an admissible residual it chooses the promised path-free subgraph, and
off the admissible region it chooses the empty graph.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- The hypotheses about a residual graph which are needed in one BLS
extraction round.  Notice that the maximum-degree condition is an interval,
not the equality occurring in the printed Key Lemma. -/
structure BLSRoundAdmissible [Fintype V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (r n : ℕ) (β : ℝ) : Prop where
  vertex_le : (Fintype.card V : ℝ) ≤
    (r * Real.log (r : ℝ) * n) / 4
  edge_lower : Real.rpow (r : ℝ) (7 / 4 : ℝ) * n ≤
    (edgeCount R : ℝ)
  edge_upper : (edgeCount R : ℝ) ≤
    (r : ℝ) ^ 2 * Real.log (r : ℝ) * n
  maxDegree_lower : (r : ℝ) ≤ 7 * (R.maxDegree : ℝ)
  maxDegree_upper : (R.maxDegree : ℝ) ≤
    β * r * Real.log (r : ℝ)

/-- The literal edge gain promised in a round with parameter `β`. -/
def BLSRoundGain (r : ℕ) (β : ℝ)
    (R H : SimpleGraph V) : Prop :=
  60 * edgeCount R /
      (Real.rpow β (9 / 10 : ℝ) * r) ≤ (edgeCount H : ℝ)

/-- Fixed-parameter form of the one-round construction.  The Key Lemma is
assumed for every residual and every equality parameter `γ`; the returned
extractor is total and only its quantitative guarantee is conditional on
admissibility. -/
theorem exists_total_BLSRoundExtractor
    {N r n : ℕ} {β β₀ : ℝ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hββ₀ : β ≤ β₀)
    (hkey : ∀ (R : SimpleGraph (Fin N)) (γ : ℝ),
      @BLSKeyLemmaAt (Fin N) inferInstance R (Classical.decRel _)
        r n γ β₀) :
    ∃ pick : SimpleGraph (Fin N) → SimpleGraph (Fin N),
      (∀ R, pick R ≤ R) ∧
      (∀ R, (pathGraph n).Free (pick R)) ∧
      (∀ R,
        @BLSRoundAdmissible (Fin N) inferInstance R
            (Classical.decRel _) r n β →
          BLSRoundGain r β R (pick R)) := by
  let Good : SimpleGraph (Fin N) → Prop := fun R =>
    @BLSRoundAdmissible (Fin N) inferInstance R
      (Classical.decRel _) r n β
  let gain : SimpleGraph (Fin N) → SimpleGraph (Fin N) → Prop :=
    BLSRoundGain r β
  have hextract : ∀ R, Good R → ∃ H : SimpleGraph (Fin N),
      H ≤ R ∧ (pathGraph n).Free H ∧ gain R H := by
    intro R hR
    letI : DecidableRel R.Adj := Classical.decRel _
    change BLSRoundAdmissible R r n β at hR
    change ∃ H : SimpleGraph (Fin N),
      H ≤ R ∧ (pathGraph n).Free H ∧ BLSRoundGain r β R H
    simpa only [BLSRoundGain] using
      (exists_pathFree_of_BLSKeyLemma_maxDegree_le R hr hββ₀
        hR.maxDegree_lower hR.maxDegree_upper hR.vertex_le
        hR.edge_lower hR.edge_upper (fun γ => hkey R γ))
  have hrReal : (0 : ℝ) < r := by positivity
  have hlogOne : (1 : ℝ) < Real.log (r : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hrReal).mpr
    exact Real.exp_one_lt_three.trans_le
      (by exact_mod_cast (show 3 ≤ r by omega))
  have hnHundred : (100 : ℝ) < n := by nlinarith
  have hnTwo : 2 ≤ n := by
    exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have hbot : (pathGraph n).Free (⊥ : SimpleGraph (Fin N)) := by
    apply SimpleGraph.free_bot
    intro hpath
    have hp : (pathGraph n).Adj
        (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := by
      rw [pathGraph_adj]
      exact Or.inl rfl
    rw [hpath] at hp
    exact hp
  simpa only [Good, gain] using
    (exists_total_conditionalFreeExtractor
      (pathGraph n) Good gain hextract hbot)

/-- Quantifier package obtained directly from `BLSKeyLemmaV1`.  The round is
available once `r` exceeds both the Key Lemma threshold and the explicit
`r ≥ 21` threshold used by maximum-degree normalisation. -/
theorem exists_BLSRoundExtractors_of_BLSKeyLemmaV1
    (hBLS : BLSKeyLemmaV1) :
    ∃ β₀ : ℝ, β₀ ∈ Set.Ioc (0 : ℝ) 1 ∧
      ∃ r₀ : ℕ, ∀ r : ℕ, max 21 r₀ ≤ r →
        ∀ n : ℕ, 100 * Real.log (r : ℝ) ≤ (n : ℝ) →
          ∀ β : ℝ, β ≤ β₀ →
            ∀ N : ℕ,
              ∃ pick : SimpleGraph (Fin N) → SimpleGraph (Fin N),
                (∀ R, pick R ≤ R) ∧
                (∀ R, (pathGraph n).Free (pick R)) ∧
                (∀ R,
                  @BLSRoundAdmissible (Fin N) inferInstance R
                      (Classical.decRel _) r n β →
                    BLSRoundGain r β R (pick R)) := by
  obtain ⟨β₀, hβ₀, r₀, hkey⟩ := hBLS
  refine ⟨β₀, hβ₀, r₀, ?_⟩
  intro r hr n hn β hβ N
  apply exists_total_BLSRoundExtractor
    (le_trans (Nat.le_max_left 21 r₀) hr) hn hβ
  intro R γ
  exact hkey r (le_trans (Nat.le_max_right 21 r₀) hr)
    n hn N R γ

end

end LeanCo.SizeRamsey
