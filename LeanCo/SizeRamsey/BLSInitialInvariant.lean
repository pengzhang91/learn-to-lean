import LeanCo.SizeRamsey.InitialCoreCleanup
import LeanCo.SizeRamsey.BLSInitialNumerics
import LeanCo.SizeRamsey.BLSRoundStep
import Mathlib.Tactic

/-!
# Initialising the BLS recursive invariant

This module packages the initial low-degree restriction and star cleanup as
the index-zero invariant consumed by the finite BLS recursion.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

/-- The initial high-core restriction and star cleanup produce a residual
that satisfies all three fields of `BLSIterationInvariant` at index zero.
The remaining conjuncts retain the cleanup colouring and all monotonicity
facts needed to glue a recursively obtained colouring back to the original
graph. -/
theorem exists_initialBLSInvariant
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C β₀ : ℝ} {r n : ℕ}
    (hC : 0 < C) (hCsmall : 10000 * C ≤ 1)
    (hCβ : 20000 * C ≤ β₀)
    (hr : 2000 ≤ r) (hn : 12 ≤ n)
    (hedges : (edgeCount G : ℝ) ≤ roundEdgeCap C r n 0) :
    ∃ R : SimpleGraph ↥(highCoreVertexFinset G (initialDegreeThreshold r)),
      R ≤ highCoreRestriction G (initialDegreeThreshold r) ∧
      BLSIterationInvariant r n (roundBeta β₀) (roundEdgeCap C r n) 0 R ∧
      ∃ Cclean :
          (highCoreRestriction G (initialDegreeThreshold r) \ R).EdgeLabeling
            (Fin (initialStarBudget r)),
        AvoidsMonochromaticCopy (pathGraph n) Cclean ∧
        Fintype.card ↥(highCoreVertexFinset G (initialDegreeThreshold r)) =
          (highCoreVertexFinset G (initialDegreeThreshold r)).card ∧
        edgeCount R ≤
          edgeCount (highCoreRestriction G (initialDegreeThreshold r)) ∧
        edgeCount (highCoreRestriction G (initialDegreeThreshold r)) ≤
          edgeCount G := by
  have hs : 0 < initialStarBudget r :=
    initialStarBudget_pos (by omega)
  obtain ⟨R, hRcore, hdegree, Cclean, hCclean, hcard,
      hRedges, hcoreEdges⟩ :=
    exists_initialCoreCleanup G (initialDegreeThreshold r) hs hn
  letI : DecidableRel R.Adj := Classical.decRel _
  have hvertex :
      (Fintype.card ↥(highCoreVertexFinset G (initialDegreeThreshold r)) : ℝ) ≤
        ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ)) / 4 :=
    initial_highCoreRestriction_card_le G hCsmall hedges
  have hcoreEdgesReal :
      (edgeCount (highCoreRestriction G (initialDegreeThreshold r)) : ℝ) ≤
        (edgeCount G : ℝ) := by
    exact_mod_cast hcoreEdges
  have hcoreCap :
      (edgeCount (highCoreRestriction G (initialDegreeThreshold r)) : ℝ) ≤
        roundEdgeCap C r n 0 :=
    hcoreEdgesReal.trans hedges
  have hRedgesReal :
      (edgeCount R : ℝ) ≤
        (edgeCount (highCoreRestriction G (initialDegreeThreshold r)) : ℝ) := by
    exact_mod_cast hRedges
  have hRedgeCap : (edgeCount R : ℝ) ≤ roundEdgeCap C r n 0 :=
    hRedgesReal.trans hcoreCap
  have hdegree' : ∀ v, R.degree v ≤
      8 * edgeCount (highCoreRestriction G (initialDegreeThreshold r)) /
        (n * initialStarBudget r) := by
    intro v
    have hv := hdegree v
    rw [Nat.card_eq_fintype_card, R.card_neighborSet_eq_degree] at hv
    exact hv
  have hmaxNat : R.maxDegree ≤
      8 * edgeCount (highCoreRestriction G (initialDegreeThreshold r)) /
        (n * initialStarBudget r) :=
    R.maxDegree_le_of_forall_degree_le _ hdegree'
  have hmaxCast : (R.maxDegree : ℝ) ≤
      ((8 * edgeCount (highCoreRestriction G (initialDegreeThreshold r)) /
        (n * initialStarBudget r) : ℕ) : ℝ) := by
    exact_mod_cast hmaxNat
  have hquotient :
      ((8 * edgeCount (highCoreRestriction G (initialDegreeThreshold r)) /
        (n * initialStarBudget r) : ℕ) : ℝ) ≤
          β₀ * (r : ℝ) * Real.log (r : ℝ) :=
    initialStarBudget_quotient_le_beta hC hCβ hr hn hcoreCap
  have hmax : (R.maxDegree : ℝ) ≤
      roundBeta β₀ 0 * (r : ℝ) * Real.log (r : ℝ) := by
    simpa [roundBeta] using hmaxCast.trans hquotient
  have hInv :
      BLSIterationInvariant r n (roundBeta β₀) (roundEdgeCap C r n) 0 R := by
    change
      (Fintype.card ↥(highCoreVertexFinset G (initialDegreeThreshold r)) : ℝ) ≤
          ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ)) / 4 ∧
        (edgeCount R : ℝ) ≤ roundEdgeCap C r n 0 ∧
        (R.maxDegree : ℝ) ≤
          roundBeta β₀ 0 * (r : ℝ) * Real.log (r : ℝ)
    exact ⟨hvertex, hRedgeCap, hmax⟩
  exact ⟨R, hRcore, hInv, Cclean, hCclean, hcard,
    hRedges, hcoreEdges⟩

end

end LeanCo.SizeRamsey
