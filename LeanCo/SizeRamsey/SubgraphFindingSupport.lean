import LeanCo.SizeRamsey.BalancedCut
import LeanCo.SizeRamsey.MaximizingBinSubgraph

/-!
# Interface support for the repaired BLS subgraph-finding lemma

This file is an independently compiled audit of the interfaces used to
assemble `BLSSubgraphFindingAt`.  It deliberately does not import or modify
the final `SubgraphFinding` module.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- The empty graph is `P_n`-free as soon as the path has an edge. -/
theorem pathGraph_free_bot_of_two_le_support {n : ℕ} (hn : 2 ≤ n) :
    (pathGraph n).Free (⊥ : SimpleGraph V) := by
  apply free_bot
  intro hbot
  have hp : (pathGraph n).Adj
      (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := by
    rw [pathGraph_adj]
    exact Or.inl rfl
  rw [hbot] at hp
  exact hp

/-- Independently compiled composition skeleton for the repaired version of
BLS Lemma 4.5.  The proof has explicit branches for zero bins, zero degree,
one bin, and at least two bins. -/
theorem BLSSubgraphFindingAt_of_v1_hypotheses_support
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r n Δ : ℕ} (V₀ U : Finset V)
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ)) :
    BLSSubgraphFindingAt G r n Δ V₀ U := by
  intro hVU hcover hU hcard hglobalDegree _hDeltaUpper
  have hrReal : (0 : ℝ) < r := by positivity
  have hlogOne : (1 : ℝ) < Real.log (r : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hrReal).mpr
    exact Real.exp_one_lt_three.trans_le
      (by exact_mod_cast (show 3 ≤ r by omega))
  have hnHundred : (100 : ℝ) < n := by nlinarith
  have hnTwo : 2 ≤ n := by
    exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have hnPos : 0 < n := by omega

  let q := subgraphFindingBinCount n V₀.card
  by_cases hqZero : q = 0
  · exact (BLSSubgraphFindingAt_of_binCount_eq_zero
      G r n Δ V₀ U hnTwo (by simpa only [q] using hqZero))
      hVU hcover hU hcard hglobalDegree _hDeltaUpper

  by_cases hDeltaZero : Δ = 0
  · subst Δ
    refine ⟨⊥, bot_le, pathGraph_free_bot_of_two_le_support hnTwo, ?_⟩
    simp [ballsBinsWeight]

  have hDeltaPos : 0 < Δ := Nat.pos_of_ne_zero hDeltaZero
  obtain ⟨A, B, hAV₀, hBdef, hAcard, hAB, hABcover, hUB,
      hBminusU, hbip, hcut⟩ :=
    exists_balancedCut_with_independent_right G hVU hcover hU
  let C : SimpleGraph V := crossSubgraph G A B
  let eA : Fin ((V₀.card + 1) / 2) ≃ A :=
    (A.equivFinOfCardEq hAcard).symm
  have hCle : C ≤ G := by
    dsimp only [C]
    exact crossSubgraph_le G A B
  have hcut' : edgeCount G ≤ 2 * edgeCount C := by
    simpa only [crossEdgeCount, C] using hcut

  by_cases hqOne : q = 1
  · exact exists_pathFree_of_dense_bipartite_cut_one_bin
      G C A B eA hCle hcut' hAB (by simpa only [C] using hbip)
      hnPos (by simpa only [q] using hqOne) hDeltaPos

  have hqTwo : 2 ≤ q := by omega
  apply exists_pathFree_of_dense_bipartite_cut
    G C A B eA hCle hcut' hAB (by simpa only [C] using hbip)
    hr hn hcard (by simpa only [q] using hqTwo) hDeltaPos
  intro b
  exact (C.degree_le_of_le hCle).trans (hglobalDegree (b : V))

end

end LeanCo.SizeRamsey
