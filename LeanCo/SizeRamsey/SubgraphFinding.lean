import LeanCo.SizeRamsey.BalancedCut
import LeanCo.SizeRamsey.MaximizingBinSubgraph

/-!
# The repaired BLS subgraph-finding lemma

This file assembles the deterministic balanced-cut argument and the finite
balls-and-bins extraction into the repaired form of Beke--Li--Sahasrabudhe
Lemma 4.5.  The degree bound is global, hence in particular controls the
right side of the bipartite cut whose neighbourhoods are sampled.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- Under the numerical hypotheses of the v1 paper, the path graph has an
edge and therefore is free in the empty graph. -/
private theorem pathGraph_free_bot_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    (pathGraph n).Free (⊥ : SimpleGraph V) := by
  apply SimpleGraph.free_bot
  intro hbot
  have hp : (pathGraph n).Adj
      (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := by
    rw [pathGraph_adj]
    exact Or.inl rfl
  rw [hbot] at hp
  exact hp

/-- Repaired BLS Lemma 4.5 at fixed parameters.

The v1 proof uses the maximum-degree bound on vertices belonging to the
right side of the random bipartite cut, whereas its printed statement only
defines the maximum over `V₀`.  The residual graphs at every application in
the key-lemma proof have a global maximum-degree bound.  This theorem states
that usable interface and proves it end-to-end from the balanced-cut and
finite averaging modules.
-/
theorem BLSSubgraphFindingAt_repaired
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r n Δ : ℕ} (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (V₀ U : Finset V) :
    BLSSubgraphFindingAt G r n Δ V₀ U := by
  have hrReal : (0 : ℝ) < r := by positivity
  have hlogOne : (1 : ℝ) < Real.log (r : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hrReal).mpr
    exact Real.exp_one_lt_three.trans_le
      (by exact_mod_cast (show 3 ≤ r by omega))
  have hnHundred : (100 : ℝ) < n := by nlinarith
  have hnNat : 2 ≤ n := by
    exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have hnPos : 0 < n := by omega
  by_cases hqZero : subgraphFindingBinCount n V₀.card = 0
  · exact BLSSubgraphFindingAt_of_binCount_eq_zero
      G r n Δ V₀ U hnNat hqZero
  intro hVU hcover hU hv hglobal _hΔBound
  by_cases hΔZero : Δ = 0
  · subst Δ
    refine ⟨⊥, bot_le, pathGraph_free_bot_of_two_le hnNat, ?_⟩
    simp [ballsBinsWeight]
  have hΔPos : 0 < Δ := Nat.pos_of_ne_zero hΔZero
  obtain ⟨A, B, hAV, hB, hAcard, hAB, hABcover, hUB, hBU, hbip, hcut⟩ :=
    exists_balancedCut_with_independent_right G hVU hcover hU
  let C : SimpleGraph V := crossSubgraph G A B
  let eA : Fin ((V₀.card + 1) / 2) ≃ A :=
    (Fintype.equivFinOfCardEq (by
      simpa only [Fintype.card_coe] using hAcard)).symm
  have hCle : C ≤ G := by
    exact crossSubgraph_le G A B
  have hcutC : edgeCount G ≤ 2 * edgeCount C := by
    simpa only [C, crossEdgeCount] using hcut
  have hdegree : ∀ b : B, C.degree b ≤ Δ := by
    intro b
    exact (C.degree_le_of_le hCle).trans (hglobal b)
  by_cases hqOne : subgraphFindingBinCount n V₀.card = 1
  · exact exists_pathFree_of_dense_bipartite_cut_one_bin
      G C A B eA hCle hcutC hAB hbip hnPos hqOne hΔPos
  · have hqTwo : 2 ≤ subgraphFindingBinCount n V₀.card := by omega
    exact exists_pathFree_of_dense_bipartite_cut
      G C A B eA hCle hcutC hAB hbip hr hn hv hqTwo hΔPos hdegree

end

end LeanCo.SizeRamsey
