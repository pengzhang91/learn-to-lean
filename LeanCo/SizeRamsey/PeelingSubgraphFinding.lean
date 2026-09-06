import LeanCo.SizeRamsey.ApproxRegularPeeling
import LeanCo.SizeRamsey.SubgraphFinding

/-!
# Applying the repaired subgraph-finding lemma to peeled layers

The degree-band construction already supplies the vertex partition,
independent outside part, and global layer-degree control required by the
repaired BLS Lemma 4.5.  This file records the direct application both to a
peeled layer and to the final residual (with empty outside part).
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- A peeled layer satisfying the remaining numerical hypotheses admits the
large path-free subgraph promised by repaired BLS Lemma 4.5. -/
theorem exists_pathFree_subgraph_of_peelingLayer
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ)
    {r n Δ : ℕ} (j : ℕ)
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hcard : ((peelingBand G τ (j + 1)).card : ℝ) ≤
      2 * (r * Real.log (r : ℝ)) * n)
    (hdegree : ∀ v, (peelingResidual G τ j).degree v ≤ Δ)
    (hΔ : Δ ≤ ⌊r * Real.log (r : ℝ)⌋₊) :
    ∃ H : SimpleGraph V,
      H ≤ peelingLayer G τ (j + 1) ∧
      (pathGraph n).Free H ∧
      (edgeCount (peelingLayer G τ (j + 1)) : ℝ) / 3 *
          ballsBinsWeight
            (subgraphFindingBinCount n (peelingBand G τ (j + 1)).card) Δ ≤
        (edgeCount H : ℝ) := by
  let E := peelingLayer G τ (j + 1)
  let V₀ := peelingBand G τ (j + 1)
  let U := peelingOutside G τ (j + 1)
  have hpkg := peelingSubgraphFindingInput G τ j Δ hdegree
  have hlemma : BLSSubgraphFindingAt E r n Δ V₀ U :=
    BLSSubgraphFindingAt_repaired E hr hn V₀ U
  apply hlemma
  · exact hpkg.partition_disjoint
  · exact hpkg.partition_cover
  · exact hpkg.outside_independent
  · exact hcard
  · exact hpkg.global_degree_upper
  · exact hΔ

/-- The final residual uses the same repaired lemma with the entire vertex
set on the controlled side and an empty independent side. -/
theorem exists_pathFree_subgraph_of_peelingResidual
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ)
    {r n Δ T : ℕ}
    (hr : 21 ≤ r)
    (hn : 100 * Real.log (r : ℝ) ≤ (n : ℝ))
    (hcard : (Fintype.card V : ℝ) ≤
      2 * (r * Real.log (r : ℝ)) * n)
    (hdegree : ∀ v, (peelingResidual G τ T).degree v ≤ Δ)
    (hΔ : Δ ≤ ⌊r * Real.log (r : ℝ)⌋₊) :
    ∃ H : SimpleGraph V,
      H ≤ peelingResidual G τ T ∧
      (pathGraph n).Free H ∧
      (edgeCount (peelingResidual G τ T) : ℝ) / 3 *
          ballsBinsWeight
            (subgraphFindingBinCount n (Fintype.card V)) Δ ≤
        (edgeCount H : ℝ) := by
  let R := peelingResidual G τ T
  let V₀ : Finset V := Finset.univ
  let U : Finset V := ∅
  have hlemma : BLSSubgraphFindingAt R r n Δ V₀ U :=
    BLSSubgraphFindingAt_repaired R hr hn V₀ U
  apply hlemma
  · simp [V₀, U]
  · simp [V₀, U]
  · simp [U]
  · simpa only [V₀, Finset.card_univ] using hcard
  · exact hdegree
  · exact hΔ

end

end LeanCo.SizeRamsey
