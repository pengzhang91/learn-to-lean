import LeanCo.SizeRamsey.ApproxRegularPeeling
import LeanCo.SizeRamsey.IncidentDegreeCount

/-!
# Degree-count bounds for peeled layers

Each peeled layer consists exactly of the residual edges incident to its
band.  Hence the band meets every layer edge, and its threshold/upper-degree
bounds convert directly into the two cardinality estimates used in the BLS
key lemma.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- The selected band meets every edge in its peeled layer. -/
theorem peelingLayer_edgesMeet_band
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    EdgesMeet (peelingLayer G τ (j + 1))
      (peelingBand G τ (j + 1)) := by
  intro x y hxy
  rw [peelingLayer_succ, degreeBandIncidentSubgraph_adj] at hxy
  exact hxy.2

/-- The layer threshold gives the paper's upper bound on band cardinality in
division-free natural-number form. -/
theorem peelingThreshold_mul_bandCard_le_twice_layerEdgeCount
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ) :
    τ (j + 1) * (peelingBand G τ (j + 1)).card ≤
      2 * edgeCount (peelingLayer G τ (j + 1)) := by
  apply mul_card_le_twice_edgeCount_of_degree_lower
  intro v hv
  exact peelingThreshold_le_layer_degree G τ j hv

/-- A global residual degree bound gives the paper's lower bound on band
cardinality, again without division or rounding. -/
theorem peelingLayerEdgeCount_le_bandCard_mul_of_residual_degree_upper
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j Δ : ℕ)
    (hdegree : ∀ v, (peelingResidual G τ j).degree v ≤ Δ) :
    edgeCount (peelingLayer G τ (j + 1)) ≤
      (peelingBand G τ (j + 1)).card * Δ := by
  apply edgeCount_le_card_mul_of_edgeMeetingSet_degree_upper
      (peelingLayer G τ (j + 1)) (peelingBand G τ (j + 1))
      (peelingLayer_edgesMeet_band G τ j)
  intro v hv
  exact (peelingLayer_degree_le_residual G τ j v).trans (hdegree v)

/-- Real division form of the band-cardinality upper estimate. -/
theorem peelingBandCard_le_two_mul_edgeCount_div_threshold
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (τ : ℕ → ℕ) (j : ℕ)
    (hτ : 0 < τ (j + 1)) :
    ((peelingBand G τ (j + 1)).card : ℝ) ≤
      2 * edgeCount (peelingLayer G τ (j + 1)) / τ (j + 1) := by
  have hnat :=
    peelingThreshold_mul_bandCard_le_twice_layerEdgeCount G τ j
  have hreal :
      (τ (j + 1) : ℝ) * (peelingBand G τ (j + 1)).card ≤
        2 * edgeCount (peelingLayer G τ (j + 1)) := by
    exact_mod_cast hnat
  exact (le_div_iff₀ (by exact_mod_cast hτ : (0 : ℝ) < τ (j + 1))).2
    (by simpa only [mul_comm] using hreal)

end

end LeanCo.SizeRamsey
