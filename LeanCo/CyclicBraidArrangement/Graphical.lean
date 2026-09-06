import LeanCo.CyclicBraidArrangement.CycleFormula
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Graphical Shi and Catalan deformation matrices. -/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

/-- The directed `0`--`1` matrix for the deleted graphical Shi arrangement:
an edge contributes in its descending orientation. -/
noncomputable def graphicalShi {n : ℕ} (G : SimpleGraph (Fin n)) :
    DeformationMatrix n := by
  classical
  exact {
    entry := fun i j ↦ if G.Adj i j ∧ j < i then 1 else 0
    diagonal_zero := by intro i; simp }

/-- The symmetric `0`--`1` matrix for the graphical Catalan arrangement. -/
noncomputable def graphicalCatalan {n : ℕ} (G : SimpleGraph (Fin n)) :
    DeformationMatrix n := by
  classical
  exact {
    entry := fun i j ↦ if G.Adj i j then 1 else 0
    diagonal_zero := by intro i; simp }

theorem graphicalShi_entry_le_one {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    (graphicalShi G).entry i j ≤ 1 := by
  classical
  simp only [graphicalShi]
  split_ifs <;> omega

theorem graphicalCatalan_entry_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) : (graphicalCatalan G).entry i j ≤ 1 := by
  classical
  simp only [graphicalCatalan]
  split_ifs <;> omega

theorem cyclicallyCompatible_graphicalShi {n : ℕ} (G : SimpleGraph (Fin n)) :
    (graphicalShi G).CyclicallyCompatible :=
  cyclicallyCompatible_of_entry_le_one _ (graphicalShi_entry_le_one G)

theorem cyclicallyCompatible_graphicalCatalan {n : ℕ} (G : SimpleGraph (Fin n)) :
    (graphicalCatalan G).CyclicallyCompatible :=
  cyclicallyCompatible_of_entry_le_one _ (graphicalCatalan_entry_le_one G)

/-- Number of cyclic descents whose underlying pair is an edge of `G`. -/
noncomputable def graphicalCyclicDescents {n : ℕ} [NeZero n]
    (G : SimpleGraph (Fin n)) (w : CyclicOrdering n) : ℕ := by
  classical
  exact (Finset.univ.filter fun k ↦
    G.Adj (w k) (w (nextPosition n k)) ∧ w (nextPosition n k) < w k).card

/-- Number of cyclic positions whose underlying pair is an edge of `G`.
For `n = 2`, the sole edge is deliberately counted twice. -/
noncomputable def graphicalCyclicEdges {n : ℕ} [NeZero n]
    (G : SimpleGraph (Fin n)) (w : CyclicOrdering n) : ℕ := by
  classical
  exact (Finset.univ.filter fun k ↦ G.Adj (w k) (w (nextPosition n k))).card

open scoped Classical in
theorem cycleWeight_graphicalShi {n : ℕ} [NeZero n]
    (G : SimpleGraph (Fin n)) (w : CyclicOrdering n) :
    (graphicalShi G).cycleWeight w = graphicalCyclicDescents G w := by
  unfold cycleWeight graphicalShi graphicalCyclicDescents
  simp only [Finset.sum_boole]
  norm_num

open scoped Classical in
theorem cycleWeight_graphicalCatalan {n : ℕ} [NeZero n]
    (G : SimpleGraph (Fin n)) (w : CyclicOrdering n) :
    (graphicalCatalan G).cycleWeight w = graphicalCyclicEdges G w := by
  unfold cycleWeight graphicalCatalan graphicalCyclicEdges
  simp only [Finset.sum_boole]
  norm_num

theorem cycleFormula_graphicalShi {n : ℕ} [NeZero n]
    (G : SimpleGraph (Fin n)) (t : ℚ) :
    cycleFormula (graphicalShi G) t =
      ∑ w : NormalizedCycle n,
        generalizedChoose (t - graphicalCyclicDescents G w.1 - 1) (n - 1) := by
  classical
  unfold cycleFormula
  apply Finset.sum_congr rfl
  intro w hw
  rw [cycleWeight_graphicalShi]

theorem cycleFormula_graphicalCatalan {n : ℕ} [NeZero n]
    (G : SimpleGraph (Fin n)) (t : ℚ) :
    cycleFormula (graphicalCatalan G) t =
      ∑ w : NormalizedCycle n,
        generalizedChoose (t - graphicalCyclicEdges G w.1 - 1) (n - 1) := by
  classical
  unfold cycleFormula
  apply Finset.sum_congr rfl
  intro w hw
  rw [cycleWeight_graphicalCatalan]

/-- The cycle formula for a two-sided graphical Shi deformation. -/
theorem cycleFormula_graphicalShi_extend {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (α β : Fin n → ℕ) (t : ℚ) :
    cycleFormula ((graphicalShi G).extend α β) t =
      cycleFormula (graphicalShi G) (t - ((∑ i, α i) + ∑ i, β i)) :=
  cycleFormula_extend_shift hn _ α β t

/-- The cycle formula for a two-sided graphical Catalan deformation. -/
theorem cycleFormula_graphicalCatalan_extend {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (α β : Fin n → ℕ) (t : ℚ) :
    cycleFormula ((graphicalCatalan G).extend α β) t =
      cycleFormula (graphicalCatalan G) (t - ((∑ i, α i) + ∑ i, β i)) :=
  cycleFormula_extend_shift hn _ α β t

/-- Displayed two-sided graphical Shi formula from the paper. -/
theorem cycleFormula_graphicalShi_extend_explicit {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (α β : Fin n → ℕ) (t : ℚ) :
    cycleFormula ((graphicalShi G).extend α β) t =
      ∑ w : NormalizedCycle n,
        generalizedChoose
          (t - ((∑ i, α i) + ∑ i, β i) - graphicalCyclicDescents G w.1 - 1)
          (n - 1) := by
  rw [cycleFormula_graphicalShi_extend hn,
    cycleFormula_graphicalShi]

/-- Displayed two-sided graphical Catalan formula from the paper. -/
theorem cycleFormula_graphicalCatalan_extend_explicit {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (α β : Fin n → ℕ) (t : ℚ) :
    cycleFormula ((graphicalCatalan G).extend α β) t =
      ∑ w : NormalizedCycle n,
        generalizedChoose
          (t - ((∑ i, α i) + ∑ i, β i) - graphicalCyclicEdges G w.1 - 1)
          (n - 1) := by
  rw [cycleFormula_graphicalCatalan_extend hn,
    cycleFormula_graphicalCatalan]

end DeformationMatrix

end CyclicBraidArrangement
