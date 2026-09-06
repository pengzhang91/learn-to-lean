import LeanCo.SizeRamsey.ColoringSplit

/-!
# Iterating coloured residual steps

This module separates the combinatorial bookkeeping of several lower-bound
rounds from their analytic invariants.  A step colours the difference between
its input graph and a nested residual.  Finitely many such steps then colour
the total difference, using the sum of the individual palette sizes.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- Sum of the next `T` round budgets, starting at round `i`. -/
def iteratedRoundBudget (budget : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i, T + 1 => budget i + iteratedRoundBudget budget (i + 1) T

@[simp]
theorem iteratedRoundBudget_zero (budget : ℕ → ℕ) (i : ℕ) :
    iteratedRoundBudget budget i 0 = 0 := rfl

@[simp]
theorem iteratedRoundBudget_succ (budget : ℕ → ℕ) (i T : ℕ) :
    iteratedRoundBudget budget i (T + 1) =
      budget i + iteratedRoundBudget budget (i + 1) T := rfl

/-- The empty difference has its unique zero-colour edge labelling. -/
theorem exists_zeroColor_path_avoidingColoring_sdiff_self
    (G : SimpleGraph V) {n : ℕ} :
    ∃ C : (G \ G).EdgeLabeling (Fin 0),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  have hGG : G \ G = (⊥ : SimpleGraph V) := sdiff_self
  rw [hGG]
  let C : (⊥ : SimpleGraph V).EdgeLabeling (Fin 0) := fun e => by
    have : False := by simpa using e.property
    exact this.elim
  exact ⟨C, fun c ↦ Fin.elim0 c⟩

/-- Generic finite iteration of residual-colouring steps.

`Invariant i G` may encode all degree, edge-mass, and vertex hypotheses at
round `i`.  The theorem only uses nesting and local avoiding colourings; the
final invariant and exact total palette are retained in the conclusion. -/
theorem exists_iterated_path_round_coloring
    (Invariant : ℕ → SimpleGraph V → Prop) (budget : ℕ → ℕ)
    {n : ℕ} (hn : 2 ≤ n)
    (step : ∀ i (G : SimpleGraph V), Invariant i G →
      ∃ R : SimpleGraph V, R ≤ G ∧ Invariant (i + 1) R ∧
        ∃ C : (G \ R).EdgeLabeling (Fin (budget i)),
          AvoidsMonochromaticCopy (pathGraph n) C) :
    ∀ (T i : ℕ) (G : SimpleGraph V), Invariant i G →
      ∃ R : SimpleGraph V, R ≤ G ∧ Invariant (i + T) R ∧
        ∃ C : (G \ R).EdgeLabeling
            (Fin (iteratedRoundBudget budget i T)),
          AvoidsMonochromaticCopy (pathGraph n) C := by
  intro T
  induction T with
  | zero =>
      intro i G hG
      refine ⟨G, le_rfl, ?_, ?_⟩
      · simpa using hG
      · exact exists_zeroColor_path_avoidingColoring_sdiff_self G
  | succ T ih =>
      intro i G hG
      obtain ⟨R₁, hR₁, hInv₁, Couter, hCouter⟩ := step i G hG
      obtain ⟨R₂, hR₂, hInv₂, Cinner, hCinner⟩ :=
        ih (i + 1) R₁ hInv₁
      refine ⟨R₂, hR₂.trans hR₁, ?_, ?_⟩
      · have hindex : i + (T + 1) = (i + 1) + T := by omega
        rw [hindex]
        exact hInv₂
      · exact exists_path_avoidingColoring_of_nested_sdiff
          hR₁ hR₂ hn Couter hCouter Cinner hCinner le_rfl

end

end LeanCo.SizeRamsey
