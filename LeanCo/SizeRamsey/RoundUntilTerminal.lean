import LeanCo.SizeRamsey.RoundColoringIteration

/-!
# Iterating rounds until a terminal colouring is available

Each lower-bound round either colours its entire current graph by a fixed
terminal palette, or colours the difference to a smaller residual and
advances the invariant.  This module performs the finite recursion and keeps
an exact account of both possibilities.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- An avoiding `Fin a` colouring can be viewed as a `Fin b` colouring when
`a ≤ b`. -/
theorem exists_path_avoidingColoring_fin_mono
    {G : SimpleGraph V} {a b n : ℕ} (hn : 2 ≤ n) (hab : a ≤ b)
    (C : G.EdgeLabeling (Fin a))
    (hC : AvoidsMonochromaticCopy (pathGraph n) C) :
    ∃ D : G.EdgeLabeling (Fin b),
      AvoidsMonochromaticCopy (pathGraph n) D := by
  let emb : Fin a ↪ Fin b := Fin.castLEEmb hab
  exact ⟨C.compRight emb,
    avoiding_compRight_of_injective
      (pathGraph_ne_bot_of_two_le_glue hn) C hC emb emb.injective⟩

/-- Finite recursion with an early terminal alternative. -/
theorem exists_path_coloring_or_iterated_residual
    (Invariant : ℕ → SimpleGraph V → Prop) (budget : ℕ → ℕ)
    (terminalBudget : ℕ) {n : ℕ} (hn : 2 ≤ n)
    (step : ∀ i (G : SimpleGraph V), Invariant i G →
      (∃ C : G.EdgeLabeling (Fin terminalBudget),
        AvoidsMonochromaticCopy (pathGraph n) C) ∨
      ∃ R : SimpleGraph V, R ≤ G ∧ Invariant (i + 1) R ∧
        ∃ C : (G \ R).EdgeLabeling (Fin (budget i)),
          AvoidsMonochromaticCopy (pathGraph n) C) :
    ∀ (T i : ℕ) (G : SimpleGraph V), Invariant i G →
      (∃ C : G.EdgeLabeling
          (Fin (iteratedRoundBudget budget i T + terminalBudget)),
        AvoidsMonochromaticCopy (pathGraph n) C) ∨
      ∃ R : SimpleGraph V, R ≤ G ∧ Invariant (i + T) R ∧
        ∃ C : (G \ R).EdgeLabeling
            (Fin (iteratedRoundBudget budget i T)),
          AvoidsMonochromaticCopy (pathGraph n) C := by
  intro T
  induction T with
  | zero =>
      intro i G hG
      right
      refine ⟨G, le_rfl, ?_, ?_⟩
      · simpa using hG
      · exact exists_zeroColor_path_avoidingColoring_sdiff_self G
  | succ T ih =>
      intro i G hG
      rcases step i G hG with hterminal | hcontinue
      · left
        obtain ⟨C, hC⟩ := hterminal
        exact exists_path_avoidingColoring_fin_mono hn
          (show terminalBudget ≤
            iteratedRoundBudget budget i (T + 1) + terminalBudget by omega)
          C hC
      · obtain ⟨R₁, hR₁, hInv₁, Couter, hCouter⟩ := hcontinue
        rcases ih (i + 1) R₁ hInv₁ with hterminal | hcontinue
        · left
          obtain ⟨Cright, hCright⟩ := hterminal
          apply exists_path_avoidingColoring_of_split
            hR₁ hn Couter hCouter Cright hCright
          simp only [iteratedRoundBudget_succ]
          omega
        · right
          obtain ⟨R₂, hR₂, hInv₂, Cinner, hCinner⟩ := hcontinue
          refine ⟨R₂, hR₂.trans hR₁, ?_, ?_⟩
          · have hindex : i + (T + 1) = (i + 1) + T := by omega
            rw [hindex]
            exact hInv₂
          · apply exists_path_avoidingColoring_of_nested_sdiff
              hR₁ hR₂ hn Couter hCouter Cinner hCinner
            simp only [iteratedRoundBudget_succ]
            exact le_rfl

end

end LeanCo.SizeRamsey
