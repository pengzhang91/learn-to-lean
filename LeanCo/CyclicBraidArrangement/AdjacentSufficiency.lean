import LeanCo.CyclicBraidArrangement.GapEnumeration

/-! The local converse behind sufficiency of adjacent gap inequalities. -/

namespace CyclicBraidArrangement

namespace DeformationMatrix

variable {n : ℕ}

/-- Every pair of adjacent admissible gaps makes the corresponding two-step
clockwise distance strictly exceed the direct forbidden bound. -/
def TwoStepGapSafe (M : DeformationMatrix n) : Prop :=
  ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    ∀ g₁ g₂ : ℕ, M.entry a b ≤ g₁ → M.entry b c ≤ g₂ →
      M.entry a c < (g₁ + 1) + (g₂ + 1)

/-- Cyclic compatibility implies local safety of adjacent gap bounds. -/
theorem twoStepGapSafe_of_cyclicallyCompatible (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) : M.TwoStepGapSafe := by
  intro a b c hab hac hbc g₁ g₂ hg₁ hg₂
  have h := hM a b c hab hac hbc
  omega

/-- If adjacent lower bounds always suffice, testing them at equality recovers
the cyclic compatibility inequality. -/
theorem cyclicallyCompatible_of_twoStepGapSafe (M : DeformationMatrix n)
    (hM : M.TwoStepGapSafe) : M.CyclicallyCompatible := by
  intro a b c hab hac hbc
  have h := hM a b c hab hac hbc
    (M.entry a b) (M.entry b c) le_rfl le_rfl
  omega

/-- Exact local characterization used in the converse part of the paper's
adjacent-gap proposition. -/
theorem cyclicallyCompatible_iff_twoStepGapSafe (M : DeformationMatrix n) :
    M.CyclicallyCompatible ↔ M.TwoStepGapSafe :=
  ⟨M.twoStepGapSafe_of_cyclicallyCompatible,
    M.cyclicallyCompatible_of_twoStepGapSafe⟩

/-- A failed compatibility inequality supplies the paper's explicit bad gap
assignment: take both adjacent gaps at their lower bounds. -/
theorem unsafe_witness_of_not_cyclicallyCompatible (M : DeformationMatrix n)
    (hM : ¬M.CyclicallyCompatible) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (M.entry a b + 1) + (M.entry b c + 1) ≤ M.entry a c := by
  rw [cyclicallyCompatible_iff_twoStepGapSafe] at hM
  simp only [TwoStepGapSafe, not_forall, not_lt] at hM
  rcases hM with ⟨a, b, c, hab, hac, hbc, g₁, g₂, hg₁, hg₂, hbad⟩
  refine ⟨a, b, c, hab, hac, hbc, ?_⟩
  omega

end DeformationMatrix

end CyclicBraidArrangement
