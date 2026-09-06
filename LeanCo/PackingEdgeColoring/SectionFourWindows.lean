import LeanCo.PackingEdgeColoring.CyclicDensity

/-!
# The local six-window reduction used in Section 4

The numerical discharging argument needs every six consecutive boundary
occurrences to contain at least two marked (degree-three) occurrences.  This
file isolates the exact finite combinatorics behind that assertion.  A window
with at most one marked occurrence either contains four consecutive unmarked
occurrences, or has one of the two exceptional `2+3` / `3+2` patterns.
-/

namespace LeanCo.PackingEdgeColoring

noncomputable section

variable {A : Type*} [Fintype A]

/-- Every four consecutive iterates contain a marked position. -/
def FourWindowMarked (σ : Equiv.Perm A) (P : A → Prop) : Prop :=
  ∀ x, P x ∨ P (σ x) ∨ P ((σ ^ 2) x) ∨ P ((σ ^ 3) x)

/-- The sole marked position in a six-window has two unmarked positions before
it and three after it. -/
def TwoThreePatternAt (σ : Equiv.Perm A) (P : A → Prop) (x : A) : Prop :=
  ¬ P x ∧ ¬ P (σ x) ∧ P ((σ ^ 2) x) ∧ ¬ P ((σ ^ 3) x) ∧
    ¬ P ((σ ^ 4) x) ∧ ¬ P ((σ ^ 5) x)

/-- The reverse exceptional pattern: three unmarked positions, one marked
position, and then two unmarked positions. -/
def ThreeTwoPatternAt (σ : Equiv.Perm A) (P : A → Prop) (x : A) : Prop :=
  ¬ P x ∧ ¬ P (σ x) ∧ ¬ P ((σ ^ 2) x) ∧ P ((σ ^ 3) x) ∧
    ¬ P ((σ ^ 4) x) ∧ ¬ P ((σ ^ 5) x)

/-- Boolean-arithmetic core of the six-window argument. -/
private theorem two_le_six_indicators
    (p₀ p₁ p₂ p₃ p₄ p₅ : Prop)
    [Decidable p₀] [Decidable p₁] [Decidable p₂]
    [Decidable p₃] [Decidable p₄] [Decidable p₅]
    (hleft : p₀ ∨ p₁ ∨ p₂ ∨ p₃)
    (hright : p₂ ∨ p₃ ∨ p₄ ∨ p₅)
    (h₂₃ : ¬ (¬p₀ ∧ ¬p₁ ∧ p₂ ∧ ¬p₃ ∧ ¬p₄ ∧ ¬p₅))
    (h₃₂ : ¬ (¬p₀ ∧ ¬p₁ ∧ ¬p₂ ∧ p₃ ∧ ¬p₄ ∧ ¬p₅)) :
    2 ≤ (if p₀ then 1 else 0) + (if p₁ then 1 else 0) +
      (if p₂ then 1 else 0) + (if p₃ then 1 else 0) +
      (if p₄ then 1 else 0) + (if p₅ then 1 else 0) := by
  by_cases hp₀ : p₀ <;> by_cases hp₁ : p₁ <;> by_cases hp₂ : p₂ <;>
    by_cases hp₃ : p₃ <;> by_cases hp₄ : p₄ <;> by_cases hp₅ : p₅ <;>
    simp_all

/-- If four-gaps and the only two possible one-mark six-windows are absent,
then every six-window contains at least two marked positions. -/
theorem two_le_cyclicWindowCount_six
    (σ : Equiv.Perm A) (P : A → Prop) [DecidablePred P]
    (hfour : FourWindowMarked σ P)
    (h₂₃ : ∀ x, ¬ TwoThreePatternAt σ P x)
    (h₃₂ : ∀ x, ¬ ThreeTwoPatternAt σ P x) (x : A) :
    2 ≤ cyclicWindowCount σ P 6 x := by
  classical
  have hleft := hfour x
  have hright := hfour ((σ ^ 2) x)
  have hcomp (m n : ℕ) :
      (σ ^ m) ((σ ^ n) x) = (σ ^ (m + n)) x := by
    rw [← Equiv.Perm.mul_apply]
    congr 1
    group
  have hσ₁ : σ ((σ ^ 2) x) = (σ ^ 3) x := by
    simpa using hcomp 1 2
  have hσ₂ : (σ ^ 2) ((σ ^ 2) x) = (σ ^ 4) x := by
    simpa using hcomp 2 2
  have hσ₃ : (σ ^ 3) ((σ ^ 2) x) = (σ ^ 5) x := by
    simpa using hcomp 3 2
  have hright' :
      P ((σ ^ 2) x) ∨ P ((σ ^ 3) x) ∨
        P ((σ ^ 4) x) ∨ P ((σ ^ 5) x) := by
    simpa only [hσ₁, hσ₂, hσ₃] using hright
  have hcore := two_le_six_indicators
    (P x) (P (σ x)) (P ((σ ^ 2) x)) (P ((σ ^ 3) x))
    (P ((σ ^ 4) x)) (P ((σ ^ 5) x))
    hleft hright' (h₂₃ x) (h₃₂ x)
  have hcount : cyclicWindowCount σ P 6 x =
      (if P x then 1 else 0) + (if P (σ x) then 1 else 0) +
        (if P ((σ ^ 2) x) then 1 else 0) +
        (if P ((σ ^ 3) x) then 1 else 0) +
        (if P ((σ ^ 4) x) then 1 else 0) +
        (if P ((σ ^ 5) x) then 1 else 0) := by
    unfold cyclicWindowCount
    simp only [Fin.sum_univ_six]
    norm_num
  rw [hcount]
  exact hcore

end

end LeanCo.PackingEdgeColoring
