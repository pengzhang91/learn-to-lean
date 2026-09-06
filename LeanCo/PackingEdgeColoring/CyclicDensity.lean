import Mathlib

/-!
# Double counting on finite cyclic permutations

If every length-`window` cyclic window contains at least `lower` marked
positions, summing over all starting positions counts each marked position
exactly `window` times.
-/

open scoped BigOperators

namespace LeanCo.PackingEdgeColoring

open Finset

noncomputable section

variable {A : Type*} [Fintype A]

/-- Number of marked positions among the first `window` iterates starting
at `x`. -/
def cyclicWindowCount (σ : Equiv.Perm A) (P : A → Prop)
    [DecidablePred P] (window : ℕ) (x : A) : ℕ :=
  ∑ j : Fin window, if P ((σ ^ (j : ℕ)) x) then 1 else 0

/-- Each marked position occurs in exactly `window` of the translated
windows.  Cyclic transitivity is not needed; bijectivity suffices. -/
theorem sum_cyclicWindowCount (σ : Equiv.Perm A) (P : A → Prop)
    [DecidablePred P] (window : ℕ) :
    (∑ x : A, cyclicWindowCount σ P window x) =
      window * (Finset.univ.filter P).card := by
  classical
  unfold cyclicWindowCount
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin window, ∑ x : A,
        if P ((σ ^ (j : ℕ)) x) then 1 else 0) =
        ∑ _j : Fin window, ∑ x : A, if P x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Equiv.sum_comp (σ ^ (j : ℕ))
        (fun x : A ↦ if P x then 1 else 0)
    _ = window * (∑ x : A, if P x then 1 else 0) := by simp
    _ = window * (Finset.univ.filter P).card := by
      congr 1
      have h := Finset.sum_boole (R := ℕ) P (Finset.univ : Finset A)
      norm_num at h ⊢

/-- The generic cyclic-window density inequality. -/
theorem mul_card_le_window_mul_marked_of_window_lower_bound
    (σ : Equiv.Perm A) (P : A → Prop) [DecidablePred P]
    (window lower : ℕ)
    (hlower : ∀ x : A, lower ≤ cyclicWindowCount σ P window x) :
    lower * Fintype.card A ≤
      window * (Finset.univ.filter P).card := by
  calc
    lower * Fintype.card A = ∑ _x : A, lower := by simp [Nat.mul_comm]
    _ ≤ ∑ x : A, cyclicWindowCount σ P window x :=
      Finset.sum_le_sum fun x _ ↦ hlower x
    _ = window * (Finset.univ.filter P).card :=
      sum_cyclicWindowCount σ P window

end

end LeanCo.PackingEdgeColoring
