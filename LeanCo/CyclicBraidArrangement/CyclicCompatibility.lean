import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Cyclically compatible matrix deformations

Core definitions and the constant cycle-weight calculation underlying the
two-sided shift theorem of arXiv:2608.29203.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

/-- A nonnegative matrix deformation with zero diagonal. -/
structure DeformationMatrix (n : ℕ) where
  entry : Fin n → Fin n → ℕ
  diagonal_zero : ∀ i, entry i i = 0

namespace DeformationMatrix

variable {n : ℕ}

/-- The paper's cyclic compatibility condition. -/
def CyclicallyCompatible (M : DeformationMatrix n) : Prop :=
  ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
    M.entry a c ≤ M.entry a b + M.entry b c + 1

/-- Two-sided vertex extension of a deformation matrix. -/
def extend (M : DeformationMatrix n) (α β : Fin n → ℕ) :
    DeformationMatrix n where
  entry i j := if i = j then 0 else M.entry i j + α i + β j
  diagonal_zero i := by simp

theorem extend_entry_of_ne (M : DeformationMatrix n) (α β : Fin n → ℕ)
    {i j : Fin n} (hij : i ≠ j) :
    (M.extend α β).entry i j = M.entry i j + α i + β j := by
  simp [extend, hij]

theorem cyclicallyCompatible_extend (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) (α β : Fin n → ℕ) :
    (M.extend α β).CyclicallyCompatible := by
  intro a b c hab hac hbc
  rw [M.extend_entry_of_ne α β hac, M.extend_entry_of_ne α β hab,
    M.extend_entry_of_ne α β hbc]
  have h := hM a b c hab hac hbc
  omega

/-- A cyclic ordering is represented by a permutation; rotating the positions
does not affect any theorem below. -/
abbrev CyclicOrdering (n : ℕ) := Equiv.Perm (Fin n)

/-- Successor of a cyclic position. -/
def nextPosition (n : ℕ) [NeZero n] : Equiv.Perm (Fin n) :=
  Equiv.addRight 1

/-- Directed Hamiltonian-cycle weight `L_M(w)`. -/
def cycleWeight (M : DeformationMatrix n) [NeZero n]
    (w : CyclicOrdering n) : ℕ :=
  ∑ k, M.entry (w k) (w (nextPosition n k))

theorem cycleWeight_extend {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (α β : Fin n → ℕ) (w : CyclicOrdering n)
    (hadj : ∀ k, w k ≠ w (nextPosition n k)) :
    (M.extend α β).cycleWeight w =
      M.cycleWeight w + ∑ i, α i + ∑ i, β i := by
  simp_rw [cycleWeight, M.extend_entry_of_ne α β (hadj _), Finset.sum_add_distrib]
  rw [Equiv.sum_comp w α]
  have hβ : (∑ k, β (w (nextPosition n k))) = ∑ i, β i := by
    simpa only [Equiv.trans_apply] using
      Equiv.sum_comp ((nextPosition n).trans w) β
  rw [hβ]

end DeformationMatrix
end CyclicBraidArrangement
