import LeanCo.CyclicBraidArrangement.GapEnumeration

/-! Weak-sum perturbations and elementary compatibility consequences. -/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

variable {n : ℕ}

def transpose (M : DeformationMatrix n) : DeformationMatrix n where
  entry i j := M.entry j i
  diagonal_zero i := M.diagonal_zero i

theorem cyclicallyCompatible_transpose (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) : M.transpose.CyclicallyCompatible := by
  intro a b c hab hac hbc
  change M.entry c a ≤ M.entry b a + M.entry c b + 1
  rw [Nat.add_comm (M.entry b a) (M.entry c b)]
  exact hM c b a hbc.symm hac.symm hab.symm

/-- Every matrix whose entries are at most one is cyclically compatible. -/
theorem cyclicallyCompatible_of_entry_le_one (M : DeformationMatrix n)
    (h01 : ∀ i j, M.entry i j ≤ 1) : M.CyclicallyCompatible := by
  intro a b c hab hac hbc
  exact (h01 a c).trans (by omega)

theorem cycleWeight_extend_eq_of_total_eq {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (α β α' β' : Fin n → ℕ)
    (w : CyclicOrdering n)
    (hadj : ∀ k, w k ≠ w (nextPosition n k))
    (htotal : (∑ i, α i) + ∑ i, β i = (∑ i, α' i) + ∑ i, β' i) :
    (M.extend α β).cycleWeight w = (M.extend α' β').cycleWeight w := by
  rw [M.cycleWeight_extend α β w hadj,
    M.cycleWeight_extend α' β' w hadj]
  omega

end DeformationMatrix

/-- Cycle weight for an arbitrary additive matrix. -/
def additiveCycleWeight {n : ℕ} [NeZero n] {R : Type*} [AddCommMonoid R]
    (D : Fin n → Fin n → R) (w : DeformationMatrix.CyclicOrdering n) : R :=
  ∑ k, D (w k) (w (DeformationMatrix.nextPosition n k))

/-- Off-diagonal weak row-plus-column form. -/
def IsWeakSum {n : ℕ} {R : Type*} [Add R]
    (D : Fin n → Fin n → R) : Prop :=
  ∃ ρ γ : Fin n → R, ∀ i j, i ≠ j → D i j = ρ i + γ j

/-- The easy direction of the weak-sum characterization: every Hamiltonian
cycle sees the same total row-plus-column perturbation. -/
theorem additiveCycleWeight_eq_of_weakSum {n : ℕ} [NeZero n]
    {R : Type*} [AddCommMonoid R] (D : Fin n → Fin n → R)
    (hD : IsWeakSum D) (w : DeformationMatrix.CyclicOrdering n)
    (hadj : ∀ k, w k ≠ w (DeformationMatrix.nextPosition n k)) :
    ∃ ρ γ : Fin n → R,
      additiveCycleWeight D w = (∑ i, ρ i) + ∑ i, γ i := by
  rcases hD with ⟨ρ, γ, hD⟩
  refine ⟨ρ, γ, ?_⟩
  simp_rw [additiveCycleWeight, hD _ _ (hadj _), Finset.sum_add_distrib]
  rw [Equiv.sum_comp w ρ]
  simpa only [Equiv.trans_apply] using congrArg
    (fun z ↦ (∑ i, ρ i) + z)
    (Equiv.sum_comp ((DeformationMatrix.nextPosition n).trans w) γ)

end CyclicBraidArrangement
