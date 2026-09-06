import LeanCo.CyclicBraidArrangement.WeakSum
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Perm

/-! The cyclic binomial sum and its two-sided shift identity. -/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

/-- Cyclic orderings modulo rotation, represented uniquely by putting label
`0` in the first position. -/
abbrev NormalizedCycle (n : ℕ) [NeZero n] :=
  {w : CyclicOrdering n // w 0 = 0}

noncomputable instance normalizedCycleFintype (n : ℕ) [NeZero n] :
    Fintype (NormalizedCycle n) := Fintype.ofFinite _

theorem nextPosition_ne_self {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : Fin n) :
    nextPosition n k ≠ k := by
  intro h
  have h1 : (1 : Fin n) = 0 := by
    exact add_left_cancel (show k + 1 = k + 0 by simpa [nextPosition] using h)
  have : (1 : ℕ) % n = 0 := congrArg Fin.val h1
  simp [Nat.mod_eq_of_lt (by omega : 1 < n)] at this

theorem normalizedCycle_adjacent_ne {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (w : NormalizedCycle n) (k : Fin n) :
    w.1 k ≠ w.1 (nextPosition n k) :=
  w.1.injective.ne (nextPosition_ne_self hn k).symm

/-- Permutations fixing `0` are exactly permutations of the complementary
subtype. -/
noncomputable def normalizedCycleEquivPermNonzero (n : ℕ) [NeZero n] :
    NormalizedCycle n ≃ Equiv.Perm {i : Fin n // i ≠ 0} := by
  classical
  let e₁ := Equiv.Perm.subtypeEquivSubtypePerm (fun i : Fin n ↦ i ≠ 0)
  let e₂ : {f : Equiv.Perm (Fin n) // ∀ a, ¬a ≠ 0 → f a = a} ≃
      NormalizedCycle n :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro f
      constructor
      · intro h
        exact h 0 (by simp)
      · intro h a ha
        have : a = 0 := not_ne_iff.mp ha
        simpa [this] using h)
  exact e₂.symm.trans e₁.symm

/-- There are `(n-1)!` cyclic orderings modulo rotation. -/
theorem card_normalizedCycle (n : ℕ) [NeZero n] :
    Fintype.card (NormalizedCycle n) = (n - 1).factorial := by
  classical
  rw [Fintype.card_congr (normalizedCycleEquivPermNonzero n),
    Fintype.card_perm]
  congr 1
  rw [Fintype.card_subtype_compl (fun i : Fin n ↦ i = 0)]
  simp

end DeformationMatrix

/-- Polynomial binomial coefficient evaluated at a rational argument. -/
def generalizedChoose (x : ℚ) (k : ℕ) : ℚ :=
  (∏ i ∈ Finset.range k, (x - i)) / k.factorial

/-- The reduced characteristic-polynomial expression furnished by the
finite-field gap enumeration. -/
noncomputable def cycleFormula {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (t : ℚ) : ℚ :=
  ∑ w : DeformationMatrix.NormalizedCycle n,
    generalizedChoose (t - M.cycleWeight w.1 - 1) (n - 1)

theorem cycleFormula_extend_shift {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (M : DeformationMatrix n) (α β : Fin n → ℕ) (t : ℚ) :
    cycleFormula (M.extend α β) t =
      cycleFormula M (t - ((∑ i, α i) + ∑ i, β i)) := by
  classical
  unfold cycleFormula
  apply Finset.sum_congr rfl
  intro w hw
  rw [M.cycleWeight_extend α β w.1
    (DeformationMatrix.normalizedCycle_adjacent_ne hn w)]
  congr 2
  push_cast
  ring

theorem cycleFormula_redistribution {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (M : DeformationMatrix n) (α β α' β' : Fin n → ℕ)
    (h : (∑ i, α i) + ∑ i, β i = (∑ i, α' i) + ∑ i, β' i)
    (t : ℚ) :
    cycleFormula (M.extend α β) t = cycleFormula (M.extend α' β') t := by
  rw [cycleFormula_extend_shift hn, cycleFormula_extend_shift hn]
  congr 2
  norm_cast

end CyclicBraidArrangement
