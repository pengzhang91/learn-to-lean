import LeanCo.CyclicBraidArrangement.CycleFormula
import Mathlib.Algebra.BigOperators.Sym

/-! Concrete gap vectors in the finite-field proof. -/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

/-- Remainder multisets parameterizing all admissible gap vectors for a fixed
cyclic ordering after subtracting the adjacent lower bounds. -/
abbrev FixedCycleGaps {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (q : ℕ) (w : CyclicOrdering n) :=
  GapRemainder n (q - n - M.cycleWeight w)

/-- The actual gap vector represented by a remainder multiset. -/
noncomputable def realizedGap {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (q : ℕ) (w : CyclicOrdering n) (s : M.FixedCycleGaps q w) (k : Fin n) : ℕ := by
  classical
  exact M.entry (w k) (w (nextPosition n k)) + (s : Multiset (Fin n)).count k

theorem adjacent_bound_realizedGap {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n)
    (s : M.FixedCycleGaps q w) (k : Fin n) :
    M.entry (w k) (w (nextPosition n k)) ≤ M.realizedGap q w s k := by
  classical
  simp [realizedGap]

/-- Remainder multisets give distinct numerical gap vectors. -/
theorem realizedGap_injective {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n) :
    Function.Injective (M.realizedGap q w) := by
  classical
  intro s t hst
  apply Sym.ext
  rw [Multiset.ext]
  intro k
  have hk := congrFun hst k
  simp only [realizedGap] at hk
  omega

/-- The realized gaps have total `q-n` whenever the adjacent lower bounds fit
around the circle. -/
theorem sum_realizedGap {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n)
    (hfit : n + M.cycleWeight w ≤ q) (s : M.FixedCycleGaps q w) :
    ∑ k, M.realizedGap q w s k = q - n := by
  classical
  simp only [realizedGap, Finset.sum_add_distrib]
  have hcount : (∑ k : Fin n, (s : Multiset (Fin n)).count k) =
      q - n - M.cycleWeight w := by
    rw [Multiset.sum_count_eq_card (s := Finset.univ) (by simp)]
    exact s.2
  change M.cycleWeight w + (∑ k : Fin n, (s : Multiset (Fin n)).count k) = q - n
  rw [hcount]
  omega

/-- Exact fixed-cycle count in the finite-field proof. -/
theorem card_fixedCycleGaps {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (q : ℕ) (w : CyclicOrdering n)
    (hfit : n + M.cycleWeight w ≤ q) :
    Fintype.card (M.FixedCycleGaps q w) =
      (q - M.cycleWeight w - 1).choose (n - 1) :=
  card_gapRemainder_shifted n q (M.cycleWeight w) hfit

/-- Equal-total two-sided extensions have equal cycle weights at each fixed
cyclic ordering. -/
theorem extend_cycleWeight_eq_of_parameter_total {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M : DeformationMatrix n)
    (α β α' β' : Fin n → ℕ)
    (htotal : (∑ i, α i) + ∑ i, β i =
      (∑ i, α' i) + ∑ i, β' i)
    (w : CyclicOrdering n) :
    (M.extend α β).cycleWeight w = (M.extend α' β').cycleWeight w := by
  apply cycleWeight_extend_eq_of_total_eq M α β α' β' w
  · intro k
    exact w.injective.ne (nextPosition_ne_self hn k).symm
  · exact htotal

/-- The direct fixed-order redistribution bijection from the finite-field
proof.  Both sides use the same remainder multiset because their adjacent
lower bounds have the same total. -/
noncomputable def fixedCycleGapsRedistributionEquiv {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M : DeformationMatrix n) (q : ℕ)
    (α β α' β' : Fin n → ℕ)
    (htotal : (∑ i, α i) + ∑ i, β i =
      (∑ i, α' i) + ∑ i, β' i)
    (w : CyclicOrdering n) :
    (M.extend α β).FixedCycleGaps q w ≃
      (M.extend α' β').FixedCycleGaps q w := by
  apply Equiv.cast
  unfold FixedCycleGaps
  rw [extend_cycleWeight_eq_of_parameter_total hn M α β α' β' htotal w]

end DeformationMatrix

end CyclicBraidArrangement
