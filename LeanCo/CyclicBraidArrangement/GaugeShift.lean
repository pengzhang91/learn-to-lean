import LeanCo.CyclicBraidArrangement.CyclePolynomial

/-! Off-diagonal gauge shifts and the Ferrers application mechanism. -/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

/-- An independently presented matrix with off-diagonal entries differing by
row and column potentials has the expected shifted cycle weight. -/
theorem cycleWeight_eq_of_offdiag_gauge {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M N : DeformationMatrix n) (ρ γ : Fin n → ℕ)
    (hentry : ∀ i j, i ≠ j → M.entry i j = N.entry i j + ρ i + γ j)
    (w : CyclicOrdering n) :
    M.cycleWeight w = N.cycleWeight w + ∑ i, ρ i + ∑ i, γ i := by
  have hadj : ∀ k, w k ≠ w (nextPosition n k) := fun k ↦
    w.injective.ne (nextPosition_ne_self hn k).symm
  simp_rw [cycleWeight, hentry _ _ (hadj _), Finset.sum_add_distrib]
  rw [Equiv.sum_comp w ρ]
  have hγ : (∑ k, γ (w (nextPosition n k))) = ∑ i, γ i := by
    simpa only [Equiv.trans_apply] using
      Equiv.sum_comp ((nextPosition n).trans w) γ
  rw [hγ]

/-- General gauge-shift form of the reduced characteristic expression. -/
theorem cycleFormula_gauge_shift {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M N : DeformationMatrix n) (ρ γ : Fin n → ℕ)
    (hentry : ∀ i j, i ≠ j → M.entry i j = N.entry i j + ρ i + γ j)
    (t : ℚ) :
    cycleFormula M t = cycleFormula N (t - ((∑ i, ρ i) + ∑ i, γ i)) := by
  classical
  unfold cycleFormula
  apply Finset.sum_congr rfl
  intro w hw
  rw [cycleWeight_eq_of_offdiag_gauge hn M N ρ γ hentry w.1]
  congr 2
  push_cast
  ring

/-- Polynomial version of the gauge-shift theorem. -/
theorem cyclePolynomial_gauge_shift {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M N : DeformationMatrix n) (ρ γ : Fin n → ℕ)
    (hentry : ∀ i j, i ≠ j → M.entry i j = N.entry i j + ρ i + γ j) :
    cyclePolynomial M =
      translatePolynomial (cyclePolynomial N) ((∑ i, ρ i) + ∑ i, γ i) := by
  apply Polynomial.funext
  intro t
  rw [eval_cyclePolynomial, eval_translatePolynomial, eval_cyclePolynomial]
  exact cycleFormula_gauge_shift hn M N ρ γ hentry t

/-- Consequently, any known factorization of a base cycle polynomial remains
valid after replacing its variable by the total gauge shift. -/
theorem gauge_preserves_factorization {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M N : DeformationMatrix n) (ρ γ : Fin n → ℕ)
    (hentry : ∀ i j, i ≠ j → M.entry i j = N.entry i j + ρ i + γ j)
    (P : Polynomial ℚ) (hN : cyclePolynomial N = P) :
    cyclePolynomial M =
      translatePolynomial P ((∑ i, ρ i) + ∑ i, γ i) := by
  rw [cyclePolynomial_gauge_shift hn M N ρ γ hentry, hN]

end DeformationMatrix

end CyclicBraidArrangement
