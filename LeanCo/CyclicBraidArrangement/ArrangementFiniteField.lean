import LeanCo.CyclicBraidArrangement.ArrangementStability

/-!
# Finite-field evaluation of the independent Whitney polynomial

Combining subset inclusion--exclusion with the large-modulus lifting theorem
gives the finite-field method for this specific integral difference
arrangement, rather than taking it as an external hypothesis.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

variable {n q : ℕ}

noncomputable local instance integrallyConsistentDecidableFF
    (M : DeformationMatrix n) (S : Finset M.ForbiddenEquation) :
    Decidable (M.IntegrallyConsistent S) := Classical.propDecidable _

private theorem card_equationSolutions_zmod_piecewise
    (M : DeformationMatrix n) (S : Finset M.ForbiddenEquation)
    [NeZero q] (hq : M.equationStabilityBound ≤ q) :
    (Fintype.card (M.EquationSolutions (ZMod q) S) : ℤ) =
      if M.IntegrallyConsistent S then
        (q : ℤ) ^ M.equationComponentCount S
      else 0 := by
  classical
  by_cases hS : M.IntegrallyConsistent S
  · rw [if_pos hS, M.card_equationSolutions_of_integrallyConsistent
      (ZMod q) S hS, ZMod.card q]
    norm_cast
  · rw [if_neg hS]
    have hEmpty : IsEmpty (M.EquationSolutions (ZMod q) S) :=
      ⟨fun x ↦ hS (M.integrallyConsistent_of_equationSolutions_zmod S hq x)⟩
    letI := hEmpty
    simp

/-- Whitney evaluation equals the actual complement count for every nonzero
modulus above the explicit stability threshold.  No primality assumption is
needed for this specialized finite-field theorem. -/
theorem eval_whitneyCharacteristicPolynomial_eq_complementCard
    (M : DeformationMatrix n) [NeZero q]
    (hq : M.equationStabilityBound ≤ q) :
    Polynomial.eval (q : ℚ) M.whitneyCharacteristicPolynomial =
      (Fintype.card (M.FiniteFieldComplement (ZMod q)) : ℚ) := by
  classical
  have hIE := M.card_finiteFieldComplement_eq_inclusionExclusion (ZMod q)
  have hpieces :
      (Fintype.card (M.FiniteFieldComplement (ZMod q)) : ℤ) =
        ∑ S : Finset M.ForbiddenEquation,
          if M.IntegrallyConsistent S then
            (-1 : ℤ) ^ S.card *
              (q : ℤ) ^ M.equationComponentCount S
          else 0 := by
    rw [hIE]
    apply Finset.sum_congr rfl
    intro S hS
    rw [M.card_equationSolutions_zmod_piecewise S hq]
    by_cases hc : M.IntegrallyConsistent S <;> simp [hc]
  have hQ := congrArg (fun z : ℤ ↦ (z : ℚ)) hpieces
  rw [M.eval_whitneyCharacteristicPolynomial]
  symm
  simpa only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] using hQ

end DeformationMatrix

end CyclicBraidArrangement
