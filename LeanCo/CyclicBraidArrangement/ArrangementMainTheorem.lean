import LeanCo.CyclicBraidArrangement.ArrangementFiniteField
import LeanCo.CyclicBraidArrangement.AnchoredGapEquiv

/-!
# High-level bridge from the independent Whitney polynomial to Theorem 1.2

The only combinatorial input to this file is the cardinal equality between
anchored genuine complement points and safe normalized circle-gap data.  The
separate sorting/gap module supplies that equality.
-/

namespace CyclicBraidArrangement

namespace DeformationMatrix

variable {n : ℕ} [NeZero n]

/-- Exact statement needed from the order-and-gap encoding of anchored
finite-field complement points. -/
def AnchorGapCardAgreement (M : DeformationMatrix n) : Prop :=
  ∀ (q : ℕ) [NeZero q], n ≤ q →
    Fintype.card (M.AnchoredFiniteFieldComplement (ZMod q)) =
      M.finiteFieldComplementOrbitCount q

/-- The sorting-and-gap equivalence supplies the exact anchored cardinal
agreement for every deformation matrix; it is not an additional hypothesis. -/
theorem anchorGapCardAgreement (M : DeformationMatrix n) :
    M.AnchorGapCardAgreement := by
  intro q _ hq
  exact M.card_anchoredFiniteFieldComplement_eq_finiteFieldComplementOrbitCount hq

/-- The independent Whitney polynomial satisfies the stronger all-natural
full finite-field specification.  The explicit lower threshold simultaneously
ensures stability of integer equations and enough residues to sort all labels. -/
theorem whitney_isFullFiniteFieldPolynomial
    (M : DeformationMatrix n) :
    M.IsFullFiniteFieldPolynomial M.whitneyCharacteristicPolynomial := by
  classical
  let Q := max M.equationStabilityBound n
  refine ⟨Q, ?_⟩
  intro q hq
  have hstable : M.equationStabilityBound ≤ q :=
    (Nat.le_max_left _ _).trans hq
  have hnq : n ≤ q := (Nat.le_max_right _ _).trans hq
  letI : NeZero q := ⟨by exact Nat.ne_of_gt (lt_of_lt_of_le (NeZero.pos n) hnq)⟩
  rw [M.eval_whitneyCharacteristicPolynomial_eq_complementCard hstable]
  have hfull := M.card_finiteFieldComplement_eq_card_mul_anchor (ZMod q)
  rw [ZMod.card q,
    M.card_anchoredFiniteFieldComplement_eq_finiteFieldComplementOrbitCount hnq]
    at hfull
  exact_mod_cast hfull

/-- The independently defined Whitney polynomial satisfies the full
prime finite-field specification once anchored points are identified with
the already formalized safe-gap orbit model. -/
theorem whitney_isFullPrimeFiniteFieldPolynomial_of_anchorGapCardAgreement
    (M : DeformationMatrix n) (hgap : M.AnchorGapCardAgreement) :
    M.IsFullPrimeFiniteFieldPolynomial M.whitneyCharacteristicPolynomial := by
  classical
  let Q := max M.equationStabilityBound n
  refine ⟨Q, ?_⟩
  intro q hq hprime
  letI : NeZero q := ⟨hprime.ne_zero⟩
  have hstable : M.equationStabilityBound ≤ q :=
    (Nat.le_max_left _ _).trans hq
  have hnq : n ≤ q := (Nat.le_max_right _ _).trans hq
  rw [M.eval_whitneyCharacteristicPolynomial_eq_complementCard hstable]
  have hfull := M.card_zmodComplement_eq_prime_mul_anchor q hprime
  rw [hgap q hnq] at hfull
  exact_mod_cast hfull

/-- Full form of Theorem 1.2 for the independently defined Whitney
characteristic polynomial, with no finite-field-polynomial premise. -/
theorem whitney_mainTheorem_full_of_anchorGapCardAgreement
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (hgap : M.AnchorGapCardAgreement) :
    M.whitneyCharacteristicPolynomial =
      Polynomial.X * cyclePolynomial M :=
  M.mainTheorem_full_of_primeFiniteFieldSpecification hM
    (M.whitney_isFullPrimeFiniteFieldPolynomial_of_anchorGapCardAgreement hgap)

/-- Independent reduced characteristic polynomial obtained by removing the
diagonal translation factor from the Whitney polynomial. -/
noncomputable def whitneyReducedCharacteristicPolynomial
    (M : DeformationMatrix n) : Polynomial ℚ :=
  M.whitneyCharacteristicPolynomial.divX

/-- Reduced form of Theorem 1.2, derived from the full Whitney identity. -/
theorem whitney_mainTheorem_reduced_of_anchorGapCardAgreement
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (hgap : M.AnchorGapCardAgreement) :
    M.whitneyReducedCharacteristicPolynomial = cyclePolynomial M := by
  rw [whitneyReducedCharacteristicPolynomial,
    M.whitney_mainTheorem_full_of_anchorGapCardAgreement hM hgap]
  ext k
  simp [Polynomial.coeff_divX]

/-- Evaluation form of the paper's displayed full characteristic-polynomial
formula. -/
theorem eval_whitney_mainTheorem_full_of_anchorGapCardAgreement
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (hgap : M.AnchorGapCardAgreement) (t : ℚ) :
    Polynomial.eval t M.whitneyCharacteristicPolynomial =
      t * cycleFormula M t := by
  rw [M.whitney_mainTheorem_full_of_anchorGapCardAgreement hM hgap,
    Polynomial.eval_mul, Polynomial.eval_X, eval_cyclePolynomial]

/-- The reduced Whitney polynomial obeys the paper's two-sided translation
law. -/
theorem whitneyReduced_extend_shift_of_anchorGapCardAgreements
    (hn : 2 ≤ n) (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) (hgap : M.AnchorGapCardAgreement)
    (α β : Fin n → ℕ)
    (hgapExt : (M.extend α β).AnchorGapCardAgreement) :
    (M.extend α β).whitneyReducedCharacteristicPolynomial =
      translatePolynomial M.whitneyReducedCharacteristicPolynomial
        ((∑ i, α i) + ∑ i, β i) := by
  calc
    (M.extend α β).whitneyReducedCharacteristicPolynomial =
        cyclePolynomial (M.extend α β) :=
      (M.extend α β).whitney_mainTheorem_reduced_of_anchorGapCardAgreement
        (M.cyclicallyCompatible_extend hM α β) hgapExt
    _ = translatePolynomial (cyclePolynomial M)
        ((∑ i, α i) + ∑ i, β i) :=
      cyclePolynomial_extend_shift hn M α β
    _ = translatePolynomial M.whitneyReducedCharacteristicPolynomial
        ((∑ i, α i) + ∑ i, β i) := by
      rw [M.whitney_mainTheorem_reduced_of_anchorGapCardAgreement hM hgap]

/-- Equal-total two-sided extensions have the same independently defined
Whitney characteristic polynomial. -/
theorem whitney_redistribution_of_anchorGapCardAgreements
    (hn : 2 ≤ n) (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    (α β α' β' : Fin n → ℕ)
    (htotal : (∑ i, α i) + ∑ i, β i =
      (∑ i, α' i) + ∑ i, β' i)
    (hgapExt : (M.extend α β).AnchorGapCardAgreement)
    (hgapExt' : (M.extend α' β').AnchorGapCardAgreement) :
    (M.extend α β).whitneyCharacteristicPolynomial =
      (M.extend α' β').whitneyCharacteristicPolynomial := by
  rw [(M.extend α β).whitney_mainTheorem_full_of_anchorGapCardAgreement
      (M.cyclicallyCompatible_extend hM α β) hgapExt,
    (M.extend α' β').whitney_mainTheorem_full_of_anchorGapCardAgreement
      (M.cyclicallyCompatible_extend hM α' β') hgapExt']
  congr 1
  exact cyclePolynomial_redistribution hn M α β α' β' htotal

/-! ## Unconditional arrangement endpoints

The preceding conditional statements expose the one combinatorial interface
used by the construction.  The explicit sorting equivalence proves that
interface, so the paper-facing results below carry no finite-field-polynomial
or cardinal-agreement premise.
-/

/-- Paper-exact prime-only specification, now discharged for the independently
defined Whitney polynomial. -/
theorem whitney_isFullPrimeFiniteFieldPolynomial
    (M : DeformationMatrix n) :
    M.IsFullPrimeFiniteFieldPolynomial M.whitneyCharacteristicPolynomial :=
  isFullFiniteFieldPolynomial_toPrime M
    M.whitney_isFullFiniteFieldPolynomial

/-- Full form of Theorem 1.2 for the independently defined arrangement
characteristic polynomial, with no external finite-field assumption. -/
theorem whitney_mainTheorem_full
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible) :
    M.whitneyCharacteristicPolynomial =
      Polynomial.X * cyclePolynomial M :=
  M.mainTheorem_full_of_finiteFieldSpecification hM
    M.whitney_isFullFiniteFieldPolynomial

/-- Reduced form of Theorem 1.2 for the independently defined arrangement
characteristic polynomial. -/
theorem whitney_mainTheorem_reduced
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible) :
    M.whitneyReducedCharacteristicPolynomial = cyclePolynomial M :=
  M.whitney_mainTheorem_reduced_of_anchorGapCardAgreement hM
    M.anchorGapCardAgreement

/-- Evaluation form of the full characteristic-polynomial identity. -/
theorem eval_whitney_mainTheorem_full
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible) (t : ℚ) :
    Polynomial.eval t M.whitneyCharacteristicPolynomial =
      t * cycleFormula M t := by
  rw [M.whitney_mainTheorem_full hM, Polynomial.eval_mul,
    Polynomial.eval_X, eval_cyclePolynomial]

/-- The reduced independent Whitney polynomial obeys the paper's two-sided
extension shift, without separately supplied characteristic polynomials. -/
theorem whitneyReduced_extend_shift
    (hn : 2 ≤ n) (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) (α β : Fin n → ℕ) :
    (M.extend α β).whitneyReducedCharacteristicPolynomial =
      translatePolynomial M.whitneyReducedCharacteristicPolynomial
        ((∑ i, α i) + ∑ i, β i) :=
  M.whitneyReduced_extend_shift_of_anchorGapCardAgreements hn hM
    M.anchorGapCardAgreement α β (M.extend α β).anchorGapCardAgreement

/-- Equal-total two-sided extensions have the same independent Whitney
characteristic polynomial, with no external agreement assumptions. -/
theorem whitney_redistribution
    (hn : 2 ≤ n) (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    (α β α' β' : Fin n → ℕ)
    (htotal : (∑ i, α i) + ∑ i, β i =
      (∑ i, α' i) + ∑ i, β' i) :
    (M.extend α β).whitneyCharacteristicPolynomial =
      (M.extend α' β').whitneyCharacteristicPolynomial :=
  M.whitney_redistribution_of_anchorGapCardAgreements hn hM α β α' β'
    htotal (M.extend α β).anchorGapCardAgreement
      (M.extend α' β').anchorGapCardAgreement

end DeformationMatrix

end CyclicBraidArrangement
