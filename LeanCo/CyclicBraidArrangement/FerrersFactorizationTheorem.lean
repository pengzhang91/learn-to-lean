import LeanCo.CyclicBraidArrangement.FerrersInsertionCardinality
import LeanCo.CyclicBraidArrangement.FerrersRecurrenceAlgebra

/-!
# Unconditional Ferrers graphical-Shi factorization

This file closes the increasing-label cyclic-insertion argument.  It first
proves, by deletion of the largest label, that the explicit Ferrers product
counts the independently defined anchored box placements.  The box model is
then compared with the genuine finite-field complement, yielding the concrete
insertion equivalence and the factorization and Proposition 4.3 endpoints
without any external factorization assumption.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

noncomputable section

/-- At every natural `q ≥ k+1`, the explicit Ferrers product counts safe
anchored cyclic-box placements on `k+1` labels. -/
theorem ferrersShiFactorValue_eq_card_anchored_succ
    (k q : ℕ) [NeZero q] (C : Finset (Fin (k + 1)))
    (hzero : (0 : Fin (k + 1)) ∉ C) (hq : k + 1 ≤ q) :
    ferrersShiFactorValue C q =
      (Fintype.card (AnchoredFerrersBoxPlacement
        (n := k + 1) (q := q) C) : ℚ) := by
  induction k generalizing q with
  | zero =>
      rw [card_anchoredFerrersBoxPlacement_fin_one q C hzero]
      have hC := ferrersColumns_fin_one_eq_empty C hzero
      subst C
      simp [ferrersShiFactorValue, fallingFactorialValue]
  | succ k ih =>
      letI : NeZero (k + 1) := ⟨by omega⟩
      letI : NeZero (k + 1 + 1) := ⟨by omega⟩
      let D := ferrersDropLastColumns C
      have hzeroD : (0 : Fin (k + 1)) ∉ D :=
        zero_not_mem_ferrersDropLastColumns C hzero
      by_cases htop : Fin.last (k + 1) ∈ C
      · cases q with
        | zero => omega
        | succ L =>
          have hqL : k + 1 ≤ L := by omega
          letI : NeZero L := ⟨by omega⟩
          have ihD := ih L D hzeroD hqL
          dsimp [D] at ihD
          rw [ferrersShiFactorValue_dropLast_of_mem C
            (((L + 1 : ℕ) : ℚ)) htop]
          rw [show (((L + 1 : ℕ) : ℚ) - 1) = (L : ℚ) by norm_num]
          rw [ihD]
          rw [card_anchoredFerrersBoxPlacement_dropLast_of_mem C htop]
          push_cast
          rw [Nat.cast_sub hqL]
          simp only [Nat.cast_add, Nat.cast_one]
          ring
      · have ihD := ih q D hzeroD (by omega)
        dsimp [D] at ihD
        rw [ferrersShiFactorValue_dropLast_of_not_mem C q hzero htop]
        rw [ihD]
        rw [card_anchoredFerrersBoxPlacement_dropLast_of_not_mem C htop]
        push_cast
        rw [Nat.cast_sub (by omega : k + 1 ≤ q)]
        simp only [Nat.cast_add, Nat.cast_one]
        ring

/-- Natural-evaluation counting theorem for every positive rank. -/
theorem ferrersShiFactorValue_eq_card_anchored
    {n q : ℕ} [NeZero n] [NeZero q] (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C) (hq : n ≤ q) :
    ferrersShiFactorValue C q =
      (Fintype.card (AnchoredFerrersBoxPlacement
        (n := n) (q := q) C) : ℚ) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  subst n
  exact ferrersShiFactorValue_eq_card_anchored_succ k q C hzero hq

/-- The concrete insertion equivalence required by the finite-field
factorization bridge.  No combinatorial law is assumed: the equivalence is
obtained from the explicit cyclic-box model and its proved cardinal formula. -/
theorem ferrersInsertionEquivalence_direct : FerrersInsertionEquivalence := by
  intro n _ C hzero q _ hq
  classical
  refine ⟨(anchoredFerrersComplementEquivBox C).trans ?_⟩
  apply Fintype.equivOfCardEq
  have hbox := ferrersShiFactorValue_eq_card_anchored C hzero hq
  have hdata := ferrersShiFactorValue_natCast_eq_card q C hzero hq
  exact_mod_cast hbox.symm.trans hdata

/-- The explicit Ferrers product is an unconditional reduced finite-field
polynomial for the graphical-Shi deformation. -/
theorem ferrersShiFactorPolynomial_isReducedFiniteFieldPolynomial_direct
    {n : ℕ} [NeZero n] (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C) :
    (graphicalShi (ferrersGraph C)).IsReducedFiniteFieldPolynomial
      (ferrersShiFactorPolynomial C) :=
  ferrersShiFactorPolynomial_isReducedFiniteFieldPolynomial
    ferrersInsertionEquivalence_direct C hzero

/-- Equation (4.1): the Ferrers graphical-Shi cycle formula factors as the
falling-factorial block times the height-indexed linear factors. -/
theorem ferrersShiFactorization_direct
    {n : ℕ} [NeZero n] (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C) (t : ℚ) :
    cycleFormula (graphicalShi (ferrersGraph C)) t =
      ferrersShiFactorValue C t :=
  ferrersShiFactorization_of_insertionEquivalence
    ferrersInsertionEquivalence_direct C hzero t

/-- Unconditional realization of the base factorization law used in the
paper's formulation of Proposition 4.3. -/
theorem ferrersShiFactorizationLaw_direct : FerrersShiFactorizationLaw :=
  fun C hzero t ↦ ferrersShiFactorization_direct C hzero t

/-- Proposition 4.3 at the cyclic-formula level, with no external Ferrers
factorization premise. -/
theorem proposition_four_three_cycleFormula_direct
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C)
    (M : DeformationMatrix n) (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) =
        ((graphicalShi (ferrersGraph C)).entry i j : ℤ) + ρ i + γ j)
    (t : ℚ) :
    cycleFormula M t = ferrersShiFactorValue C
      (t - (integerGaugeTotal ρ γ : ℚ)) :=
  proposition_four_three_cycleFormula_of_insertionEquivalence
    ferrersInsertionEquivalence_direct hn C hzero M ρ γ hentry t

/-- Proposition 4.3 for the independently defined Whitney reduced
characteristic polynomial, again with no external factorization premise. -/
theorem proposition_four_three_whitney_direct
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (C : Finset (Fin n))
    (hzero : (0 : Fin n) ∉ C)
    (M : DeformationMatrix n) (hcompat : M.CyclicallyCompatible)
    (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) =
        ((graphicalShi (ferrersGraph C)).entry i j : ℤ) + ρ i + γ j)
    (t : ℚ) :
    Polynomial.eval t M.whitneyReducedCharacteristicPolynomial =
      ferrersShiFactorValue C
        (t - (integerGaugeTotal ρ γ : ℚ)) :=
  proposition_four_three_whitney_of_insertionEquivalence
    ferrersInsertionEquivalence_direct hn C hzero M hcompat ρ γ hentry t

end

end DeformationMatrix

end CyclicBraidArrangement
