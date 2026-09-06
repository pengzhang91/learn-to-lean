import LeanCo.CyclicBraidArrangement.ArrangementMainTheorem
import LeanCo.CyclicBraidArrangement.AdjacentPlacement
import LeanCo.CyclicBraidArrangement.AffineHullDirect
import LeanCo.CyclicBraidArrangement.WeakSumDirect
import LeanCo.CyclicBraidArrangement.CharacteristicCorollaries
import LeanCo.CyclicBraidArrangement.ArrangementPaperDefinition
import LeanCo.CyclicBraidArrangement.TransposeArrangement
import LeanCo.CyclicBraidArrangement.SharpnessExample
import LeanCo.CyclicBraidArrangement.ShiPartitionBridge
import LeanCo.CyclicBraidArrangement.BraidPartitionBridge
import LeanCo.CyclicBraidArrangement.FerrersFactorizationTheorem

/-!
# Paper-facing statements for arXiv:2608.29203

This module gives a compact interface indexed by the numbering in the paper.
Every theorem exported here is unconditional apart from the mathematical
hypotheses displayed in its statement.  In particular, the characteristic
polynomial endpoints use the independently defined Whitney polynomial and do
not take a finite-field specification or a gap-cardinality agreement as an
argument.

Proposition 4.3 and Corollaries 4.4--4.5 below are unconditional.  In
particular, Proposition 4.3 uses the proved cyclic deletion/insertion
equivalence rather than assuming the Ferrers-Shi factorization quoted in the
paper.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace PaperStatements

open DeformationMatrix

/-! ## Definition 1.1 and Theorem 1.2 -/

/-- Definition 1.1: cyclic compatibility of a deformation matrix. -/
abbrev DefinitionOneOne {n : ℕ} (M : DeformationMatrix n) : Prop :=
  M.CyclicallyCompatible

/-- Theorem 1.2, full characteristic-polynomial form. -/
theorem theorem_one_two_full {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (hM : DefinitionOneOne M) :
    M.whitneyCharacteristicPolynomial =
      Polynomial.X * cyclePolynomial M :=
  M.whitney_mainTheorem_full hM

/-- Theorem 1.2, reduced characteristic-polynomial form. -/
theorem theorem_one_two_reduced {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (hM : DefinitionOneOne M) :
    M.whitneyReducedCharacteristicPolynomial = cyclePolynomial M :=
  M.whitney_mainTheorem_reduced hM

/-- Theorem 1.2, displayed evaluation formula for the full polynomial. -/
theorem theorem_one_two_evaluation {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (hM : DefinitionOneOne M) (t : ℚ) :
    Polynomial.eval t M.whitneyCharacteristicPolynomial =
      t * cycleFormula M t :=
  M.eval_whitney_mainTheorem_full hM t

/-- Theorem 1.2, two-sided extension/translation statement. -/
theorem theorem_one_two_extension {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M : DeformationMatrix n) (hM : DefinitionOneOne M)
    (alpha beta : Fin n → ℕ) :
    (M.extend alpha beta).whitneyReducedCharacteristicPolynomial =
      translatePolynomial M.whitneyReducedCharacteristicPolynomial
        ((∑ i, alpha i) + ∑ i, beta i) :=
  M.whitneyReduced_extend_shift hn hM alpha beta

/-- Equal-total redistribution consequence used later in the paper. -/
theorem theorem_one_two_redistribution {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M : DeformationMatrix n) (hM : DefinitionOneOne M)
    (alpha beta alpha' beta' : Fin n → ℕ)
    (htotal : (∑ i, alpha i) + ∑ i, beta i =
      (∑ i, alpha' i) + ∑ i, beta' i) :
    (M.extend alpha beta).whitneyCharacteristicPolynomial =
      (M.extend alpha' beta').whitneyCharacteristicPolynomial :=
  M.whitney_redistribution hn hM alpha beta alpha' beta' htotal

/-! ## Proposition 2.2 -/

/-- Lemma 2.1 in the exact specialization used by the paper: above an
explicit threshold, the independently defined Whitney polynomial evaluates
to the literal modular complement cardinality.  This version is stronger
than the quoted prime-only statement because the modulus need only be
nonzero. -/
theorem lemma_two_one_for_difference_arrangements
    {n q : ℕ} [NeZero q] (M : DeformationMatrix n)
    (hq : M.equationStabilityBound ≤ q) :
    Polynomial.eval (q : ℚ) M.whitneyCharacteristicPolynomial =
      (Fintype.card (M.FiniteFieldComplement (ZMod q)) : ℚ) :=
  M.eval_whitneyCharacteristicPolynomial_eq_complementCard hq

/-- Proposition 2.2: cyclic compatibility is equivalent to adjacent-gap
sufficiency for every circular placement. -/
theorem proposition_two_two {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) :
    DefinitionOneOne M ↔ M.AdjacentSufficiencyProperty :=
  M.cyclicallyCompatible_iff_adjacentSufficiencyProperty

/-! ## Remarks 2.1 and 2.2 -/

/-- Remark 2.1: coordinate negation identifies a deformation with its
transpose without any compatibility assumption. -/
theorem remark_two_one_transpose {n : ℕ} (M : DeformationMatrix n) :
    M.transpose.whitneyCharacteristicPolynomial =
      M.whitneyCharacteristicPolynomial :=
  M.whitneyCharacteristicPolynomial_transpose

/-- Remark 2.1: transposition preserves cyclic compatibility. -/
theorem remark_two_one_transpose_compatibility {n : ℕ}
    (M : DeformationMatrix n) (hM : DefinitionOneOne M) :
    DefinitionOneOne M.transpose :=
  M.cyclicallyCompatible_transpose hM

/-- Remark 2.1: coordinate negation swaps the two extension parameters,
without requiring cyclic compatibility. -/
theorem remark_two_one_swapped_extension {n : ℕ}
    (M : DeformationMatrix n) (alpha beta : Fin n → ℕ) :
    (M.extend alpha beta).whitneyCharacteristicPolynomial =
      (M.transpose.extend beta alpha).whitneyCharacteristicPolynomial :=
  M.whitneyCharacteristicPolynomial_extend_transpose alpha beta

/-- Remark 2.1: after equal-total redistribution, the same two extension
parameters may be used on the transposed compatible matrix. -/
theorem remark_two_one_extended_transpose {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M : DeformationMatrix n) (hM : DefinitionOneOne M)
    (alpha beta : Fin n → ℕ) :
    (M.extend alpha beta).whitneyCharacteristicPolynomial =
      (M.transpose.extend alpha beta).whitneyCharacteristicPolynomial :=
  M.whitneyCharacteristicPolynomial_extend_transpose_sameParameters
    hn hM alpha beta

/-- Remark 2.2: the paper's incompatible three-label example violates the
shift formula for the actual independently defined reduced characteristic
polynomials. -/
theorem remark_two_two_sharpness :
    (SharpnessExample.matrix.extend SharpnessExample.alpha
        SharpnessExample.beta).whitneyReducedCharacteristicPolynomial ≠
      translatePolynomial
        SharpnessExample.matrix.whitneyReducedCharacteristicPolynomial
        (((∑ i, SharpnessExample.alpha i) +
          ∑ i, SharpnessExample.beta i : ℕ) : ℚ) :=
  SharpnessExample.whitneyReduced_shift_formula_fails

/-- Remark 2.2 in one paper-facing package: the example is incompatible,
both displayed polynomials are the actual independently defined reduced
Whitney polynomials, and the shift identity fails. -/
theorem remark_two_two_complete :
    ¬ DefinitionOneOne SharpnessExample.matrix ∧
    SharpnessExample.matrix.whitneyReducedCharacteristicPolynomial =
      SharpnessExample.basePolynomial ∧
    (SharpnessExample.matrix.extend SharpnessExample.alpha
        SharpnessExample.beta).whitneyReducedCharacteristicPolynomial =
      SharpnessExample.extendedPolynomial ∧
    (SharpnessExample.matrix.extend SharpnessExample.alpha
        SharpnessExample.beta).whitneyReducedCharacteristicPolynomial ≠
      translatePolynomial
        SharpnessExample.matrix.whitneyReducedCharacteristicPolynomial
        (((∑ i, SharpnessExample.alpha i) +
          ∑ i, SharpnessExample.beta i : ℕ) : ℚ) := by
  refine ⟨SharpnessExample.not_cyclicallyCompatible,
    SharpnessExample.whitneyReduced_base_eq_basePolynomial, ?_,
    SharpnessExample.whitneyReduced_shift_formula_fails⟩
  simpa [SharpnessExample.extendedMatrix] using
    SharpnessExample.whitneyReduced_extended_eq_extendedPolynomial

/-! ## Lemma 3.1 and Theorem 3.2 -/

/-- Lemma 3.1: Hamiltonian-cycle incidence differences span precisely the
balanced in/out-degree direction space. -/
theorem lemma_three_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    Submodule.span ℝ
        (WeakSumConverse.differenceSet
          (WeakSumConverse.cycleIncidence hn)) =
      LinearMap.ker (WeakSumConverse.degreeMap n) :=
  WeakSumConverse.span_cycleIncidence_differences_eq_balanced hn

/-- Theorem 3.2: constant Hamiltonian-cycle difference is equivalent to an
off-diagonal weak row-plus-column representation. -/
theorem theorem_three_two {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (M N : Fin n → Fin n → ℝ) :
    (∀ a b : DeformationMatrix.CyclicOrdering n,
      additiveCycleWeight N a - additiveCycleWeight M a =
        additiveCycleWeight N b - additiveCycleWeight M b) ↔
      IsWeakSum (fun i j ↦ N i j - M i j) :=
  WeakSumConverse.cycleWeight_difference_constant_iff_weakSum_direct hn M N

/-! ## Corollaries 4.1 and 4.2 -/

/-- Corollary 4.1: the uniform two-sided deformation, grouped by cyclic
Eulerian number. -/
theorem corollary_four_one {n u v : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alpha beta : Fin n → ℕ) (t : ℚ) :
    Polynomial.eval t
        ((uniform n u v).extend alpha beta).whitneyReducedCharacteristicPolynomial =
      ∑ d ∈ Finset.range (n - 1),
        (cyclicEulerianNumber n d : ℚ) *
          generalizedChoose
            (t - ((∑ i, alpha i) + ∑ i, beta i) -
              (((n : ℤ) * u + ((v : ℤ) - u) * (d + 1) : ℤ) : ℚ) - 1)
            (n - 1) :=
  whitneyReduced_uniform_eulerian hn alpha beta t

/-- Corollary 4.2, graphical Shi specialization. -/
theorem corollary_four_two_shi {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (alpha beta : Fin n → ℕ) (t : ℚ) :
    Polynomial.eval t
        ((graphicalShi G).extend alpha beta).whitneyReducedCharacteristicPolynomial =
      ∑ w : NormalizedCycle n,
        generalizedChoose
          (t - ((∑ i, alpha i) + ∑ i, beta i) -
            graphicalCyclicDescents G w.1 - 1)
          (n - 1) :=
  whitneyReduced_graphicalShi hn G alpha beta t

/-- Corollary 4.2, graphical Catalan specialization. -/
theorem corollary_four_two_catalan {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (alpha beta : Fin n → ℕ) (t : ℚ) :
    Polynomial.eval t
        ((graphicalCatalan G).extend alpha beta).whitneyReducedCharacteristicPolynomial =
      ∑ w : NormalizedCycle n,
        generalizedChoose
          (t - ((∑ i, alpha i) + ∑ i, beta i) -
            graphicalCyclicEdges G w.1 - 1)
          (n - 1) :=
  whitneyReduced_graphicalCatalan hn G alpha beta t

/-! ## Equation (4.1) and Proposition 4.3 -/

/-- Equation (4.1): unconditional Ferrers graphical-Shi factorization. -/
theorem equation_four_one {n : ℕ} [NeZero n]
    (C : Finset (Fin n)) (hC : (0 : Fin n) ∉ C) (t : ℚ) :
    cycleFormula (graphicalShi (ferrersGraph C)) t =
      ferrersShiFactorValue C t :=
  ferrersShiFactorization_direct C hC t

/-- Proposition 4.3: the reduced Whitney characteristic polynomial of an
integer row-and-column gauge of a Ferrers graphical-Shi deformation has the
displayed product factorization.  The factorization is proved internally;
there is no external finite-field-polynomial or insertion-law hypothesis. -/
theorem proposition_four_three {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (C : Finset (Fin n))
    (hC : (0 : Fin n) ∉ C)
    (M : DeformationMatrix n) (hM : DefinitionOneOne M)
    (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) =
        ((graphicalShi (ferrersGraph C)).entry i j : ℤ) + ρ i + γ j)
    (t : ℚ) :
    Polynomial.eval t M.whitneyReducedCharacteristicPolynomial =
      ferrersShiFactorValue C
        (t - (integerGaugeTotal ρ γ : ℚ)) :=
  proposition_four_three_whitney_direct
    hn C hC M hM ρ γ hentry t

/-! ## Corollary 4.4 -/

/-- Corollary 4.4: both displayed Shi partition expansions, proved directly
for arbitrary positive rank without a partition-convolution premise. -/
theorem corollary_four_four {n : ℕ} [NeZero n]
    (alpha : Fin n → ℕ) (t : ℚ) :
    shiPartitionPolynomialValue alpha t =
        regionConvolution t (shiRegionBlock alpha) ∧
      regionConvolution t (shiRegionBlock alpha) =
        boundedConvolution t (shiBoundedBlock alpha) :=
  ShiPartitionBridge.shi_partition_convolutions_direct alpha t

/-! ## Corollary 4.5 -/

/-- Corollary 4.5: both displayed braid partition expansions, proved
directly for arbitrary positive rank without a partition-convolution
premise. -/
theorem corollary_four_five {n : ℕ} [NeZero n]
    (alpha : Fin n → ℕ) (t : ℚ) :
    braidPartitionPolynomialValue alpha t =
        regionConvolution t (braidRegionBlock alpha) ∧
      regionConvolution t (braidRegionBlock alpha) =
        boundedConvolution t (braidBoundedBlock alpha) :=
  braid_partition_convolutions_direct alpha t

end PaperStatements

end CyclicBraidArrangement
