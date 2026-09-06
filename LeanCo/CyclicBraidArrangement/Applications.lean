import LeanCo.CyclicBraidArrangement.CharacteristicBridge
import LeanCo.CyclicBraidArrangement.Graphical
import LeanCo.CyclicBraidArrangement.PartitionWeights

/-!
# Section 4: Ferrers and partition-convolution applications

This file formalizes Proposition 4.3 and Corollaries 4.4--4.5 of the paper.
The two results quoted from the literature are kept visible as reusable
interfaces:

* `FerrersShiFactorizationLaw` is the base graphical-Shi factorization;
* `PartitionConvolutionLaw` is the pair of standard region and bounded-region
  convolution formulas.

Neither interface assumes the specialized conclusion for the shifted Ferrers
matrix or for either concrete family of block weights.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

/-! ## Integer row-and-column gauges -/

/-- Total of an integer row potential and an integer column potential. -/
def integerGaugeTotal {n : ℕ} (ρ γ : Fin n → ℤ) : ℤ :=
  (∑ i, ρ i) + ∑ i, γ i

/-- The cycle-weight shift remains valid for integer potentials.  The matrix
entries themselves are natural numbers; the casted off-diagonal identity is
exactly the nonnegativity proviso in Proposition 4.3. -/
theorem cycleWeight_eq_of_offdiag_integerGauge {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M N : DeformationMatrix n) (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) = (N.entry i j : ℤ) + ρ i + γ j)
    (w : CyclicOrdering n) :
    (M.cycleWeight w : ℤ) =
      (N.cycleWeight w : ℤ) + integerGaugeTotal ρ γ := by
  have hadj : ∀ k, w k ≠ w (nextPosition n k) := fun k ↦
    w.injective.ne (nextPosition_ne_self hn k).symm
  rw [cycleWeight, cycleWeight]
  push_cast
  simp_rw [hentry _ _ (hadj _)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Equiv.sum_comp w ρ]
  have hγ : (∑ k, γ (w (nextPosition n k))) = ∑ i, γ i := by
    simpa only [Equiv.trans_apply] using
      Equiv.sum_comp ((nextPosition n).trans w) γ
  rw [hγ]
  simp [integerGaugeTotal, add_assoc]

/-- Integer-gauge form of the cycle formula, with no artificial sign
restriction on the row and column potentials. -/
theorem cycleFormula_integerGauge_shift {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M N : DeformationMatrix n) (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) = (N.entry i j : ℤ) + ρ i + γ j)
    (t : ℚ) :
    cycleFormula M t =
      cycleFormula N (t - (integerGaugeTotal ρ γ : ℚ)) := by
  classical
  unfold cycleFormula
  apply Finset.sum_congr rfl
  intro w hw
  have hwgt := cycleWeight_eq_of_offdiag_integerGauge hn M N ρ γ hentry w.1
  have hwgtQ : (M.cycleWeight w.1 : ℚ) =
      (N.cycleWeight w.1 : ℚ) + (integerGaugeTotal ρ γ : ℚ) := by
    exact_mod_cast hwgt
  rw [hwgtQ]
  congr 2
  ring

/-- Polynomial form of the integer-gauge shift. -/
theorem cyclePolynomial_integerGauge_shift {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (M N : DeformationMatrix n) (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) = (N.entry i j : ℤ) + ρ i + γ j) :
    cyclePolynomial M =
      translatePolynomial (cyclePolynomial N) (integerGaugeTotal ρ γ : ℚ) := by
  apply Polynomial.funext
  intro t
  rw [eval_cyclePolynomial, eval_translatePolynomial, eval_cyclePolynomial]
  exact cycleFormula_integerGauge_shift hn M N ρ γ hentry t

/-! ## Ferrers graphical Shi factorization -/

/-- The Ferrers graph encoded by its set `C` of column vertices: `{b,c}` is
an edge precisely when `c ∈ C` and `b < c`. -/
def ferrersGraph {n : ℕ} (C : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj i j := (i < j ∧ j ∈ C) ∨ (j < i ∧ i ∈ C)
  symm.symm i j hij := hij.elim
    (fun h ↦ Or.inr ⟨h.1, h.2⟩)
    (fun h ↦ Or.inl ⟨h.1, h.2⟩)

@[simp] theorem ferrersGraph_adj {n : ℕ} (C : Finset (Fin n)) (i j : Fin n) :
    (ferrersGraph C).Adj i j ↔
      (i < j ∧ j ∈ C) ∨ (j < i ∧ i ∈ C) := Iff.rfl

/-- The height `h_j=c_j-j`: equivalently, the number of vertices outside
`C` lying below the column vertex `c`. -/
def ferrersHeight {n : ℕ} (C : Finset (Fin n)) (c : Fin n) : ℕ :=
  ((Finset.Iio c).filter fun b ↦ b ∉ C).card

/-- Falling-factorial evaluation used in the Ferrers product. -/
def fallingFactorialValue (x : ℚ) (k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, (x - i)

/-- The reduced Ferrers graphical-Shi factor from equation (4.1). -/
def ferrersShiFactorValue {n : ℕ} (C : Finset (Fin n)) (t : ℚ) : ℚ :=
  fallingFactorialValue (t - C.card - 1) (n - C.card - 1) *
    ∏ c ∈ C, (t - C.card - ferrersHeight C c)

/-- The external Ferrers-Shi result cited by the paper, isolated as a law
about every admissible base Ferrers graph.  It says nothing about a gauged
matrix `M`, so Proposition 4.3 below is a genuine specialization theorem. -/
def FerrersShiFactorizationLaw : Prop :=
  ∀ {n : ℕ} [NeZero n] (C : Finset (Fin n)),
    (0 : Fin n) ∉ C →
    ∀ t : ℚ,
      cycleFormula (graphicalShi (ferrersGraph C)) t =
        ferrersShiFactorValue C t

/-- Candidate-polynomial form of Proposition 4.3. -/
theorem proposition_four_three_cycleFormula
    (baseFactorization : FerrersShiFactorizationLaw)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (C : Finset (Fin n))
    (hC : (0 : Fin n) ∉ C)
    (M : DeformationMatrix n) (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) =
        ((graphicalShi (ferrersGraph C)).entry i j : ℤ) + ρ i + γ j)
    (t : ℚ) :
    cycleFormula M t = ferrersShiFactorValue C
      (t - (integerGaugeTotal ρ γ : ℚ)) := by
  rw [cycleFormula_integerGauge_shift hn M
    (graphicalShi (ferrersGraph C)) ρ γ hentry]
  exact baseFactorization C hC _

/-- Proposition 4.3 for an independently supplied reduced characteristic
polynomial satisfying the paper-exact sufficiently-large-prime finite-field
specification.  Cyclic compatibility is retained as an explicit paper
hypothesis, while the finite-field specification is the formal bridge from
the arrangement invariant to the constructed cyclic polynomial. -/
theorem proposition_four_three
    (baseFactorization : FerrersShiFactorizationLaw)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (C : Finset (Fin n))
    (hC : (0 : Fin n) ∉ C)
    (M : DeformationMatrix n) (hcompat : M.CyclicallyCompatible)
    (ρ γ : Fin n → ℤ)
    (hentry : ∀ i j, i ≠ j →
      (M.entry i j : ℤ) =
        ((graphicalShi (ferrersGraph C)).entry i j : ℤ) + ρ i + γ j)
    (P : Polynomial ℚ) (hP : M.IsReducedPrimeFiniteFieldPolynomial P)
    (t : ℚ) :
    Polynomial.eval t P = ferrersShiFactorValue C
      (t - (integerGaugeTotal ρ γ : ℚ)) := by
  rw [mainTheorem_reduced_eval_of_primeFiniteFieldSpecification M hcompat hP]
  exact proposition_four_three_cycleFormula baseFactorization hn C hC M ρ γ hentry t

end DeformationMatrix

/-! ## Standard partition convolutions and their two specializations -/

/-- Abstract data to which the standard partition convolution theorem
applies.  Its three functions are independent: the two fields record the
general region and bounded-region convolution laws. -/
structure PartitionConvolutionLaw (n : ℕ) where
  characteristicValue : ℚ → ℚ
  regionBlock : Finset (Fin n) → ℕ
  boundedBlock : Finset (Fin n) → ℕ
  regionFormula : ∀ t,
    characteristicValue t = regionConvolution t regionBlock
  boundedFormula : ∀ t,
    characteristicValue t = boundedConvolution t boundedBlock

/-- Partition sums only inspect nonempty blocks. -/
theorem partitionBlockSumRat_congr_nonempty {n ℓ : ℕ}
    (f g : Finset (Fin n) → ℕ)
    (hfg : ∀ B, B.Nonempty → f B = g B) :
    partitionBlockSumRat ℓ f = partitionBlockSumRat ℓ g := by
  classical
  unfold partitionBlockSumRat partitionBlockProduct
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs
  · congr 1
    apply Finset.prod_congr rfl
    intro B hB
    exact_mod_cast hfg B (P.nonempty_of_mem_parts hB)
  · rfl

/-- Region convolution is unchanged when block weights agree on nonempty
blocks. -/
theorem regionConvolution_congr_nonempty {n : ℕ} (t : ℚ)
    (f g : Finset (Fin n) → ℕ)
    (hfg : ∀ B, B.Nonempty → f B = g B) :
    regionConvolution t f = regionConvolution t g := by
  unfold regionConvolution
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [partitionBlockSumRat_congr_nonempty f g hfg]

/-- Bounded convolution is unchanged when block weights agree on nonempty
blocks. -/
theorem boundedConvolution_congr_nonempty {n : ℕ} (t : ℚ)
    (f g : Finset (Fin n) → ℕ)
    (hfg : ∀ B, B.Nonempty → f B = g B) :
    boundedConvolution t f = boundedConvolution t g := by
  unfold boundedConvolution
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [partitionBlockSumRat_congr_nonempty f g hfg]

/-- A concrete family realizes the vertex-extended Shi specialization of a
general partition-convolution law.  These are the earlier characteristic and
block-region results used in the paper, not either target partition identity. -/
structure IsShiConvolutionSpecialization {n : ℕ}
    (D : PartitionConvolutionLaw n) (α : Fin n → ℕ) : Prop where
  characteristicValue_eq : ∀ t,
    D.characteristicValue t = shiPartitionPolynomialValue α t
  regionBlock_eq : ∀ B, B.Nonempty →
    D.regionBlock B = shiRegionBlock α B
  boundedBlock_eq : ∀ B, B.Nonempty →
    D.boundedBlock B = shiBoundedBlock α B

/-- Corollary 4.4: the two Shi partition-convolution expansions. -/
theorem corollary_four_four_shi_partition_convolution {n : ℕ}
    (D : PartitionConvolutionLaw n) (α : Fin n → ℕ)
    (hD : IsShiConvolutionSpecialization D α) (t : ℚ) :
    shiPartitionPolynomialValue α t =
        regionConvolution t (shiRegionBlock α) ∧
      regionConvolution t (shiRegionBlock α) =
        boundedConvolution t (shiBoundedBlock α) := by
  have hregion : shiPartitionPolynomialValue α t =
      regionConvolution t (shiRegionBlock α) := by
    rw [← hD.characteristicValue_eq t, D.regionFormula]
    exact regionConvolution_congr_nonempty t D.regionBlock
      (shiRegionBlock α) hD.regionBlock_eq
  have hbounded : shiPartitionPolynomialValue α t =
      boundedConvolution t (shiBoundedBlock α) := by
    rw [← hD.characteristicValue_eq t, D.boundedFormula]
    exact boundedConvolution_congr_nonempty t D.boundedBlock
      (shiBoundedBlock α) hD.boundedBlock_eq
  exact ⟨hregion, hregion.symm.trans hbounded⟩

/-- A concrete family realizes the vertex-extended braid specialization of
the general partition-convolution law. -/
structure IsBraidConvolutionSpecialization {n : ℕ}
    (D : PartitionConvolutionLaw n) (α : Fin n → ℕ) : Prop where
  characteristicValue_eq : ∀ t,
    D.characteristicValue t = braidPartitionPolynomialValue α t
  regionBlock_eq : ∀ B, B.Nonempty →
    D.regionBlock B = braidRegionBlock α B
  boundedBlock_eq : ∀ B, B.Nonempty →
    D.boundedBlock B = braidBoundedBlock α B

/-- Corollary 4.5: the two braid partition-convolution expansions. -/
theorem corollary_four_five_braid_partition_convolution {n : ℕ}
    (D : PartitionConvolutionLaw n) (α : Fin n → ℕ)
    (hD : IsBraidConvolutionSpecialization D α) (t : ℚ) :
    braidPartitionPolynomialValue α t =
        regionConvolution t (braidRegionBlock α) ∧
      regionConvolution t (braidRegionBlock α) =
        boundedConvolution t (braidBoundedBlock α) := by
  have hregion : braidPartitionPolynomialValue α t =
      regionConvolution t (braidRegionBlock α) := by
    rw [← hD.characteristicValue_eq t, D.regionFormula]
    exact regionConvolution_congr_nonempty t D.regionBlock
      (braidRegionBlock α) hD.regionBlock_eq
  have hbounded : braidPartitionPolynomialValue α t =
      boundedConvolution t (braidBoundedBlock α) := by
    rw [← hD.characteristicValue_eq t, D.boundedFormula]
    exact boundedConvolution_congr_nonempty t D.boundedBlock
      (braidBoundedBlock α) hD.boundedBlock_eq
  exact ⟨hregion, hregion.symm.trans hbounded⟩

end CyclicBraidArrangement
