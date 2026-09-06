import LeanCo.CyclicBraidArrangement.GaugeShift
import Mathlib.Order.Partition.Finpartition

/-! Block factors in the Shi and braid partition-convolution identities. -/

namespace CyclicBraidArrangement

open scoped BigOperators

/-- Sum of the vertex parameters restricted to a block. -/
def blockParameterSum {n : ℕ} (α : Fin n → ℕ) (B : Finset (Fin n)) : ℕ :=
  ∑ i ∈ B, α i

theorem blockParameterSum_add {n : ℕ} (α β : Fin n → ℕ)
    (B : Finset (Fin n)) :
    blockParameterSum (α + β) B = blockParameterSum α B + blockParameterSum β B := by
  simp [blockParameterSum, Finset.sum_add_distrib]

/-- Rising factorial on natural arguments. -/
def risingFactorial (x k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (x + i)

@[simp] theorem risingFactorial_zero (x : ℕ) : risingFactorial x 0 = 1 := by
  simp [risingFactorial]

/-- Region block factor for the vertex-extended Shi arrangement. -/
def shiRegionBlock {n : ℕ} (α : Fin n → ℕ) (B : Finset (Fin n)) : ℕ :=
  (blockParameterSum α B + B.card + 1) ^ (B.card - 1)

/-- Bounded-region block factor for the vertex-extended Shi arrangement. -/
def shiBoundedBlock {n : ℕ} (α : Fin n → ℕ) (B : Finset (Fin n)) : ℕ :=
  (blockParameterSum α B + B.card - 1) ^ (B.card - 1)

/-- Region block factor for the vertex-extended braid arrangement. -/
def braidRegionBlock {n : ℕ} (α : Fin n → ℕ) (B : Finset (Fin n)) : ℕ :=
  risingFactorial (blockParameterSum α B + 2) (B.card - 1)

/-- Bounded-region block factor for the vertex-extended braid arrangement. -/
def braidBoundedBlock {n : ℕ} (α : Fin n → ℕ) (B : Finset (Fin n)) : ℕ :=
  risingFactorial (blockParameterSum α B) (B.card - 1)

@[simp] theorem shiRegionBlock_singleton {n : ℕ} (α : Fin n → ℕ) (i : Fin n) :
    shiRegionBlock α {i} = 1 := by simp [shiRegionBlock]

@[simp] theorem shiBoundedBlock_singleton {n : ℕ} (α : Fin n → ℕ) (i : Fin n) :
    shiBoundedBlock α {i} = 1 := by simp [shiBoundedBlock]

@[simp] theorem braidRegionBlock_singleton {n : ℕ} (α : Fin n → ℕ) (i : Fin n) :
    braidRegionBlock α {i} = 1 := by simp [braidRegionBlock]

@[simp] theorem braidBoundedBlock_singleton {n : ℕ} (α : Fin n → ℕ) (i : Fin n) :
    braidBoundedBlock α {i} = 1 := by simp [braidBoundedBlock]

/-- All four block factors in the two-sided identities are obtained by
replacing `α` by the pointwise sum `α+β`. -/
theorem twoSided_blockParameterSum {n : ℕ} (α β : Fin n → ℕ)
    (B : Finset (Fin n)) :
    blockParameterSum (α + β) B =
      blockParameterSum α B + blockParameterSum β B :=
  blockParameterSum_add α β B

/-- Set partitions of `[n]`, represented by Mathlib finite partitions of the
universal finset. -/
abbrev SetPartition (n : ℕ) := Finpartition (Finset.univ : Finset (Fin n))

/-- Product of a block weight over a set partition. -/
def partitionBlockProduct {n : ℕ} (weight : Finset (Fin n) → ℕ)
    (P : SetPartition n) : ℕ :=
  ∏ B ∈ P.parts, weight B

/-- Inner sum over partitions with exactly `ℓ` blocks, as it occurs in both
standard convolution formulas quoted by the paper. -/
noncomputable def partitionBlockSum {n : ℕ} (ℓ : ℕ)
    (weight : Finset (Fin n) → ℕ) : ℕ := by
  classical
  exact ∑ P : SetPartition n,
    if P.parts.card = ℓ then partitionBlockProduct weight P else 0

theorem partitionBlockSum_congr {n ℓ : ℕ}
    (f g : Finset (Fin n) → ℕ) (hfg : ∀ B, f B = g B) :
    partitionBlockSum ℓ f = partitionBlockSum ℓ g := by
  classical
  unfold partitionBlockSum partitionBlockProduct
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs
  · apply Finset.prod_congr rfl
    intro B hB
    exact hfg B
  · rfl

/-- Rational version of the inner partition sum used in the displayed
convolution identities. -/
noncomputable def partitionBlockSumRat {n : ℕ} (ℓ : ℕ)
    (weight : Finset (Fin n) → ℕ) : ℚ :=
  ∑ P : SetPartition n,
    if P.parts.card = ℓ then (partitionBlockProduct weight P : ℚ) else 0

/-- Region-form convolution expression. -/
noncomputable def regionConvolution {n : ℕ} (t : ℚ)
    (weight : Finset (Fin n) → ℕ) : ℚ :=
  (-1 : ℚ) ^ n * ∑ ℓ ∈ Finset.Icc 1 n,
    (ℓ.factorial : ℚ) * generalizedChoose (-t) ℓ * partitionBlockSumRat ℓ weight

/-- Bounded-region-form convolution expression. -/
noncomputable def boundedConvolution {n : ℕ} (t : ℚ)
    (weight : Finset (Fin n) → ℕ) : ℚ :=
  ∑ ℓ ∈ Finset.Icc 1 n,
    (-1 : ℚ) ^ (n - ℓ) * (ℓ.factorial : ℚ) *
      generalizedChoose t ℓ * partitionBlockSumRat ℓ weight

/-- Left side of the extended-Shi partition identity. -/
def shiPartitionPolynomialValue {n : ℕ} (α : Fin n → ℕ) (t : ℚ) : ℚ :=
  t * (t - (∑ i, α i) - n) ^ (n - 1)

/-- Left side of the extended-braid partition identity. -/
def braidPartitionPolynomialValue {n : ℕ} (α : Fin n → ℕ) (t : ℚ) : ℚ :=
  t * ∏ i ∈ Finset.range (n - 1), (t - (∑ j, α j) - 1 - i)

end CyclicBraidArrangement
