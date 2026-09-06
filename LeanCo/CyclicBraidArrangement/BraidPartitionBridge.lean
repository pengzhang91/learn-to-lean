import LeanCo.CyclicBraidArrangement.PartitionIdentitiesDirect
import LeanCo.CyclicBraidArrangement.BraidPartitionIdentityDirect

/-!
# Direct endpoint wiring for Corollary 4.5

This file specializes the generic falling-factorial partition identity to
the two braid block weights and connects it to the paper's convolution
notation.  No convolution law is assumed.
-/

namespace CyclicBraidArrangement

open scoped BigOperators
open BraidPartitionIdentityDirect

noncomputable section

theorem fallingValue_eq_rationalFallingFactorial (z : ℚ) (k : ℕ) :
    fallingValue z k = rationalFallingFactorial z k := by
  rw [fallingValue_eq_prod_range]
  rfl

theorem braidRegionBlock_cast_eq_fallingValue {n : ℕ}
    (α : Fin n → ℕ) (B : Finset (Fin n)) (_hB : B.Nonempty) :
    (braidRegionBlock α B : ℚ) =
      fallingValue (∑ i ∈ B, ((α i : ℚ) + 1)) (B.card - 1) := by
  exact cast_braidRegionBlock_eq_fallingValue_sum α B

theorem braidBoundedBlock_signed_cast_eq_fallingValue {n : ℕ}
    (α : Fin n → ℕ) (B : Finset (Fin n)) :
    (-1 : ℚ) ^ (B.card - 1) * (braidBoundedBlock α B : ℚ) =
      fallingValue (∑ i ∈ B, -(α i : ℚ)) (B.card - 1) := by
  rw [sign_mul_cast_braidBoundedBlock_eq_fallingValue_sum_neg]
  congr 2
  simp

theorem setPartition_block_defect_sum {n : ℕ} (P : SetPartition n) :
    (∑ B ∈ P.parts, (B.card - 1)) = n - P.parts.card := by
  have hplus :
      (∑ B ∈ P.parts, (B.card - 1)) + P.parts.card = n := by
    calc
      (∑ B ∈ P.parts, (B.card - 1)) + P.parts.card =
          ∑ B ∈ P.parts, ((B.card - 1) + 1) := by
            rw [Finset.sum_add_distrib]
            simp
      _ = ∑ B ∈ P.parts, B.card := by
            apply Finset.sum_congr rfl
            intro B hB
            exact Nat.sub_add_cancel
              (Finset.one_le_card.mpr (P.nonempty_of_mem_parts hB))
      _ = n := by simpa using P.sum_card_parts
  omega

theorem setPartition_sign_eq_block_signs {n : ℕ} (P : SetPartition n) :
    (-1 : ℚ) ^ (n - P.parts.card) =
      ∏ B ∈ P.parts, (-1 : ℚ) ^ (B.card - 1) := by
  rw [← setPartition_block_defect_sum P]
  exact (Finset.prod_pow_eq_pow_sum P.parts
    (fun B ↦ B.card - 1) (-1 : ℚ)).symm

theorem partitionFallingSum_braidRegion_eq_fallingPartitionSum {n : ℕ}
    (u : ℚ) (α : Fin n → ℕ) :
    partitionFallingSum u (braidRegionBlock α) =
      fallingPartitionSumOn Finset.univ u (fun i ↦ (α i : ℚ) + 1) := by
  classical
  unfold partitionFallingSum fallingPartitionSumOn partitionBlockProduct
  apply Finset.sum_congr rfl
  intro P hP
  rw [← fallingValue_eq_rationalFallingFactorial]
  congr 1
  push_cast
  apply Finset.prod_congr rfl
  intro B hB
  exact braidRegionBlock_cast_eq_fallingValue α B
    (P.nonempty_of_mem_parts hB)

theorem boundedBraidPartitionSum_eq_fallingPartitionSum {n : ℕ}
    (t : ℚ) (α : Fin n → ℕ) :
    (∑ P : SetPartition n,
        (-1 : ℚ) ^ (n - P.parts.card) *
          rationalFallingFactorial t P.parts.card *
          (partitionBlockProduct (braidBoundedBlock α) P : ℚ)) =
      fallingPartitionSumOn Finset.univ t (fun i ↦ -(α i : ℚ)) := by
  classical
  unfold fallingPartitionSumOn partitionBlockProduct
  apply Finset.sum_congr rfl
  intro P hP
  rw [← fallingValue_eq_rationalFallingFactorial,
    setPartition_sign_eq_block_signs]
  push_cast
  calc
    (∏ B ∈ P.parts, (-1 : ℚ) ^ (B.card - 1)) *
          fallingValue t P.parts.card *
          ∏ B ∈ P.parts, (braidBoundedBlock α B : ℚ) =
        fallingValue t P.parts.card *
          ((∏ B ∈ P.parts, (-1 : ℚ) ^ (B.card - 1)) *
            ∏ B ∈ P.parts, (braidBoundedBlock α B : ℚ)) := by ring
    _ = fallingValue t P.parts.card *
          ∏ B ∈ P.parts,
            ((-1 : ℚ) ^ (B.card - 1) *
              (braidBoundedBlock α B : ℚ)) := by
          rw [Finset.prod_mul_distrib]
    _ = fallingValue t P.parts.card *
          ∏ B ∈ P.parts,
            fallingValue (∑ i ∈ B, -(α i : ℚ)) (B.card - 1) := by
          congr 1
          apply Finset.prod_congr rfl
          intro B hB
          exact braidBoundedBlock_signed_cast_eq_fallingValue α B

theorem sum_cast_add_one_fin {n : ℕ} (α : Fin n → ℕ) :
    (∑ i, ((α i : ℚ) + 1)) = (∑ i, α i : ℕ) + n := by
  push_cast
  simp [Finset.sum_add_distrib]

theorem sum_neg_cast_fin {n : ℕ} (α : Fin n → ℕ) :
    (∑ i, -(α i : ℚ)) = -(∑ i, α i : ℕ) := by
  push_cast
  simp

/-- Corollary 4.5, region-form equality, with no external convolution
premise. -/
theorem braid_regionConvolution_direct {n : ℕ} [NeZero n]
    (α : Fin n → ℕ) (t : ℚ) :
    regionConvolution t (braidRegionBlock α) =
      braidPartitionPolynomialValue α t := by
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [regionConvolution_eq_partitionFallingSum,
    partitionFallingSum_braidRegion_eq_fallingPartitionSum,
    fallingPartitionSumOn_closed, if_neg Finset.univ_nonempty.ne_empty]
  rw [sum_cast_add_one_fin]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.succ_sub_one]
  rw [Nat.cast_succ]
  have harg :
      -t + ((∑ i, α i : ℕ) + (k + 1)) - 1 =
        -(t - (∑ i, α i : ℕ) - 1) + (k : ℚ) - 1 := by
    push_cast
    ring
  rw [harg, fallingValue_reflect, fallingValue_eq_prod_range]
  unfold braidPartitionPolynomialValue
  simp only [Nat.succ_sub_one]
  have hsign :
      (-1 : ℚ) ^ (k + 1) * (-1) * (-1 : ℚ) ^ k = 1 := by
    calc
      (-1 : ℚ) ^ (k + 1) * (-1) * (-1 : ℚ) ^ k =
          (-1 : ℚ) ^ k * (-1 : ℚ) ^ k := by
            rw [pow_succ]
            ring
      _ = (-1 : ℚ) ^ (k + k) := by rw [pow_add]
      _ = 1 := by
        rw [show k + k = 2 * k by omega, pow_mul]
        norm_num
  calc
    (-1 : ℚ) ^ (k + 1) *
          (-t * ((-1 : ℚ) ^ k *
            ∏ i ∈ Finset.range k,
              (t - (∑ i, α i : ℕ) - 1 - i))) =
        ((-1 : ℚ) ^ (k + 1) * (-1) * (-1 : ℚ) ^ k) *
          (t * ∏ i ∈ Finset.range k,
            (t - (∑ i, α i : ℕ) - 1 - i)) := by ring
    _ = t * ∏ i ∈ Finset.range k,
          (t - (∑ i, α i : ℕ) - 1 - i) := by rw [hsign]; ring

/-- Corollary 4.5, bounded-form equality, with no external convolution
premise. -/
theorem braid_boundedConvolution_direct {n : ℕ} [NeZero n]
    (α : Fin n → ℕ) (t : ℚ) :
    boundedConvolution t (braidBoundedBlock α) =
      braidPartitionPolynomialValue α t := by
  rw [boundedConvolution_eq_partitionFallingSum,
    boundedBraidPartitionSum_eq_fallingPartitionSum,
    fallingPartitionSumOn_closed, if_neg Finset.univ_nonempty.ne_empty]
  rw [sum_neg_cast_fin, fallingValue_eq_prod_range]
  unfold braidPartitionPolynomialValue
  simp only [Finset.card_univ, Fintype.card_fin]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  ring

/-- Both braid convolution expressions in arbitrary positive rank, directly
from Mathlib and the finite-difference partition identity. -/
theorem braid_partition_convolutions_direct {n : ℕ} [NeZero n]
    (α : Fin n → ℕ) (t : ℚ) :
    braidPartitionPolynomialValue α t =
        regionConvolution t (braidRegionBlock α) ∧
      regionConvolution t (braidRegionBlock α) =
        boundedConvolution t (braidBoundedBlock α) := by
  constructor
  · exact (braid_regionConvolution_direct α t).symm
  · rw [braid_regionConvolution_direct, braid_boundedConvolution_direct]

end

end CyclicBraidArrangement
