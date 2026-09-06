import LeanCo.Negami.TwoBoundaryPartitions
import LeanCo.Negami.SplittingMatrix
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The two-boundary inverse kernel and four-term formula

This module transports the explicit `2 x 2` inverse to the actual finite type
of partitions of a two-element boundary.  It also expands the inverse pairing
into the four scalar terms of Corollary 6.3.
-/

open scoped Matrix

namespace LeanCo.Negami

/-- Reindexing a square matrix transports its bilinear action by composing
both vectors with the same equivalence. -/
theorem reindexed_inverse_pairing
    {I J F : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] [CommSemiring F] (e : I ≃ J) (B : Matrix I I F)
    (q h : J → F) :
    q ⬝ᵥ (Matrix.reindex e e B *ᵥ h) =
      (fun i => q (e i)) ⬝ᵥ (B *ᵥ fun i => h (e i)) := by
  unfold dotProduct Matrix.mulVec
  calc
    (∑ j : J, q j * ∑ k : J, Matrix.reindex e e B j k * h k) =
        ∑ i : I, q (e i) *
          ∑ k : J, Matrix.reindex e e B (e i) k * h k :=
      (e.sum_comp (fun j => q j *
        ∑ k : J, Matrix.reindex e e B j k * h k)).symm
    _ = ∑ i : I, q (e i) * ∑ l : I, B i l * h (e l) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact (e.sum_comp (fun l =>
        Matrix.reindex e e B (e i) l * h l)).symm.trans (by
          apply Finset.sum_congr rfl
          intro l _
          simp [Matrix.reindex_apply])

/-- The explicit inverse kernel indexed by the two actual boundary
partitions. -/
noncomputable def twoBoundaryPartitionInverse {F : Type*} [Field F] (t : F) :
    Matrix (FinitePartition (Fin 2)) (FinitePartition (Fin 2)) F :=
  Matrix.reindex twoPartitionEquiv twoPartitionEquiv (twoBoundaryInverse t)

/-- The actual connectivity matrix is the reindexing of the displayed
`T₂(t)`. -/
theorem twoBoundaryConnectivity_eq_reindex {F : Type*} [Field F] (t : F) :
    BoundaryData.connectivityMatrix (P := FinitePartition (Fin 2))
      FinitePartition.rho t =
      Matrix.reindex twoPartitionEquiv twoPartitionEquiv
        (twoBoundaryMatrix t) := by
  ext π σ
  let i := twoPartitionEquiv.symm π
  let j := twoPartitionEquiv.symm σ
  have h := congrFun (congrFun (twoBoundaryMatrix_from_partitions t) i) j
  change t ^ FinitePartition.rho π σ =
    twoBoundaryMatrix t (twoPartitionEquiv.symm π) (twoPartitionEquiv.symm σ)
  calc
    t ^ FinitePartition.rho π σ =
        t ^ FinitePartition.rho
          (twoPartition (twoPartitionEquiv.symm π))
          (twoPartition (twoPartitionEquiv.symm σ)) := by
      rw [show twoPartition (twoPartitionEquiv.symm π) = π from
        twoPartitionEquiv.apply_symm_apply π]
      rw [show twoPartition (twoPartitionEquiv.symm σ) = σ from
        twoPartitionEquiv.apply_symm_apply σ]
    _ = twoBoundaryMatrix t (twoPartitionEquiv.symm π)
        (twoPartitionEquiv.symm σ) := by
      simpa [i, j] using h

/-- Proposition 6.2 on the actual partition index type. -/
theorem twoBoundaryPartitionInverse_mul_connectivity
    {F : Type*} [Field F] (t : F) (ht : t ≠ 0) (ht1 : t ≠ 1) :
    twoBoundaryPartitionInverse t *
      BoundaryData.connectivityMatrix (P := FinitePartition (Fin 2))
        FinitePartition.rho t = 1 := by
  rw [twoBoundaryConnectivity_eq_reindex]
  change (Matrix.reindexRingEquiv F twoPartitionEquiv) (twoBoundaryInverse t) *
    (Matrix.reindexRingEquiv F twoPartitionEquiv) (twoBoundaryMatrix t) = 1
  rw [← map_mul, twoBoundaryInverse_mul_matrix t ht ht1, map_one]

/-- Corollary 6.3: expansion of the inverse-kernel pairing into its four
terms in the `(C,D)` ordering. -/
theorem twoBoundary_inverse_pairing {F : Type*} [Field F]
    (t : F) (ht : t ≠ 0) (ht1 : t ≠ 1) (qK qH : Fin 2 → F) :
    qK ⬝ᵥ (twoBoundaryInverse t *ᵥ qH) =
      qK 0 * qH 0 / (t - 1) -
      qK 0 * qH 1 / (t * (t - 1)) -
      qK 1 * qH 0 / (t * (t - 1)) +
      qK 1 * qH 1 / (t * (t - 1)) := by
  have hs : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  simp [dotProduct, Matrix.mulVec, twoBoundaryInverse, Fin.sum_univ_two]
  field_simp [ht, hs]
  ring

end LeanCo.Negami
