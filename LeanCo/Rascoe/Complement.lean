import LeanCo.Rascoe.Basic

/-!
# Rascoe and non-Rascoe partitions are complementary

This file proves the literal finite partition of the ambient type.  It is
the coefficientwise input for both generating functions in Theorem 1.1 of
arXiv:2608.30180.
-/

namespace LeanCo.Rascoe

/-- Every unrestricted partition is uniquely either Rascoe or non-Rascoe. -/
noncomputable def rascoeNonRascoeEquiv (n : ℕ) :
    RascoePartition n ⊕ NonRascoePartition n ≃ Nat.Partition n := by
  classical
  simpa only [RascoePartition, NonRascoePartition, IsRascoe, IsNonRascoe]
    using (Equiv.sumCompl (fun p : Nat.Partition n => length p ∈ p.parts))

/-- The finite coefficient identity `c(n) + e(n) = p(n)`. -/
theorem rascoeNumber_add_nonRascoeNumber (n : ℕ) :
    rascoeNumber n + nonRascoeNumber n = partitionNumber n := by
  rw [rascoeNumber, nonRascoeNumber, partitionNumber, ← Fintype.card_sum]
  exact Fintype.card_congr (rascoeNonRascoeEquiv n)

@[simp] theorem partitionNumber_zero : partitionNumber 0 = 1 := by
  simp [partitionNumber]

@[simp] theorem rascoeNumber_zero : rascoeNumber 0 = 0 := by
  rw [rascoeNumber, Fintype.card_eq_zero_iff]
  exact ⟨fun p => by
    have hp : p.1.parts = 0 := Nat.Partition.partition_zero_parts p.1
    have hm : length p.1 ∈ p.1.parts := p.2
    simpa [length, hp] using hm⟩

@[simp] theorem nonRascoeNumber_zero : nonRascoeNumber 0 = 1 := by
  have h := rascoeNumber_add_nonRascoeNumber 0
  simpa using h

end LeanCo.Rascoe
