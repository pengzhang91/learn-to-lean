import LeanCo.Rascoe.Complement
import LeanCo.Rascoe.NoOne

/-!
# Coefficient formulas for unrestricted Rascoe partitions

These are the coefficientwise consequences of the rightmost generating
functions in Theorem 1.1, proved directly from the finite bijections.  The
successor indexing makes the paper's convention `p(k)=0` for `k<0`
unnecessary.
-/

namespace LeanCo.Rascoe

/-- `c(n+2) = p(n+1)-p(n)`. -/
theorem rascoeNumber_add_two_eq_partitionNumber_sub (n : ℕ) :
    rascoeNumber (n + 2) = partitionNumber (n + 1) - partitionNumber n := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    rascoeNumber_succ_eq_noOneNumber,
    noOneNumber_succ_eq_partitionNumber_sub]

/-- The non-Rascoe coefficient formula, safely indexed for every natural `n`. -/
theorem nonRascoeNumber_add_two_eq_partitionFormula (n : ℕ) :
    nonRascoeNumber (n + 2) =
      partitionNumber (n + 2) - partitionNumber (n + 1) + partitionNumber n := by
  have hcomp := rascoeNumber_add_nonRascoeNumber (n + 2)
  have hrascoe : rascoeNumber (n + 2) = noOneNumber (n + 1) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      rascoeNumber_succ_eq_noOneNumber (n + 1)
  have hmono := partitionNumber_succ_eq_noOneNumber_add n
  have hmono' :
      partitionNumber (n + 2) =
        noOneNumber (n + 2) + partitionNumber (n + 1) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      partitionNumber_succ_eq_noOneNumber_add (n + 1)
  omega

/-- The paper's unshifted formula under its required lower-bound condition. -/
theorem nonRascoeNumber_eq_partitionFormula {n : ℕ} (hn : 2 ≤ n) :
    nonRascoeNumber n =
      partitionNumber n - partitionNumber (n - 1) + partitionNumber (n - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 k]
  have hpred : k + 2 - 1 = k + 1 := by omega
  have hpredpred : k + 2 - 2 = k := by omega
  rw [hpred, hpredpred]
  exact nonRascoeNumber_add_two_eq_partitionFormula k

end LeanCo.Rascoe
