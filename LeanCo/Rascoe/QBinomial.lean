import LeanCo.InversionDescent.GaussianFactorial
import LeanCo.Rascoe.QPochhammer

/-!
# Gaussian polynomials used by arXiv:2608.30180

The Gaussian coefficient is defined by the finite rectangle-partition
enumerator already available in this project.  This avoids division and is
valid at every value of the indeterminate.  In particular, the two Pascal
forms below correct the first formula printed in Theorem 2.1 of the paper:
its second summand must have top index `a - 1`.
-/

open scoped BigOperators PowerSeries.WithPiTopology

namespace LeanCo.Rascoe

open PowerSeries

/-- The Gaussian polynomial `[n choose k]_X` as a formal power series over `ℤ`. -/
noncomputable def gaussianPS (n k : ℕ) : ℤ⟦X⟧ :=
  LeanCo.qBinomialEval X n k

@[simp] theorem gaussianPS_zero_right (n : ℕ) : gaussianPS n 0 = 1 := by
  simp [gaussianPS]

@[simp] theorem gaussianPS_self (n : ℕ) : gaussianPS n n = 1 := by
  simp [gaussianPS]

@[simp] theorem gaussianPS_of_lt {n k : ℕ} (h : n < k) :
    gaussianPS n k = 0 := by
  simp [gaussianPS, LeanCo.qBinomialEval_of_lt X h]

/-- The first (corrected) q-Pascal recurrence. -/
theorem gaussianPS_pascal_first {n k : ℕ} (h : k < n) :
    gaussianPS (n + 1) (k + 1) =
      gaussianPS n k + X ^ (k + 1) * gaussianPS n (k + 1) := by
  exact LeanCo.qBinomialEval_succ_succ X h

theorem constantCoeff_qIntegerGF_X {n : ℕ} (hn : 0 < n) :
    constantCoeff (LeanCo.qIntegerGF (X : ℤ⟦X⟧) n) = 1 := by
  simp [LeanCo.qIntegerGF, hn.ne']

theorem constantCoeff_qFactorialGF_X (n : ℕ) :
    constantCoeff (LeanCo.qFactorialGF (X : ℤ⟦X⟧) n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [LeanCo.qFactorialGF_succ, map_mul, ih]
      simp only [one_mul]
      exact constantCoeff_qIntegerGF_X (Nat.succ_pos n)

theorem qFactorialGF_X_ne_zero (n : ℕ) :
    LeanCo.qFactorialGF (X : ℤ⟦X⟧) n ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  simpa [constantCoeff_qFactorialGF_X] using this

/-- Symmetry of Gaussian polynomials, derived without any quotient notation. -/
theorem gaussianPS_symm {n k : ℕ} (hkn : k ≤ n) :
    gaussianPS n k = gaussianPS n (n - k) := by
  have hk := LeanCo.qBinomialEval_mul_factorials (X : ℤ⟦X⟧) hkn
  have hnk : n - k ≤ n := Nat.sub_le n k
  have hnk' := LeanCo.qBinomialEval_mul_factorials (X : ℤ⟦X⟧) hnk
  simp only [gaussianPS] at *
  have hsub : n - (n - k) = k := Nat.sub_sub_self hkn
  rw [hsub] at hnk'
  have hfactor :
      LeanCo.qFactorialGF (X : ℤ⟦X⟧) k *
          LeanCo.qFactorialGF (X : ℤ⟦X⟧) (n - k) ≠ 0 :=
    mul_ne_zero (qFactorialGF_X_ne_zero k)
      (qFactorialGF_X_ne_zero (n - k))
  apply mul_right_cancel₀ hfactor
  calc
    LeanCo.qBinomialEval X n k *
          (LeanCo.qFactorialGF X k * LeanCo.qFactorialGF X (n - k)) =
        LeanCo.qFactorialGF X n := by
      simpa [mul_assoc] using hk
    _ = LeanCo.qBinomialEval X n (n - k) *
          (LeanCo.qFactorialGF X k * LeanCo.qFactorialGF X (n - k)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hnk'.symm

/-- The second q-Pascal recurrence, the form used in the proof of Theorem 1.1. -/
theorem gaussianPS_pascal_second {n k : ℕ} (hkn : k ≤ n) :
    gaussianPS (n + 1) (k + 1) =
      gaussianPS n (k + 1) + X ^ (n - k) * gaussianPS n k := by
  rcases hkn.eq_or_lt with rfl | hlt
  · simp
  · have hA : n - k - 1 < n := by omega
    have hB : n - k ≤ n + 1 := by omega
    calc
      gaussianPS (n + 1) (k + 1) =
          gaussianPS (n + 1) ((n + 1) - (k + 1)) :=
        gaussianPS_symm (by omega)
      _ = gaussianPS (n + 1) ((n - k - 1) + 1) := by
        congr 2 <;> omega
      _ = gaussianPS n (n - k - 1) +
          X ^ (n - k) * gaussianPS n (n - k) := by
        have heq : n - k - 1 + 1 = n - k := by omega
        simpa only [heq] using gaussianPS_pascal_first hA
      _ = gaussianPS n (k + 1) + X ^ (n - k) * gaussianPS n k := by
        rw [gaussianPS_symm (show n - k - 1 ≤ n by omega),
          gaussianPS_symm (show n - k ≤ n by omega)]
        congr 3 <;> omega

/-- Paper-indexed corrected q-Pascal formula. -/
theorem qPascal_corrected {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    gaussianPS a b = X ^ b * gaussianPS (a - 1) b +
      gaussianPS (a - 1) (b - 1) := by
  rcases hba.eq_or_lt with rfl | hlt
  · have hsub : b - 1 < b := Nat.sub_lt hb (by omega)
    rw [gaussianPS_self, gaussianPS_of_lt hsub, gaussianPS_self]
    simp
  · cases a with
    | zero => omega
    | succ n =>
        cases b with
        | zero => omega
        | succ k =>
            have hk : k < n := by omega
            simpa [add_comm] using gaussianPS_pascal_first hk

end LeanCo.Rascoe
