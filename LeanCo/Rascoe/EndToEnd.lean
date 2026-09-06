import LeanCo.Rascoe.DoubleSum
import LeanCo.Rascoe.Analytic
import LeanCo.Rascoe.Beck
import LeanCo.Rascoe.QBinomial

/-!
# End-to-end statements for arXiv:2608.30180

This module assembles the exact finite partition counts, the locally finite
Gaussian formal-power-series realization, the analytic Euler-product values
on the open unit disc, and the rank-weighted identity from Section 4.
-/

open scoped BigOperators PowerSeries.WithPiTopology

namespace LeanCo.Rascoe

open PowerSeries

/-! ## Formal-power-series form of Theorem 1.1 -/

/-- The two complete formal-power-series chains in Theorem 1.1.  The middle
series retain the displayed Gaussian factors, finite denominators, exponents,
and exceptional terms, with each coefficient represented by a finite sum. -/
theorem cuthbertson_theorem_1_1_formal :
    (rascoeSeries ℤ = rascoeGaussianDoubleSeries ∧
        rascoeGaussianDoubleSeries = X * noOneEulerProduct ℤ) ∧
      (nonRascoeSeries ℤ = nonRascoeGaussianDoubleSeries ∧
        nonRascoeGaussianDoubleSeries =
          (1 - X + X ^ 2) * partitionEulerProduct ℤ) := by
  constructor
  · exact ⟨rascoeGaussianDoubleSeries_eq_rascoeSeries.symm,
      rascoeGaussianDoubleSeries_eq_rascoeSeries.trans
        (rascoeSeries_eq_X_mul_noOneEulerProduct ℤ)⟩
  · exact ⟨nonRascoeGaussianDoubleSeries_eq_nonRascoeSeries.symm,
      nonRascoeGaussianDoubleSeries_eq_nonRascoeSeries.trans
        (nonRascoeSeries_eq_polynomial_mul_partitionEulerProduct ℤ)⟩

/-! ## Analytic generating functions in Theorem 1.1 -/

/-- The two analytic coefficient generating functions in Theorem 1.1.
Both statements include every complex `q` in the open unit disc, including
`q = 0`. -/
theorem cuthbertson_theorem_1_1_analytic_generating_functions
    (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (rascoeNumber n : ℂ) * q ^ n)
        (q * (analyticQPochhammer (q ^ 2) q)⁻¹) ∧
      HasSum (fun n : ℕ ↦ (nonRascoeNumber n : ℂ) * q ^ n)
        ((1 - q + q ^ 2) * (analyticQPochhammer q q)⁻¹) :=
  ⟨rascoeNumber_hasSum q hq, nonRascoeNumber_hasSum q hq⟩

/-- Analytic evaluation of the coefficient sequence of the locally finite
Rascoe Gaussian middle series. -/
theorem rascoeGaussianDoubleSeries_hasSum (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum
      (fun n : ℕ ↦
        ((coeff n rascoeGaussianDoubleSeries : ℤ) : ℂ) * q ^ n)
      (q * (analyticQPochhammer (q ^ 2) q)⁻¹) := by
  simpa [rascoeGaussianDoubleSeries_eq_rascoeSeries] using
    rascoeNumber_hasSum q hq

/-- Analytic evaluation of the coefficient sequence of the locally finite
non-Rascoe Gaussian middle series. -/
theorem nonRascoeGaussianDoubleSeries_hasSum (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum
      (fun n : ℕ ↦
        ((coeff n nonRascoeGaussianDoubleSeries : ℤ) : ℂ) * q ^ n)
      ((1 - q + q ^ 2) * (analyticQPochhammer q q)⁻¹) := by
  simpa [nonRascoeGaussianDoubleSeries_eq_nonRascoeSeries] using
    nonRascoeNumber_hasSum q hq

/-! ## Theorem 4.3 -/

/-- Theorem 4.3 at every natural index, with negative partition-number
indices represented by `shiftedPartitionCount`. -/
theorem cuthbertson_theorem_4_3_all_n (n : ℕ) :
    nonRascoeNumber n =
        partitionNumber n - shiftedPartitionCount n 1 +
          shiftedPartitionCount n 2 ∧
      partitionNumber n - shiftedPartitionCount n 1 +
          shiftedPartitionCount n 2 = rankPartSizeSum n :=
  ⟨nonRascoeNumber_eq_shiftedPartitionFormula n,
    (rankPartSizeSum_eq_shiftedPartitionFormula n).symm⟩

/-- Theorem 4.3 in the paper's displayed indexing. -/
theorem cuthbertson_theorem_4_3 {n : ℕ} (hn : 2 ≤ n) :
    nonRascoeNumber n =
        partitionNumber n - partitionNumber (n - 1) +
          partitionNumber (n - 2) ∧
      partitionNumber n - partitionNumber (n - 1) +
          partitionNumber (n - 2) = rankPartSizeSum n :=
  beck_theorem_paper_formula hn

end LeanCo.Rascoe
