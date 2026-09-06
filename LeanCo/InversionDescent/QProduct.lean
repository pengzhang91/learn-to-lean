import LeanCo.InversionDescent.GeneratingFunction
import LeanCo.InversionDescent.QDifference

/-!
# The actual factors in Theorem 3.1

The coefficient recurrence and its q-difference form are proved in
`QExponential` and `QDifference`.  Here we record the product-iteration part
of Theorem 3.1 with genuine formal power series.  In particular, the factors
below are literally

`1 + (q - 1) q^k X * (1 + t * (exp_q(q^(k+1) X) - 1))`.

The finite identity is purely algebraic.  The infinite identity remains
conditional on the two convergence hypotheses which the paper omits.
-/

open scoped BigOperators Topology PowerSeries.WithPiTopology
open Filter Topology

namespace LeanCo.QProduct

open PowerSeries

/-- The polynomial q-factorial `n!_q = product_{1 <= i <= n} [i]_q`. -/
def qFactorial {R : Type*} [CommSemiring R] (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => qFactorial q n * QExponential.qInteger q (n + 1)

@[simp]
theorem qFactorial_zero {R : Type*} [CommSemiring R] (q : R) :
    qFactorial q 0 = 1 := rfl

@[simp]
theorem qFactorial_succ {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    qFactorial q (n + 1) =
      qFactorial q n * QExponential.qInteger q (n + 1) := rfl

/-- The paper's `exp_q(X)`, as an honest formal power series over a field. -/
noncomputable def qExponential {K : Type*} [Field K] (q : K) : K⟦X⟧ :=
  PowerSeries.mk fun n ↦ (qFactorial q n)⁻¹

@[simp]
theorem coeff_qExponential {K : Type*} [Field K] (q : K) (n : ℕ) :
    PowerSeries.coeff n (qExponential q) = (qFactorial q n)⁻¹ := by
  simp [qExponential]

@[simp]
theorem rescale_C_apply {R : Type*} [CommSemiring R] (a b : R) :
    PowerSeries.rescale a (PowerSeries.C b) = PowerSeries.C b := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C, hn]

/-- The `k = 0` factor in the product of Theorem 3.1. -/
noncomputable def baseFactor {K : Type*} [Field K] (q t : K) : K⟦X⟧ :=
  1 + (PowerSeries.C (q - 1) * PowerSeries.X) *
    (1 + PowerSeries.C t *
      (PowerSeries.rescale q (qExponential q) - 1))

/-- The literal `k`-th factor in the product of Theorem 3.1. -/
noncomputable def paperFactor {K : Type*} [Field K]
    (q t : K) (k : ℕ) : K⟦X⟧ :=
  PowerSeries.rescale (q ^ k) (baseFactor q t)

/-- Expanded form of the paper's factor. -/
theorem paperFactor_eq {K : Type*} [Field K]
    (q t : K) (k : ℕ) :
    paperFactor q t k =
      1 + (PowerSeries.C ((q - 1) * q ^ k) * PowerSeries.X) *
        (1 + PowerSeries.C t *
          (PowerSeries.rescale (q ^ (k + 1)) (qExponential q) - 1)) := by
  simp only [paperFactor, baseFactor, map_add, map_one, map_mul, map_sub,
    PowerSeries.rescale_X]
  rw [PowerSeries.rescale_rescale]
  rw [show q * q ^ k = q ^ (k + 1) by rw [pow_succ, mul_comm]]
  simp only [rescale_C_apply]
  ring

/-- Rescaling the base factor by `q^k` produces factor `k`. -/
theorem rescale_baseFactor {K : Type*} [Field K]
    (q t : K) (k : ℕ) :
    PowerSeries.rescale (q ^ k) (baseFactor q t) = paperFactor q t k := rfl

/-- The factors have constant coefficient one, hence are units. -/
@[simp]
theorem constantCoeff_paperFactor {K : Type*} [Field K]
    (q t : K) (k : ℕ) :
    PowerSeries.constantCoeff (paperFactor q t k) = 1 := by
  rw [paperFactor_eq]
  simp

theorem isUnit_paperFactor {K : Type*} [Field K]
    (q t : K) (k : ℕ) : IsUnit (paperFactor q t k) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- Factor `k`, regarded as a unit of the formal-power-series ring. -/
noncomputable def paperFactorUnit {K : Type*} [Field K]
    (q t : K) (k : ℕ) : (K⟦X⟧)ˣ :=
  (isUnit_paperFactor q t k).unit

@[simp]
theorem coe_paperFactorUnit {K : Type*} [Field K]
    (q t : K) (k : ℕ) :
    ↑(paperFactorUnit q t k) = paperFactor q t k := by
  exact IsUnit.unit_spec (isUnit_paperFactor q t k)

/-- Rescaling factor zero by `q^k` gives factor `k`. -/
theorem rescale_paperFactor_zero {K : Type*} [Field K]
    (q t : K) (k : ℕ) :
    PowerSeries.rescale (q ^ k) (paperFactor q t 0) =
      paperFactor q t k := by
  simp [paperFactor]

/--
The unconditional finite-product form of the iteration in Theorem 3.1.
The hypothesis is equation (6) written without division in the
formal-power-series ring.
-/
theorem finite_product_of_equation_six {K : Type*} [Field K]
    (q t : K) (I : K⟦X⟧)
    (hstep : PowerSeries.rescale q I = I * paperFactor q t 0) (N : ℕ) :
    PowerSeries.rescale (q ^ N) I =
      I * ∏ k ∈ Finset.range N, paperFactor q t k := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        PowerSeries.rescale (q ^ (N + 1)) I =
            PowerSeries.rescale (q ^ N)
              (PowerSeries.rescale q I) := by
          rw [PowerSeries.rescale_rescale]
          congr 2
          rw [pow_succ]
          exact mul_comm (q ^ N) q
        _ = PowerSeries.rescale (q ^ N)
              (I * paperFactor q t 0) := by rw [hstep]
        _ = PowerSeries.rescale (q ^ N) I *
              PowerSeries.rescale (q ^ N) (paperFactor q t 0) := by
          rw [map_mul]
        _ = (I * ∏ k ∈ Finset.range N, paperFactor q t k) *
              paperFactor q t N := by
          rw [ih, rescale_paperFactor_zero]
        _ = I * ∏ k ∈ Finset.range (N + 1), paperFactor q t k := by
          rw [Finset.prod_range_succ]
          ac_rfl

/-- A series with constant coefficient one is a unit. -/
theorem isUnit_series_of_constantCoeff_one {K : Type*} [Field K]
    (I : K⟦X⟧) (hconst : PowerSeries.constantCoeff I = 1) : IsUnit I := by
  rw [PowerSeries.isUnit_iff_constantCoeff, hconst]
  exact isUnit_one

/-- A series with constant coefficient one, regarded as a unit. -/
noncomputable def seriesUnit {K : Type*} [Field K]
    (I : K⟦X⟧) (hconst : PowerSeries.constantCoeff I = 1) : (K⟦X⟧)ˣ :=
  (isUnit_series_of_constantCoeff_one I hconst).unit

@[simp]
theorem coe_seriesUnit {K : Type*} [Field K]
    (I : K⟦X⟧) (hconst : PowerSeries.constantCoeff I = 1) :
    ↑(seriesUnit I hconst) = I := by
  exact IsUnit.unit_spec (isUnit_series_of_constantCoeff_one I hconst)

/-- The unit obtained from `I(q,t;q^k X)`. -/
noncomputable def rescaledUnit {K : Type*} [Field K]
    (q : K) (I : K⟦X⟧) (hconst : PowerSeries.constantCoeff I = 1)
    (k : ℕ) : (K⟦X⟧)ˣ :=
  Units.map (PowerSeries.rescale (q ^ k)) (seriesUnit I hconst)

@[simp]
theorem coe_rescaledUnit {K : Type*} [Field K]
    (q : K) (I : K⟦X⟧) (hconst : PowerSeries.constantCoeff I = 1)
    (k : ℕ) :
    ↑(rescaledUnit q I hconst k) = PowerSeries.rescale (q ^ k) I := by
  simp [rescaledUnit]

/-- Equation (6) at the `k`-th rescaling, as a multiplicative step of units. -/
theorem rescaledUnit_succ {K : Type*} [Field K]
    (q t : K) (I : K⟦X⟧) (hconst : PowerSeries.constantCoeff I = 1)
    (hstep : PowerSeries.rescale q I = I * paperFactor q t 0) (k : ℕ) :
    rescaledUnit q I hconst (k + 1) =
      rescaledUnit q I hconst k * paperFactorUnit q t k := by
  apply Units.ext
  have hmul :
      PowerSeries.rescale (q ^ (k + 1)) I =
        PowerSeries.rescale (q ^ k) I * paperFactor q t k := by
    calc
      PowerSeries.rescale (q ^ (k + 1)) I =
          PowerSeries.rescale (q ^ k) (PowerSeries.rescale q I) := by
        rw [PowerSeries.rescale_rescale]
        congr 2
        rw [pow_succ]
        exact mul_comm (q ^ k) q
      _ = PowerSeries.rescale (q ^ k) (I * paperFactor q t 0) := by
        rw [hstep]
      _ = PowerSeries.rescale (q ^ k) I *
          PowerSeries.rescale (q ^ k) (paperFactor q t 0) := by
        rw [map_mul]
      _ = PowerSeries.rescale (q ^ k) I * paperFactor q t k := by
        rw [rescale_paperFactor_zero]
  simpa using hmul

/-- Quotient form of the rescaled unit step, used by telescoping products. -/
theorem rescaledUnit_succ_div {K : Type*} [Field K]
    (q t : K) (I : K⟦X⟧) (hconst : PowerSeries.constantCoeff I = 1)
    (hstep : PowerSeries.rescale q I = I * paperFactor q t 0) (k : ℕ) :
    rescaledUnit q I hconst (k + 1) / rescaledUnit q I hconst k =
      paperFactorUnit q t k := by
  rw [rescaledUnit_succ q t I hconst hstep k]
  simp

/--
The literal infinite-product conclusion of Theorem 3.1.  Unlike the paper,
the statement explicitly assumes both convergence of the rescaled iterates
and unconditional convergence of the product of factor units.
-/
theorem infinite_product_of_equation_six
    {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (q t : K) (I : K⟦X⟧) (hconst : PowerSeries.constantCoeff I = 1)
    (hstep : PowerSeries.rescale q I = I * paperFactor q t 0)
    (hI : Tendsto (rescaledUnit q I hconst) atTop (nhds 1))
    (hF : Multipliable (paperFactorUnit q t)) :
    seriesUnit I hconst = (∏' k, paperFactorUnit q t k)⁻¹ := by
  have h := GeneratingFunction.initial_eq_inv_tprod
    (rescaledUnit q I hconst) (paperFactorUnit q t)
    (rescaledUnit_succ_div q t I hconst hstep) hI hF
  have hzero : rescaledUnit q I hconst 0 = seriesUnit I hconst := by
    apply Units.ext
    simp
  rwa [hzero] at h

/-- The finite reciprocal form when the rescaled series is exactly one. -/
theorem eq_inverse_finite_product_of_rescale_eq_one
    {K : Type*} [Field K] (q t : K) (I : K⟦X⟧)
    (hstep : PowerSeries.rescale q I = I * paperFactor q t 0)
    (N : ℕ) (hN : PowerSeries.rescale (q ^ N) I = 1) :
    I = (∏ k ∈ Finset.range N, paperFactor q t k)⁻¹ := by
  have hprod := finite_product_of_equation_six q t I hstep N
  rw [hN] at hprod
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2
  exact hprod.symm

end LeanCo.QProduct
