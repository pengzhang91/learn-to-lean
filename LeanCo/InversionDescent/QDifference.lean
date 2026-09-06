import LeanCo.InversionDescent.QExponential

/-!
# The q-difference step without symbolic division

This file records the algebraic step between equations (5) and (6) of the
paper in the q-divided-power coefficient model.  It deliberately avoids the
paper's quotient by `(q - 1) * x`; the identity therefore remains valid at
`q = 1` and in arbitrary commutative rings.
-/

open scoped BigOperators

namespace LeanCo.QExponential

/-- The q-integer `[n]_q = 1 + q + ... + q^(n-1)`. -/
def qInteger {R : Type*} [Semiring R] (q : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range n, q ^ i

/-- Coefficient action of replacing `x` by `q*x`. -/
def qRescale {R : Type*} [Monoid R] (q : R) (f : QSeries R) : QSeries R :=
  fun n ↦ q ^ n * f n

/-- Multiplication by `x` in the q-divided-power basis. -/
def qMulX {R : Type*} [Semiring R] (q : R) (f : QSeries R) : QSeries R
  | 0 => 0
  | n + 1 => qInteger q (n + 1) * f n

/-- The polynomial geometric-sum identity, with no invertibility assumption. -/
theorem q_sub_one_mul_qInteger {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    (q - 1) * qInteger q n = q ^ n - 1 := by
  simpa [qInteger] using (Commute.one_right q).mul_geom_sum₂ n

/-- The defining numerator identity for the q-derivative. -/
theorem qRescale_sub_eq_qMulX_qDerivative
    {R : Type*} [CommRing R] (q : R) (f : QSeries R) :
    (fun n ↦ qRescale q f n - f n) =
      fun n ↦ (q - 1) * qMulX q (qDerivative f) n := by
  funext n
  cases n with
  | zero => simp [qRescale, qMulX]
  | succ n =>
      simp only [qRescale, qMulX, qDerivative]
      rw [← mul_assoc, q_sub_one_mul_qInteger]
      ring

/-- Equation (5) rewritten as the q-rescaling identity, without division. -/
theorem qRescale_eq_of_qDifferentialEquation
    {R : Type*} [CommRing R] (q : R) (I H : QSeries R)
    (hdiff : qDerivative I = H) :
    qRescale q I = fun n ↦ I n + (q - 1) * qMulX q H n := by
  funext n
  have hnum := congrFun (qRescale_sub_eq_qMulX_qDerivative q I) n
  rw [hdiff] at hnum
  calc
    qRescale q I n = (qRescale q I n - I n) + I n := by ring
    _ = (q - 1) * qMulX q H n + I n := by rw [hnum]
    _ = I n + (q - 1) * qMulX q H n := by ac_rfl

/--
The no-division form of equation (6), specialized to the right-hand side of
the paper's q-differential equation.
-/
theorem equation_6_no_division
    {R : Type*} [CommRing R] (q t : R) (I : QSeries R)
    (hdiff : qDerivative I =
      fun n ↦ I n + t * qCauchy q I (scaledQExpTail q) n) :
    qRescale q I = fun n ↦
      I n + (q - 1) * qMulX q
        (fun m ↦ I m + t * qCauchy q I (scaledQExpTail q) m) n :=
  qRescale_eq_of_qDifferentialEquation q I _ hdiff

end LeanCo.QExponential
