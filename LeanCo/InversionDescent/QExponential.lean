import LeanCo.InversionDescent.Gaussian

/-!
# The q-exponential coefficient equation

The paper passes from Theorem 2.5 to a q-differential equation for its
q-exponential generating function.  This file formalizes that passage without
dividing by a symbolic q-factorial.  A sequence `f n` represents

`\sum n, f n * x^n / n!_q`.

In this divided-power basis, ordinary multiplication has Gaussian-binomial
structure constants; this is `qCauchy`.  Consequently, `qDerivative` is just
the left shift.  `scaledQExpTail q` represents `exp_q(q*x) - 1`.
-/

open scoped BigOperators

namespace LeanCo.QExponential

/-- Coefficients in the q-divided-power basis. -/
abbrev QSeries (R : Type*) := ℕ → R

/-- Product coefficients in the q-divided-power basis. -/
noncomputable def qCauchy {R : Type*} [CommSemiring R] (q : R)
    (f g : QSeries R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1),
    qBinomialEval q n k * f k * g (n - k)

/-- The q-derivative shifts divided-power coefficients one place left. -/
def qDerivative {R : Type*} (f : QSeries R) : QSeries R :=
  fun n ↦ f (n + 1)

/-- Coefficients of `exp_q(q*x) - 1` in the q-divided-power basis. -/
def scaledQExpTail {R : Type*} [Zero R] [One R] [Pow R ℕ]
    (q : R) : QSeries R :=
  fun n ↦ if n = 0 then 0 else q ^ n

@[simp]
theorem scaledQExpTail_zero {R : Type*} [Semiring R] (q : R) :
    scaledQExpTail q 0 = 0 := by
  simp [scaledQExpTail]

theorem scaledQExpTail_of_pos {R : Type*} [Semiring R] (q : R)
    {n : ℕ} (hn : 0 < n) : scaledQExpTail q n = q ^ n := by
  simp [scaledQExpTail, hn.ne']

/-- The zero constant term removes exactly the last summand of `qCauchy`. -/
theorem qCauchy_scaledQExpTail {R : Type*} [CommSemiring R] (q : R)
    (f : QSeries R) (n : ℕ) :
    qCauchy q f (scaledQExpTail q) n =
      ∑ k ∈ Finset.range n,
        qBinomialEval q n k * f k * q ^ (n - k) := by
  classical
  rw [qCauchy, Finset.sum_range_succ]
  simp only [Nat.sub_self, scaledQExpTail_zero, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k < n := Finset.mem_range.mp hk
  have hpos : 0 < n - k := by omega
  rw [scaledQExpTail_of_pos q hpos]

/--
Coefficient form of equation (5) in the paper.  This is precisely the passage
from the last-zero recurrence to

`D_q I = I + t * I * (exp_q(q*x) - 1)`.
-/
theorem qDifferentialEquation_of_recurrence
    {R : Type*} [CommSemiring R] (q t : R) (I : QSeries R)
    (hrec : ∀ n,
      I (n + 1) = I n +
        t * ∑ k ∈ Finset.range n,
          qBinomialEval q n k * I k * q ^ (n - k)) :
    qDerivative I =
      fun n ↦ I n + t * qCauchy q I (scaledQExpTail q) n := by
  funext n
  rw [qDerivative, qCauchy_scaledQExpTail]
  exact hrec n

/-- Paper-numbered alias for the rigorously defined coefficient equation. -/
theorem theorem_3_1_coefficient_equation
    {R : Type*} [CommSemiring R] (q t : R) (I : QSeries R)
    (hrec : ∀ n,
      I (n + 1) = I n +
        t * ∑ k ∈ Finset.range n,
          qBinomialEval q n k * I k * q ^ (n - k)) :
    qDerivative I =
      fun n ↦ I n + t * qCauchy q I (scaledQExpTail q) n :=
  qDifferentialEquation_of_recurrence q t I hrec

end LeanCo.QExponential
