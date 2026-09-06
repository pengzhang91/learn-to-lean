import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff

/-!
# The polynomial `(u^h - 1) / (u - 1)`

The graph zeta and `L`-functions use this expression at every divisor class.
We define it division-free as `1 + u + ⋯ + u^(h-1)`, including the
important boundary value `h = 0`.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

/-- The division-free geometric polynomial attached to `h`. -/
noncomputable def geometricPolynomial {R : Type*} [Semiring R] (h : ℕ) : Polynomial R :=
  ∑ i ∈ Finset.range h, Polynomial.X ^ i

@[simp]
theorem geometricPolynomial_zero {R : Type*} [Semiring R] :
    geometricPolynomial (R := R) 0 = 0 := by
  simp [geometricPolynomial]

theorem geometricPolynomial_succ {R : Type*} [Semiring R] (h : ℕ) :
    geometricPolynomial (R := R) (h + 1) =
      geometricPolynomial h + Polynomial.X ^ h := by
  simp [geometricPolynomial, Finset.sum_range_succ]

/-- The same geometric-sum recurrence, factored from the low-degree end. -/
theorem geometricPolynomial_succ_eq_one_add_X_mul
    {R : Type*} [CommSemiring R] (h : ℕ) :
    geometricPolynomial (R := R) (h + 1) =
      1 + Polynomial.X * geometricPolynomial h := by
  induction h with
  | zero => simp [geometricPolynomial]
  | succ h ih =>
      calc
        geometricPolynomial (R := R) (h + 1 + 1) =
            geometricPolynomial (h + 1) + Polynomial.X ^ (h + 1) :=
          geometricPolynomial_succ (h + 1)
        _ = (1 + Polynomial.X * geometricPolynomial h) +
            Polynomial.X ^ (h + 1) := by rw [ih]
        _ = 1 + Polynomial.X *
            (geometricPolynomial h + Polynomial.X ^ h) := by
          rw [pow_succ]
          ring
        _ = 1 + Polynomial.X * geometricPolynomial (h + 1) := by
          rw [geometricPolynomial_succ]

/-- Consecutive geometric polynomials satisfy the quadratic recurrence whose
characteristic factors are `(1-t)(1-ut)`. -/
theorem geometricPolynomial_quadratic_recurrence
    {R : Type*} [CommRing R] (h : ℕ) :
    geometricPolynomial (R := R) (h + 2) -
        (1 + Polynomial.X) * geometricPolynomial (h + 1) +
        Polynomial.X * geometricPolynomial h = 0 := by
  rw [show h + 2 = (h + 1) + 1 by omega,
    geometricPolynomial_succ_eq_one_add_X_mul,
    geometricPolynomial_succ_eq_one_add_X_mul]
  ring

/-- A first-order telescoping form of the geometric-sum identity. -/
theorem geometricPolynomial_succ_sub_X_mul
    {R : Type*} [CommRing R] (h : ℕ) :
    geometricPolynomial (R := R) (h + 1) -
      Polynomial.X * geometricPolynomial h = 1 := by
  rw [geometricPolynomial_succ_eq_one_add_X_mul]
  ring

@[simp]
theorem coeff_zero_geometricPolynomial {R : Type*} [Semiring R] (h : ℕ) :
    (geometricPolynomial (R := R) h).coeff 0 = if h = 0 then 0 else 1 := by
  cases h with
  | zero => simp
  | succ h =>
      by_cases hh : h = 0
      · subst h
        simp [geometricPolynomial, Finset.sum_range_succ]
      · have hp : 0 < h := Nat.pos_of_ne_zero hh
        have hz : (0 : ℕ) ≠ h := Ne.symm hh
        simp [geometricPolynomial, hh, hp, hz]

@[simp]
theorem coeff_zero_geometricPolynomial_of_pos {R : Type*} [Semiring R]
    {h : ℕ} (hh : 0 < h) :
    (geometricPolynomial (R := R) h).coeff 0 = 1 := by
  simp [hh.ne']

@[simp]
theorem eval_one_geometricPolynomial {R : Type*} [Semiring R] (h : ℕ) :
    Polynomial.eval 1 (geometricPolynomial (R := R) h) = h := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [geometricPolynomial_succ, Polynomial.eval_add, ih]
      rw [Polynomial.eval_X_pow]
      simp

theorem geometricPolynomial_eq_zero_iff {R : Type*} [Nontrivial R]
    [Semiring R] (h : ℕ) :
    geometricPolynomial (R := R) h = 0 ↔ h = 0 := by
  constructor
  · intro hp
    by_contra hh
    have hc := congrArg (fun p : Polynomial R ↦ p.coeff 0) hp
    simp [hh] at hc
  · rintro rfl
    exact geometricPolynomial_zero

end LeanCo.LaplacianLFunctions
