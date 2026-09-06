import LeanCo.LaplacianLFunctions.LFunction
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Polynomiality from high-degree rank stability

This file isolates the finite-character algebra in Proposition 3.8 of
arXiv:2608.29981.  If `h` is constant on one fixed-degree Picard torsor, the
corresponding coefficient of a nontrivially twisted `L`-function vanishes.
Consequently, constancy in every degree above a bound makes the formal power
series the image of an explicit polynomial.

The graph Riemann--Roch theorem supplies the required high-degree constancy;
keeping that input separate makes the cancellation argument independent of
the particular proof of Riemann--Roch.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- A nontrivial character has zero total sum. -/
theorem sum_addChar_eq_zero_of_ne_one
    {A : Type*} [AddCommGroup A] [Fintype A]
    (chi : AddChar A ℂ) (hchi : chi ≠ 1) :
    ∑ a : A, chi a = 0 := by
  classical
  exact (AddChar.sum_eq_zero_iff_ne_zero (ψ := chi)).2
    (by simpa only [AddChar.one_eq_zero] using hchi)

/-- If `h` is constant on the degree-`d` Picard torsor, the degree-`d`
coefficient of every nontrivial twist vanishes. -/
theorem lCoefficient_eq_zero_of_h_constant
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (d n : ℕ) (hchi : chi ≠ 1)
    (hconstant : ∀ a : G.Jacobian,
      G.h (G.classInDegree D₁ (d : ℤ) a) = n) :
    G.lCoefficient D₁ chi d = 0 := by
  classical
  simp only [lCoefficient, hconstant]
  rw [← Finset.sum_mul]
  rw [← map_sum, sum_addChar_eq_zero_of_ne_one chi hchi]
  simp

/-- The degree-`bound` truncation of an `L`-function, regarded as a
polynomial in `t` with coefficients in `ℂ[u]`. -/
def lPolynomial (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (bound : ℕ) : Polynomial (Polynomial ℂ) :=
  PowerSeries.trunc (bound + 1) (G.lFunction D₁ chi)

theorem coeff_lPolynomial (G : LooplessMultigraph V)
    [Fintype G.Jacobian] (D₁ : G.PicardDegree 1)
    (chi : AddChar G.Jacobian ℂ) (bound d : ℕ) :
    (G.lPolynomial D₁ chi bound).coeff d =
      if d ≤ bound then G.lCoefficient D₁ chi d else 0 := by
  rw [lPolynomial, PowerSeries.coeff_trunc]
  simp only [G.coeff_lFunction D₁ chi d]
  simp only [Nat.lt_add_one_iff]

/-- If all coefficients above `bound` vanish, the `L`-function is exactly
the power-series image of its finite truncation. -/
theorem lFunction_eq_lPolynomial
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (bound : ℕ)
    (htail : ∀ d : ℕ, bound < d → G.lCoefficient D₁ chi d = 0) :
    G.lFunction D₁ chi = (G.lPolynomial D₁ chi bound :
      PowerSeries (Polynomial ℂ)) := by
  apply PowerSeries.ext
  intro d
  rw [G.coeff_lFunction D₁ chi d, Polynomial.coeff_coe,
    G.coeff_lPolynomial D₁ chi bound d]
  by_cases hd : d ≤ bound
  · simp [hd]
  · have hlt : bound < d := Nat.lt_of_not_ge hd
    simp [hd, htail d hlt]

/-- High-degree constancy of `h` is sufficient for polynomiality of every
nontrivially twisted `L`-function. -/
theorem lFunction_eq_lPolynomial_of_h_constant_above
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (bound : ℕ) (hchi : chi ≠ 1)
    (hconstant : ∀ d : ℕ, bound < d →
      ∃ n : ℕ, ∀ a : G.Jacobian,
        G.h (G.classInDegree D₁ (d : ℤ) a) = n) :
    G.lFunction D₁ chi = (G.lPolynomial D₁ chi bound :
      PowerSeries (Polynomial ℂ)) := by
  apply G.lFunction_eq_lPolynomial D₁ chi bound
  intro d hd
  obtain ⟨n, hn⟩ := hconstant d hd
  exact G.lCoefficient_eq_zero_of_h_constant D₁ chi d n hchi hn

/-- A nonzero coefficient at the truncation bound makes the `t`-degree of
the resulting polynomial exactly that bound. -/
theorem natDegree_lPolynomial_eq_of_leading_coeff_ne_zero
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (bound : ℕ) (hlead : G.lCoefficient D₁ chi bound ≠ 0) :
    (G.lPolynomial D₁ chi bound).natDegree = bound := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · have hlt := PowerSeries.natDegree_trunc_lt
      (G.lFunction D₁ chi) bound
    simpa only [lPolynomial, Nat.lt_add_one_iff] using hlt
  · simpa [G.coeff_lPolynomial D₁ chi bound bound] using hlead

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
