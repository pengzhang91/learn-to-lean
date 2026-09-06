import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.Tactic

/-!
# The genus-one obstruction in Remark 3.11

This module formalizes the coefficient comparison used in the paper to show
that the proposed Artin-type factorization cannot hold for nontrivial cycle
graphs.  The parameters `cX` and `cY` are kept arbitrary throughout.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

/-- The common denominator of the genus-one zeta expression. -/
def genusOneDenominator (c : ℂ) : Polynomial ℂ :=
  1 - Polynomial.C (c + 1) * Polynomial.X +
    Polynomial.C c * Polynomial.X ^ 2

/-- The numerator for a genus-one graph whose Jacobian has cardinality `k`. -/
def genusOneNumerator (k : ℕ) (c : ℂ) : Polynomial ℂ :=
  1 + Polynomial.C ((k : ℂ) - (c + 1)) * Polynomial.X +
    Polynomial.C c * Polynomial.X ^ 2

theorem genusOneNumerator_eq (k : ℕ) (c : ℂ) :
    genusOneNumerator k c =
      genusOneDenominator c + Polynomial.C (k : ℂ) * Polynomial.X := by
  simp [genusOneNumerator, genusOneDenominator]
  ring

theorem genusOneDenominator_ne_zero (c : ℂ) :
    genusOneDenominator c ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℂ ↦ p.coeff 0) h
  simp [genusOneDenominator] at hc

/-- The rational expression displayed in Remark 3.11. -/
def genusOneZetaCandidate (k : ℕ) (c : ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (genusOneNumerator k c) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (genusOneDenominator c)

/-- Polynomial cross-multiplication already forces the degenerate case in
the cycle-cover comparison from Remark 3.11. -/
theorem genusOne_cross_eq_forces (n : ℕ) (hn : 0 < n) (cX cY : ℂ)
    (h : genusOneNumerator (n * n) cY * genusOneDenominator cX =
      genusOneNumerator n cX * genusOneDenominator cY) :
    n = 1 ∧ cX = cY := by
  rw [genusOneNumerator_eq, genusOneNumerator_eq] at h
  have hred :
      Polynomial.C ((n * n : ℕ) : ℂ) * Polynomial.X * genusOneDenominator cX =
        Polynomial.C (n : ℂ) * Polynomial.X * genusOneDenominator cY := by
    linear_combination h
  have hcoeffOne := congrArg (fun p : Polynomial ℂ ↦ p.coeff 1) hred
  simp only [mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul] at hcoeffOne
  simp [genusOneDenominator] at hcoeffOne
  have hnSq : n * n = n := by
    exact_mod_cast hcoeffOne
  have hnOne : n = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hn
    simpa using hnSq
  subst n
  have hden : genusOneDenominator cX = genusOneDenominator cY := by
    simp only [Nat.cast_one, Polynomial.C_1, one_mul] at hred
    exact mul_left_cancel₀ Polynomial.X_ne_zero hred
  have hcoeffOneDen := congrArg (fun p : Polynomial ℂ ↦ p.coeff 1) hden
  simp [genusOneDenominator] at hcoeffOneDen
  constructor
  · rfl
  · linear_combination hcoeffOneDen

/-- Exact conclusion of the displayed calculation in Remark 3.11: equality
of the two genus-one zeta candidates implies `n = 1` and equal parameters. -/
theorem remark_3_11_obstruction (n : ℕ) (hn : 0 < n) (cX cY : ℂ)
    (h : genusOneZetaCandidate (n * n) cY =
      genusOneZetaCandidate n cX) :
    n = 1 ∧ cX = cY := by
  apply genusOne_cross_eq_forces n hn cX cY
  have hdy :
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (genusOneDenominator cY) ≠ 0 := by
    simpa only [map_zero] using
      (RatFunc.algebraMap_injective ℂ).ne (genusOneDenominator_ne_zero cY)
  have hdx :
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (genusOneDenominator cX) ≠ 0 := by
    simpa only [map_zero] using
      (RatFunc.algebraMap_injective ℂ).ne (genusOneDenominator_ne_zero cX)
  have hcross := (div_eq_div_iff hdy hdx).mp h
  apply RatFunc.algebraMap_injective ℂ
  simpa only [map_mul] using hcross

end

end LeanCo.LaplacianLFunctions
