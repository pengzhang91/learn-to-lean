import LeanCo.LaplacianLFunctions.ZetaRationality

/-!
# Integral-to-complex base change for graph zeta functions

The integral series used to prove Proposition 3.3 maps coefficientwise to
the paper's complex-valued zeta series.  This closes the type-level bridge
between the integral numerator and Definition 3.1.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

/-- Coefficientwise inclusion `ℤ[u] → ℂ[u]`. -/
def intPolynomialToComplex : Polynomial ℤ →+* Polynomial ℂ :=
  Polynomial.mapRingHom (Int.castRingHom ℂ)

@[simp]
theorem intPolynomialToComplex_geometricPolynomial (h : ℕ) :
    intPolynomialToComplex (geometricPolynomial (R := ℤ) h) =
      geometricPolynomial (R := ℂ) h := by
  simp [intPolynomialToComplex, geometricPolynomial]

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- Every integral zeta coefficient maps to the corresponding complex
coefficient of Definition 3.1. -/
theorem intPolynomialToComplex_integralZetaCoefficient
    (G : LooplessMultigraph V) [Fintype G.Jacobian] (d : ℕ) :
    intPolynomialToComplex (G.integralZetaCoefficient d) =
      G.zetaCoefficient d := by
  classical
  simp [integralZetaCoefficient, zetaCoefficient,
    intPolynomialToComplex_geometricPolynomial]

/-- The integral zeta series maps coefficientwise to the paper's complex
zeta series. -/
theorem map_integralZeta_eq_zeta
    (G : LooplessMultigraph V) [Fintype G.Jacobian] :
    PowerSeries.map intPolynomialToComplex G.integralZeta = G.zeta := by
  apply PowerSeries.ext
  intro d
  rw [PowerSeries.coeff_map, G.coeff_integralZeta, G.coeff_zeta]
  exact G.intPolynomialToComplex_integralZetaCoefficient d

/-- The integral numerator viewed as a polynomial in `t` with complex
polynomial coefficients in `u`. -/
def complexZetaNumerator (G : LooplessMultigraph V)
    [Fintype G.Jacobian] : Polynomial (Polynomial ℂ) :=
  Polynomial.map intPolynomialToComplex G.integralZetaNumerator

@[simp]
theorem natDegree_complexZetaNumerator
    (G : LooplessMultigraph V) [Fintype G.Jacobian] :
    G.complexZetaNumerator.natDegree = G.integralZetaNumerator.natDegree := by
  apply Polynomial.natDegree_map_eq_of_injective
  intro p q hpq
  apply Polynomial.ext
  intro n
  have hcoeff := congrArg (fun r : Polynomial ℂ ↦ r.coeff n) hpq
  simpa [intPolynomialToComplex] using hcoeff

/-- Evaluation at `t = 1` commutes with the integral-to-complex map. -/
theorem eval_one_complexZetaNumerator
    (G : LooplessMultigraph V) [Fintype G.Jacobian] :
    Polynomial.eval 1 G.complexZetaNumerator =
      intPolynomialToComplex (Polynomial.eval 1 G.integralZetaNumerator) := by
  exact Polynomial.eval_one_map intPolynomialToComplex
    G.integralZetaNumerator

/-- Proposition 3.3's rationality identity after mapping the integral
numerator to the complex coefficient ring used by Definition 3.1. -/
theorem complexZeta_rationality
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1) :
    (1 - PowerSeries.X) *
        (1 - PowerSeries.C (Polynomial.X : Polynomial ℂ) * PowerSeries.X) *
        G.zeta =
      (G.complexZetaNumerator : PowerSeries (Polynomial ℂ)) := by
  have hmap := congrArg
    (fun s : PowerSeries (Polynomial ℤ) ↦
      PowerSeries.map intPolynomialToComplex s)
    (G.integralZeta_rationality hRR D₁)
  simp only [map_mul, map_sub, map_one, PowerSeries.map_X,
    PowerSeries.map_C] at hmap
  rw [G.map_integralZeta_eq_zeta] at hmap
  simpa [complexZetaNumerator, intPolynomialToComplex] using hmap

/-- Base change preserves the exact numerator degree. -/
theorem natDegree_complexZetaNumerator_of_riemannRoch
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1) :
    G.complexZetaNumerator.natDegree = G.zetaNumeratorBound := by
  rw [G.natDegree_complexZetaNumerator,
    G.natDegree_integralZetaNumerator hRR D₁]

/-- The mapped numerator still evaluates at `t = 1` to the Jacobian order. -/
theorem eval_one_complexZetaNumerator_of_riemannRoch
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1) :
    Polynomial.eval 1 G.complexZetaNumerator =
      (Fintype.card G.Jacobian : Polynomial ℂ) := by
  rw [G.eval_one_complexZetaNumerator,
    G.eval_one_integralZetaNumerator hRR D₁]
  simp [intPolynomialToComplex]

/-- Proposition 3.3 stated directly for Definition 3.1's complex zeta
series while retaining an integral bivariate numerator. -/
theorem proposition_3_3_complex
    (G : LooplessMultigraph V) [Fact G.Connected] :
    ∃ f : Polynomial (Polynomial ℤ),
      (1 - PowerSeries.X) *
          (1 - PowerSeries.C (Polynomial.X : Polynomial ℂ) *
            PowerSeries.X) *
          G.zeta =
            ((Polynomial.map intPolynomialToComplex f :
              Polynomial (Polynomial ℂ)) :
              PowerSeries (Polynomial ℂ)) ∧
        f.natDegree = G.zetaNumeratorBound ∧
        Polynomial.eval 1 f =
          (Fintype.card G.Jacobian : Polynomial ℤ) := by
  let v : V := Classical.choice (inferInstance : Nonempty V)
  let D₁ : G.PicardDegree 1 := G.vertexClass v
  have hRR : G.RiemannRochFormula :=
    G.riemannRochFormula_of_connected (Fact.out : G.Connected)
  refine ⟨G.integralZetaNumerator,
    G.complexZeta_rationality hRR D₁,
    G.natDegree_integralZetaNumerator hRR D₁,
    G.eval_one_integralZetaNumerator hRR D₁⟩

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
