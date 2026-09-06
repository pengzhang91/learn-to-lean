import LeanCo.LaplacianLFunctions.RiemannRochConsequences
import LeanCo.LaplacianLFunctions.Zeta

/-!
# Proposition 3.8

This module packages both character cases of Proposition 3.8 of
arXiv:2608.29981 behind the paper's standing connectedness hypothesis.  The
nontrivial-character branch derives graph Riemann--Roch internally, so the
paper-facing statement exposes no additional Riemann--Roch assumption.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- Connected-graph wrapper for the nontrivial-character branch of
Proposition 3.8.  Riemann--Roch and Jacobian finiteness are both derived from
the connectedness instance. -/
theorem nontrivial_lFunction_polynomial_of_connected
    (G : LooplessMultigraph V) [Fact G.Connected]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (hchi : chi ≠ 1) :
    G.lFunction D₁ chi =
        (G.lPolynomial D₁ chi G.riemannRochBound :
          PowerSeries (Polynomial ℂ)) ∧
      (G.lPolynomial D₁ chi G.riemannRochBound).natDegree =
        G.riemannRochBound := by
  exact G.nontrivial_lFunction_polynomial_of_riemannRoch
    (G.riemannRochFormula_of_connected (Fact.out : G.Connected))
    D₁ chi hchi

/-- Proposition 3.8 in paper-facing form.  The trivial character gives the
intrinsic zeta function; every nontrivial character gives a polynomial of
exact `t`-degree `2g-2`, represented by `riemannRochBound`. -/
theorem proposition_3_8
    (G : LooplessMultigraph V) [Fact G.Connected]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ) :
    (chi = 1 ∧
        G.lFunction D₁ chi = G.zeta) ∨
      (chi ≠ 1 ∧
        G.lFunction D₁ chi =
            (G.lPolynomial D₁ chi G.riemannRochBound :
              PowerSeries (Polynomial ℂ)) ∧
        (G.lPolynomial D₁ chi G.riemannRochBound).natDegree =
          G.riemannRochBound) := by
  by_cases hchi : chi = 1
  · left
    refine ⟨hchi, ?_⟩
    subst chi
    exact G.lFunction_trivial_eq_zeta_of_connected D₁
  · right
    exact ⟨hchi, G.nontrivial_lFunction_polynomial_of_connected D₁ chi hchi⟩

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
