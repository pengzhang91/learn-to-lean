import LeanCo.LaplacianLFunctions.JacobianFinite
import LeanCo.LaplacianLFunctions.LFunction
import LeanCo.LaplacianLFunctions.PicardSplitting

/-!
# The two-variable graph zeta function

Definition 3.1 of arXiv:2608.29981 sums the geometric polynomial attached to
`h(C)` over all divisor classes `C`, recording the degree by a power of `t`.
We package it intrinsically as a formal power series: its coefficient of
`t^d` is the sum over the fixed-degree Picard slice `Pic^d(G)`.

We also prove the trivial-character part of Proposition 3.8.  Relative to any
degree-one base class, Jacobian coordinates enumerate `Pic^d(G)`; therefore
the trivially twisted `L`-coefficient is exactly the intrinsic zeta
coefficient.  No rationality statement is made in this file.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- Translation by `d D₁` identifies the Jacobian with the degree-`d`
Picard slice. -/
def jacobianEquivPicardDegree (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (d : ℤ) :
    G.Jacobian ≃ G.PicardDegree d where
  toFun a := ⟨G.classInDegree D₁ d a,
    G.picardDegree_classInDegree D₁ d a⟩
  invFun C := G.jacobianCoordinate D₁ C.1
  left_inv a := by
    simpa only [classInDegree] using
      G.jacobianCoordinate_jacobian_add_zsmul D₁ a d
  right_inv C := by
    apply Subtype.ext
    simpa only [classInDegree, C.2] using
      G.jacobianCoordinate_add_degree D₁ C.1

/-- Every fixed-degree Picard slice is finite once the Jacobian is finite. -/
noncomputable instance picardDegreeFintype (G : LooplessMultigraph V)
    [Fintype G.Jacobian] (d : ℤ) : Fintype (G.PicardDegree d) := by
  let root : V := Classical.choice (inferInstance : Nonempty V)
  exact Fintype.ofEquiv G.Jacobian
    (G.jacobianEquivPicardDegree (G.vertexClass root) d)

/-- The coefficient of `t^d` in the intrinsic graph zeta function. -/
def zetaCoefficient (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (d : ℕ) : Polynomial ℂ :=
  ∑ C : G.PicardDegree (d : ℤ),
    geometricPolynomial (R := ℂ) (G.h (C : G.Picard))

/-- Definition 3.1: the two-variable graph zeta function, interpreted as a
formal power series in `t` with polynomial coefficients in `u`. -/
def zeta (G : LooplessMultigraph V) [Fintype G.Jacobian] :
    PowerSeries (Polynomial ℂ) :=
  PowerSeries.mk G.zetaCoefficient

@[simp]
theorem coeff_zeta (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (d : ℕ) :
    PowerSeries.coeff d G.zeta = G.zetaCoefficient d := by
  simp [zeta]

/-- At the trivial character, each `L`-coefficient is the intrinsic zeta
coefficient. -/
theorem lCoefficient_trivial_eq_zetaCoefficient
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (d : ℕ) :
    G.lCoefficient D₁ (1 : AddChar G.Jacobian ℂ) d =
      G.zetaCoefficient d := by
  classical
  simp only [lCoefficient, AddChar.one_apply, Polynomial.C_1,
    one_mul, zetaCoefficient]
  exact Fintype.sum_equiv
    (G.jacobianEquivPicardDegree D₁ (d : ℤ))
    (fun a : G.Jacobian ↦
      geometricPolynomial (R := ℂ)
        (G.h (G.classInDegree D₁ (d : ℤ) a)))
    (fun C : G.PicardDegree (d : ℤ) ↦
      geometricPolynomial (R := ℂ) (G.h (C : G.Picard)))
    (fun _ ↦ rfl)

/-- Proposition 3.8 for the trivial additive character: for every choice of
degree-one base class, the `L`-function is the intrinsic zeta function. -/
theorem lFunction_trivial_eq_zeta
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) :
    G.lFunction D₁ (1 : AddChar G.Jacobian ℂ) = G.zeta := by
  apply PowerSeries.ext
  intro d
  rw [G.coeff_lFunction D₁ (1 : AddChar G.Jacobian ℂ) d,
    G.coeff_zeta d]
  exact G.lCoefficient_trivial_eq_zetaCoefficient D₁ d

/-- Connected-graph specialization, with Jacobian finiteness supplied by
`JacobianFinite`. -/
theorem lFunction_trivial_eq_zeta_of_connected
    (G : LooplessMultigraph V) [Fact G.Connected]
    (D₁ : G.PicardDegree 1) :
    G.lFunction D₁ (1 : AddChar G.Jacobian ℂ) = G.zeta :=
  G.lFunction_trivial_eq_zeta D₁

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
