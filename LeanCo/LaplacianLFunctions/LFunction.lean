import LeanCo.LaplacianLFunctions.EffectiveRank
import LeanCo.LaplacianLFunctions.GeometricPolynomial
import LeanCo.LaplacianLFunctions.Characters
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The two-variable graph `L`-function

For a degree-one Picard class `D₁`, every class of nonnegative degree `d`
has a unique presentation `a + d D₁`, with `a` in the Jacobian.  This file
uses that presentation to define the paper's series as an honest element of
`(ℂ[u])[[t]]`.  In particular, no expression with a negative exponent of
`t` is needed.

The coefficient of `t¹u⁰` is isolated explicitly.  It is the Fourier
transform of the indicator of the effective degree-one classes, which is the
only coefficient needed by the reconstruction theorem.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- The Picard class of degree `d` represented by `a + d D₁`. -/
def classInDegree (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (d : ℤ) (a : G.Jacobian) : G.Picard :=
  (a : G.Picard) + d • (D₁ : G.Picard)

@[simp]
theorem picardDegree_classInDegree (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (d : ℤ) (a : G.Jacobian) :
    G.picardDegree (G.classInDegree D₁ d a) = d := by
  simp [classInDegree, a.2, D₁.2]

/-- The coefficient of `t^d` in the graph `L`-function.  The polynomial
`P_h(u)` is represented by `geometricPolynomial h`. -/
def lCoefficient (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ) (d : ℕ) :
    Polynomial ℂ :=
  ∑ a : G.Jacobian,
    Polynomial.C (chi a) *
      geometricPolynomial (R := ℂ) (G.h (G.classInDegree D₁ (d : ℤ) a))

/-- Definition 3.6, rigorously interpreted as a formal power series in `t`
whose coefficients are polynomials in `u`. -/
def lFunction (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ) :
    PowerSeries (Polynomial ℂ) :=
  PowerSeries.mk (G.lCoefficient D₁ chi)

@[simp]
theorem coeff_lFunction (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ) (d : ℕ) :
    PowerSeries.coeff d (G.lFunction D₁ chi) =
      G.lCoefficient D₁ chi d := by
  simp [lFunction]

/-- Complex-valued indicator of effective degree-one classes in Jacobian
coordinates relative to `D₁`. -/
def degreeOneEffectiveIndicator (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (a : G.Jacobian) : ℂ :=
  if 0 < G.h (G.classInDegree D₁ 1 a) then 1 else 0

@[simp]
theorem degreeOneEffectiveIndicator_eq_one_iff
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (a : G.Jacobian) :
    G.degreeOneEffectiveIndicator D₁ a = 1 ↔
      0 < G.h (G.classInDegree D₁ 1 a) := by
  constructor
  · intro hind
    by_contra hp
    have hnot : ¬ 0 < G.h (G.classInDegree D₁ 1 a) := hp
    rw [degreeOneEffectiveIndicator, if_neg hnot] at hind
    exact zero_ne_one hind
  · intro hp
    rw [degreeOneEffectiveIndicator, if_pos hp]

@[simp]
theorem degreeOneEffectiveIndicator_ne_zero_iff
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (a : G.Jacobian) :
    G.degreeOneEffectiveIndicator D₁ a ≠ 0 ↔
      0 < G.h (G.classInDegree D₁ 1 a) := by
  constructor
  · intro hind
    by_contra hp
    have hnot : ¬ 0 < G.h (G.classInDegree D₁ 1 a) := hp
    rw [degreeOneEffectiveIndicator, if_neg hnot] at hind
    exact hind rfl
  · intro hp
    rw [degreeOneEffectiveIndicator, if_pos hp]
    exact one_ne_zero

/-- The constant coefficient in `u` of the `t¹` coefficient is precisely a
character-weighted sum of the effective-class indicator. -/
theorem coeff_zero_lCoefficient_one (G : LooplessMultigraph V)
    [Fintype G.Jacobian] (D₁ : G.PicardDegree 1)
    (chi : AddChar G.Jacobian ℂ) :
    (G.lCoefficient D₁ chi 1).coeff 0 =
      ∑ a : G.Jacobian, G.degreeOneEffectiveIndicator D₁ a * chi a := by
  classical
  simp only [lCoefficient]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, coeff_zero_geometricPolynomial,
    degreeOneEffectiveIndicator]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hz : G.h (G.classInDegree D₁ 1 a) = 0
  · simp [hz]
  · have hp : 0 < G.h (G.classInDegree D₁ 1 a) := Nat.pos_of_ne_zero hz
    simp [hz, hp, mul_comm]

/-- Evaluating the `u`-polynomial coefficient at `u = 1` replaces
`P_h(u)` by `h`. -/
theorem eval_one_lCoefficient (G : LooplessMultigraph V)
    [Fintype G.Jacobian] (D₁ : G.PicardDegree 1)
    (chi : AddChar G.Jacobian ℂ) (d : ℕ) :
    Polynomial.eval 1 (G.lCoefficient D₁ chi d) =
      ∑ a : G.Jacobian,
        (G.h (G.classInDegree D₁ (d : ℤ) a) : ℂ) * chi a := by
  classical
  simp only [lCoefficient]
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    eval_one_geometricPolynomial]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Equality of all `L`-functions implies equality of all their coefficients.
This small projection lemma keeps the main proof independent of extensionality
details of formal power series. -/
theorem lCoefficient_eq_of_lFunction_eq (G : LooplessMultigraph V)
    [Fintype G.Jacobian] (D₁ : G.PicardDegree 1)
    {chi psi : AddChar G.Jacobian ℂ}
    (hEq : G.lFunction D₁ chi = G.lFunction D₁ psi) (d : ℕ) :
    G.lCoefficient D₁ chi d = G.lCoefficient D₁ psi d := by
  have := congrArg (PowerSeries.coeff d) hEq
  simpa using this

/-- Equality of the paper's full `L`-functions, with characters transported
along a Jacobian isomorphism, recovers the effective degree-one indicator.
Only the `t¹u⁰` coefficient is used in the proof. -/
theorem degreeOneEffectiveIndicator_transport_of_lFunction_eq
    {V' : Type*} [Fintype V'] [Nonempty V'] [DecidableEq V']
    (G : LooplessMultigraph V) (G' : LooplessMultigraph V')
    [Fintype G.Jacobian] [Fintype G'.Jacobian]
    (D₁ : G.PicardDegree 1) (D₁' : G'.PicardDegree 1)
    (phi : G'.Jacobian ≃+ G.Jacobian)
    (hL : ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁' (chi.compAddMonoidHom phi.toAddMonoidHom)) :
    ∀ a' : G'.Jacobian,
      G.degreeOneEffectiveIndicator D₁ (phi a') =
        G'.degreeOneEffectiveIndicator D₁' a' := by
  apply eq_comp_addEquiv_of_forall_character_sum_eq phi
  intro chi
  have hcoeff := congrArg
    (fun F : PowerSeries (Polynomial ℂ) ↦
      (PowerSeries.coeff 1 F).coeff 0) (hL chi)
  simpa only [coeff_lFunction, coeff_zero_lCoefficient_one,
    AddChar.compAddMonoidHom_apply, AddEquiv.coe_toAddMonoidHom] using hcoeff

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
