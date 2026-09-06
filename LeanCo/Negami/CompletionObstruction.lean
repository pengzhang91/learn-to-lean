import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

/-!
# Finite-support obstruction and completed inverse

This file formalizes Propositions 8.1 and 8.3 of arXiv:2608.30053.  Evaluation
at `t = 1` proves that the required denominators cannot be inverted by a
finite Laurent polynomial.  In the power-series completion, the inverse is
the shifted geometric series with every coefficient equal to `-1`.
-/

namespace LeanCo.Negami

open LaurentPolynomial
open scoped BigOperators

/-- Laurent Hilbert polynomial of a finite homogeneous basis. -/
noncomputable def finiteGradedHilbert {B : Type*} [Fintype B]
    (degree : B → ℤ) : LaurentPolynomial ℤ :=
  ∑ b : B, T (degree b)

/-- Coefficientwise nonnegativity, a necessary condition for a Hilbert
polynomial of an ordinary graded vector space. -/
def CoeffNonnegative (p : LaurentPolynomial ℤ) : Prop :=
  ∀ z : ℤ, 0 ≤ p z

/-- A negative one-dimensional monomial cannot be an ordinary Hilbert
polynomial. -/
theorem neg_monomial_not_coeffNonnegative (z : ℤ) :
    ¬ CoeffNonnegative (-(T z : LaurentPolynomial ℤ)) := by
  intro h
  have hz := h z
  simp at hz

/-- There is no finite Laurent-polynomial inverse of `t - 1`. -/
theorem no_laurent_inverse_t_sub_one :
    ¬ ∃ p : LaurentPolynomial ℤ, (T 1 - 1) * p = 1 := by
  rintro ⟨p, hp⟩
  have h := congrArg
    (LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)) hp
  simp at h

/-- In particular no finite graded basis realizes the first inverse entry. -/
theorem finiteGradedHilbert_not_inverse_t_sub_one
    {B : Type*} [Fintype B] (degree : B → ℤ) :
    (T 1 - 1) * finiteGradedHilbert degree ≠ 1 := by
  intro h
  exact no_laurent_inverse_t_sub_one ⟨finiteGradedHilbert degree, h⟩

/-- The second signed denominator in the two-boundary inverse is likewise
impossible in finite Laurent support. -/
theorem no_laurent_negative_inverse_t_mul_t_sub_one :
    ¬ ∃ p : LaurentPolynomial ℤ, (T 1 * (T 1 - 1)) * p = -1 := by
  rintro ⟨p, hp⟩
  have h := congrArg
    (LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)) hp
  simp at h

/-- No finite graded basis realizes the second signed inverse entry. -/
theorem finiteGradedHilbert_not_negative_inverse_t_mul_t_sub_one
    {B : Type*} [Fintype B] (degree : B → ℤ) :
    (T 1 * (T 1 - 1)) * finiteGradedHilbert degree ≠ -1 := by
  intro h
  exact no_laurent_negative_inverse_t_mul_t_sub_one
    ⟨finiteGradedHilbert degree, h⟩

/-- The completed realization of `1 / (t - 1)`. -/
def completedTSubOneInverse : PowerSeries ℤ := -(PowerSeries.mk 1)

/-- The formal geometric series is an actual inverse after completion. -/
theorem completedTSubOneInverse_spec :
    (PowerSeries.X - 1) * completedTSubOneInverse = 1 := by
  rw [completedTSubOneInverse]
  have h := PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  calc
    (PowerSeries.X - 1) * -PowerSeries.mk 1 =
        PowerSeries.mk 1 * (1 - PowerSeries.X) := by ring
    _ = 1 := h

/-- Every coefficient of the completed inverse is `-1`, expressing
`-(1 + t + t² + ⋯)`. -/
@[simp] theorem completedTSubOneInverse_coeff (n : ℕ) :
    PowerSeries.coeff n completedTSubOneInverse = -1 := by
  simp [completedTSubOneInverse]

/-! ## A locally finite infinite graded realization -/

/-- A `ℤ`-graded object with finite even and odd multiplicities in every
degree, supported in nonnegative internal degrees.  Natural-valued
multiplicities make local finiteness part of the data representation. -/
structure LocallyFiniteZGradedObject where
  evenMultiplicity : ℤ → ℕ
  oddMultiplicity : ℤ → ℕ
  even_eq_zero_of_neg : ∀ z < 0, evenMultiplicity z = 0
  odd_eq_zero_of_neg : ∀ z < 0, oddMultiplicity z = 0

namespace LocallyFiniteZGradedObject

/-- Multiplicity in a chosen homological parity. -/
def multiplicity (A : LocallyFiniteZGradedObject) (odd : Bool) (z : ℤ) : ℕ :=
  if odd then A.oddMultiplicity z else A.evenMultiplicity z

/-- The finite-dimensional vector space in one internal degree and one
homological parity. -/
abbrev gradedPiece (A : LocallyFiniteZGradedObject)
    (k : Type u) [Field k] (odd : Bool) (z : ℤ) : Type u :=
  Fin (A.multiplicity odd z) → k

/-- Every individual graded piece has the prescribed finite dimension. -/
theorem finrank_gradedPiece (A : LocallyFiniteZGradedObject)
    (k : Type u) [Field k] (odd : Bool) (z : ℤ) :
    Module.finrank k (A.gradedPiece k odd z) = A.multiplicity odd z := by
  change Module.finrank k (Fin (A.multiplicity odd z) → k) = _
  rw [Module.finrank_pi]
  exact Fintype.card_fin _

/-- Homological shift by one swaps even and odd pieces. -/
def homologicalShift (A : LocallyFiniteZGradedObject) :
    LocallyFiniteZGradedObject where
  evenMultiplicity := A.oddMultiplicity
  oddMultiplicity := A.evenMultiplicity
  even_eq_zero_of_neg := A.odd_eq_zero_of_neg
  odd_eq_zero_of_neg := A.even_eq_zero_of_neg

/-- Completed Euler series, with odd homological degree contributing a
minus sign. -/
def eulerSeries (A : LocallyFiniteZGradedObject) : PowerSeries ℤ :=
  PowerSeries.mk fun n ↦
    (A.evenMultiplicity n : ℤ) - (A.oddMultiplicity n : ℤ)

/-- A homological shift negates the completed Euler series. -/
theorem eulerSeries_homologicalShift (A : LocallyFiniteZGradedObject) :
    eulerSeries (homologicalShift A) = -eulerSeries A := by
  ext n
  simp [eulerSeries, homologicalShift]

/-- One even one-dimensional piece in every nonnegative internal degree. -/
def geometricObject : LocallyFiniteZGradedObject where
  evenMultiplicity z := if 0 ≤ z then 1 else 0
  oddMultiplicity _ := 0
  even_eq_zero_of_neg := by
    intro z hz
    simp [not_le.mpr hz]
  odd_eq_zero_of_neg := by simp

@[simp] theorem geometricObject_even_ofNat (n : ℕ) :
    geometricObject.evenMultiplicity n = 1 := by
  simp [geometricObject]

@[simp] theorem geometricObject_odd (z : ℤ) :
    geometricObject.oddMultiplicity z = 0 := by
  rfl

/-- The unshifted object's Hilbert/Euler series is the geometric series. -/
theorem eulerSeries_geometricObject :
    eulerSeries geometricObject = PowerSeries.mk 1 := by
  ext n
  simp [eulerSeries]

/-- The shifted infinite graded object realizes `1 / (t - 1)` in the
completed Euler theory. -/
theorem eulerSeries_shiftedGeometricObject :
    eulerSeries (homologicalShift geometricObject) =
      completedTSubOneInverse := by
  rw [eulerSeries_homologicalShift, eulerSeries_geometricObject]
  rfl

/-- Object-level completion of Proposition 8.3: the shifted geometric object
has Euler series inverse to `t - 1`. -/
theorem shiftedGeometricObject_inverse_spec :
    (PowerSeries.X - 1) *
        eulerSeries (homologicalShift geometricObject) = 1 := by
  rw [eulerSeries_shiftedGeometricObject]
  exact completedTSubOneInverse_spec

end LocallyFiniteZGradedObject

end LeanCo.Negami
