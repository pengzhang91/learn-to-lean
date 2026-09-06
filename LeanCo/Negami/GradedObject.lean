import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Pi

/-!
# Finite triply graded objects

This file gives a concrete model of the additive categorical objects used in
arXiv:2608.30053.  An object is a finite homogeneous basis with a tridegree.
Over a semiring `k`, its realization is the free finite-dimensional `k`-module
on that basis.  A degree-preserving basis equivalence therefore supplies an
honest graded linear equivalence.
-/

open scoped BigOperators

namespace LeanCo.Negami

/-- A tridegree records the exponents of `t`, `x`, and `y`. -/
structure Tridegree where
  t : ℕ
  x : ℕ
  y : ℕ
  deriving DecidableEq

@[ext] theorem Tridegree.ext {a b : Tridegree}
    (ht : a.t = b.t) (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a
  cases b
  simp_all

namespace Tridegree

instance : Zero Tridegree := ⟨⟨0, 0, 0⟩⟩
instance : Add Tridegree :=
  ⟨fun a b => ⟨a.t + b.t, a.x + b.x, a.y + b.y⟩⟩

@[simp] theorem zero_t : (0 : Tridegree).t = 0 := rfl
@[simp] theorem zero_x : (0 : Tridegree).x = 0 := rfl
@[simp] theorem zero_y : (0 : Tridegree).y = 0 := rfl
@[simp] theorem add_t (a b : Tridegree) : (a + b).t = a.t + b.t := rfl
@[simp] theorem add_x (a b : Tridegree) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : Tridegree) : (a + b).y = a.y + b.y := rfl

/-- One unit of component grading. -/
def tUnit : Tridegree := ⟨1, 0, 0⟩

/-- One unit of selected-edge grading. -/
def xUnit : Tridegree := ⟨0, 1, 0⟩

/-- One unit of unselected-edge grading. -/
def yUnit : Tridegree := ⟨0, 0, 1⟩

end Tridegree

/-- The monomial associated with a tridegree after choosing three scalars. -/
def gradeWeight {R : Type*} [CommSemiring R]
    (t x y : R) (d : Tridegree) : R :=
  t ^ d.t * x ^ d.x * y ^ d.y

@[simp] theorem gradeWeight_zero {R : Type*} [CommSemiring R]
    (t x y : R) : gradeWeight t x y 0 = 1 := by
  simp [gradeWeight]

theorem gradeWeight_add {R : Type*} [CommSemiring R]
    (t x y : R) (a b : Tridegree) :
    gradeWeight t x y (a + b) =
      gradeWeight t x y a * gradeWeight t x y b := by
  simp only [gradeWeight, Tridegree.add_t, Tridegree.add_x,
    Tridegree.add_y, pow_add]
  ac_rfl

@[simp] theorem gradeWeight_tUnit {R : Type*} [CommSemiring R]
    (t x y : R) : gradeWeight t x y Tridegree.tUnit = t := by
  simp [gradeWeight, Tridegree.tUnit]

@[simp] theorem gradeWeight_xUnit {R : Type*} [CommSemiring R]
    (t x y : R) : gradeWeight t x y Tridegree.xUnit = x := by
  simp [gradeWeight, Tridegree.xUnit]

@[simp] theorem gradeWeight_yUnit {R : Type*} [CommSemiring R]
    (t x y : R) : gradeWeight t x y Tridegree.yUnit = y := by
  simp [gradeWeight, Tridegree.yUnit]

/-- A finite based triply graded object.  Its canonical realization over `k`
is the function space from `Basis` to `k`. -/
structure GradedObject where
  Basis : Type*
  fintypeBasis : Fintype Basis
  degree : Basis → Tridegree

attribute [instance] GradedObject.fintypeBasis

namespace GradedObject

/-- The canonical free-module realization of a finite based object. -/
abbrev realization (A : GradedObject) (k : Type*) := A.Basis → k

/-- The Hilbert polynomial evaluated at three elements of a commutative
semiring. -/
noncomputable def hilbert {R : Type*} [CommSemiring R]
    (A : GradedObject) (t x y : R) : R :=
  ∑ b : A.Basis, gradeWeight t x y (A.degree b)

/-- An equivalence of finite graded objects is an equivalence of homogeneous
bases preserving all three degrees. -/
structure Equiv (A B : GradedObject) where
  basisEquiv : A.Basis ≃ B.Basis
  degree_eq : ∀ a, B.degree (basisEquiv a) = A.degree a

namespace Equiv

/-- A graded-basis equivalence induces a linear equivalence of the realized
finite-dimensional modules. -/
def toLinearEquiv {k : Type*} [Semiring k] {A B : GradedObject}
    (e : Equiv A B) : A.realization k ≃ₗ[k] B.realization k where
  toFun f b := f (e.basisEquiv.symm b)
  invFun f a := f (e.basisEquiv a)
  left_inv f := by funext a; simp
  right_inv f := by funext b; simp
  map_add' f g := rfl
  map_smul' c f := rfl

theorem hilbert_eq {R : Type*} [CommSemiring R]
    {A B : GradedObject} (e : Equiv A B) (t x y : R) :
    A.hilbert t x y = B.hilbert t x y := by
  classical
  exact Fintype.sum_equiv e.basisEquiv _ _ fun a => by
    rw [e.degree_eq]

end Equiv

/-- Direct sum, modeled on the disjoint union of bases. -/
abbrev sum (A B : GradedObject) : GradedObject := by
  exact {
    Basis := A.Basis ⊕ B.Basis
    fintypeBasis := inferInstance
    degree := Sum.elim A.degree B.degree }

/-- Tensor product, modeled on the product of bases. -/
abbrev tensor (A B : GradedObject) : GradedObject := by
  exact {
    Basis := A.Basis × B.Basis
    fintypeBasis := inferInstance
    degree p := A.degree p.1 + B.degree p.2 }

/-- Shift every homogeneous basis vector by the same tridegree. -/
abbrev shift (d : Tridegree) (A : GradedObject) : GradedObject where
  Basis := A.Basis
  fintypeBasis := inferInstance
  degree a := d + A.degree a

/-- Finite indexed direct sum. -/
abbrev sigma {ι : Type*} [Fintype ι]
    (A : ι → GradedObject) : GradedObject := by
  exact {
    Basis := Σ i, (A i).Basis
    fintypeBasis := inferInstance
    degree a := (A a.1).degree a.2 }

theorem hilbert_sum {R : Type*} [CommSemiring R]
    (A B : GradedObject) (t x y : R) :
    (sum A B).hilbert t x y = A.hilbert t x y + B.hilbert t x y := by
  classical
  simp [hilbert, sum]

theorem hilbert_tensor {R : Type*} [CommSemiring R]
    (A B : GradedObject) (t x y : R) :
    (tensor A B).hilbert t x y = A.hilbert t x y * B.hilbert t x y := by
  classical
  simp only [hilbert, tensor, gradeWeight_add]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  congr 1
  funext a
  rw [Finset.mul_sum]

theorem hilbert_shift {R : Type*} [CommSemiring R]
    (d : Tridegree) (A : GradedObject) (t x y : R) :
    (shift d A).hilbert t x y =
      gradeWeight t x y d * A.hilbert t x y := by
  classical
  simp only [hilbert, shift, gradeWeight_add]
  rw [Finset.mul_sum]

theorem hilbert_sigma {R : Type*} [CommSemiring R]
    {ι : Type*} [Fintype ι] (A : ι → GradedObject) (t x y : R) :
    (sigma A).hilbert t x y = ∑ i, (A i).hilbert t x y := by
  classical
  unfold hilbert
  change (∑ z : Σ i, (A i).Basis,
    gradeWeight t x y ((A z.1).degree z.2)) = _
  rw [show (Finset.univ : Finset (Σ i, (A i).Basis)) =
      Finset.univ.sigma (fun i => Finset.univ) by ext z; simp]
  simp only [Finset.sum_sigma]

end GradedObject

end LeanCo.Negami
