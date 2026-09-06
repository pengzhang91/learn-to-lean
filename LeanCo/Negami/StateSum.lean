import LeanCo.Negami.GradedObject
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/-!
# The Negami state sum and its finite categorification

This file formalizes Sections 2--3 of arXiv:2608.30053.  The small abstract
record `NegamiData` isolates the finite state-sum calculation.  The graph
files instantiate it with the actual number of connected components of a
spanning subgraph.

The categorification is concrete: its homogeneous basis is the finite type
of edge states itself, and its realization is the free module on that basis.
-/

open scoped BigOperators

namespace LeanCo.Negami

/-- Variable indices in the polynomial presentation: `t`, `x`, and `y`. -/
abbrev Degree := Fin 3

/-- The finite data read from a spanning-subgraph state sum. -/
structure NegamiData where
  Edge : Type
  edgeFintype : Fintype Edge
  edgeDecidableEq : DecidableEq Edge
  components : Finset Edge → ℕ

attribute [instance] NegamiData.edgeFintype NegamiData.edgeDecidableEq

namespace NegamiData

variable (G : NegamiData)

/-- The multivariate exponent vector `(components, selected, unselected)`. -/
noncomputable def degree (S : Finset G.Edge) : Degree →₀ ℕ :=
  Finsupp.single 0 (G.components S) + Finsupp.single 1 S.card +
    Finsupp.single 2 (Nat.card G.Edge - S.card)

/-- The same degree as an explicit tridegree. -/
noncomputable def triDegree (S : Finset G.Edge) : Tridegree :=
  ⟨G.components S, S.card, Nat.card G.Edge - S.card⟩

@[simp] theorem degree_zero (S : Finset G.Edge) :
    G.degree S 0 = G.components S := by
  simp [degree]

@[simp] theorem degree_one (S : Finset G.Edge) :
    G.degree S 1 = S.card := by
  simp [degree]

@[simp] theorem degree_two (S : Finset G.Edge) :
    G.degree S 2 = Nat.card G.Edge - S.card := by
  simp [degree]

/-- Equation (2.1), as an honest multivariate polynomial. -/
noncomputable def polynomial (R : Type*) [CommSemiring R] : MvPolynomial Degree R :=
  ∑ S : Finset G.Edge, MvPolynomial.monomial (G.degree S) 1

/-- Equation (2.1), evaluated at three elements of a commutative semiring. -/
noncomputable def stateSum {R : Type*} [CommSemiring R]
    (t x y : R) : R :=
  ∑ S : Finset G.Edge,
    t ^ G.components S * x ^ S.card * y ^ (Nat.card G.Edge - S.card)

/-- Evaluation point for the variables ordered as `(t,x,y)`. -/
def evalPoint {R : Type*} (t x y : R) : Degree → R :=
  Fin.cases t (Fin.cases x (fun _ => y))

private theorem degree_prod {R : Type*} [CommSemiring R]
    (t x y : R) (a b c : ℕ) :
    (Finsupp.single (0 : Degree) a + Finsupp.single 1 b +
        Finsupp.single 2 c).prod
      (fun i e => evalPoint t x y i ^ e) = t ^ a * x ^ b * y ^ c := by
  rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add])]
  rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add])]
  have h0 : (Finsupp.single (0 : Degree) a).prod
      (fun i e => evalPoint t x y i ^ e) = t ^ a := by
    rw [Finsupp.prod_single_index]
    · rfl
    · simp
  have h1 : (Finsupp.single (1 : Degree) b).prod
      (fun i e => evalPoint t x y i ^ e) = x ^ b := by
    rw [Finsupp.prod_single_index]
    · rfl
    · simp
  have h2 : (Finsupp.single (2 : Degree) c).prod
      (fun i e => evalPoint t x y i ^ e) = y ^ c := by
    rw [Finsupp.prod_single_index]
    · rfl
    · simp
  rw [h0, h1, h2]

/-- The additive categorification from Theorem 3.2. -/
noncomputable abbrev stateObject : GradedObject := {
  Basis := Finset G.Edge
  fintypeBasis := inferInstance
  degree := G.triDegree
}

/-- Decategorification of the state object is exactly the Negami state sum. -/
theorem hilbert_stateObject {R : Type*} [CommSemiring R] (t x y : R) :
    G.stateObject.hilbert t x y = G.stateSum t x y := by
  rfl

/-- The polynomial presentation evaluates to the scalar state sum. -/
theorem eval_polynomial {R : Type*} [CommSemiring R] (t x y : R) :
    MvPolynomial.eval (evalPoint t x y) (G.polynomial R) =
      G.stateSum t x y := by
  classical
  simp only [polynomial, MvPolynomial.eval_sum, MvPolynomial.eval_monomial,
    stateSum, one_mul]
  apply Finset.sum_congr rfl
  intro S _
  exact degree_prod t x y _ _ _

/-- The multiplicity of a homogeneous tridegree. -/
noncomputable def gradedMultiplicity (d : Tridegree) : ℕ :=
  ∑ S : Finset G.Edge, if G.triDegree S = d then 1 else 0

/-- The paper's graded vector space, degree by degree. -/
noncomputable def gradedPiece (G : NegamiData) (k : Type u) [Field k]
    (d : Tridegree) : Type u :=
  Fin (G.gradedMultiplicity d) → k

noncomputable instance (k : Type*) [Field k] (d : Tridegree) :
    AddCommGroup (G.gradedPiece k d) := Pi.addCommGroup

noncomputable instance (k : Type*) [Field k] (d : Tridegree) :
    Module k (G.gradedPiece k d) := Pi.module _ _ _

/-- Each graded piece has precisely the state multiplicity prescribed by the
state sum. -/
theorem finrank_gradedPiece (k : Type*) [Field k] (d : Tridegree) :
    Module.finrank k (G.gradedPiece k d) = G.gradedMultiplicity d := by
  change Module.finrank k (Fin (G.gradedMultiplicity d) → k) = _
  rw [Module.finrank_pi]
  exact Fintype.card_fin _

/-- A degree-preserving bijection of states. -/
structure StateEquiv (G H : NegamiData) where
  states : Finset G.Edge ≃ Finset H.Edge
  degree_eq : ∀ S, H.triDegree (states S) = G.triDegree S

namespace StateEquiv

/-- A state equivalence gives an equivalence of the categorifying objects. -/
def objectEquiv {G H : NegamiData} (W : StateEquiv G H) :
    GradedObject.Equiv G.stateObject H.stateObject where
  basisEquiv := W.states
  degree_eq := W.degree_eq

/-- Consequently every scalar realization of the state sum is invariant. -/
theorem stateSum_eq {G H : NegamiData} (W : StateEquiv G H)
    {R : Type*} [CommSemiring R] (t x y : R) :
    G.stateSum t x y = H.stateSum t x y := by
  calc
    G.stateSum t x y = G.stateObject.hilbert t x y :=
      (G.hilbert_stateObject t x y).symm
    _ = H.stateObject.hilbert t x y := W.objectEquiv.hilbert_eq t x y
    _ = H.stateSum t x y := H.hilbert_stateObject t x y

end StateEquiv

/-- Selected and unselected exponents add to the total number of edges. -/
theorem degree_selected_add_unselected (S : Finset G.Edge) :
    G.degree S 1 + G.degree S 2 = Nat.card G.Edge := by
  classical
  simp [degree]
  exact Nat.add_sub_of_le
    (by simpa [Nat.card_eq_fintype_card] using Finset.card_le_univ S)

end NegamiData

end LeanCo.Negami
