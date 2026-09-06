import LeanCo.Negami.TutteRank
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Mathlib.Tactic.FinCases

/-!
# Relation with the Tutte polynomial

The first part records the assumption-free Laurent regrading.  The second
part defines the actual two-variable Tutte state sum and polynomial on the
same finite edge states as `NegamiData`, and proves Corollary 2.3 after scalar
evaluation in a field.  The two denominator hypotheses are explicit.
-/

namespace LeanCo.Negami

abbrev TutteDegree := Fin 2 → ℤ
abbrev TutteVariable := Fin 2
abbrev LaurentNegamiDegree := Fin 3 → ℤ

/-- Rank of a spanning state, written `|V| - omega(S)`. -/
def stateRank (vertexCount components : ℕ) : ℤ :=
  (vertexCount : ℤ) - components

/-- Exponents of `(X-1)` and `(Y-1)` in the Tutte state sum. -/
def tutteStateDegree (vertexCount fullComponents stateComponents selected : ℕ) :
    TutteDegree := fun
  | 0 => stateRank vertexCount fullComponents - stateRank vertexCount stateComponents
  | 1 => (selected : ℤ) - stateRank vertexCount stateComponents

/-- Exponents of the prefactor `t^c x^r y^nu`. -/
def tuttePrefactor (vertexCount edgeCount fullComponents : ℕ) :
    LaurentNegamiDegree := fun
  | 0 => fullComponents
  | 1 => stateRank vertexCount fullComponents
  | 2 => (edgeCount : ℤ) - stateRank vertexCount fullComponents

/-- Effect on `(t,x,y)` exponents of substituting
`X-1 = t*y/x` and `Y-1 = x/y`. -/
def substituteTutteDegree (d : TutteDegree) : LaurentNegamiDegree := fun
  | 0 => d 0
  | 1 => -d 0 + d 1
  | 2 => d 0 - d 1

/-- The Laurent exponent vector of one Negami state. -/
def laurentNegamiStateDegree (edgeCount stateComponents selected : ℕ) :
    LaurentNegamiDegree := fun
  | 0 => stateComponents
  | 1 => selected
  | 2 => (edgeCount : ℤ) - selected

/-- Corollary 2.3 term by term: after the displayed substitution and
multiplication by the prefactor, each Tutte monomial has exactly the Negami
exponents. -/
theorem tutte_regrading_identity (vertexCount edgeCount fullComponents
    stateComponents selected : ℕ) :
    (fun i => tuttePrefactor vertexCount edgeCount fullComponents i +
      substituteTutteDegree
        (tutteStateDegree vertexCount fullComponents stateComponents selected) i) =
      laurentNegamiStateDegree edgeCount stateComponents selected := by
  funext i
  fin_cases i <;>
    simp [tuttePrefactor, substituteTutteDegree, tutteStateDegree,
      stateRank, laurentNegamiStateDegree] <;> omega

/-- The Negami state sum as a finite formal sum of Laurent exponent vectors. -/
noncomputable def formalNegamiLaurent (G : NegamiData) :
    LaurentNegamiDegree →₀ ℤ :=
  ∑ S : Finset G.Edge,
    Finsupp.single
      (laurentNegamiStateDegree (Nat.card G.Edge) (G.components S) S.card) 1

/-- The Tutte state sum after applying the substitution of Corollary 2.3 and
adding the prefactor exponent, but before evaluating any possibly vanishing
variable. -/
noncomputable def formalTutteSubstituted (G : NegamiData)
    (vertexCount : ℕ) : LaurentNegamiDegree →₀ ℤ :=
  ∑ S : Finset G.Edge,
    Finsupp.single
      (fun i =>
        tuttePrefactor vertexCount (Nat.card G.Edge) (G.components Finset.univ) i +
          substituteTutteDegree
            (tutteStateDegree vertexCount (G.components Finset.univ)
              (G.components S) S.card) i) 1

/-- Corollary 2.3 as an equality of complete finite Laurent state sums.  This
form is valid without division hypotheses; scalar specializations with the
paper's quotients follow whenever `x` and `y` are nonzero. -/
theorem formal_tutte_relation (G : NegamiData) (vertexCount : ℕ) :
    formalTutteSubstituted G vertexCount = formalNegamiLaurent G := by
  classical
  unfold formalTutteSubstituted formalNegamiLaurent
  apply Finset.sum_congr rfl
  intro S _
  rw [tutte_regrading_identity]

namespace NegamiData

variable (G : NegamiData)

/-- Natural-valued rank of a spanning state. -/
def natStateRank (vertexCount : ℕ) (S : Finset G.Edge) : ℕ :=
  vertexCount - G.components S

/-- The graph rank `r(G)`. -/
def natFullRank (vertexCount : ℕ) : ℕ :=
  G.natStateRank vertexCount Finset.univ

/-- The nullity `|S| - r(S)` of a spanning state. -/
def stateNullity (vertexCount : ℕ) (S : Finset G.Edge) : ℕ :=
  S.card - G.natStateRank vertexCount S

/-- The three elementary inequalities needed for the natural-exponent Tutte
state sum.  Concrete graph data have these properties: components are
bounded by vertices, adding all edges can only merge components, and a state
of rank `r` contains at least `r` edges. -/
structure TutteAdmissible (vertexCount : ℕ) : Prop where
  components_le_vertices : ∀ S, G.components S ≤ vertexCount
  fullComponents_le : ∀ S, G.components Finset.univ ≤ G.components S
  rank_le_selected : ∀ S, G.natStateRank vertexCount S ≤ S.card

/-- The standard two-variable Tutte state sum
`sum (X-1)^(r(G)-r(S)) (Y-1)^(|S|-r(S))`. -/
noncomputable def tutteStateSum {R : Type*} [CommRing R]
    (vertexCount : ℕ) (X Y : R) : R :=
  ∑ S : Finset G.Edge,
    (X - 1) ^ (G.natFullRank vertexCount - G.natStateRank vertexCount S) *
      (Y - 1) ^ G.stateNullity vertexCount S

/-- Evaluation point for the two Tutte variables. -/
def tutteEvalPoint {R : Type*} (X Y : R) : TutteVariable → R :=
  fun i ↦ if i = 0 then X else Y

/-- The actual Tutte polynomial, defined by its finite spanning-state sum. -/
noncomputable def tuttePolynomial (vertexCount : ℕ)
    (R : Type*) [CommRing R] : MvPolynomial TutteVariable R :=
  ∑ S : Finset G.Edge,
    (MvPolynomial.X 0 - 1) ^
        (G.natFullRank vertexCount - G.natStateRank vertexCount S) *
      (MvPolynomial.X 1 - 1) ^ G.stateNullity vertexCount S

/-- Evaluating the formal Tutte polynomial gives the scalar state sum. -/
theorem eval_tuttePolynomial {R : Type*} [CommRing R]
    (vertexCount : ℕ) (X Y : R) :
    MvPolynomial.eval (tutteEvalPoint X Y) (G.tuttePolynomial vertexCount R) =
      G.tutteStateSum vertexCount X Y := by
  classical
  simp [tuttePolynomial, tutteStateSum, tutteEvalPoint]

private theorem scalar_regrading_term
    {F : Type*} [Field F] (t x y : F) (hx : x ≠ 0) (hy : y ≠ 0)
    (c r ν a b w s m : ℕ)
    (ht : c + a = w) (hxx : r + b = s + a)
    (hyy : ν + a = (m - s) + b) :
    t ^ c * x ^ r * y ^ ν * (t * y / x) ^ a * (x / y) ^ b =
      t ^ w * x ^ s * y ^ (m - s) := by
  rw [div_pow, div_pow]
  field_simp [pow_ne_zero _ hx, pow_ne_zero _ hy]
  calc
    t ^ c * x ^ r * y ^ ν * (t * y) ^ a * x ^ b =
        t ^ (c + a) * x ^ (r + b) * y ^ (ν + a) := by
      simp [mul_pow, pow_add]
      ring
    _ = x ^ a * y ^ b * t ^ w * x ^ s * y ^ (m - s) := by
      rw [ht, hxx, hyy]
      simp [pow_add]
      ring

/-- The scalar regrading identity for one actual state of admissible Tutte
data. -/
theorem tutte_term_relation (vertexCount : ℕ)
    (hG : G.TutteAdmissible vertexCount) (S : Finset G.Edge)
    {F : Type*} [Field F] (t x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    t ^ G.components Finset.univ * x ^ G.natFullRank vertexCount *
        y ^ (Nat.card G.Edge - G.natFullRank vertexCount) *
        (t * y / x) ^
          (G.natFullRank vertexCount - G.natStateRank vertexCount S) *
        (x / y) ^ G.stateNullity vertexCount S =
      t ^ G.components S * x ^ S.card *
        y ^ (Nat.card G.Edge - S.card) := by
  have hwv := hG.components_le_vertices S
  have hcv := hG.components_le_vertices Finset.univ
  have hcw := hG.fullComponents_le S
  have hrs := hG.rank_le_selected S
  have hrm := hG.rank_le_selected Finset.univ
  have hsm : S.card ≤ Nat.card G.Edge := by
    simpa [Nat.card_eq_fintype_card] using Finset.card_le_univ S
  have huniv : (Finset.univ : Finset G.Edge).card = Nat.card G.Edge := by
    simp [Nat.card_eq_fintype_card]
  have ha : G.natFullRank vertexCount - G.natStateRank vertexCount S =
      G.components S - G.components Finset.univ := by
    simp only [natFullRank, natStateRank]
    omega
  have hrDecomp : G.natFullRank vertexCount =
      G.natStateRank vertexCount S +
        (G.components S - G.components Finset.univ) := by
    simp only [natFullRank, natStateRank]
    omega
  have hnull : G.stateNullity vertexCount S +
      G.natStateRank vertexCount S = S.card := by
    exact Nat.sub_add_cancel hrs
  have hrFull : G.natFullRank vertexCount ≤ Nat.card G.Edge := by
    rw [← huniv]
    exact hrm
  apply scalar_regrading_term t x y hx hy
  · rw [ha]
    omega
  · rw [ha]
    omega
  · rw [ha]
    omega

/-- Corollary 2.3 as the scalar identity stated in the paper. -/
theorem stateSum_eq_tutte_specialization (vertexCount : ℕ)
    (hG : G.TutteAdmissible vertexCount)
    {F : Type*} [Field F] (t x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    G.stateSum t x y =
      t ^ G.components Finset.univ * x ^ G.natFullRank vertexCount *
        y ^ (Nat.card G.Edge - G.natFullRank vertexCount) *
        G.tutteStateSum vertexCount (1 + t * y / x) (1 + x / y) := by
  classical
  unfold stateSum tutteStateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  simp only [add_sub_cancel_left]
  simpa only [mul_assoc] using
    (G.tutte_term_relation vertexCount hG S t x y hx hy).symm

/-- Polynomial-evaluation form of Corollary 2.3. -/
theorem stateSum_eq_eval_tuttePolynomial (vertexCount : ℕ)
    (hG : G.TutteAdmissible vertexCount)
    {F : Type*} [Field F] (t x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    G.stateSum t x y =
      t ^ G.components Finset.univ * x ^ G.natFullRank vertexCount *
        y ^ (Nat.card G.Edge - G.natFullRank vertexCount) *
        MvPolynomial.eval
          (tutteEvalPoint (1 + t * y / x) (1 + x / y))
          (G.tuttePolynomial vertexCount F) := by
  rw [G.eval_tuttePolynomial]
  exact G.stateSum_eq_tutte_specialization vertexCount hG t x y hx hy

end NegamiData

namespace FiniteMultigraph

variable (G : FiniteMultigraph)

/-- Every state's spanning simple graph is a subgraph of the full graph. -/
theorem stateGraph_le_full (S : Finset G.Edge) :
    G.stateGraph S ≤ G.stateGraph Finset.univ := by
  intro u v huv
  rw [stateGraph, SimpleGraph.fromEdgeSet_adj] at huv ⊢
  refine ⟨?_, huv.2⟩
  obtain ⟨e, heS, he⟩ := Finset.mem_image.mp huv.1
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he⟩

/-- The number of components of a spanning state is bounded by the number
of vertices. -/
theorem omega_le_card_vertex (S : Finset G.Edge) :
    G.omega S ≤ Nat.card G.Vertex := by
  unfold omega StateComponent
  exact Nat.card_le_card_of_surjective
    (Quotient.mk' (s := G.stateSetoid S)) Quotient.mk_surjective

/-- Adding all graph edges cannot increase the component count. -/
theorem omega_full_le (S : Finset G.Edge) :
    G.omega Finset.univ ≤ G.omega S := by
  unfold omega StateComponent stateSetoid
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le (G.stateGraph_le_full S)

/-- Every concrete finite labelled multigraph supplies all inequalities
needed by the natural-exponent Tutte state sum. -/
theorem tutteAdmissible :
    G.toNegamiData.TutteAdmissible (Nat.card G.Vertex) where
  components_le_vertices S := G.omega_le_card_vertex S
  fullComponents_le S := G.omega_full_le S
  rank_le_selected S := by
    change Nat.card G.Vertex - G.omega S ≤ S.card
    exact G.card_vertex_sub_omega_le_card S

/-- The standard Tutte state sum of a concrete finite labelled multigraph. -/
noncomputable abbrev tutteStateSum {R : Type*} [CommRing R] (X Y : R) : R :=
  G.toNegamiData.tutteStateSum (Nat.card G.Vertex) X Y

/-- The standard two-variable Tutte polynomial of a concrete finite labelled
multigraph. -/
noncomputable abbrev tuttePolynomial (R : Type*) [CommRing R] :
    MvPolynomial TutteVariable R :=
  G.toNegamiData.tuttePolynomial (Nat.card G.Vertex) R

/-- The concrete polynomial expanded over all labelled spanning states. -/
theorem tuttePolynomial_eq_state_sum (R : Type*) [CommRing R] :
    G.tuttePolynomial R =
      ∑ S : Finset G.Edge,
        (MvPolynomial.X 0 - 1) ^
            ((Nat.card G.Vertex - G.omega Finset.univ) -
              (Nat.card G.Vertex - G.omega S)) *
          (MvPolynomial.X 1 - 1) ^
            (S.card - (Nat.card G.Vertex - G.omega S)) :=
  rfl

/-- Evaluation of the concrete Tutte polynomial is its spanning-state sum. -/
theorem eval_tuttePolynomial {R : Type*} [CommRing R] (X Y : R) :
    MvPolynomial.eval (NegamiData.tutteEvalPoint X Y) (G.tuttePolynomial R) =
      G.tutteStateSum X Y :=
  G.toNegamiData.eval_tuttePolynomial (Nat.card G.Vertex) X Y

/-- Corollary 2.3 for every finite labelled multigraph, with no graph-side
premise and with the two division hypotheses displayed explicitly. -/
theorem stateSum_eq_tutte_specialization
    {F : Type*} [Field F] (t x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    G.stateSum t x y =
      t ^ G.omega Finset.univ *
        x ^ G.toNegamiData.natFullRank (Nat.card G.Vertex) *
        y ^ (Nat.card G.Edge -
          G.toNegamiData.natFullRank (Nat.card G.Vertex)) *
        G.tutteStateSum (1 + t * y / x) (1 + x / y) := by
  exact G.toNegamiData.stateSum_eq_tutte_specialization
    (Nat.card G.Vertex) G.tutteAdmissible t x y hx hy

/-- Polynomial-evaluation form of the concrete Corollary 2.3 endpoint. -/
theorem stateSum_eq_eval_tuttePolynomial
    {F : Type*} [Field F] (t x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    G.stateSum t x y =
      t ^ G.omega Finset.univ *
        x ^ G.toNegamiData.natFullRank (Nat.card G.Vertex) *
        y ^ (Nat.card G.Edge -
          G.toNegamiData.natFullRank (Nat.card G.Vertex)) *
        MvPolynomial.eval
          (NegamiData.tutteEvalPoint (1 + t * y / x) (1 + x / y))
          (G.tuttePolynomial F) := by
  rw [G.eval_tuttePolynomial]
  exact G.stateSum_eq_tutte_specialization t x y hx hy

end FiniteMultigraph

end LeanCo.Negami
