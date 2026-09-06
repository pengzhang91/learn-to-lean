import LeanCo.CyclicBraidArrangement.CharacteristicBridge
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Fintype.Lattice
import Mathlib.FieldTheory.Finiteness

/-!
# An independent Whitney polynomial for the deformation arrangement

This file builds the arrangement from its actual integer equations.  In
particular, none of the definitions below mention the cyclic formula.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

variable {n : ℕ}

/-- An oriented forbidden equation `x_target - x_source = distance`.

Using both orientations duplicates the zero translate.  This is harmless for
inclusion--exclusion (and will make the comparison with the paper's ordered
clockwise-distance inequalities literal).
-/
abbrev ForbiddenEquation (M : DeformationMatrix n) :=
  Σ a : Fin n, Σ b : {b : Fin n // b ≠ a}, Fin (M.entry a b + 1)

namespace ForbiddenEquation

variable (M : DeformationMatrix n)

def source (e : M.ForbiddenEquation) : Fin n := e.1

def target (e : M.ForbiddenEquation) : Fin n := e.2.1

def distance (e : M.ForbiddenEquation) : ℕ := e.2.2.1

theorem source_ne_target (e : M.ForbiddenEquation) : e.source M ≠ e.target M := by
  exact (e.2.1.2).symm

theorem distance_le (e : M.ForbiddenEquation) :
    e.distance M ≤ M.entry (e.source M) (e.target M) := by
  exact Nat.le_of_lt_succ e.2.2.2

end ForbiddenEquation

noncomputable instance forbiddenEquationFintype (M : DeformationMatrix n) :
    Fintype M.ForbiddenEquation := Fintype.ofFinite _

noncomputable instance forbiddenEquationDecidableEq (M : DeformationMatrix n) :
    DecidableEq M.ForbiddenEquation := Classical.decEq _

/-- Satisfaction of one integer defining equation after base change to a ring. -/
def SatisfiesEquation (M : DeformationMatrix n) {R : Type*}
    [Ring R] (x : Fin n → R) (e : M.ForbiddenEquation) : Prop :=
  x (e.target M) - x (e.source M) = (e.distance M : R)

/-- The actual complement of the defining equations over a finite ring. -/
def FiniteFieldComplement (M : DeformationMatrix n) (R : Type*)
    [Ring R] :=
  {x : Fin n → R // ∀ e : M.ForbiddenEquation, ¬ M.SatisfiesEquation x e}

/-- A subset of equations is integrally consistent if it has a simultaneous
integer solution.  For difference equations this is equivalent to nonempty
intersection over `ℚ`, but the integral form is stronger and constructive. -/
def IntegrallyConsistent (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) : Prop :=
  ∃ p : Fin n → ℤ, ∀ e ∈ S, M.SatisfiesEquation p e

noncomputable local instance integrallyConsistentDecidable (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) : Decidable (M.IntegrallyConsistent S) :=
  Classical.propDecidable _

/-- The unoriented graph underlying a set of defining equations. -/
def equationGraph (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b ↦
    ∃ e ∈ S, e.source M = a ∧ e.target M = b

theorem equationGraph_adj_of_mem (M : DeformationMatrix n)
    {S : Finset M.ForbiddenEquation} {e : M.ForbiddenEquation} (he : e ∈ S) :
    (M.equationGraph S).Adj (e.source M) (e.target M) := by
  change (SimpleGraph.fromRel fun a b ↦
    ∃ e ∈ S, e.source M = a ∧ e.target M = b).Adj
      (e.source M) (e.target M)
  rw [SimpleGraph.fromRel_adj]
  exact ⟨e.source_ne_target M, Or.inl ⟨e, he, rfl, rfl⟩⟩

/-- Number of connected components of the equation graph.  `Nat.card` keeps
the definition independent of the particular synthesized `Fintype` instance. -/
noncomputable def equationComponentCount (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) : ℕ :=
  Nat.card (M.equationGraph S).ConnectedComponent

/-- Whitney's subset expansion for the integral difference arrangement.
Inconsistent intersections contribute zero; a consistent intersection has
one free parameter for each connected component of its underlying graph. -/
noncomputable def whitneyCharacteristicPolynomial (M : DeformationMatrix n) :
    Polynomial ℚ := by
  classical
  exact ∑ S : Finset M.ForbiddenEquation,
      if M.IntegrallyConsistent S then
        (-1 : Polynomial ℚ) ^ S.card *
          Polynomial.X ^ M.equationComponentCount S
      else 0

@[simp] theorem eval_whitneyCharacteristicPolynomial
    (M : DeformationMatrix n) (t : ℚ) :
    Polynomial.eval t M.whitneyCharacteristicPolynomial =
      ∑ S : Finset M.ForbiddenEquation,
        if M.IntegrallyConsistent S then
          (-1 : ℚ) ^ S.card *
            t ^ M.equationComponentCount S
        else 0 := by
  classical
  rw [whitneyCharacteristicPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases h : M.IntegrallyConsistent S
  · simp [h]
  · simp [h]

/-- Simultaneous solutions of a selected family of equations. -/
def EquationSolutions (M : DeformationMatrix n) (R : Type*) [Ring R]
    (S : Finset M.ForbiddenEquation) :=
  {x : Fin n → R // ∀ e ∈ S, M.SatisfiesEquation x e}

/-- Solutions of the homogeneous equations underlying a selected family. -/
def HomogeneousSolutions (M : DeformationMatrix n) (R : Type*)
    (S : Finset M.ForbiddenEquation) :=
  {x : Fin n → R // ∀ e ∈ S, x (e.target M) = x (e.source M)}

noncomputable instance equationSolutionsFintype (M : DeformationMatrix n)
    (R : Type*) [Ring R] [Fintype R] (S : Finset M.ForbiddenEquation) :
    Fintype (M.EquationSolutions R S) := by
  letI : Finite R := Finite.of_fintype R
  letI : Finite (Fin n → R) := by infer_instance
  letI : Finite (M.EquationSolutions R S) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance homogeneousSolutionsFintype (M : DeformationMatrix n)
    (R : Type*) [Fintype R] (S : Finset M.ForbiddenEquation) :
    Fintype (M.HomogeneousSolutions R S) := by
  letI : Finite R := Finite.of_fintype R
  letI : Finite (Fin n → R) := by infer_instance
  letI : Finite (M.HomogeneousSolutions R S) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance finiteFieldComplementFintype (M : DeformationMatrix n)
    (R : Type*) [Ring R] [Fintype R] : Fintype (M.FiniteFieldComplement R) := by
  letI : Finite R := Finite.of_fintype R
  letI : Finite (Fin n → R) := by infer_instance
  letI : Finite (M.FiniteFieldComplement R) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private theorem homogeneous_eq_of_adj (M : DeformationMatrix n)
    {R : Type*} {S : Finset M.ForbiddenEquation}
    (x : M.HomogeneousSolutions R S) {a b : Fin n}
    (hab : (M.equationGraph S).Adj a b) : x.1 a = x.1 b := by
  change (SimpleGraph.fromRel fun a b ↦
    ∃ e ∈ S, e.source M = a ∧ e.target M = b).Adj a b at hab
  rw [SimpleGraph.fromRel_adj] at hab
  rcases hab.2 with h | h
  · rcases h with ⟨e, he, rfl, rfl⟩
    exact (x.2 e he).symm
  · rcases h with ⟨e, he, rfl, rfl⟩
    exact x.2 e he

/-- Homogeneous solutions are exactly arbitrary functions on the connected
components of the underlying equation graph. -/
noncomputable def componentFunctionsEquivHomogeneous
    (M : DeformationMatrix n) (R : Type*)
    (S : Finset M.ForbiddenEquation) :
    ((M.equationGraph S).ConnectedComponent → R) ≃
      M.HomogeneousSolutions R S where
  toFun c := ⟨fun v ↦ c ((M.equationGraph S).connectedComponentMk v), by
    intro e he
    exact congrArg c (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (M.equationGraph_adj_of_mem he)).symm⟩
  invFun x := SimpleGraph.ConnectedComponent.lift x.1 (fun a b p ↦ by
    induction p with
    | nil => intro _; rfl
    | cons h p ih =>
        intro hp
        exact (homogeneous_eq_of_adj M x h).trans (ih hp.of_cons))
  left_inv c := by
    funext C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ v => rfl
  right_inv x := by
    apply Subtype.ext
    funext v
    rfl

/-- Consequently, over a finite coefficient type, a homogeneous intersection
has `|R|^c` points, where `c` is its number of graph components. -/
theorem card_homogeneousSolutions (M : DeformationMatrix n)
    (R : Type*) [Fintype R] (S : Finset M.ForbiddenEquation) :
    Fintype.card (M.HomogeneousSolutions R S) =
      Fintype.card R ^ M.equationComponentCount S := by
  classical
  rw [← Fintype.card_congr (M.componentFunctionsEquivHomogeneous R S),
    Fintype.card_fun, equationComponentCount, Nat.card_eq_fintype_card]

/-- Translation by an integral solution identifies a nonempty affine
intersection over any ring with its homogeneous intersection. -/
noncomputable def equationSolutionsEquivHomogeneousOfIntegral
    (M : DeformationMatrix n) {R : Type*} [CommRing R]
    (S : Finset M.ForbiddenEquation) (p : Fin n → ℤ)
    (hp : ∀ e ∈ S, M.SatisfiesEquation p e) :
    M.EquationSolutions R S ≃ M.HomogeneousSolutions R S where
  toFun x := ⟨fun v ↦ x.1 v - (p v : R), by
    intro e he
    have hx := x.2 e he
    have hz := hp e he
    have hzR := congrArg (fun z : ℤ ↦ (z : R)) hz
    change x.1 (e.target M) - x.1 (e.source M) = (e.distance M : R) at hx
    push_cast at hzR
    change x.1 (e.target M) - (p (e.target M) : R) =
      x.1 (e.source M) - (p (e.source M) : R)
    linear_combination hx - hzR⟩
  invFun y := ⟨fun v ↦ y.1 v + (p v : R), by
    intro e he
    have hy := y.2 e he
    have hz := hp e he
    have hzR := congrArg (fun z : ℤ ↦ (z : R)) hz
    push_cast at hzR
    change (y.1 (e.target M) + (p (e.target M) : R)) -
      (y.1 (e.source M) + (p (e.source M) : R)) =
        (e.distance M : R)
    linear_combination hy + hzR⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    simp
  right_inv y := by
    apply Subtype.ext
    funext v
    simp

/-- Every integrally consistent selected intersection has the expected
finite-ring cardinality. -/
theorem card_equationSolutions_of_integrallyConsistent
    (M : DeformationMatrix n) (R : Type*) [CommRing R] [Fintype R]
    (S : Finset M.ForbiddenEquation) (hS : M.IntegrallyConsistent S) :
    Fintype.card (M.EquationSolutions R S) =
      Fintype.card R ^ M.equationComponentCount S := by
  classical
  rcases hS with ⟨p, hp⟩
  rw [Fintype.card_congr (M.equationSolutionsEquivHomogeneousOfIntegral S p hp),
    M.card_homogeneousSolutions R S]

private noncomputable def equationEvent (M : DeformationMatrix n)
    (R : Type*) [Ring R] [Fintype R] (e : M.ForbiddenEquation) :
    Finset (Fin n → R) := by
  classical
  exact Finset.univ.filter fun x ↦ M.SatisfiesEquation x e

private noncomputable def equationIntersection (M : DeformationMatrix n)
    (R : Type*) [Ring R] [Fintype R] (S : Finset M.ForbiddenEquation) :
    Finset (Fin n → R) := by
  classical
  exact S.inf (M.equationEvent R)

private noncomputable def equationComplementIntersection
    (M : DeformationMatrix n) (R : Type*) [Ring R] [Fintype R] :
    Finset (Fin n → R) := by
  classical
  exact (Finset.univ : Finset M.ForbiddenEquation).inf
    (fun e ↦ (M.equationEvent R e)ᶜ)

private theorem mem_inf_equationEvent_iff (M : DeformationMatrix n)
    (R : Type*) [Ring R] [Fintype R]
    (S : Finset M.ForbiddenEquation) (x : Fin n → R) :
    x ∈ M.equationIntersection R S ↔
      ∀ e ∈ S, M.SatisfiesEquation x e := by
  classical
  unfold equationIntersection
  rw [Finset.mem_inf]
  simp [equationEvent]

private theorem mem_inf_compl_equationEvent_iff (M : DeformationMatrix n)
    (R : Type*) [Ring R] [Fintype R] (x : Fin n → R) :
    x ∈ M.equationComplementIntersection R ↔
      ∀ e : M.ForbiddenEquation, ¬ M.SatisfiesEquation x e := by
  classical
  unfold equationComplementIntersection
  rw [Finset.mem_inf]
  simp [equationEvent]

private theorem card_inf_equationEvent (M : DeformationMatrix n)
    (R : Type*) [Ring R] [Fintype R]
    (S : Finset M.ForbiddenEquation) :
    (M.equationIntersection R S).card =
      Fintype.card (M.EquationSolutions R S) := by
  classical
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦
    M.mem_inf_equationEvent_iff R S x)

private theorem card_inf_compl_equationEvent (M : DeformationMatrix n)
    (R : Type*) [Ring R] [Fintype R] :
    (M.equationComplementIntersection R).card =
      Fintype.card (M.FiniteFieldComplement R) := by
  classical
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦
    M.mem_inf_compl_equationEvent_iff R x)

/-- Inclusion--exclusion for the actual complement of the integer defining
equations after base change to any finite ring. -/
theorem card_finiteFieldComplement_eq_inclusionExclusion
    (M : DeformationMatrix n) (R : Type*) [Ring R] [Fintype R] :
    (Fintype.card (M.FiniteFieldComplement R) : ℤ) =
      ∑ S : Finset M.ForbiddenEquation,
        (-1 : ℤ) ^ S.card * Fintype.card (M.EquationSolutions R S) := by
  classical
  have h := Finset.inclusion_exclusion_card_inf_compl
    (Finset.univ : Finset M.ForbiddenEquation) (M.equationEvent R)
  have hcomp :
      ((Finset.univ : Finset M.ForbiddenEquation).inf
        (fun e ↦ (M.equationEvent R e)ᶜ)).card =
          Fintype.card (M.FiniteFieldComplement R) := by
    simpa [equationComplementIntersection] using
      M.card_inf_compl_equationEvent R
  rw [hcomp] at h
  have hinter (S : Finset M.ForbiddenEquation) :
      (S.inf (M.equationEvent R)).card =
        Fintype.card (M.EquationSolutions R S) := by
    simpa [equationIntersection] using M.card_inf_equationEvent R S
  simpa [hinter] using h

end DeformationMatrix

end CyclicBraidArrangement
