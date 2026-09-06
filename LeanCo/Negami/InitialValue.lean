import LeanCo.Negami.FiniteGraph
import Mathlib.Tactic

/-!
# The isolated-vertex initial value

The empty spanning state has one connected component per vertex.  If the
entire edge type is empty, it is the unique state, so both the scalar state
sum and the multivariate polynomial reduce to the initial monomial from
Definition 2.1.
-/

namespace LeanCo.Negami
namespace FiniteMultigraph

variable (G : FiniteMultigraph)

theorem stateGraph_empty : G.stateGraph ∅ = ⊥ := by
  ext u v
  simp [stateGraph]

/-- Components of the empty spanning state are canonically its vertices. -/
noncomputable def stateComponentEmptyEquiv :
    G.StateComponent ∅ ≃ G.Vertex where
  toFun := Quotient.lift id (by
    intro u v huv
    change (G.stateGraph ∅).Reachable u v at huv
    rw [G.stateGraph_empty, SimpleGraph.reachable_bot] at huv
    exact huv)
  invFun v := @Quotient.mk' _ (G.stateSetoid ∅) v
  left_inv c := by
    induction c using Quotient.inductionOn with
    | _ v => rfl
  right_inv v := rfl

@[simp] theorem omega_empty : G.omega ∅ = Nat.card G.Vertex := by
  unfold omega
  exact Nat.card_congr G.stateComponentEmptyEquiv

/-- An edge-free graph has the paper's scalar initial value. -/
theorem stateSum_of_isEmpty [IsEmpty G.Edge]
    {R : Type*} [CommSemiring R] (t x y : R) :
    G.stateSum t x y = t ^ Nat.card G.Vertex := by
  classical
  have hstates : (Finset.univ : Finset (Finset G.Edge)) = {∅} := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim S ∅
  unfold FiniteMultigraph.stateSum NegamiData.stateSum
  rw [hstates]
  simp [G.omega_empty]

/-- An edge-free graph has a single component-grading monomial. -/
theorem polynomial_of_isEmpty [IsEmpty G.Edge]
    (R : Type*) [CommSemiring R] :
    G.polynomial R =
      MvPolynomial.monomial (Finsupp.single 0 (Nat.card G.Vertex)) 1 := by
  classical
  have hstates : (Finset.univ : Finset (Finset G.Edge)) = {∅} := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim S ∅
  unfold FiniteMultigraph.polynomial NegamiData.polynomial
  rw [hstates]
  simp [NegamiData.degree, G.omega_empty]

/-- The finite multigraph with vertex type `V` and no edges. -/
def edgeless (V : Type) [Fintype V] [DecidableEq V] : FiniteMultigraph where
  Vertex := V
  Edge := Empty
  ends e := Empty.elim e

/-- The paper's graph on `n` isolated labelled vertices. -/
def isolated (n : ℕ) : FiniteMultigraph :=
  edgeless (Fin n)

@[simp] theorem isolated_stateSum (n : ℕ)
    {R : Type*} [CommSemiring R] (t x y : R) :
    (isolated n).stateSum t x y = t ^ n := by
  letI : IsEmpty (isolated n).Edge := by
    dsimp [isolated, edgeless]
    infer_instance
  simpa [isolated, edgeless] using (isolated n).stateSum_of_isEmpty t x y

@[simp] theorem isolated_polynomial (n : ℕ)
    (R : Type*) [CommSemiring R] :
    (isolated n).polynomial R =
      MvPolynomial.monomial (Finsupp.single 0 n) 1 := by
  letI : IsEmpty (isolated n).Edge := by
    dsimp [isolated, edgeless]
    infer_instance
  simpa [isolated, edgeless] using (isolated n).polynomial_of_isEmpty R

end FiniteMultigraph
end LeanCo.Negami
