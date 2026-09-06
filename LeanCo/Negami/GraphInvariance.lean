import LeanCo.Negami.FiniteGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Tactic.FinCases

/-!
# Invariance under finite multigraph isomorphism

An isomorphism consists of independent equivalences of vertices and labelled
edges that commute with the unordered-endpoint maps.  This file transports
states, connected components, the graded state object, and both versions of
the Negami state sum along such an isomorphism.
-/

namespace LeanCo.Negami
namespace FiniteMultigraph

/-- Isomorphism of labelled finite multigraphs. -/
structure Iso (G H : FiniteMultigraph) where
  vertexEquiv : G.Vertex ≃ H.Vertex
  edgeEquiv : G.Edge ≃ H.Edge
  map_ends : ∀ e,
    H.ends (edgeEquiv e) = Sym2.map vertexEquiv (G.ends e)

namespace Iso

variable {G H : FiniteMultigraph} (f : Iso G H)

private theorem sym2_map_injective {A B : Type*} (g : A → B)
    (hg : Function.Injective g) : Function.Injective (Sym2.map g) := by
  intro z w h
  induction z using Sym2.inductionOn with
  | _ a b =>
    induction w using Sym2.inductionOn with
    | _ c d =>
      simp only [Sym2.map_mk] at h ⊢
      rcases Sym2.eq_iff.mp h with h | h
      · exact Sym2.eq_iff.mpr (Or.inl ⟨hg h.1, hg h.2⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨hg h.1, hg h.2⟩)

/-- Transport an edge state along the edge equivalence. -/
def mapState (S : Finset G.Edge) : Finset H.Edge :=
  f.edgeEquiv.finsetCongr S

@[simp] theorem mem_mapState (S : Finset G.Edge) (e : G.Edge) :
    f.edgeEquiv e ∈ f.mapState S ↔ e ∈ S := by
  simp [mapState, Equiv.finsetCongr_apply]

theorem card_mapState (S : Finset G.Edge) :
    (f.mapState S).card = S.card := by
  simp [mapState, Equiv.finsetCongr_apply]

include f in theorem card_edge : Nat.card H.Edge = Nat.card G.Edge :=
  (Nat.card_congr f.edgeEquiv).symm

/-- The vertex equivalence restricts to an isomorphism of every pair of
corresponding spanning simple graphs. -/
noncomputable def stateGraphIso (S : Finset G.Edge) :
    G.stateGraph S ≃g H.stateGraph (f.mapState S) where
  toEquiv := f.vertexEquiv
  map_rel_iff' := by
    intro u v
    rw [stateGraph, stateGraph, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.fromEdgeSet_adj]
    constructor
    · rintro ⟨hm, hne⟩
      rcases Finset.mem_image.mp hm with ⟨b, hb, hbEnds⟩
      rw [mapState, Equiv.finsetCongr_apply] at hb
      rcases Finset.mem_map.mp hb with ⟨a, ha, rfl⟩
      have hmap : Sym2.map f.vertexEquiv (G.ends a) =
          Sym2.map f.vertexEquiv s(u, v) := by
        rw [← f.map_ends a]
        simpa [Sym2.map_mk] using hbEnds
      have hEnds : G.ends a = s(u, v) :=
        sym2_map_injective f.vertexEquiv f.vertexEquiv.injective hmap
      refine ⟨Finset.mem_image.mpr ⟨a, ha, hEnds⟩, ?_⟩
      exact fun huv ↦ hne (congrArg f.vertexEquiv huv)
    · rintro ⟨hm, hne⟩
      rcases Finset.mem_image.mp hm with ⟨a, ha, haEnds⟩
      refine ⟨Finset.mem_image.mpr ⟨f.edgeEquiv a, ?_, ?_⟩, ?_⟩
      · exact (f.mem_mapState S a).mpr ha
      · rw [f.map_ends a, haEnds, Sym2.map_mk]
      · exact f.vertexEquiv.injective.ne hne

/-- State connectivity is preserved and reflected by a graph isomorphism. -/
theorem stateConnected_map_iff (S : Finset G.Edge) (u v : G.Vertex) :
    H.StateConnected (f.mapState S) (f.vertexEquiv u) (f.vertexEquiv v) ↔
      G.StateConnected S u v := by
  exact f.stateGraphIso S |>.reachable_iff

/-- Corresponding states have the same number of connected components. -/
theorem omega_mapState (S : Finset G.Edge) :
    H.omega (f.mapState S) = G.omega S := by
  unfold omega StateComponent stateSetoid
  exact (Nat.card_congr (f.stateGraphIso S).connectedComponentEquiv).symm

theorem triDegree_mapState (S : Finset G.Edge) :
    H.toNegamiData.triDegree (f.mapState S) =
      G.toNegamiData.triDegree S := by
  have hcomp := f.omega_mapState S
  have hstate := f.card_mapState S
  have hedge := f.card_edge
  change
    (⟨H.omega (f.mapState S), (f.mapState S).card,
      Nat.card H.Edge - (f.mapState S).card⟩ : Tridegree) =
      ⟨G.omega S, S.card, Nat.card G.Edge - S.card⟩
  simp only [Tridegree.mk.injEq]
  omega

theorem degree_mapState (S : Finset G.Edge) :
    H.toNegamiData.degree (f.mapState S) =
      G.toNegamiData.degree S := by
  have hcomp := f.omega_mapState S
  have hstate := f.card_mapState S
  have hedge := f.card_edge
  have hedge' : Fintype.card H.Edge = Fintype.card G.Edge := by
    simpa only [Nat.card_eq_fintype_card] using hedge
  ext i
  fin_cases i <;>
    simp [NegamiData.degree, hcomp, hstate, hedge']

/-- The concrete graph isomorphism supplies the abstract state equivalence. -/
noncomputable def toStateEquiv :
    NegamiData.StateEquiv G.toNegamiData H.toNegamiData where
  states := f.edgeEquiv.finsetCongr
  degree_eq := f.triDegree_mapState

/-- Theorem 3.2's object-level graph invariance. -/
noncomputable def stateObjectEquiv :
    GradedObject.Equiv G.stateObject H.stateObject :=
  NegamiData.StateEquiv.objectEquiv (toStateEquiv f)

include f

/-- The scalar state sum is a finite-multigraph invariant. -/
theorem stateSum_eq {R : Type*} [CommSemiring R] (t x y : R) :
    G.stateSum t x y = H.stateSum t x y :=
  NegamiData.StateEquiv.stateSum_eq (toStateEquiv f) t x y

/-- The multivariate polynomial is a finite-multigraph invariant. -/
theorem polynomial_eq (R : Type*) [CommSemiring R] :
    G.polynomial R = H.polynomial R := by
  classical
  unfold FiniteMultigraph.polynomial NegamiData.polynomial
  exact Fintype.sum_equiv (f.edgeEquiv.finsetCongr) _ _ fun S ↦ by
    change MvPolynomial.monomial (G.toNegamiData.degree S) 1 =
      MvPolynomial.monomial (H.toNegamiData.degree (f.mapState S)) 1
    rw [degree_mapState f S]

end Iso
end FiniteMultigraph
end LeanCo.Negami
