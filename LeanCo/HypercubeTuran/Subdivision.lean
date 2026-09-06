import LeanCo.HypercubeTuran.Hypercube
import Mathlib.Data.Sym.Sym2

/-!
# The one-subdivision is layered

Poles are sent to singleton coordinate sets and subdivision vertices to the
two-element set of their endpoints.  This realizes `T₁(G)` inside the first
edge layer of a hypercube.
-/

open scoped SimpleGraph symmDiff

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

private noncomputable abbrev vertexIndex (V : Type u) [Fintype V] :
    V ≃ Fin (Fintype.card V) :=
  Fintype.equivFin V

/-- The concrete layer vertex assigned to a pole or subdivision vertex. -/
noncomputable def subdivisionLayerMap (x : SubdivisionVertex G) :
    {A : Finset (Fin (Fintype.card V)) // #A = 1 ∨ #A = 1 + 1} := by
  classical
  cases x with
  | inl v =>
      exact ⟨{vertexIndex V v}, by simp⟩
  | inr e =>
      refine ⟨e.1.toFinset.map (vertexIndex V).toEmbedding, Or.inr ?_⟩
      rw [Finset.card_map]
      exact Sym2.card_toFinset_of_not_isDiag e.1
        (G.not_isDiag_of_mem_edgeSet e.2)

@[simp]
theorem subdivisionLayerMap_pole (v : V) :
    (subdivisionLayerMap G (Sum.inl v)).1 = {vertexIndex V v} :=
  rfl

@[simp]
theorem subdivisionLayerMap_edge (e : G.edgeSet) :
    (subdivisionLayerMap G (Sum.inr e)).1 =
      e.1.toFinset.map (vertexIndex V).toEmbedding :=
  rfl

theorem subdivisionLayerMap_injective :
    Function.Injective (subdivisionLayerMap G) := by
  classical
  intro x y hxy
  cases x with
  | inl v =>
      cases y with
      | inl w =>
          have hs : {vertexIndex V v} = ({vertexIndex V w} :
              Finset (Fin (Fintype.card V))) := congrArg Subtype.val hxy
          exact congrArg Sum.inl ((vertexIndex V).injective
            (Finset.singleton_injective hs))
      | inr e =>
          have hc := congrArg (fun z => z.1.card) hxy
          simp only [subdivisionLayerMap_pole, subdivisionLayerMap_edge,
            Finset.card_singleton, Finset.card_map] at hc
          rw [Sym2.card_toFinset_of_not_isDiag e.1
            (G.not_isDiag_of_mem_edgeSet e.2)] at hc
          omega
  | inr e =>
      cases y with
      | inl v =>
          have hc := congrArg (fun z => z.1.card) hxy
          simp only [subdivisionLayerMap_pole, subdivisionLayerMap_edge,
            Finset.card_singleton, Finset.card_map] at hc
          rw [Sym2.card_toFinset_of_not_isDiag e.1
            (G.not_isDiag_of_mem_edgeSet e.2)] at hc
          omega
      | inr f =>
          apply congrArg Sum.inr
          apply Subtype.ext
          apply Sym2.ext
          intro v
          have hmapped :
              e.1.toFinset.map (vertexIndex V).toEmbedding =
                f.1.toFinset.map (vertexIndex V).toEmbedding := by
            exact congrArg Subtype.val hxy
          have hv : vertexIndex V v ∈
                e.1.toFinset.map (vertexIndex V).toEmbedding ↔
              vertexIndex V v ∈
                f.1.toFinset.map (vertexIndex V).toEmbedding := by
            rw [hmapped]
          simpa using hv

/-- Incidence with an endpoint becomes cube adjacency between the singleton
and the endpoint pair. -/
theorem subdivisionLayerMap_adj_of_mem (v : V) (e : G.edgeSet)
  (hve : v ∈ e.1) :
    (cubeEdgeLayer (Fin (Fintype.card V)) 1).Adj
      (subdivisionLayerMap G (Sum.inl v))
      (subdivisionLayerMap G (Sum.inr e)) := by
  classical
  change (hypercubeGraph (Fin (Fintype.card V))).Adj
    (subdivisionLayerMap G (Sum.inl v)).1
    (subdivisionLayerMap G (Sum.inr e)).1
  rw [hypercubeGraph_adj]
  obtain ⟨w, he⟩ := Sym2.mem_iff_exists.mp hve
  have hvw : v ≠ w := by
    intro hvw
    subst w
    exact G.not_isDiag_of_mem_edgeSet e.2 (he ▸ by simp)
  have hidx : vertexIndex V v ≠ vertexIndex V w :=
    (vertexIndex V).injective.ne hvw
  have hsd :
      ({vertexIndex V v} : Finset (Fin (Fintype.card V))) ∆
          {vertexIndex V v, vertexIndex V w} = {vertexIndex V w} := by
    ext x
    by_cases hx : x = vertexIndex V v
    · subst x
      simp [Finset.mem_symmDiff, hidx]
    · simp [Finset.mem_symmDiff, hx]
  rw [subdivisionLayerMap_pole, subdivisionLayerMap_edge, he,
    Sym2.toFinset_mk_eq]
  simp only [Finset.map_insert, Finset.map_singleton]
  change #(({vertexIndex V v} : Finset (Fin (Fintype.card V))) ∆
    {vertexIndex V v, vertexIndex V w}) = 1
  rw [hsd]
  simp

/-- The canonical copy of `T₁(G)` in the first edge layer. -/
noncomputable def oneSubdivisionLayerCopy :
    SimpleGraph.Copy (oneSubdivision G)
      (cubeEdgeLayer (Fin (Fintype.card V)) 1) where
  toHom :=
    { toFun := subdivisionLayerMap G
      map_rel' := by
        intro x y hxy
        cases x with
        | inl v =>
            cases y with
            | inl w => exact (not_oneSubdivision_adj_pole_pole v w hxy).elim
            | inr e =>
                exact subdivisionLayerMap_adj_of_mem G v e
                  ((oneSubdivision_adj_pole_edge v e).mp hxy)
        | inr e =>
            cases y with
            | inl v =>
                exact (subdivisionLayerMap_adj_of_mem G v e
                  ((oneSubdivision_adj_edge_pole e v).mp hxy)).symm
            | inr f => exact (not_oneSubdivision_adj_edge_edge e f hxy).elim }
  injective' := subdivisionLayerMap_injective G

/-- Every one-subdivision of a finite simple graph is layered. -/
theorem oneSubdivision_isLayered : IsLayered (oneSubdivision G) :=
  ⟨Fintype.card V, 1, ⟨oneSubdivisionLayerCopy G⟩⟩

end LeanCo.HypercubeTuran
