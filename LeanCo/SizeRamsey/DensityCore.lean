import LeanCo.SizeRamsey.GraphBasics
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Dense connected cores

This file formalizes the minimal-vertex-set argument used in Claim 4.1 of the
paper.  A finite graph of scaled average degree at least `2 * d` has a
connected contained induced core with the same average-degree lower bound and
minimum degree strictly greater than `d`.

The assumption `0 < d` is necessary in this weak-average formulation: for
`d = 0`, a single isolated vertex satisfies the average-degree hypothesis but
not the strict minimum-degree conclusion.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u v

variable {V : Type u} {W : Type v}

noncomputable local instance connectedComponentFintype
    {G : SimpleGraph V} [Finite V] (C : G.ConnectedComponent) : Fintype C :=
  Fintype.ofFinite C

local instance connectedComponentToSimpleGraphDecidableAdj
    {G : SimpleGraph V} [DecidableRel G.Adj] (C : G.ConnectedComponent) :
    DecidableRel C.toSimpleGraph.Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x.val y.val))

/-! ## Invariance and connected-component bookkeeping -/

/-- Graph isomorphisms preserve the choice-free edge count. -/
theorem edgeCount_eq_of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : edgeCount G = edgeCount H := by
  unfold edgeCount
  exact Nat.card_congr e.mapEdgeSet

/-- A scaled average-degree lower bound is invariant under graph isomorphism. -/
theorem HasAverageDegreeAtLeast.map_iso {G : SimpleGraph V} {H : SimpleGraph W}
    {d : Nat} (h : HasAverageDegreeAtLeast G d) (e : G ≃g H) :
    HasAverageDegreeAtLeast H d := by
  unfold HasAverageDegreeAtLeast at h ⊢
  rw [← Nat.card_congr e.toEquiv, ← edgeCount_eq_of_iso e]
  exact h

/-- The sigma type of the supports of all connected components is equivalent
to the original vertex type. -/
noncomputable def sigmaConnectedComponentEquiv (G : SimpleGraph V) :
    (Σ C : G.ConnectedComponent, C) ≃ V :=
  (Equiv.sigmaCongrRight fun C =>
      Equiv.subtypeEquivProp
        (funext fun x => propext (ConnectedComponent.mem_supp_iff C x))).trans
    (Equiv.sigmaFiberEquiv G.connectedComponentMk)

@[simp]
theorem sigmaConnectedComponentEquiv_apply (G : SimpleGraph V)
    (x : Σ C : G.ConnectedComponent, C) :
    sigmaConnectedComponentEquiv G x = x.2.val :=
  rfl

/-- The vertex cardinality is the sum of the cardinalities of the connected
components. -/
theorem card_eq_sum_card_connectedComponents (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    Fintype.card V = ∑ C : G.ConnectedComponent, Fintype.card C := by
  rw [← Fintype.card_sigma]
  exact (Fintype.card_congr (sigmaConnectedComponentEquiv G)).symm

/-- Cardinality of a finset regarded as a set subtype. -/
theorem card_coe_finset_set [Fintype V] [DecidableEq V] (S : Finset V) :
    Fintype.card (S : Set V) = #S := by
  calc
    Fintype.card (S : Set V) = Fintype.card S :=
      Fintype.card_congr (Finset.equivToSet S).symm
    _ = #S := Fintype.card_coe S

/-- Passing to a connected component preserves the degree of each of its
vertices, since all neighbours lie in the same component. -/
theorem degree_connectedComponent_toSimpleGraph (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (C : G.ConnectedComponent) (x : C) :
    C.toSimpleGraph.degree x = G.degree x.val := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  apply Fintype.card_congr
  exact
    { toFun := fun y => ⟨y.val.val, y.prop⟩
      invFun := fun y =>
        ⟨⟨y.val, C.mem_supp_of_adj_mem_supp x.prop y.prop⟩, y.prop⟩
      left_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        rfl }

/-- The degree sum decomposes as the sum of the degree sums of the connected
components. -/
theorem sum_degrees_eq_sum_connectedComponents (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (∑ x : V, G.degree x) =
      ∑ C : G.ConnectedComponent, ∑ x : C, C.toSimpleGraph.degree x := by
  calc
    (∑ x : V, G.degree x) =
        ∑ z : Σ C : G.ConnectedComponent, C, G.degree z.2.val := by
      exact Fintype.sum_equiv (sigmaConnectedComponentEquiv G).symm _ _ fun _ => rfl
    _ = ∑ C : G.ConnectedComponent, ∑ x : C, G.degree x.val := by
      rw [Fintype.sum_sigma]
    _ = ∑ C : G.ConnectedComponent, ∑ x : C, C.toSimpleGraph.degree x := by
      apply Finset.sum_congr rfl
      intro C _
      apply Finset.sum_congr rfl
      intro x _
      exact (degree_connectedComponent_toSimpleGraph G C x).symm

/-- At least one connected component has average degree at least that of the
whole graph, in the scaled inequality sense. -/
theorem exists_connectedComponent_hasAverageDegreeAtLeast
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] {d : Nat} (hG : HasAverageDegreeAtLeast G d) :
    ∃ C : G.ConnectedComponent, HasAverageDegreeAtLeast C.toSimpleGraph d := by
  rw [hasAverageDegreeAtLeast_iff_sum_degrees] at hG
  by_contra h
  push Not at h
  have hlt (C : G.ConnectedComponent) :
      (∑ x : C, C.toSimpleGraph.degree x) < d * Fintype.card C := by
    rw [← not_le]
    intro hle
    exact h C ((hasAverageDegreeAtLeast_iff_sum_degrees C.toSimpleGraph).2 hle)
  have hsum_lt :
      (∑ C : G.ConnectedComponent, ∑ x : C, C.toSimpleGraph.degree x) <
        ∑ C : G.ConnectedComponent, d * Fintype.card C := by
    apply Finset.sum_lt_sum
    · intro C _
      exact (hlt C).le
    · let C₀ : G.ConnectedComponent := Classical.choice inferInstance
      exact ⟨C₀, Finset.mem_univ _, hlt C₀⟩
  apply (not_lt_of_ge hG)
  calc
    (∑ x : V, G.degree x) =
        ∑ C : G.ConnectedComponent, ∑ x : C, C.toSimpleGraph.degree x :=
      sum_degrees_eq_sum_connectedComponents G
    _ < ∑ C : G.ConnectedComponent, d * Fintype.card C := hsum_lt
    _ = d * ∑ C : G.ConnectedComponent, Fintype.card C := by
      rw [Finset.mul_sum]
    _ = d * Fintype.card V := by
      rw [← card_eq_sum_card_connectedComponents G]

/-! ## Deleting a low-degree vertex -/

/-- Flatten the induced graph obtained by first restricting to `S` and then
deleting `v` into the graph induced by `S.erase v` in the original graph. -/
def induceComplSingletonIsoInduceErase (G : SimpleGraph V) [DecidableEq V]
    (S : Finset V) (v : S) :
    (G.induce (S : Set V)).induce ({v}ᶜ : Set S) ≃g
      G.induce ((S.erase v.val : Finset V) : Set V) where
  toFun x := by
    refine ⟨x.val.val, Finset.mem_erase.mpr ⟨?_, x.val.prop⟩⟩
    intro hx
    apply x.prop
    simpa using Subtype.ext hx
  invFun x := by
    have hx := Finset.mem_erase.mp x.prop
    refine ⟨⟨x.val, hx.2⟩, ?_⟩
    simpa using fun h : (⟨x.val, hx.2⟩ : S) = v => hx.1 (congrArg Subtype.val h)
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_rel_iff' := by
    intro x y
    rfl

/-- Exact edge-count change when erasing one vertex from an induced vertex
set. -/
theorem edgeCount_induce_erase (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (S : Finset V) (v : S) :
    edgeCount (G.induce ((S.erase v.val : Finset V) : Set V)) =
      edgeCount (G.induce (S : Set V)) - (G.induce (S : Set V)).degree v := by
  let J := G.induce (S : Set V)
  calc
    edgeCount (G.induce ((S.erase v.val : Finset V) : Set V)) =
        edgeCount (J.induce ({v}ᶜ : Set S)) :=
      (edgeCount_eq_of_iso (induceComplSingletonIsoInduceErase G S v)).symm
    _ = #(J.induce ({v}ᶜ : Set S)).edgeFinset :=
      edgeCount_eq_card_edgeFinset _
    _ = #(J.deleteIncidenceSet v).edgeFinset :=
      J.card_edgeFinset_induce_compl_singleton v
    _ = #J.edgeFinset - J.degree v :=
      J.card_edgeFinset_deleteIncidenceSet v
    _ = edgeCount J - J.degree v := by
      rw [edgeCount_eq_card_edgeFinset]

/-- Removing a vertex of degree at most `d` preserves scaled average degree
at least `2 * d`. -/
theorem hasAverageDegreeAtLeast_induce_erase_of_degree_le
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) (v : S) {d : Nat}
    (havg : HasAverageDegreeAtLeast (G.induce (S : Set V)) (2 * d))
    (hdeg : (G.induce (S : Set V)).degree v <= d) :
    HasAverageDegreeAtLeast
      (G.induce ((S.erase v.val : Finset V) : Set V)) (2 * d) := by
  let J := G.induce (S : Set V)
  have hcancel : d * #S <= edgeCount J := by
    have htwice : 2 * (d * #S) <= 2 * edgeCount J := by
      simpa [HasAverageDegreeAtLeast, J, Nat.card_eq_fintype_card,
        card_coe_finset_set, Nat.mul_assoc] using havg
    omega
  have hcard_pos : 0 < #S := Finset.card_pos.mpr ⟨v.val, v.prop⟩
  have hadd : d * (#S - 1) + J.degree v <= edgeCount J := by
    calc
      d * (#S - 1) + J.degree v <= d * (#S - 1) + d :=
        Nat.add_le_add_left hdeg _
      _ = d * #S := by
        rw [show #S = (#S - 1) + 1 by omega, Nat.mul_add]
        simp
      _ <= edgeCount J := hcancel
  have hsub : d * (#S - 1) <= edgeCount J - J.degree v :=
    Nat.le_sub_of_add_le hadd
  have htwice := Nat.mul_le_mul_left 2 hsub
  unfold HasAverageDegreeAtLeast
  rw [Nat.card_eq_fintype_card, card_coe_finset_set,
    Finset.card_erase_of_mem v.prop, edgeCount_induce_erase]
  simpa [J, Nat.mul_assoc] using htwice

/-! ## Minimal dense induced sets and the density core -/

/-- Among all nonempty induced vertex sets satisfying a fixed average-degree
bound, one has minimum cardinality. -/
theorem exists_minimal_dense_induced_finset
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] {d : Nat} (hG : HasAverageDegreeAtLeast G d) :
    ∃ S : Finset V,
      S.Nonempty ∧ HasAverageDegreeAtLeast (G.induce (S : Set V)) d ∧
        ∀ T : Finset V, T.Nonempty ->
          HasAverageDegreeAtLeast (G.induce (T : Set V)) d -> #S <= #T := by
  classical
  let p : Nat -> Prop := fun n =>
    ∃ S : Finset V, #S = n ∧ S.Nonempty ∧
      HasAverageDegreeAtLeast (G.induce (S : Set V)) d
  have hG_univ : HasAverageDegreeAtLeast (G.induce (Set.univ : Set V)) d :=
    hG.map_iso (G.induceUnivIso).symm
  have hp : ∃ n, p n := by
    refine ⟨#(Finset.univ : Finset V), Finset.univ, rfl,
      Finset.univ_nonempty, ?_⟩
    have hset : ((Finset.univ : Finset V) : Set V) = Set.univ := by simp
    rw [hset]
    exact hG_univ
  obtain ⟨S, hScard, hSne, hSavg⟩ := Nat.find_spec hp
  refine ⟨S, hSne, hSavg, ?_⟩
  intro T hTne hTavg
  rw [hScard]
  exact Nat.find_min' hp ⟨T, rfl, hTne, hTavg⟩

/-- A minimum-cardinality nonempty induced graph of scaled average degree at
least `2 * d` has minimum degree strictly greater than `d`. -/
theorem exists_minimalDegree_dense_induced_finset
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] {d : Nat} (hd : 0 < d)
    (hG : HasAverageDegreeAtLeast G (2 * d)) :
    ∃ S : Finset V,
      S.Nonempty ∧ HasAverageDegreeAtLeast (G.induce (S : Set V)) (2 * d) ∧
        HasMinimumDegreeGreaterThan (G.induce (S : Set V)) d := by
  obtain ⟨S, hSne, hSavg, hminimal⟩ :=
    exists_minimal_dense_induced_finset G hG
  have hcard_two : 2 <= #S := by
    by_contra hnot
    have hcard_le : #S <= 1 := by omega
    have hedge_zero : edgeCount (G.induce (S : Set V)) = 0 := by
      rw [edgeCount_eq_card_edgeFinset]
      apply Nat.eq_zero_of_le_zero
      refine (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two.trans ?_
      interval_cases hcard : #S <;> simp [hcard]
    unfold HasAverageDegreeAtLeast at hSavg
    rw [Nat.card_eq_fintype_card, card_coe_finset_set, hedge_zero] at hSavg
    have hcard_pos : 0 < #S := Finset.card_pos.mpr hSne
    have hprod_pos : 0 < (2 * d) * #S :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hcard_pos
    omega
  refine ⟨S, hSne, hSavg, ?_⟩
  intro v
  by_contra hnot
  have hdeg : (G.induce (S : Set V)).degree v <= d := by omega
  have herase_ne : (S.erase v.val).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hcard_zero : #(S.erase v.val) = 0 := by simp [hempty]
    rw [Finset.card_erase_of_mem v.prop] at hcard_zero
    omega
  have herase_avg :=
    hasAverageDegreeAtLeast_induce_erase_of_degree_le G S v hSavg hdeg
  have hminimal' := hminimal (S.erase v.val) herase_ne herase_avg
  exact (not_lt_of_ge hminimal') (Finset.card_erase_lt_of_mem v.prop)

/-- General connected density-core theorem.  The witness is presented as a
connected component of an induced subgraph, together with its containment in
the original graph.  Hence it is itself an induced graph on a subset of the
original vertices (up to the canonical subtype identification). -/
theorem exists_connected_induced_densityCore
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] {d : Nat} (hd : 0 < d)
    (hG : HasAverageDegreeAtLeast G (2 * d)) :
    ∃ S : Finset V, ∃ C : (G.induce (S : Set V)).ConnectedComponent,
      C.toSimpleGraph.Connected ∧
        HasAverageDegreeAtLeast C.toSimpleGraph (2 * d) ∧
        HasMinimumDegreeGreaterThan C.toSimpleGraph d ∧
        C.toSimpleGraph ⊑ G := by
  obtain ⟨S, hSne, hSavg, hmindeg⟩ :=
    exists_minimalDegree_dense_induced_finset G hd hG
  let J := G.induce (S : Set V)
  letI : Nonempty S := Finset.nonempty_coe_sort.mpr hSne
  obtain ⟨C, hCavg⟩ := exists_connectedComponent_hasAverageDegreeAtLeast J hSavg
  refine ⟨S, C, C.connected_toSimpleGraph, hCavg, ?_, ?_⟩
  · intro x
    rw [degree_connectedComponent_toSimpleGraph J C x]
    exact hmindeg x.val
  · exact ⟨(Copy.induce G (S : Set V)).comp (Copy.induce J C.supp)⟩

/-- Claim 4.1 in its paper-facing `16d/8d` normalization. -/
theorem exists_connected_induced_densityCore_sixteen_eight
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] {d : Nat} (hd : 0 < d)
    (hG : HasAverageDegreeAtLeast G (16 * d)) :
    ∃ S : Finset V, ∃ C : (G.induce (S : Set V)).ConnectedComponent,
      C.toSimpleGraph.Connected ∧
        HasAverageDegreeAtLeast C.toSimpleGraph (16 * d) ∧
        HasMinimumDegreeGreaterThan C.toSimpleGraph (8 * d) ∧
        C.toSimpleGraph ⊑ G := by
  have hpos : 0 < 8 * d := Nat.mul_pos (by norm_num) hd
  have heq : 2 * (8 * d) = 16 * d := by ring
  have hG' : HasAverageDegreeAtLeast G (2 * (8 * d)) := by
    rw [heq]
    exact hG
  simpa only [heq] using
    (exists_connected_induced_densityCore G hpos (d := 8 * d) hG')

end LeanCo.SizeRamsey
