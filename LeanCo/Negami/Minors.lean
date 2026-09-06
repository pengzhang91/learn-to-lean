import LeanCo.Negami.FiniteGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Fintype.Quotient
import Mathlib.Tactic

/-!
# Deletion and contraction of finite labelled multigraphs

The two state equivalences in this file implement the partition of spanning
states around a fixed edge.  The accompanying theorems prove that deletion
preserves the component count of unselected states and contraction preserves
the component count of selected states.  These are the graph-theoretic facts
behind deletion--contraction for the Negami state object.
-/

namespace LeanCo.Negami
namespace FiniteMultigraph

variable (G : FiniteMultigraph)

/-! ## Deletion and unselected states -/

/-- Delete one labelled edge while retaining the full vertex set. -/
def deleteEdge (e : G.Edge) : FiniteMultigraph where
  Vertex := G.Vertex
  Edge := {a : G.Edge // a ≠ e}
  ends a := G.ends a.1

/-- States omitting `e` are exactly states of the deleted graph. -/
noncomputable def unselectedStateEquiv (e : G.Edge) :
    {S : Finset G.Edge // e ∉ S} ≃ Finset (G.deleteEdge e).Edge where
  toFun S := S.1.subtype (· ≠ e)
  invFun T := ⟨T.map ⟨Subtype.val, Subtype.val_injective⟩, by
    intro he
    rcases Finset.mem_map.mp he with ⟨a, ha, hae⟩
    exact a.2 hae⟩
  left_inv S := by
    ext a
    simp only [Finset.mem_map, Finset.mem_subtype]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro ha
      refine ⟨⟨a, ?_⟩, ha, rfl⟩
      intro hae
      exact S.2 (hae ▸ ha)
  right_inv T := by
    ext a
    rw [Finset.mem_subtype]
    constructor
    · intro ha
      rcases Finset.mem_map.mp ha with ⟨b, hb, hba⟩
      exact Subtype.ext hba ▸ hb
    · intro ha
      exact Finset.mem_map.mpr ⟨a, ha, rfl⟩

theorem unselectedStateEquiv_card (e : G.Edge)
    (S : {S : Finset G.Edge // e ∉ S}) :
    (G.unselectedStateEquiv e S).card = S.1.card := by
  change (S.1.subtype (· ≠ e)).card = S.1.card
  have hmap := Finset.subtype_map_of_mem (s := S.1) (p := fun a ↦ a ≠ e)
    (fun a ha hae ↦ S.2 (hae ▸ ha))
  have hcard := congrArg Finset.card hmap
  simpa using hcard

theorem stateGraph_deleteEdge (e : G.Edge)
    (S : {S : Finset G.Edge // e ∉ S}) :
    (G.deleteEdge e).stateGraph (G.unselectedStateEquiv e S) =
      G.stateGraph S.1 := by
  have himage :
      (G.unselectedStateEquiv e S).image (G.deleteEdge e).ends =
        S.1.image G.ends := by
    change (S.1.subtype (· ≠ e)).image (fun a ↦ G.ends a.1) =
      S.1.image G.ends
    ext p
    rw [Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, hap⟩
      exact ⟨a.1, Finset.mem_subtype.mp ha, hap⟩
    · rintro ⟨a, ha, hap⟩
      have hae : a ≠ e := fun h ↦ S.2 (h ▸ ha)
      exact ⟨⟨a, hae⟩, Finset.mem_subtype.mpr ha, hap⟩
  unfold stateGraph
  rw [himage]
  rfl

theorem stateConnected_deleteEdge (e : G.Edge)
    (S : {S : Finset G.Edge // e ∉ S}) (u v : G.Vertex) :
    (G.deleteEdge e).StateConnected (G.unselectedStateEquiv e S) u v ↔
      G.StateConnected S.1 u v := by
  rw [StateConnected, StateConnected, G.stateGraph_deleteEdge e S]
  exact Iff.rfl

/-- Component-count preservation for the unselected half of the state split. -/
theorem omega_deleteEdge (e : G.Edge)
    (S : {S : Finset G.Edge // e ∉ S}) :
    (G.deleteEdge e).omega (G.unselectedStateEquiv e S) = G.omega S.1 := by
  unfold omega StateComponent stateSetoid
  rw [G.stateGraph_deleteEdge e S]
  rfl

theorem card_deleteEdge (e : G.Edge) :
    Nat.card (G.deleteEdge e).Edge = Nat.card G.Edge - 1 := by
  classical
  simp only [Nat.card_eq_fintype_card]
  change Fintype.card {a : G.Edge // ¬a = e} = _
  rw [Fintype.card_subtype_compl (fun a : G.Edge ↦ a = e)]
  simp

/-- The complete exponent vector of an unselected state differs from its
deleted state by one unit in the unselected-edge grading. -/
theorem degree_deleteEdge (e : G.Edge)
    (S : {S : Finset G.Edge // e ∉ S}) :
    G.toNegamiData.degree S.1 =
      (G.deleteEdge e).toNegamiData.degree (G.unselectedStateEquiv e S) +
        Finsupp.single 2 1 := by
  classical
  have hcard := G.unselectedStateEquiv_card e S
  have hcomp := G.omega_deleteEdge e S
  have hlt : S.1.card < Nat.card G.Edge := by
    rw [Nat.card_eq_fintype_card]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro hEq
    exact S.2 (hEq ▸ Finset.mem_univ e)
  have hEdge := G.card_deleteEdge e
  have hunselected : Nat.card G.Edge - S.1.card =
      (Nat.card (G.deleteEdge e).Edge - S.1.card) + 1 := by
    rw [hEdge]
    omega
  ext i
  fin_cases i
  · simpa [NegamiData.degree, FiniteMultigraph.toNegamiData] using hcomp.symm
  · simpa [NegamiData.degree, FiniteMultigraph.toNegamiData] using hcard.symm
  · simpa [NegamiData.degree, FiniteMultigraph.toNegamiData, hcard] using
      hunselected

/-! ## Contraction and selected states -/

noncomputable local instance contractVertexDecidableEq (e : G.Edge) :
    DecidableEq (Quotient (G.stateSetoid {e})) :=
  @Quotient.decidableEq _ (G.stateSetoid {e})
    (fun _ _ ↦ Classical.propDecidable _)

/-- Send a vertex to its class after identifying the endpoints of `e`. -/
noncomputable abbrev contractVertex (e : G.Edge) (v : G.Vertex) :
    Quotient (G.stateSetoid {e}) :=
  @Quotient.mk' _ (G.stateSetoid {e}) v

/-- Contract the endpoints of `e` and remove its edge label.  When `e` is a
loop its one-edge state has discrete connectivity, realizing the convention
that loop contraction agrees with deletion up to the canonical quotient. -/
noncomputable abbrev contractEdge (e : G.Edge) : FiniteMultigraph where
  Vertex := Quotient (G.stateSetoid {e})
  Edge := {a : G.Edge // a ≠ e}
  vertexFintype := Fintype.ofFinite _
  vertexDecidableEq := contractVertexDecidableEq G e
  edgeFintype := Fintype.ofFinite _
  edgeDecidableEq := Classical.decEq _
  ends a := Sym2.map (G.contractVertex e) (G.ends a.1)

/-- Erasing `e` identifies selected states with states that omit it. -/
def selectedToUnselectedEquiv (e : G.Edge) :
    {S : Finset G.Edge // e ∈ S} ≃ {S : Finset G.Edge // e ∉ S} where
  toFun S := ⟨S.1.erase e, Finset.notMem_erase e S.1⟩
  invFun S := ⟨insert e S.1, Finset.mem_insert_self e S.1⟩
  left_inv S := by
    apply Subtype.ext
    exact Finset.insert_erase S.2
  right_inv S := by
    apply Subtype.ext
    exact Finset.erase_insert S.2

/-- Selected states correspond bijectively to states of the contracted graph. -/
noncomputable def selectedStateEquiv (e : G.Edge) :
    {S : Finset G.Edge // e ∈ S} ≃ Finset (G.contractEdge e).Edge :=
  (G.selectedToUnselectedEquiv e).trans (G.unselectedStateEquiv e)

theorem selectedStateEquiv_card (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) :
    (G.selectedStateEquiv e S).card + 1 = S.1.card := by
  change (G.unselectedStateEquiv e
    (G.selectedToUnselectedEquiv e S)).card + 1 = S.1.card
  rw [G.unselectedStateEquiv_card]
  change (S.1.erase e).card + 1 = S.1.card
  rw [Finset.card_erase_of_mem S.2]
  have hpos : 0 < S.1.card := Finset.card_pos.mpr ⟨e, S.2⟩
  omega

theorem mem_selectedStateEquiv (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S})
    (a : (G.contractEdge e).Edge) :
    a ∈ G.selectedStateEquiv e S ↔ a.1 ∈ S.1 := by
  change a ∈ G.unselectedStateEquiv e
      (G.selectedToUnselectedEquiv e S) ↔ _
  change a ∈ (S.1.erase e).subtype (· ≠ e) ↔ _
  rw [Finset.mem_subtype, Finset.mem_erase]
  exact and_iff_right a.2

theorem stateGraph_single_le (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) :
    G.stateGraph {e} ≤ G.stateGraph S.1 := by
  intro u v huv
  rw [stateGraph, SimpleGraph.fromEdgeSet_adj] at huv ⊢
  refine ⟨?_, huv.2⟩
  rcases Finset.mem_image.mp huv.1 with ⟨a, ha, hEnds⟩
  rw [Finset.mem_singleton] at ha
  subst a
  exact Finset.mem_image.mpr ⟨e, S.2, hEnds⟩

theorem reachable_of_contractVertex_eq (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) {u v : G.Vertex}
    (h : G.contractVertex e u = G.contractVertex e v) :
    G.StateConnected S.1 u v := by
  apply SimpleGraph.Reachable.mono (G.stateGraph_single_le e S)
  exact Quotient.exact h

/-- A contracted edge step lifts to a path between arbitrary original
representatives. -/
theorem reachable_of_contract_adj (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) {u v : G.Vertex}
    (huv : ((G.contractEdge e).stateGraph (G.selectedStateEquiv e S)).Adj
      (G.contractVertex e u) (G.contractVertex e v)) :
    G.StateConnected S.1 u v := by
  classical
  rw [stateGraph, SimpleGraph.fromEdgeSet_adj] at huv
  rcases Finset.mem_image.mp huv.1 with ⟨a, ha, hpair⟩
  have haS : a.1 ∈ S.1 := (G.mem_selectedStateEquiv e S a).mp ha
  induction hEnds : G.ends a.1 using Sym2.inductionOn with
  | _ x y =>
    have hpair' : s(G.contractVertex e x, G.contractVertex e y) =
        s(G.contractVertex e u, G.contractVertex e v) := by
      simpa [contractEdge, hEnds, Sym2.map_mk] using hpair
    have hxy_ne : x ≠ y := by
      intro hxy
      subst y
      have hq : G.contractVertex e u = G.contractVertex e v := by
        rcases Sym2.eq_iff.mp hpair' with h | h
        · exact h.1.symm.trans h.2
        · exact h.2.symm.trans h.1
      exact huv.2 hq
    have hxy_adj : (G.stateGraph S.1).Adj x y := by
      rw [stateGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨Finset.mem_image.mpr ⟨a.1, haS, hEnds⟩, hxy_ne⟩
    rcases Sym2.eq_iff.mp hpair' with h | h
    · exact (G.reachable_of_contractVertex_eq e S h.1.symm).trans
        (SimpleGraph.Adj.reachable hxy_adj) |>.trans
          (G.reachable_of_contractVertex_eq e S h.2)
    · exact (G.reachable_of_contractVertex_eq e S h.2.symm).trans
        (SimpleGraph.Adj.reachable hxy_adj.symm) |>.trans
          (G.reachable_of_contractVertex_eq e S h.1)

/-- Every contracted path lifts between chosen representatives. -/
theorem reachable_of_contract_reachable (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) {u v : G.Vertex}
    (huv : ((G.contractEdge e).stateGraph (G.selectedStateEquiv e S)).Reachable
      (G.contractVertex e u) (G.contractVertex e v)) :
    G.StateConnected S.1 u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  let q := G.contractVertex e
  have lift : ∀ {a b}, Relation.ReflTransGen
      ((G.contractEdge e).stateGraph (G.selectedStateEquiv e S)).Adj a b →
      ∀ x y, q x = a → q y = b → G.StateConnected S.1 x y := by
    intro a b hab
    induction hab using Relation.ReflTransGen.trans_induction_on with
    | refl a =>
        intro x y hx hy
        exact G.reachable_of_contractVertex_eq e S (hx.trans hy.symm)
    | single hab =>
        intro x y hx hy
        change G.contractVertex e x = _ at hx
        change G.contractVertex e y = _ at hy
        apply G.reachable_of_contract_adj e S
        rw [hx, hy]
        exact hab
    | @trans a b c hab hbc ihab ihbc =>
        intro x z hx hz
        let y : G.Vertex := Quotient.out b
        have hy : q y = b := Quotient.out_eq b
        exact (ihab x y hx hy).trans (ihbc y z hy hz)
  exact lift huv u v rfl rfl

/-- An original edge step becomes an edge step or an equality after
contraction, hence is connected in the contracted state. -/
theorem reachable_contractVertex_of_adj (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) {u v : G.Vertex}
    (huv : (G.stateGraph S.1).Adj u v) :
    ((G.contractEdge e).stateGraph (G.selectedStateEquiv e S)).Reachable
      (G.contractVertex e u) (G.contractVertex e v) := by
  classical
  rw [stateGraph, SimpleGraph.fromEdgeSet_adj] at huv
  rcases Finset.mem_image.mp huv.1 with ⟨a, haS, haEnds⟩
  by_cases hae : a = e
  · subst a
    have huvOne : (G.stateGraph {e}).Reachable u v := by
      apply SimpleGraph.Adj.reachable
      rw [stateGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨Finset.mem_image.mpr ⟨e, Finset.mem_singleton_self e, haEnds⟩,
        huv.2⟩
    have hq : G.contractVertex e u = G.contractVertex e v := Quotient.sound huvOne
    rw [hq]
  · by_cases hq : G.contractVertex e u = G.contractVertex e v
    · rw [hq]
    · apply SimpleGraph.Adj.reachable
      rw [stateGraph, SimpleGraph.fromEdgeSet_adj]
      refine ⟨Finset.mem_image.mpr ⟨⟨a, hae⟩, ?_, ?_⟩, hq⟩
      · exact (G.mem_selectedStateEquiv e S ⟨a, hae⟩).mpr haS
      · change Sym2.map (G.contractVertex e) (G.ends a) =
          s(G.contractVertex e u, G.contractVertex e v)
        rw [haEnds, Sym2.map_mk]

theorem reachable_contractVertex (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) {u v : G.Vertex}
    (huv : G.StateConnected S.1 u v) :
    ((G.contractEdge e).stateGraph (G.selectedStateEquiv e S)).Reachable
      (G.contractVertex e u) (G.contractVertex e v) := by
  rcases huv with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h p ih =>
      exact (G.reachable_contractVertex_of_adj e S h).trans ih

/-- Map original state components to contracted state components. -/
noncomputable def contractComponentMap (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) :
    G.StateComponent S.1 →
      (G.contractEdge e).StateComponent (G.selectedStateEquiv e S) := by
  refine Quot.map (G.contractVertex e) ?_
  intro u v huv
  exact G.reachable_contractVertex e S huv

theorem contractComponentMap_surjective (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) :
    Function.Surjective (G.contractComponentMap e S) := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | _ q =>
    induction q using Quotient.inductionOn with
    | _ v =>
      exact ⟨(G.stateGraph S.1).connectedComponentMk v, rfl⟩

theorem contractComponentMap_injective (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) :
    Function.Injective (G.contractComponentMap e S) := by
  intro c d hcd
  induction c using SimpleGraph.ConnectedComponent.ind with
  | _ u =>
    induction d using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
      apply SimpleGraph.ConnectedComponent.sound
      apply G.reachable_of_contract_reachable e S
      apply SimpleGraph.ConnectedComponent.exact
      exact hcd

noncomputable def contractComponentEquiv (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) :
    G.StateComponent S.1 ≃
      (G.contractEdge e).StateComponent (G.selectedStateEquiv e S) :=
  Equiv.ofBijective (G.contractComponentMap e S)
    ⟨G.contractComponentMap_injective e S,
      G.contractComponentMap_surjective e S⟩

/-- Component-count preservation for the selected half of the state split. -/
theorem omega_contractEdge (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) :
    (G.contractEdge e).omega (G.selectedStateEquiv e S) = G.omega S.1 := by
  unfold omega
  exact (Nat.card_congr (G.contractComponentEquiv e S)).symm

theorem card_contractEdge (e : G.Edge) :
    Nat.card (G.contractEdge e).Edge = Nat.card G.Edge - 1 := by
  change Nat.card {a : G.Edge // a ≠ e} = Nat.card G.Edge - 1
  exact G.card_deleteEdge e

/-- The complete exponent vector of a selected state differs from its
contracted state by one unit in the selected-edge grading. -/
theorem degree_contractEdge (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) :
    G.toNegamiData.degree S.1 =
      (G.contractEdge e).toNegamiData.degree (G.selectedStateEquiv e S) +
        Finsupp.single 1 1 := by
  classical
  have hcard := G.selectedStateEquiv_card e S
  have hcomp := G.omega_contractEdge e S
  have hEdge := G.card_contractEdge e
  have hS : S.1.card ≤ Nat.card G.Edge := by
    simpa only [Nat.card_eq_fintype_card] using Finset.card_le_univ S.1
  have hT : (G.selectedStateEquiv e S).card ≤
      Nat.card (G.contractEdge e).Edge := by
    simpa only [Nat.card_eq_fintype_card] using
      Finset.card_le_univ (G.selectedStateEquiv e S)
  have hunselected : Nat.card G.Edge - S.1.card =
      Nat.card (G.contractEdge e).Edge - (G.selectedStateEquiv e S).card := by
    omega
  ext i
  fin_cases i
  · simpa [NegamiData.degree, FiniteMultigraph.toNegamiData] using hcomp.symm
  · simpa [NegamiData.degree, FiniteMultigraph.toNegamiData] using hcard.symm
  · simpa [NegamiData.degree, FiniteMultigraph.toNegamiData, hcard] using
      hunselected

theorem triDegree_contractEdge (e : G.Edge)
    (S : {S : Finset G.Edge // e ∈ S}) :
    Tridegree.xUnit +
        (G.contractEdge e).toNegamiData.triDegree
          (G.selectedStateEquiv e S) =
      G.toNegamiData.triDegree S.1 := by
  have hcomp := G.omega_contractEdge e S
  have hcard := G.selectedStateEquiv_card e S
  have hEdge := G.card_contractEdge e
  have hS : S.1.card ≤ Nat.card G.Edge := by
    simpa only [Nat.card_eq_fintype_card] using Finset.card_le_univ S.1
  have hT : (G.selectedStateEquiv e S).card ≤
      Nat.card (G.contractEdge e).Edge := by
    simpa only [Nat.card_eq_fintype_card] using
      Finset.card_le_univ (G.selectedStateEquiv e S)
  change
    (⟨0 + (G.contractEdge e).omega (G.selectedStateEquiv e S),
      1 + (G.selectedStateEquiv e S).card,
      0 + (Nat.card (G.contractEdge e).Edge -
        (G.selectedStateEquiv e S).card)⟩ : Tridegree) =
      ⟨G.omega S.1, S.1.card, Nat.card G.Edge - S.1.card⟩
  simp only [Tridegree.mk.injEq]
  constructor
  · omega
  constructor
  · omega
  · have hdeg := congrArg (fun q : Degree →₀ ℕ ↦ q 2)
        (G.degree_contractEdge e S)
    simpa [NegamiData.degree] using hdeg.symm

theorem triDegree_deleteEdge (e : G.Edge)
    (S : {S : Finset G.Edge // e ∉ S}) :
    Tridegree.yUnit +
        (G.deleteEdge e).toNegamiData.triDegree
          (G.unselectedStateEquiv e S) =
      G.toNegamiData.triDegree S.1 := by
  have hcomp := G.omega_deleteEdge e S
  have hcard := G.unselectedStateEquiv_card e S
  have hEdge := G.card_deleteEdge e
  have hlt : S.1.card < Nat.card G.Edge := by
    rw [Nat.card_eq_fintype_card]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro hEq
    exact S.2 (hEq ▸ Finset.mem_univ e)
  change
    (⟨0 + (G.deleteEdge e).omega (G.unselectedStateEquiv e S),
      0 + (G.unselectedStateEquiv e S).card,
      1 + (Nat.card (G.deleteEdge e).Edge -
        (G.unselectedStateEquiv e S).card)⟩ : Tridegree) =
      ⟨G.omega S.1, S.1.card, Nat.card G.Edge - S.1.card⟩
  simp only [Tridegree.mk.injEq]
  omega

/-! ## Object-level and polynomial deletion--contraction -/

/-- Split every original state according to membership of the chosen edge,
then transport the two halves to contraction and deletion. -/
noncomputable def stateSplitEquiv (e : G.Edge) :
    Finset G.Edge ≃
      Finset (G.contractEdge e).Edge ⊕ Finset (G.deleteEdge e).Edge :=
  (Equiv.sumCompl (fun S : Finset G.Edge ↦ e ∈ S)).symm |>.trans
    (Equiv.sumCongr (G.selectedStateEquiv e) (G.unselectedStateEquiv e))

theorem stateSplitEquiv_apply_of_mem (e : G.Edge) (S : Finset G.Edge)
    (h : e ∈ S) :
    G.stateSplitEquiv e S =
      Sum.inl (G.selectedStateEquiv e ⟨S, h⟩) := by
  unfold stateSplitEquiv
  rw [Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_pos
      (p := fun T : Finset G.Edge ↦ e ∈ T) h,
    Equiv.sumCongr_apply, Sum.map_inl]

theorem stateSplitEquiv_apply_of_notMem (e : G.Edge) (S : Finset G.Edge)
    (h : e ∉ S) :
    G.stateSplitEquiv e S =
      Sum.inr (G.unselectedStateEquiv e ⟨S, h⟩) := by
  unfold stateSplitEquiv
  rw [Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_neg
      (p := fun T : Finset G.Edge ↦ e ∈ T) h,
    Equiv.sumCongr_apply, Sum.map_inr]

/-- Theorem 3.3: the actual graph state object decomposes into the contracted
and deleted state objects, with the two paper grading shifts. -/
noncomputable def stateObject_deletionContraction (e : G.Edge) :
    GradedObject.Equiv G.stateObject
      (GradedObject.sum
        (GradedObject.shift Tridegree.xUnit (G.contractEdge e).stateObject)
        (GradedObject.shift Tridegree.yUnit (G.deleteEdge e).stateObject)) where
  basisEquiv := G.stateSplitEquiv e
  degree_eq S := by
    change Finset G.Edge at S
    dsimp only [FiniteMultigraph.stateObject, NegamiData.stateObject,
      GradedObject.sum, GradedObject.shift]
    by_cases h : e ∈ S
    · rw [G.stateSplitEquiv_apply_of_mem e S h]
      exact G.triDegree_contractEdge e ⟨S, h⟩
    · rw [G.stateSplitEquiv_apply_of_notMem e S h]
      exact G.triDegree_deleteEdge e ⟨S, h⟩

/-- Scalar deletion--contraction obtained by decategorifying the object
equivalence. -/
theorem stateSum_deletion_contraction (e : G.Edge)
    {R : Type*} [CommSemiring R] (t x y : R) :
    G.stateSum t x y =
      x * (G.contractEdge e).stateSum t x y +
      y * (G.deleteEdge e).stateSum t x y := by
  calc
    G.stateSum t x y = G.stateObject.hilbert t x y :=
      (G.hilbert_stateObject t x y).symm
    _ = (GradedObject.sum
          (GradedObject.shift Tridegree.xUnit (G.contractEdge e).stateObject)
          (GradedObject.shift Tridegree.yUnit (G.deleteEdge e).stateObject)).hilbert
          t x y :=
      (G.stateObject_deletionContraction e).hilbert_eq t x y
    _ = x * (G.contractEdge e).stateSum t x y +
        y * (G.deleteEdge e).stateSum t x y := by
      rw [GradedObject.hilbert_sum, GradedObject.hilbert_shift,
        GradedObject.hilbert_shift, gradeWeight_xUnit, gradeWeight_yUnit,
        (G.contractEdge e).hilbert_stateObject,
        (G.deleteEdge e).hilbert_stateObject]

end FiniteMultigraph

namespace NegamiData

/-! The following finite-state statement is useful independently of a graph
presentation and keeps the polynomial proof separate from quotient details. -/

/-- A grading shift of every state monomial. -/
noncomputable def shiftedPolynomial (A : NegamiData)
    (R : Type*) [CommSemiring R] (q : Degree →₀ ℕ) :
    MvPolynomial Degree R :=
  ∑ S : Finset A.Edge, MvPolynomial.monomial (A.degree S + q) 1

/-- The exact state-level data supplied by contraction and deletion. -/
structure DeletionContraction (A C D : NegamiData) (e : A.Edge) where
  selected : {S : Finset A.Edge // e ∈ S} ≃ Finset C.Edge
  unselected : {S : Finset A.Edge // e ∉ S} ≃ Finset D.Edge
  selected_degree : ∀ S,
    A.degree S.1 = C.degree (selected S) + Finsupp.single 1 1
  unselected_degree : ∀ S,
    A.degree S.1 = D.degree (unselected S) + Finsupp.single 2 1

/-- Partitioning a finite state space proves polynomial deletion--contraction. -/
theorem polynomial_deletion_contraction_shifted {A C D : NegamiData}
    (e : A.Edge) (W : DeletionContraction A C D e)
    (R : Type*) [CommSemiring R] :
    A.polynomial R =
      C.shiftedPolynomial R (Finsupp.single 1 1) +
      D.shiftedPolynomial R (Finsupp.single 2 1) := by
  classical
  rw [polynomial, ← Fintype.sum_subtype_add_sum_subtype
    (fun S : Finset A.Edge ↦ e ∈ S)]
  congr 1
  · exact Fintype.sum_equiv W.selected _ _ fun S ↦ by
      rw [W.selected_degree S, add_comm]
  · exact Fintype.sum_equiv W.unselected _ _ fun S ↦ by
      rw [W.unselected_degree S, add_comm]

theorem shiftedPolynomial_single_eq_X_mul (A : NegamiData)
    (R : Type*) [CommSemiring R] (i : Degree) :
    A.shiftedPolynomial R (Finsupp.single i 1) =
      MvPolynomial.X i * A.polynomial R := by
  classical
  unfold shiftedPolynomial polynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [MvPolynomial.monomial_add_single, pow_one, mul_comm]

end NegamiData

namespace FiniteMultigraph

variable (G : FiniteMultigraph)

/-- The concrete graph operations furnish the abstract state partition. -/
noncomputable def deletionContraction (e : G.Edge) :
    NegamiData.DeletionContraction G.toNegamiData
      (G.contractEdge e).toNegamiData (G.deleteEdge e).toNegamiData e where
  selected := G.selectedStateEquiv e
  unselected := G.unselectedStateEquiv e
  selected_degree := G.degree_contractEdge e
  unselected_degree := G.degree_deleteEdge e

theorem polynomial_deletion_contraction_shifted (e : G.Edge)
    (R : Type*) [CommSemiring R] :
    G.polynomial R =
      (G.contractEdge e).toNegamiData.shiftedPolynomial R
        (Finsupp.single 1 1) +
      (G.deleteEdge e).toNegamiData.shiftedPolynomial R
        (Finsupp.single 2 1) :=
  NegamiData.polynomial_deletion_contraction_shifted e
    (G.deletionContraction e) R

/-- Equation (2.1) satisfies the defining Negami recurrence. -/
theorem polynomial_deletion_contraction (e : G.Edge)
    (R : Type*) [CommSemiring R] :
    G.polynomial R =
      MvPolynomial.X 1 * (G.contractEdge e).polynomial R +
      MvPolynomial.X 2 * (G.deleteEdge e).polynomial R := by
  rw [G.polynomial_deletion_contraction_shifted e R,
    NegamiData.shiftedPolynomial_single_eq_X_mul,
    NegamiData.shiftedPolynomial_single_eq_X_mul]

end FiniteMultigraph
end LeanCo.Negami
