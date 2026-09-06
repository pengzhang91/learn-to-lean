import LeanCo.HypercubeTuran.RandomBaseExistence
import LeanCo.HypercubeTuran.ShortCycleAlteration
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-!
# Local sparsity separates short cycles

This file supplies the deterministic bridge from the local sparsity event in
the binomial source construction to the vertex-disjointness hypothesis used by
the short-cycle alteration.
-/

open scoped SimpleGraph Finset

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

noncomputable section

set_option maxHeartbeats 200000

namespace RB

@[simp]
lemma mem_internalEdgeFinset_iff {N : ℕ} (U : Finset (Fin N))
    (e : RandomEdge N) :
    e ∈ internalEdgeFinset U ↔ e.1 ∈ U.sym2 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
      simp only [internalEdgeFinset, Finset.mem_map, Finset.mem_univ,
        true_and, Finset.mk_mem_sym2_iff]
      constructor
      · rintro ⟨x, hx⟩
        have hxv := congrArg Subtype.val hx
        rcases x with ⟨x, hxnd⟩
        induction x using Sym2.ind with
        | _ a b =>
            have hxv' : s(a.1, b.1) = s(u, v) := by
              simpa [internalEdgeEmbedding,
                Function.Embedding.sym2Map_apply] using hxv
            rw [Sym2.eq_iff] at hxv'
            rcases hxv' with h | h
            · exact ⟨h.1 ▸ a.2, h.2 ▸ b.2⟩
            · exact ⟨h.2 ▸ b.2, h.1 ▸ a.2⟩
      · rintro ⟨hu, hv⟩
        have huv : u ≠ v := by
          intro h
          apply he
          simpa [Sym2.mk_isDiag_iff] using h
        let x : InternalEdgeIndex U := internalEdgeOfNe U ⟨u, hu⟩ ⟨v, hv⟩
          (fun h => huv (congrArg Subtype.val h))
        refine ⟨x, ?_⟩
        apply Subtype.ext
        simp [x, internalEdgeEmbedding, internalEdgeOfNe,
          Function.Embedding.sym2Map_apply]

/-- `internalEdgeCount` is the ordinary number of graph edges with both
endpoints in `U`. -/
theorem internalEdgeCount_eq_card_filter {N : ℕ}
    (E : Set (RandomEdge N)) (U : Finset (Fin N)) :
    internalEdgeCount E U =
      {e : Sym2 (Fin N) |
        e ∈ (graphOfEdges E).edgeSet ∧ e ∈ U.sym2}.ncard := by
  classical
  let f : RandomEdge N ↪ Sym2 (Fin N) := Function.Embedding.subtype _
  let A := selectedFinset (internalEdgeFinset U) E
  have hmap : ((A.map f : Finset (Sym2 (Fin N))) : Set (Sym2 (Fin N))) =
      {e : Sym2 (Fin N) |
        e ∈ (graphOfEdges E).edgeSet ∧ e ∈ U.sym2} := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
      rw [mem_selectedFinset] at he'
      refine ⟨?_, ?_⟩
      · rw [edgeSet_graphOfEdges]
        exact ⟨e', he'.2, rfl⟩
      · exact (mem_internalEdgeFinset_iff U e').mp he'.1
    · intro he
      rw [edgeSet_graphOfEdges] at he
      obtain ⟨⟨e', he'E, he'e⟩, heU⟩ := he
      have heq : e'.1 = e := he'e
      subst e
      exact Finset.mem_map.mpr ⟨e',
        mem_selectedFinset.mpr
          ⟨(mem_internalEdgeFinset_iff U e').mpr heU, he'E⟩, rfl⟩
  calc
    internalEdgeCount E U = #A := rfl
    _ = #(A.map f) := (Finset.card_map f).symm
    _ = ((A.map f : Finset (Sym2 (Fin N))) : Set (Sym2 (Fin N))).ncard :=
      (Set.ncard_coe_finset _).symm
    _ = _ := congrArg Set.ncard hmap

end RB

section TwoCycles

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected finite graph containing two cycles with different edge sets
has strictly more edges than vertices. -/
private theorem card_lt_card_edgeFinset_of_two_cycles
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {u v : V} (p : G.Walk u u) (q : G.Walk v v)
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hne : p.edges.toFinset ≠ q.edges.toFinset) :
    Fintype.card V < #G.edgeFinset := by
  have hdiff :
      (∃ e ∈ p.edges.toFinset, e ∉ q.edges.toFinset) ∨
        (∃ e ∈ q.edges.toFinset, e ∉ p.edges.toFinset) := by
    contrapose! hne
    exact Finset.Subset.antisymm hne.1 hne.2
  have aux {a b : V} (r : G.Walk a a) (s : G.Walk b b)
      (hr : r.IsCycle) (hs : s.IsCycle)
      (hdiff : ∃ e ∈ r.edges.toFinset, e ∉ s.edges.toFinset) :
      Fintype.card V < #G.edgeFinset := by
    obtain ⟨e, her, hes⟩ := hdiff
    have her' : e ∈ r.edges := List.mem_toFinset.mp her
    have heG : e ∈ G.edgeSet := r.edges_subset_edgeSet her'
    have hnbridge : ¬G.IsBridge e := by
      intro hb
      exact (SimpleGraph.isBridge_iff_forall_cycle_notMem heG).mp hb r hr her'
    have hconn : (G.deleteEdges ({e} : Set (Sym2 V))).Connected := by
      induction e using Sym2.ind with
      | _ x y => exact hG.connected_delete_edge_of_not_isBridge hnbridge
    have hsdel : ∃ (s' : (G.deleteEdges ({e} : Set (Sym2 V))).Walk b b),
        s'.IsCycle := by
      have havoid : ∀ f ∈ s.edges, f ∉ ({e} : Set (Sym2 V)) := by
        intro f hf hfe
        simp only [Set.mem_singleton_iff] at hfe
        subst f
        exact hes (List.mem_toFinset.mpr hf)
      exact ⟨s.toDeleteEdges ({e} : Set (Sym2 V)) havoid,
        SimpleGraph.Walk.IsCycle.toDeleteEdges G
          ({e} : Set (Sym2 V)) hs havoid⟩
    have hnotTree : ¬(G.deleteEdges ({e} : Set (Sym2 V))).IsTree := by
      intro ht
      obtain ⟨s', hs'⟩ := hsdel
      exact ht.isAcyclic s' hs'
    have hnecard :
        Nat.card (G.deleteEdges ({e} : Set (Sym2 V))).edgeSet + 1 ≠
          Fintype.card V := by
      intro heqcard
      exact hnotTree ((SimpleGraph.isTree_iff_connected_and_card).2
        ⟨hconn, by simpa [Nat.card_eq_fintype_card] using heqcard⟩)
    have hlower :
        Fintype.card V ≤
          Nat.card (G.deleteEdges ({e} : Set (Sym2 V))).edgeSet + 1 := by
      simpa [Nat.card_eq_fintype_card] using
        hconn.card_vert_le_card_edgeSet_add_one
    have hstrict : Fintype.card V <
        Nat.card (G.deleteEdges ({e} : Set (Sym2 V))).edgeSet + 1 :=
      lt_of_le_of_ne hlower (Ne.symm hnecard)
    have hstrict' : Fintype.card V <
        (G.deleteEdges ({e} : Set (Sym2 V))).edgeSet.ncard + 1 := by
      simpa only [Nat.card_coe_set_eq] using hstrict
    have hdelset :
        (G.deleteEdges ({e} : Set (Sym2 V))).edgeSet = G.edgeSet \ {e} :=
      SimpleGraph.edgeSet_deleteEdges (G := G) ({e} : Set (Sym2 V))
    have hcard : (G.deleteEdges ({e} : Set (Sym2 V))).edgeSet.ncard + 1 =
        G.edgeSet.ncard := by
      rw [hdelset]
      exact Set.ncard_sdiff_singleton_add_one heG
    have htarget : Fintype.card V < G.edgeSet.ncard := by omega
    have hedgeCard : G.edgeSet.ncard = Fintype.card G.edgeSet := by
      calc
        G.edgeSet.ncard = Nat.card G.edgeSet :=
          (Nat.card_coe_set_eq G.edgeSet).symm
        _ = Fintype.card G.edgeSet := Nat.card_eq_fintype_card
    calc
      Fintype.card V < G.edgeSet.ncard := htarget
      _ = Fintype.card G.edgeSet := hedgeCard
      _ = #G.edgeFinset := G.card_edgeSet
  exact hdiff.elim (aux p q hp hq) (aux q p hq hp)

/-- The vertices incident with the edges of a nonempty closed walk are
exactly its support. -/
@[simp]
lemma edgeVertexFinset_edges_toFinset_eq_support_toFinset
    (G : SimpleGraph V) {u : V} (p : G.Walk u u) (hp : ¬p.Nil) :
    edgeVertexFinset p.edges.toFinset = p.support.toFinset := by
  ext x
  rw [List.mem_toFinset,
    p.mem_support_iff_exists_mem_edges_of_not_nil hp]
  simp only [edgeVertexFinset, Finset.mem_biUnion, List.mem_toFinset,
    Sym2.mem_toFinset]

/-- A simple cycle has as many incident vertices as edges. -/
lemma card_edgeVertexFinset_edges_toFinset_eq_length_of_isCycle
    (G : SimpleGraph V) {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    #(edgeVertexFinset p.edges.toFinset) = p.length := by
  rw [edgeVertexFinset_edges_toFinset_eq_support_toFinset G p hp.not_nil]
  have hsupp : p.support.toFinset = p.support.tail.toFinset := by
    calc
      p.support.toFinset = insert u p.support.tail.toFinset := by
        simpa only [List.toFinset_cons] using
          congrArg List.toFinset p.cons_tail_support.symm
      _ = p.support.tail.toFinset :=
        Finset.insert_eq_of_mem
          (List.mem_toFinset.mpr (p.end_mem_tail_support hp.not_nil))
  rw [hsupp, List.toFinset_card_of_nodup hp.support_nodup]
  simp

/-- The local sparsity clause of a good random source forces all short
cycles to have pairwise disjoint vertex supports. -/
theorem RB.IsGoodSource.shortCyclesVertexDisjoint
    {N d g : ℕ} {E : Set (RandomEdge N)}
    (h : RB.IsGoodSource E d g) :
    ShortCyclesVertexDisjoint (graphOfEdges E) g := by
  classical
  let G := graphOfEdges E
  letI : DecidableRel G.Adj := Classical.decRel _
  intro X Y hXY
  rw [Finset.disjoint_left]
  intro z hzX hzY
  obtain ⟨a, p, hp, hpLen, hpEdges⟩ := X.2
  obtain ⟨b, q, hq, hqLen, hqEdges⟩ := Y.2
  let U : Finset (Fin N) := edgeVertexFinset X.1 ∪ edgeVertexFinset Y.1
  let H : G.Subgraph := p.toSubgraph ⊔ q.toSubgraph
  have hzP : z ∈ p.support := by
    have hzP' : z ∈ edgeVertexFinset p.edges.toFinset := by
      rwa [hpEdges]
    rw [edgeVertexFinset_edges_toFinset_eq_support_toFinset G p hp.not_nil,
      List.mem_toFinset] at hzP'
    exact hzP'
  have hzQ : z ∈ q.support := by
    have hzQ' : z ∈ edgeVertexFinset q.edges.toFinset := by
      rwa [hqEdges]
    rw [edgeVertexFinset_edges_toFinset_eq_support_toFinset G q hq.not_nil,
      List.mem_toFinset] at hzQ'
    exact hzQ'
  have hHconn : H.Connected := by
    apply Subgraph.connected_sup p.toSubgraph_connected.preconnected
      q.toSubgraph_connected.preconnected
    exact ⟨z, p.mem_verts_toSubgraph.mpr hzP,
      q.mem_verts_toSubgraph.mpr hzQ⟩
  have hHverts : H.verts = (U : Set (Fin N)) := by
    ext x
    simp only [H, U, Subgraph.verts_sup, Set.mem_union,
      Walk.mem_verts_toSubgraph, Finset.mem_coe, Finset.mem_union]
    have hpV := edgeVertexFinset_edges_toFinset_eq_support_toFinset
      G p hp.not_nil
    have hqV := edgeVertexFinset_edges_toFinset_eq_support_toFinset
      G q hq.not_nil
    rw [← List.mem_toFinset, ← List.mem_toFinset,
      ← hpV, ← hqV, hpEdges, hqEdges]
  letI : Fintype {x : Fin N // x ∈ (U : Set (Fin N))} :=
    FinsetCoe.fintype U
  let K : SimpleGraph U := G.induce (U : Set (Fin N))
  have hKconn : K.Connected := by
    change (G.induce (U : Set (Fin N))).Connected
    rw [← hHverts]
    exact hHconn.induce_verts
  have hpSub : ∀ x ∈ p.support, x ∈ (U : Set (Fin N)) := by
    intro x hx
    rw [← hHverts]
    exact Or.inl (p.mem_verts_toSubgraph.mpr hx)
  have hqSub : ∀ x ∈ q.support, x ∈ (U : Set (Fin N)) := by
    intro x hx
    rw [← hHverts]
    exact Or.inr (q.mem_verts_toSubgraph.mpr hx)
  let pU := p.induce (U : Set (Fin N)) hpSub
  let qU := q.induce (U : Set (Fin N)) hqSub
  have hpUCycle : pU.IsCycle := by
    apply (Walk.map_isCycle_iff_of_injective
      (f := (SimpleGraph.Embedding.induce
        (G := G) (U : Set (Fin N))).toHom)
      (SimpleGraph.Embedding.induce
        (G := G) (U : Set (Fin N))).injective).mp
    change ((p.induce (U : Set (Fin N)) hpSub).map
      (SimpleGraph.Embedding.induce
        (G := G) (U : Set (Fin N))).toHom).IsCycle
    rw [Walk.map_induce]
    exact hp
  have hqUCycle : qU.IsCycle := by
    apply (Walk.map_isCycle_iff_of_injective
      (f := (SimpleGraph.Embedding.induce
        (G := G) (U : Set (Fin N))).toHom)
      (SimpleGraph.Embedding.induce
        (G := G) (U : Set (Fin N))).injective).mp
    change ((q.induce (U : Set (Fin N)) hqSub).map
      (SimpleGraph.Embedding.induce
        (G := G) (U : Set (Fin N))).toHom).IsCycle
    rw [Walk.map_induce]
    exact hq
  have hneqU : pU.edges.toFinset ≠ qU.edges.toFinset := by
    intro heq
    apply hXY
    apply Subtype.ext
    rw [← hpEdges, ← hqEdges]
    let f : K →g G := (SimpleGraph.Embedding.induce
      (G := G) (U : Set (Fin N))).toHom
    have hpWalk : pU.map f = p := by
      exact Walk.map_induce (s := (U : Set (Fin N))) p hpSub
    have hqWalk : qU.map f = q := by
      exact Walk.map_induce (s := (U : Set (Fin N))) q hqSub
    ext e
    simp only [List.mem_toFinset]
    constructor
    · intro hep
      have hep' : e ∈ (pU.map f).edges := hpWalk.symm ▸ hep
      rw [Walk.edges_map] at hep'
      obtain ⟨eU, heUp, heUe⟩ := List.mem_map.mp hep'
      have heUq : eU ∈ qU.edges :=
        List.mem_toFinset.mp (heq ▸ List.mem_toFinset.mpr heUp)
      have heq' : e ∈ (qU.map f).edges := by
        rw [Walk.edges_map]
        exact List.mem_map.mpr ⟨eU, heUq, heUe⟩
      exact hqWalk ▸ heq'
    · intro heq'
      have heq'' : e ∈ (qU.map f).edges := hqWalk.symm ▸ heq'
      rw [Walk.edges_map] at heq''
      obtain ⟨eU, heUq, heUe⟩ := List.mem_map.mp heq''
      have heUp : eU ∈ pU.edges :=
        List.mem_toFinset.mp (heq.symm ▸ List.mem_toFinset.mpr heUq)
      have hep : e ∈ (pU.map f).edges := by
        rw [Walk.edges_map]
        exact List.mem_map.mpr ⟨eU, heUp, heUe⟩
      exact hpWalk ▸ hep
  have hmany : Fintype.card U < #K.edgeFinset :=
    card_lt_card_edgeFinset_of_two_cycles K hKconn pU qU
      hpUCycle hqUCycle hneqU
  have hUcard : #U ≤ 2 * g := by
    calc
      #U ≤ #(edgeVertexFinset X.1) + #(edgeVertexFinset Y.1) :=
        Finset.card_union_le _ _
      _ = p.length + q.length := by
        rw [← hpEdges, ← hqEdges,
          card_edgeVertexFinset_edges_toFinset_eq_length_of_isCycle G p hp,
          card_edgeVertexFinset_edges_toFinset_eq_length_of_isCycle G q hq]
      _ ≤ 2 * g := by omega
  let T : Set (Sym2 (Fin N)) :=
    {e | e ∈ G.edgeSet ∧ e ∈ U.sym2}
  let ef : Sym2 U → Sym2 (Fin N) :=
    Sym2.map (Function.Embedding.subtype fun x => x ∈ (U : Set (Fin N)))
  have hefInj : Function.Injective ef := by
    exact (Function.Embedding.subtype
      (fun x => x ∈ (U : Set (Fin N)))).sym2Map.injective
  have hpre : K.edgeSet = ef ⁻¹' T := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
        simp [K, ef, T, SimpleGraph.mem_edgeSet,
          Function.Embedding.sym2Map_apply]
        intro _ a ha _
        exact ha
  have hTrange : T ⊆ Set.range ef := by
    intro e he
    rcases he with ⟨heG, heU⟩
    induction e using Sym2.ind with
    | _ x y =>
        rw [Finset.mk_mem_sym2_iff] at heU
        refine ⟨s(⟨x, heU.1⟩, ⟨y, heU.2⟩), ?_⟩
        simp [ef, Function.Embedding.sym2Map_apply]
  have hncardPre : (ef ⁻¹' T).ncard = T.ncard :=
    Set.ncard_preimage_of_injective_subset_range hefInj hTrange
  have hKedgeNcard : K.edgeSet.ncard = T.ncard := by
    rw [hpre]
    exact hncardPre
  have hedgeFinCard : #K.edgeFinset = K.edgeSet.ncard := by
    calc
      #K.edgeFinset = Fintype.card K.edgeSet := K.edgeFinset_card
      _ = Nat.card K.edgeSet := Nat.card_eq_fintype_card.symm
      _ = K.edgeSet.ncard := Nat.card_coe_set_eq K.edgeSet
  have hcount : #U < RB.internalEdgeCount E U := by
    rw [RB.internalEdgeCount_eq_card_filter E U]
    change #U < T.ncard
    rw [← hKedgeNcard, ← hedgeFinCard]
    simpa only [Fintype.card_coe] using hmany
  exact (Nat.not_lt_of_ge (h.locally_sparse U hUcard)) hcount

end TwoCycles

end

end LeanCo.HypercubeTuran
