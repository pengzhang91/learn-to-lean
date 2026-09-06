import LeanCo.PackingEdgeColoring.TreeRotation

/-!
# Euler characteristic bound for rotation systems

This file proves the genus-independent inequality `|V| + |F| ≤ |E| + 2`
for a rotation system on a finite connected graph.  The proof deletes edges
outside a spanning tree.  One deletion can lower the old face count by at
most one, while a tree rotation has at most one face.
-/

open scoped BigOperators SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Deleting one edge can reduce the number of facial cycles by at most one.
This includes all same-face degeneracies at degree-one endpoints. -/
theorem deleteEdge_faceCount_le_add_one
    (R : RotationSystem G) (e : Sym2 V) (a : G.Dart)
    (ha : a.edge = e) :
    R.faceCount ≤ (R.deleteEdge e a ha).faceCount + 1 := by
  by_cases hsame : R.faceStep.SameCycle a a.symm
  · obtain ⟨p, q, -, -, -, -, hface, -, -⟩ :=
      R.exists_deleteEdge_faceSplit_of_sameCycle e a ha hsame
    by_cases hp : 2 ≤ p.length <;> by_cases hq : 2 ≤ q.length <;>
      simp only [if_pos, hp, hq] at hface <;> omega
  · have htwo : R.IsTwoSidedDart a :=
      (R.isTwoSidedDart_iff_not_sameCycle a).mpr hsame
    have hface := R.deleteEdge_faceCount_add_one_of_isTwoSidedDart
      e a ha htwo
    omega

/-- Every face contains at least two darts, hence there are at most as many
faces as undirected edges. -/
theorem faceCount_le_card_edges (R : RotationSystem G) :
    R.faceCount ≤ G.edgeFinset.card := by
  have hsum : 2 * R.faceCount ≤ ∑ f : R.Face, R.faceLength f := by
    rw [R.faceCount_eq_card_face]
    calc
      2 * Fintype.card R.Face = ∑ _f : R.Face, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ f : R.Face, R.faceLength f := by
        apply Finset.sum_le_sum
        intro f _
        exact R.two_le_faceLength f
  rw [R.sum_faceLength_eq_two_mul_card_edges] at hsum
  omega

/-- A finite tree rotation has at most one face, including the singleton
tree, which has no darts and no faces. -/
theorem faceCount_le_one_of_isTree (R : RotationSystem G) (hG : G.IsTree) :
    R.faceCount ≤ 1 := by
  by_cases hedge : G.edgeSet.Nonempty
  · rw [R.faceCount_eq_one_of_isTree_of_edgeSet_nonempty hG hedge]
  · have hbot : G = ⊥ := by
      simpa only [SimpleGraph.edgeSet_nonempty, not_ne_iff] using hedge
    have hface := R.faceCount_le_card_edges
    have hcard : G.edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero, SimpleGraph.edgeFinset_eq_empty]
      exact hbot
    omega

/-- Every present undirected edge has an oriented dart above it. -/
theorem exists_dart_edge_eq_of_mem_edgeSet (e : Sym2 V)
    (he : e ∈ G.edgeSet) : ∃ a : G.Dart, a.edge = e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by
        simpa only [SimpleGraph.mem_edgeSet] using he
      exact ⟨⟨(u, v), huv⟩, rfl⟩

end Finite

section SpanningTree

variable [Fintype V] [DecidableEq V]

/-- Relative Euler bound: if `T` is a spanning tree subgraph, the number of
faces is at most one plus the number of edges outside `T`.  The ambient graph
is explicit so the well-founded recursion can change it after deletion. -/
theorem faceCount_le_card_sdiff_add_one_of_isTree_le
    (G' T : SimpleGraph V) [DecidableRel G'.Adj] [DecidableRel T.Adj]
    (R : RotationSystem G') (hT : T.IsTree) (hTG : T ≤ G') :
    R.faceCount ≤ (G'.edgeFinset \ T.edgeFinset).card + 1 := by
  classical
  by_cases hempty : G'.edgeFinset \ T.edgeFinset = ∅
  · have hGT : G' ≤ T := by
      rw [← SimpleGraph.edgeFinset_subset_edgeFinset]
      exact Finset.sdiff_eq_empty_iff_subset.mp hempty
    have hEq : T = G' := le_antisymm hTG hGT
    have hGtree : G'.IsTree := hEq ▸ hT
    have hface := R.faceCount_le_one_of_isTree hGtree
    have hcard : (G'.edgeFinset \ T.edgeFinset).card = 0 := by
      rw [hempty]
      rfl
    omega
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have he' := Finset.mem_sdiff.mp he
    have heG : e ∈ G'.edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using he'.1
    obtain ⟨a, ha⟩ := exists_dart_edge_eq_of_mem_edgeSet e heG
    let H : SimpleGraph V := G'.deleteEdges {e}
    let R' : RotationSystem H := R.deleteEdge e a ha
    have hTH : T ≤ H := by
      intro u v huv
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hTG huv, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro huvEdge
      apply he'.2
      rw [← huvEdge, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact huv
    have hdiff : H.edgeFinset \ T.edgeFinset =
        (G'.edgeFinset \ T.edgeFinset).erase e := by
      ext q
      simp only [H, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
        SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff,
        Set.mem_singleton_iff, Finset.mem_erase]
      tauto
    have hlt : (H.edgeFinset \ T.edgeFinset).card <
        (G'.edgeFinset \ T.edgeFinset).card := by
      rw [hdiff]
      exact Finset.card_erase_lt_of_mem he
    have hrec := faceCount_le_card_sdiff_add_one_of_isTree_le
      H T R' hT hTH
    change (R.deleteEdge e a ha).faceCount ≤
      (H.edgeFinset \ T.edgeFinset).card + 1 at hrec
    have hface := R.deleteEdge_faceCount_le_add_one e a ha
    have hcard : (H.edgeFinset \ T.edgeFinset).card + 1 =
        (G'.edgeFinset \ T.edgeFinset).card := by
      rw [hdiff]
      exact Finset.card_erase_add_one he
    omega
termination_by (G'.edgeFinset \ T.edgeFinset).card
decreasing_by exact hlt

/-- Euler's genus-independent upper bound for a finite connected rotation
system.  Equality is the spherical case; no topological realization theorem
is needed for this combinatorial inequality. -/
theorem eulerCharacteristic_le_two
    (G' : SimpleGraph V) [DecidableRel G'.Adj]
    (R : RotationSystem G') (hG : G'.Connected) :
    Fintype.card V + R.faceCount ≤ G'.edgeFinset.card + 2 := by
  classical
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  letI : DecidableRel T.Adj := Classical.decRel _
  have hface := faceCount_le_card_sdiff_add_one_of_isTree_le
    G' T R hT hTG
  have htree := hT.card_edgeFinset
  have hsubset : T.edgeFinset ⊆ G'.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hTG
  have hedge := Finset.card_sdiff_add_card_eq_card hsubset
  omega

end SpanningTree

end RotationSystem

end

end LeanCo.PackingEdgeColoring
