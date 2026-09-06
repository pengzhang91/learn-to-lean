import LeanCo.HypercubeTuran.BaseGraph
import LeanCo.HypercubeTuran.MaxDegreeTwo
import LeanCo.HypercubeTuran.ShortCycleAlteration
import Mathlib.Tactic

/-!
# Deterministic estimates for the short-cycle alteration

Deleting a matching costs at most one incident edge at each vertex.  This
file records the two consequences used by the random construction: cuts lose
at most the smaller shore, and an independent set in the altered graph
contains a one-third-size independent set in the original graph.
-/

open scoped SimpleGraph

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable section

/-- Neighbors of `v` whose incident edge belongs to `D`. -/
def deletedNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Sym2 V)) (v : V) : Finset V :=
  G.neighborFinset v |>.filter fun w => s(v, w) ∈ D

theorem card_deletedNeighborFinset_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Sym2 V)) (hD : IsEdgeFinsetMatching D) (v : V) :
    #(deletedNeighborFinset G D v) ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro x y hx hy
  simp only [deletedNeighborFinset, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset] at hx hy
  have hedges : s(v, x) = s(v, y) :=
    hD hx.2 hy.2 ⟨v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  exact Sym2.congr_right.mp hedges

theorem source_neighbor_sdiff_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Sym2 V)) (S : Finset V) (v : V) :
    G.neighborFinset v \ S ⊆
      ((G.deleteEdges (D : Set (Sym2 V))).neighborFinset v \ S) ∪
        deletedNeighborFinset G D v := by
  intro w hw
  simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset,
    Finset.mem_union, deletedNeighborFinset, Finset.mem_filter] at hw ⊢
  by_cases hDvw : s(v, w) ∈ D
  · exact Or.inr ⟨hw.1, hDvw⟩
  · exact Or.inl ⟨by simpa using ⟨hw.1, hDvw⟩, hw.2⟩

/-- From a fixed shore, deleting a matching removes at most one crossing
edge per vertex. -/
theorem cutSize_le_deleteEdges_add_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Sym2 V)) (hD : IsEdgeFinsetMatching D)
    (S : Finset V) :
    cutSize G S ≤
      cutSize (G.deleteEdges (D : Set (Sym2 V))) S + #S := by
  change S.sum (fun v => #(G.neighborFinset v \ S)) ≤
    S.sum (fun v =>
      #((G.deleteEdges (D : Set (Sym2 V))).neighborFinset v \ S)) + #S
  calc
    S.sum (fun v => #(G.neighborFinset v \ S)) ≤
        S.sum (fun v =>
          #((G.deleteEdges (D : Set (Sym2 V))).neighborFinset v \ S) + 1) := by
      refine Finset.sum_le_sum (s := S) fun v hv => ?_
      calc
        #(G.neighborFinset v \ S) ≤
            #(((G.deleteEdges (D : Set (Sym2 V))).neighborFinset v \ S) ∪
              deletedNeighborFinset G D v) :=
          Finset.card_le_card (source_neighbor_sdiff_subset G D S v)
        _ ≤ #((G.deleteEdges (D : Set (Sym2 V))).neighborFinset v \ S) +
              #(deletedNeighborFinset G D v) := Finset.card_union_le _ _
        _ ≤ #((G.deleteEdges (D : Set (Sym2 V))).neighborFinset v \ S) + 1 :=
          Nat.add_le_add_left (card_deletedNeighborFinset_le_one G D hD v) _
    _ = S.sum (fun v =>
          #((G.deleteEdges (D : Set (Sym2 V))).neighborFinset v \ S)) +
          S.sum (fun _v => 1) := Finset.sum_add_distrib
    _ = S.sum (fun v =>
          #((G.deleteEdges (D : Set (Sym2 V))).neighborFinset v \ S)) + #S := by
      simp

private theorem cutSize_eq_doubleSum
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutSize G S =
      ∑ v ∈ S, ∑ w ∈ Sᶜ, if G.Adj v w then 1 else 0 := by
  rw [cutSize]
  apply Finset.sum_congr rfl
  intro v hv
  have heq : G.neighborFinset v \ S =
      Sᶜ.filter (G.Adj v) := by
    ext w
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- A graph cut has the same cardinality when the two shores are swapped. -/
theorem cutSize_compl
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutSize G Sᶜ = cutSize G S := by
  rw [cutSize_eq_doubleSum, cutSize_eq_doubleSum]
  simp only [compl_compl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro w hw
  simp only [G.adj_comm]

/-- The loss across a cut is bounded by either shore. -/
theorem cutSize_le_deleteEdges_add_compl_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Sym2 V)) (hD : IsEdgeFinsetMatching D)
    (S : Finset V) :
    cutSize G S ≤
      cutSize (G.deleteEdges (D : Set (Sym2 V))) S + #Sᶜ := by
  simpa only [cutSize_compl] using
    cutSize_le_deleteEdges_add_card G D hD Sᶜ

/-- Deleting edges cannot spoil an upper bound on the total edge count. -/
theorem controlledEdgeCount_deleteEdges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Sym2 V)) {d : ℕ}
    (hcontrol : HasControlledEdgeCount G d) :
    HasControlledEdgeCount (G.deleteEdges (D : Set (Sym2 V))) d := by
  unfold HasControlledEdgeCount graphEdgeCount at hcontrol ⊢
  have hcard : #(G.deleteEdges (D : Set (Sym2 V))).edgeFinset ≤
      #G.edgeFinset :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _))
  exact (Nat.mul_le_mul_left 4 hcard).trans hcontrol

/-- The stronger source cut estimate survives deletion of a matching with
the constants used by `IsCombinatorialBase`. -/
theorem strongCutExpansion_deleteEdges_of_matching
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Sym2 V)) (hD : IsEdgeFinsetMatching D)
    {d : ℕ} (hd : 10 ≤ d)
    (hstrong : ∀ S : Finset V,
      8 * d * #S * (Fintype.card V - #S) ≤
        5 * Fintype.card V * cutSize G S) :
    HasStrongCutExpansion (G.deleteEdges (D : Set (Sym2 V))) d := by
  intro S
  let N := Fintype.card V
  let s := #S
  let t := #Sᶜ
  let H := G.deleteEdges (D : Set (Sym2 V))
  have hsN : s ≤ N := by
    dsimp [s, N]
    simpa using Finset.card_le_univ S
  have ht_eq : t = N - s := by
    dsimp [t, N, s]
    exact Finset.card_compl S
  have hsum : N = s + t := by omega
  have hsource : 8 * d * s * t ≤ 5 * N * cutSize G S := by
    simpa [N, s, t, ht_eq] using hstrong S
  have finish (loss : ℕ) (hloss : cutSize G S ≤ cutSize H S + loss)
      (hpenalty : 5 * N * loss ≤ d * s * t) :
      7 * d * s * t ≤ 5 * N * cutSize H S := by
    have hscaled : 5 * N * cutSize G S ≤
        5 * N * (cutSize H S + loss) :=
      Nat.mul_le_mul_left (5 * N) hloss
    have h8 : 8 * (d * s * t) ≤
        5 * N * cutSize H S + d * s * t := by
      calc
        8 * (d * s * t) = 8 * d * s * t := by ring
        _ ≤ 5 * N * cutSize G S := hsource
        _ ≤ 5 * N * (cutSize H S + loss) := hscaled
        _ = 5 * N * cutSize H S + 5 * N * loss := by ring
        _ ≤ 5 * N * cutSize H S + d * s * t :=
          Nat.add_le_add_left hpenalty _
    have hresult : 7 * (d * s * t) ≤ 5 * N * cutSize H S := by omega
    simpa only [Nat.mul_assoc] using hresult
  change 7 * d * s * (N - s) ≤ 5 * N * cutSize H S
  rw [← ht_eq]
  by_cases hst : s ≤ t
  · apply finish s
    · simpa [H, s] using cutSize_le_deleteEdges_add_card G D hD S
    · have hNle : N ≤ 2 * t := by omega
      have hcoef : 5 * N ≤ d * t := by
        calc
          5 * N ≤ 5 * (2 * t) := Nat.mul_le_mul_left 5 hNle
          _ = 10 * t := by ring
          _ ≤ d * t := Nat.mul_le_mul_right t hd
      have := Nat.mul_le_mul_right s hcoef
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
  · have hts : t ≤ s := by omega
    apply finish t
    · simpa [H, t] using cutSize_le_deleteEdges_add_compl_card G D hD S
    · have hNle : N ≤ 2 * s := by omega
      have hcoef : 5 * N ≤ d * s := by
        calc
          5 * N ≤ 5 * (2 * s) := Nat.mul_le_mul_left 5 hNle
          _ = 10 * s := by ring
          _ ≤ d * s := Nat.mul_le_mul_right s hd
      have := Nat.mul_le_mul_right t hcoef
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

/-- A positive uniform cut lower bound forces connectedness on a nonempty
finite vertex type. -/
theorem connected_of_strongCutExpansion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hcard : 0 < Fintype.card V) (hd : 0 < d)
    (hexpand : HasStrongCutExpansion G d) : G.Connected := by
  classical
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨root⟩ := Fintype.card_pos_iff.mp hcard
  refine ⟨root, fun w => ?_⟩
  by_contra hnreach
  let S : Finset V := Finset.univ.filter fun x => G.Reachable root x
  have hrootS : root ∈ S := by simp [S]
  have hwS : w ∉ S := by simpa [S] using hnreach
  have hScard_pos : 0 < #S := Finset.card_pos.mpr ⟨root, hrootS⟩
  have hSlt : #S < Fintype.card V := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, ?_⟩
    intro hSuniv
    have : w ∈ S := hSuniv.symm ▸ Finset.mem_univ w
    exact hwS this
  have hcut_zero : cutSize G S = 0 := by
    rw [cutSize]
    apply Finset.sum_eq_zero
    intro x hx
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨y, hy⟩
    simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hy
    have hxreach : G.Reachable root x := by simpa [S] using hx
    have hyreach : G.Reachable root y :=
      hxreach.trans hy.1.reachable
    have hyS : y ∈ S := by simpa [S] using hyreach
    exact hy.2 hyS
  have hbound := hexpand S
  rw [hcut_zero, Nat.mul_zero] at hbound
  have hcompl_pos : 0 < Fintype.card V - #S := by omega
  have hpositive : 0 < 7 * d * #S * (Fintype.card V - #S) := by positivity
  omega

/-- Deterministic hypotheses required before deleting one edge from every
short cycle.  These are precisely the finite events supplied by the random
graph existence argument. -/
structure IsAlterationSource (G : SimpleGraph V) [DecidableRel G.Adj]
    (d g : ℕ) : Prop where
  ten_le_card : 10 ≤ Fintype.card V
  ten_le_d : 10 ≤ d
  edgeCount_control : HasControlledEdgeCount G d
  stronger_cut : ∀ S : Finset V,
    8 * d * #S * (Fintype.card V - #S) ≤
      5 * Fintype.card V * cutSize G S
  very_small_independent : ∀ I : Finset V,
    G.IsIndepSet (I : Set V) → 300 * #I < Fintype.card V
  shortCycles_disjoint : ShortCyclesVertexDisjoint G g

/-- If `I` is independent after deleting a matching, the graph induced by
`G` on `I` has maximum degree at most one. -/
theorem source_degree_le_one_of_independent_deleteEdges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Sym2 V)) (hD : IsEdgeFinsetMatching D)
    (I : Finset V)
    (hI : (G.deleteEdges (D : Set (Sym2 V))).IsIndepSet (I : Set V)) :
    ∀ v ∈ I, #(G.neighborFinset v ∩ I) ≤ 1 := by
  intro v hv
  rw [Finset.card_le_one_iff]
  intro x y hx hy
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx hy
  have hxD : s(v, x) ∈ D := by
    by_contra hnot
    have hadj : (G.deleteEdges (D : Set (Sym2 V))).Adj v x := by
      simpa using ⟨hx.1, hnot⟩
    exact (hI hv hx.2 hx.1.ne) hadj
  have hyD : s(v, y) ∈ D := by
    by_contra hnot
    have hadj : (G.deleteEdges (D : Set (Sym2 V))).Adj v y := by
      simpa using ⟨hy.1, hnot⟩
    exact (hI hv hy.2 hy.1.ne) hadj
  have hedges : s(v, x) = s(v, y) :=
    hD hxD hyD ⟨v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  exact Sym2.congr_right.mp hedges

/-- Independent sets grow by a factor of at most three when a matching is
deleted, provided the original graph has the stated `300`-scaled bound. -/
theorem smallIndependentSets_deleteEdges_of_matching
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Sym2 V)) (hD : IsEdgeFinsetMatching D)
    (hsmall : ∀ J : Finset V, G.IsIndepSet (J : Set V) →
      300 * #J < Fintype.card V) :
    HasSmallIndependentSets (G.deleteEdges (D : Set (Sym2 V))) := by
  intro I hI
  obtain ⟨J, hJI, hJind, hcard⟩ :=
    exists_indepSet_card_third G I (fun v hv =>
      (source_degree_le_one_of_independent_deleteEdges G D hD I hI v hv).trans
        (by omega))
  have hsource := hsmall J hJind
  omega

/-- Altering a source certificate gives exactly the combinatorial base used
by the hypercube argument. -/
theorem IsAlterationSource.deleteShortCycles_isCombinatorialBase
    {G : SimpleGraph V} [DecidableRel G.Adj] {d g : ℕ}
    (h : IsAlterationSource G d g) :
    IsCombinatorialBase (deleteShortCycles G g) d := by
  let D := shortCycleDeletionEdges G g
  have hmatch : IsEdgeFinsetMatching D :=
    shortCycleDeletionEdges_isMatching h.shortCycles_disjoint
  have hcuts : HasStrongCutExpansion (deleteShortCycles G g) d := by
    change HasStrongCutExpansion (G.deleteEdges (D : Set (Sym2 V))) d
    exact strongCutExpansion_deleteEdges_of_matching G D hmatch h.ten_le_d h.stronger_cut
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) h.ten_le_d
  have hcardpos : 0 < Fintype.card V :=
    lt_of_lt_of_le (by norm_num) h.ten_le_card
  refine
    { ten_le_card := h.ten_le_card
      d_pos := hdpos
      connected := connected_of_strongCutExpansion _ hcardpos hdpos hcuts
      edgeCount_control := ?_
      cut_expansion := hcuts
      small_independent := ?_ }
  · change HasControlledEdgeCount (G.deleteEdges (D : Set (Sym2 V))) d
    exact controlledEdgeCount_deleteEdges G D h.edgeCount_control
  · change HasSmallIndependentSets (G.deleteEdges (D : Set (Sym2 V)))
    exact smallIndependentSets_deleteEdges_of_matching
      G D hmatch h.very_small_independent

end

end LeanCo.HypercubeTuran
