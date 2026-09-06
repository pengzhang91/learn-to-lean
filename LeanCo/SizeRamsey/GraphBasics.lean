import LeanCo.SizeRamsey.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Finite graph basics for the size--Ramsey argument

This file records the elementary finite-graph language used throughout the
upper-bound proof: external neighbourhoods, edges spanned by a vertex set,
local sparsity and expansion, scaled average/minimum-degree hypotheses, and a
walk-based formulation of containing a cycle of a prescribed length.

The average-degree predicates are deliberately written without division.  Thus
`HasAverageDegreeAtLeast G d` means `d * |V(G)| <= 2 * e(G)`, exactly the form
used by the degree-sum identity.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u v

variable {V : Type u} {W : Type v}

/-! ## Edge counts -/

/-- On a finite graph with decidable adjacency, the choice-free `edgeCount`
agrees with the cardinality of mathlib's `edgeFinset`. -/
theorem edgeCount_eq_card_edgeFinset (G : SimpleGraph V) [Fintype V]
    [DecidableRel G.Adj] :
    edgeCount G = #G.edgeFinset := by
  rw [edgeCount, Nat.card_eq_fintype_card, G.card_edgeSet]

/-- An injective graph homomorphism cannot decrease the number of edges. -/
theorem edgeCount_le_of_copy {G : SimpleGraph V} {H : SimpleGraph W}
    [Finite H.edgeSet] (f : G.Copy H) :
    edgeCount G <= edgeCount H := by
  exact Nat.card_le_card_of_injective f.mapEdgeSet f.mapEdgeSet.injective

/-- Edge count is monotone under the subgraph order. -/
theorem edgeCount_mono {G H : SimpleGraph V} [Finite H.edgeSet] (h : G <= H) :
    edgeCount G <= edgeCount H :=
  edgeCount_le_of_copy (Copy.ofLE G H h)

/-- The number of edges of `G` with both endpoints in `S`. -/
noncomputable def spannedEdgeCount (G : SimpleGraph V) (S : Set V) : Nat :=
  edgeCount (G.induce S)

@[simp]
theorem spannedEdgeCount_empty (G : SimpleGraph V) :
    spannedEdgeCount G (∅ : Set V) = 0 := by
  change edgeCount (G.induce (∅ : Set V)) = 0
  have hbot : G.induce (∅ : Set V) = (⊥ : SimpleGraph (∅ : Set V)) := by
    ext u
    exact u.property.elim
  rw [hbot]
  simp [edgeCount]

/-- Enlarging the ambient graph can only enlarge the number of edges spanned
by a fixed vertex set. -/
theorem spannedEdgeCount_mono_graph {G H : SimpleGraph V} [Finite V]
    (h : G <= H) (S : Set V) :
    spannedEdgeCount G S <= spannedEdgeCount H S := by
  apply edgeCount_mono
  exact fun _ _ hadj => h hadj

/-- Enlarging the vertex set can only enlarge its spanned edge count. -/
theorem spannedEdgeCount_mono_set (G : SimpleGraph V) [Finite V]
    {S T : Set V} (h : S <= T) :
    spannedEdgeCount G S <= spannedEdgeCount G T := by
  apply edgeCount_le_of_copy
  exact (G.induceHomOfLE h).toCopy

/-- Every induced subgraph spans at most all the edges of its ambient graph. -/
theorem spannedEdgeCount_le (G : SimpleGraph V) [Finite V] (S : Set V) :
    spannedEdgeCount G S <= edgeCount G :=
  edgeCount_le_of_copy (Copy.induce G S)

/-! ## External neighbourhoods, local sparsity, and local expansion -/

/-- The vertices outside `S` having a neighbour in `S`. -/
def externalNeighborFinset (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  Finset.univ.filter fun v => v ∉ S ∧ ∃ u ∈ S, G.Adj u v

@[simp]
theorem mem_externalNeighborFinset (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {S : Finset V} {v : V} :
    v ∈ externalNeighborFinset G S ↔ v ∉ S ∧ ∃ u ∈ S, G.Adj u v := by
  simp [externalNeighborFinset]

@[simp]
theorem externalNeighborFinset_empty (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] :
    externalNeighborFinset G ∅ = ∅ := by
  ext
  simp

/-- External neighbourhoods are monotone in the ambient graph (for a fixed
vertex set). -/
theorem externalNeighborFinset_mono_graph {G H : SimpleGraph V} [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G <= H) (S : Finset V) :
    externalNeighborFinset G S ⊆ externalNeighborFinset H S := by
  intro v hv
  rw [mem_externalNeighborFinset] at hv ⊢
  obtain ⟨u, huS, huv⟩ := hv.2
  exact ⟨hv.1, ⟨u, huS, h huv⟩⟩

/-- Every set of at most `vertexBound` vertices spans at most
`edgeFactor * |S|` edges. -/
def IsLocallySparse (G : SimpleGraph V) (vertexBound edgeFactor : Nat) : Prop :=
  ∀ S : Finset V, #S <= vertexBound ->
    spannedEdgeCount G (S : Set V) <= edgeFactor * #S

/-- Every nonempty set of at most `vertexBound` vertices has strictly more
than `expansionFactor * |S|` external neighbours. -/
def HasLocalExpansion (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (vertexBound expansionFactor : Nat) : Prop :=
  ∀ S : Finset V, S.Nonempty -> #S <= vertexBound ->
    expansionFactor * #S < #(externalNeighborFinset G S)

/-- Local expansion is monotone under adding edges. -/
theorem HasLocalExpansion.mono {G H : SimpleGraph V} [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    {vertexBound expansionFactor : Nat} (hGH : G <= H)
    (hG : HasLocalExpansion G vertexBound expansionFactor) :
    HasLocalExpansion H vertexBound expansionFactor := by
  intro S hS hcard
  exact (hG S hS hcard).trans_le
    (Finset.card_le_card (externalNeighborFinset_mono_graph hGH S))

/-! ## Average and minimum degree -/

/-- Scaled average degree at least `d`: `d * |V| <= 2 * e(G)`. -/
def HasAverageDegreeAtLeast (G : SimpleGraph V) (d : Nat) : Prop :=
  d * Nat.card V <= 2 * edgeCount G

/-- Scaled average degree strictly greater than `d`. -/
def HasAverageDegreeGreaterThan (G : SimpleGraph V) (d : Nat) : Prop :=
  d * Nat.card V < 2 * edgeCount G

/-- Every vertex has degree at least `d`. -/
def HasMinimumDegreeAtLeast (G : SimpleGraph V) [G.LocallyFinite] (d : Nat) : Prop :=
  ∀ v, d <= G.degree v

/-- Every vertex has degree strictly greater than `d`. -/
def HasMinimumDegreeGreaterThan (G : SimpleGraph V) [G.LocallyFinite] (d : Nat) : Prop :=
  ∀ v, d < G.degree v

theorem hasAverageDegreeAtLeast_iff_sum_degrees (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {d : Nat} :
    HasAverageDegreeAtLeast G d ↔ d * Fintype.card V <= ∑ v, G.degree v := by
  rw [HasAverageDegreeAtLeast, Nat.card_eq_fintype_card,
    edgeCount_eq_card_edgeFinset, G.sum_degrees_eq_twice_card_edges]

theorem hasAverageDegreeGreaterThan_iff_sum_degrees (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {d : Nat} :
    HasAverageDegreeGreaterThan G d ↔ d * Fintype.card V < ∑ v, G.degree v := by
  rw [HasAverageDegreeGreaterThan, Nat.card_eq_fintype_card,
    edgeCount_eq_card_edgeFinset, G.sum_degrees_eq_twice_card_edges]

theorem hasMinimumDegreeAtLeast_iff_minDegree (G : SimpleGraph V)
    [Fintype V] [Nonempty V] [DecidableRel G.Adj] {d : Nat} :
    HasMinimumDegreeAtLeast G d ↔ d <= G.minDegree := by
  constructor
  · exact G.le_minDegree_of_forall_le_degree d
  · intro h v
    exact h.trans (G.minDegree_le_degree v)

/-- Adding edges preserves a lower bound on every vertex degree. -/
theorem HasMinimumDegreeAtLeast.mono {G H : SimpleGraph V}
    [G.LocallyFinite] [H.LocallyFinite] {d : Nat} (hGH : G <= H)
    (hG : HasMinimumDegreeAtLeast G d) : HasMinimumDegreeAtLeast H d := by
  intro v
  exact (hG v).trans (G.degree_le_of_le hGH)

/-- A pointwise minimum-degree lower bound implies the corresponding
average-degree lower bound. -/
theorem HasMinimumDegreeAtLeast.hasAverageDegreeAtLeast (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] {d : Nat}
    (h : HasMinimumDegreeAtLeast G d) : HasAverageDegreeAtLeast G d := by
  rw [hasAverageDegreeAtLeast_iff_sum_degrees]
  calc
    d * Fintype.card V = ∑ _v : V, d := by simp [Nat.mul_comm]
    _ <= ∑ v : V, G.degree v := Finset.sum_le_sum fun v _ => h v

/-- Adding edges preserves a (weak) average-degree lower bound. -/
theorem HasAverageDegreeAtLeast.mono {G H : SimpleGraph V} [Finite V]
    {d : Nat} (hGH : G <= H) (hG : HasAverageDegreeAtLeast G d) :
    HasAverageDegreeAtLeast H d :=
  hG.trans (Nat.mul_le_mul_left 2 (edgeCount_mono hGH))

/-! ## Cycles as walks and as copies of `cycleGraph` -/

/-- `G` contains a simple closed walk with exactly `n` edges. -/
def ContainsCycleLength (G : SimpleGraph V) (n : Nat) : Prop :=
  ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = n

/-- A contained cycle has length at least three. -/
theorem ContainsCycleLength.three_le {G : SimpleGraph V} {n : Nat}
    (h : ContainsCycleLength G n) : 3 <= n := by
  obtain ⟨_, c, hc, rfl⟩ := h
  exact hc.three_le_length

/-- Adding edges preserves a cycle of a prescribed length. -/
theorem ContainsCycleLength.mono {G H : SimpleGraph V} {n : Nat}
    (hGH : G <= H) (hG : ContainsCycleLength G n) :
    ContainsCycleLength H n := by
  obtain ⟨v, c, hc, hlen⟩ := hG
  refine ⟨v, c.mapLe hGH, hc.mapLe hGH, ?_⟩
  change (c.map (Hom.ofLE hGH)).length = n
  rw [Walk.length_map, hlen]

/-- Mapping along a copy preserves a cycle of a prescribed length. -/
theorem ContainsCycleLength.map_copy {G : SimpleGraph V} {H : SimpleGraph W}
    {n : Nat} (f : G.Copy H) (hG : ContainsCycleLength G n) :
    ContainsCycleLength H n := by
  obtain ⟨v, c, hc, hlen⟩ := hG
  exact ⟨f v, c.map f.toHom, hc.map f.injective, by simpa using hlen⟩

/-- The cyclic adjacency alternatives expressed without modular subtraction. -/
theorem cycleGraph_adj_cases {n : Nat} (_hn : 3 <= n) {i j : Fin n}
    (hij : (cycleGraph n).Adj i j) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n) := by
  rw [cycleGraph_adj'] at hij
  rcases hij with hij | hij
  · have hsub := Fin.intCast_val_sub_eq_sub_add_ite i j
    rw [hij] at hsub
    by_cases hji : j <= i
    · right
      left
      simp [hji] at hsub
      omega
    · right
      right
      left
      simp [hji] at hsub
      constructor <;> omega
  · have hsub := Fin.intCast_val_sub_eq_sub_add_ite j i
    rw [hij] at hsub
    by_cases hij' : i <= j
    · left
      simp [hij'] at hsub
      omega
    · right
      right
      right
      simp [hij'] at hsub
      constructor <;> omega

/-- A closed walk of length at least three induces a homomorphism from the
cycle graph of the same length. -/
def cycleGraphHom {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hlen : 3 <= c.length) : cycleGraph c.length →g G where
  toFun i := c.getVert i.val
  map_rel' {i j} hij := by
    rcases cycleGraph_adj_cases hlen hij with h | h | h | h
    · simpa [h] using c.adj_getVert_succ (i := i.val) i.isLt
    · have hadj := c.adj_getVert_succ (i := j.val) j.isLt
      simpa [h] using hadj.symm
    · obtain ⟨hi, hj⟩ := h
      have hadj := c.adj_getVert_succ (i := j.val) j.isLt
      simpa [hi, hj] using hadj.symm
    · obtain ⟨hj, hi⟩ := h
      have hadj := c.adj_getVert_succ (i := i.val) i.isLt
      simpa [hj, hi] using hadj

/-- A simple closed walk supplies an actual copy of the corresponding cycle
graph. -/
def cycleGraphCopy {G : SimpleGraph V} {v : V}
    {c : G.Walk v v} (hc : c.IsCycle) : (cycleGraph c.length).Copy G := by
  refine ⟨cycleGraphHom c hc.three_le_length, ?_⟩
  intro i j hij
  apply Fin.ext
  apply hc.getVert_injOn'
  · simp only [Set.mem_setOf_eq]
    omega
  · simp only [Set.mem_setOf_eq]
    omega
  · exact hij

/-- The walk formulation always gives containment of `cycleGraph`. -/
theorem containsCycle_of_containsCycleLength {G : SimpleGraph V} {n : Nat}
    (h : ContainsCycleLength G n) : ContainsCycle G n := by
  obtain ⟨_, c, hc, rfl⟩ := h
  exact ⟨cycleGraphCopy hc⟩

/-- A copy of `cycleGraph n`, for `n >= 3`, maps its canonical cycle to a
simple closed walk of length `n`. -/
theorem containsCycleLength_of_containsCycle {G : SimpleGraph V} {n : Nat}
    (hn : 3 <= n) (h : ContainsCycle G n) : ContainsCycleLength G n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨f⟩ := h
  refine ⟨f 0, (cycleGraph.cycle m).map f.toHom, ?_, ?_⟩
  · exact cycleGraph.isCycle_cycle.map f.injective
  · simp

/-- For genuine cycle lengths, the walk and graph-copy formulations agree. -/
theorem containsCycleLength_iff_containsCycle {G : SimpleGraph V} {n : Nat}
    (hn : 3 <= n) :
    ContainsCycleLength G n ↔ ContainsCycle G n :=
  ⟨containsCycle_of_containsCycleLength,
    containsCycleLength_of_containsCycle hn⟩

end LeanCo.SizeRamsey
