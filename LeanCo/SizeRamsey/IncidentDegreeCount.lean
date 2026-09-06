import LeanCo.SizeRamsey.GraphBasics

/-!
# Degree counting over a set meeting every edge

An approximately regular peeled layer has a distinguished vertex set meeting
every edge.  Summing degrees over that set therefore counts every edge at
least once and at most twice.  These exact natural-number inequalities give
the vertex-cardinality bounds used before applying the BLS subgraph-finding
lemma.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- Every edge of `G` has an endpoint in `S`. -/
def EdgesMeet [DecidableEq V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃x y⦄, G.Adj x y → x ∈ S ∨ y ∈ S

/-- If `S` meets every edge, summing degrees over `S` counts every edge at
least once.  The proof injects an undirected edge into an incident oriented
edge whose first endpoint lies in `S`. -/
theorem edgeCount_le_sum_degrees_over_edgeMeetingSet
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hmeet : EdgesMeet G S) :
    edgeCount G ≤ ∑ v : S, G.degree (v : V) := by
  have hout (e : G.edgeSet) : G.Adj e.1.out.1 e.1.out.2 := by
    rw [← mem_edgeSet]
    change Quot.mk (Sym2.Rel V) e.1.out ∈ G.edgeSet
    rw [e.1.out_eq]
    exact e.2
  let orient : G.edgeSet → Σ v : S, G.neighborSet (v : V) := fun e ↦
    if hx : e.1.out.1 ∈ S then
      ⟨⟨e.1.out.1, hx⟩, ⟨e.1.out.2, by
        exact hout e⟩⟩
    else
      ⟨⟨e.1.out.2, by
          exact (hmeet (hout e)).resolve_left hx⟩,
        ⟨e.1.out.1, by
          exact (hout e).symm⟩⟩
  let forget : (Σ v : S, G.neighborSet (v : V)) → Sym2 V :=
    fun p ↦ s((p.1 : V), (p.2 : V))
  have hforget (e : G.edgeSet) : forget (orient e) = e.1 := by
    by_cases hx : e.1.out.1 ∈ S
    · simp only [orient, hx, dif_pos, forget]
      exact e.1.out_eq
    · simp only [orient, hx, forget]
      rw [Sym2.eq_swap]
      exact e.1.out_eq
  have horient : Function.Injective orient := by
    intro e f hef
    apply Subtype.ext
    calc
      e.1 = forget (orient e) := (hforget e).symm
      _ = forget (orient f) := congrArg forget hef
      _ = f.1 := hforget f
  have hcard := Fintype.card_le_of_injective orient horient
  rw [Fintype.card_sigma] at hcard
  simpa only [edgeCount, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
    using hcard

/-- A partial degree sum is at most the total degree sum, hence at most twice
the number of edges. -/
theorem sum_degrees_over_finset_le_twice_edgeCount
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ v : S, G.degree (v : V)) ≤ 2 * edgeCount G := by
  calc
    (∑ v : S, G.degree (v : V)) = ∑ v ∈ S, G.degree v := by
      exact Finset.sum_attach S (fun v ↦ G.degree v)
    _ ≤ ∑ v, G.degree v :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    _ = 2 * edgeCount G := by
      rw [G.sum_degrees_eq_twice_card_edges,
        ← edgeCount_eq_card_edgeFinset]

/-- Minimum degree on an edge-meeting set bounds its cardinality from above. -/
theorem mul_card_le_twice_edgeCount_of_degree_lower
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {d : ℕ}
    (hlower : ∀ v ∈ S, d ≤ G.degree v) :
    d * S.card ≤ 2 * edgeCount G := by
  calc
    d * S.card = ∑ _v : S, d := by simp [Nat.mul_comm]
    _ ≤ ∑ v : S, G.degree (v : V) := by
      apply Finset.sum_le_sum
      intro v _
      exact hlower v v.2
    _ ≤ 2 * edgeCount G :=
      sum_degrees_over_finset_le_twice_edgeCount G S

/-- Maximum degree on an edge-meeting set bounds its cardinality from below. -/
theorem edgeCount_le_card_mul_of_edgeMeetingSet_degree_upper
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {D : ℕ} (hmeet : EdgesMeet G S)
    (hupper : ∀ v ∈ S, G.degree v ≤ D) :
    edgeCount G ≤ S.card * D := by
  calc
    edgeCount G ≤ ∑ v : S, G.degree (v : V) :=
      edgeCount_le_sum_degrees_over_edgeMeetingSet G S hmeet
    _ ≤ ∑ _v : S, D := by
      apply Finset.sum_le_sum
      intro v _
      exact hupper v v.2
    _ = S.card * D := by simp

end

end LeanCo.SizeRamsey
