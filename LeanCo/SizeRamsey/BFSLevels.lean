import LeanCo.SizeRamsey.GraphBasics
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Distance levels and finite BFS balls

These are the canonical level sets of a breadth-first search.  They are
defined directly from graph distance, so later arguments do not depend on an
implementation-specific queue or predecessor choice.
-/

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The vertices at graph distance exactly `i` from `root`. -/
noncomputable def distanceLevelFinset [Fintype V]
    (G : SimpleGraph V) (root : V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ G.dist root v = i

/-- The closed BFS ball of integral radius `i`. -/
noncomputable def closedBallFinset [Fintype V]
    (G : SimpleGraph V) (root : V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ G.dist root v ≤ i

@[simp]
theorem mem_distanceLevelFinset [Fintype V] (root : V) {i : ℕ} {v : V} :
    v ∈ distanceLevelFinset G root i ↔ G.dist root v = i := by
  classical
  simp [distanceLevelFinset]

@[simp]
theorem mem_closedBallFinset [Fintype V] (root : V) {i : ℕ} {v : V} :
    v ∈ closedBallFinset G root i ↔ G.dist root v ≤ i := by
  classical
  simp [closedBallFinset]

theorem distanceLevelFinset_disjoint [Fintype V] (root : V) {i j : ℕ}
    (hij : i ≠ j) :
    Disjoint (distanceLevelFinset G root i) (distanceLevelFinset G root j) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact hij ((mem_distanceLevelFinset root).mp hvi |>.symm.trans
    ((mem_distanceLevelFinset root).mp hvj))

theorem distanceLevelFinset_subset_closedBallFinset [Fintype V]
    (root : V) (i : ℕ) :
    distanceLevelFinset G root i ⊆ closedBallFinset G root i := by
  intro v hv
  rw [mem_closedBallFinset]
  exact ((mem_distanceLevelFinset root).mp hv).le

theorem closedBallFinset_mono [Fintype V] (root : V) {i j : ℕ}
    (hij : i ≤ j) :
    closedBallFinset G root i ⊆ closedBallFinset G root j := by
  intro v hv
  rw [mem_closedBallFinset] at hv ⊢
  exact hv.trans hij

/-- A closed ball grows by adjoining the next distance level. -/
theorem closedBallFinset_succ [Fintype V] [DecidableEq V] (root : V) (i : ℕ) :
    closedBallFinset G root (i + 1) =
      closedBallFinset G root i ∪ distanceLevelFinset G root (i + 1) := by
  classical
  ext v
  simp only [mem_closedBallFinset, mem_union, mem_distanceLevelFinset]
  omega

theorem closedBallFinset_disjoint_nextLevel [Fintype V] [DecidableEq V]
    (root : V) (i : ℕ) :
    Disjoint (closedBallFinset G root i) (distanceLevelFinset G root (i + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvB hvL
  rw [mem_closedBallFinset] at hvB
  rw [mem_distanceLevelFinset] at hvL
  omega

theorem card_closedBallFinset_succ [Fintype V] [DecidableEq V] (root : V) (i : ℕ) :
    #(closedBallFinset G root (i + 1)) =
      #(closedBallFinset G root i) + #(distanceLevelFinset G root (i + 1)) := by
  rw [closedBallFinset_succ, Finset.card_union_of_disjoint
    (closedBallFinset_disjoint_nextLevel root i)]

/-- In a connected graph the zero-th level is exactly the root. -/
theorem distanceLevelFinset_zero (hG : G.Connected) [Fintype V] (root : V) :
    distanceLevelFinset G root 0 = {root} := by
  classical
  ext v
  simp only [mem_distanceLevelFinset, mem_singleton]
  simpa [eq_comm] using (hG.dist_eq_zero_iff (u := root) (v := v))

theorem closedBallFinset_zero (hG : G.Connected) [Fintype V] (root : V) :
    closedBallFinset G root 0 = {root} := by
  classical
  ext v
  simp only [mem_closedBallFinset, Nat.le_zero, mem_singleton]
  simpa [eq_comm] using (hG.dist_eq_zero_iff (u := root) (v := v))

/-- The radius-one BFS ball is the root together with all its neighbours. -/
theorem closedBallFinset_one (hG : G.Connected) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (root : V) :
    closedBallFinset G root 1 = insert root (G.neighborFinset root) := by
  ext v
  simp only [mem_closedBallFinset, mem_insert, mem_neighborFinset]
  constructor
  · intro hv
    have hcases : G.dist root v = 0 ∨ G.dist root v = 1 := by omega
    rcases hcases with hzero | hone
    · exact Or.inl ((hG.dist_eq_zero_iff (u := root) (v := v)).mp hzero).symm
    · exact Or.inr (G.dist_eq_one_iff_adj.mp hone)
  · rintro (rfl | hv)
    · simp
    · rw [G.dist_eq_one_iff_adj.mpr hv]

theorem card_closedBallFinset_one (hG : G.Connected) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (root : V) :
    #(closedBallFinset G root 1) = G.degree root + 1 := by
  rw [closedBallFinset_one hG root,
    Finset.card_insert_of_notMem (G.notMem_neighborFinset_self root),
    G.card_neighborFinset_eq_degree, Nat.add_comm]

/-- Adjacent vertices occupy the same or consecutive distance levels. -/
theorem adj_distanceLevel_cases [Fintype V] (root : V) {v w : V} {i j : ℕ}
    (hv : v ∈ distanceLevelFinset G root i)
    (hw : w ∈ distanceLevelFinset G root j)
    (hvw : G.Adj v w) :
    j = i ∨ j = i + 1 ∨ j = i - 1 := by
  have h := hvw.diff_dist_adj (u := root)
  rw [mem_distanceLevelFinset] at hv hw
  simpa [hv, hw] using
    (show G.dist root w = G.dist root v ∨
        G.dist root w = G.dist root v + 1 ∨
        G.dist root w = G.dist root v - 1 from h)

/-- In a connected bipartite graph, two vertices at the same distance from a
root cannot be adjacent.  This is the parity fact behind the exact
consecutive-level edge decomposition in a BFS. -/
theorem not_adj_of_dist_eq_of_bipartite (hbip : G.IsBipartite)
    (hG : G.Connected) {root v w : V} (hdist : G.dist root v = G.dist root w) :
    ¬ G.Adj v w := by
  intro hvw
  let cFin : G.Coloring (Fin 2) := Classical.choice hbip
  let c : G.Coloring Bool := recolorOfEquiv G finTwoEquiv cFin
  obtain ⟨pv, hpv⟩ := (hG root v).exists_walk_length_eq_dist
  obtain ⟨pw, hpw⟩ := (hG root w).exists_walk_length_eq_dist
  have hparity : Even pv.length ↔ Even pw.length := by
    rw [hpv, hpw, hdist]
  have hcroot : (c root ↔ c v) ↔ (c root ↔ c w) := by
    rw [← c.even_length_iff_congr pv, ← c.even_length_iff_congr pw]
    exact hparity
  have hvw_iff : c v ↔ c w := by
    tauto
  exact c.valid hvw (Bool.eq_iff_iff.mpr hvw_iff)

/-- Hence adjacent vertices of a connected bipartite graph lie in consecutive
distance levels. -/
theorem adj_distanceLevel_consecutive_of_bipartite (hbip : G.IsBipartite)
    (hG : G.Connected) [Fintype V] (root : V) {v w : V} {i j : ℕ}
    (hv : v ∈ distanceLevelFinset G root i)
    (hw : w ∈ distanceLevelFinset G root j)
    (hvw : G.Adj v w) :
    j = i + 1 ∨ i = j + 1 := by
  have hne : j ≠ i := by
    intro hji
    have hdist : G.dist root v = G.dist root w := by
      rw [(mem_distanceLevelFinset root).mp hv,
        (mem_distanceLevelFinset root).mp hw, hji]
    exact (not_adj_of_dist_eq_of_bipartite hbip hG hdist) hvw
  rcases adj_distanceLevel_cases root hv hw hvw with h | h | h
  · exact (hne h).elim
  · exact Or.inl h
  · right
    have hi : 0 < i := by
      by_contra hi0
      have : i = 0 := Nat.eq_zero_of_not_pos hi0
      omega
    omega

/-- Every neighbour of the radius-`i` closed ball lies in the
radius-`i+1` closed ball. -/
theorem adj_mem_closedBallFinset_succ [Fintype V] (root : V) {v w : V} {i : ℕ}
    (hv : v ∈ closedBallFinset G root i) (hvw : G.Adj v w) :
    w ∈ closedBallFinset G root (i + 1) := by
  rw [mem_closedBallFinset] at hv ⊢
  rcases hvw.diff_dist_adj (u := root) with h | h | h <;> omega

/-- A shortest path in a finite connected graph has fewer vertices than the
ambient vertex type, hence every graph distance is strictly below that
cardinality. -/
theorem connected_dist_lt_card (hG : G.Connected) [Fintype V] (root v : V) :
    G.dist root v < Fintype.card V := by
  obtain ⟨p, hp⟩ := (hG root v).exists_walk_length_eq_dist
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  simpa [hp] using hpath.length_lt

/-- By radius `|V|`, the finite connected BFS ball contains every vertex. -/
theorem closedBallFinset_card_eq_univ (hG : G.Connected) [Fintype V] (root : V) :
    closedBallFinset G root (Fintype.card V) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro v
  rw [mem_closedBallFinset]
  exact (connected_dist_lt_card hG root v).le

end LeanCo.SizeRamsey
