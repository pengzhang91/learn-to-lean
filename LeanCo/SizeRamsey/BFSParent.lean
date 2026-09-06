import LeanCo.SizeRamsey.BFSLevels
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-!
# A canonical parent system for breadth-first levels

The paper phrases its length-adjustment argument using a breadth-first
spanning tree.  For the proof it is enough, and technically cleaner, to keep
only the rooted parent map: every non-root vertex chooses a neighbour one
level closer to the root.  Iterating this map gives the unique branches used
in the deepest-common-ancestor argument.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Every non-root vertex in a connected graph has a neighbour exactly one
BFS level closer to the root. -/
theorem exists_bfs_predecessor (hG : G.Connected) (root v : V)
    (hv : v ≠ root) :
    ∃ w : V, G.Adj w v ∧ G.dist root w + 1 = G.dist root v := by
  obtain ⟨p, hp, hlen⟩ := hG.exists_path_of_dist root v
  have hnil : ¬p.Nil := Walk.not_nil_of_ne hv.symm
  refine ⟨p.penultimate, p.adj_penultimate hnil, ?_⟩
  have hdrop : p.dropLast.length = G.dist root p.penultimate :=
    length_eq_dist_of_subwalk hlen (Walk.isSubwalk_take p (p.length - 1))
  rw [Walk.length_dropLast, hlen] at hdrop
  have hpos : 0 < p.length := Walk.not_nil_iff_lt_length.mp hnil
  omega

/-- The parent data of a rooted breadth-first spanning tree, without
materialising the tree as a separate graph. -/
structure BFSParentSystem (G : SimpleGraph V) (root : V) where
  parent : V → V
  parent_root : parent root = root
  parent_adj : ∀ {v : V}, v ≠ root → G.Adj (parent v) v
  parent_dist : ∀ v : V, G.dist root (parent v) = G.dist root v - 1

/-- Choose one breadth-first predecessor at every vertex. -/
noncomputable def BFSParentSystem.ofConnected (hG : G.Connected) (root : V) :
    BFSParentSystem G root := by
  classical
  exact {
    parent := fun v ↦ if hv : v = root then root else
      Classical.choose (exists_bfs_predecessor hG root v hv)
    parent_root := by simp
    parent_adj := by
      intro v hv
      simp only [dif_neg hv]
      exact (Classical.choose_spec (exists_bfs_predecessor hG root v hv)).1
    parent_dist := by
      intro v
      by_cases hv : v = root
      · subst v
        simp
      · simp only [dif_neg hv]
        have hpred :=
          (Classical.choose_spec (exists_bfs_predecessor hG root v hv)).2
        omega }

namespace BFSParentSystem

variable {root : V} (T : BFSParentSystem G root)

/-- The ancestor obtained after `steps` parent moves. -/
def ancestor : Nat → V → V
  | 0, v => v
  | steps + 1, v => T.parent (ancestor steps v)

@[simp]
theorem ancestor_zero (v : V) : T.ancestor 0 v = v := rfl

@[simp]
theorem ancestor_succ (steps : Nat) (v : V) :
    T.ancestor (steps + 1) v = T.parent (T.ancestor steps v) := rfl

@[simp]
theorem ancestor_root (steps : Nat) : T.ancestor steps root = root := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [ancestor_succ, ih, T.parent_root]

/-- Each parent iteration lowers the BFS depth by one, stopping at zero. -/
theorem dist_ancestor (steps : Nat) (v : V) :
    G.dist root (T.ancestor steps v) = G.dist root v - steps := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [ancestor_succ, T.parent_dist, ih]
      omega

/-- Ancestors compose by addition of the numbers of parent moves. -/
theorem ancestor_add (a b : Nat) (v : V) :
    T.ancestor (a + b) v = T.ancestor b (T.ancestor a v) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, ancestor_succ, ancestor_succ, ih]

/-- The parent-chain walk from an ancestor down to a vertex.  The bound says
that the chain does not attempt to move above the root. -/
def ascentWalk (v : V) :
    (steps : Nat) → steps ≤ G.dist root v →
      G.Walk (T.ancestor steps v) v
  | 0, _ => Walk.nil
  | steps + 1, hsteps => by
      have hle : steps ≤ G.dist root v := by omega
      have hne : T.ancestor steps v ≠ root := by
        intro heq
        have hd := T.dist_ancestor steps v
        rw [heq] at hd
        simp at hd
        omega
      exact Walk.cons (T.parent_adj hne)
        (ascentWalk v steps hle)

@[simp]
theorem length_ascentWalk (v : V) (steps : Nat)
    (hsteps : steps ≤ G.dist root v) :
    (T.ascentWalk v steps hsteps).length = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [ascentWalk, Walk.length_cons]
      rw [ih]

/-- The `j`-th vertex of a parent-chain walk is the ancestor with
`steps-j` parent moves remaining. -/
theorem getVert_ascentWalk (v : V) (steps : Nat)
    (hsteps : steps ≤ G.dist root v) (j : Nat) (hj : j ≤ steps) :
    (T.ascentWalk v steps hsteps).getVert j =
      T.ancestor (steps - j) v := by
  induction steps generalizing j with
  | zero =>
      have : j = 0 := by omega
      subst j
      rfl
  | succ steps ih =>
      by_cases hj0 : j = 0
      · subst j
        simp only [Walk.getVert_zero, Nat.sub_zero]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        simp only [ascentWalk, Walk.getVert_cons_succ]
        have hjle : j ≤ steps := by omega
        simpa only [Nat.succ_sub_succ_eq_sub] using
          ih (by omega) j hjle

/-- The parent-chain walk has the expected shortest possible length. -/
theorem dist_ancestor_vertex (hG : G.Connected) (v : V) (steps : Nat)
    (hsteps : steps ≤ G.dist root v) :
    G.dist (T.ancestor steps v) v = steps := by
  have hupp : G.dist (T.ancestor steps v) v ≤ steps := by
    calc
      G.dist (T.ancestor steps v) v ≤
          (T.ascentWalk v steps hsteps).length :=
        SimpleGraph.dist_le (T.ascentWalk v steps hsteps)
      _ = steps := T.length_ascentWalk v steps hsteps
  have htri := hG.dist_triangle (u := root)
    (v := T.ancestor steps v) (w := v)
  rw [T.dist_ancestor] at htri
  omega

/-- Parent chains are simple shortest paths. -/
theorem isPath_ascentWalk (hG : G.Connected) (v : V) (steps : Nat)
    (hsteps : steps ≤ G.dist root v) :
    (T.ascentWalk v steps hsteps).IsPath := by
  apply Walk.isPath_of_length_eq_dist
  calc
    (T.ascentWalk v steps hsteps).length = steps :=
      T.length_ascentWalk v steps hsteps
    _ = G.dist (T.ancestor steps v) v :=
      (T.dist_ancestor_vertex hG v steps hsteps).symm

/-- Depth along a parent-chain walk increases by exactly one at each edge. -/
theorem dist_getVert_ascentWalk (v : V) (steps : Nat)
    (hsteps : steps ≤ G.dist root v) (j : Nat) (hj : j ≤ steps) :
    G.dist root ((T.ascentWalk v steps hsteps).getVert j) =
      G.dist root v - steps + j := by
  rw [T.getVert_ascentWalk v steps hsteps j hj, T.dist_ancestor]
  omega

/-- Every vertex of a parent chain other than its final endpoint lies on a
strictly lower BFS level than that endpoint. -/
theorem dist_lt_of_mem_ascentWalk_of_ne (v : V) (steps : Nat)
    (hsteps : steps ≤ G.dist root v) {x : V}
    (hx : x ∈ (T.ascentWalk v steps hsteps).support) (hxv : x ≠ v) :
    G.dist root x < G.dist root v := by
  rw [Walk.mem_support_iff_exists_getVert] at hx
  obtain ⟨j, hjx, hj⟩ := hx
  have hlen := T.length_ascentWalk v steps hsteps
  rw [hlen] at hj
  have hjne : j ≠ steps := by
    intro hjeq
    subst j
    have hend := Walk.getVert_length (T.ascentWalk v steps hsteps)
    rw [T.length_ascentWalk] at hend
    exact hxv (hjx ▸ hend)
  have hd := T.dist_getVert_ascentWalk v steps hsteps j hj
  rw [hjx] at hd
  omega

end BFSParentSystem

end LeanCo.SizeRamsey
