import LeanCo.SizeRamsey.BFSBranches
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Graph copies supported on two consecutive BFS levels

These lemmas isolate the elementary bipartite facts used in Claims 3.4 and
3.5: every copied edge crosses the two levels, the lower side has at least
two vertices under minimum degree three, and even copied walks return to the
same level.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u v

variable {V : Type u} {W : Type v}
  {G : SimpleGraph V} {F : SimpleGraph W}

/-- Vertices of `F` whose images lie on the lower of two BFS levels. -/
noncomputable def copyLowerLevelFinset [Fintype W]
    (f : F.Copy G) (root : V) (level : Nat) : Finset W :=
  Finset.univ.filter fun x ↦ G.dist root (f x) = level

@[simp]
theorem mem_copyLowerLevelFinset [Fintype W]
    (f : F.Copy G) (root : V) (level : Nat) (x : W) :
    x ∈ copyLowerLevelFinset f root level ↔
      G.dist root (f x) = level := by
  classical
  simp [copyLowerLevelFinset]

/-- A copied edge supported on two consecutive levels has one endpoint on
each level. -/
theorem adjacent_copy_levels_cross
    (hbip : G.IsBipartite) (hG : G.Connected)
    (f : F.Copy G) (root : V) {level : Nat} {x y : W}
    (hlevels : ∀ z : W,
      G.dist root (f z) = level ∨ G.dist root (f z) = level + 1)
    (hxy : F.Adj x y) :
    (G.dist root (f x) = level ∧ G.dist root (f y) = level + 1) ∨
      (G.dist root (f x) = level + 1 ∧ G.dist root (f y) = level) := by
  have hfxy : G.Adj (f x) (f y) := f.toHom.map_adj hxy
  rcases hlevels x with hx | hx <;>
    rcases hlevels y with hy | hy
  · exact (not_adj_of_dist_eq_of_bipartite hbip hG (hx.trans hy.symm) hfxy).elim
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact (not_adj_of_dist_eq_of_bipartite hbip hG (hx.trans hy.symm) hfxy).elim

/-- Every neighbour of an upper-level vertex lies on the lower level. -/
theorem neighborFinset_subset_copyLowerLevelFinset
    [Fintype W] [DecidableEq W] [DecidableRel F.Adj]
    (hbip : G.IsBipartite) (hG : G.Connected)
    (f : F.Copy G) (root : V) {level : Nat}
    (hlevels : ∀ z : W,
      G.dist root (f z) = level ∨ G.dist root (f z) = level + 1)
    {x : W} (hx : G.dist root (f x) = level + 1) :
    F.neighborFinset x ⊆ copyLowerLevelFinset f root level := by
  intro y hy
  rw [mem_copyLowerLevelFinset]
  have hxy : F.Adj x y := (F.mem_neighborFinset x y).mp hy
  rcases adjacent_copy_levels_cross hbip hG f root hlevels hxy with h | h
  · omega
  · exact h.2

/-- Minimum degree three forces at least two vertices on the lower level. -/
theorem two_le_card_copyLowerLevelFinset
    [Fintype W] [Nonempty W] [DecidableEq W] [DecidableRel F.Adj]
    (hbip : G.IsBipartite) (hG : G.Connected)
    (f : F.Copy G) (root : V) {level : Nat}
    (hlevels : ∀ z : W,
      G.dist root (f z) = level ∨ G.dist root (f z) = level + 1)
    (hmin : ∀ x : W, 3 ≤ F.degree x) :
    2 ≤ (copyLowerLevelFinset f root level).card := by
  let x : W := Classical.choice ‹Nonempty W›
  have hxcard : 0 < (F.neighborFinset x).card := by
    rw [F.card_neighborFinset_eq_degree]
    exact (hmin x).trans_lt' (by omega)
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hxcard
  have hxy : F.Adj x y := (F.mem_neighborFinset x y).mp hy
  rcases adjacent_copy_levels_cross hbip hG f root hlevels hxy with h | h
  · have hsub := neighborFinset_subset_copyLowerLevelFinset
      hbip hG f root hlevels h.2
    have hcard := Finset.card_le_card hsub
    rw [F.card_neighborFinset_eq_degree] at hcard
    exact (hmin y).trans hcard |>.trans' (by omega)
  · have hsub := neighborFinset_subset_copyLowerLevelFinset
      hbip hG f root hlevels h.1
    have hcard := Finset.card_le_card hsub
    rw [F.card_neighborFinset_eq_degree] at hcard
    exact (hmin x).trans hcard |>.trans' (by omega)

/-- The deepest-common-branch selection transported through an injective
copy of a graph supported on two BFS levels. -/
theorem exists_copy_deepest_common_branches
    [Fintype W] [Nonempty W] [DecidableEq V] [DecidableEq W]
    [DecidableRel F.Adj]
    (hbip : G.IsBipartite) (hG : G.Connected)
    (f : F.Copy G) (root : V) {level : Nat}
    (hlevels : ∀ z : W,
      G.dist root (f z) = level ∨ G.dist root (f z) = level + 1)
    (hmin : ∀ x : W, 3 ≤ F.degree x)
    (T : BFSParentSystem G root) :
    ∃ depth z u₀ u₁,
      depth < level ∧
      u₀ ∈ copyLowerLevelFinset f root level ∧
      u₁ ∈ copyLowerLevelFinset f root level ∧
      (∀ x ∈ copyLowerLevelFinset f root level,
        T.ancestorAtLevel level depth (f x) = z) ∧
      T.ancestorAtLevel level (depth + 1) (f u₀) ≠
        T.ancestorAtLevel level (depth + 1) (f u₁) := by
  classical
  let U := copyLowerLevelFinset f root level
  let I : Finset V := U.image f
  have hUcard : 2 ≤ U.card :=
    two_le_card_copyLowerLevelFinset hbip hG f root hlevels hmin
  have hIcard : 2 ≤ I.card := by
    dsimp only [I]
    have hinj : Function.Injective (fun x ↦ f x) := f.injective
    rw [Finset.card_image_of_injective U hinj]
    exact hUcard
  have hIlevel : ∀ v ∈ I, G.dist root v = level := by
    intro v hv
    change v ∈ U.image f at hv
    rw [Finset.mem_image] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact (mem_copyLowerLevelFinset f root level x).mp hx
  obtain ⟨depth, z, v₀, v₁, hdepth, hv₀, hv₁, hz, hchildren⟩ :=
    T.exists_deepest_common_branches hG I level hIcard hIlevel
  change v₀ ∈ U.image f at hv₀
  change v₁ ∈ U.image f at hv₁
  rw [Finset.mem_image] at hv₀ hv₁
  obtain ⟨u₀, hu₀, rfl⟩ := hv₀
  obtain ⟨u₁, hu₁, rfl⟩ := hv₁
  refine ⟨depth, z, u₀, u₁, hdepth, hu₀, hu₁, ?_, hchildren⟩
  intro x hx
  apply hz (f x)
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- The lower-level vertices entering the same selected child branch as
`pivot`. -/
def copyBranchSet [Fintype W]
    (T : BFSParentSystem G root) (f : F.Copy G)
    (level depth : Nat) (pivot : W) : Set W :=
  {x | x ∈ copyLowerLevelFinset f root level ∧
    T.ancestorAtLevel level (depth + 1) (f x) =
      T.ancestorAtLevel level (depth + 1) (f pivot)}

/-- The selected branch and its complement are nonempty, and they are not a
bipartition of the copied graph.  The witness is an edge from a lower vertex
in another branch to an upper-level neighbour, both of which lie in the
complement. -/
theorem copyBranchSet_nontrivial_not_bipartite
    [Fintype W] [DecidableEq W] [DecidableRel F.Adj]
    (hbip : G.IsBipartite) (hG : G.Connected)
    (f : F.Copy G) (root : V) {level depth : Nat}
    (hlevels : ∀ z : W,
      G.dist root (f z) = level ∨ G.dist root (f z) = level + 1)
    (T : BFSParentSystem G root) {pivot other : W}
    (hpivot : pivot ∈ copyLowerLevelFinset f root level)
    (hother : other ∈ copyLowerLevelFinset f root level)
    (hchildren : T.ancestorAtLevel level (depth + 1) (f pivot) ≠
      T.ancestorAtLevel level (depth + 1) (f other))
    (hdeg : 1 ≤ F.degree other) :
    (copyBranchSet T f level depth pivot).Nonempty ∧
      (copyBranchSet T f level depth pivot)ᶜ.Nonempty ∧
      ¬F.IsBipartiteWith (copyBranchSet T f level depth pivot)
        (copyBranchSet T f level depth pivot)ᶜ := by
  classical
  let A := copyBranchSet T f level depth pivot
  have hpivotA : pivot ∈ A := by
    exact ⟨hpivot, rfl⟩
  have hotherNotA : other ∉ A := by
    intro hoA
    exact hchildren hoA.2.symm
  have hotherB : other ∈ Aᶜ := hotherNotA
  have hneighbor : (F.neighborFinset other).Nonempty := by
    rw [← Finset.card_pos, F.card_neighborFinset_eq_degree]
    omega
  obtain ⟨y, hy⟩ := hneighbor
  have hoy : F.Adj other y := (F.mem_neighborFinset other y).mp hy
  have hotherLevel : G.dist root (f other) = level :=
    (mem_copyLowerLevelFinset f root level other).mp hother
  have hyUpper : G.dist root (f y) = level + 1 := by
    rcases adjacent_copy_levels_cross hbip hG f root hlevels hoy with h | h
    · exact h.2
    · omega
  have hyNotA : y ∉ A := by
    intro hyA
    have hyLower :=
      (mem_copyLowerLevelFinset f root level y).mp hyA.1
    omega
  have hyB : y ∈ Aᶜ := hyNotA
  refine ⟨⟨pivot, hpivotA⟩, ⟨other, hotherB⟩, ?_⟩
  intro hbi
  have hyA : y ∈ A := hbi.mem_of_mem_adj' hotherB hoy.symm
  exact hyNotA hyA

/-- Membership in the lower level is a proper Boolean two-colouring of a
copy supported on two consecutive BFS levels. -/
noncomputable def copyLowerLevelColoring [Fintype W]
    (hbip : G.IsBipartite) (hG : G.Connected)
    (f : F.Copy G) (root : V) (level : Nat)
    (hlevels : ∀ z : W,
      G.dist root (f z) = level ∨ G.dist root (f z) = level + 1) :
    F.Coloring Bool := by
  classical
  apply Coloring.mk (fun x ↦ decide (G.dist root (f x) = level))
  intro x y hxy
  rcases adjacent_copy_levels_cross hbip hG f root hlevels hxy with h | h
  · simp [h.1, h.2]
  · simp [h.1, h.2]

/-- An even walk in the copied two-level graph has endpoints on the same BFS
level. -/
theorem lowerLevel_iff_of_even_walk [Fintype W]
    (hbip : G.IsBipartite) (hG : G.Connected)
    (f : F.Copy G) (root : V) {level : Nat}
    (hlevels : ∀ z : W,
      G.dist root (f z) = level ∨ G.dist root (f z) = level + 1)
    {x y : W} (p : F.Walk x y) (heven : Even p.length) :
    G.dist root (f x) = level ↔ G.dist root (f y) = level := by
  classical
  let c := copyLowerLevelColoring hbip hG f root level hlevels
  have hsame := (c.even_length_iff_congr p).mp heven
  dsimp only [c, copyLowerLevelColoring, Coloring.mk] at hsame
  change (decide (G.dist root (f x) = level) = true ↔
    decide (G.dist root (f y) = level) = true) at hsame
  simpa only [decide_eq_true_eq] using hsame

/-- After mapping a walk from the copied two-level graph into the ambient
graph, every support vertex lies at or above the lower level. -/
theorem level_le_dist_of_mem_support_map_copy
    (f : F.Copy G) (root : V) {level : Nat}
    (hlevels : ∀ z : W,
      G.dist root (f z) = level ∨ G.dist root (f z) = level + 1)
    {x y : W} (p : F.Walk x y) {z : V}
    (hz : z ∈ (p.map f.toHom).support) :
    level ≤ G.dist root z := by
  rw [Walk.support_map, List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwlevels : G.dist root (f.toHom w) = level ∨
      G.dist root (f.toHom w) = level + 1 := by
    simpa only [SimpleGraph.Copy.toHom_apply] using hlevels w
  rcases hwlevels with h | h <;> omega

end LeanCo.SizeRamsey
