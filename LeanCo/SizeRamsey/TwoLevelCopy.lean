import LeanCo.SizeRamsey.TwoLevelCore
import LeanCo.SizeRamsey.BFSLocalization

/-!
# Reading levels from an induced two-level copy

The localized core is represented on nested subtype vertex types.  This
small bridge recovers the ambient BFS-level statement required by the
length-adjustment theorem from the subtype membership proof.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u v

variable {V : Type u} {W : Type v}
  {G : SimpleGraph V} {F : SimpleGraph W}

/-- A copy into the graph induced by `L_i ∪ L_{i+1}`, followed by the
canonical inclusion, has every image vertex on one of those two levels. -/
theorem copy_induce_twoLevel_levels
    [Fintype V] [DecidableEq V]
    (root : V) (level : Nat)
    (f : F.Copy
      (G.induce ((twoLevelFinset G root level : Finset V) : Set V))) :
    let fG : F.Copy G :=
      (SimpleGraph.Copy.induce G
        ((twoLevelFinset G root level : Finset V) : Set V)).comp f
    ∀ x : W,
      G.dist root (fG x) = level ∨
        G.dist root (fG x) = level + 1 := by
  classical
  dsimp only
  intro x
  have hx := (f x).property
  change (f x).val ∈ twoLevelFinset G root level at hx
  change (f x).val ∈
    distanceLevelFinset G root level ∪
      distanceLevelFinset G root (level + 1) at hx
  rw [Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact Or.inl ((mem_distanceLevelFinset root).mp hx)
  · exact Or.inr ((mem_distanceLevelFinset root).mp hx)

end LeanCo.SizeRamsey
