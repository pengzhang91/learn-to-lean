import LeanCo.SizeRamsey.BFSBranches
import LeanCo.SizeRamsey.TwoLevelCore
import LeanCo.SizeRamsey.CycleGlue
import LeanCo.SizeRamsey.PathLengths

/-!
# Length adjustment inside two consecutive BFS levels

This is the graph-theoretic core of Wang--Wang Lemma 3.3.  The only input
still abstracted is the prescribed-length path theorem across a nontrivial
vertex partition.  Its oriented formulation below is exactly what is needed
after reversing an `A`--`Aᶜ` path when necessary.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u v

/-- Length adjustment from an abstract family of paths across every
nontrivial, non-bipartite complementary partition. -/
theorem exists_cycleLength_interval_of_crossPartPaths
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {F : SimpleGraph W}
    [DecidableRel F.Adj]
    (hbip : G.IsBipartite) (hG : G.Connected) (_hF : F.Connected)
    (f : F.Copy G) (root : V) {level : ℕ}
    (hlevels : ∀ x : W,
      G.dist root (f x) = level ∨ G.dist root (f x) = level + 1)
    (hmin : ∀ x : W, 3 ≤ F.degree x)
    (T : BFSParentSystem G root)
    {c₀ : W} (c : F.Walk c₀ c₀) (_hc : c.IsCycle)
    (hpaths : ∀ A : Set W, A.Nonempty → Aᶜ.Nonempty →
      ¬F.IsBipartiteWith A Aᶜ →
      ∀ s : ℕ, 1 ≤ s → s < c.length →
        ∃ x y, x ∈ A ∧ y ∈ Aᶜ ∧
          ∃ q : F.Walk x y, q.IsPath ∧ q.length = s) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ level ∧
      ∀ s : ℕ, Even s → 2 ≤ s → s ≤ c.length - 2 →
        ContainsCycleLength G (2 * r + s) := by
  letI : Nonempty W := ⟨c₀⟩
  obtain ⟨depth, z, pivot, other, hdepth, hpivot, hother,
      hcommon, hchildren⟩ :=
    exists_copy_deepest_common_branches hbip hG f root hlevels hmin T
  let A : Set W := copyBranchSet T f level depth pivot
  have hparts : A.Nonempty ∧ Aᶜ.Nonempty ∧
      ¬F.IsBipartiteWith A Aᶜ := by
    exact copyBranchSet_nontrivial_not_bipartite hbip hG f root hlevels T
      hpivot hother hchildren (by exact (hmin other).trans' (by omega))
  have hAB := hpaths A hparts.1 hparts.2.1 hparts.2.2
  refine ⟨level - depth, by omega, Nat.sub_le _ _, ?_⟩
  intro s hsEven hsTwo hsUpper
  have hsLt : s < c.length := by omega
  obtain ⟨x, y, hxA, hyA, q, hqPath, hqLength⟩ :=
    hAB s (by omega) hsLt
  have hxLowerMem : x ∈ copyLowerLevelFinset f root level := by
    exact hxA.1
  have hxLevel : G.dist root (f x) = level :=
    (mem_copyLowerLevelFinset f root level x).mp hxLowerMem
  have hqEven : Even q.length := by
    rw [hqLength]
    exact hsEven
  have hyLevel : G.dist root (f y) = level :=
    (lowerLevel_iff_of_even_walk hbip hG f root hlevels q hqEven).mp hxLevel
  have hyLowerMem : y ∈ copyLowerLevelFinset f root level :=
    (mem_copyLowerLevelFinset f root level y).mpr hyLevel
  have hchildrenXY :
      T.ancestorAtLevel level (depth + 1) (f x) ≠
        T.ancestorAtLevel level (depth + 1) (f y) := by
    intro heq
    apply hyA
    refine ⟨hyLowerMem, ?_⟩
    exact heq.symm.trans hxA.2
  obtain ⟨p, hpPath, hpLength, hpInternal⟩ :=
    T.exists_branch_path hG hdepth hxLevel hyLevel
      (hcommon x hxLowerMem) (hcommon y hyLowerMem) hchildrenXY
  let qG : G.Walk (f x) (f y) := q.map f.toHom
  have hqGPath : qG.IsPath := by
    exact Walk.map_isPath_of_injective f.injective hqPath
  have hqGLength : qG.length = s := by
    dsimp only [qG]
    rw [Walk.length_map, hqLength]
  have hqGTwo : 1 < qG.length := by omega
  have hqLevel : ∀ w ∈ qG.support, level ≤ G.dist root w := by
    intro w hw
    exact level_le_dist_of_mem_support_map_copy f root hlevels q hw
  have hcycle := containsCycleLength_add_of_levelSeparatedPaths
    hqGPath hpPath hqGTwo hqLevel hpInternal
  rw [hqGLength, hpLength] at hcycle
  simpa only [Nat.add_comm] using hcycle

/-- Wang--Wang Lemma 3.3: a connected minimum-degree-three copy supported
on two consecutive BFS levels supplies the whole stated interval of even
cycle lengths in the ambient graph. -/
theorem exists_cycleLength_interval
    {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {F : SimpleGraph W}
    [DecidableRel F.Adj]
    (hbip : G.IsBipartite) (hG : G.Connected) (hF : F.Connected)
    (f : F.Copy G) (root : V) {level : ℕ}
    (hlevels : ∀ x : W,
      G.dist root (f x) = level ∨ G.dist root (f x) = level + 1)
    (hmin : ∀ x : W, 3 ≤ F.degree x)
    (T : BFSParentSystem G root)
    {c₀ : W} (c : F.Walk c₀ c₀) (hc : c.IsCycle) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ level ∧
      ∀ s : ℕ, Even s → 2 ≤ s → s ≤ c.length - 2 →
        ContainsCycleLength G (2 * r + s) := by
  apply exists_cycleLength_interval_of_crossPartPaths hbip hG hF f root
    hlevels hmin T c hc
  intro A hA hAc hnot s hsOne hsLt
  have hp := hasABPathLengths (G := F) (A := A) (B := Aᶜ)
    hF (by simp) disjoint_compl_right hA hAc hmin hnot hc s hsOne hsLt
  obtain ⟨x, y, q, hqPath, hqLength, hxy⟩ := hp
  rcases hxy with hxy | hxy
  · exact ⟨x, y, hxy.1, hxy.2, q, hqPath, hqLength⟩
  · refine ⟨y, x, hxy.2, hxy.1, q.reverse, hqPath.reverse, ?_⟩
    simpa only [Walk.length_reverse] using hqLength

end LeanCo.SizeRamsey
