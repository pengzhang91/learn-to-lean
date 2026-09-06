import LeanCo.SizeRamsey.GraphBasics

/-!
# Gluing level-separated paths into a cycle

The length-adjustment argument joins a path contained in two consecutive BFS
levels to a second path whose internal vertices lie strictly below those
levels.  This module packages the walk-level simplicity check.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The starting vertex of a simple path does not occur in the tail of its
support. -/
theorem start_not_mem_support_tail_of_isPath {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) : u ∉ p.support.tail := by
  have hnodup := hp.support_nodup
  rw [← p.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1

/-- A path living at or above `level` and a return path whose internal
vertices live below `level` form a simple cycle. -/
theorem containsCycleLength_add_of_levelSeparatedPaths
    {root u w : V} {q p : G.Walk u w} {level : Nat}
    (hq : q.IsPath) (hp : p.IsPath) (hqlen : 1 < q.length)
    (hqlevel : ∀ x ∈ q.support, level ≤ G.dist root x)
    (hpinternal : ∀ x ∈ p.support, x ≠ u → x ≠ w →
      G.dist root x < level) :
    ContainsCycleLength G (q.length + p.length) := by
  have hqstart : u ∉ q.support.tail :=
    start_not_mem_support_tail_of_isPath hq
  have hprevstart : w ∉ p.reverse.support.tail :=
    start_not_mem_support_tail_of_isPath hp.reverse
  have hdisj : q.support.tail.Disjoint p.reverse.support.tail := by
    rw [List.disjoint_left]
    intro x hxq hxp
    have hxqSupport : x ∈ q.support := List.mem_of_mem_tail hxq
    have hxpSupport : x ∈ p.support := by
      have : x ∈ p.reverse.support := List.mem_of_mem_tail hxp
      simpa only [Walk.support_reverse, List.mem_reverse] using this
    have hxu : x ≠ u := by
      intro hxu
      subst x
      exact hqstart hxq
    have hxw : x ≠ w := by
      intro hxw
      subst x
      exact hprevstart hxp
    have hlower := hqlevel x hxqSupport
    have hupper := hpinternal x hxpSupport hxu hxw
    omega
  let c : G.Walk u u := q.append p.reverse
  have hc : c.IsCycle := by
    dsimp only [c]
    exact hq.isCycle_append hp.reverse hdisj (Or.inl hqlen)
  refine ⟨u, c, hc, ?_⟩
  dsimp only [c]
  rw [Walk.length_append, Walk.length_reverse]

end LeanCo.SizeRamsey
