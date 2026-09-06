import LeanCo.SizeRamsey.BFSParent

/-!
# Deepest common branches in a breadth-first parent system

This is the finite combinatorial choice at the heart of Wang--Wang Lemma 3.3.
For at least two vertices on one BFS level, it selects their deepest common
ancestor and two vertices which enter distinct child branches immediately
below it.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {root : V}

namespace BFSParentSystem

variable (T : BFSParentSystem G root)

/-- The ancestor of a level-`level` vertex which lies at `depth`. -/
def ancestorAtLevel (level depth : Nat) (v : V) : V :=
  T.ancestor (level - depth) v

/-- All vertices of `U` have the same ancestor at the displayed depth. -/
def CommonAtLevel (U : Finset V) (level depth : Nat) : Prop :=
  ∃ z : V, ∀ v ∈ U, T.ancestorAtLevel level depth v = z

/-- Every family contained in one BFS level has the root as a common
ancestor at depth zero. -/
theorem commonAtLevel_zero (hG : G.Connected) (U : Finset V) (level : Nat)
    (hlevel : ∀ v ∈ U, G.dist root v = level) :
    T.CommonAtLevel U level 0 := by
  refine ⟨root, ?_⟩
  intro v hv
  have hd := T.dist_ancestor level v
  rw [hlevel v hv] at hd
  simp only [Nat.sub_self] at hd
  exact ((hG.dist_eq_zero_iff (u := root)
    (v := T.ancestor level v)).mp hd).symm

/-- A common ancestor at one depth remains common at every shallower depth. -/
theorem CommonAtLevel.mono {U : Finset V} {level shallow deep : Nat}
    (hshallow : shallow ≤ deep) (hdeep : deep ≤ level)
    (h : T.CommonAtLevel U level deep) :
    T.CommonAtLevel U level shallow := by
  obtain ⟨z, hz⟩ := h
  refine ⟨T.ancestor (deep - shallow) z, ?_⟩
  intro v hv
  have harith : level - shallow = (level - deep) + (deep - shallow) := by
    omega
  rw [ancestorAtLevel, harith, T.ancestor_add]
  apply congrArg (T.ancestor (deep - shallow))
  simpa only [ancestorAtLevel] using hz v hv

/-- Equality of two branch positions propagates toward the root. -/
theorem ancestorAtLevel_eq_of_le {level shallow deep : Nat} {u v : V}
    (hshallow : shallow ≤ deep) (hdeep : deep ≤ level)
    (h : T.ancestorAtLevel level deep u =
      T.ancestorAtLevel level deep v) :
    T.ancestorAtLevel level shallow u =
      T.ancestorAtLevel level shallow v := by
  have harith : level - shallow = (level - deep) + (deep - shallow) := by
    omega
  simp only [ancestorAtLevel, harith, T.ancestor_add]
  exact congrArg (T.ancestor (deep - shallow)) h

/-- At the level itself, commonality would force the finite set to have at
most one element. -/
theorem not_commonAtLevel_self {U : Finset V} {level : Nat}
    (hcard : 2 ≤ U.card) :
    ¬T.CommonAtLevel U level level := by
  intro h
  obtain ⟨z, hz⟩ := h
  have hone : U.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro a b ha hb
    have ha' := hz a ha
    have hb' := hz b hb
    simp only [ancestorAtLevel, Nat.sub_self, ancestor_zero] at ha' hb'
    exact ha'.trans hb'.symm
  omega

/-- A finite family of at least two vertices on one BFS level has a deepest
common ancestor, and immediately below it at least two distinct child
branches meet the family. -/
theorem exists_deepest_common_branches [DecidableEq V]
    (hG : G.Connected) (U : Finset V) (level : Nat)
    (hcard : 2 ≤ U.card)
    (hlevel : ∀ v ∈ U, G.dist root v = level) :
    ∃ depth z u₀ u₁,
      depth < level ∧ u₀ ∈ U ∧ u₁ ∈ U ∧
      (∀ v ∈ U, T.ancestorAtLevel level depth v = z) ∧
      T.ancestorAtLevel level (depth + 1) u₀ ≠
        T.ancestorAtLevel level (depth + 1) u₁ := by
  classical
  let P : Nat → Prop := fun depth ↦ T.CommonAtLevel U level depth
  let depth := Nat.findGreatest P level
  have hzero : P 0 := T.commonAtLevel_zero hG U level hlevel
  have hdepth : P depth :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le level) hzero
  have hdepth_le : depth ≤ level := Nat.findGreatest_le level
  have hnot_top : ¬P level := T.not_commonAtLevel_self hcard
  have hdepth_lt : depth < level := lt_of_le_of_ne hdepth_le fun heq ↦ by
    apply hnot_top
    simpa [heq] using hdepth
  have hnot_next : ¬P (depth + 1) :=
    Nat.findGreatest_is_greatest (P := P) (n := level)
      (by dsimp only [depth]; omega) (by omega)
  obtain ⟨z, hz⟩ := hdepth
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u₀, hu₀⟩ := hUne
  have hdiff : ∃ u₁ ∈ U,
      T.ancestorAtLevel level (depth + 1) u₀ ≠
        T.ancestorAtLevel level (depth + 1) u₁ := by
    by_contra hnone
    push Not at hnone
    apply hnot_next
    refine ⟨T.ancestorAtLevel level (depth + 1) u₀, ?_⟩
    intro v hv
    exact (hnone v hv).symm
  obtain ⟨u₁, hu₁, hchildren⟩ := hdiff
  exact ⟨depth, z, u₀, u₁, hdepth_lt, hu₀, hu₁, hz, hchildren⟩

/-- Parent chains entering distinct child branches below a common ancestor
meet only at that common ancestor. -/
theorem eq_commonAncestor_of_mem_ascentWalk_support
    {level depth : Nat} {z u w x : V}
    (hdepth : depth < level)
    (hulevel : G.dist root u = level)
    (hwlevel : G.dist root w = level)
    (hucommon : T.ancestorAtLevel level depth u = z)
    (_hwcommon : T.ancestorAtLevel level depth w = z)
    (hchildren : T.ancestorAtLevel level (depth + 1) u ≠
      T.ancestorAtLevel level (depth + 1) w)
    (hru : level - depth ≤ G.dist root u)
    (hrw : level - depth ≤ G.dist root w)
    (hxu : x ∈ (T.ascentWalk u (level - depth) hru).support)
    (hxw : x ∈ (T.ascentWalk w (level - depth) hrw).support) :
    x = z := by
  rw [Walk.mem_support_iff_exists_getVert] at hxu hxw
  obtain ⟨a, hax, ha⟩ := hxu
  obtain ⟨b, hbx, hb⟩ := hxw
  have hlenu := T.length_ascentWalk u (level - depth) hru
  have hlenw := T.length_ascentWalk w (level - depth) hrw
  rw [hlenu] at ha
  rw [hlenw] at hb
  have hda := T.dist_getVert_ascentWalk
    u (level - depth) hru a ha
  have hdb := T.dist_getVert_ascentWalk
    w (level - depth) hrw b hb
  rw [hax, hulevel] at hda
  rw [hbx, hwlevel] at hdb
  have hab : a = b := by omega
  subst b
  by_cases ha0 : a = 0
  · subst a
    have huz : T.ancestor (level - depth) u = z := by
      simpa only [ancestorAtLevel] using hucommon
    have hux : T.ancestor (level - depth) u = x := by
      simpa only [Walk.getVert_zero] using hax
    exact hux.symm.trans huz
  · exfalso
    have hadeep : depth + a ≤ level := by omega
    have hu_deep : T.ancestorAtLevel level (depth + a) u = x := by
      rw [ancestorAtLevel]
      have harith : level - (depth + a) = level - depth - a := by
        omega
      rw [harith]
      exact (T.getVert_ascentWalk
        u (level - depth) hru a ha).symm.trans hax
    have hw_deep : T.ancestorAtLevel level (depth + a) w = x := by
      rw [ancestorAtLevel]
      have harith : level - (depth + a) = level - depth - a := by
        omega
      rw [harith]
      exact (T.getVert_ascentWalk
        w (level - depth) hrw a hb).symm.trans hbx
    apply hchildren
    apply T.ancestorAtLevel_eq_of_le (deep := depth + a)
      (by omega) hadeep
    exact hu_deep.trans hw_deep.symm

/-- Two vertices in distinct child branches are joined through their common
ancestor by a simple path of length twice the remaining BFS depth.  Every
internal vertex of this path lies strictly below their common endpoint
level. -/
theorem exists_branch_path (hG : G.Connected)
    {level depth : Nat} {z u w : V}
    (hdepth : depth < level)
    (hulevel : G.dist root u = level)
    (hwlevel : G.dist root w = level)
    (hucommon : T.ancestorAtLevel level depth u = z)
    (hwcommon : T.ancestorAtLevel level depth w = z)
    (hchildren : T.ancestorAtLevel level (depth + 1) u ≠
      T.ancestorAtLevel level (depth + 1) w) :
    ∃ p : G.Walk u w,
      p.IsPath ∧ p.length = 2 * (level - depth) ∧
      ∀ x ∈ p.support, x ≠ u → x ≠ w → G.dist root x < level := by
  let r := level - depth
  have hru : r ≤ G.dist root u := by
    dsimp only [r]
    rw [hulevel]
    omega
  have hrw : r ≤ G.dist root w := by
    dsimp only [r]
    rw [hwlevel]
    omega
  let pu := T.ascentWalk u r hru
  let pw := T.ascentWalk w r hrw
  have hstartu : T.ancestor r u = z := by
    simpa only [r, ancestorAtLevel] using hucommon
  have hstartw : T.ancestor r w = z := by
    simpa only [r, ancestorAtLevel] using hwcommon
  have hstart : T.ancestor r w = T.ancestor r u :=
    hstartw.trans hstartu.symm
  let pw' : G.Walk (T.ancestor r u) w := pw.copy hstart rfl
  let p : G.Walk u w := pu.reverse.append pw'
  have hpuPath : pu.IsPath := by
    exact T.isPath_ascentWalk hG u r hru
  have hpwPath : pw.IsPath := by
    exact T.isPath_ascentWalk hG w r hrw
  have hpw'Path : pw'.IsPath := by
    rw [Walk.isPath_def]
    dsimp only [pw']
    rw [Walk.support_copy]
    exact hpwPath.support_nodup
  have hznot : z ∉ pw'.support.tail := by
    have hnodup := hpw'Path.support_nodup
    have hcons : z :: pw'.support.tail = pw'.support := by
      calc
        z :: pw'.support.tail = T.ancestor r u :: pw'.support.tail := by
          congr 1
          exact hstartu.symm
        _ = pw'.support := pw'.cons_tail_support
    rw [← hcons] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hdisj : pu.reverse.support.Disjoint pw'.support.tail := by
    rw [List.disjoint_left]
    intro x hxu hxw
    have hxu' : x ∈ pu.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hxu
    have hxw' : x ∈ pw.support := by
      have hxwSupport : x ∈ pw'.support := List.mem_of_mem_tail hxw
      simpa only [pw', Walk.support_copy] using hxwSupport
    have hxz := T.eq_commonAncestor_of_mem_ascentWalk_support
      hdepth hulevel hwlevel hucommon hwcommon hchildren hru hrw hxu' hxw'
    subst x
    exact hznot hxw
  have hpPath : p.IsPath := by
    dsimp only [p]
    rw [Walk.isPath_def, Walk.support_append]
    exact hpuPath.reverse.support_nodup.append hpw'Path.support_nodup.tail hdisj
  refine ⟨p, hpPath, ?_, ?_⟩
  · dsimp only [p]
    rw [Walk.length_append, Walk.length_reverse, Walk.length_copy,
      T.length_ascentWalk, T.length_ascentWalk]
    omega
  · intro x hxp hxu hxw
    dsimp only [p] at hxp
    rw [Walk.mem_support_append_iff] at hxp
    rcases hxp with hxp | hxp
    · have hxpu : x ∈ pu.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hxp
      have hlt := T.dist_lt_of_mem_ascentWalk_of_ne u r hru hxpu hxu
      simpa only [hulevel] using hlt
    · have hxpw : x ∈ pw.support := by
        simpa only [pw', Walk.support_copy] using hxp
      have hlt := T.dist_lt_of_mem_ascentWalk_of_ne w r hrw hxpw hxw
      simpa only [hwlevel] using hlt

end BFSParentSystem

end LeanCo.SizeRamsey
