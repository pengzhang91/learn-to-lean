import LeanCo.HypercubeTuran.BaseGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-!
# Excluding the acyclic case

Every finite forest is two-colourable, so one of its two colour classes is a
large independent set.  The base graphs used in the formalization forbid even
independent sets of density `1/100`; consequently they contain a cycle.  This
small bridge lets extended-girth bounds be converted to ordinary natural-number
girth bounds without adding cyclicity as a separate random-graph event.
-/

open scoped SimpleGraph

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Replace each edge of a walk by its two incidence edges in the
one-subdivision. -/
def subdivideWalk (G : SimpleGraph V) :
    ∀ {v w : V}, G.Walk v w →
      (oneSubdivision G).Walk (Sum.inl v) (Sum.inl w)
  | _, _, .nil => .nil
  | v, _, .cons (v := w) h p => by
      let e : G.edgeSet := ⟨s(v, w), h⟩
      have hve : (oneSubdivision G).Adj (Sum.inl v) (Sum.inr e) := by
        simp [e]
      have hew : (oneSubdivision G).Adj (Sum.inr e) (Sum.inl w) := by
        simp [e]
      exact .cons hve (.cons hew (subdivideWalk G p))

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem subdivideWalk_support_pole_iff (G : SimpleGraph V) {v w x : V}
    (p : G.Walk v w) :
    Sum.inl x ∈ (subdivideWalk G p).support ↔ x ∈ p.support := by
  induction p with
  | nil => simp [subdivideWalk]
  | @cons v w z h p ih =>
      simp [subdivideWalk, Walk.support_cons, ih]

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem subdivideWalk_support_edge_iff (G : SimpleGraph V) {v w : V}
    (p : G.Walk v w) (e : G.edgeSet) :
    Sum.inr e ∈ (subdivideWalk G p).support ↔ (e : Sym2 V) ∈ p.edges := by
  induction p with
  | nil => simp [subdivideWalk]
  | @cons v w z h p ih =>
      simp [subdivideWalk, Walk.support_cons, Walk.edges_cons, ih, Subtype.ext_iff]

omit [Fintype V] [DecidableEq V] in
/-- Subdivision sends a simple path to a simple path. -/
theorem subdivideWalk_isPath (G : SimpleGraph V) {v w : V}
    (p : G.Walk v w) (hp : p.IsPath) :
    (subdivideWalk G p).IsPath := by
  induction p with
  | nil => exact Walk.IsPath.nil
  | @cons v w z h p ih =>
      let e : G.edgeSet := ⟨s(v, w), h⟩
      have hpParts : p.IsPath ∧ v ∉ p.support :=
        (Walk.cons_isPath_iff h p).mp hp
      have hlift : (subdivideWalk G p).IsPath := ih hpParts.1
      have heNot : Sum.inr e ∉ (subdivideWalk G p).support := by
        rw [subdivideWalk_support_edge_iff]
        intro he
        exact hpParts.2 (p.fst_mem_support_of_mem_edges (by simpa [e] using he))
      have hew : (oneSubdivision G).Adj (Sum.inr e) (Sum.inl w) := by
        simp [e]
      have hve : (oneSubdivision G).Adj (Sum.inl v) (Sum.inr e) := by
        simp [e]
      have hinner :
          ((subdivideWalk G p).cons hew).IsPath :=
        (Walk.cons_isPath_iff hew _).mpr ⟨hlift, heNot⟩
      have houter : (((subdivideWalk G p).cons hew).cons hve).IsPath := by
        apply (Walk.cons_isPath_iff hve _).mpr
        refine ⟨hinner, ?_⟩
        simp only [Walk.support_cons, List.mem_cons, reduceCtorEq, false_or]
        simpa using hpParts.2
      simpa only [subdivideWalk] using houter

omit [Fintype V] [DecidableEq V] in
/-- Subdivision sends every cycle to a cycle. -/
theorem subdivideWalk_isCycle (G : SimpleGraph V) {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    (subdivideWalk G p).IsCycle := by
  cases p with
  | nil => exact (Walk.IsCycle.not_of_nil hp).elim
  | @cons _ w _ h q =>
      let e : G.edgeSet := ⟨s(v, w), h⟩
      have hpParts : q.IsPath ∧ s(v, w) ∉ q.edges :=
        (Walk.cons_isCycle_iff q h).mp hp
      have hlift : (subdivideWalk G q).IsPath :=
        subdivideWalk_isPath G q hpParts.1
      have heNot : Sum.inr e ∉ (subdivideWalk G q).support := by
        simpa [e] using hpParts.2
      have hew : (oneSubdivision G).Adj (Sum.inr e) (Sum.inl w) := by
        simp [e]
      have hve : (oneSubdivision G).Adj (Sum.inl v) (Sum.inr e) := by
        simp [e]
      have hinner :
          ((subdivideWalk G q).cons hew).IsPath :=
        (Walk.cons_isPath_iff hew _).mpr ⟨hlift, heNot⟩
      have houter : (((subdivideWalk G q).cons hew).cons hve).IsCycle := by
        apply (Walk.cons_isCycle_iff _ hve).mpr
        refine ⟨hinner, ?_⟩
        simp only [Walk.edges_cons, List.mem_cons, not_or]
        constructor
        · simp [e, h.ne]
        · intro hedge
          have hsupp : Sum.inr e ∈ (subdivideWalk G q).support :=
            (subdivideWalk G q).mem_support_of_mem_edges hedge (by simp)
          exact hpParts.2 ((subdivideWalk_support_edge_iff G q e).mp hsupp)
      simpa only [subdivideWalk] using houter

omit [Fintype V] [DecidableEq V] in
/-- The one-subdivision of a cyclic graph is cyclic. -/
theorem oneSubdivision_not_isAcyclic {G : SimpleGraph V}
    (hG : ¬G.IsAcyclic) : ¬(oneSubdivision G).IsAcyclic := by
  intro hS
  obtain ⟨v, p, hp, _⟩ := SimpleGraph.exists_egirth_eq_length.mpr hG
  exact hS (subdivideWalk G p) (subdivideWalk_isCycle G p hp)

/-- A finite graph on at least one vertex whose independent sets all have
density strictly below `1/100` cannot be a forest. -/
theorem not_isAcyclic_of_hasSmallIndependentSets
    (G : SimpleGraph V) (hsmall : HasSmallIndependentSets G) :
    ¬G.IsAcyclic := by
  classical
  intro hacyc
  let C : G.Coloring (Fin 2) := hacyc.coloringTwo
  let I₀ : Finset V := Finset.univ.filter fun v ↦ C v = 0
  let I₁ : Finset V := Finset.univ.filter fun v ↦ C v = 1
  have hI₀ : G.IsIndepSet (I₀ : Set V) := by
    simpa [I₀, C, Coloring.colorClass] using C.isIndepSet_colorClass (0 : Fin 2)
  have hI₁ : G.IsIndepSet (I₁ : Set V) := by
    simpa [I₁, C, Coloring.colorClass] using C.isIndepSet_colorClass (1 : Fin 2)
  have hpartition : #I₀ + #I₁ = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [I₀, I₁, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro _
        trivial
      · intro _
        have hv : (C v).val = 0 ∨ (C v).val = 1 := by omega
        rcases hv with hv | hv
        · left
          exact Fin.ext hv
        · right
          exact Fin.ext hv
    · rw [Finset.disjoint_left]
      intro v hv₀ hv₁
      simp only [I₀, I₁, Finset.mem_filter, Finset.mem_univ, true_and] at hv₀ hv₁
      omega
  have hsmall₀ := hsmall I₀ hI₀
  have hsmall₁ := hsmall I₁ hI₁
  omega

/-- Every combinatorial base graph contains a cycle. -/
theorem IsCombinatorialBase.not_isAcyclic {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hbase : IsCombinatorialBase G d) :
    ¬G.IsAcyclic :=
  not_isAcyclic_of_hasSmallIndependentSets G hbase.small_independent

/-- Every avoidance base graph contains a cycle. -/
theorem IsAvoidanceBase.not_isAcyclic {G : SimpleGraph V}
    (hbase : IsAvoidanceBase G) :
    ¬G.IsAcyclic :=
  not_isAcyclic_of_hasSmallIndependentSets G hbase.small_independent

/-- The subdivision of a combinatorial base graph also contains a cycle. -/
theorem IsCombinatorialBase.oneSubdivision_not_isAcyclic
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (hbase : IsCombinatorialBase G d) :
    ¬(oneSubdivision G).IsAcyclic :=
  LeanCo.HypercubeTuran.oneSubdivision_not_isAcyclic hbase.not_isAcyclic

/-- The subdivision of an avoidance base graph also contains a cycle. -/
theorem IsAvoidanceBase.oneSubdivision_not_isAcyclic
    {G : SimpleGraph V} (hbase : IsAvoidanceBase G) :
    ¬(oneSubdivision G).IsAcyclic :=
  LeanCo.HypercubeTuran.oneSubdivision_not_isAcyclic hbase.not_isAcyclic

omit [Fintype V] [DecidableEq V] in
/-- A natural girth lower bound follows from an extended-girth lower bound as
soon as the graph is known to contain a cycle. -/
theorem girth_ge_of_coe_le_egirth {G : SimpleGraph V} {g : ℕ}
    (hcycle : ¬G.IsAcyclic) (hegirth : (g : ℕ∞) ≤ G.egirth) :
    g ≤ G.girth := by
  simpa [SimpleGraph.girth] using
    ENat.toNat_le_toNat hegirth (SimpleGraph.egirth_eq_top.not.mpr hcycle)

/-- Package the extended-to-natural girth conversion for a combinatorial
base graph. -/
theorem IsCombinatorialBase.girth_ge {G : SimpleGraph V}
    [DecidableRel G.Adj] {d g : ℕ} (hbase : IsCombinatorialBase G d)
    (hegirth : (g : ℕ∞) ≤ G.egirth) :
    g ≤ G.girth :=
  girth_ge_of_coe_le_egirth hbase.not_isAcyclic hegirth

/-- Package the same conversion for the one-subdivision of a combinatorial
base graph. -/
theorem IsCombinatorialBase.oneSubdivision_girth_ge {G : SimpleGraph V}
    [DecidableRel G.Adj] {d g : ℕ} (hbase : IsCombinatorialBase G d)
    (hegirth : (g : ℕ∞) ≤ (oneSubdivision G).egirth) :
    g ≤ (oneSubdivision G).girth :=
  girth_ge_of_coe_le_egirth hbase.oneSubdivision_not_isAcyclic hegirth

end LeanCo.HypercubeTuran
