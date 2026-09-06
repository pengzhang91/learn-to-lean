import LeanCo.HypercubeTuran.Defs

/-!
# Girth of the one-subdivision

A trail in the one-subdivision whose endpoints are poles alternates between
poles and edge-vertices.  Removing the edge-vertices gives a trail in the
original graph, with exactly half the length.  For cycles this compression is
again a cycle.  Consequently one-subdivision doubles extended girth.
-/

open scoped SimpleGraph

namespace LeanCo.HypercubeTuran

open SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

private theorem common_edge_eq {v w : V} (e : G.edgeSet)
    (hv : v ∈ (e : Sym2 V)) (hw : w ∈ (e : Sym2 V)) (hvw : v ≠ w) :
    (e : Sym2 V) = s(v, w) := by
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hv
  have hw' : w = v ∨ w = x := by
    simpa [hx] using hw
  rcases hw' with rfl | rfl
  · exact (hvw rfl).elim
  · exact hx

private theorem adj_of_common_edge {v w : V} (e : G.edgeSet)
    (hv : v ∈ (e : Sym2 V)) (hw : w ∈ (e : Sym2 V)) (hvw : v ≠ w) :
    G.Adj v w := by
  show s(v, w) ∈ G.edgeSet
  rw [← common_edge_eq G e hv hw hvw]
  exact e.property

/-- Compress a pole-to-pole trail in the subdivision by deleting its
edge-vertices. -/
noncomputable def compressPoleTrail :
    ∀ {v w : V} (p : (oneSubdivision G).Walk (Sum.inl v) (Sum.inl w)),
      p.IsTrail → G.Walk v w
  | _, _, .nil, _ => .nil
  | v, _, .cons (v := Sum.inl x) h _, _ =>
      (not_oneSubdivision_adj_pole_pole v x h).elim
  | _, _, .cons (v := Sum.inr e) _ (.cons (v := Sum.inr f) h' _), _ =>
      (not_oneSubdivision_adj_edge_edge e f h').elim
  | v, _, .cons (v := Sum.inr e) h (.cons (v := Sum.inl x) h' q), hp => by
      have hvx : v ≠ x := by
        intro hvx
        subst x
        have hnot := (Walk.isTrail_cons h (.cons h' q)).mp hp |>.2
        apply hnot
        simp [Sym2.eq_swap]
      have hg : G.Adj v x := adj_of_common_edge G e
        ((oneSubdivision_adj_pole_edge v e).mp h)
        ((oneSubdivision_adj_edge_pole e x).mp h') hvx
      have hq : q.IsTrail :=
        Walk.IsTrail.of_cons (Walk.IsTrail.of_cons hp)
      exact .cons hg (compressPoleTrail q hq)
termination_by v w p _ => p.length
decreasing_by
  simp_wf

theorem length_compressPoleTrail {v w : V}
    (p : (oneSubdivision G).Walk (Sum.inl v) (Sum.inl w)) (hp : p.IsTrail) :
    2 * (compressPoleTrail G p hp).length = p.length := by
  fun_induction compressPoleTrail G p hp <;>
    (simp_all [Walk.length_cons] <;> omega)

private def pole? : SubdivisionVertex G → Option V
  | Sum.inl v => some v
  | Sum.inr _ => none

private theorem pole?_fiber :
    ∀ (a a' : SubdivisionVertex G) (b : V),
      b ∈ pole? G a → b ∈ pole? G a' → a = a' := by
  intro a a' b ha ha'
  cases a with
  | inr => simp [pole?] at ha
  | inl v =>
      cases a' with
      | inr => simp [pole?] at ha'
      | inl w =>
          simp [pole?] at ha ha'
          subst v
          subst w
          rfl

theorem support_compressPoleTrail {v w : V}
    (p : (oneSubdivision G).Walk (Sum.inl v) (Sum.inl w)) (hp : p.IsTrail) :
    (compressPoleTrail G p hp).support = p.support.filterMap (pole? G) := by
  fun_induction compressPoleTrail G p hp <;>
    simp_all [pole?, Walk.support_cons]

private def subdivisionEdge? : SubdivisionVertex G → Option (Sym2 V)
  | Sum.inl _ => none
  | Sum.inr e => some e.1

private theorem subdivisionEdge?_fiber :
    ∀ (a a' : SubdivisionVertex G) (b : Sym2 V),
      b ∈ subdivisionEdge? G a → b ∈ subdivisionEdge? G a' → a = a' := by
  intro a a' b ha ha'
  cases a with
  | inl => simp [subdivisionEdge?] at ha
  | inr e =>
      cases a' with
      | inl => simp [subdivisionEdge?] at ha'
      | inr f =>
          simp [subdivisionEdge?] at ha ha'
          apply congrArg Sum.inr
          apply Subtype.ext
          exact ha.trans ha'.symm

theorem edges_compressPoleTrail {v w : V}
    (p : (oneSubdivision G).Walk (Sum.inl v) (Sum.inl w)) (hp : p.IsTrail) :
    (compressPoleTrail G p hp).edges =
      p.support.filterMap (subdivisionEdge? G) := by
  fun_induction compressPoleTrail G p hp <;>
    simp_all [subdivisionEdge?, Walk.edges_cons, Walk.support_cons]
  apply Eq.symm
  apply common_edge_eq G
  · simpa only [oneSubdivision_adj_pole_edge] using
      (by assumption : (oneSubdivision G).Adj (Sum.inl _) (Sum.inr _))
  · simpa only [oneSubdivision_adj_edge_pole] using
      (by assumption : (oneSubdivision G).Adj (Sum.inr _) (Sum.inl _))
  · assumption

theorem compressPoleTrail_isTrail {v : V}
    (p : (oneSubdivision G).Walk (Sum.inl v) (Sum.inl v)) (hp : p.IsCycle) :
    (compressPoleTrail G p hp.isTrail).IsTrail := by
  constructor
  rw [edges_compressPoleTrail]
  rw [← p.cons_tail_support]
  simp only [subdivisionEdge?, List.filterMap_cons_none]
  exact hp.support_nodup.filterMap (subdivisionEdge?_fiber G)

/-- Compressing a subdivision cycle based at a pole produces a cycle of the
original graph. -/
theorem compressPoleTrail_isCycle {v : V}
    (p : (oneSubdivision G).Walk (Sum.inl v) (Sum.inl v)) (hp : p.IsCycle) :
    (compressPoleTrail G p hp.isTrail).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨compressPoleTrail_isTrail G p hp, ?_, ?_⟩
  · intro hnil
    have hzero : (compressPoleTrail G p hp.isTrail).length = 0 := by
      rw [hnil]
      rfl
    have hdouble := length_compressPoleTrail G p hp.isTrail
    have hthree := hp.three_le_length
    omega
  · rw [support_compressPoleTrail]
    rw [← p.cons_tail_support]
    simp only [pole?]
    exact hp.support_nodup.filterMap (pole?_fiber G)

private theorem two_mul_egirth_le_length_of_pole_cycle {v : V}
    (p : (oneSubdivision G).Walk (Sum.inl v) (Sum.inl v)) (hp : p.IsCycle) :
    (2 : ℕ∞) * G.egirth ≤ p.length := by
  have hcycle := compressPoleTrail_isCycle G p hp
  have hmin : G.egirth ≤ (compressPoleTrail G p hp.isTrail).length :=
    G.egirth_le_length hcycle
  calc
    (2 : ℕ∞) * G.egirth ≤
        2 * (compressPoleTrail G p hp.isTrail).length :=
      by simpa [mul_comm] using mul_le_mul_right hmin (2 : ℕ∞)
    _ = p.length := by
      norm_cast
      exact length_compressPoleTrail G p hp.isTrail

/-- One-subdivision doubles extended girth.  The statement also covers
forests: in that case both sides force the subdivision to be acyclic. -/
theorem two_mul_egirth_le_oneSubdivision_egirth :
    (2 : ℕ∞) * G.egirth ≤ (oneSubdivision G).egirth := by
  classical
  rw [SimpleGraph.le_egirth]
  intro a p hp
  cases a with
  | inl v => exact two_mul_egirth_le_length_of_pole_cycle G p hp
  | inr e =>
      cases p with
      | nil => exact (Walk.IsCycle.not_of_nil hp).elim
      | @cons _ x _ h q =>
          cases x with
          | inr f => exact (not_oneSubdivision_adj_edge_edge e f h).elim
          | inl v =>
              have hv : Sum.inl v ∈ (Walk.cons h q).support := by simp
              let c := (Walk.cons h q).rotate (Sum.inl v) hv
              have hc : c.IsCycle := hp.rotate hv
              simpa [c] using two_mul_egirth_le_length_of_pole_cycle G c hc

/-- Natural-number girth is doubled as well (with the standard value `0`
for an acyclic graph). -/
theorem two_mul_girth_le_oneSubdivision_girth
    (hS : ¬(oneSubdivision G).IsAcyclic) :
    2 * G.girth ≤ (oneSubdivision G).girth := by
  have h := ENat.toNat_le_toNat (two_mul_egirth_le_oneSubdivision_egirth G)
    (SimpleGraph.egirth_eq_top.not.mpr hS)
  simpa [SimpleGraph.girth] using h

/-- In particular, any lower bound on the base girth is preserved by
one-subdivision. -/
theorem girth_le_oneSubdivision_girth
    (hS : ¬(oneSubdivision G).IsAcyclic) :
    G.girth ≤ (oneSubdivision G).girth := by
  exact (Nat.le_mul_of_pos_left G.girth (by omega)).trans
    (two_mul_girth_le_oneSubdivision_girth G hS)

end LeanCo.HypercubeTuran
