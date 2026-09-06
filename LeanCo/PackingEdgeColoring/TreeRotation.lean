import LeanCo.PackingEdgeColoring.BridgeComponents

/-!
# Facial cycles of a tree rotation

Every rotation system on a nontrivial finite tree has exactly one facial
cycle.  The proof is purely combinatorial: every edge of a tree is a bridge,
so its two darts lie on one face; the local cyclic orders and connectedness
then put every dart in that same facial orbit.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Across a bridge, a facial orbit also contains the next dart in the local
rotation. -/
theorem sameCycle_faceStep_rotation_of_isBridge
    (R : RotationSystem G) (d : G.Dart) (hbridge : G.IsBridge d.edge) :
    R.faceStep.SameCycle d (R.rotation d) := by
  have h₁ := R.sameCycle_faceStep_of_isBridge d hbridge
  have h₂ : R.faceStep.SameCycle d.symm (R.faceStep d.symm) :=
    Equiv.Perm.sameCycle_apply_right.mpr
      (Equiv.Perm.SameCycle.refl R.faceStep d.symm)
  exact h₁.trans (by simpa only [faceStep_apply, Dart.symm_symm] using h₂)

/-- If every edge is a bridge, outgoing darts at one vertex belong to one
facial orbit. -/
theorem sameCycle_faceStep_of_same_fst_of_all_isBridge
    (R : RotationSystem G)
    (hbridge : ∀ d : G.Dart, G.IsBridge d.edge)
    (d e : G.Dart) (hde : d.fst = e.fst) :
    R.faceStep.SameCycle d e := by
  have hrot : R.rotation.SameCycle d e :=
    (R.rotation_sameCycle_iff_fst_eq d e).mpr hde
  obtain ⟨n, -, hn⟩ := hrot.exists_pow_eq'
  have hp : ∀ n : ℕ, R.faceStep.SameCycle d ((R.rotation ^ n) d) := by
    intro n
    induction n with
    | zero => simpa using Equiv.Perm.SameCycle.refl R.faceStep d
    | succ n ih =>
        have hs := R.sameCycle_faceStep_rotation_of_isBridge
          ((R.rotation ^ n) d) (hbridge ((R.rotation ^ n) d))
        exact ih.trans (by
          simpa only [pow_succ', Equiv.Perm.mul_apply] using hs)
  rw [← hn]
  exact hp n

/-- If every edge is a bridge, a walk joins the facial orbits of darts based
at its two endpoints. -/
theorem sameCycle_faceStep_of_walk_of_all_isBridge
    (R : RotationSystem G)
    (hbridge : ∀ d : G.Dart, G.IsBridge d.edge)
    {u v : V} (p : G.Walk u v) (a b : G.Dart)
    (ha : a.fst = u) (hb : b.fst = v) :
    R.faceStep.SameCycle a b := by
  induction p generalizing a with
  | nil =>
      exact R.sameCycle_faceStep_of_same_fst_of_all_isBridge hbridge a b
        (ha.trans hb.symm)
  | @cons u w v hadj p ih =>
      let d : G.Dart := ⟨(u, w), hadj⟩
      have had : R.faceStep.SameCycle a d :=
        R.sameCycle_faceStep_of_same_fst_of_all_isBridge hbridge a d ha
      have hds : R.faceStep.SameCycle d d.symm :=
        R.sameCycle_faceStep_of_isBridge d (hbridge d)
      have hsb : R.faceStep.SameCycle d.symm b :=
        ih d.symm rfl hb
      exact had.trans (hds.trans hsb)

/-- All darts of a tree lie in one facial orbit. -/
theorem sameCycle_faceStep_of_isTree
    (R : RotationSystem G) (hG : G.IsTree)
    (a b : G.Dart) : R.faceStep.SameCycle a b := by
  have hbridge : ∀ d : G.Dart, G.IsBridge d.edge := fun d ↦
    SimpleGraph.isAcyclic_iff_forall_isBridge.mp hG.isAcyclic d.edge_mem
  exact (hG.preconnected a.fst b.fst).elim fun p ↦
    R.sameCycle_faceStep_of_walk_of_all_isBridge hbridge p a b rfl rfl

/-- A rotation system on a finite tree containing an edge has exactly one
facial cycle. -/
theorem faceCount_eq_one_of_isTree_of_edgeSet_nonempty
    (R : RotationSystem G) (hG : G.IsTree) (hedge : G.edgeSet.Nonempty) :
    R.faceCount = 1 := by
  have hedgeFinset : G.edgeFinset.Nonempty := by
    simpa [SimpleGraph.mem_edgeFinset] using hedge
  have hdartCard : 0 < Fintype.card G.Dart := by
    have hedgeCard : 0 < G.edgeFinset.card := Finset.card_pos.mpr hedgeFinset
    rw [card_darts_eq_two_mul_card_edges]
    omega
  haveI : Nonempty G.Dart := Fintype.card_pos_iff.mp hdartCard
  let a : G.Dart := Classical.choice inferInstance
  have hcycle : R.faceStep.IsCycle := by
    rw [Equiv.Perm.isCycle_iff_sameCycle (R.faceStep_ne_self a)]
    intro b
    constructor
    · intro _
      exact R.faceStep_ne_self b
    · intro _
      exact R.sameCycle_faceStep_of_isTree hG a b
  unfold faceCount faceCycles
  rw [hcycle.cycleFactorsFinset_eq_singleton]
  exact Finset.card_singleton _

end RotationSystem

end

end LeanCo.PackingEdgeColoring
