import LeanCo.QuantumLatin.SingularProduct

/-!
# Pointed separated copies

The shared hole is fixed while the remaining entries are separated by a
one-coordinate diagonal unitary.  This is the pointed form of the finite
avoidance argument used in Lemma 4.8(2).
-/

namespace LeanCo.QuantumLatin

universe u v

open PointedMaximalRQLS

variable {β : Type u} [Fintype β] [DecidableEq β]

/-- Rotate one surviving coordinate of a pointed square. -/
noncomputable def PointedMaximalRQLS.rotateCoordinate
    (P : PointedMaximalRQLS β) (d : β) (u : Circle) :
    PointedMaximalRQLS β where
  full := P.full.rotateCoordinate (some d) u
  hole_entry := by
    change LeanCo.QuantumLatin.rotateCoordinate (some d) u
      (P.full.square.entry none none) = basis none
    rw [P.hole_entry]
    funext c
    rcases c with _ | b
    · simp [LeanCo.QuantumLatin.rotateCoordinate, basis_apply]
    · simp [LeanCo.QuantumLatin.rotateCoordinate, basis_apply]
  hole_transversal := P.hole_transversal

theorem PointedMaximalRQLS.rotateCoordinate_regular
    (P : PointedMaximalRQLS β) {d e : β} (hP : P.RegularAt d e)
    (u : Circle) : (P.rotateCoordinate d u).RegularAt d e := by
  refine ⟨hP.1, ?_⟩
  intro i j hij
  have h := hP.2 i j hij
  constructor
  · change LeanCo.QuantumLatin.rotateCoordinate (some d) u
      (P.full.square.entry i j) (some d) ≠ 0
    rw [rotateCoordinate_apply_same]
    exact mul_ne_zero (Circle.coe_ne_zero u) h.1
  · change LeanCo.QuantumLatin.rotateCoordinate (some d) u
      (P.full.square.entry i j) (some e) ≠ 0
    rw [rotateCoordinate_apply_of_ne]
    · exact h.2
    · simpa using Ne.symm hP.1

/-- Pairwise projective disjointness, with the shared hole omitted. -/
def PointedRotatedCopiesDisjoint (P : PointedMaximalRQLS β)
    (d : β) (u v : Circle) : Prop :=
  ∀ i j i' j' : Option β,
    IsNonholeCell i j → IsNonholeCell i' j' →
    ¬ PhaseEquivalent
      (LeanCo.QuantumLatin.rotateCoordinate (some d) u
        (P.full.square.entry i j))
      (LeanCo.QuantumLatin.rotateCoordinate (some d) v
        (P.full.square.entry i' j'))

private noncomputable instance : Infinite Circle :=
  Infinite.of_injective
    (fun x : ℝ ↦ Circle.exp (Real.arctan x)) (by
      intro x y hxy
      apply Real.arctan_injective
      exact Circle.exp_injOn_Icc (by nlinarith [Real.pi_pos])
        ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩
        ⟨(Real.neg_pi_div_two_lt_arctan y).le, (Real.arctan_lt_pi_div_two y).le⟩ hxy)

private noncomputable def nonholeCells : Finset (Option β × Option β) :=
  by
    classical
    exact Finset.univ.filter fun q ↦ IsNonholeCell q.1 q.2

private theorem mem_nonholeCells {q : Option β × Option β} :
    q ∈ (nonholeCells : Finset (Option β × Option β)) ↔
      IsNonholeCell q.1 q.2 := by
  classical
  simp [nonholeCells]

private noncomputable def pointedForbiddenSet (P : PointedMaximalRQLS β)
    (d : β) (s : Finset Circle) : Finset Circle := by
  classical
  exact (((s ×ˢ (nonholeCells : Finset (Option β × Option β))) ×ˢ
      (nonholeCells : Finset (Option β × Option β))).image fun q ↦
    forbiddenPhase (some d) q.1.1
      (P.full.square.entry q.1.2.1 q.1.2.2)
      (P.full.square.entry q.2.1 q.2.2))

private theorem mem_pointedForbiddenSet_of_phaseEquivalent
    (P : PointedMaximalRQLS β) {d e : β} (hP : P.RegularAt d e)
    {s : Finset Circle} {u v : Circle} (hv : v ∈ s)
    {i j i' j' : Option β} (hij : IsNonholeCell i j)
    (hij' : IsNonholeCell i' j')
    (h : PhaseEquivalent
      (LeanCo.QuantumLatin.rotateCoordinate (some d) u
        (P.full.square.entry i j))
      (LeanCo.QuantumLatin.rotateCoordinate (some d) v
        (P.full.square.entry i' j'))) :
    u ∈ pointedForbiddenSet P d s := by
  classical
  rw [pointedForbiddenSet, Finset.mem_image]
  refine ⟨((v, (i, j)), (i', j')), ?_, ?_⟩
  · simp [hv, mem_nonholeCells, hij, hij']
  · apply (eq_forbiddenPhase_of_phaseEquivalent (by simpa using hP.1)
      (hP.2 i j hij).1 (hP.2 i' j' hij').2 h).symm

private def PointedPhaseSetSeparated (P : PointedMaximalRQLS β)
    (d : β) (s : Finset Circle) : Prop :=
  ∀ ⦃u : Circle⦄, u ∈ s → ∀ ⦃v : Circle⦄, v ∈ s → u ≠ v →
    PointedRotatedCopiesDisjoint P d u v

private theorem exists_pointedPhaseSetSeparated_card
    (P : PointedMaximalRQLS β) {d e : β} (hP : P.RegularAt d e) :
    ∀ k : ℕ, ∃ s : Finset Circle,
      s.card = k ∧ PointedPhaseSetSeparated P d s := by
  classical
  intro k
  induction k with
  | zero => exact ⟨∅, by simp, by simp [PointedPhaseSetSeparated]⟩
  | succ k ih =>
      obtain ⟨s, hcard, hsep⟩ := ih
      obtain ⟨u, hu⟩ :=
        Infinite.exists_notMem_finset (pointedForbiddenSet P d s ∪ s)
      have huBad : u ∉ pointedForbiddenSet P d s :=
        fun hm ↦ hu (Finset.mem_union_left s hm)
      have huS : u ∉ s :=
        fun hm ↦ hu (Finset.mem_union_right (pointedForbiddenSet P d s) hm)
      refine ⟨insert u s, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem huS, hcard]
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact (hab rfl).elim
          · intro i j i' j' hij hij' hphase
            exact huBad (mem_pointedForbiddenSet_of_phaseEquivalent
              P hP hb hij hij' hphase)
        · rcases hb with rfl | hb
          · intro i j i' j' hij hij' hphase
            exact huBad (mem_pointedForbiddenSet_of_phaseEquivalent
              P hP ha hij' hij hphase.symm)
          · exact hsep ha hb hab

/-- A pointed regular square has arbitrarily many copies sharing precisely
the distinguished hole and otherwise having disjoint projective entries. -/
theorem PointedMaximalRQLS.exists_phaseDisjoint_pointed_copies
    (P : PointedMaximalRQLS β) {d e : β} (hP : P.RegularAt d e)
    (ρ : Type v) [Fintype ρ] :
    ∃ F : PhaseDisjointPointedRQLSFamily ρ β,
      ∀ r, (F.copy r).RegularAt d e := by
  classical
  obtain ⟨s, hcard, hsep⟩ :=
    exists_pointedPhaseSetSeparated_card P hP (Fintype.card ρ)
  let idx : {u // u ∈ s} ≃ Fin (Fintype.card ρ) :=
    Fintype.equivFinOfCardEq ((Fintype.card_coe s).trans hcard)
  let phase : ρ → Circle := fun r ↦
    (idx.symm (Fintype.equivFin ρ r)).1
  have hphase : Function.Injective phase := by
    intro r r' h
    apply (Fintype.equivFin ρ).injective
    apply idx.symm.injective
    exact Subtype.ext h
  let F : PhaseDisjointPointedRQLSFamily ρ β := {
    copy := fun r ↦ P.rotateCoordinate d (phase r)
    pairwise_disjoint := by
      intro r r' hrr i j i' j' hij hij'
      exact hsep (idx.symm (Fintype.equivFin ρ r)).2
        (idx.symm (Fintype.equivFin ρ r')).2 (fun h ↦ hrr (hphase h))
        i j i' j' hij hij' }
  exact ⟨F, fun r ↦ P.rotateCoordinate_regular hP (phase r)⟩

end LeanCo.QuantumLatin
