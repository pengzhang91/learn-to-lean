import LeanCo.QuantumLatin.SeparatedCopies

/-!
# Phase-disjoint copies avoiding a finite target family

This strengthens the separated-copy construction by requiring every entry of
every new copy to avoid every ray in a prescribed finite family.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

universe u v w

noncomputable local instance : Infinite Circle :=
  Infinite.of_injective
    (fun x : ℝ ↦ Circle.exp (Real.arctan x)) (by
      intro x y hxy
      apply Real.arctan_injective
      exact Circle.exp_injOn_Icc (by nlinarith [Real.pi_pos])
        ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩
        ⟨(Real.neg_pi_div_two_lt_arctan y).le, (Real.arctan_lt_pi_div_two y).le⟩ hxy)

section TargetAvoidance

variable {β : Type u} [Fintype β] [DecidableEq β]
variable {τ : Type v} [Fintype τ]

@[simp] theorem rotateCoordinate_one (d : β) (x : Ket β) :
    rotateCoordinate d (1 : Circle) x = x := by
  funext c
  by_cases hcd : c = d
  · subst c
    simp
  · simp [rotateCoordinate_apply_of_ne d (1 : Circle) x hcd]

/-- The finite set containing the sole possible bad phase for each ordered
pair consisting of an entry of `R` and a target vector. -/
noncomputable def targetForbiddenSet (R : MaximalRQLS β) (d : β)
    (T : τ → Ket β) : Finset Circle := by
  classical
  exact ((Finset.univ : Finset ((β × β) × τ)).image fun q ↦
    forbiddenPhase d 1 (R.square.entry q.1.1 q.1.2) (T q.2))

theorem mem_targetForbiddenSet_of_phaseEquivalent (R : MaximalRQLS β)
    {d e : β} (hde : d ≠ e)
    (hR : ∀ i j, R.square.entry i j d ≠ 0)
    (T : τ → Ket β) (hT : ∀ t, T t e ≠ 0)
    {u : Circle} {i j : β} {t : τ}
    (h : PhaseEquivalent
      (rotateCoordinate d u (R.square.entry i j)) (T t)) :
    u ∈ targetForbiddenSet R d T := by
  classical
  rw [targetForbiddenSet, Finset.mem_image]
  refine ⟨((i, j), t), by simp, ?_⟩
  apply (eq_forbiddenPhase_of_phaseEquivalent hde (hR i j) (hT t) ?_).symm
  simpa only [rotateCoordinate_one] using h

/-- Every phase in `s` makes all entries of the corresponding rotated copy
avoid all prescribed target rays. -/
def PhaseSetAvoidsTargets (R : MaximalRQLS β) (d : β)
    (T : τ → Ket β) (s : Finset Circle) : Prop :=
  ∀ ⦃u : Circle⦄, u ∈ s → ∀ i j t,
    ¬ PhaseEquivalent (rotateCoordinate d u (R.square.entry i j)) (T t)

/-- Simultaneous finite avoidance: the phase set has prescribed cardinality,
its distinct rotations are mutually disjoint, and all its rotations avoid the
target family. -/
theorem exists_phaseSetSeparated_avoiding_card (R : MaximalRQLS β)
    {d e : β} (hde : d ≠ e)
    (hR : ∀ i j, R.square.entry i j d ≠ 0 ∧ R.square.entry i j e ≠ 0)
    (T : τ → Ket β) (hT : ∀ t, T t d ≠ 0 ∧ T t e ≠ 0) :
    ∀ k : ℕ, ∃ s : Finset Circle,
      s.card = k ∧ PhaseSetSeparated R d s ∧ PhaseSetAvoidsTargets R d T s := by
  classical
  intro k
  induction k with
  | zero =>
      exact ⟨∅, by simp, by simp [PhaseSetSeparated], by simp [PhaseSetAvoidsTargets]⟩
  | succ k ih =>
      obtain ⟨s, hcard, hsep, havoid⟩ := ih
      obtain ⟨u, hu⟩ := Infinite.exists_notMem_finset
        ((forbiddenSet R d s ∪ targetForbiddenSet R d T) ∪ s)
      have huPair : u ∉ forbiddenSet R d s := fun hmem ↦
        hu (Finset.mem_union_left s
          (Finset.mem_union_left (targetForbiddenSet R d T) hmem))
      have huTarget : u ∉ targetForbiddenSet R d T := fun hmem ↦
        hu (Finset.mem_union_left s
          (Finset.mem_union_right (forbiddenSet R d s) hmem))
      have huS : u ∉ s := fun hmem ↦
        hu (Finset.mem_union_right (forbiddenSet R d s ∪ targetForbiddenSet R d T) hmem)
      refine ⟨insert u s, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem huS, hcard]
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact (hab rfl).elim
          · intro i j i' j' hphase
            exact huPair (mem_forbiddenSet_of_phaseEquivalent R hde hR hb hphase)
        · rcases hb with rfl | hb
          · intro i j i' j' hphase
            exact huPair (mem_forbiddenSet_of_phaseEquivalent R hde hR ha hphase.symm)
          · exact hsep ha hb hab
      · intro a ha i j t hphase
        rw [Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact huTarget (mem_targetForbiddenSet_of_phaseEquivalent R hde
            (fun i j ↦ (hR i j).1) T (fun t ↦ (hT t).2) hphase)
        · exact havoid ha i j t hphase

end TargetAvoidance

/-! ## Interface for singular products -/

/-- Coordinate-rotation copies of one maximal RQLS which are pairwise
projectively disjoint and avoid a prescribed target family.  Storing the
phases makes it definitionally clear that every copy is obtained from `R` by
the same kind of common-coordinate unitary. -/
structure PhaseDisjointCopiesAvoiding
    {β : Type u} [Fintype β] [DecidableEq β]
    (R : MaximalRQLS β) (d : β) {τ : Type v} (T : τ → Ket β)
    (α : Type w) where
  phase : α → Circle
  phase_injective : Function.Injective phase
  pairwise_disjoint : ∀ ⦃a b : α⦄, a ≠ b →
    RotatedCopiesDisjoint R d (phase a) (phase b)
  avoids_targets : ∀ a i j t,
    ¬ PhaseEquivalent
      (rotateCoordinate d (phase a) (R.square.entry i j)) (T t)

namespace PhaseDisjointCopiesAvoiding

variable {β : Type u} [Fintype β] [DecidableEq β]
variable {τ : Type v} {α : Type w}
variable {R : MaximalRQLS β} {d : β} {T : τ → Ket β}

/-- The actual maximal RQLS at family index `a`. -/
def copy (F : PhaseDisjointCopiesAvoiding R d T α) (a : α) : MaximalRQLS β :=
  R.rotateCoordinate d (F.phase a)

@[simp] theorem copy_entry (F : PhaseDisjointCopiesAvoiding R d T α)
    (a : α) (i j c : β) :
    (F.copy a).square.entry i j c =
      rotateCoordinate d (F.phase a) (R.square.entry i j) c := rfl

/-- Forget the target-avoidance data and expose the family interface from
`SeparatedCopies`. -/
def toPhaseDisjointFamily (F : PhaseDisjointCopiesAvoiding R d T α) :
    PhaseDisjointMaximalRQLSFamily α β where
  copy := F.copy
  pairwise_disjoint := by
    intro a b hab i j i' j'
    exact F.pairwise_disjoint hab i j i' j'

theorem copy_avoids_target (F : PhaseDisjointCopiesAvoiding R d T α)
    (a : α) (i j : β) (t : τ) :
    ¬ PhaseEquivalent ((F.copy a).square.entry i j) (T t) :=
  F.avoids_targets a i j t

end PhaseDisjointCopiesAvoiding

section ArbitraryFiniteIndex

variable {β : Type u} [Fintype β] [DecidableEq β]
variable {τ : Type v} [Fintype τ]
variable {α : Type w} [Fintype α]

/-- Arbitrary-finite-index form of the target-avoiding separated-copy
theorem. -/
theorem MaximalRQLS.exists_phaseDisjoint_copies_avoiding
    (R : MaximalRQLS β) {d e : β} (hde : d ≠ e)
    (hR : ∀ i j, R.square.entry i j d ≠ 0 ∧ R.square.entry i j e ≠ 0)
    (T : τ → Ket β) (hT : ∀ t, T t d ≠ 0 ∧ T t e ≠ 0) :
    Nonempty (PhaseDisjointCopiesAvoiding R d T α) := by
  classical
  obtain ⟨s, hcard, hsep, havoid⟩ :=
    exists_phaseSetSeparated_avoiding_card R hde hR T hT (Fintype.card α)
  let idx : {u // u ∈ s} ≃ α :=
    Fintype.equivOfCardEq ((Fintype.card_coe s).trans hcard)
  let phase : α → Circle := fun a ↦ (idx.symm a).1
  refine ⟨{
    phase := phase
    phase_injective := ?_
    pairwise_disjoint := ?_
    avoids_targets := ?_ }⟩
  · intro a b hab
    apply idx.symm.injective
    exact Subtype.ext hab
  · intro a b hab
    apply hsep (idx.symm a).2 (idx.symm b).2
    intro huv
    apply hab
    apply idx.symm.injective
    exact Subtype.ext huv
  · intro a i j t
    exact havoid (idx.symm a).2 i j t

end ArbitraryFiniteIndex

end LeanCo.QuantumLatin
