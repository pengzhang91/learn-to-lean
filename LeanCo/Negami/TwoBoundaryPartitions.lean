import LeanCo.Negami.FinitePartition
import LeanCo.Negami.TwoBoundary
import Mathlib.Tactic

/-!
# Derivation of the two-boundary connectivity matrix

This file proves that a two-element boundary has exactly the connected and
discrete partitions, computes all four generated block counts, and derives
the matrix of Proposition 6.1 from those partition calculations.
-/

namespace LeanCo.Negami

/-- The one-block partition of a two-element boundary. -/
def connectedTwoPartition : FinitePartition (Fin 2) :=
  ⟨fun _ _ => true, by simp [IsEquivBool]⟩

/-- The two-block partition of a two-element boundary. -/
def discreteTwoPartition : FinitePartition (Fin 2) :=
  ⟨fun i j => decide (i = j), by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp
    · intro i j
      apply Bool.eq_iff_iff.mpr
      simp [eq_comm]
    · intro i j k hij hjk
      simp only [decide_eq_true_eq] at hij hjk ⊢
      exact hij.trans hjk⟩

@[simp] theorem connectedTwoPartition_rel (i j : Fin 2) :
    connectedTwoPartition.toSetoid i j := by
  rfl

@[simp] theorem discreteTwoPartition_rel (i j : Fin 2) :
    discreteTwoPartition.toSetoid i j ↔ i = j := by
  change decide (i = j) = true ↔ i = j
  simp

noncomputable def connectedTwoQuotientEquiv :
    Quotient connectedTwoPartition.toSetoid ≃ Unit where
  toFun _ := ()
  invFun _ := @Quotient.mk' _ connectedTwoPartition.toSetoid 0
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ i => apply Quotient.sound; simp
  right_inv u := by cases u; rfl

noncomputable def discreteTwoQuotientEquiv :
    Quotient discreteTwoPartition.toSetoid ≃ Fin 2 where
  toFun := Quotient.lift id (by
    intro i j h
    exact (discreteTwoPartition_rel i j).mp h)
  invFun i := @Quotient.mk' _ discreteTwoPartition.toSetoid i
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ i => rfl
  right_inv i := rfl

@[simp] theorem connectedTwoPartition_blocks :
    FinitePartition.blocks connectedTwoPartition = 1 := by
  unfold FinitePartition.blocks
  rw [Nat.card_congr connectedTwoQuotientEquiv]
  simp

@[simp] theorem discreteTwoPartition_blocks :
    FinitePartition.blocks discreteTwoPartition = 2 := by
  unfold FinitePartition.blocks
  rw [Nat.card_congr discreteTwoQuotientEquiv]
  simp

theorem join_connectedTwoPartition_left (π : FinitePartition (Fin 2)) :
    FinitePartition.join connectedTwoPartition π = connectedTwoPartition := by
  apply Subtype.ext
  funext i j
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro _
    rfl
  · intro _
    exact (FinitePartition.join_rel connectedTwoPartition π i j).mpr
      (Relation.EqvGen.rel _ _ (Or.inl (by rfl)))

theorem join_connectedTwoPartition_right (π : FinitePartition (Fin 2)) :
    FinitePartition.join π connectedTwoPartition = connectedTwoPartition := by
  rw [FinitePartition.join_comm]
  exact join_connectedTwoPartition_left π

private theorem eq_of_eqvGen_discrete {i j : Fin 2}
    (h : Relation.EqvGen
      (fun a b : Fin 2 => discreteTwoPartition.toSetoid a b ∨
        discreteTwoPartition.toSetoid a b) i j) : i = j := by
  induction h with
  | rel x y hxy =>
      exact hxy.elim
        (fun q => (discreteTwoPartition_rel _ _).mp q)
        (fun q => (discreteTwoPartition_rel _ _).mp q)
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ih₁ ih₂ => exact ih₁.trans ih₂

theorem join_discreteTwoPartition :
    FinitePartition.join discreteTwoPartition discreteTwoPartition =
      discreteTwoPartition := by
  apply Subtype.ext
  funext i j
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hg : Relation.EqvGen
        (fun a b : Fin 2 => discreteTwoPartition.toSetoid a b ∨
          discreteTwoPartition.toSetoid a b) i j :=
      (FinitePartition.join_rel discreteTwoPartition
        discreteTwoPartition i j).mp h
    have hij : i = j := eq_of_eqvGen_discrete hg
    simpa [discreteTwoPartition] using hij
  · intro h
    have hij : i = j := by
      simpa [discreteTwoPartition] using h
    cases hij
    exact (FinitePartition.join_rel discreteTwoPartition
      discreteTwoPartition i i).mpr (Relation.EqvGen.refl i)

@[simp] theorem rho_connected_connected :
    FinitePartition.rho connectedTwoPartition connectedTwoPartition = 1 := by
  simp [FinitePartition.rho, join_connectedTwoPartition_left]

@[simp] theorem rho_connected_discrete :
    FinitePartition.rho connectedTwoPartition discreteTwoPartition = 1 := by
  simp [FinitePartition.rho, join_connectedTwoPartition_left]

@[simp] theorem rho_discrete_connected :
    FinitePartition.rho discreteTwoPartition connectedTwoPartition = 1 := by
  simp [FinitePartition.rho, join_connectedTwoPartition_right]

@[simp] theorem rho_discrete_discrete :
    FinitePartition.rho discreteTwoPartition discreteTwoPartition = 2 := by
  simp [FinitePartition.rho, join_discreteTwoPartition]

/-- Exhaustion of every equivalence relation on a two-element set. -/
theorem finitePartition_fin_two_eq_connected_or_discrete
    (π : FinitePartition (Fin 2)) :
    π = connectedTwoPartition ∨ π = discreteTwoPartition := by
  by_cases h : π.1 0 1 = true
  · left
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j
    · exact π.2.1 0
    · exact h
    · rw [π.2.2.1]
      exact h
    · exact π.2.1 1
  · right
    have hf : π.1 0 1 = false := Bool.eq_false_of_not_eq_true h
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j
    · simpa [discreteTwoPartition] using π.2.1 0
    · simpa [discreteTwoPartition] using hf
    · rw [π.2.2.1]
      simpa [discreteTwoPartition] using hf
    · simpa [discreteTwoPartition] using π.2.1 1

theorem connectedTwoPartition_ne_discreteTwoPartition :
    connectedTwoPartition ≠ discreteTwoPartition := by
  intro h
  have hb := congrArg FinitePartition.blocks h
  simp at hb

theorem discreteTwoPartition_ne_connectedTwoPartition :
    discreteTwoPartition ≠ connectedTwoPartition :=
  Ne.symm connectedTwoPartition_ne_discreteTwoPartition

/-- The paper's ordering `(C,D)` of every two-boundary partition. -/
def twoPartition (i : Fin 2) : FinitePartition (Fin 2) :=
  if i = 0 then connectedTwoPartition else discreteTwoPartition

noncomputable def twoPartitionEquiv : Fin 2 ≃ FinitePartition (Fin 2) :=
  Equiv.ofBijective twoPartition ⟨by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [twoPartition, connectedTwoPartition_ne_discreteTwoPartition,
        discreteTwoPartition_ne_connectedTwoPartition], by
    intro π
    rcases finitePartition_fin_two_eq_connected_or_discrete π with h | h
    · exact ⟨0, by simp [twoPartition, h]⟩
    · exact ⟨1, by simp [twoPartition, h]⟩⟩

/-- Proposition 6.1: the connectivity matrix derived from the two actual
boundary partitions is exactly the displayed matrix `T₂(t)`. -/
theorem twoBoundaryMatrix_from_partitions {F : Type*} [Field F] (t : F) :
    (fun i j : Fin 2 =>
      t ^ FinitePartition.rho (twoPartition i) (twoPartition j)) =
      twoBoundaryMatrix t := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoPartition, twoBoundaryMatrix]

end LeanCo.Negami
