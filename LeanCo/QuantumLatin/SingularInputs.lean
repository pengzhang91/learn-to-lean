import LeanCo.QuantumLatin.AvoidingCopies
import LeanCo.QuantumLatin.PointedCopies
import LeanCo.QuantumLatin.SingularMaximal

/-!
# Supplying the separation data for the singular product

This file closes conditions (ii)--(iv) of Construction 4.6.  First make
pointed copies with a common deleted hole, then regard all their non-hole
projections as one finite target family, and finally choose the ordinary
copies while avoiding that family.
-/

namespace LeanCo.QuantumLatin

universe u v w x

variable {α : Type u} {β : Type v} {ρ : Type w} {γ : Type x}
  [Fintype α] [Fintype β] [Fintype ρ] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq ρ] [DecidableEq γ]

open PointedMaximalRQLS

/-- Index all non-hole cells of a pointed square. -/
abbrev NonholeCell (β : Type v) :=
  {q : Option β × Option β // IsNonholeCell q.1 q.2}

namespace PhaseDisjointCopiesAvoiding

theorem copy_regular {R : MaximalRQLS β} {d e : β}
    {τ : Type*} {T : τ → Ket β} {γ : Type*}
    (F : PhaseDisjointCopiesAvoiding R d T γ)
    (hde : d ≠ e)
    (hR : ∀ i j, R.square.entry i j d ≠ 0 ∧
      R.square.entry i j e ≠ 0) (g : γ) :
    (F.copy g).square.entry i j d ≠ 0 ∧
      (F.copy g).square.entry i j e ≠ 0 := by
  constructor
  · rw [copy_entry, rotateCoordinate_apply_same]
    exact mul_ne_zero (Circle.coe_ne_zero (F.phase g)) (hR i j).1
  · rw [copy_entry, rotateCoordinate_apply_of_ne]
    · exact (hR i j).2
    · exact Ne.symm hde

end PhaseDisjointCopiesAvoiding

namespace SingularProductData

/-- Conditions (ii)--(iv) can be met from one regular ordinary square and one
regular pointed square.  The conclusion exposes the exact data and
separation witness consumed by the singular-product maximality theorem. -/
theorem exists_data_and_separation
    (A : ClassicalBiresolution α) (split : α ≃ (γ ⊕ ρ))
    (R : MaximalRQLS β) (P : PointedMaximalRQLS β)
    (D : MaximalRQLS ρ) {d e : β}
    (hR : ∀ i j, R.square.entry i j d ≠ 0 ∧
      R.square.entry i j e ≠ 0)
    (hP : P.RegularAt d e) :
    ∃ X : SingularProductData (α := α) (β := β) (ρ := ρ) (γ := γ),
      X.SeparationHypotheses := by
  classical
  obtain ⟨C, hC⟩ := P.exists_phaseDisjoint_pointed_copies hP ρ
  let target : (ρ × NonholeCell β) → Ket β := fun q b ↦
    (C.copy q.1).full.square.entry q.2.1.1 q.2.1.2 (some b)
  have htarget : ∀ q, target q d ≠ 0 ∧ target q e ≠ 0 := by
    rintro ⟨r, ⟨⟨s, t⟩, hst⟩⟩
    exact (hC r).2 s t hst
  obtain ⟨B⟩ := R.exists_phaseDisjoint_copies_avoiding
    (α := γ) (τ := ρ × NonholeCell β) hP.1 hR target htarget
  let X : SingularProductData (α := α) (β := β) (ρ := ρ) (γ := γ) := {
    outer := A
    split := split
    ordinary := B.toPhaseDisjointFamily
    special := C
    exceptional := D }
  refine ⟨X, {
    regular_coordinates := ⟨d, e, hP.1, ?_, hC⟩
    ordinary_avoids_special := ?_ }⟩
  · intro g i j
    exact B.copy_regular hP.1 hR g
  · intro g i j r s t hst hc0
    exact B.copy_avoids_target g i j (r, ⟨(s, t), hst⟩)

end SingularProductData

end LeanCo.QuantumLatin
