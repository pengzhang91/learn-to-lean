import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# A finite one-quarter averaging lemma

An independent fair bit is assigned to every coordinate.  Prescribing the
two bits on a two-element coordinate set keeps exactly one quarter of all
assignments.  Double counting then produces one assignment that keeps at
least a quarter of any finite family of such constraints.
-/

open scoped BigOperators

namespace LeanCo.HypercubeTuran

open Finset

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Bit assignments agreeing with `target` on `P`. -/
def twoCoordinateEvent (P : Finset ι) (target : ι → Fin 2) :
    Finset (ι → Fin 2) :=
  Finset.univ.filter fun r => ∀ i ∈ P, r i = target i

lemma twoCoordinateEvent_eq_piFinset (P : Finset ι) (target : ι → Fin 2) :
    twoCoordinateEvent P target =
      Fintype.piFinset (fun i => if i ∈ P then {target i} else Finset.univ) := by
  ext r
  simp only [twoCoordinateEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    Fintype.mem_piFinset]
  constructor
  · intro h i
    by_cases hi : i ∈ P
    · simp [hi, h i hi]
    · simp [hi]
  · intro h i hi
    simpa [hi] using h i

lemma card_twoCoordinateEvent (P : Finset ι) (target : ι → Fin 2)
    (hP : #P = 2) :
    4 * #(twoCoordinateEvent P target) = Fintype.card (ι → Fin 2) := by
  classical
  rw [twoCoordinateEvent_eq_piFinset, Fintype.card_piFinset,
    Fintype.card_pi]
  have hprod :
      (∏ i : ι, #(if i ∈ P then {target i} else (Finset.univ : Finset (Fin 2)))) =
        ∏ i : ι, if i ∈ P then 1 else 2 := by
    apply Fintype.prod_congr
    intro i
    by_cases hi : i ∈ P <;> simp [hi]
  rw [hprod]
  simp only [Fintype.card_fin]
  rw [show (∏ i : ι, if i ∈ P then 1 else 2) =
      ∏ i ∈ (Finset.univ \ P), 2 by
    calc
      (∏ i : ι, if i ∈ P then 1 else 2) =
        (∏ i ∈ (Finset.univ.filter fun i : ι => i ∈ P), 1) *
          (∏ i ∈ (Finset.univ.filter fun i : ι => i ∉ P), 2) := by
            exact Finset.prod_ite (s := (Finset.univ : Finset ι))
              (fun _ => (1 : ℕ)) (fun _ => 2)
      _ = ∏ i ∈ (Finset.univ.filter fun i : ι => i ∉ P), 2 := by simp
      _ = ∏ i ∈ (Finset.univ \ P), 2 := by
            congr 2
            ext i
            simp [Finset.mem_sdiff]]
  simp only [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ P),
    Finset.card_univ, hP, Nat.nsmul_eq_mul, mul_one]
  have hcard : 2 ≤ Fintype.card ι := by
    rw [← hP]
    exact Finset.card_le_univ P
  calc
    4 * 2 ^ (Fintype.card ι - 2) =
        2 ^ (Fintype.card ι - 2) * 2 ^ 2 := by ring
    _ = 2 ^ ((Fintype.card ι - 2) + 2) :=
      (pow_add 2 (Fintype.card ι - 2) 2).symm
    _ = 2 ^ Fintype.card ι := by congr 1; omega

/-- Constraints attached to vertices of a finite set. -/
def keptByAssignment {V : Type v} [DecidableEq V]
    (L : Finset V) (P : V → Finset ι) (target : V → ι → Fin 2)
    (r : ι → Fin 2) : Finset V :=
  L.filter fun v => ∀ i ∈ P v, r i = target v i

@[simp]
lemma mem_keptByAssignment {V : Type v} [DecidableEq V]
    {L : Finset V} {P : V → Finset ι} {target : V → ι → Fin 2}
    {r : ι → Fin 2} {v : V} :
    v ∈ keptByAssignment L P target r ↔
      v ∈ L ∧ ∀ i ∈ P v, r i = target v i := by
  simp [keptByAssignment]

/-- Finite averaging: some bit assignment satisfies at least one quarter of
the prescribed two-coordinate constraints. -/
theorem exists_assignment_card_le_four_mul_kept
    {V : Type v} [Fintype V] [DecidableEq V]
    (L : Finset V) (P : V → Finset ι) (target : V → ι → Fin 2)
    (hP : ∀ v ∈ L, #(P v) = 2) :
    ∃ r : ι → Fin 2, #L ≤ 4 * #(keptByAssignment L P target r) := by
  classical
  let R : Finset (ι → Fin 2) := Finset.univ
  have hdouble :
      (∑ r ∈ R, #(keptByAssignment L P target r)) =
        ∑ v ∈ L, #(twoCoordinateEvent (P v) (target v)) := by
    simp only [keptByAssignment, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    simp [R, twoCoordinateEvent]
  have hscaled :
      4 * (∑ r ∈ R, #(keptByAssignment L P target r)) =
        Fintype.card (ι → Fin 2) * #L := by
    rw [hdouble, Finset.mul_sum]
    calc
      (∑ v ∈ L, 4 * #(twoCoordinateEvent (P v) (target v))) =
          ∑ _v ∈ L, Fintype.card (ι → Fin 2) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact card_twoCoordinateEvent (P v) (target v) (hP v hv)
      _ = Fintype.card (ι → Fin 2) * #L := by
            simp [Nat.mul_comm]
  by_contra hnone
  push_neg at hnone
  have hlt :
      (∑ r ∈ R, 4 * #(keptByAssignment L P target r)) <
        ∑ _r ∈ R, #L := by
    apply Finset.sum_lt_sum
    · intro r hr
      exact (hnone r).le
    · have hR : R.Nonempty := by simp [R]
      obtain ⟨r, hr⟩ := hR
      exact ⟨r, hr, hnone r⟩
  rw [← Finset.mul_sum, hscaled] at hlt
  simp [R, Nat.mul_comm] at hlt

end LeanCo.HypercubeTuran
