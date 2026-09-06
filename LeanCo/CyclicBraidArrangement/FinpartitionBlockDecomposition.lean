import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.BigOperators

/-!
# Splitting a finite set partition at one distinguished block

This elementary equivalence is the recursion interface needed by the direct
set-partition identities in Section 4.  A partition of `s`, together with a
distinguished element `a ∈ s`, is the same as its block containing `a`
and a partition of the complementary finset.
-/

namespace CyclicBraidArrangement

open Finset

namespace Finpartition

variable {α : Type*} [DecidableEq α]

/-- A block contained in `s` and containing the distinguished element `a`. -/
abbrev PointedBlock (s : Finset α) (a : α) :=
  {B : Finset α // a ∈ B ∧ B ⊆ s}

/-- Data obtained by removing the block containing `a` from a partition. -/
abbrev SplitAtData (s : Finset α) (a : α) :=
  Σ B : PointedBlock s a, Finpartition (s \ B.1)

/-- Split off the unique block containing `a`. -/
noncomputable def splitAt {s : Finset α} (P : Finpartition s)
    {a : α} (ha : a ∈ s) : SplitAtData s a :=
  ⟨⟨P.part a, P.mem_part ha, P.part_subset a⟩, P.avoid (P.part a)⟩

/-- Reinsert a pointed block into a partition of its complement. -/
def joinAt {s : Finset α} {a : α} (z : SplitAtData s a) :
    Finpartition s :=
  z.2.extend
    (nonempty_iff_ne_empty.mp ⟨a, z.1.2.1⟩)
    disjoint_sdiff_self_left
    (sdiff_union_of_subset z.1.2.2)

@[simp] theorem parts_joinAt {s : Finset α} {a : α}
    (z : SplitAtData s a) :
    (joinAt z).parts = insert z.1.1 z.2.parts := rfl

/-- Avoiding one whole part simply erases that part from the part finset. -/
theorem parts_avoid_part {s : Finset α} (P : Finpartition s)
    {B : Finset α} (hB : B ∈ P.parts) :
    (P.avoid B).parts = P.parts.erase B := by
  ext D
  rw [P.mem_avoid]
  constructor
  · rintro ⟨E, hE, hnot, rfl⟩
    have hEB : Disjoint E B := by
      by_cases hEq : E = B
      · subst E
        exact (hnot (Subset.rfl)).elim
      · exact P.disjoint hE hB hEq
    have hdiff : E \ B = E := sdiff_eq_self_of_disjoint hEB
    rw [hdiff]
    exact mem_erase.mpr ⟨by
      intro h
      subst E
      exact hnot Subset.rfl, hE⟩
  · intro hD
    have hD' := mem_of_mem_erase hD
    have hDB : D ≠ B := ne_of_mem_erase hD
    have hdisj : Disjoint D B := P.disjoint hD' hB hDB
    refine ⟨D, hD', ?_, ?_⟩
    · intro hsub
      obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hD'
      exact disjoint_left.mp hdisj hx (hsub hx)
    · exact sdiff_eq_self_of_disjoint hdisj

/-- Rejoining the block split from a partition recovers the partition. -/
theorem joinAt_splitAt {s : Finset α} (P : Finpartition s)
    {a : α} (ha : a ∈ s) :
    joinAt (splitAt P ha) = P := by
  apply Finpartition.ext
  change insert (P.part a) (P.avoid (P.part a)).parts = P.parts
  rw [parts_avoid_part P (P.part_mem.mpr ha),
    Finset.insert_erase (P.part_mem.mpr ha)]

/-- In a rejoined partition, the distinguished element lies in the block
that was explicitly inserted. -/
theorem part_joinAt {s : Finset α} {a : α} (z : SplitAtData s a) :
    (joinAt z).part a = z.1.1 := by
  apply (joinAt z).part_eq_of_mem
  · rw [parts_joinAt]
    exact mem_insert_self _ _
  · exact z.1.2.1

/-- The pointed block cannot already be a part of the complementary tail. -/
theorem pointedBlock_not_mem_tail {s : Finset α} {a : α}
    (z : SplitAtData s a) : z.1.1 ∉ z.2.parts := by
  intro hpart
  have hsub := z.2.subset hpart
  have ha : a ∈ s \ z.1.1 := hsub z.1.2.1
  exact (mem_sdiff.mp ha).2 z.1.2.1

@[simp] theorem card_parts_joinAt {s : Finset α} {a : α}
    (z : SplitAtData s a) :
    (joinAt z).parts.card = z.2.parts.card + 1 := by
  rw [parts_joinAt, card_insert_of_notMem (pointedBlock_not_mem_tail z)]

/-- A block product factors into the distinguished-block factor and the
product over the complementary tail. -/
theorem prod_parts_joinAt {s : Finset α} {a : α}
    (z : SplitAtData s a) {R : Type*} [CommMonoid R]
    (weight : Finset α → R) :
    (∏ B ∈ (joinAt z).parts, weight B) =
      weight z.1.1 * ∏ B ∈ z.2.parts, weight B := by
  rw [parts_joinAt, prod_insert (pointedBlock_not_mem_tail z)]

/-- Removing the explicitly reinserted block leaves the original tail
partition. -/
theorem avoid_joinAt {s : Finset α} {a : α} (z : SplitAtData s a) :
    (joinAt z).avoid z.1.1 = z.2 := by
  have hmem : z.1.1 ∈ (joinAt z).parts := by
    rw [parts_joinAt]
    exact mem_insert_self _ _
  have hnot : z.1.1 ∉ z.2.parts := by
    exact pointedBlock_not_mem_tail z
  apply Finpartition.ext
  rw [parts_avoid_part (joinAt z) hmem, parts_joinAt,
    erase_insert hnot]

/-- Splitting a rejoined partition recovers both the pointed block and its
tail partition. -/
theorem splitAt_joinAt {s : Finset α} {a : α} (z : SplitAtData s a) :
    splitAt (joinAt z) (by
      exact mem_of_subset z.1.2.2 z.1.2.1) = z := by
  have hcarrier : (joinAt z).part a = z.1.1 := part_joinAt z
  have hpointed :
      (⟨(joinAt z).part a,
        (joinAt z).mem_part (mem_of_subset z.1.2.2 z.1.2.1),
        (joinAt z).part_subset a⟩ : PointedBlock s a) = z.1 := by
    apply Subtype.ext
    exact hcarrier
  apply Sigma.ext hpointed
  change (joinAt z).avoid ((joinAt z).part a) ≍ z.2
  rw [hcarrier]
  exact heq_of_eq (avoid_joinAt z)

/-- Canonical equivalence used to recurse over finite set partitions by the
block containing a distinguished element. -/
noncomputable def equivSplitAt {s : Finset α} {a : α} (ha : a ∈ s) :
    Finpartition s ≃ SplitAtData s a where
  toFun P := splitAt P ha
  invFun := joinAt
  left_inv P := joinAt_splitAt P ha
  right_inv := splitAt_joinAt

/-- Sum form of `equivSplitAt`, ready for partition recurrences. -/
theorem sum_eq_sum_pointedBlock [Fintype α]
    {s : Finset α} {a : α} (ha : a ∈ s)
    {R : Type*} [AddCommMonoid R] (f : Finpartition s → R) :
    (∑ P : Finpartition s, f P) =
      ∑ B : PointedBlock s a, ∑ Q : Finpartition (s \ B.1),
        f (joinAt ⟨B, Q⟩) := by
  calc
    (∑ P : Finpartition s, f P) =
        ∑ z : SplitAtData s a, f (joinAt z) :=
      ((equivSplitAt ha).symm.sum_comp f).symm
    _ = _ := Fintype.sum_sigma _

/-- Weighted recurrence obtained by splitting at the distinguished block. -/
theorem sum_coeff_mul_blockProduct [Fintype α]
    {s : Finset α} {a : α} (ha : a ∈ s)
    {R : Type*} [AddCommMonoid R] [CommMonoid R] (coeff : ℕ → R)
    (weight : Finset α → R) :
    (∑ P : Finpartition s,
        coeff P.parts.card * ∏ B ∈ P.parts, weight B) =
      ∑ B : PointedBlock s a, ∑ Q : Finpartition (s \ B.1),
        coeff (Q.parts.card + 1) *
          (weight B.1 * ∏ D ∈ Q.parts, weight D) := by
  rw [sum_eq_sum_pointedBlock ha]
  apply Fintype.sum_congr
  intro B
  apply Fintype.sum_congr
  intro Q
  rw [card_parts_joinAt, prod_parts_joinAt]

end Finpartition

end CyclicBraidArrangement
