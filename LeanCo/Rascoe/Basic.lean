import Mathlib

/-!
# Integer partitions and Rascoe statistics

This file fixes the literal finite objects used in arXiv:2608.30180.
A partition is mathlib's `Nat.Partition`: a multiset of positive natural
numbers with prescribed sum.  Thus no ordering convention for a displayed
partition is built into any theorem.
-/

open scoped BigOperators

namespace LeanCo.Rascoe

open Nat

/-- The number of parts of an integer partition. -/
def length {n : ℕ} (p : Nat.Partition n) : ℕ := p.parts.card

/-- A Rascoe partition is one whose number of parts occurs as a part. -/
def IsRascoe {n : ℕ} (p : Nat.Partition n) : Prop := length p ∈ p.parts

/-- A non-Rascoe partition is one whose number of parts does not occur as a part. -/
def IsNonRascoe {n : ℕ} (p : Nat.Partition n) : Prop := length p ∉ p.parts

/-- A partition with no part of size one. -/
def HasNoOne {n : ℕ} (p : Nat.Partition n) : Prop := 1 ∉ p.parts

/-- Partitions of `n` satisfying the unrestricted Rascoe condition. -/
abbrev RascoePartition (n : ℕ) := {p : Nat.Partition n // IsRascoe p}

/-- Partitions of `n` satisfying the unrestricted non-Rascoe condition. -/
abbrev NonRascoePartition (n : ℕ) := {p : Nat.Partition n // IsNonRascoe p}

/-- Partitions of `n` with no part equal to one. -/
abbrev NoOnePartition (n : ℕ) := {p : Nat.Partition n // HasNoOne p}

noncomputable instance (n : ℕ) : Fintype (RascoePartition n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : Fintype (NonRascoePartition n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : Fintype (NoOnePartition n) := Fintype.ofFinite _

/-- The ordinary partition number. -/
noncomputable def partitionNumber (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The number `c(n)` of unrestricted Rascoe partitions in the paper. -/
noncomputable def rascoeNumber (n : ℕ) : ℕ := Fintype.card (RascoePartition n)

/-- The number `e(n)` of unrestricted non-Rascoe partitions in the paper. -/
noncomputable def nonRascoeNumber (n : ℕ) : ℕ := Fintype.card (NonRascoePartition n)

/-- The number of partitions of `n` with no part of size one. -/
noncomputable def noOneNumber (n : ℕ) : ℕ := Fintype.card (NoOnePartition n)

/-- The number of distinct part sizes of a partition (the paper's `D`). -/
def distinctPartSizes {n : ℕ} (p : Nat.Partition n) : ℕ := p.parts.toFinset.card

@[simp] theorem length_eq_card {n : ℕ} (p : Nat.Partition n) :
    length p = p.parts.card := rfl

theorem sum_map_succ (s : Multiset ℕ) :
    (s.map Nat.succ).sum = s.sum + s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [ih, Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm]

theorem sum_map_pred_add_card (s : Multiset ℕ)
    (hs : ∀ x ∈ s, 0 < x) :
    (s.map Nat.pred).sum + s.card = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : 0 < a := hs a (by simp)
      have hs' : ∀ x ∈ s, 0 < x := by
        intro x hx
        exact hs x (by simp [hx])
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      calc
        a.pred + (s.map Nat.pred).sum + (s.card + 1) =
            (a.pred + 1) + ((s.map Nat.pred).sum + s.card) := by omega
        _ = a + s.sum := by
          rw [← Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos ha, ih hs']

/-- Remove one occurrence of the length and raise every remaining part by one. -/
def eraseLengthRaise {n : ℕ} (p : RascoePartition (n + 1)) : NoOnePartition n := by
  let r := length p.1
  let s := p.1.parts.erase r
  have hrmem : r ∈ p.1.parts := p.2
  have hcard : s.card + 1 = r := by
    simpa [s, r, length] using Multiset.card_erase_add_one hrmem
  have hsum : s.sum + r = n + 1 := by
    have hp := congrArg Multiset.sum (Multiset.cons_erase hrmem)
    simp only [Multiset.sum_cons, p.1.parts_sum] at hp
    simpa [s, add_comm] using hp
  refine ⟨⟨s.map Nat.succ, ?_, ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hi
    omega
  · rw [sum_map_succ]
    omega
  · intro hOne
    obtain ⟨j, hjmem, hj⟩ := Multiset.mem_map.mp hOne
    have hjpos := p.1.parts_pos (Multiset.mem_of_mem_erase hjmem)
    omega

/-- Lower every part by one and adjoin the new length. -/
def lowerAdjoinLength {n : ℕ} (p : NoOnePartition n) : RascoePartition (n + 1) := by
  let r := p.1.parts.card + 1
  let s := p.1.parts.map Nat.pred
  have hpartsTwo : ∀ x ∈ p.1.parts, 2 ≤ x := by
    intro x hx
    have hxpos := p.1.parts_pos hx
    have hxne : x ≠ 1 := by
      intro h
      exact p.2 (h ▸ hx)
    omega
  have hspos : ∀ x ∈ s, 0 < x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    have hyTwo := hpartsTwo y hy
    simpa [Nat.pred_eq_sub_one] using (show 0 < y - 1 by omega)
  have hsSum : s.sum + p.1.parts.card = n := by
    simpa [s, p.1.parts_sum] using
      sum_map_pred_add_card p.1.parts (fun x hx => p.1.parts_pos hx)
  refine ⟨⟨r ::ₘ s, ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [Multiset.mem_cons] at hi
    rcases hi with rfl | hi
    · simp [r]
    · exact hspos i hi
  · rw [Multiset.sum_cons]
    dsimp [r]
    omega
  · simp [IsRascoe, length, r, s]

@[simp] theorem eraseLengthRaise_parts {n : ℕ} (p : RascoePartition (n + 1)) :
    (eraseLengthRaise p).1.parts =
      (p.1.parts.erase (length p.1)).map Nat.succ := rfl

@[simp] theorem lowerAdjoinLength_parts {n : ℕ} (p : NoOnePartition n) :
    (lowerAdjoinLength p).1.parts =
      (p.1.parts.card + 1) ::ₘ p.1.parts.map Nat.pred := rfl

theorem eraseLengthRaise_lowerAdjoinLength {n : ℕ} (p : NoOnePartition n) :
    eraseLengthRaise (lowerAdjoinLength p) = p := by
  apply Subtype.ext
  apply Nat.Partition.ext
  simp only [eraseLengthRaise_parts, lowerAdjoinLength_parts, length,
    Multiset.card_cons, Multiset.card_map, Multiset.erase_cons_head,
    Multiset.map_map]
  calc
    Multiset.map (Nat.succ ∘ Nat.pred) p.1.parts =
        Multiset.map id p.1.parts := by
      apply Multiset.map_congr rfl
      intro x hx
      have hxpos := p.1.parts_pos hx
      have hxne : x ≠ 1 := by
        intro h
        exact p.2 (h ▸ hx)
      simp only [Function.comp_apply, id_eq]
      simpa [Nat.pred_eq_sub_one] using Nat.succ_pred_eq_of_pos hxpos
    _ = p.1.parts := Multiset.map_id _

theorem lowerAdjoinLength_eraseLengthRaise {n : ℕ} (p : RascoePartition (n + 1)) :
    lowerAdjoinLength (eraseLengthRaise p) = p := by
  apply Subtype.ext
  apply Nat.Partition.ext
  change
    (((p.1.parts.erase (length p.1)).map Nat.succ).card + 1) ::ₘ
        ((p.1.parts.erase (length p.1)).map Nat.succ).map Nat.pred =
      p.1.parts
  simp only [Multiset.card_map, length]
  have hr := Multiset.card_erase_add_one p.2
  simp only [length] at hr
  have hmap :
      ((p.1.parts.erase p.1.parts.card).map Nat.succ).map Nat.pred =
        p.1.parts.erase p.1.parts.card := by
    rw [Multiset.map_map]
    calc
      Multiset.map (Nat.pred ∘ Nat.succ)
          (p.1.parts.erase p.1.parts.card) =
          Multiset.map id (p.1.parts.erase p.1.parts.card) := by
        apply Multiset.map_congr rfl
        intro x hx
        simp
      _ = p.1.parts.erase p.1.parts.card := Multiset.map_id _
  rw [hmap]
  have hcons := Multiset.cons_erase p.2
  exact (congrArg (fun a ↦ a ::ₘ p.1.parts.erase p.1.parts.card) hr).trans hcons

/-- The fundamental Rascoe bijection: remove the length and raise the other parts. -/
noncomputable def rascoeEquivNoOne (n : ℕ) :
    RascoePartition (n + 1) ≃ NoOnePartition n where
  toFun := eraseLengthRaise
  invFun := lowerAdjoinLength
  left_inv := lowerAdjoinLength_eraseLengthRaise
  right_inv := eraseLengthRaise_lowerAdjoinLength

theorem rascoeNumber_succ_eq_noOneCard (n : ℕ) :
    rascoeNumber (n + 1) = Fintype.card (NoOnePartition n) := by
  exact Fintype.card_congr (rascoeEquivNoOne n)

theorem rascoeNumber_succ_eq_noOneNumber (n : ℕ) :
    rascoeNumber (n + 1) = noOneNumber n := by
  exact rascoeNumber_succ_eq_noOneCard n

end LeanCo.Rascoe
