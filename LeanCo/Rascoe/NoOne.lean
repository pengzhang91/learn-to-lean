import LeanCo.Rascoe.Basic

/-!
# Partitions with no part of size one

This file formalizes the two finite bijections used in Lemmas 4.1 and 4.2
of arXiv:2608.30180.  All statements are shifted so that subtraction at the
small values `0` and `1` never enters their types.
-/

open scoped BigOperators

namespace LeanCo.Rascoe

open Nat

/-! ## Removing one occurrence of the part one -/

/-- Partitions containing at least one part of size one. -/
abbrev ContainsOnePartition (n : ℕ) :=
  {p : Nat.Partition n // 1 ∈ p.parts}

/-- Remove one occurrence of `1` from a partition of `n + 1`. -/
def eraseOne {n : ℕ} (p : ContainsOnePartition (n + 1)) : Nat.Partition n := by
  let s := p.1.parts.erase 1
  have hsum : 1 + s.sum = n + 1 := by
    have h := congrArg Multiset.sum (Multiset.cons_erase p.2)
    simpa [s, p.1.parts_sum] using h
  refine ⟨s, ?_, ?_⟩
  · intro k hk
    exact p.1.parts_pos (Multiset.mem_of_mem_erase hk)
  · omega

/-- Adjoin one occurrence of `1` to a partition of `n`. -/
def adjoinOne {n : ℕ} (p : Nat.Partition n) :
    ContainsOnePartition (n + 1) := by
  refine ⟨⟨1 ::ₘ p.parts, ?_, ?_⟩, ?_⟩
  · intro k hk
    rw [Multiset.mem_cons] at hk
    rcases hk with rfl | hk
    · norm_num
    · exact p.parts_pos hk
  · simp [p.parts_sum, add_comm]
  · simp

@[simp] theorem eraseOne_parts {n : ℕ}
    (p : ContainsOnePartition (n + 1)) :
    (eraseOne p).parts = p.1.parts.erase 1 := rfl

@[simp] theorem adjoinOne_parts {n : ℕ} (p : Nat.Partition n) :
    (adjoinOne p).1.parts = 1 ::ₘ p.parts := rfl

theorem eraseOne_adjoinOne {n : ℕ} (p : Nat.Partition n) :
    eraseOne (adjoinOne p) = p := by
  apply Nat.Partition.ext
  simp

theorem adjoinOne_eraseOne {n : ℕ}
    (p : ContainsOnePartition (n + 1)) :
    adjoinOne (eraseOne p) = p := by
  apply Subtype.ext
  apply Nat.Partition.ext
  simpa using Multiset.cons_erase p.2

/-- Removing one `1` is an equivalence between partitions of `n + 1`
containing `1` and arbitrary partitions of `n`. -/
noncomputable def containsOneEquivPartition (n : ℕ) :
    ContainsOnePartition (n + 1) ≃ Nat.Partition n where
  toFun := eraseOne
  invFun := adjoinOne
  left_inv := adjoinOne_eraseOne
  right_inv := eraseOne_adjoinOne

theorem containsOneCard_succ (n : ℕ) :
    Fintype.card (ContainsOnePartition (n + 1)) = partitionNumber n := by
  exact Fintype.card_congr (containsOneEquivPartition n)

/-- The exhaustive split into partitions containing `1` and partitions
with no part equal to `1`. -/
noncomputable def containsOneSumNoOneEquivPartition (n : ℕ) :
    ContainsOnePartition n ⊕ NoOnePartition n ≃ Nat.Partition n :=
  Equiv.sumCompl (fun p : Nat.Partition n ↦ 1 ∈ p.parts)

/-- Lemma 4.1 in subtraction-free form: every partition either contains
`1` or has no part of size `1`. -/
theorem partitionNumber_succ_eq_noOneCard_add (n : ℕ) :
    partitionNumber (n + 1) =
      Fintype.card (NoOnePartition (n + 1)) + partitionNumber n := by
  classical
  have hsplit :
      Fintype.card (ContainsOnePartition (n + 1)) +
          Fintype.card (NoOnePartition (n + 1)) =
        Fintype.card (Nat.Partition (n + 1)) := by
    simpa only [Fintype.card_sum] using Fintype.card_congr
      (containsOneSumNoOneEquivPartition (n + 1))
  calc
    partitionNumber (n + 1) =
        Fintype.card (ContainsOnePartition (n + 1)) +
          Fintype.card (NoOnePartition (n + 1)) := by
      simpa only [partitionNumber] using hsplit.symm
    _ = Fintype.card (NoOnePartition (n + 1)) + partitionNumber n := by
      rw [containsOneCard_succ]
      omega

theorem partitionNumber_succ_eq_noOneNumber_add (n : ℕ) :
    partitionNumber (n + 1) = noOneNumber (n + 1) + partitionNumber n := by
  exact partitionNumber_succ_eq_noOneCard_add n

/-- Lemma 4.1 in the paper's difference form, with the index shifted to
avoid a negative partition-number argument. -/
theorem noOneCard_succ_eq_partitionNumber_sub (n : ℕ) :
    Fintype.card (NoOnePartition (n + 1)) =
      partitionNumber (n + 1) - partitionNumber n := by
  have h := partitionNumber_succ_eq_noOneCard_add n
  omega

theorem noOneNumber_succ_eq_partitionNumber_sub (n : ℕ) :
    noOneNumber (n + 1) = partitionNumber (n + 1) - partitionNumber n := by
  exact noOneCard_succ_eq_partitionNumber_sub n

/-! ## Removing a marked part size and replacing it by ones -/

/-- A no-one partition together with a chosen distinct part size. -/
abbrev MarkedNoOnePartition (n : ℕ) :=
  Sigma fun p : NoOnePartition n ↦ {k : ℕ // k ∈ p.1.parts.toFinset}

theorem markedNoOnePart_ge_two {n : ℕ} (x : MarkedNoOnePartition n) :
    2 ≤ x.2.1 := by
  have hmem : x.2.1 ∈ x.1.1.parts := Multiset.mem_toFinset.mp x.2.2
  have hpos := x.1.1.parts_pos hmem
  have hne : x.2.1 ≠ 1 := by
    intro h
    exact x.1.2 (h ▸ hmem)
  omega

/-- Split a multiset into all of its copies of `1` and the remaining
elements. -/
theorem replicate_count_one_add_filter_ne_one (s : Multiset ℕ) :
    Multiset.replicate (s.count 1) 1 + s.filter (· ≠ 1) = s := by
  rw [← Multiset.filter_eq' s 1]
  exact Multiset.filter_add_not (fun x : ℕ ↦ x = 1) s

/-- Remove one occurrence of the marked size `k` and add `k - 2` ones. -/
def removeMarkedPartAddOnes {n : ℕ}
    (x : MarkedNoOnePartition (n + 2)) : Nat.Partition n := by
  let k := x.2.1
  let rest := x.1.1.parts.erase k
  let s := Multiset.replicate (k - 2) 1 + rest
  have hkmem : k ∈ x.1.1.parts := Multiset.mem_toFinset.mp x.2.2
  have hk : 2 ≤ k := markedNoOnePart_ge_two x
  have hsum : k + rest.sum = n + 2 := by
    have h := congrArg Multiset.sum (Multiset.cons_erase hkmem)
    simpa [rest, x.1.1.parts_sum] using h
  refine ⟨s, ?_, ?_⟩
  · intro a ha
    rw [Multiset.mem_add] at ha
    rcases ha with ha | ha
    · exact (Multiset.eq_of_mem_replicate ha).symm ▸ by norm_num
    · exact x.1.1.parts_pos (Multiset.mem_of_mem_erase ha)
  · rw [show s = Multiset.replicate (k - 2) 1 + rest by rfl,
      Multiset.sum_add]
    have hrep : (Multiset.replicate (k - 2) 1).sum = k - 2 := by simp
    rw [hrep]
    have hk' : k - 2 + 2 = k := Nat.sub_add_cancel hk
    rw [← hk'] at hsum
    omega

/-- Delete all ones and adjoin one marked part whose size is two more than
the number of deleted ones. -/
def removeOnesAdjoinMarked {n : ℕ} (p : Nat.Partition n) :
    MarkedNoOnePartition (n + 2) := by
  let m := p.parts.count 1
  let k := m + 2
  let rest := p.parts.filter (· ≠ 1)
  have hdecomp : Multiset.replicate m 1 + rest = p.parts := by
    simpa [m, rest] using replicate_count_one_add_filter_ne_one p.parts
  have hsum : m + rest.sum = n := by
    have h := congrArg Multiset.sum hdecomp
    simpa [p.parts_sum] using h
  let q : Nat.Partition (n + 2) := by
    refine ⟨k ::ₘ rest, ?_, ?_⟩
    · intro a ha
      rw [Multiset.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [k]
      · exact p.parts_pos (Multiset.mem_of_mem_filter ha)
    · simp only [Multiset.sum_cons]
      dsimp [k]
      omega
  have hqNoOne : HasNoOne q := by
    intro h
    change 1 ∈ k ::ₘ rest at h
    rw [Multiset.mem_cons] at h
    rcases h with h | h
    · simp [k] at h
    · exact (Multiset.of_mem_filter h) rfl
  refine ⟨⟨q, hqNoOne⟩, ⟨k, ?_⟩⟩
  simp [q]

@[simp] theorem removeMarkedPartAddOnes_parts {n : ℕ}
    (x : MarkedNoOnePartition (n + 2)) :
    (removeMarkedPartAddOnes x).parts =
      Multiset.replicate (x.2.1 - 2) 1 + x.1.1.parts.erase x.2.1 := rfl

@[simp] theorem removeOnesAdjoinMarked_parts {n : ℕ}
    (p : Nat.Partition n) :
    (removeOnesAdjoinMarked p).1.1.parts =
      (p.parts.count 1 + 2) ::ₘ p.parts.filter (· ≠ 1) := rfl

@[simp] theorem removeOnesAdjoinMarked_mark {n : ℕ}
    (p : Nat.Partition n) :
    (removeOnesAdjoinMarked p).2.1 = p.parts.count 1 + 2 := rfl

theorem removeMarkedPartAddOnes_removeOnesAdjoinMarked {n : ℕ}
    (p : Nat.Partition n) :
    removeMarkedPartAddOnes (removeOnesAdjoinMarked p) = p := by
  apply Nat.Partition.ext
  simp only [removeMarkedPartAddOnes_parts, removeOnesAdjoinMarked_parts,
    removeOnesAdjoinMarked_mark, Multiset.erase_cons_head, Nat.add_sub_cancel_left]
  exact replicate_count_one_add_filter_ne_one p.parts

theorem removeOnesAdjoinMarked_removeMarkedPartAddOnes {n : ℕ}
    (x : MarkedNoOnePartition (n + 2)) :
    removeOnesAdjoinMarked (removeMarkedPartAddOnes x) = x := by
  let k := x.2.1
  let rest := x.1.1.parts.erase k
  have hkmem : k ∈ x.1.1.parts := Multiset.mem_toFinset.mp x.2.2
  have hk : 2 ≤ k := markedNoOnePart_ge_two x
  have honeRest : 1 ∉ rest := by
    intro h
    exact x.1.2 (Multiset.mem_of_mem_erase h)
  have hcount : (removeMarkedPartAddOnes x).parts.count 1 = k - 2 := by
    simp [removeMarkedPartAddOnes_parts, k, rest,
      Multiset.count_eq_zero_of_notMem honeRest]
  have hfilter : (removeMarkedPartAddOnes x).parts.filter (· ≠ 1) = rest := by
    rw [removeMarkedPartAddOnes_parts, Multiset.filter_add]
    have hrep : (Multiset.replicate (k - 2) 1).filter (· ≠ 1) = 0 := by
      rw [Multiset.filter_eq_nil]
      intro a ha
      simpa [Multiset.eq_of_mem_replicate ha]
    have hrest : rest.filter (· ≠ 1) = rest := by
      rw [Multiset.filter_eq_self]
      intro a ha hEq
      apply honeRest
      simpa [hEq] using ha
    simpa [k, rest, hrep, hrest]
  have hkback : (removeMarkedPartAddOnes x).parts.count 1 + 2 = k := by
    rw [hcount]
    omega
  have hbase : (removeOnesAdjoinMarked (removeMarkedPartAddOnes x)).1 = x.1 := by
    apply Subtype.ext
    apply Nat.Partition.ext
    rw [removeOnesAdjoinMarked_parts, hkback, hfilter]
    exact Multiset.cons_erase hkmem
  apply Sigma.ext hbase
  apply (Subtype.heq_iff_coe_eq (fun a ↦ by rw [hbase])).2
  exact hkback

/-- Lemma 4.2's bijection: a no-one partition of `n + 2` with a marked
distinct part size is equivalent to an arbitrary partition of `n`. -/
noncomputable def markedNoOneEquivPartition (n : ℕ) :
    MarkedNoOnePartition (n + 2) ≃ Nat.Partition n where
  toFun := removeMarkedPartAddOnes
  invFun := removeOnesAdjoinMarked
  left_inv := removeOnesAdjoinMarked_removeMarkedPartAddOnes
  right_inv := removeMarkedPartAddOnes_removeOnesAdjoinMarked

/-- Lemma 4.2: the total number of distinct part sizes over all no-one
partitions of `n + 2` is the partition number `p(n)`. -/
theorem sum_distinctPartSizes_noOne_add_two (n : ℕ) :
    (∑ p : NoOnePartition (n + 2), distinctPartSizes p.1) =
      partitionNumber n := by
  classical
  have hcard :
      Fintype.card
          (Sigma fun p : NoOnePartition (n + 2) ↦
            {k : ℕ // k ∈ p.1.parts.toFinset}) =
        Fintype.card (Nat.Partition n) :=
    Fintype.card_congr (markedNoOneEquivPartition n)
  rw [Fintype.card_sigma] at hcard
  have hfiber (p : NoOnePartition (n + 2)) :
      Fintype.card {k : ℕ // k ∈ p.1.parts.toFinset} =
        distinctPartSizes p.1 := by
    exact Fintype.card_coe p.1.parts.toFinset
  simp_rw [hfiber] at hcard
  simpa only [partitionNumber] using hcard

end LeanCo.Rascoe
