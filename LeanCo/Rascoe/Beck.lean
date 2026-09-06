import LeanCo.Rascoe.NoOne
import LeanCo.Rascoe.CoefficientFormula

/-!
# Beck's rank interpretation of unrestricted non-Rascoe partitions

This file formalizes Section 4 of arXiv:2608.30180 after the two
`NoOnePartition` bijections.  A partition of `2 * n + 2` has the rank used
by Beck precisely when its largest part is `n + 1` plus its number of parts.
Removing that largest part and raising the remaining parts gives a
weight-preserving equivalence, up to the one removed part size, with
partitions of `n` having no part equal to one.
-/

open scoped BigOperators

namespace LeanCo.Rascoe

open Nat

/-! ## Largest parts and the relevant rank -/

/-- The largest part of a partition, with value zero for the empty partition. -/
noncomputable def largestPart {n : ℕ} (p : Nat.Partition n) : ℕ :=
  if h : p.parts.toFinset.Nonempty then p.parts.toFinset.max' h else 0

theorem largestPart_mem_of_parts_ne_zero {n : ℕ} (p : Nat.Partition n)
    (hp : p.parts ≠ 0) : largestPart p ∈ p.parts := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [largestPart, dif_pos hne]
  exact Multiset.mem_toFinset.mp (Finset.max'_mem p.parts.toFinset hne)

theorem part_le_largestPart_of_parts_ne_zero {n : ℕ} (p : Nat.Partition n)
    (hp : p.parts ≠ 0) {a : ℕ} (ha : a ∈ p.parts) : a ≤ largestPart p := by
  have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hp
  rw [largestPart, dif_pos hne]
  exact Finset.le_max' p.parts.toFinset a (Multiset.mem_toFinset.mpr ha)

/-- The usual partition rank, largest part minus number of parts. -/
noncomputable def rank {n : ℕ} (p : Nat.Partition n) : ℤ :=
  (largestPart p : ℤ) - (length p : ℤ)

/-- Subtraction-free form of the condition `rank p = n + 1` for a
partition of `2 * n + 2`. -/
def IsBeckRank (n : ℕ) (p : Nat.Partition (2 * n + 2)) : Prop :=
  largestPart p = n + 1 + length p

/-- Partitions of `2 * n + 2` having rank `n + 1`. -/
abbrev BeckRankPartition (n : ℕ) :=
  {p : Nat.Partition (2 * n + 2) // IsBeckRank n p}

noncomputable instance (n : ℕ) : Fintype (BeckRankPartition n) :=
  Fintype.ofFinite _

theorem isBeckRank_iff_rank_eq (n : ℕ) (p : Nat.Partition (2 * n + 2)) :
    IsBeckRank n p ↔ rank p = (n + 1 : ℕ) := by
  simp only [IsBeckRank, rank, length]
  constructor <;> intro h
  · omega
  · omega

theorem beckRank_parts_ne_zero {n : ℕ} (p : Nat.Partition (2 * n + 2)) :
    p.parts ≠ 0 := by
  intro h
  have hs := p.parts_sum
  simp only [h, Multiset.sum_zero] at hs
  omega

theorem beckRank_largestPart_mem {n : ℕ} (p : Nat.Partition (2 * n + 2)) :
    largestPart p ∈ p.parts :=
  largestPart_mem_of_parts_ne_zero p (beckRank_parts_ne_zero p)

theorem beckRank_part_le_largestPart {n : ℕ}
    (p : Nat.Partition (2 * n + 2)) {a : ℕ} (ha : a ∈ p.parts) :
    a ≤ largestPart p :=
  part_le_largestPart_of_parts_ne_zero p (beckRank_parts_ne_zero p) ha

/-! ## The rank-to-no-one bijection -/

/-- Delete the largest part and raise every remaining part by one. -/
noncomputable def rankToNoOne {n : ℕ} (x : BeckRankPartition n) : NoOnePartition n := by
  let L := largestPart x.1
  let tail := x.1.parts.erase L
  have hLmem : L ∈ x.1.parts := by
    simpa only [L] using beckRank_largestPart_mem x.1
  have hsum : L + tail.sum = 2 * n + 2 := by
    simpa [tail, x.1.parts_sum] using Multiset.sum_erase hLmem
  have hcard : tail.card + 1 = x.1.parts.card := by
    simpa [tail] using Multiset.card_erase_add_one hLmem
  have hrank : L = n + 1 + x.1.parts.card := by
    simpa only [L, IsBeckRank, length] using x.2
  let q : Nat.Partition n := by
    refine ⟨tail.map Nat.succ, ?_, ?_⟩
    · intro i hi
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hi
      omega
    · rw [sum_map_succ]
      omega
  have hno : HasNoOne q := by
    intro h
    change 1 ∈ tail.map Nat.succ at h
    obtain ⟨a, ha, hsucc⟩ := Multiset.mem_map.mp h
    have hapos : 0 < a := x.1.parts_pos (Multiset.mem_of_mem_erase ha)
    omega
  exact ⟨q, hno⟩

/-- Lower every part by one and adjoin the uniquely determined new largest
part. -/
def noOneToRank {n : ℕ} (x : NoOnePartition n) : BeckRankPartition n := by
  let tail := x.1.parts.map Nat.pred
  let L := n + 2 + x.1.parts.card
  have hpartsTwo : ∀ a ∈ x.1.parts, 2 ≤ a := by
    intro a ha
    have hpos := x.1.parts_pos ha
    have hne : a ≠ 1 := by
      intro h
      exact x.2 (h ▸ ha)
    omega
  have hpredpos : ∀ a ∈ x.1.parts, 0 < a.pred := by
    intro a ha
    rw [Nat.pred_eq_sub_one]
    have := hpartsTwo a ha
    omega
  have hsum : tail.sum + x.1.parts.card = n := by
    simpa [tail, x.1.parts_sum] using
      sum_map_pred_add_card x.1.parts (fun a ha => x.1.parts_pos ha)
  let p : Nat.Partition (2 * n + 2) := by
    refine ⟨L ::ₘ tail, ?_, ?_⟩
    · intro a ha
      rw [Multiset.mem_cons] at ha
      rcases ha with rfl | ha
      · dsimp [L]
        omega
      · dsimp [tail] at ha
        obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
        exact hpredpos b hb
    · rw [Multiset.sum_cons]
      dsimp [L]
      omega
  have hLmem : L ∈ p.parts := by simp [p]
  have hmax : largestPart p = L := by
    apply le_antisymm
    · have hpne : p.parts ≠ 0 := beckRank_parts_ne_zero p
      have hne : p.parts.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hpne
      rw [largestPart, dif_pos hne]
      apply (Finset.max'_le_iff p.parts.toFinset hne).2
      intro a ha
      rw [Multiset.mem_toFinset, show p.parts = L ::ₘ tail by rfl,
        Multiset.mem_cons] at ha
      rcases ha with rfl | ha
      · exact le_rfl
      · dsimp [tail] at ha
        obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
        have hb_le : b ≤ n := Nat.Partition.le_of_mem_parts hb
        dsimp [L]
        omega
    · exact beckRank_part_le_largestPart p hLmem
  refine ⟨p, ?_⟩
  rw [IsBeckRank, hmax]
  simp only [length, p, Multiset.card_cons, tail, Multiset.card_map]
  dsimp [L]
  omega

theorem largestPart_noOneToRank {n : ℕ} (x : NoOnePartition n) :
    largestPart (noOneToRank x).1 = n + 2 + x.1.parts.card := by
  have hrank := (noOneToRank x).2
  have hcard : (noOneToRank x).1.parts.card = x.1.parts.card + 1 := by
    simp [noOneToRank]
  simp only [IsBeckRank, length] at hrank
  omega

theorem largestPart_not_mem_erase {n : ℕ} (x : BeckRankPartition n) :
    largestPart x.1 ∉ x.1.parts.erase (largestPart x.1) := by
  intro htwice
  have hfirst := Multiset.sum_erase (beckRank_largestPart_mem x.1)
  have hsecond := Multiset.sum_erase htwice
  rw [x.1.parts_sum] at hfirst
  have hcardpos : 0 < x.1.parts.card :=
    Multiset.card_pos.mpr (beckRank_parts_ne_zero x.1)
  have hrank := x.2
  simp only [IsBeckRank, length] at hrank
  omega

theorem largestPart_count_eq_one {n : ℕ} (x : BeckRankPartition n) :
    x.1.parts.count (largestPart x.1) = 1 := by
  have hm : 0 < x.1.parts.count (largestPart x.1) :=
    Multiset.count_pos.mpr (beckRank_largestPart_mem x.1)
  have he : (x.1.parts.erase (largestPart x.1)).count (largestPart x.1) = 0 :=
    Multiset.count_eq_zero.mpr (largestPart_not_mem_erase x)
  rw [Multiset.count_erase_self] at he
  omega

theorem map_pred_map_succ_of_pos (s : Multiset ℕ)
    (_hs : ∀ a ∈ s, 0 < a) :
    (s.map Nat.succ).map Nat.pred = s := by
  rw [Multiset.map_map]
  calc
    s.map (Nat.pred ∘ Nat.succ) = s.map id := by
      apply Multiset.map_congr rfl
      intro a ha
      simp
    _ = s := Multiset.map_id s

theorem map_succ_map_pred_of_two_le (s : Multiset ℕ)
    (hs : ∀ a ∈ s, 2 ≤ a) :
    (s.map Nat.pred).map Nat.succ = s := by
  rw [Multiset.map_map]
  calc
    s.map (Nat.succ ∘ Nat.pred) = s.map id := by
      apply Multiset.map_congr rfl
      intro a ha
      simp only [Function.comp_apply, id_eq]
      exact Nat.succ_pred (by have := hs a ha; omega)
    _ = s := Multiset.map_id s

theorem noOneToRank_rankToNoOne {n : ℕ} (x : BeckRankPartition n) :
    noOneToRank (rankToNoOne x) = x := by
  apply Subtype.ext
  apply Nat.Partition.ext
  simp only [noOneToRank, rankToNoOne]
  let L := largestPart x.1
  let tail := x.1.parts.erase L
  have hLmem : L ∈ x.1.parts := by
    simpa only [L] using beckRank_largestPart_mem x.1
  have hcard : tail.card + 1 = x.1.parts.card := by
    simpa [tail] using Multiset.card_erase_add_one hLmem
  have hrank : L = n + 1 + x.1.parts.card := by
    simpa only [L, IsBeckRank, length] using x.2
  have htailpos : ∀ a ∈ tail, 0 < a := by
    intro a ha
    exact x.1.parts_pos (Multiset.mem_of_mem_erase ha)
  rw [map_pred_map_succ_of_pos tail htailpos]
  have hnewL : n + 2 + tail.card = L := by omega
  simp only [Multiset.card_map]
  change (n + 2 + tail.card) ::ₘ tail = x.1.parts
  rw [hnewL]
  exact Multiset.cons_erase hLmem

theorem rankToNoOne_noOneToRank {n : ℕ} (x : NoOnePartition n) :
    rankToNoOne (noOneToRank x) = x := by
  apply Subtype.ext
  apply Nat.Partition.ext
  change
    (((noOneToRank x).1.parts.erase (largestPart (noOneToRank x).1)).map
      Nat.succ) = x.1.parts
  rw [largestPart_noOneToRank x]
  change
    (((n + 2 + x.1.parts.card) ::ₘ x.1.parts.map Nat.pred).erase
      (n + 2 + x.1.parts.card)).map Nat.succ = x.1.parts
  rw [Multiset.erase_cons_head]
  apply map_succ_map_pred_of_two_le
  intro a ha
  have hpos := x.1.parts_pos ha
  have hne : a ≠ 1 := by
    intro h
    exact x.2 (h ▸ ha)
  omega

/-- The bijection in Theorem 4.3 between partitions of `2*n+2` of rank
`n+1` and partitions of `n` with no part equal to one. -/
noncomputable def rankWithoutOneEquiv (n : ℕ) :
    BeckRankPartition n ≃ NoOnePartition n where
  toFun := rankToNoOne
  invFun := noOneToRank
  left_inv := noOneToRank_rankToNoOne
  right_inv := rankToNoOne_noOneToRank

/-! ## Transport of the distinct-part-size weight -/

theorem distinctPartSizes_map_succ (s : Multiset ℕ) :
    (s.map Nat.succ).toFinset.card = s.toFinset.card := by
  rw [Multiset.toFinset_map]
  exact Finset.card_image_of_injective s.toFinset Nat.succ_injective

/-- Deleting the unique largest part and raising the other parts removes
exactly one distinct part size. -/
theorem rank_distinctPartSizes {n : ℕ} (x : BeckRankPartition n) :
    distinctPartSizes x.1 = 1 + distinctPartSizes (rankToNoOne x).1 := by
  let L := largestPart x.1
  let tail := x.1.parts.erase L
  have hLmem : L ∈ x.1.parts := by
    simpa only [L] using beckRank_largestPart_mem x.1
  have hLnot : L ∉ tail.toFinset := by
    rw [Multiset.mem_toFinset]
    exact largestPart_not_mem_erase x
  have hparts : x.1.parts = L ::ₘ tail := (Multiset.cons_erase hLmem).symm
  change x.1.parts.toFinset.card = 1 + (tail.map Nat.succ).toFinset.card
  rw [hparts, Multiset.toFinset_cons, Finset.card_insert_of_notMem hLnot]
  rw [distinctPartSizes_map_succ]
  omega

/-- Beck's weighted count `f(n)`. -/
noncomputable def rankPartSizeSum (n : ℕ) : ℕ :=
  ∑ p : BeckRankPartition n, distinctPartSizes p.1

theorem rankPartSizeSum_eq_sum_noOne (n : ℕ) :
    rankPartSizeSum n =
      ∑ p : NoOnePartition n, (1 + distinctPartSizes p.1) := by
  unfold rankPartSizeSum
  apply Fintype.sum_equiv (rankWithoutOneEquiv n)
  intro x
  exact rank_distinctPartSizes x

theorem rankPartSizeSum_eq_noOneNumber_add (n : ℕ) :
    rankPartSizeSum n = noOneNumber n +
      ∑ p : NoOnePartition n, distinctPartSizes p.1 := by
  rw [rankPartSizeSum_eq_sum_noOne, Finset.sum_add_distrib]
  simp [noOneNumber]

/-! ## The shifted partition-number formula -/

/-- `p(n-d)` with the paper's convention that the partition number is zero
at negative arguments.  This avoids the incorrect interpretation of a
negative subscript as truncated natural-number subtraction. -/
noncomputable def shiftedPartitionCount (n d : ℕ) : ℕ :=
  if d ≤ n then partitionNumber (n - d) else 0

@[simp] theorem shiftedPartitionCount_eq_partitionNumber {n d : ℕ}
    (h : d ≤ n) : shiftedPartitionCount n d = partitionNumber (n - d) := by
  simp [shiftedPartitionCount, h]

@[simp] theorem shiftedPartitionCount_eq_zero {n d : ℕ}
    (h : ¬d ≤ n) : shiftedPartitionCount n d = 0 := by
  simp [shiftedPartitionCount, h]

private noncomputable def noOneZeroEquivPartitionZero :
    NoOnePartition 0 ≃ Nat.Partition 0 where
  toFun := Subtype.val
  invFun p := ⟨p, by
    intro h
    rw [Nat.Partition.partition_zero_parts p] at h
    simp at h⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := rfl

private theorem noOneNumber_zero_eq_partitionNumber :
    noOneNumber 0 = partitionNumber 0 := by
  exact Fintype.card_congr noOneZeroEquivPartitionZero

/-- Lemma 4.1 with the negative-index convention made explicit, valid for
every natural `n`. -/
theorem noOneNumber_eq_partitionNumber_sub_shiftedCount (n : ℕ) :
    noOneNumber n = partitionNumber n - shiftedPartitionCount n 1 := by
  cases n with
  | zero =>
      simp [shiftedPartitionCount, noOneNumber_zero_eq_partitionNumber]
  | succ n =>
      simpa [shiftedPartitionCount] using
        noOneNumber_succ_eq_partitionNumber_sub n

private theorem sum_distinctPartSizes_noOne_zero :
    (∑ p : NoOnePartition 0, distinctPartSizes p.1) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  simp [distinctPartSizes]

private theorem sum_distinctPartSizes_noOne_one :
    (∑ p : NoOnePartition 1, distinctPartSizes p.1) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  exfalso
  apply p.2
  rw [Nat.Partition.partition_one_parts p.1]
  simp

/-- Lemma 4.2 with the negative-index convention made explicit, valid for
every natural `n`. -/
theorem sum_distinctPartSizes_noOne_eq_shiftedCount (n : ℕ) :
    (∑ p : NoOnePartition n, distinctPartSizes p.1) =
      shiftedPartitionCount n 2 := by
  rcases n with _ | _ | n
  · simpa [shiftedPartitionCount] using sum_distinctPartSizes_noOne_zero
  · simpa [shiftedPartitionCount] using sum_distinctPartSizes_noOne_one
  · simpa [shiftedPartitionCount, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using sum_distinctPartSizes_noOne_add_two n

/-- The rank-weighted side of Theorem 4.3, with the paper's negative-index
convention represented by `shiftedPartitionCount`. -/
theorem rankPartSizeSum_eq_shiftedPartitionFormula (n : ℕ) :
    rankPartSizeSum n =
      partitionNumber n - shiftedPartitionCount n 1 +
        shiftedPartitionCount n 2 := by
  rw [rankPartSizeSum_eq_noOneNumber_add,
    noOneNumber_eq_partitionNumber_sub_shiftedCount,
    sum_distinctPartSizes_noOne_eq_shiftedCount]

private theorem partitionNumber_one : partitionNumber 1 = 1 := by
  simp [partitionNumber]

private theorem nonRascoeNumber_one_eq_zero : nonRascoeNumber 1 = 0 := by
  have hc : rascoeNumber 1 = noOneNumber 0 := by
    simpa using rascoeNumber_succ_eq_noOneNumber 0
  have hno : noOneNumber 0 = partitionNumber 0 :=
    noOneNumber_zero_eq_partitionNumber
  have hcomp := rascoeNumber_add_nonRascoeNumber 1
  rw [partitionNumber_zero] at hno
  rw [hc, hno, partitionNumber_one] at hcomp
  omega

/-- The unrestricted non-Rascoe count has the same shifted partition-number
formula.  This is the coefficient identity used for the first equality in
Theorem 4.3. -/
theorem nonRascoeNumber_eq_shiftedPartitionFormula (n : ℕ) :
    nonRascoeNumber n =
      partitionNumber n - shiftedPartitionCount n 1 +
        shiftedPartitionCount n 2 := by
  rcases n with _ | _ | n
  · simp [shiftedPartitionCount]
  · simp [shiftedPartitionCount, nonRascoeNumber_one_eq_zero,
      partitionNumber_one]
  · change nonRascoeNumber (n + 2) =
      partitionNumber (n + 2) - shiftedPartitionCount (n + 2) 1 +
        shiftedPartitionCount (n + 2) 2
    simp only [shiftedPartitionCount, if_pos (by omega : 1 ≤ n + 2),
      if_pos (by omega : 2 ≤ n + 2)]
    have hsub1 : n + 2 - 1 = n + 1 := by omega
    have hsub2 : n + 2 - 2 = n := by omega
    rw [hsub1, hsub2]
    exact nonRascoeNumber_add_two_eq_partitionFormula n

/-- Beck's conjectured equality, valid at every natural index. -/
theorem beck_conjecture (n : ℕ) :
    nonRascoeNumber n = rankPartSizeSum n := by
  rw [nonRascoeNumber_eq_shiftedPartitionFormula,
    rankPartSizeSum_eq_shiftedPartitionFormula]

/-- The rank-weighted equality in the paper's displayed `n ≥ 2` notation. -/
theorem rankPartSizeSum_eq_paper_formula {n : ℕ} (hn : 2 ≤ n) :
    rankPartSizeSum n =
      partitionNumber n - partitionNumber (n - 1) + partitionNumber (n - 2) := by
  rw [rankPartSizeSum_eq_shiftedPartitionFormula]
  simp only [shiftedPartitionCount, if_pos (by omega : 1 ≤ n), if_pos hn]

/-- The non-Rascoe equality in the paper's displayed `n ≥ 2` notation. -/
theorem nonRascoeNumber_eq_paper_formula {n : ℕ} (hn : 2 ≤ n) :
    nonRascoeNumber n =
      partitionNumber n - partitionNumber (n - 1) + partitionNumber (n - 2) := by
  exact nonRascoeNumber_eq_partitionFormula hn

/-- The full chain of equalities displayed in Theorem 4.3. -/
theorem beck_theorem_paper_formula {n : ℕ} (hn : 2 ≤ n) :
    nonRascoeNumber n =
        partitionNumber n - partitionNumber (n - 1) + partitionNumber (n - 2) ∧
      partitionNumber n - partitionNumber (n - 1) + partitionNumber (n - 2) =
        rankPartSizeSum n := by
  exact ⟨nonRascoeNumber_eq_paper_formula hn,
    (rankPartSizeSum_eq_paper_formula hn).symm⟩

end LeanCo.Rascoe
