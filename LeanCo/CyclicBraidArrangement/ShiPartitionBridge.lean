import LeanCo.CyclicBraidArrangement.PartitionIdentitiesDirect

/-!
# From the Hurwitz subset identity to the Shi partition sum

This file closes the induction that evaluates the set-partition sum used in
Corollary 4.4.  The only polynomial input is the directly proved Hurwitz
subset identity in `ShiPartitionIdentityDirect`.
-/

namespace CyclicBraidArrangement

open scoped BigOperators
open Polynomial

noncomputable section

namespace Finpartition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A block containing `a` is equivalently recorded by its complement in
`S`; that complement is an arbitrary subset of `S.erase a`. -/
def pointedBlockEquivTail (S : Finset ι) (a : ι) (ha : a ∈ S) :
    PointedBlock S a ≃ {T : Finset ι // T ∈ (S.erase a).powerset} where
  toFun B := ⟨S \ B.1, by
    rw [Finset.mem_powerset]
    intro i hi
    have hiS : i ∈ S := (Finset.mem_sdiff.mp hi).1
    have hiB : i ∉ B.1 := (Finset.mem_sdiff.mp hi).2
    exact Finset.mem_erase.mpr ⟨by
      intro hia
      subst i
      exact hiB B.2.1, hiS⟩⟩
  invFun T := ⟨S \ T.1, by
    constructor
    · exact Finset.mem_sdiff.mpr ⟨ha, by
        intro haT
        have := Finset.mem_powerset.mp T.2 haT
        exact (Finset.mem_erase.mp this).1 rfl⟩
    · exact Finset.sdiff_subset⟩
  left_inv B := by
    apply Subtype.ext
    ext i
    have hBS : i ∈ B.1 → i ∈ S := fun hi ↦ B.2.2 hi
    simp only [Finset.mem_sdiff]
    aesop
  right_inv T := by
    apply Subtype.ext
    ext i
    have hTS : i ∈ T.1 → i ∈ S := fun hi ↦
      Finset.mem_of_mem_erase (Finset.mem_powerset.mp T.2 hi)
    simp only [Finset.mem_sdiff]
    aesop

end Finpartition

namespace ShiPartitionBridge

open ShiPartitionIdentityDirect

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem eval_abelBlockPoly (x : ι → ℚ) (T : Finset ι) (u : ℚ) :
    eval u (abelBlockPoly x T) =
      if T = ∅ then 1 else u * (u + ∑ i ∈ T, x i) ^ (T.card - 1) := by
  by_cases hT : T = ∅
  · simp [abelBlockPoly, hT]
  · simp only [abelBlockPoly, if_neg hT, eval_mul, eval_X, eval_pow,
      eval_add, eval_C]

theorem sum_pointedBlock_eq_eval_hurwitz
    (S : Finset ι) (a : ι) (ha : a ∈ S) (u : ℚ) (x : ι → ℚ)
    (hsmall : ∀ T : Finset ι, T ⊂ S →
      abelPartitionSumOn T (u - 1) x =
        if T = ∅ then 1 else
          (u - 1) * ((u - 1) + ∑ i ∈ T, x i) ^ (T.card - 1)) :
    (∑ B : Finpartition.PointedBlock S a,
        (1 + ∑ i ∈ B.1, x i) ^ (B.1.card - 1) *
          abelPartitionSumOn (S \ B.1) (u - 1) x) =
      eval (u - 1)
        (hurwitzSubsetPoly x (S.erase a) (1 + x a)) := by
  classical
  let e := Finpartition.pointedBlockEquivTail S a ha
  rw [Fintype.sum_equiv e
    (fun B : Finpartition.PointedBlock S a ↦
      (1 + ∑ i ∈ B.1, x i) ^ (B.1.card - 1) *
        abelPartitionSumOn (S \ B.1) (u - 1) x)
    (fun T : {T : Finset ι // T ∈ (S.erase a).powerset} ↦
      eval (u - 1) (abelBlockPoly x T.1) *
        (1 + x a + ∑ i ∈ (S.erase a) \ T.1, x i) ^
          ((S.erase a) \ T.1).card) ?_]
  · rw [hurwitzSubsetPoly, eval_finset_sum]
    rw [← (S.erase a).powerset.sum_attach]
    apply Finset.sum_congr rfl
    intro T hT
    simp only [eval_mul, eval_C]
  · intro B
    have htailSub : S \ B.1 ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
      intro heq
      have haTail : a ∈ S \ B.1 := heq.symm ▸ ha
      exact (Finset.mem_sdiff.mp haTail).2 B.2.1
    rw [hsmall (S \ B.1) htailSub]
    change
      (1 + ∑ i ∈ B.1, x i) ^ (B.1.card - 1) *
          (if S \ B.1 = ∅ then 1 else
            (u - 1) * ((u - 1) + ∑ i ∈ S \ B.1, x i) ^
              ((S \ B.1).card - 1)) = _
    rw [eval_abelBlockPoly]
    have htail : (e B).1 = S \ B.1 := rfl
    have hcomp : (S.erase a) \ (S \ B.1) = B.1.erase a := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hia, hiS⟩, hnot⟩
        refine ⟨hia, ?_⟩
        by_contra hiB
        exact hnot ⟨hiS, hiB⟩
      · rintro ⟨hia, hiB⟩
        exact ⟨⟨hia, B.2.2 hiB⟩, fun h ↦ h.2 hiB⟩
    have hsumB :
        (∑ i ∈ B.1, x i) = x a + ∑ i ∈ B.1.erase a, x i := by
      rw [← Finset.sum_erase_add _ _ B.2.1]
      ring
    have hcardB : B.1.card - 1 = (B.1.erase a).card := by
      rw [Finset.card_erase_of_mem B.2.1]
    rw [htail, hcomp, hsumB, hcardB]
    split_ifs <;> ring

/-- The Abel set-partition sum has its closed form on every finite carrier. -/
theorem abelPartitionSumOn_closed
    (S : Finset ι) (u : ℚ) (x : ι → ℚ) :
    abelPartitionSumOn S u x =
      if S = ∅ then 1 else u * (u + ∑ i ∈ S, x i) ^ (S.card - 1) := by
  classical
  induction S using Finset.strongInduction generalizing u with
  | H S ih =>
      by_cases hS : S = ∅
      · subst S
        letI : Unique (Finpartition (∅ : Finset ι)) := by
          change Unique (Finpartition (⊥ : Finset ι))
          infer_instance
        unfold abelPartitionSumOn
        rw [Fintype.sum_unique]
        have hp : (default : Finpartition (∅ : Finset ι)).parts = ∅ :=
          Finpartition.parts_eq_empty_iff.mpr rfl
        simp [hp]
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        rw [abelPartitionSumOn_rec S a ha]
        rw [sum_pointedBlock_eq_eval_hurwitz S a ha u x]
        · rw [hurwitzSubsetPoly_eq]
          simp only [eval_pow, eval_add, eval_X, eval_C]
          have hsum : x a + ∑ i ∈ S.erase a, x i = ∑ i ∈ S, x i := by
            rw [add_comm, Finset.sum_erase_add _ _ ha]
          have hcard : (S.erase a).card = S.card - 1 := by
            rw [Finset.card_erase_of_mem ha]
          rw [hcard, if_neg hS]
          congr 2
          linear_combination hsum
        · intro T hTS
          exact ih T hTS (u - 1)

/-- Finite-index form used by the Shi convolution statements. -/
theorem abelPartitionSum_closed {n : ℕ} [NeZero n]
    (u : ℚ) (x : Fin n → ℚ) :
    abelPartitionSum u x = u * (u + ∑ i, x i) ^ (n - 1) := by
  rw [abelPartitionSum_eq_on, abelPartitionSumOn_closed]
  have hne : (Finset.univ : Finset (Fin n)) ≠ ∅ :=
    Finset.univ_nonempty.ne_empty
  rw [if_neg hne]
  simp

private theorem neg_one_sign_cancel {n : ℕ} (hn : n ≠ 0) :
    (-1 : ℚ) ^ n * (-1) * (-1) ^ (n - 1) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Nat.succ_sub_one, pow_succ]
  have hsquare : ((-1 : ℚ) ^ k) * ((-1 : ℚ) ^ k) = 1 := by
    rw [← pow_add]
    norm_num [show k + k = 2 * k by omega, pow_mul]
  linear_combination hsquare

/-- The region expansion in Corollary 4.4, with no convolution premise. -/
theorem shiPartitionPolynomialValue_eq_regionConvolution_direct
    {n : ℕ} [NeZero n] (α : Fin n → ℕ) (t : ℚ) :
    shiPartitionPolynomialValue α t =
      regionConvolution t (shiRegionBlock α) := by
  rw [regionConvolution_shi_eq_abelPartitionSum,
    abelPartitionSum_closed]
  unfold shiPartitionPolynomialValue
  have hx :
      (∑ i, ((α i : ℚ) + 1)) = (∑ i, α i : ℕ) + (n : ℚ) := by
    rw [Finset.sum_add_distrib]
    push_cast
    simp
  rw [hx]
  have hbase :
      -t + ((∑ i, α i : ℕ) + (n : ℚ)) =
        -(t - (∑ i, α i : ℕ) - n) := by
    push_cast
    ring
  have hpow :
      (-t + ((∑ i, α i : ℕ) + (n : ℚ))) ^ (n - 1) =
        (-1 : ℚ) ^ (n - 1) *
          (t - (∑ i, α i : ℕ) - n) ^ (n - 1) := by
    rw [hbase, neg_pow]
  rw [hpow]
  have hsign := neg_one_sign_cancel (n := n) (NeZero.ne n)
  calc
    t * (t - (∑ i, α i) - n) ^ (n - 1) =
        1 * t * (t - (∑ i, α i) - n) ^ (n - 1) := by ring
    _ = ((-1 : ℚ) ^ n * (-1) * (-1) ^ (n - 1)) * t *
        (t - (∑ i, α i) - n) ^ (n - 1) := by rw [hsign]
    _ = (-1 : ℚ) ^ n *
        (-t * ((-1 : ℚ) ^ (n - 1) *
          (t - (∑ i, α i) - n) ^ (n - 1))) := by ring

/-- After negating the vertex parameters, an Abel block is the bounded-Shi
block together with its blockwise sign. -/
theorem abelBlockWeight_neg_eq_cast_shiBoundedBlock
    {n : ℕ} (α : Fin n → ℕ) (B : Finset (Fin n)) (hB : B.Nonempty) :
    abelBlockWeight (fun i ↦ -((α i : ℚ) + 1)) B =
      (-1 : ℚ) ^ (B.card - 1) * (shiBoundedBlock α B : ℚ) := by
  have hcard : 1 ≤ B.card := Finset.one_le_card.mpr hB
  have hle : 1 ≤ blockParameterSum α B + B.card := by omega
  have hcastBase :
      ((blockParameterSum α B + B.card - 1 : ℕ) : ℚ) =
        (blockParameterSum α B : ℚ) + (B.card : ℚ) - 1 := by
    rw [Nat.cast_sub hle]
    push_cast
    rfl
  have hbase :
      1 + ∑ i ∈ B, -((α i : ℚ) + 1) =
        -((blockParameterSum α B : ℚ) + (B.card : ℚ) - 1) := by
    unfold blockParameterSum
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
    push_cast
    simp
    ring
  unfold abelBlockWeight shiBoundedBlock
  rw [hbase, neg_pow, Nat.cast_pow, hcastBase]

theorem prod_abelBlockWeight_neg_eq_shiBounded
    {n : ℕ} (α : Fin n → ℕ) (P : SetPartition n) :
    (∏ B ∈ P.parts,
        abelBlockWeight (fun i ↦ -((α i : ℚ) + 1)) B) =
      (-1 : ℚ) ^ (n - P.parts.card) *
        (partitionBlockProduct (shiBoundedBlock α) P : ℚ) := by
  classical
  have hsum : (∑ B ∈ P.parts, (B.card - 1)) = n - P.parts.card := by
    rw [Finset.sum_tsub_distrib]
    · rw [P.sum_card_parts]
      simp
    · intro B hB
      exact Finset.one_le_card.mpr (P.nonempty_of_mem_parts hB)
  calc
    (∏ B ∈ P.parts,
        abelBlockWeight (fun i ↦ -((α i : ℚ) + 1)) B) =
        ∏ B ∈ P.parts,
          ((-1 : ℚ) ^ (B.card - 1) * (shiBoundedBlock α B : ℚ)) := by
      apply Finset.prod_congr rfl
      intro B hB
      exact abelBlockWeight_neg_eq_cast_shiBoundedBlock α B
        (P.nonempty_of_mem_parts hB)
    _ = (∏ B ∈ P.parts, (-1 : ℚ) ^ (B.card - 1)) *
        ∏ B ∈ P.parts, (shiBoundedBlock α B : ℚ) := by
      rw [Finset.prod_mul_distrib]
    _ = (-1 : ℚ) ^ (n - P.parts.card) *
        ∏ B ∈ P.parts, (shiBoundedBlock α B : ℚ) := by
      rw [Finset.prod_pow_eq_pow_sum, hsum]
    _ = _ := by
      unfold partitionBlockProduct
      push_cast
      rfl

theorem boundedConvolution_shi_eq_abelPartitionSum
    {n : ℕ} [NeZero n] (α : Fin n → ℕ) (t : ℚ) :
    boundedConvolution t (shiBoundedBlock α) =
      abelPartitionSum t (fun i ↦ -((α i : ℚ) + 1)) := by
  classical
  rw [boundedConvolution_eq_partitionFallingSum]
  unfold abelPartitionSum
  apply Finset.sum_congr rfl
  intro P hP
  rw [prod_abelBlockWeight_neg_eq_shiBounded α P]
  ring

/-- The bounded-region expansion in Corollary 4.4, with no convolution
premise. -/
theorem shiPartitionPolynomialValue_eq_boundedConvolution_direct
    {n : ℕ} [NeZero n] (α : Fin n → ℕ) (t : ℚ) :
    shiPartitionPolynomialValue α t =
      boundedConvolution t (shiBoundedBlock α) := by
  rw [boundedConvolution_shi_eq_abelPartitionSum,
    abelPartitionSum_closed]
  unfold shiPartitionPolynomialValue
  have hx :
      (∑ i, -((α i : ℚ) + 1)) =
        -((∑ i, α i : ℕ) + (n : ℚ)) := by
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
    push_cast
    simp
  rw [hx]
  congr 2
  push_cast
  ring

/-- Corollary 4.4 in the exact two-equality form used by the paper. -/
theorem shi_partition_convolutions_direct
    {n : ℕ} [NeZero n] (α : Fin n → ℕ) (t : ℚ) :
    shiPartitionPolynomialValue α t =
        regionConvolution t (shiRegionBlock α) ∧
      regionConvolution t (shiRegionBlock α) =
        boundedConvolution t (shiBoundedBlock α) := by
  have hr := shiPartitionPolynomialValue_eq_regionConvolution_direct α t
  have hb := shiPartitionPolynomialValue_eq_boundedConvolution_direct α t
  exact ⟨hr, hr.symm.trans hb⟩

end ShiPartitionBridge

end

end CyclicBraidArrangement
