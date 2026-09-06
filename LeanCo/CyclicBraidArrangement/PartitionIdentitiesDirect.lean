import LeanCo.CyclicBraidArrangement.PartitionWeights
import LeanCo.CyclicBraidArrangement.FinpartitionBlockDecomposition
import LeanCo.CyclicBraidArrangement.ShiPartitionIdentityDirect
import Mathlib.Data.Finset.Grade

/-!
# Direct algebraic checks for the partition identities

This file develops the partition identities of Corollaries 4.4 and 4.5
without packaging either identity as an external convolution hypothesis.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

private theorem factorial_mul_generalizedChoose (x : ℚ) (k : ℕ) :
    (k.factorial : ℚ) * generalizedChoose x k =
      ∏ i ∈ Finset.range k, (x - i) := by
  rw [generalizedChoose]
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- Falling factorial over `ℚ`, kept separate from `generalizedChoose` so
the partition sum has no division. -/
def rationalFallingFactorial (x : ℚ) (k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, (x - i)

@[simp] theorem rationalFallingFactorial_zero (x : ℚ) :
    rationalFallingFactorial x 0 = 1 := by
  simp [rationalFallingFactorial]

theorem rationalFallingFactorial_succ (x : ℚ) (k : ℕ) :
    rationalFallingFactorial x (k + 1) =
      x * rationalFallingFactorial (x - 1) k := by
  induction k with
  | zero => simp [rationalFallingFactorial]
  | succ k ih =>
      simp only [rationalFallingFactorial, Finset.prod_range_succ] at ih ⊢
      rw [ih]
      push_cast
      ring

private theorem factorial_mul_generalizedChoose_eq_falling
    (x : ℚ) (k : ℕ) :
    (k.factorial : ℚ) * generalizedChoose x k =
      rationalFallingFactorial x k :=
  factorial_mul_generalizedChoose x k

/-- A single sum over set partitions, equivalent to the nested sum by the
number of blocks in the region convolution. -/
noncomputable def partitionFallingSum {n : ℕ} (x : ℚ)
    (weight : Finset (Fin n) → ℕ) : ℚ :=
  ∑ P : SetPartition n,
    rationalFallingFactorial x P.parts.card *
      (partitionBlockProduct weight P : ℚ)

private theorem parts_card_mem_Icc {n : ℕ} [NeZero n]
    (P : SetPartition n) : P.parts.card ∈ Finset.Icc 1 n := by
  simp only [Finset.mem_Icc]
  constructor
  · exact Finset.one_le_card.mpr (P.parts_nonempty Finset.univ_nonempty.ne_empty)
  · simpa using P.card_parts_le_card

/-- Remove the artificial grouping by the number of blocks from the region
convolution.  This is valid in every positive rank and uses no combinatorial
identity about the special block weights. -/
theorem regionConvolution_eq_partitionFallingSum {n : ℕ} [NeZero n]
    (t : ℚ) (weight : Finset (Fin n) → ℕ) :
    regionConvolution t weight =
      (-1 : ℚ) ^ n * partitionFallingSum (-t) weight := by
  classical
  unfold regionConvolution partitionFallingSum partitionBlockSumRat
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.sum_eq_single P.parts.card]
  · simp [factorial_mul_generalizedChoose_eq_falling]
  · intro ℓ hℓ hne
    simp [hne, hne.symm]
  · intro hnot
    exact (hnot (parts_card_mem_Icc P)).elim

/-- The analogous single-partition form of the bounded convolution. -/
theorem boundedConvolution_eq_partitionFallingSum {n : ℕ} [NeZero n]
    (t : ℚ) (weight : Finset (Fin n) → ℕ) :
    boundedConvolution t weight =
      ∑ P : SetPartition n,
        (-1 : ℚ) ^ (n - P.parts.card) *
          rationalFallingFactorial t P.parts.card *
          (partitionBlockProduct weight P : ℚ) := by
  classical
  unfold boundedConvolution partitionBlockSumRat
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.sum_eq_single P.parts.card]
  · simp only [if_pos]
    calc
      (-1 : ℚ) ^ (n - P.parts.card) * (P.parts.card.factorial : ℚ) *
          generalizedChoose t P.parts.card * (partitionBlockProduct weight P : ℚ) =
          (-1 : ℚ) ^ (n - P.parts.card) *
            ((P.parts.card.factorial : ℚ) * generalizedChoose t P.parts.card) *
            (partitionBlockProduct weight P : ℚ) := by ring
      _ = _ := by rw [factorial_mul_generalizedChoose_eq_falling]
  · intro ℓ hℓ hne
    simp [hne, hne.symm]
  · intro hnot
    exact (hnot (parts_card_mem_Icc P)).elim

/-- The block weight in the multivariate Abel--Hurwitz identity. -/
noncomputable def abelBlockWeight {n : ℕ} (x : Fin n → ℚ)
    (B : Finset (Fin n)) : ℚ :=
  (1 + ∑ i ∈ B, x i) ^ (B.card - 1)

/-- Carrier-general version, used for induction after deleting one block. -/
noncomputable def abelPartitionSumOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (u : ℚ) (x : ι → ℚ) : ℚ :=
  ∑ P : Finpartition S,
    rationalFallingFactorial u P.parts.card *
      ∏ B ∈ P.parts, (1 + ∑ i ∈ B, x i) ^ (B.card - 1)

/-- Splitting off the block containing `a` gives the exact recursion for the
Abel partition sum. -/
theorem abelPartitionSumOn_rec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (a : ι) (ha : a ∈ S) (u : ℚ) (x : ι → ℚ) :
    abelPartitionSumOn S u x =
      u * ∑ B : Finpartition.PointedBlock S a,
        (1 + ∑ i ∈ B.1, x i) ^ (B.1.card - 1) *
          abelPartitionSumOn (S \ B.1) (u - 1) x := by
  classical
  unfold abelPartitionSumOn
  rw [Finpartition.sum_eq_sum_pointedBlock ha]
  simp_rw [Finpartition.card_parts_joinAt,
    rationalFallingFactorial_succ, Finpartition.prod_parts_joinAt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  ring

/-- A pointed block containing `a` is equivalently specified by the
complementary subset of `S.erase a`. -/
noncomputable def pointedBlockEquivPowerset {ι : Type*}
    [DecidableEq ι] {S : Finset ι} {a : ι} (ha : a ∈ S) :
    Finpartition.PointedBlock S a ≃
      {C : Finset ι // C ∈ (S.erase a).powerset} where
  toFun B := ⟨S \ B.1, by
    rw [Finset.mem_powerset]
    intro i hi
    have hi' := Finset.mem_sdiff.mp hi
    exact Finset.mem_erase.mpr
      ⟨fun hia ↦ hi'.2 (hia ▸ B.2.1), hi'.1⟩⟩
  invFun C := ⟨S \ C.1, by
    constructor
    · rw [Finset.mem_sdiff]
      exact ⟨ha, fun hac ↦
        (Finset.mem_erase.mp (Finset.mem_powerset.mp C.2 hac)).1 rfl⟩
    · exact Finset.sdiff_subset⟩
  left_inv B := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hiS, hn⟩
      by_contra hiB
      exact hn ⟨hiS, hiB⟩
    · intro hiB
      exact ⟨B.2.2 hiB, fun h ↦ h.2 hiB⟩
  right_inv C := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_sdiff]
    have hCS : C.1 ⊆ S := fun _ hi ↦
      (Finset.mem_erase.mp (Finset.mem_powerset.mp C.2 hi)).2
    constructor
    · rintro ⟨hiS, hn⟩
      by_contra hiC
      exact hn ⟨hiS, hiC⟩
    · intro hiC
      exact ⟨hCS hiC, fun h ↦ h.2 hiC⟩

/-- The multivariate Abel--Hurwitz partition identity.  This is the generic
closed form needed for both Shi convolution evaluations; all of its inputs
are arbitrary rational parameters. -/
theorem abelPartitionSumOn_closed {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Finset ι) (u : ℚ) (x : ι → ℚ) :
    abelPartitionSumOn S u x =
      if S = ∅ then 1 else
        u * (u + ∑ i ∈ S, x i) ^ (S.card - 1) := by
  classical
  induction S using Finset.strongInduction generalizing u with
  | H S ih =>
      by_cases hS : S = ∅
      · subst S
        letI : Unique (Finpartition (∅ : Finset ι)) :=
          { default := ⊥
            uniq := by
              intro P
              apply Finpartition.ext
              ext B
              constructor <;> intro hB
              · obtain ⟨i, hi⟩ := P.nonempty_of_mem_parts hB
                simpa using P.subset hB hi
              · obtain ⟨i, hi⟩ :=
                  (⊥ : Finpartition (∅ : Finset ι)).nonempty_of_mem_parts hB
                simpa using
                  (⊥ : Finpartition (∅ : Finset ι)).subset hB hi }
        rw [abelPartitionSumOn, Fintype.sum_unique]
        have hparts :
            (default : Finpartition (∅ : Finset ι)).parts = ∅ := by
          ext B
          constructor
          · intro hB
            obtain ⟨i, hi⟩ :=
              (default : Finpartition (∅ : Finset ι)).nonempty_of_mem_parts hB
            simpa using
              (default : Finpartition (∅ : Finset ι)).subset hB hi
          · simp
        rw [hparts]
        simp [rationalFallingFactorial]
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        rw [abelPartitionSumOn_rec S a ha, if_neg hS]
        congr 1
        let U := S.erase a
        let e := pointedBlockEquivPowerset ha
        let f : Finpartition.PointedBlock S a → ℚ := fun B ↦
          (1 + ∑ i ∈ B.1, x i) ^ (B.1.card - 1) *
            abelPartitionSumOn (S \ B.1) (u - 1) x
        let g : {C : Finset ι // C ∈ U.powerset} → ℚ := fun C ↦
          (1 + x a + ∑ i ∈ U \ C.1, x i) ^ (U \ C.1).card *
            (if C.1 = ∅ then 1 else
              (u - 1) * ((u - 1) + ∑ i ∈ C.1, x i) ^ (C.1.card - 1))
        have hterm : ∀ B, f B = g (e B) := by
          intro B
          have hproper : S \ B.1 ⊂ S :=
            Finset.sdiff_ssubset B.2.2 ⟨a, B.2.1⟩
          have hi := ih (S \ B.1) hproper (u - 1)
          have herase : U \ (S \ B.1) = B.1.erase a := by
            dsimp only [U]
            ext i
            simp only [Finset.mem_sdiff, Finset.mem_erase]
            constructor
            · rintro ⟨⟨hia, hiS⟩, hn⟩
              exact ⟨hia, by
                by_contra hiB
                exact hn ⟨hiS, hiB⟩⟩
            · rintro ⟨hia, hiB⟩
              exact ⟨⟨hia, B.2.2 hiB⟩, fun h ↦ h.2 hiB⟩
          dsimp only [f, g]
          change
            (1 + ∑ i ∈ B.1, x i) ^ (B.1.card - 1) *
                abelPartitionSumOn (S \ B.1) (u - 1) x =
              (1 + x a + ∑ i ∈ U \ (S \ B.1), x i) ^
                  (U \ (S \ B.1)).card *
                (if S \ B.1 = ∅ then 1 else
                  (u - 1) * ((u - 1) + ∑ i ∈ S \ B.1, x i) ^
                    ((S \ B.1).card - 1))
          rw [hi, herase, Finset.card_erase_of_mem B.2.1,
            ← Finset.sum_erase_add _ _ B.2.1]
          ring
        calc
          (∑ B : Finpartition.PointedBlock S a,
              (1 + ∑ i ∈ B.1, x i) ^ (B.1.card - 1) *
                abelPartitionSumOn (S \ B.1) (u - 1) x) =
              ∑ C : {C : Finset ι // C ∈ U.powerset}, g C :=
            Fintype.sum_equiv e f g hterm
          _ = ∑ C ∈ U.powerset,
              (1 + x a + ∑ i ∈ U \ C, x i) ^ (U \ C).card *
                (if C = ∅ then 1 else
                  (u - 1) * ((u - 1) + ∑ i ∈ C, x i) ^
                    (C.card - 1)) := by
              rw [Finset.sum_subtype U.powerset (by intro; rfl)]
          _ = (1 + x a + (u - 1) + ∑ i ∈ U, x i) ^ U.card := by
              simpa [mul_comm] using
                (ShiPartitionIdentityDirect.hurwitzSubset_identity
                  x U (1 + x a) (u - 1))
          _ = (u + ∑ i ∈ S, x i) ^ (S.card - 1) := by
              dsimp only [U]
              rw [← Finset.sum_erase_add _ _ ha,
                Finset.card_erase_of_mem ha]
              ring_nf

/-- The one master sum whose evaluation yields both Shi identities. -/
noncomputable def abelPartitionSum {n : ℕ} (s : ℚ)
    (x : Fin n → ℚ) : ℚ :=
  ∑ P : SetPartition n,
    rationalFallingFactorial s P.parts.card *
      ∏ B ∈ P.parts, abelBlockWeight x B

theorem abelPartitionSum_eq_on {n : ℕ} (s : ℚ) (x : Fin n → ℚ) :
    abelPartitionSum s x = abelPartitionSumOn Finset.univ s x := by
  rfl

theorem cast_shiRegionBlock_eq_abelBlockWeight {n : ℕ}
    (α : Fin n → ℕ) (B : Finset (Fin n)) :
    (shiRegionBlock α B : ℚ) =
      abelBlockWeight (fun i ↦ (α i : ℚ) + 1) B := by
  unfold shiRegionBlock abelBlockWeight blockParameterSum
  push_cast
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- The Shi region convolution is literally the positive-parameter instance
of the Abel partition sum, before evaluating that master sum. -/
theorem partitionFallingSum_shiRegion_eq_abelPartitionSum
    {n : ℕ} (s : ℚ) (α : Fin n → ℕ) :
    partitionFallingSum s (shiRegionBlock α) =
      abelPartitionSum s (fun i ↦ (α i : ℚ) + 1) := by
  classical
  unfold partitionFallingSum abelPartitionSum partitionBlockProduct
  apply Finset.sum_congr rfl
  intro P hP
  congr 1
  push_cast
  apply Finset.prod_congr rfl
  intro B hB
  exact cast_shiRegionBlock_eq_abelBlockWeight α B

/-- Consequently, Corollary 4.4's region side has been reduced in every
positive rank to the single multivariate Abel--Hurwitz evaluation. -/
theorem regionConvolution_shi_eq_abelPartitionSum {n : ℕ} [NeZero n]
    (α : Fin n → ℕ) (t : ℚ) :
    regionConvolution t (shiRegionBlock α) =
      (-1 : ℚ) ^ n *
        abelPartitionSum (-t) (fun i ↦ (α i : ℚ) + 1) := by
  rw [regionConvolution_eq_partitionFallingSum,
    partitionFallingSum_shiRegion_eq_abelPartitionSum]

theorem partitionBlockSumRat_fin_one (weight : Finset (Fin 1) → ℕ) :
    partitionBlockSumRat 1 weight = weight Finset.univ := by
  classical
  have hatom : IsAtom (Finset.univ : Finset (Fin 1)) := by
    rw [show (Finset.univ : Finset (Fin 1)) = {0} by ext i; fin_cases i; simp]
    exact Finset.isAtom_singleton 0
  letI : Unique (SetPartition 1) :=
    @IsAtom.uniqueFinpartition _ _ _ _ (Finpartition.indiscrete hatom.1) hatom
  unfold partitionBlockSumRat partitionBlockProduct
  rw [Fintype.sum_unique]
  rw [show (default : SetPartition 1) = Finpartition.indiscrete hatom.1 from rfl]
  simp [Finpartition.indiscrete]

/-- Both Shi convolution expressions are direct identities in rank one. -/
theorem shi_partition_convolutions_fin_one (α : Fin 1 → ℕ) (t : ℚ) :
    shiPartitionPolynomialValue α t =
        regionConvolution t (shiRegionBlock α) ∧
      regionConvolution t (shiRegionBlock α) =
        boundedConvolution t (shiBoundedBlock α) := by
  simp [shiPartitionPolynomialValue, regionConvolution, boundedConvolution,
    partitionBlockSumRat_fin_one, generalizedChoose]

/-- Both braid convolution expressions are direct identities in rank one. -/
theorem braid_partition_convolutions_fin_one (α : Fin 1 → ℕ) (t : ℚ) :
    braidPartitionPolynomialValue α t =
        regionConvolution t (braidRegionBlock α) ∧
      regionConvolution t (braidRegionBlock α) =
        boundedConvolution t (braidBoundedBlock α) := by
  simp [braidPartitionPolynomialValue, regionConvolution, boundedConvolution,
    partitionBlockSumRat_fin_one, generalizedChoose]

private noncomputable def indiscreteTwo : SetPartition 2 :=
  Finpartition.indiscrete (Finset.univ_nonempty.ne_empty)

private theorem setPartition_fin_two_cases (P : SetPartition 2) :
    P = ⊥ ∨ P = indiscreteTwo := by
  classical
  revert P
  decide

private theorem univ_setPartition_fin_two :
    (Finset.univ : Finset (SetPartition 2)) = {⊥, indiscreteTwo} := by
  classical
  ext P
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact setPartition_fin_two_cases P

private theorem bottomParts_fin_two :
    (⊥ : SetPartition 2).parts = {{0}, {1}} := by
  decide

private theorem bottom_ne_indiscreteTwo :
    (⊥ : SetPartition 2) ≠ indiscreteTwo := by
  intro h
  have hc := congrArg (fun P : SetPartition 2 ↦ P.parts.card) h
  simpa [indiscreteTwo, Finpartition.indiscrete, bottomParts_fin_two] using hc

private theorem indiscreteTwo_parts :
    indiscreteTwo.parts = {Finset.univ} := by
  rfl

theorem partitionBlockSumRat_fin_two_one
    (weight : Finset (Fin 2) → ℕ) :
    partitionBlockSumRat 1 weight = weight Finset.univ := by
  classical
  unfold partitionBlockSumRat partitionBlockProduct
  rw [univ_setPartition_fin_two]
  simp [indiscreteTwo, Finpartition.indiscrete]

theorem partitionBlockSumRat_fin_two_two
    (weight : Finset (Fin 2) → ℕ) :
    partitionBlockSumRat 2 weight = weight {0} * weight {1} := by
  classical
  unfold partitionBlockSumRat partitionBlockProduct
  rw [univ_setPartition_fin_two]
  rw [Finset.sum_insert (by simpa using bottom_ne_indiscreteTwo)]
  rw [Finset.sum_singleton, bottomParts_fin_two, indiscreteTwo_parts]
  norm_num

/-- Both Shi convolution expressions, proved without a convolution-law
hypothesis, in rank two. -/
theorem shi_partition_convolutions_fin_two (α : Fin 2 → ℕ) (t : ℚ) :
    shiPartitionPolynomialValue α t =
        regionConvolution t (shiRegionBlock α) ∧
      regionConvolution t (shiRegionBlock α) =
        boundedConvolution t (shiBoundedBlock α) := by
  simp only [regionConvolution, boundedConvolution]
  rw [show Finset.Icc 1 2 = {1, 2} by decide]
  simp only [Finset.sum_insert (by decide : 1 ∉ ({2} : Finset ℕ)),
    Finset.sum_singleton, partitionBlockSumRat_fin_two_one,
    partitionBlockSumRat_fin_two_two]
  simp [shiPartitionPolynomialValue, shiRegionBlock, shiBoundedBlock,
    blockParameterSum, generalizedChoose, Finset.prod_range_succ]
  constructor <;> ring

/-- Both braid convolution expressions, proved without a convolution-law
hypothesis, in rank two. -/
theorem braid_partition_convolutions_fin_two (α : Fin 2 → ℕ) (t : ℚ) :
    braidPartitionPolynomialValue α t =
        regionConvolution t (braidRegionBlock α) ∧
      regionConvolution t (braidRegionBlock α) =
        boundedConvolution t (braidBoundedBlock α) := by
  simp only [regionConvolution, boundedConvolution]
  rw [show Finset.Icc 1 2 = {1, 2} by decide]
  simp only [Finset.sum_insert (by decide : 1 ∉ ({2} : Finset ℕ)),
    Finset.sum_singleton, partitionBlockSumRat_fin_two_one,
    partitionBlockSumRat_fin_two_two]
  simp [braidPartitionPolynomialValue, braidRegionBlock, braidBoundedBlock,
    risingFactorial, blockParameterSum, generalizedChoose, Finset.prod_range_succ]
  constructor <;> ring

/-! Rank three is still small enough that the five set partitions can be
classified in the kernel.  These lemmas are also useful regression tests for
the general Abel--Hurwitz identity needed in arbitrary rank. -/

private def partitionThree01 : SetPartition 3 where
  parts := {{0, 1}, {2}}
  supIndep := by decide
  sup_parts := by decide
  bot_notMem := by decide

private def partitionThree02 : SetPartition 3 where
  parts := {{0, 2}, {1}}
  supIndep := by decide
  sup_parts := by decide
  bot_notMem := by decide

private def partitionThree12 : SetPartition 3 where
  parts := {{1, 2}, {0}}
  supIndep := by decide
  sup_parts := by decide
  bot_notMem := by decide

private def indiscreteThree : SetPartition 3 :=
  Finpartition.indiscrete Finset.univ_nonempty.ne_empty

private theorem parts_eq_fin_three (P : SetPartition 3) :
    P.parts = {P.part 0, P.part 1, P.part 2} := by
  classical
  ext B
  constructor
  · intro hB
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hB
    have heq := P.part_eq_of_mem hB hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    fin_cases x
    · exact Or.inl heq.symm
    · exact Or.inr (Or.inl heq.symm)
    · exact Or.inr (Or.inr heq.symm)
  · intro hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with hB | hB | hB <;> subst B
    · exact P.part_mem.2 (by simp)
    · exact P.part_mem.2 (by simp)
    · exact P.part_mem.2 (by simp)

private theorem bottomParts_fin_three :
    (⊥ : SetPartition 3).parts = {{0}, {1}, {2}} := by
  decide

@[simp] private theorem partitionThree01_parts :
    partitionThree01.parts = {{0, 1}, {2}} := rfl

@[simp] private theorem partitionThree02_parts :
    partitionThree02.parts = {{0, 2}, {1}} := rfl

@[simp] private theorem partitionThree12_parts :
    partitionThree12.parts = {{1, 2}, {0}} := rfl

@[simp] private theorem indiscreteThree_parts :
    indiscreteThree.parts = {Finset.univ} := rfl

@[simp] private theorem card_parts_partitionThree01 :
    partitionThree01.parts.card = 2 := by decide

@[simp] private theorem card_parts_partitionThree02 :
    partitionThree02.parts.card = 2 := by decide

@[simp] private theorem card_parts_partitionThree12 :
    partitionThree12.parts.card = 2 := by decide

@[simp] private theorem card_parts_bottomThree :
    (⊥ : SetPartition 3).parts.card = 3 := by decide

@[simp] private theorem card_parts_indiscreteThree :
    indiscreteThree.parts.card = 1 := by decide

@[simp] private theorem card_literal_partitionThree01 :
    ({{0, 1}, {2}} : Finset (Finset (Fin 3))).card = 2 := by decide

@[simp] private theorem card_literal_partitionThree02 :
    ({{0, 2}, {1}} : Finset (Finset (Fin 3))).card = 2 := by decide

@[simp] private theorem card_literal_partitionThree12 :
    ({{1, 2}, {0}} : Finset (Finset (Fin 3))).card = 2 := by decide

private theorem setPartition_fin_three_cases (P : SetPartition 3) :
    P = ⊥ ∨ P = partitionThree01 ∨ P = partitionThree02 ∨
      P = partitionThree12 ∨ P = indiscreteThree := by
  classical
  have hrel (a b : Fin 3) :
      a ∈ P.part b ↔ P.part a = P.part b :=
    P.mem_part_iff_part_eq_part (by simp) (by simp)
  by_cases h01 : (1 : Fin 3) ∈ P.part 0
  · have e10 : P.part 1 = P.part 0 := (hrel 1 0).1 h01
    by_cases h02 : (2 : Fin 3) ∈ P.part 0
    · have e20 : P.part 2 = P.part 0 := (hrel 2 0).1 h02
      have hp0 : P.part 0 = Finset.univ := by
        ext x
        fin_cases x <;> simp [h01, h02]
      right; right; right; right
      apply Finpartition.ext
      rw [parts_eq_fin_three, indiscreteThree_parts, e10, e20, hp0]
      simp
    · have ne20 : P.part 2 ≠ P.part 0 := fun e ↦ h02 ((hrel 2 0).2 e)
      have hp0 : P.part 0 = {0, 1} := by
        ext x
        fin_cases x <;> simp [h01, h02]
      have hp2 : P.part 2 = {2} := by
        ext x
        fin_cases x <;> simp [hrel, e10, ne20, ne20.symm]
      right; left
      apply Finpartition.ext
      rw [parts_eq_fin_three, partitionThree01_parts, e10, hp0, hp2]
      simp
  · have ne10 : P.part 1 ≠ P.part 0 := fun e ↦ h01 ((hrel 1 0).2 e)
    by_cases h02 : (2 : Fin 3) ∈ P.part 0
    · have e20 : P.part 2 = P.part 0 := (hrel 2 0).1 h02
      have hp0 : P.part 0 = {0, 2} := by
        ext x
        fin_cases x <;> simp [h01, h02]
      have hp1 : P.part 1 = {1} := by
        ext x
        fin_cases x <;> simp [hrel, e20, ne10, ne10.symm]
      right; right; left
      apply Finpartition.ext
      rw [parts_eq_fin_three, partitionThree02_parts, e20, hp0, hp1]
      ext B
      simp [or_comm]
    · have ne20 : P.part 2 ≠ P.part 0 := fun e ↦ h02 ((hrel 2 0).2 e)
      by_cases h12 : (2 : Fin 3) ∈ P.part 1
      · have e21 : P.part 2 = P.part 1 := (hrel 2 1).1 h12
        have hp0 : P.part 0 = {0} := by
          ext x
          fin_cases x <;> simp [h01, h02]
        have hp1 : P.part 1 = {1, 2} := by
          ext x
          fin_cases x <;> simp [hrel, e21, ne10, ne10.symm, h12]
        right; right; right; left
        apply Finpartition.ext
        rw [parts_eq_fin_three, partitionThree12_parts, e21, hp0, hp1]
        ext B
        simp [or_comm]
      · have ne21 : P.part 2 ≠ P.part 1 := fun e ↦ h12 ((hrel 2 1).2 e)
        have hp0 : P.part 0 = {0} := by
          ext x
          fin_cases x <;> simp [h01, h02]
        have hp1 : P.part 1 = {1} := by
          ext x
          fin_cases x <;> simp [hrel, ne10, ne10.symm, ne21, ne21.symm]
        have hp2 : P.part 2 = {2} := by
          ext x
          fin_cases x <;> simp [hrel, ne20, ne20.symm, ne21, ne21.symm]
        left
        apply Finpartition.ext
        rw [parts_eq_fin_three, bottomParts_fin_three, hp0, hp1, hp2]

private theorem univ_setPartition_fin_three :
    (Finset.univ : Finset (SetPartition 3)) =
      {⊥, partitionThree01, partitionThree02, partitionThree12, indiscreteThree} := by
  classical
  ext P
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact setPartition_fin_three_cases P

private theorem partitionsThree_pairwise_ne :
    (⊥ : SetPartition 3) ≠ partitionThree01 ∧
    (⊥ : SetPartition 3) ≠ partitionThree02 ∧
    (⊥ : SetPartition 3) ≠ partitionThree12 ∧
    (⊥ : SetPartition 3) ≠ indiscreteThree ∧
    partitionThree01 ≠ partitionThree02 ∧
    partitionThree01 ≠ partitionThree12 ∧
    partitionThree01 ≠ indiscreteThree ∧
    partitionThree02 ≠ partitionThree12 ∧
    partitionThree02 ≠ indiscreteThree ∧
    partitionThree12 ≠ indiscreteThree := by
  decide

private theorem prod_pair {R : Type*} [CommMonoid R]
    (f : Finset (Fin 3) → R) (A B : Finset (Fin 3)) (hAB : A ≠ B) :
    ∏ C ∈ ({A, B} : Finset (Finset (Fin 3))), f C = f A * f B := by
  rw [Finset.prod_insert (by simpa using hAB), Finset.prod_singleton]

@[simp] private theorem prod_literal_partitionThree01 {R : Type*} [CommMonoid R]
    (f : Finset (Fin 3) → R) :
    ∏ C ∈ ({{0, 1}, {2}} : Finset (Finset (Fin 3))), f C =
      f {0, 1} * f {2} :=
  prod_pair f {0, 1} {2} (by decide)

@[simp] private theorem prod_literal_partitionThree02 {R : Type*} [CommMonoid R]
    (f : Finset (Fin 3) → R) :
    ∏ C ∈ ({{0, 2}, {1}} : Finset (Finset (Fin 3))), f C =
      f {0, 2} * f {1} :=
  prod_pair f {0, 2} {1} (by decide)

@[simp] private theorem prod_literal_partitionThree12 {R : Type*} [CommMonoid R]
    (f : Finset (Fin 3) → R) :
    ∏ C ∈ ({{1, 2}, {0}} : Finset (Finset (Fin 3))), f C =
      f {1, 2} * f {0} :=
  prod_pair f {1, 2} {0} (by decide)

theorem partitionBlockSumRat_fin_three_one
    (weight : Finset (Fin 3) → ℕ) :
    partitionBlockSumRat 1 weight = weight Finset.univ := by
  classical
  unfold partitionBlockSumRat partitionBlockProduct
  rw [univ_setPartition_fin_three]
  rcases partitionsThree_pairwise_ne with
    ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  simp [h01, h02, h03, h04, h12, h13, h14, h23, h24, h34,
    Fin.prod_univ_three, prod_pair]

theorem partitionBlockSumRat_fin_three_two
    (weight : Finset (Fin 3) → ℕ) :
    partitionBlockSumRat 2 weight =
      weight {0, 1} * weight {2} +
      weight {0, 2} * weight {1} +
      weight {1, 2} * weight {0} := by
  classical
  unfold partitionBlockSumRat partitionBlockProduct
  rw [univ_setPartition_fin_three]
  rcases partitionsThree_pairwise_ne with
    ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  simp [h01, h02, h03, h04, h12, h13, h14, h23, h24, h34,
    Fin.prod_univ_three, prod_pair]
  ring

theorem partitionBlockSumRat_fin_three_three
    (weight : Finset (Fin 3) → ℕ) :
    partitionBlockSumRat 3 weight =
      weight {0} * weight {1} * weight {2} := by
  classical
  unfold partitionBlockSumRat partitionBlockProduct
  rw [univ_setPartition_fin_three]
  rcases partitionsThree_pairwise_ne with
    ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  simp [h01, h02, h03, h04, h12, h13, h14, h23, h24, h34,
    Fin.prod_univ_three, prod_pair]

/-- Corollary 4.4, checked directly through all five set partitions in rank
three.  No arrangement or convolution-law hypothesis occurs. -/
theorem shi_partition_convolutions_fin_three (α : Fin 3 → ℕ) (t : ℚ) :
    shiPartitionPolynomialValue α t =
        regionConvolution t (shiRegionBlock α) ∧
      regionConvolution t (shiRegionBlock α) =
        boundedConvolution t (shiBoundedBlock α) := by
  simp only [regionConvolution, boundedConvolution]
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]
  simp only [Finset.sum_insert (by decide : 1 ∉ ({2, 3} : Finset ℕ)),
    Finset.sum_insert (by decide : 2 ∉ ({3} : Finset ℕ)),
    Finset.sum_singleton, partitionBlockSumRat_fin_three_one,
    partitionBlockSumRat_fin_three_two, partitionBlockSumRat_fin_three_three]
  simp [shiPartitionPolynomialValue, shiRegionBlock, shiBoundedBlock,
    blockParameterSum, generalizedChoose, Finset.prod_range_succ,
    Fin.sum_univ_three]
  constructor <;> ring

/-- Corollary 4.5, checked directly through all five set partitions in rank
three.  No arrangement or convolution-law hypothesis occurs. -/
theorem braid_partition_convolutions_fin_three (α : Fin 3 → ℕ) (t : ℚ) :
    braidPartitionPolynomialValue α t =
        regionConvolution t (braidRegionBlock α) ∧
      regionConvolution t (braidRegionBlock α) =
        boundedConvolution t (braidBoundedBlock α) := by
  simp only [regionConvolution, boundedConvolution]
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]
  simp only [Finset.sum_insert (by decide : 1 ∉ ({2, 3} : Finset ℕ)),
    Finset.sum_insert (by decide : 2 ∉ ({3} : Finset ℕ)),
    Finset.sum_singleton, partitionBlockSumRat_fin_three_one,
    partitionBlockSumRat_fin_three_two, partitionBlockSumRat_fin_three_three]
  simp [braidPartitionPolynomialValue, braidRegionBlock, braidBoundedBlock,
    risingFactorial, blockParameterSum, generalizedChoose,
    Finset.prod_range_succ, Fin.sum_univ_three]
  constructor <;> ring

end CyclicBraidArrangement
