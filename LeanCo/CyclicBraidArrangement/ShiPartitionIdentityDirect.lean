import LeanCo.CyclicBraidArrangement.PartitionWeights
import LeanCo.CyclicBraidArrangement.FinpartitionBlockDecomposition
import Mathlib.Algebra.Polynomial.Derivative

/-!
# A direct Abel--Hurwitz proof of the Shi partition identities

This file proves the polynomial identity behind Corollary 4.4 without taking
the partition-convolution formula as a premise.  The key input is proved here:
Hurwitz's multivariate subset identity, obtained by induction after
differentiating in one distinguished variable.
-/

namespace CyclicBraidArrangement

open scoped BigOperators
open Polynomial

namespace ShiPartitionIdentityDirect

noncomputable section

/-- The Abel polynomial attached to a finite block, regarded as a polynomial
in its root parameter.  The empty block has the continuous value `1`. -/
def abelBlockPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (S : Finset ι) : ℚ[X] :=
  if S = ∅ then 1 else
    X * (X + C (∑ i ∈ S, x i)) ^ (S.card - 1)

/-- The right side of Hurwitz's subset identity. -/
def hurwitzSubsetPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a : ℚ) : ℚ[X] :=
  ∑ S ∈ U.powerset,
    abelBlockPoly x S * C ((a + ∑ i ∈ U \ S, x i) ^ (U \ S).card)

@[simp] theorem abelBlockPoly_empty {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) : abelBlockPoly x ∅ = 1 := by
  simp [abelBlockPoly]

@[simp] theorem abelBlockPoly_singleton {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (i : ι) : abelBlockPoly x {i} = X := by
  simp [abelBlockPoly]

/-- Differentiating a block Abel polynomial amounts to choosing one element
of the block and shifting the root parameter by its weight. -/
theorem derivative_abelBlockPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (S : Finset ι) :
    derivative (abelBlockPoly x S) =
      ∑ i ∈ S, (abelBlockPoly x (S.erase i)).comp (X + C (x i)) := by
  classical
  by_cases hS : S = ∅
  · simp [hS, abelBlockPoly]
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨k, hk⟩
  cases k with
  | zero =>
      have hcard : S.card = 1 := by omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      simp [abelBlockPoly]
  | succ k =>
      have hcard : S.card = k + 2 := by omega
      rw [abelBlockPoly, if_neg hS, derivative_mul, derivative_X,
        derivative_pow]
      simp only [one_mul, derivative_add, derivative_X, derivative_C,
        add_zero, mul_one]
      have herase_ne : ∀ i ∈ S, S.erase i ≠ ∅ := by
        intro i hi hempty
        have hc : (S.erase i).card = 0 := Finset.card_eq_zero.mpr hempty
        simp [Finset.card_erase_of_mem hi, hcard] at hc
      have hsum (i : ι) (hi : i ∈ S) :
          (∑ j ∈ S.erase i, x j) + x i = ∑ j ∈ S, x j := by
        rw [Finset.sum_erase_add _ _ hi]
      have hterm (i : ι) (hi : i ∈ S) :
          (abelBlockPoly x (S.erase i)).comp (X + C (x i)) =
            (X + C (x i)) * (X + C (∑ j ∈ S, x j)) ^ k := by
        rw [abelBlockPoly, if_neg (herase_ne i hi), mul_comp, X_comp,
          pow_comp, add_comp, X_comp, C_comp,
          Finset.card_erase_of_mem hi, hcard]
        rw [← hsum i hi]
        congr 2
        simp only [map_add, C_comp]
        ring
      rw [Finset.sum_congr rfl hterm]
      rw [hcard]
      rw [← Finset.sum_mul]
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [← map_sum]
      rw [hcard]
      norm_num
      ring

/-- Subsets containing `i`, with `i` erased, are exactly the subsets of
`U.erase i`.  This weighted form is used to rearrange the derivative. -/
theorem sum_powerset_filter_erase {ι M : Type*} [DecidableEq ι]
    [AddCommMonoid M] (U : Finset ι) {i : ι} (hi : i ∈ U)
    (f : Finset ι → M) :
    (∑ S ∈ U.powerset, if i ∈ S then f (S.erase i) else 0) =
      ∑ T ∈ (U.erase i).powerset, f T := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun T _ ↦ insert i T) ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    constructor
    · exact Finset.insert_subset hi (fun _ hj ↦ Finset.mem_of_mem_erase (hT hj))
    · exact Finset.mem_insert_self i T
  · intro A hA B hB hab
    have hiA : i ∉ A := Finset.notMem_of_mem_powerset_of_notMem hA (by simp)
    have hiB : i ∉ B := Finset.notMem_of_mem_powerset_of_notMem hB (by simp)
    have := congrArg (Finset.erase · i) hab
    simpa [hiA, hiB] using this
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    refine ⟨S.erase i, ?_, ?_⟩
    · exact Finset.mem_powerset.mpr (Finset.erase_subset_erase i hS.1)
    · exact Finset.insert_erase hS.2
  · intro T hT
    have hit : i ∉ T := Finset.notMem_of_mem_powerset_of_notMem hT (by simp)
    simp [hit]

/-- The incidence pairs `(S,i)` with `S ⊆ U` are equivalently indexed by an
element `i ∈ U` and a subset of `U.erase i`. -/
theorem sum_powerset_sum_erase {ι M : Type*} [DecidableEq ι]
    [AddCommMonoid M] (U : Finset ι) (f : ι → Finset ι → M) :
    (∑ S ∈ U.powerset, ∑ i ∈ S, f i (S.erase i)) =
      ∑ i ∈ U, ∑ T ∈ (U.erase i).powerset, f i T := by
  classical
  calc
    (∑ S ∈ U.powerset, ∑ i ∈ S, f i (S.erase i)) =
        ∑ S ∈ U.powerset, ∑ i ∈ U,
          if i ∈ S then f i (S.erase i) else 0 := by
            apply Finset.sum_congr rfl
            intro S hS
            have hSU : S ⊆ U := Finset.mem_powerset.mp hS
            rw [← Finset.sum_filter]
            apply Finset.sum_congr
            · ext i
              simp [hSU]
            · intro i hii
              simp only [Finset.mem_filter] at hii
              simp [hii.2]
    _ = ∑ i ∈ U, ∑ S ∈ U.powerset,
          if i ∈ S then f i (S.erase i) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i ∈ U, ∑ T ∈ (U.erase i).powerset, f i T := by
            apply Finset.sum_congr rfl
            intro i hi
            exact sum_powerset_filter_erase U hi (f i)

/-- Derivative recurrence for the Hurwitz subset sum. -/
theorem derivative_hurwitzSubsetPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a : ℚ) :
    derivative (hurwitzSubsetPoly x U a) =
      ∑ i ∈ U, (hurwitzSubsetPoly x (U.erase i) a).comp (X + C (x i)) := by
  classical
  rw [hurwitzSubsetPoly, derivative_sum]
  simp_rw [derivative_mul, derivative_C, mul_zero, add_zero,
    derivative_abelBlockPoly, Finset.sum_mul]
  let f : ι → Finset ι → ℚ[X] := fun i T ↦
    (abelBlockPoly x T).comp (X + C (x i)) *
      C ((a + ∑ j ∈ U \ insert i T, x j) ^ (U \ insert i T).card)
  have hreindex :
      (∑ S ∈ U.powerset,
        ∑ i ∈ S, (abelBlockPoly x (S.erase i)).comp (X + C (x i)) *
          C ((a + ∑ j ∈ U \ S, x j) ^ (U \ S).card)) =
        ∑ i ∈ U, ∑ T ∈ (U.erase i).powerset, f i T := by
    calc
      _ = ∑ S ∈ U.powerset, ∑ i ∈ S, f i (S.erase i) := by
        apply Finset.sum_congr rfl
        intro S hS
        apply Finset.sum_congr rfl
        intro i hi
        simp only [f]
        rw [Finset.insert_erase hi]
      _ = _ := sum_powerset_sum_erase U f
  rw [hreindex]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hurwitzSubsetPoly, sum_comp]
  apply Finset.sum_congr rfl
  intro T hT
  rw [mul_comp, C_comp]
  simp only [f]
  have hset : U \ insert i T = U.erase i \ T := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    aesop
  rw [hset]

theorem eval_zero_abelBlockPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (S : Finset ι) :
    eval 0 (abelBlockPoly x S) = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅ <;> simp [abelBlockPoly, hS]

theorem eval_abelBlockPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (S : Finset ι) (b : ℚ) :
    eval b (abelBlockPoly x S) =
      if S = ∅ then 1 else b * (b + ∑ i ∈ S, x i) ^ (S.card - 1) := by
  by_cases hS : S = ∅
  · simp [abelBlockPoly, hS]
  · rw [abelBlockPoly, if_neg hS, if_neg hS, eval_mul, eval_X,
      eval_pow, eval_add, eval_X, eval_C]

theorem eval_zero_hurwitzSubsetPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a : ℚ) :
    eval 0 (hurwitzSubsetPoly x U a) =
      (a + ∑ i ∈ U, x i) ^ U.card := by
  classical
  rw [hurwitzSubsetPoly, eval_finset_sum]
  simp_rw [eval_mul, eval_zero_abelBlockPoly, eval_C]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro S hS hSne
    simp [hSne]
  · simp

/-- Hurwitz's multivariate subset identity, as an equality of polynomials in
the second root parameter. -/
theorem hurwitzSubsetPoly_eq {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a : ℚ) :
    hurwitzSubsetPoly x U a =
      (X + C (a + ∑ i ∈ U, x i)) ^ U.card := by
  classical
  induction U using Finset.strongInduction with
  | H U ih =>
      by_cases hU : U = ∅
      · simp [hU, hurwitzSubsetPoly]
      have hcard : 0 < U.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU)
      let q : ℚ[X] := (X + C (a + ∑ i ∈ U, x i)) ^ U.card
      have hterm (i : ι) (hi : i ∈ U) :
          (hurwitzSubsetPoly x (U.erase i) a).comp (X + C (x i)) =
            (X + C (a + ∑ j ∈ U, x j)) ^ (U.card - 1) := by
        rw [ih (U.erase i) (Finset.erase_ssubset hi)]
        rw [pow_comp, Finset.card_erase_of_mem hi]
        apply congrArg (fun p : ℚ[X] ↦ p ^ (U.card - 1))
        simp only [add_comp, X_comp, C_comp]
        rw [← Finset.sum_erase_add _ _ hi]
        simp only [map_add]
        ring
      have hd : derivative (hurwitzSubsetPoly x U a) = derivative q := by
        rw [derivative_hurwitzSubsetPoly]
        rw [Finset.sum_congr rfl hterm]
        rw [Finset.sum_const, nsmul_eq_mul]
        dsimp only [q]
        rw [derivative_pow]
        simp only [derivative_add, derivative_X, derivative_C, add_zero, mul_one]
        simp
      have hzero : eval 0 (hurwitzSubsetPoly x U a) = eval 0 q := by
        rw [eval_zero_hurwitzSubsetPoly]
        simp only [q, eval_pow, eval_add, eval_X, eval_C, zero_add]
      have hdz : derivative (hurwitzSubsetPoly x U a - q) = 0 := by
        rw [derivative_sub, hd, sub_self]
      have hc : (hurwitzSubsetPoly x U a - q).coeff 0 = 0 := by
        rw [coeff_zero_eq_eval_zero, eval_sub, hzero, sub_self]
      have heq := eq_C_of_derivative_eq_zero hdz
      rw [hc, C_0] at heq
      exact sub_eq_zero.mp heq

/-- Evaluation form of the multivariate Hurwitz identity. -/
theorem hurwitzSubset_identity {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a b : ℚ) :
    (∑ S ∈ U.powerset,
      (if S = ∅ then 1 else b * (b + ∑ i ∈ S, x i) ^ (S.card - 1)) *
        (a + ∑ i ∈ U \ S, x i) ^ (U \ S).card) =
      (a + b + ∑ i ∈ U, x i) ^ U.card := by
  have h := congrArg (eval b) (hurwitzSubsetPoly_eq x U a)
  simp only [hurwitzSubsetPoly] at h
  rw [eval_finset_sum] at h
  simp only [eval_mul, eval_C, eval_pow, eval_add,
    eval_X, eval_abelBlockPoly] at h
  simpa [add_assoc, add_left_comm, add_comm] using h

/-- Rational falling factorial used as the root-label coefficient. -/
def rootFalling (u : ℚ) (k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, (u - i)

@[simp] theorem rootFalling_zero (u : ℚ) : rootFalling u 0 = 1 := by
  simp [rootFalling]

theorem rootFalling_succ (u : ℚ) (k : ℕ) :
    rootFalling u (k + 1) = u * rootFalling (u - 1) k := by
  induction k with
  | zero => simp [rootFalling]
  | succ k ih =>
      simp only [rootFalling, Finset.prod_range_succ] at ih ⊢
      rw [ih]
      push_cast
      ring

/-- The Abel-weighted partition sum on an arbitrary finite carrier. -/
def abelPartitionSumOnDirect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (u : ℚ) (x : ι → ℚ) : ℚ :=
  ∑ P : Finpartition S,
    rootFalling u P.parts.card *
      ∏ B ∈ P.parts, (1 + ∑ i ∈ B, x i) ^ (B.card - 1)

/-- Exact pointed-block recurrence for the Abel partition sum. -/
theorem abelPartitionSumOnDirect_rec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (a : ι) (ha : a ∈ S) (u : ℚ) (x : ι → ℚ) :
    abelPartitionSumOnDirect S u x =
      u * ∑ B : Finpartition.PointedBlock S a,
        (1 + ∑ i ∈ B.1, x i) ^ (B.1.card - 1) *
          abelPartitionSumOnDirect (S \ B.1) (u - 1) x := by
  classical
  unfold abelPartitionSumOnDirect
  rw [Finpartition.sum_eq_sum_pointedBlock ha]
  simp_rw [Finpartition.card_parts_joinAt, rootFalling_succ,
    Finpartition.prod_parts_joinAt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  ring

end

end ShiPartitionIdentityDirect

end CyclicBraidArrangement
