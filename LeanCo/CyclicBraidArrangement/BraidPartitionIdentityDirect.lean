import LeanCo.CyclicBraidArrangement.ShiPartitionIdentityDirect
import Mathlib.Algebra.Polynomial.Roots

/-!
# Direct finite-difference kernel for the braid partition identities

This is the falling-factorial analogue of the Abel--Hurwitz argument in
`ShiPartitionIdentityDirect`.  The ordinary derivative is replaced by the
forward-difference operator.
-/

namespace CyclicBraidArrangement

open scoped BigOperators
open Polynomial

namespace BraidPartitionIdentityDirect

noncomputable section

/-- Falling factorial evaluated in `ℚ`. -/
def fallingValue (z : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => fallingValue z k * (z - k)

@[simp] theorem fallingValue_zero (z : ℚ) : fallingValue z 0 = 1 := rfl

theorem fallingValue_succ (z : ℚ) (k : ℕ) :
    fallingValue z (k + 1) = fallingValue z k * (z - k) := rfl

/-- Falling factorial of an arbitrary polynomial argument. -/
def fallingPoly (p : ℚ[X]) : ℕ → ℚ[X]
  | 0 => 1
  | k + 1 => fallingPoly p k * (p - C (k : ℚ))

@[simp] theorem fallingPoly_zero (p : ℚ[X]) : fallingPoly p 0 = 1 := rfl

theorem fallingPoly_succ (p : ℚ[X]) (k : ℕ) :
    fallingPoly p (k + 1) = fallingPoly p k * (p - C (k : ℚ)) := rfl

theorem eval_fallingPoly (p : ℚ[X]) (k : ℕ) (z : ℚ) :
    eval z (fallingPoly p k) = fallingValue (eval z p) k := by
  induction k with
  | zero => simp [fallingValue]
  | succ k ih =>
      rw [fallingPoly_succ, eval_mul, eval_sub, eval_C, ih,
        fallingValue_succ]

/-- Shifting a falling factorial one unit exposes its leading factor. -/
theorem fallingPoly_add_one_succ (p : ℚ[X]) (k : ℕ) :
    fallingPoly (p + 1) (k + 1) =
      (p + 1) * fallingPoly p k := by
  induction k with
  | zero => simp [fallingPoly]
  | succ k ih =>
      rw [fallingPoly_succ, ih, fallingPoly_succ]
      push_cast
      simp only [map_add, map_one]
      ring

/-- Forward difference of a falling factorial. -/
theorem fallingPoly_forwardDifference (p : ℚ[X]) (k : ℕ) :
    fallingPoly (p + 1) k - fallingPoly p k =
      C (k : ℚ) * fallingPoly p (k - 1) := by
  cases k with
  | zero => simp
  | succ k =>
      rw [fallingPoly_add_one_succ, fallingPoly_succ]
      simp only [Nat.add_sub_cancel]
      push_cast
      simp only [map_add, map_one]
      ring

/-- Substitution commutes with the falling-factorial construction. -/
theorem fallingPoly_comp (p q : ℚ[X]) (k : ℕ) :
    (fallingPoly p k).comp q = fallingPoly (p.comp q) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [fallingPoly_succ, fallingPoly_succ, mul_comp, ih, sub_comp,
        C_comp]

/-- Forward difference in the polynomial variable. -/
def forwardDifference (p : ℚ[X]) : ℚ[X] := p.comp (X + 1) - p

/-- A rational polynomial is determined by its forward difference and its
value at zero. -/
theorem eq_of_forwardDifference_eq_of_eval_zero_eq (p q : ℚ[X])
    (hd : forwardDifference p = forwardDifference q)
    (h0 : eval 0 p = eval 0 q) : p = q := by
  let r : ℚ[X] := p - q
  have hrshift : r.comp (X + 1) = r := by
    dsimp only [forwardDifference] at hd
    dsimp only [r]
    rw [sub_comp]
    apply sub_eq_zero.mp
    linear_combination hd
  have hrzero : eval 0 r = 0 := by
    simp [r, h0]
  have hrnat : ∀ n : ℕ, eval (n : ℚ) r = 0 := by
    intro n
    induction n with
    | zero => exact hrzero
    | succ n ih =>
        have hs := congrArg (eval (n : ℚ)) hrshift
        rw [eval_comp] at hs
        norm_num at hs
        simpa only [Nat.cast_add, Nat.cast_one] using hs.trans ih
  have hinf : Set.Infinite {z : ℚ | IsRoot r z} := by
    have hrange : Set.Infinite (Set.range fun n : ℕ ↦ (n : ℚ)) :=
      Set.infinite_range_of_injective Nat.cast_injective
    apply hrange.mono
    rintro z ⟨n, rfl⟩
    exact hrnat n
  have hr : r = 0 := eq_zero_of_infinite_isRoot r hinf
  exact sub_eq_zero.mp hr

/-- The local falling-factorial block polynomial. -/
def fallingBlockPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (S : Finset ι) : ℚ[X] :=
  if S = ∅ then 1 else
    X * fallingPoly (X + C ((∑ i ∈ S, x i) - 1)) (S.card - 1)

@[simp] theorem fallingBlockPoly_empty {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) : fallingBlockPoly x ∅ = 1 := by
  simp [fallingBlockPoly]

@[simp] theorem fallingBlockPoly_singleton {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (i : ι) : fallingBlockPoly x {i} = X := by
  simp [fallingBlockPoly]

/-- The local deletion recurrence is the exact finite-difference analogue of
`derivative_abelBlockPoly`. -/
theorem forwardDifference_fallingBlockPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (S : Finset ι) :
    forwardDifference (fallingBlockPoly x S) =
      ∑ i ∈ S, (fallingBlockPoly x (S.erase i)).comp (X + C (x i)) := by
  classical
  by_cases hS : S = ∅
  · simp [hS, fallingBlockPoly, forwardDifference]
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨k, hk⟩
  cases k with
  | zero =>
      have hcard : S.card = 1 := by omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      simp [fallingBlockPoly, forwardDifference]
  | succ k =>
      have hcard : S.card = k + 2 := by omega
      have herase_ne : ∀ i ∈ S, S.erase i ≠ ∅ := by
        intro i hi hempty
        have hc : (S.erase i).card = 0 := Finset.card_eq_zero.mpr hempty
        simp [Finset.card_erase_of_mem hi, hcard] at hc
      let p : ℚ[X] := X + C ((∑ i ∈ S, x i) - 1)
      have hpcomp : p.comp (X + 1) = p + 1 := by
        simp only [p, add_comp, X_comp, C_comp]
        ring
      have hterm (i : ι) (hi : i ∈ S) :
          (fallingBlockPoly x (S.erase i)).comp (X + C (x i)) =
            (X + C (x i)) * fallingPoly p k := by
        rw [fallingBlockPoly, if_neg (herase_ne i hi), mul_comp, X_comp,
          fallingPoly_comp, Finset.card_erase_of_mem hi, hcard]
        have hsum : (∑ j ∈ S.erase i, x j) + x i = ∑ j ∈ S, x j := by
          rw [Finset.sum_erase_add _ _ hi]
        congr 2
        simp only [p, add_comp, X_comp, C_comp]
        rw [← hsum]
        simp only [map_sub, map_add]
        ring
      rw [Finset.sum_congr rfl hterm]
      rw [← Finset.sum_mul]
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [← map_sum, hcard]
      unfold forwardDifference fallingBlockPoly
      rw [if_neg hS, mul_comp, X_comp, fallingPoly_comp, hpcomp, hcard]
      have hkminus : k + 2 - 1 = k + 1 := by omega
      rw [hkminus]
      rw [show X + C ((∑ i ∈ S, x i) - 1) = p from rfl]
      rw [fallingPoly_add_one_succ, fallingPoly_succ]
      dsimp only [p]
      push_cast
      simp only [← C_eq_natCast, map_add, map_sub, map_one]
      ring

/-- Subset convolution for falling factorials, polynomial in the root
parameter. -/
def fallingHurwitzSubsetPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a : ℚ) : ℚ[X] :=
  ∑ S ∈ U.powerset,
    fallingBlockPoly x S *
      C (fallingValue (a + ∑ i ∈ U \ S, x i) (U \ S).card)

theorem forwardDifference_fallingHurwitzSubsetPoly
    {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a : ℚ) :
    forwardDifference (fallingHurwitzSubsetPoly x U a) =
      ∑ i ∈ U,
        (fallingHurwitzSubsetPoly x (U.erase i) a).comp (X + C (x i)) := by
  classical
  unfold forwardDifference fallingHurwitzSubsetPoly
  rw [sum_comp]
  simp_rw [mul_comp, C_comp]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  change (∑ S ∈ U.powerset,
      forwardDifference (fallingBlockPoly x S) *
        C (fallingValue (a + ∑ i ∈ U \ S, x i) (U \ S).card)) = _
  simp_rw [forwardDifference_fallingBlockPoly, Finset.sum_mul]
  let f : ι → Finset ι → ℚ[X] := fun i T ↦
    (fallingBlockPoly x T).comp (X + C (x i)) *
      C (fallingValue (a + ∑ j ∈ U \ insert i T, x j)
        (U \ insert i T).card)
  have hreindex :
      (∑ S ∈ U.powerset,
        ∑ i ∈ S, (fallingBlockPoly x (S.erase i)).comp (X + C (x i)) *
          C (fallingValue (a + ∑ j ∈ U \ S, x j) (U \ S).card)) =
        ∑ i ∈ U, ∑ T ∈ (U.erase i).powerset, f i T := by
    calc
      _ = ∑ S ∈ U.powerset, ∑ i ∈ S, f i (S.erase i) := by
        apply Finset.sum_congr rfl
        intro S hS
        apply Finset.sum_congr rfl
        intro i hi
        simp only [f]
        rw [Finset.insert_erase hi]
      _ = _ := ShiPartitionIdentityDirect.sum_powerset_sum_erase U f
  rw [hreindex]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_comp]
  apply Finset.sum_congr rfl
  intro T hT
  rw [mul_comp, C_comp]
  simp only [f]
  have hset : U \ insert i T = U.erase i \ T := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    aesop
  rw [hset]

theorem eval_fallingBlockPoly_zero {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (S : Finset ι) :
    eval 0 (fallingBlockPoly x S) = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅
  · simp [hS, fallingBlockPoly]
  · rw [fallingBlockPoly, if_neg hS, eval_mul, eval_X, zero_mul,
      if_neg hS]

theorem eval_fallingHurwitzSubsetPoly_zero
    {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a : ℚ) :
    eval 0 (fallingHurwitzSubsetPoly x U a) =
      fallingValue (a + ∑ i ∈ U, x i) U.card := by
  classical
  rw [fallingHurwitzSubsetPoly, eval_finset_sum]
  simp_rw [eval_mul, eval_fallingBlockPoly_zero, eval_C]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro S hS hSne
    simp [hSne]
  · simp

/-- Multivariate Chu--Vandermonde/Hurwitz identity for falling factorials. -/
theorem fallingHurwitzSubsetPoly_eq {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a : ℚ) :
    fallingHurwitzSubsetPoly x U a =
      fallingPoly (X + C (a + ∑ i ∈ U, x i)) U.card := by
  classical
  induction U using Finset.strongInduction with
  | H U ih =>
      by_cases hU : U = ∅
      · simp [hU, fallingHurwitzSubsetPoly, fallingPoly]
      let p : ℚ[X] := fallingHurwitzSubsetPoly x U a
      let q : ℚ[X] := fallingPoly (X + C (a + ∑ i ∈ U, x i)) U.card
      have hterm (i : ι) (hi : i ∈ U) :
          (fallingHurwitzSubsetPoly x (U.erase i) a).comp (X + C (x i)) =
            fallingPoly (X + C (a + ∑ j ∈ U, x j)) (U.card - 1) := by
        rw [ih (U.erase i) (Finset.erase_ssubset hi), fallingPoly_comp,
          Finset.card_erase_of_mem hi]
        congr 2
        simp only [add_comp, X_comp, C_comp]
        rw [← Finset.sum_erase_add _ _ hi]
        simp only [map_add]
        ring
      have hp : forwardDifference p =
          C (U.card : ℚ) *
            fallingPoly (X + C (a + ∑ i ∈ U, x i)) (U.card - 1) := by
        dsimp only [p]
        rw [forwardDifference_fallingHurwitzSubsetPoly]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
        simp only [← C_eq_natCast]
      have hq : forwardDifference q =
          C (U.card : ℚ) *
            fallingPoly (X + C (a + ∑ i ∈ U, x i)) (U.card - 1) := by
        dsimp only [q, forwardDifference]
        rw [fallingPoly_comp]
        have hbase :
            (X + C (a + ∑ i ∈ U, x i)).comp (X + 1) =
              (X + C (a + ∑ i ∈ U, x i)) + 1 := by
          simp only [add_comp, X_comp, C_comp]
          ring
        rw [hbase, fallingPoly_forwardDifference]
      apply eq_of_forwardDifference_eq_of_eval_zero_eq p q
      · rw [hp, hq]
      · dsimp only [p, q]
        rw [eval_fallingHurwitzSubsetPoly_zero, eval_fallingPoly]
        simp only [eval_add, eval_X, eval_C, zero_add]

theorem eval_fallingBlockPoly {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (S : Finset ι) (b : ℚ) :
    eval b (fallingBlockPoly x S) =
      if S = ∅ then 1 else
        b * fallingValue (b + (∑ i ∈ S, x i) - 1) (S.card - 1) := by
  by_cases hS : S = ∅
  · simp [hS, fallingBlockPoly]
  · rw [fallingBlockPoly, if_neg hS, if_neg hS, eval_mul, eval_X,
      eval_fallingPoly, eval_add, eval_X, eval_C]
    ring

/-- Evaluation form of the falling-factorial Hurwitz identity. -/
theorem fallingHurwitzSubset_identity {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (U : Finset ι) (a b : ℚ) :
    (∑ S ∈ U.powerset,
      (if S = ∅ then 1 else
        b * fallingValue (b + (∑ i ∈ S, x i) - 1) (S.card - 1)) *
      fallingValue (a + ∑ i ∈ U \ S, x i) (U \ S).card) =
      fallingValue (a + b + ∑ i ∈ U, x i) U.card := by
  have h := congrArg (eval b) (fallingHurwitzSubsetPoly_eq x U a)
  simp only [fallingHurwitzSubsetPoly] at h
  rw [eval_finset_sum] at h
  simp only [eval_mul, eval_fallingBlockPoly, eval_C,
    eval_fallingPoly, eval_add, eval_X] at h
  simpa [add_assoc, add_left_comm, add_comm] using h

/-- Removing the distinguished point identifies pointed blocks with subsets
of the remaining carrier. -/
def pointedBlockEraseEquiv {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι) (ha : a ∈ S) :
    Finpartition.PointedBlock S a ≃
      {T : Finset ι // T ∈ (S.erase a).powerset} where
  toFun B := ⟨B.1.erase a, Finset.mem_powerset.mpr
    (Finset.erase_subset_erase a B.2.2)⟩
  invFun T := ⟨insert a T.1, Finset.mem_insert_self _ _,
    Finset.insert_subset ha (fun _ ht ↦
      Finset.mem_of_mem_erase (Finset.mem_powerset.mp T.2 ht))⟩
  left_inv B := by
    apply Subtype.ext
    exact Finset.insert_erase B.2.1
  right_inv T := by
    apply Subtype.ext
    have hat : a ∉ T.1 := Finset.notMem_of_mem_powerset_of_notMem T.2 (by simp)
    simp [hat]

theorem sum_pointedBlock_eq_sum_powerset {ι M : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (S : Finset ι) (a : ι) (ha : a ∈ S)
    (f : Finpartition.PointedBlock S a → M) :
    (∑ B : Finpartition.PointedBlock S a, f B) =
      ∑ T : {T : Finset ι // T ∈ (S.erase a).powerset},
        f ((pointedBlockEraseEquiv S a ha).symm T) := by
  let e := pointedBlockEraseEquiv S a ha
  simpa [e] using e.sum_comp (fun T ↦ f (e.symm T))

/-- Rational falling factorial also satisfies the root-first recurrence. -/
theorem fallingValue_root_succ (u : ℚ) (k : ℕ) :
    fallingValue u (k + 1) = u * fallingValue (u - 1) k := by
  induction k with
  | zero => simp [fallingValue]
  | succ k ih =>
      rw [fallingValue_succ, ih, fallingValue_succ]
      push_cast
      ring

/-- A pointed block can equivalently be indexed by its complementary tail. -/
def pointedBlockComplementEquiv {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι) (ha : a ∈ S) :
    Finpartition.PointedBlock S a ≃
      {C : Finset ι // C ∈ (S.erase a).powerset} where
  toFun B := ⟨S \ B.1, Finset.mem_powerset.mpr (by
    intro i hi
    have hiS := (Finset.mem_sdiff.mp hi).1
    have hia : i ≠ a := by
      intro h
      subst i
      exact (Finset.mem_sdiff.mp hi).2 B.2.1
    exact Finset.mem_erase.mpr ⟨hia, hiS⟩)⟩
  invFun C := ⟨S \ C.1, by
      exact Finset.mem_sdiff.mpr ⟨ha, fun hac ↦
        (Finset.notMem_of_mem_powerset_of_notMem C.2 (by simp)) hac⟩,
    Finset.sdiff_subset⟩
  left_inv B := by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_sdiff]
    constructor
    · intro hi
      by_contra hiB
      exact hi.2 ⟨hi.1, hiB⟩
    · intro hi
      exact ⟨B.2.2 hi, fun h ↦ h.2 hi⟩
  right_inv C := by
    apply Subtype.ext
    ext i
    have hCS : C.1 ⊆ S := fun _ hi ↦
      Finset.mem_of_mem_erase (Finset.mem_powerset.mp C.2 hi)
    simp only [Finset.mem_sdiff]
    constructor
    · intro hi
      by_contra hiC
      exact hi.2 ⟨hi.1, hiC⟩
    · intro hi
      exact ⟨hCS hi, fun h ↦ h.2 hi⟩

/-- Falling-factorial weighted sum over set partitions of an arbitrary
carrier. -/
def fallingPartitionSumOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (u : ℚ) (x : ι → ℚ) : ℚ :=
  ∑ P : Finpartition S,
    fallingValue u P.parts.card *
      ∏ B ∈ P.parts, fallingValue (∑ i ∈ B, x i) (B.card - 1)

theorem fallingPartitionSumOn_rec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (a : ι) (ha : a ∈ S) (u : ℚ) (x : ι → ℚ) :
    fallingPartitionSumOn S u x =
      u * ∑ B : Finpartition.PointedBlock S a,
        fallingValue (∑ i ∈ B.1, x i) (B.1.card - 1) *
          fallingPartitionSumOn (S \ B.1) (u - 1) x := by
  classical
  unfold fallingPartitionSumOn
  rw [Finpartition.sum_eq_sum_pointedBlock ha]
  simp_rw [Finpartition.card_parts_joinAt, fallingValue_root_succ,
    Finpartition.prod_parts_joinAt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  ring

@[simp] theorem fallingPartitionSumOn_empty {ι : Type*} [Fintype ι]
    [DecidableEq ι] (u : ℚ) (x : ι → ℚ) :
    fallingPartitionSumOn (∅ : Finset ι) u x = 1 := by
  classical
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
          simpa using (⊥ : Finpartition (∅ : Finset ι)).subset hB hi }
  rw [fallingPartitionSumOn, Fintype.sum_unique]
  have hparts :
      (default : Finpartition (∅ : Finset ι)).parts = ∅ := by
    ext B
    constructor
    · intro hB
      obtain ⟨i, hi⟩ :=
        (default : Finpartition (∅ : Finset ι)).nonempty_of_mem_parts hB
      simpa using (default : Finpartition (∅ : Finset ι)).subset hB hi
    · simp
  rw [hparts]
  simp [fallingValue]

@[simp] theorem pointedBlockComplementEquiv_symm_val {ι : Type*}
    [DecidableEq ι] (S : Finset ι) (a : ι) (ha : a ∈ S)
    (C : {C : Finset ι // C ∈ (S.erase a).powerset}) :
    ((pointedBlockComplementEquiv S a ha).symm C).1 = S \ C.1 := rfl

/-- Reindex a sum over pointed blocks by the complementary subset. -/
theorem sum_pointedBlock_eq_sum_complement_powerset {ι M : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (S : Finset ι) (a : ι) (ha : a ∈ S)
    (f : Finpartition.PointedBlock S a → M) :
    (∑ B : Finpartition.PointedBlock S a, f B) =
      ∑ C : {C : Finset ι // C ∈ (S.erase a).powerset},
        f ((pointedBlockComplementEquiv S a ha).symm C) := by
  let e := pointedBlockComplementEquiv S a ha
  simpa [e] using e.sum_comp (fun C ↦ f (e.symm C))

/-- The falling-factorial weighted set-partition sum has a closed form on
every finite carrier.  This is the generic identity underlying both sides
of the braid convolution formula. -/
theorem fallingPartitionSumOn_closed {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Finset ι) (u : ℚ) (x : ι → ℚ) :
    fallingPartitionSumOn S u x =
      if S = ∅ then 1 else
        u * fallingValue (u + (∑ i ∈ S, x i) - 1) (S.card - 1) := by
  classical
  induction S using Finset.strongInduction generalizing u with
  | H S ih =>
      by_cases hS : S = ∅
      · subst S
        simp
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        rw [fallingPartitionSumOn_rec S a ha, if_neg hS]
        congr 1
        let U := S.erase a
        let e := pointedBlockComplementEquiv S a ha
        let f : Finpartition.PointedBlock S a → ℚ := fun B ↦
          fallingValue (∑ i ∈ B.1, x i) (B.1.card - 1) *
            fallingPartitionSumOn (S \ B.1) (u - 1) x
        let g : {C : Finset ι // C ∈ U.powerset} → ℚ := fun C ↦
          fallingValue (x a + ∑ i ∈ U \ C.1, x i) (U \ C.1).card *
            (if C.1 = ∅ then 1 else
              (u - 1) * fallingValue
                ((u - 1) + (∑ i ∈ C.1, x i) - 1)
                (C.1.card - 1))
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
          dsimp only [f, g, e, pointedBlockComplementEquiv]
          change
            fallingValue (∑ i ∈ B.1, x i) (B.1.card - 1) *
                fallingPartitionSumOn (S \ B.1) (u - 1) x =
              fallingValue (x a + ∑ i ∈ U \ (S \ B.1), x i)
                  (U \ (S \ B.1)).card *
                (if S \ B.1 = ∅ then 1 else
                  (u - 1) * fallingValue
                    ((u - 1) + (∑ i ∈ S \ B.1, x i) - 1)
                    ((S \ B.1).card - 1))
          rw [hi, herase, Finset.card_erase_of_mem B.2.1,
            ← Finset.sum_erase_add _ _ B.2.1]
          ring
        calc
          (∑ B : Finpartition.PointedBlock S a,
              fallingValue (∑ i ∈ B.1, x i) (B.1.card - 1) *
                fallingPartitionSumOn (S \ B.1) (u - 1) x) =
              ∑ C : {C : Finset ι // C ∈ U.powerset}, g C :=
            Fintype.sum_equiv e f g hterm
          _ = ∑ C ∈ U.powerset,
              fallingValue (x a + ∑ i ∈ U \ C, x i) (U \ C).card *
                (if C = ∅ then 1 else
                  (u - 1) * fallingValue
                    ((u - 1) + (∑ i ∈ C, x i) - 1)
                    (C.card - 1)) := by
              rw [Finset.sum_subtype U.powerset (by intro; rfl)]
          _ = fallingValue
              (x a + (u - 1) + ∑ i ∈ U, x i) U.card := by
              simpa [mul_comm] using
                (fallingHurwitzSubset_identity x U (x a) (u - 1))
          _ = fallingValue
              (u + (∑ i ∈ S, x i) - 1) (S.card - 1) := by
              dsimp only [U]
              rw [← Finset.sum_erase_add _ _ ha,
                Finset.card_erase_of_mem ha]
              ring_nf

/-- Rising factorial evaluated in `ℚ`. -/
def risingValue (z : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => risingValue z k * (z + k)

@[simp] theorem risingValue_zero (z : ℚ) : risingValue z 0 = 1 := rfl

theorem risingValue_succ (z : ℚ) (k : ℕ) :
    risingValue z (k + 1) = risingValue z k * (z + k) := rfl

/-- The natural rising factorial, after casting, is `risingValue`. -/
theorem cast_risingFactorial_eq_risingValue (z k : ℕ) :
    (risingFactorial z k : ℚ) = risingValue (z : ℚ) k := by
  induction k with
  | zero => simp [risingFactorial]
  | succ k ih =>
      simp only [risingFactorial, Finset.prod_range_succ] at ih ⊢
      rw [Nat.cast_mul, ih, risingValue_succ]
      push_cast
      rfl

/-- Rising and falling factorials differ only by reversing their factors. -/
theorem risingValue_eq_fallingValue_shift (z : ℚ) (k : ℕ) :
    risingValue z k = fallingValue (z + k - 1) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [risingValue_succ, fallingValue_root_succ]
      have harg :
          z + (↑(k + 1) : ℚ) - 1 - 1 = z + (k : ℚ) - 1 := by
        push_cast
        ring
      rw [harg, ← ih]
      push_cast
      ring

/-- Negating the argument converts a falling factorial to a signed rising
factorial. -/
theorem fallingValue_neg_eq_sign_mul_risingValue (z : ℚ) (k : ℕ) :
    fallingValue (-z) k = (-1 : ℚ) ^ k * risingValue z k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [fallingValue_succ, risingValue_succ, ih, pow_succ]
      push_cast
      ring

/-- Reflection formula for falling factorials. -/
theorem fallingValue_reflect (z : ℚ) (k : ℕ) :
    fallingValue (-z + k - 1) k =
      (-1 : ℚ) ^ k * fallingValue z k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [fallingValue_root_succ, fallingValue_succ, pow_succ]
      have harg :
          -z + (↑(k + 1) : ℚ) - 1 - 1 = -z + (k : ℚ) - 1 := by
        push_cast
        ring
      rw [harg, ih]
      push_cast
      ring

/-- Product form of the rational falling factorial. -/
theorem fallingValue_eq_prod_range (z : ℚ) (k : ℕ) :
    fallingValue z k = ∏ i ∈ Finset.range k, (z - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [fallingValue_succ, Finset.prod_range_succ, ih]

theorem factorial_mul_generalizedChoose_eq_fallingValue (z : ℚ) (k : ℕ) :
    (k.factorial : ℚ) * generalizedChoose z k = fallingValue z k := by
  rw [generalizedChoose, fallingValue_eq_prod_range]
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- The sign carried by a bounded-region block turns its natural rising
factorial into a falling factorial at the negated parameter. -/
theorem sign_mul_cast_risingFactorial_eq_fallingValue (a k : ℕ) :
    (-1 : ℚ) ^ k * (risingFactorial a k : ℚ) =
      fallingValue (-(a : ℚ)) k := by
  rw [cast_risingFactorial_eq_risingValue]
  exact (fallingValue_neg_eq_sign_mul_risingValue (a : ℚ) k).symm

/-- A braid region block is exactly the falling-factorial block weight after
adding one to every vertex parameter. -/
theorem cast_braidRegionBlock_eq_fallingValue_sum {n : ℕ}
    (α : Fin n → ℕ) (B : Finset (Fin n)) :
    (braidRegionBlock α B : ℚ) =
      fallingValue (∑ i ∈ B, ((α i : ℚ) + 1)) (B.card - 1) := by
  classical
  by_cases hB : B = ∅
  · subst B
    simp [braidRegionBlock, risingFactorial]
  · have hc : 1 ≤ B.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hB)
    rw [braidRegionBlock, cast_risingFactorial_eq_risingValue,
      risingValue_eq_fallingValue_shift]
    congr 1
    push_cast [Nat.cast_sub hc]
    simp [blockParameterSum, Finset.sum_add_distrib]
    ring

/-- A signed braid bounded block is the falling-factorial block weight at
the negative sum of its vertex parameters. -/
theorem sign_mul_cast_braidBoundedBlock_eq_fallingValue_sum_neg {n : ℕ}
    (α : Fin n → ℕ) (B : Finset (Fin n)) :
    (-1 : ℚ) ^ (B.card - 1) * (braidBoundedBlock α B : ℚ) =
      fallingValue (-(∑ i ∈ B, (α i : ℚ))) (B.card - 1) := by
  rw [braidBoundedBlock,
    sign_mul_cast_risingFactorial_eq_fallingValue]
  congr 2
  simp [blockParameterSum]

/-- The total block defect of a finite set partition is `|S| - #blocks`. -/
theorem finpartition_block_defect_sum {ι : Type*} [DecidableEq ι]
    {S : Finset ι} (P : Finpartition S) :
    (∑ B ∈ P.parts, (B.card - 1)) = S.card - P.parts.card := by
  have hplus :
      (∑ B ∈ P.parts, (B.card - 1)) + P.parts.card = S.card := by
    calc
      (∑ B ∈ P.parts, (B.card - 1)) + P.parts.card =
          ∑ B ∈ P.parts, ((B.card - 1) + 1) := by
            rw [Finset.sum_add_distrib]
            simp
      _ = ∑ B ∈ P.parts, B.card := by
            apply Finset.sum_congr rfl
            intro B hB
            exact Nat.sub_add_cancel
              (Finset.one_le_card.mpr (P.nonempty_of_mem_parts hB))
      _ = S.card := P.sum_card_parts
  omega

/-- Reflection of one nonempty block after the substitution `x ↦ 1-x`. -/
theorem fallingValue_sum_one_sub_block {ι : Type*} [DecidableEq ι]
    (x : ι → ℚ) (B : Finset ι) (hB : B.Nonempty) :
    fallingValue (∑ i ∈ B, (1 - x i)) (B.card - 1) =
      (-1 : ℚ) ^ (B.card - 1) *
        fallingValue ((∑ i ∈ B, x i) - 2) (B.card - 1) := by
  have hc : 1 ≤ B.card := Finset.one_le_card.mpr hB
  have harg :
      (∑ i ∈ B, (1 - x i)) =
        -((∑ i ∈ B, x i) - 2) + (B.card - 1 : ℕ) - 1 := by
    rw [Finset.sum_sub_distrib]
    push_cast [Nat.cast_sub hc]
    simp
    ring
  rw [harg, fallingValue_reflect]

/-- Rising-factorial version of the partition sum. -/
def risingPartitionSumOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (u : ℚ) (x : ι → ℚ) : ℚ :=
  ∑ P : Finpartition S,
    risingValue u P.parts.card *
      ∏ B ∈ P.parts,
        fallingValue ((∑ i ∈ B, x i) - 2) (B.card - 1)

/-- The substitution `u ↦ -u`, `xᵢ ↦ 1-xᵢ` converts the falling master
sum into the rising master sum, with one global sign. -/
theorem fallingPartitionSumOn_neg_one_sub {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Finset ι) (u : ℚ) (x : ι → ℚ) :
    fallingPartitionSumOn S (-u) (fun i ↦ 1 - x i) =
      (-1 : ℚ) ^ S.card * risingPartitionSumOn S u x := by
  classical
  unfold fallingPartitionSumOn risingPartitionSumOn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [fallingValue_neg_eq_sign_mul_risingValue]
  have hprod :
      (∏ B ∈ P.parts,
          fallingValue (∑ i ∈ B, (1 - x i)) (B.card - 1)) =
        (∏ B ∈ P.parts, (-1 : ℚ) ^ (B.card - 1)) *
          ∏ B ∈ P.parts,
            fallingValue ((∑ i ∈ B, x i) - 2) (B.card - 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro B hB
    exact fallingValue_sum_one_sub_block x B
      (P.nonempty_of_mem_parts hB)
  rw [hprod, Finset.prod_pow_eq_pow_sum,
    finpartition_block_defect_sum]
  have hpow :
      (-1 : ℚ) ^ P.parts.card * (-1 : ℚ) ^ (S.card - P.parts.card) =
        (-1 : ℚ) ^ S.card := by
    rw [← pow_add, Nat.add_sub_of_le P.card_parts_le_card]
  calc
    (-1 : ℚ) ^ P.parts.card * risingValue u P.parts.card *
          ((-1 : ℚ) ^ (S.card - P.parts.card) *
            ∏ B ∈ P.parts,
              fallingValue ((∑ i ∈ B, x i) - 2) (B.card - 1)) =
        ((-1 : ℚ) ^ P.parts.card *
            (-1 : ℚ) ^ (S.card - P.parts.card)) *
          (risingValue u P.parts.card *
            ∏ B ∈ P.parts,
              fallingValue ((∑ i ∈ B, x i) - 2) (B.card - 1)) := by ring
    _ = _ := by rw [hpow]

/-- Closed form of the rising-factorial partition identity.  Together with
`fallingPartitionSumOn_closed`, this gives the two generic forms used for
the braid region and bounded-region formulas. -/
theorem risingPartitionSumOn_closed {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Finset ι) (u : ℚ) (x : ι → ℚ) :
    risingPartitionSumOn S u x =
      if S = ∅ then 1 else
        u * fallingValue (u + (∑ i ∈ S, x i) - 1) (S.card - 1) := by
  classical
  by_cases hS : S = ∅
  · subst S
    rw [if_pos rfl]
    have htrans := fallingPartitionSumOn_neg_one_sub
      (∅ : Finset ι) u x
    rw [fallingPartitionSumOn_empty] at htrans
    simpa using htrans.symm
  · rw [if_neg hS]
    have htrans := fallingPartitionSumOn_neg_one_sub S u x
    rw [fallingPartitionSumOn_closed, if_neg hS] at htrans
    have hc : 1 ≤ S.card :=
      Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have harg :
        -u + (∑ i ∈ S, (1 - x i)) - 1 =
          -(u + (∑ i ∈ S, x i) - 1) + (S.card - 1 : ℕ) - 1 := by
      rw [Finset.sum_sub_distrib]
      push_cast [Nat.cast_sub hc]
      simp
      ring
    rw [harg, fallingValue_reflect] at htrans
    have hpow :
        (-1 : ℚ) ^ S.card = -((-1 : ℚ) ^ (S.card - 1)) := by
      calc
        (-1 : ℚ) ^ S.card =
            (-1 : ℚ) ^ ((S.card - 1) + 1) := by
              rw [Nat.sub_add_cancel hc]
        _ = -((-1 : ℚ) ^ (S.card - 1)) := by
              rw [pow_succ]
              ring
    have hcancel : -((-1 : ℚ) ^ (S.card - 1)) ≠ 0 := by
      exact neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hcanceled :
        -((-1 : ℚ) ^ (S.card - 1)) *
              (u * fallingValue
                (u + (∑ i ∈ S, x i) - 1) (S.card - 1)) =
          -((-1 : ℚ) ^ (S.card - 1)) * risingPartitionSumOn S u x := by
      calc
        -((-1 : ℚ) ^ (S.card - 1)) *
              (u * fallingValue
                (u + (∑ i ∈ S, x i) - 1) (S.card - 1)) =
            (-u) *
              ((-1 : ℚ) ^ (S.card - 1) *
                fallingValue
                  (u + (∑ i ∈ S, x i) - 1) (S.card - 1)) := by ring
        _ = (-1 : ℚ) ^ S.card * risingPartitionSumOn S u x := htrans
        _ = -((-1 : ℚ) ^ (S.card - 1)) *
              risingPartitionSumOn S u x := by rw [hpow]
    exact (mul_left_cancel₀ hcancel hcanceled).symm

end


end BraidPartitionIdentityDirect

end CyclicBraidArrangement
