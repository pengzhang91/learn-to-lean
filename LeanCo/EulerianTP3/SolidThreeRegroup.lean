import LeanCo.EulerianTP3.SolidThree
import LeanCo.EulerianTP3.Rows

/-!
# Regrouping the ordinary solid third-order minor

This file carries out the global finite-sum regrouping left after the
four local `Phi` blocks have been checked.  Repeated deletion indices give
the singleton and pair blocks; three distinct indices give the triple block.
-/

namespace LeanCo.EulerianTP3

open scoped BigOperators Matrix
open Polynomial

/-! ## Symmetric ordered sums -/

lemma sum_offDiagonal_swap {α : Type*} [Fintype α] [DecidableEq α]
    {M : Type*} [AddCommMonoid M] (f : α → α → M) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f j i) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  simp_rw [show ∀ i : α,
      Finset.univ.erase i = Finset.univ.filter (fun j ↦ j ≠ i) by
    intro i
    ext j
    simp]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

lemma sum_distinctThree_swap_first_second {α : Type*} [Fintype α]
    [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (f : α → α → α → M) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, f j i k) =
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, f i j k := by
  simp_rw [show ∀ i : α,
      Finset.univ.erase i = Finset.univ.filter (fun j ↦ j ≠ i) by
    intro i
    ext j
    simp]
  simp_rw [show ∀ i j : α,
      (Finset.univ.filter (fun x ↦ x ≠ i)).erase j =
        Finset.univ.filter (fun k ↦ k ≠ i ∧ k ≠ j) by
    intro i j
    ext k
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij, and_comm]

lemma sum_distinctThree_swap_second_third {α : Type*} [Fintype α]
    [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (f : α → α → α → M) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, f i k j) =
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, f i j k := by
  apply Finset.sum_congr rfl
  intro i hi
  let t := Finset.univ.erase i
  have hswap : (∑ j ∈ t, ∑ k ∈ t.erase j, f i k j) =
      ∑ j ∈ t, ∑ k ∈ t.erase j, f i j k := by
    simp_rw [show ∀ j : α, t.erase j = t.filter (fun k ↦ k ≠ j) by
      intro j
      ext k
      simp only [Finset.mem_erase, Finset.mem_filter]
      tauto]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hjk : j = k
    · subst k
      simp
    · simp [hjk, Ne.symm hjk]
  simpa [t] using hswap

lemma sum_distinctThree_cycle {α : Type*} [Fintype α] [DecidableEq α]
    {M : Type*} [AddCommMonoid M] (f : α → α → α → M) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, f k i j) =
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, f i j k := by
  calc
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∑ k ∈ (Finset.univ.erase i).erase j, f j i k :=
      (sum_distinctThree_swap_second_third (fun a b c ↦ f c a b)).symm
    _ = _ := sum_distinctThree_swap_first_second f

lemma sum_allPairs_eq_diagonal_add_offDiagonal {α : Type*} [Fintype α]
    [DecidableEq α] {M : Type*} [AddCommMonoid M] (f : α → α → M) :
    (∑ i, ∑ j, f i j) =
      (∑ i, f i i) + ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Finset.add_sum_erase Finset.univ (f i) (Finset.mem_univ i)).symm

lemma sum_oneAgainstPair_partition {α : Type*} [Fintype α] [DecidableEq α]
    {M : Type*} [AddCommMonoid M] (f : α → α → α → M) :
    (∑ a, ∑ b, ∑ c ∈ Finset.univ.erase b, f a b c) =
      (∑ b, ∑ c ∈ Finset.univ.erase b, (f b b c + f c b c)) +
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∑ k ∈ (Finset.univ.erase i).erase j, f k i j := by
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    (∑ a, f a b c) = f b b c + ∑ a ∈ Finset.univ.erase b, f a b c :=
      (Finset.add_sum_erase Finset.univ (fun a ↦ f a b c) (Finset.mem_univ b)).symm
    _ = f b b c + (f c b c +
        ∑ a ∈ (Finset.univ.erase b).erase c, f a b c) := by
      rw [(Finset.add_sum_erase (Finset.univ.erase b) (fun a ↦ f a b c)
        (a := c) hc).symm]
    _ = (f b b c + f c b c) +
        ∑ a ∈ (Finset.univ.erase b).erase c, f a b c := by ac_rfl

/-- Burnside-style regrouping for one unrestricted pair, one ordered
off-diagonal pair, and one index against an ordered pair. -/
theorem orderedDeletion_orbit_regroup {α : Type*} [Fintype α] [DecidableEq α]
    (d e : α → α → ℝ) (h : α → α → α → ℝ)
    (hsym : ∀ i j k, h i j k = h i k j) :
    (∑ i, ∑ j, d i j) +
        (∑ i, ∑ j ∈ Finset.univ.erase i, e i j) +
        (∑ a, ∑ b, ∑ c ∈ Finset.univ.erase b, h a b c) =
      (∑ i, d i i) +
        (1 / 2 : ℝ) * (∑ i, ∑ j ∈ Finset.univ.erase i,
          (2 * e i j + d i j + d j i + 2 * h i i j + 2 * h j j i)) +
        (1 / 6 : ℝ) * (∑ i, ∑ j ∈ Finset.univ.erase i,
          ∑ k ∈ (Finset.univ.erase i).erase j,
            (2 * h i j k + 2 * h j i k + 2 * h k i j)) := by
  have hd := sum_allPairs_eq_diagonal_add_offDiagonal d
  have hdswap := sum_offDiagonal_swap d
  have hsplit := sum_oneAgainstPair_partition h
  have hcyc := sum_distinctThree_cycle h
  have hoverlap :
      (∑ b, ∑ c ∈ Finset.univ.erase b, (h b b c + h c b c)) =
        ∑ b, ∑ c ∈ Finset.univ.erase b, (h b b c + h c c b) := by
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    rw [hsym c b c]
  have hpair :
      (1 / 2 : ℝ) * (∑ i, ∑ j ∈ Finset.univ.erase i,
          (2 * e i j + d i j + d j i + 2 * h i i j + 2 * h j j i)) =
        (∑ i, ∑ j ∈ Finset.univ.erase i, e i j) +
        (∑ i, ∑ j ∈ Finset.univ.erase i, d i j) +
        (∑ i, ∑ j ∈ Finset.univ.erase i, (h i i j + h j j i)) := by
    simp_rw [Finset.sum_add_distrib]
    have hscale (f : α → α → ℝ) (a : ℝ) :
        (∑ i, ∑ j ∈ Finset.univ.erase i, a * f i j) =
          a * ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    rw [hscale e 2, hscale (fun i j ↦ h i i j) 2,
      hscale (fun i j ↦ h j j i) 2, hdswap]
    ring
  have htriple :
      (1 / 6 : ℝ) * (∑ i, ∑ j ∈ Finset.univ.erase i,
          ∑ k ∈ (Finset.univ.erase i).erase j,
            (2 * h i j k + 2 * h j i k + 2 * h k i j)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∑ k ∈ (Finset.univ.erase i).erase j, h i j k := by
    simp_rw [Finset.sum_add_distrib]
    have hs2 := sum_distinctThree_swap_first_second (fun i j k ↦ 2 * h i j k)
    have hc2 := sum_distinctThree_cycle (fun i j k ↦ 2 * h i j k)
    rw [hs2, hc2]
    have hscale (f : α → α → α → ℝ) (a : ℝ) :
        (∑ i, ∑ j ∈ Finset.univ.erase i,
          ∑ k ∈ (Finset.univ.erase i).erase j, a * f i j k) =
          a * ∑ i, ∑ j ∈ Finset.univ.erase i,
            ∑ k ∈ (Finset.univ.erase i).erase j, f i j k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
    rw [hscale h 2]
    ring
  rw [hd, hsplit, hoverlap]
  rw [hcyc, hpair, htriple]
  ring

/-! ## The four global block values -/

/-- The empty-union block, with every factor common to the three rows. -/
noncomputable def secondZeroBlock {n : ℕ} (r : Fin n → ℝ)
    (i j k : ℕ) : ℝ :=
  weightedCoefficientMinor3 phiZeroWeights
    (polynomialTripleCoefficients
      (fun u row ↦ phiZeroTriples u row * factorPolynomial r)) i j k

/-- The block whose union of deleted indices is the singleton `{u}`. -/
noncomputable def secondSingletonBlock {n : ℕ} (r : Fin n → ℝ)
    (u : Fin n) (i j k : ℕ) : ℝ :=
  weightedCoefficientMinor3 (phiSingletonWeights (r u))
    (polynomialTripleCoefficients
      (fun t row ↦ phiSingletonTriples (r u) t row *
        factorPolynomialOn (Finset.univ.erase u) r)) i j k

/-- The block whose union of deleted indices is the pair `{u,v}`. -/
noncomputable def secondPairBlock {n : ℕ} (r : Fin n → ℝ)
    (u v : Fin n) (i j k : ℕ) : ℝ :=
  weightedCoefficientMinor3 (phiPairWeights (r u) (r v))
    (polynomialTripleCoefficients
      (fun t row ↦ phiPairTriples (r u) (r v) t row *
        factorPolynomialOn ((Finset.univ.erase u).erase v) r)) i j k

/-- The block whose union of deleted indices is the triple `{u,v,w}`. -/
noncomputable def secondTripleBlock {n : ℕ} (r : Fin n → ℝ)
    (u v w : Fin n) (i j k : ℕ) : ℝ :=
  weightedCoefficientMinor3 (phiTripleWeights (r u) (r v) (r w))
    (polynomialTripleCoefficients
      (fun t row ↦ phiTripleTriples (r u) (r v) (r w) t row *
        factorPolynomialOn (((Finset.univ.erase u).erase v).erase w) r)) i j k

private theorem coefficientMinor3_polynomialTriple_apply {α : Type*}
    (p : α → Fin 3 → ℝ[X]) (u : α) (i j k : ℕ) :
    coefficientMinor3 (polynomialTripleCoefficients p u) i j k =
      polynomialMinor3 (p u 0) (p u 1) (p u 2) i j k := by
  simp [coefficientMinor3, polynomialTripleCoefficients, polynomialMinor3,
    tripleCoefficientMatrix, threePolynomialRows, coefficientMatrix, det3]

theorem secondZeroBlock_eq {n : ℕ} (r : Fin n → ℝ) (i j k : ℕ) :
    secondZeroBlock r i j k =
      polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
        (X ^ 2 * factorPolynomial r) i j k := by
  simp [secondZeroBlock, weightedCoefficientMinor3, phiZeroWeights, phiZeroTriples,
    coefficientMinor3_polynomialTriple_apply, polynomialOfLocalVec_localOne,
    polynomialOfLocalVec_shiftOne_localOne, polynomialOfLocalVec_shiftTwo_localOne,
    Fin.sum_univ_succ]

theorem secondSingletonBlock_eq {n : ℕ} (r : Fin n → ℝ) (u : Fin n)
    (i j k : ℕ) :
    secondSingletonBlock r u i j k =
      3 * (1 + r u) * polynomialMinor3 (factorPolynomial r)
          (X * factorPolynomial r) (X ^ 2 * deletedFactorPolynomial r u) i j k
      + (1 + r u) * polynomialMinor3 (factorPolynomial r)
          (X * deletedFactorPolynomial r u) (X ^ 2 * factorPolynomial r) i j k
      + 3 * (1 + r u) ^ 2 * polynomialMinor3 (factorPolynomial r)
          (X * deletedFactorPolynomial r u) (X ^ 2 * deletedFactorPolynomial r u)
            i j k := by
  have hP := factorPolynomial_eq_linear_mul_deletedFactor r u
  have hf := deletedFactorPolynomial_eq_factorPolynomialOn r u
  have hrow₀ :
      polynomialOfLocalVec (localLinear (r u)) *
          factorPolynomialOn (Finset.univ.erase u) r = factorPolynomial r := by
    rw [polynomialOfLocalVec_localLinear, ← hf, hP]
  have hrow₁ :
      polynomialOfLocalVec (shiftOne (localLinear (r u))) *
          factorPolynomialOn (Finset.univ.erase u) r = X * factorPolynomial r := by
    rw [polynomialOfLocalVec_shiftOne_localLinear, ← hf, hP]
    ring
  have hrow₁' :
      polynomialOfLocalVec (shiftOne localOne) *
          factorPolynomialOn (Finset.univ.erase u) r =
        X * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftOne_localOne, ← hf]
  have hrow₂ :
      polynomialOfLocalVec (shiftTwo (localLinear (r u))) *
          factorPolynomialOn (Finset.univ.erase u) r = X ^ 2 * factorPolynomial r := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, ← hf, hP]
    ring
  have hrow₂' :
      polynomialOfLocalVec (shiftTwo localOne) *
          factorPolynomialOn (Finset.univ.erase u) r =
        X ^ 2 * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftTwo_localOne, ← hf]
  have hrow₀r := hrow₀
  have hrow₁r := hrow₁
  have hrow₁r' := hrow₁'
  have hrow₂r := hrow₂
  have hrow₂r' := hrow₂'
  rw [mul_comm] at hrow₀r hrow₁r hrow₁r' hrow₂r hrow₂r'
  simp [secondSingletonBlock, weightedCoefficientMinor3, phiSingletonWeights,
    phiSingletonTriples, coefficientMinor3_polynomialTriple_apply,
    hrow₀, hrow₁, hrow₁', hrow₂, hrow₂', hrow₀r, hrow₁r,
    hrow₁r', hrow₂r, hrow₂r', Fin.sum_univ_succ]
  ring

theorem secondZeroBlock_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ secondZeroBlock r i j k := by
  unfold secondZeroBlock
  exact phiZero_block_nonnegative Finset.univ r (fun u hu ↦ hr u) i j k hij hjk

theorem secondSingletonBlock_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) (u : Fin n) {i j k : ℕ}
    (hij : i < j) (hjk : j < k) :
    0 ≤ secondSingletonBlock r u i j k := by
  unfold secondSingletonBlock
  exact phiSingleton_block_nonnegative (r u) (hr u) (Finset.univ.erase u) r
    (fun v hv ↦ hr v) i j k hij hjk

theorem secondPairBlock_eq {n : ℕ} (r : Fin n → ℝ) (u v : Fin n)
    (huv : u ≠ v) (i j k : ℕ) :
    secondPairBlock r u v i j k =
      2 * (1 + r u) * (1 + r v) *
        polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
          (X ^ 2 * deletedPairFactorPolynomial r u v) i j k
      + 3 * (1 + r u) * (1 + r v) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
          (X ^ 2 * deletedFactorPolynomial r v) i j k
      + 3 * (1 + r v) * (1 + r u) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r v)
          (X ^ 2 * deletedFactorPolynomial r u) i j k
      + 2 * (1 + r u) ^ 2 * (1 + r v) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
          (X ^ 2 * deletedPairFactorPolynomial r u v) i j k
      + 2 * (1 + r v) ^ 2 * (1 + r u) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r v)
          (X ^ 2 * deletedPairFactorPolynomial r u v) i j k := by
  have hpair := deletedPairFactorPolynomial_eq_factorPolynomialOn r u v
  have hP := factorPolynomial_eq_linear_mul_linear_mul_deletedPair r u v huv
  have hfu := deletedFactorPolynomial_eq_linear_mul_deletedPair r u v huv
  have hfvu := deletedFactorPolynomial_eq_linear_mul_deletedPair r v u huv.symm
  have hcomm := deletedPairFactorPolynomial_comm r v u
  have hfv : deletedFactorPolynomial r v =
      (1 + C (r u) * X) * deletedPairFactorPolynomial r u v := by
    rw [hfvu, hcomm]
  have hrow₀ :
      polynomialOfLocalVec (localQuadratic (r u) (r v)) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r = factorPolynomial r := by
    rw [polynomialOfLocalVec_localQuadratic, ← hpair, hP]
  have hrow₁ :
      polynomialOfLocalVec (shiftOne (localQuadratic (r u) (r v))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X * factorPolynomial r := by
    rw [polynomialOfLocalVec_shiftOne_localQuadratic, ← hpair, hP]
    ring
  have hrow₁u :
      polynomialOfLocalVec (shiftOne (localLinear (r v))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftOne_localLinear, ← hpair, hfu]
    ring
  have hrow₁v :
      polynomialOfLocalVec (shiftOne (localLinear (r u))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X * deletedFactorPolynomial r v := by
    rw [polynomialOfLocalVec_shiftOne_localLinear, ← hpair, hfv]
    ring
  have hrow₂pair :
      polynomialOfLocalVec (shiftTwo localOne) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X ^ 2 * deletedPairFactorPolynomial r u v := by
    rw [polynomialOfLocalVec_shiftTwo_localOne, ← hpair]
  have hrow₂u :
      polynomialOfLocalVec (shiftTwo (localLinear (r v))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X ^ 2 * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, ← hpair, hfu]
    ring
  have hrow₂v :
      polynomialOfLocalVec (shiftTwo (localLinear (r u))) *
          factorPolynomialOn ((Finset.univ.erase u).erase v) r =
        X ^ 2 * deletedFactorPolynomial r v := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, ← hpair, hfv]
    ring
  simp [secondPairBlock, weightedCoefficientMinor3, phiPairWeights, phiPairTriples,
    coefficientMinor3_polynomialTriple_apply, hrow₀, hrow₁, hrow₁u, hrow₁v,
    hrow₂pair, hrow₂u, hrow₂v, Fin.sum_univ_succ]
  ring

theorem secondPairBlock_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) (u v : Fin n) {i j k : ℕ}
    (hij : i < j) (hjk : j < k) :
    0 ≤ secondPairBlock r u v i j k := by
  unfold secondPairBlock
  exact phiPair_block_nonnegative (r u) (r v) (hr u) (hr v)
    ((Finset.univ.erase u).erase v) r (fun w hw ↦ hr w) i j k hij hjk

private lemma factorPolynomialOn_eq_linear_mul_erase {α : Type*} [DecidableEq α]
    (r : α → ℝ) (s : Finset α) {u : α} (hu : u ∈ s) :
    factorPolynomialOn s r =
      (1 + C (r u) * X) * factorPolynomialOn (s.erase u) r := by
  simpa [factorPolynomialOn] using
    (Finset.mul_prod_erase s (fun v ↦ (1 + C (r v) * X)) hu).symm

theorem secondTripleBlock_eq {n : ℕ} (r : Fin n → ℝ) (u v w : Fin n)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (i j k : ℕ) :
    secondTripleBlock r u v w i j k =
      2 * (1 + r u) * (1 + r v) * (1 + r w) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
          (X ^ 2 * deletedPairFactorPolynomial r v w) i j k
      + 2 * (1 + r v) * (1 + r u) * (1 + r w) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r v)
          (X ^ 2 * deletedPairFactorPolynomial r u w) i j k
      + 2 * (1 + r w) * (1 + r u) * (1 + r v) *
        polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r w)
          (X ^ 2 * deletedPairFactorPolynomial r u v) i j k := by
  let outside := ((Finset.univ.erase u).erase v).erase w
  have hwmem : w ∈ (Finset.univ.erase u).erase v := by simp [huw.symm, hvw.symm]
  have hpUV : deletedPairFactorPolynomial r u v =
      (1 + C (r w) * X) * factorPolynomialOn outside r := by
    simpa [outside, deletedPairFactorPolynomial_eq_factorPolynomialOn] using
      factorPolynomialOn_eq_linear_mul_erase r ((Finset.univ.erase u).erase v) hwmem
  have hpUW : deletedPairFactorPolynomial r u w =
      (1 + C (r v) * X) * factorPolynomialOn outside r := by
    have hvmem : v ∈ (Finset.univ.erase u).erase w := by simp [huv.symm, hvw]
    have h := factorPolynomialOn_eq_linear_mul_erase r
      ((Finset.univ.erase u).erase w) hvmem
    rw [show ((Finset.univ.erase u).erase w).erase v = outside by
      simp [outside, Finset.erase_right_comm]] at h
    simpa [deletedPairFactorPolynomial_eq_factorPolynomialOn] using h
  have hpVW : deletedPairFactorPolynomial r v w =
      (1 + C (r u) * X) * factorPolynomialOn outside r := by
    have humem : u ∈ (Finset.univ.erase v).erase w := by simp [huv, huw]
    have h := factorPolynomialOn_eq_linear_mul_erase r
      ((Finset.univ.erase v).erase w) humem
    rw [show ((Finset.univ.erase v).erase w).erase u = outside by
      ext x
      simp only [Finset.mem_erase, Finset.mem_univ, true_and, outside]
      tauto] at h
    simpa [deletedPairFactorPolynomial_eq_factorPolynomialOn] using h
  have hfu := deletedFactorPolynomial_eq_linear_mul_deletedPair r u v huv
  have hfv := deletedFactorPolynomial_eq_linear_mul_deletedPair r v u huv.symm
  rw [deletedPairFactorPolynomial_comm r v u] at hfv
  have hfw := deletedFactorPolynomial_eq_linear_mul_deletedPair r w u huw.symm
  rw [deletedPairFactorPolynomial_comm r w u] at hfw
  have hP := factorPolynomial_eq_linear_mul_linear_mul_deletedPair r u v huv
  have hrow₀ :
      polynomialOfLocalVec (localCubic (r u) (r v) (r w)) *
          factorPolynomialOn outside r = factorPolynomial r := by
    rw [polynomialOfLocalVec_localCubic, hP, hpUV]
    ring
  have hrow₁u :
      polynomialOfLocalVec (shiftOne (localQuadratic (r v) (r w))) *
          factorPolynomialOn outside r = X * deletedFactorPolynomial r u := by
    rw [polynomialOfLocalVec_shiftOne_localQuadratic, hfu, hpUV]
    ring
  have hrow₁v :
      polynomialOfLocalVec (shiftOne (localQuadratic (r u) (r w))) *
          factorPolynomialOn outside r = X * deletedFactorPolynomial r v := by
    rw [polynomialOfLocalVec_shiftOne_localQuadratic, hfv, hpUV]
    ring
  have hrow₁w :
      polynomialOfLocalVec (shiftOne (localQuadratic (r u) (r v))) *
          factorPolynomialOn outside r = X * deletedFactorPolynomial r w := by
    rw [polynomialOfLocalVec_shiftOne_localQuadratic, hfw, hpUW]
    ring
  have hrow₂u :
      polynomialOfLocalVec (shiftTwo (localLinear (r u))) *
          factorPolynomialOn outside r = X ^ 2 * deletedPairFactorPolynomial r v w := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, hpVW]
    ring
  have hrow₂v :
      polynomialOfLocalVec (shiftTwo (localLinear (r v))) *
          factorPolynomialOn outside r = X ^ 2 * deletedPairFactorPolynomial r u w := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, hpUW]
    ring
  have hrow₂w :
      polynomialOfLocalVec (shiftTwo (localLinear (r w))) *
          factorPolynomialOn outside r = X ^ 2 * deletedPairFactorPolynomial r u v := by
    rw [polynomialOfLocalVec_shiftTwo_localLinear, hpUV]
    ring
  simp [secondTripleBlock, outside, weightedCoefficientMinor3, phiTripleWeights,
    phiTripleTriples, coefficientMinor3_polynomialTriple_apply, hrow₀,
    hrow₁u, hrow₁v, hrow₁w, hrow₂u, hrow₂v, hrow₂w,
    Fin.sum_univ_succ]
  ring

theorem secondTripleBlock_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) (u v w : Fin n) {i j k : ℕ}
    (hij : i < j) (hjk : j < k) :
    0 ≤ secondTripleBlock r u v w i j k := by
  unfold secondTripleBlock
  exact phiTriple_block_nonnegative (r u) (r v) (r w) (hr u) (hr v) (hr w)
    (((Finset.univ.erase u).erase v).erase w) r (fun x hx ↦ hr x)
      i j k hij hjk

/-! ## Bilinear expansion of the second summand -/

theorem polynomialMinor3_add_last (P Q R₁ R₂ : ℝ[X]) (i j k : ℕ) :
    polynomialMinor3 P Q (R₁ + R₂) i j k =
      polynomialMinor3 P Q R₁ i j k + polynomialMinor3 P Q R₂ i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

theorem polynomialMinor3_sum_last {α : Type*} (s : Finset α)
    (P Q : ℝ[X]) (R : α → ℝ[X]) (i j k : ℕ) :
    polynomialMinor3 P Q (∑ u ∈ s, R u) i j k =
      ∑ u ∈ s, polynomialMinor3 P Q (R u) i j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, polynomialMinor3_add_last, ih, Finset.sum_insert ha]

theorem polynomialMinor3_C_mul_middle (P Q R : ℝ[X]) (a : ℝ) (i j k : ℕ) :
    polynomialMinor3 P (C a * Q) R i j k =
      a * polynomialMinor3 P Q R i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

theorem polynomialMinor3_C_mul_last (P Q R : ℝ[X]) (a : ℝ) (i j k : ℕ) :
    polynomialMinor3 P Q (C a * R) i j k =
      a * polynomialMinor3 P Q R i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
  ring

/-- The raw bilinear expansion before equal deletion indices are grouped. -/
theorem secondSummand_raw_expansion {n : ℕ} (r : Fin n → ℝ) (i j k : ℕ) :
    polynomialMinor3 (factorPolynomial r) (X * (factorPolynomial r + G1 r))
        (X ^ 2 * (factorPolynomial r + 3 * G1 r + 2 * G2 r)) i j k =
      polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
          (X ^ 2 * factorPolynomial r) i j k
      + ∑ u, 3 * (1 + r u) *
          polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
            (X ^ 2 * deletedFactorPolynomial r u) i j k
      + ∑ u, (1 + r u) *
          polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
            (X ^ 2 * factorPolynomial r) i j k
      + ∑ u, ∑ v, 3 * (1 + r u) * (1 + r v) *
          polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
            (X ^ 2 * deletedFactorPolynomial r v) i j k
      + ∑ u, ∑ v ∈ Finset.univ.erase u, (1 + r u) * (1 + r v) *
          polynomialMinor3 (factorPolynomial r) (X * factorPolynomial r)
            (X ^ 2 * deletedPairFactorPolynomial r u v) i j k
      + ∑ u, ∑ v, ∑ w ∈ Finset.univ.erase v,
          (1 + r u) * (1 + r v) * (1 + r w) *
            polynomialMinor3 (factorPolynomial r) (X * deletedFactorPolynomial r u)
              (X ^ 2 * deletedPairFactorPolynomial r v w) i j k := by
  classical
  let P := factorPolynomial r
  let F := fun u ↦ deletedFactorPolynomial r u
  let H := fun u v ↦ deletedPairFactorPolynomial r u v
  have hCtwo : C (2 : ℝ) = (2 : ℝ[X]) := by
    exact (map_ofNat (C : ℝ →+* ℝ[X]) 2).symm.symm
  have hCthree : C (3 : ℝ) = (3 : ℝ[X]) := by
    exact (map_ofNat (C : ℝ →+* ℝ[X]) 3).symm.symm
  have hmiddle : X * (factorPolynomial r + G1 r) =
      X * P + ∑ u, C (1 + r u) * (X * F u) := by
    rw [mul_add, G1, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [F]
    ring
  have htwoG2 : (2 : ℝ[X]) * G2 r =
      ∑ u, ∑ v ∈ Finset.univ.erase u,
        C ((1 + r u) * (1 + r v)) * H u v := by
    simp only [G2]
    have hc : (2 : ℝ[X]) * C (1 / 2 : ℝ) = 1 := by
      rw [← hCtwo, ← C_mul]
      norm_num
    rw [← mul_assoc, hc, one_mul]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    dsimp [H]
    rw [map_mul]
    ring
  have hthreeG1 : X ^ 2 * (3 * G1 r) =
      ∑ u, C (3 * (1 + r u)) * (X ^ 2 * F u) := by
    rw [G1, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [F]
    rw [← hCthree, map_mul]
    ring
  have htwoG2X : X ^ 2 * ((2 : ℝ[X]) * G2 r) =
      ∑ u, ∑ v ∈ Finset.univ.erase u,
        C ((1 + r u) * (1 + r v)) * (X ^ 2 * H u v) := by
    rw [htwoG2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  have hlast : X ^ 2 * (factorPolynomial r + 3 * G1 r + 2 * G2 r) =
      X ^ 2 * P
        + ∑ u, C (3 * (1 + r u)) * (X ^ 2 * F u)
        + ∑ u, ∑ v ∈ Finset.univ.erase u,
            C ((1 + r u) * (1 + r v)) * (X ^ 2 * H u v) := by
    calc
      _ = X ^ 2 * P + X ^ 2 * (3 * G1 r) + X ^ 2 * ((2 : ℝ[X]) * G2 r) := by
        dsimp [P]
        ring
      _ = _ := by rw [hthreeG1, htwoG2X]
  rw [hmiddle, hlast]
  simp_rw [polynomialMinor3_add_middle, polynomialMinor3_add_last]
  simp_rw [polynomialMinor3_sum_middle, polynomialMinor3_sum_last]
  simp_rw [polynomialMinor3_C_mul_middle, polynomialMinor3_C_mul_last]
  dsimp [P, F, H]
  ring

/-! ## Regrouped second summand -/

/-- Sum of the four union-size blocks.  Pairs and triples are represented
by ordered tuples and divided by their orbit sizes. -/
noncomputable def secondBlockSum {n : ℕ} (r : Fin n → ℝ)
    (i j k : ℕ) : ℝ :=
  secondZeroBlock r i j k
    + ∑ u, secondSingletonBlock r u i j k
    + (1 / 2 : ℝ) *
        (∑ u, ∑ v ∈ Finset.univ.erase u, secondPairBlock r u v i j k)
    + (1 / 6 : ℝ) *
        (∑ u, ∑ v ∈ Finset.univ.erase u,
          ∑ w ∈ (Finset.univ.erase u).erase v, secondTripleBlock r u v w i j k)

/-- The global deletion-index regrouping for the second summand. -/
theorem secondSummand_eq_secondBlockSum {n : ℕ} (r : Fin n → ℝ)
    (i j k : ℕ) :
    polynomialMinor3 (factorPolynomial r) (X * (factorPolynomial r + G1 r))
        (X ^ 2 * (factorPolynomial r + 3 * G1 r + 2 * G2 r)) i j k =
      secondBlockSum r i j k := by
  classical
  let P := factorPolynomial r
  let F := fun u ↦ deletedFactorPolynomial r u
  let H := fun u v ↦ deletedPairFactorPolynomial r u v
  let A := fun u ↦ 3 * (1 + r u) *
    polynomialMinor3 P (X * P) (X ^ 2 * F u) i j k
  let B := fun u ↦ (1 + r u) *
    polynomialMinor3 P (X * F u) (X ^ 2 * P) i j k
  let d := fun u v ↦ 3 * (1 + r u) * (1 + r v) *
    polynomialMinor3 P (X * F u) (X ^ 2 * F v) i j k
  let e := fun u v ↦ (1 + r u) * (1 + r v) *
    polynomialMinor3 P (X * P) (X ^ 2 * H u v) i j k
  let h := fun u v w ↦ (1 + r u) * (1 + r v) * (1 + r w) *
    polynomialMinor3 P (X * F u) (X ^ 2 * H v w) i j k
  have hsym : ∀ u v w, h u v w = h u w v := by
    intro u v w
    dsimp [h, H]
    rw [deletedPairFactorPolynomial_comm r v w]
    ring
  have horbit := orderedDeletion_orbit_regroup d e h hsym
  have hsingle : (∑ u, secondSingletonBlock r u i j k) =
      (∑ u, A u) + (∑ u, B u) + ∑ u, d u u := by
    simp_rw [secondSingletonBlock_eq]
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [A, B, d, P, F]
    ring
  have hpair :
      (∑ u, ∑ v ∈ Finset.univ.erase u, secondPairBlock r u v i j k) =
        ∑ u, ∑ v ∈ Finset.univ.erase u,
          (2 * e u v + d u v + d v u + 2 * h u u v + 2 * h v v u) := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    rw [secondPairBlock_eq r u v hvu.symm]
    dsimp [d, e, h, P, F, H]
    rw [deletedPairFactorPolynomial_comm r v u]
    ring
  have htriple :
      (∑ u, ∑ v ∈ Finset.univ.erase u,
        ∑ w ∈ (Finset.univ.erase u).erase v, secondTripleBlock r u v w i j k) =
      ∑ u, ∑ v ∈ Finset.univ.erase u,
        ∑ w ∈ (Finset.univ.erase u).erase v,
          (2 * h u v w + 2 * h v u w + 2 * h w u v) := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hvu : v ≠ u := (Finset.mem_erase.mp hv).1
    apply Finset.sum_congr rfl
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    have hwu : w ≠ u :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    rw [secondTripleBlock_eq r u v w hvu.symm hwu.symm hwv.symm]
    dsimp [h, P, F, H]
    ring
  rw [secondSummand_raw_expansion]
  unfold secondBlockSum
  rw [secondZeroBlock_eq, hsingle, hpair, htriple]
  dsimp [A, B, d, e, h, P, F, H] at horbit ⊢
  linear_combination horbit

theorem secondBlockSum_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ secondBlockSum r i j k := by
  have h₀ := secondZeroBlock_nonnegative r hr hij hjk
  have h₁ : 0 ≤ ∑ u, secondSingletonBlock r u i j k := by
    apply Finset.sum_nonneg
    intro u hu
    exact secondSingletonBlock_nonnegative r hr u hij hjk
  have h₂ : 0 ≤ ∑ u, ∑ v ∈ Finset.univ.erase u,
      secondPairBlock r u v i j k := by
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro v hv
    exact secondPairBlock_nonnegative r hr u v hij hjk
  have h₃ : 0 ≤ ∑ u, ∑ v ∈ Finset.univ.erase u,
      ∑ w ∈ (Finset.univ.erase u).erase v, secondTripleBlock r u v w i j k := by
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro v hv
    apply Finset.sum_nonneg
    intro w hw
    exact secondTripleBlock_nonnegative r hr u v w hij hjk
  unfold secondBlockSum
  exact add_nonneg
    (add_nonneg (add_nonneg h₀ h₁) (mul_nonneg (by norm_num) h₂))
    (mul_nonneg (by norm_num) h₃)

/-- Nonnegativity of the whole second summand in the three-row split. -/
theorem secondSummand_nonnegative {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 ≤ r u) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ polynomialMinor3 (factorPolynomial r) (X * (factorPolynomial r + G1 r))
      (X ^ 2 * (factorPolynomial r + 3 * G1 r + 2 * G2 r)) i j k := by
  rw [secondSummand_eq_secondBlockSum]
  exact secondBlockSum_nonnegative r hr hij hjk

/-- The second summand is strictly positive on the consecutive triples
covered by the factor-product strict Toeplitz theorem. -/
theorem secondSummand_consecutive_pos {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ u, 0 < r u) (k : ℕ) (hk : k ≤ n) :
    0 < polynomialMinor3 (factorPolynomial r) (X * (factorPolynomial r + G1 r))
      (X ^ 2 * (factorPolynomial r + 3 * G1 r + 2 * G2 r)) k (k + 1) (k + 2) := by
  rw [secondSummand_eq_secondBlockSum]
  have hzero : 0 < secondZeroBlock r k (k + 1) (k + 2) :=
    phiZero_fullFactor_consecutive_pos r hr k hk
  have hrest₁ : 0 ≤ ∑ u, secondSingletonBlock r u k (k + 1) (k + 2) := by
    apply Finset.sum_nonneg
    intro u hu
    exact secondSingletonBlock_nonnegative r (fun v ↦ (hr v).le) u (by omega) (by omega)
  have hrest₂ : 0 ≤ ∑ u, ∑ v ∈ Finset.univ.erase u,
      secondPairBlock r u v k (k + 1) (k + 2) := by
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro v hv
    exact secondPairBlock_nonnegative r (fun x ↦ (hr x).le) u v (by omega) (by omega)
  have hrest₃ : 0 ≤ ∑ u, ∑ v ∈ Finset.univ.erase u,
      ∑ w ∈ (Finset.univ.erase u).erase v,
        secondTripleBlock r u v w k (k + 1) (k + 2) := by
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro v hv
    apply Finset.sum_nonneg
    intro w hw
    exact secondTripleBlock_nonnegative r (fun x ↦ (hr x).le) u v w (by omega) (by omega)
  unfold secondBlockSum
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg hzero hrest₁)
      (mul_nonneg (by norm_num) hrest₂))
    (mul_nonneg (by norm_num) hrest₃)

/-! ## Two ordinary Eulerian steps -/

/-- One ordinary Eulerian differential step from degree parameter `n`. -/
noncomputable def ordinaryEulerianStep (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (1 + C (n + 1 : ℝ) * X) * p + X * (1 - X) * p.derivative

/-- For a positive linear-factor product, two successive ordinary Eulerian
steps give a strictly positive consecutive solid three-row minor. -/
theorem factorPolynomial_eulerianSteps_det3_consecutive_pos {n : ℕ}
    (r : Fin n → ℝ) (hr : ∀ u, 0 < r u) (k : ℕ) (hk : k ≤ n) :
    0 < polynomialMinor3 (factorPolynomial r)
      (ordinaryEulerianStep n (factorPolynomial r))
      (ordinaryEulerianStep (n + 1) (ordinaryEulerianStep n (factorPolynomial r)))
      k (k + 1) (k + 2) := by
  let P := factorPolynomial r
  let Q := ordinaryEulerianStep n P
  let R := ordinaryEulerianStep (n + 1) Q
  have hQ : Q = (1 + X) * P + X * G1 r := by
    dsimp [Q, P, ordinaryEulerianStep]
    exact ordinaryEulerian_Q_formula r
  have hR : R = (1 + 4 * X + X ^ 2) * P +
      3 * X * (1 + X) * G1 r + 2 * X ^ 2 * G2 r := by
    dsimp [R, ordinaryEulerianStep]
    rw [show C ((((n + 1 : ℕ) : ℝ) + 1)) = C (n + 2 : ℝ) by
      congr 1
      push_cast
      ring]
    exact ordinaryEulerian_R_formula r Q hQ
  let V₁ := X * (P + G1 r)
  let V₂ := X * P
  let V₃ := X ^ 2 * (P + 3 * G1 r + 2 * G2 r)
  have hQsplit : Q = P + V₁ := by
    rw [hQ]
    dsimp [V₁]
    ring
  have hRsplit : R = P + 3 * V₁ + V₂ + V₃ := by
    rw [hR]
    dsimp [V₁, V₂, V₃]
    ring
  have hfirstEq : polynomialMinor3 P V₁ V₂ k (k + 1) (k + 2) =
      polynomialMinor3 P (X * G1 r) (X * P) k (k + 1) (k + 2) := by
    dsimp [V₁, V₂]
    rw [mul_add, polynomialMinor3_add_middle]
    have hz : polynomialMinor3 P (X * P) (X * P) k (k + 1) (k + 2) = 0 := by
      simp [polynomialMinor3, threePolynomialRows, coefficientMatrix, det3]
      ring
    rw [hz, zero_add]
  have hfirst : 0 ≤ polynomialMinor3 P V₁ V₂ k (k + 1) (k + 2) := by
    rw [hfirstEq]
    dsimp [P]
    exact firstSummand_nonnegative r (fun u ↦ (hr u).le) (by omega) (by omega)
  have hsecond : 0 < polynomialMinor3 P V₁ V₃ k (k + 1) (k + 2) := by
    dsimp [P, V₁, V₃]
    exact secondSummand_consecutive_pos r hr k hk
  change 0 < polynomialMinor3 P Q R k (k + 1) (k + 2)
  rw [hQsplit, hRsplit, polynomialMinor3_three_row_split]
  exact add_pos_of_nonneg_of_pos hfirst hsecond

private theorem polynomialMinor3_eulerianPoly_eq_triangle (n i j k : ℕ) :
    polynomialMinor3 (eulerianPoly n) (eulerianPoly (n + 1))
        (eulerianPoly (n + 2)) i j k =
      det3 eulerianTriangle n (n + 1) (n + 2) i j k := by
  simp [polynomialMinor3, threePolynomialRows, coefficientMatrix,
    eulerianTriangle, det3]

/-- Row-level ordinary conclusion: every consecutive solid `3 × 3` minor
in rows `n,n+1,n+2` and within the support of row `n` is strictly positive. -/
theorem eulerianTriangle_det3_solid_pos (n k : ℕ) (hk : k ≤ n) :
    0 < det3 eulerianTriangle n (n + 1) (n + 2) k (k + 1) (k + 2) := by
  obtain ⟨r, hr, hfactor⟩ := eulerianPoly_exists_positive_linearFactors n
  have hfactor' : eulerianPoly n = factorPolynomial r := by
    simpa [factorPolynomial] using hfactor
  have h := factorPolynomial_eulerianSteps_det3_consecutive_pos r hr k hk
  rw [← hfactor'] at h
  change 0 < polynomialMinor3 (eulerianPoly n)
      (ordinaryEulerianStep n (eulerianPoly n))
      (ordinaryEulerianStep (n + 1) (ordinaryEulerianStep n (eulerianPoly n)))
      k (k + 1) (k + 2) at h
  rw [show ordinaryEulerianStep n (eulerianPoly n) = eulerianPoly (n + 1) by
    simp [ordinaryEulerianStep, eulerianPoly_succ]] at h
  rw [show ordinaryEulerianStep (n + 1) (eulerianPoly (n + 1)) =
      eulerianPoly (n + 2) by
    simpa [ordinaryEulerianStep, Nat.add_assoc] using (eulerianPoly_succ (n + 1)).symm] at h
  rwa [polynomialMinor3_eulerianPoly_eq_triangle] at h

end LeanCo.EulerianTP3
