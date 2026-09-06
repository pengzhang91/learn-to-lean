import LeanCo.EulerianTP3.SolidThree

/-!
# Local algebra for the generalized Eulerian three-row minor

This file formalizes the four local tables in the proof of Theorem 4.1 of
arXiv:2608.29224.  The global parameters are denoted by `a`, `b`, and `t`
(corresponding to `alpha n`, `alpha (n + 1)`, and `beta`).  The local variables
`r`, `s`, and `u` are parameters of positive linear factors `1 + r X`.

The definitions retain the two coefficient vectors

* `mu = (a, t)`, and
* `nu = (a * b, t * (a + b + t), 2 * t^2)`,

so that the weights record exactly the root-deletion expansion from the
paper.  As in `LocalAlgebra`, nonnegativity is proved for the weighted
aggregate, not for each individual determinant.
-/

namespace LeanCo.EulerianTP3

open scoped BigOperators Matrix
open Polynomial

/-! ## The parameter vectors and the four weighted local packages -/

/-- The coefficients of the two terms in
`V = a * B_n + t * G_1`. -/
noncomputable def generalizedMu (a t : ℝ) : Fin 2 → ℝ := ![a, t]

/-- The coefficients of the three terms in
`Q = a*b*B_n + t*(a+b+t)*G_1 + 2*t^2*G_2`. -/
noncomputable def generalizedNu (a b t : ℝ) : Fin 3 → ℝ :=
  ![a * b, t * (a + b + t), 2 * t ^ 2]

@[simp] theorem generalizedMu_zero (a t : ℝ) :
    generalizedMu a t (0 : Fin 2) = a := by rfl

@[simp] theorem generalizedMu_one (a t : ℝ) :
    generalizedMu a t (1 : Fin 2) = t := by rfl

@[simp] theorem generalizedNu_zero (a b t : ℝ) :
    generalizedNu a b t (0 : Fin 3) = a * b := by rfl

@[simp] theorem generalizedNu_one (a b t : ℝ) :
    generalizedNu a b t (1 : Fin 3) = t * (a + b + t) := by rfl

@[simp] theorem generalizedNu_two (a b t : ℝ) :
    generalizedNu a b t (2 : Fin 3) = 2 * t ^ 2 := by rfl

/-- Weight for the unique pair `(I,J) = (empty,empty)`. -/
noncomputable def generalizedPhiZeroWeights (a b t : ℝ) : Fin 1 → ℝ :=
  ![generalizedMu a t 0 * generalizedNu a b t 0]

/-- The three weights whose union is one fixed deleted factor. -/
noncomputable def generalizedPhiSingletonWeights (a b t r : ℝ) : Fin 3 → ℝ :=
  ![generalizedMu a t 0 * generalizedNu a b t 1 * (1 + r),
    generalizedMu a t 1 * generalizedNu a b t 0 * (1 + r),
    generalizedMu a t 1 * generalizedNu a b t 1 * (1 + r) ^ 2]

/-- The five weights whose union is a fixed pair of deleted factors. -/
noncomputable def generalizedPhiPairWeights (a b t r s : ℝ) : Fin 5 → ℝ :=
  ![generalizedMu a t 0 * generalizedNu a b t 2 * (1 + r) * (1 + s),
    generalizedMu a t 1 * generalizedNu a b t 1 * (1 + r) * (1 + s),
    generalizedMu a t 1 * generalizedNu a b t 1 * (1 + s) * (1 + r),
    generalizedMu a t 1 * generalizedNu a b t 2 * (1 + r) ^ 2 * (1 + s),
    generalizedMu a t 1 * generalizedNu a b t 2 * (1 + s) ^ 2 * (1 + r)]

/-- The three weights whose union is a fixed triple of deleted factors. -/
noncomputable def generalizedPhiTripleWeights (a b t r s u : ℝ) : Fin 3 → ℝ :=
  ![generalizedMu a t 1 * generalizedNu a b t 2 * (1 + r) * (1 + s) * (1 + u),
    generalizedMu a t 1 * generalizedNu a b t 2 * (1 + s) * (1 + r) * (1 + u),
    generalizedMu a t 1 * generalizedNu a b t 2 * (1 + u) * (1 + r) * (1 + s)]

/-!
The polynomial triples themselves are precisely the structural triples
`phiZeroTriples`, `phiSingletonTriples`, `phiPairTriples`, and
`phiTripleTriples` from `SolidThree`; only their weights change.
-/

noncomputable def generalizedPhiZero (a b t : ℝ) (i j k : ℕ) : ℝ :=
  generalizedMu a t 0 * generalizedNu a b t 0 *
    localMinor localOne (shiftOne localOne) (shiftTwo localOne) i j k

noncomputable def generalizedPhiSingleton (a b t r : ℝ) (i j k : ℕ) : ℝ :=
  generalizedMu a t 0 * generalizedNu a b t 1 * (1 + r) *
      localMinor (localLinear r) (shiftOne (localLinear r))
        (shiftTwo localOne) i j k
    + generalizedMu a t 1 * generalizedNu a b t 0 * (1 + r) *
      localMinor (localLinear r) (shiftOne localOne)
        (shiftTwo (localLinear r)) i j k
    + generalizedMu a t 1 * generalizedNu a b t 1 * (1 + r) ^ 2 *
      localMinor (localLinear r) (shiftOne localOne)
        (shiftTwo localOne) i j k

noncomputable def generalizedPhiPair (a b t r s : ℝ) (i j k : ℕ) : ℝ :=
  generalizedMu a t 0 * generalizedNu a b t 2 * (1 + r) * (1 + s) *
      localMinor (localQuadratic r s) (shiftOne (localQuadratic r s))
        (shiftTwo localOne) i j k
    + generalizedMu a t 1 * generalizedNu a b t 1 * (1 + r) * (1 + s) *
      localMinor (localQuadratic r s) (shiftOne (localLinear s))
        (shiftTwo (localLinear r)) i j k
    + generalizedMu a t 1 * generalizedNu a b t 1 * (1 + s) * (1 + r) *
      localMinor (localQuadratic r s) (shiftOne (localLinear r))
        (shiftTwo (localLinear s)) i j k
    + generalizedMu a t 1 * generalizedNu a b t 2 * (1 + r) ^ 2 * (1 + s) *
      localMinor (localQuadratic r s) (shiftOne (localLinear s))
        (shiftTwo localOne) i j k
    + generalizedMu a t 1 * generalizedNu a b t 2 * (1 + s) ^ 2 * (1 + r) *
      localMinor (localQuadratic r s) (shiftOne (localLinear r))
        (shiftTwo localOne) i j k

noncomputable def generalizedPhiTriple (a b t r s u : ℝ) (i j k : ℕ) : ℝ :=
  generalizedMu a t 1 * generalizedNu a b t 2 * (1 + r) * (1 + s) * (1 + u) *
      localMinor (localCubic r s u) (shiftOne (localQuadratic s u))
        (shiftTwo (localLinear r)) i j k
    + generalizedMu a t 1 * generalizedNu a b t 2 * (1 + s) * (1 + r) * (1 + u) *
      localMinor (localCubic r s u) (shiftOne (localQuadratic r u))
        (shiftTwo (localLinear s)) i j k
    + generalizedMu a t 1 * generalizedNu a b t 2 * (1 + u) * (1 + r) * (1 + s) *
      localMinor (localCubic r s u) (shiftOne (localQuadratic r s))
        (shiftTwo (localLinear u)) i j k

/-! ## Identification with weighted polynomial determinants -/

theorem generalizedPhiZero_weighted_eq (a b t : ℝ) (i j k : ℕ) :
    weightedCoefficientMinor3 (generalizedPhiZeroWeights a b t)
        (polynomialTripleCoefficients phiZeroTriples) i j k =
      generalizedPhiZero a b t i j k := by
  simp [weightedCoefficientMinor3, generalizedPhiZeroWeights, phiZeroTriples,
    polynomialTripleCoefficients, coefficientMinor3, tripleCoefficientMatrix,
    generalizedPhiZero, localMinor, det3]

theorem generalizedPhiSingleton_weighted_eq (a b t r : ℝ) (i j k : ℕ) :
    weightedCoefficientMinor3 (generalizedPhiSingletonWeights a b t r)
        (polynomialTripleCoefficients (phiSingletonTriples r)) i j k =
      generalizedPhiSingleton a b t r i j k := by
  simp [weightedCoefficientMinor3, generalizedPhiSingletonWeights,
    phiSingletonTriples, polynomialTripleCoefficients, coefficientMinor3,
    tripleCoefficientMatrix, generalizedPhiSingleton, localMinor, det3,
    Fin.sum_univ_succ]
  ring

theorem generalizedPhiPair_weighted_eq (a b t r s : ℝ) (i j k : ℕ) :
    weightedCoefficientMinor3 (generalizedPhiPairWeights a b t r s)
        (polynomialTripleCoefficients (phiPairTriples r s)) i j k =
      generalizedPhiPair a b t r s i j k := by
  simp [weightedCoefficientMinor3, generalizedPhiPairWeights, phiPairTriples,
    polynomialTripleCoefficients, coefficientMinor3, tripleCoefficientMatrix,
    generalizedPhiPair, localMinor, det3, Fin.sum_univ_succ]
  ring

theorem generalizedPhiTriple_weighted_eq (a b t r s u : ℝ) (i j k : ℕ) :
    weightedCoefficientMinor3 (generalizedPhiTripleWeights a b t r s u)
        (polynomialTripleCoefficients (phiTripleTriples r s u)) i j k =
      generalizedPhiTriple a b t r s u i j k := by
  simp [weightedCoefficientMinor3, generalizedPhiTripleWeights,
    phiTripleTriples, polynomialTripleCoefficients, coefficientMinor3,
    tripleCoefficientMatrix, generalizedPhiTriple, localMinor, det3,
    Fin.sum_univ_succ]
  ring

/-! ## The four exact tables -/

theorem generalizedPhiZero_table (a b t : ℝ) :
    generalizedPhiZero a b t 0 1 2 = a ^ 2 * b ∧
      generalizedPhiZero a b t 0 1 3 = 0 ∧
      generalizedPhiZero a b t 0 2 3 = 0 ∧
      generalizedPhiZero a b t 1 2 3 = 0 := by
  norm_num [generalizedPhiZero, localMinor,
    localOne, shiftOne, shiftTwo, det3]
  ring

theorem generalizedPhiSingleton_table (a b t r : ℝ) :
    generalizedPhiSingleton a b t r 0 1 2 =
        t * (1 + r) *
          (a ^ 2 + 2 * a * b + a * t * (r + 2) + t * (b + t) * (r + 1)) ∧
      generalizedPhiSingleton a b t r 0 1 3 = a * b * t * r * (1 + r) ∧
      generalizedPhiSingleton a b t r 0 2 3 = 0 ∧
      generalizedPhiSingleton a b t r 1 2 3 = 0 := by
  norm_num [generalizedPhiSingleton, localMinor,
    localOne, localLinear, shiftOne, shiftTwo, det3]
  repeat' apply And.intro
  all_goals ring

theorem generalizedPhiPair_table (a b t r s : ℝ) :
    generalizedPhiPair a b t r s 0 1 2 =
        2 * t ^ 2 * (1 + r) * (1 + s) *
          (2 * a + b + t * (r + s + 3)) ∧
      generalizedPhiPair a b t r s 0 1 3 =
        t ^ 2 * (1 + r) * (1 + s) * (r + s) * (a + b + t) ∧
      generalizedPhiPair a b t r s 0 2 3 =
        2 * t ^ 2 * r * s * (1 + r) * (1 + s) * (b + t) ∧
      generalizedPhiPair a b t r s 1 2 3 =
        t ^ 2 * r * s * (1 + r) * (1 + s) * (r + s) * (b - a + t) := by
  norm_num [generalizedPhiPair, localMinor,
    localOne, localLinear, localQuadratic, shiftOne, shiftTwo, det3]
  repeat' apply And.intro
  all_goals ring

theorem generalizedPhiTriple_table (a b t r s u : ℝ) :
    generalizedPhiTriple a b t r s u 0 1 2 =
        6 * t ^ 3 * (1 + r) * (1 + s) * (1 + u) ∧
      generalizedPhiTriple a b t r s u 0 1 3 =
        2 * t ^ 3 * (1 + r) * (1 + s) * (1 + u) * (r + s + u) ∧
      generalizedPhiTriple a b t r s u 0 2 3 =
        2 * t ^ 3 * (1 + r) * (1 + s) * (1 + u) *
          (r * s + r * u + s * u) ∧
      generalizedPhiTriple a b t r s u 1 2 3 =
        6 * t ^ 3 * (1 + r) * (1 + s) * (1 + u) * r * s * u := by
  norm_num [generalizedPhiTriple, localMinor,
    localLinear, localQuadratic, localCubic, shiftOne, shiftTwo, det3]
  repeat' apply And.intro
  all_goals ring

/-! ## Vanishing outside the four displayed ordered column triples -/

lemma generalizedPhiZero_eq_zero_of_four_le (a b t : ℝ) (i j k : ℕ)
    (hk : 4 ≤ k) : generalizedPhiZero a b t i j k = 0 := by
  unfold generalizedPhiZero
  rw [localMinor_eq_zero_of_last localOne_supported shiftOne_localOne_supported
    shiftTwo_localOne_supported i j k hk]
  ring

lemma generalizedPhiSingleton_eq_zero_of_four_le (a b t r : ℝ) (i j k : ℕ)
    (hk : 4 ≤ k) : generalizedPhiSingleton a b t r i j k = 0 := by
  unfold generalizedPhiSingleton
  rw [localMinor_eq_zero_of_last (localLinear_supported r)
      (shiftOne_localLinear_supported r) shiftTwo_localOne_supported i j k hk,
    localMinor_eq_zero_of_last (localLinear_supported r) shiftOne_localOne_supported
      (shiftTwo_localLinear_supported r) i j k hk,
    localMinor_eq_zero_of_last (localLinear_supported r) shiftOne_localOne_supported
      shiftTwo_localOne_supported i j k hk]
  ring

lemma generalizedPhiPair_eq_zero_of_four_le (a b t r s : ℝ) (i j k : ℕ)
    (hk : 4 ≤ k) : generalizedPhiPair a b t r s i j k = 0 := by
  unfold generalizedPhiPair
  rw [localMinor_eq_zero_of_last (localQuadratic_supported r s)
      (shiftOne_localQuadratic_supported r s) shiftTwo_localOne_supported i j k hk,
    localMinor_eq_zero_of_last (localQuadratic_supported r s)
      (shiftOne_localLinear_supported s) (shiftTwo_localLinear_supported r) i j k hk,
    localMinor_eq_zero_of_last (localQuadratic_supported r s)
      (shiftOne_localLinear_supported r) (shiftTwo_localLinear_supported s) i j k hk,
    localMinor_eq_zero_of_last (localQuadratic_supported r s)
      (shiftOne_localLinear_supported s) shiftTwo_localOne_supported i j k hk,
    localMinor_eq_zero_of_last (localQuadratic_supported r s)
      (shiftOne_localLinear_supported r) shiftTwo_localOne_supported i j k hk]
  ring

lemma generalizedPhiTriple_eq_zero_of_four_le (a b t r s u : ℝ) (i j k : ℕ)
    (hk : 4 ≤ k) : generalizedPhiTriple a b t r s u i j k = 0 := by
  unfold generalizedPhiTriple
  rw [localMinor_eq_zero_of_last (localCubic_supported r s u)
      (shiftOne_localQuadratic_supported s u) (shiftTwo_localLinear_supported r) i j k hk,
    localMinor_eq_zero_of_last (localCubic_supported r s u)
      (shiftOne_localQuadratic_supported r u) (shiftTwo_localLinear_supported s) i j k hk,
    localMinor_eq_zero_of_last (localCubic_supported r s u)
      (shiftOne_localQuadratic_supported r s) (shiftTwo_localLinear_supported u) i j k hk]
  ring

private lemma generalized_ordered_triple_through_three {i j k : ℕ}
    (hij : i < j) (hjk : j < k) (hk : k ≤ 3) :
    (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 0 ∧ j = 1 ∧ k = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 3) ∨ (i = 1 ∧ j = 2 ∧ k = 3) := by
  omega

/-! ## Nonnegativity of every ordered local minor -/

theorem generalizedPhiZero_ordered_nonnegative (a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ generalizedPhiZero a b t i j k := by
  by_cases hk : k ≤ 3
  · rcases generalized_ordered_triple_through_three hij hjk hk with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals have htable := generalizedPhiZero_table a b t
    all_goals simp only [htable.1, htable.2.1, htable.2.2.1, htable.2.2.2]
    all_goals positivity
  · rw [generalizedPhiZero_eq_zero_of_four_le a b t i j k (by omega)]

theorem generalizedPhiSingleton_ordered_nonnegative (a b t r : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hr : 0 ≤ r)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ generalizedPhiSingleton a b t r i j k := by
  by_cases hk : k ≤ 3
  · rcases generalized_ordered_triple_through_three hij hjk hk with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals have htable := generalizedPhiSingleton_table a b t r
    all_goals simp only [htable.1, htable.2.1, htable.2.2.1, htable.2.2.2]
    all_goals positivity
  · rw [generalizedPhiSingleton_eq_zero_of_four_le a b t r i j k (by omega)]

theorem generalizedPhiPair_ordered_nonnegative (a b t r s : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hdelta : 0 ≤ b - a + t)
    (hr : 0 ≤ r) (hs : 0 ≤ s) {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ generalizedPhiPair a b t r s i j k := by
  by_cases hk : k ≤ 3
  · rcases generalized_ordered_triple_through_three hij hjk hk with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals have htable := generalizedPhiPair_table a b t r s
    all_goals simp only [htable.1, htable.2.1, htable.2.2.1, htable.2.2.2]
    all_goals positivity
  · rw [generalizedPhiPair_eq_zero_of_four_le a b t r s i j k (by omega)]

theorem generalizedPhiTriple_ordered_nonnegative (a b t r s u : ℝ)
    (ht : 0 < t) (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ u)
    {i j k : ℕ} (hij : i < j) (hjk : j < k) :
    0 ≤ generalizedPhiTriple a b t r s u i j k := by
  by_cases hk : k ≤ 3
  · rcases generalized_ordered_triple_through_three hij hjk hk with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl, rfl⟩
    all_goals have htable := generalizedPhiTriple_table a b t r s u
    all_goals simp only [htable.1, htable.2.1, htable.2.2.1, htable.2.2.2]
    all_goals positivity
  · rw [generalizedPhiTriple_eq_zero_of_four_le a b t r s u i j k (by omega)]

/-! ## Weighted polynomial forms and preservation by a common factor -/

theorem generalizedPhiZero_weighted_ordered_nonnegative (a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    WeightedOrderedDet3Nonnegative (generalizedPhiZeroWeights a b t)
      (polynomialTripleCoefficients phiZeroTriples) := by
  intro i j k hij hjk
  rw [generalizedPhiZero_weighted_eq]
  exact generalizedPhiZero_ordered_nonnegative a b t ha hb hij hjk

theorem generalizedPhiSingleton_weighted_ordered_nonnegative
    (a b t r : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hr : 0 ≤ r) :
    WeightedOrderedDet3Nonnegative (generalizedPhiSingletonWeights a b t r)
      (polynomialTripleCoefficients (phiSingletonTriples r)) := by
  intro i j k hij hjk
  rw [generalizedPhiSingleton_weighted_eq]
  exact generalizedPhiSingleton_ordered_nonnegative a b t r ha hb ht hr hij hjk

theorem generalizedPhiPair_weighted_ordered_nonnegative
    (a b t r s : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hdelta : 0 ≤ b - a + t) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    WeightedOrderedDet3Nonnegative (generalizedPhiPairWeights a b t r s)
      (polynomialTripleCoefficients (phiPairTriples r s)) := by
  intro i j k hij hjk
  rw [generalizedPhiPair_weighted_eq]
  exact generalizedPhiPair_ordered_nonnegative a b t r s ha hb ht hdelta hr hs hij hjk

theorem generalizedPhiTriple_weighted_ordered_nonnegative
    (a b t r s u : ℝ) (ht : 0 < t) (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    WeightedOrderedDet3Nonnegative (generalizedPhiTripleWeights a b t r s u)
      (polynomialTripleCoefficients (phiTripleTriples r s u)) := by
  intro i j k hij hjk
  rw [generalizedPhiTriple_weighted_eq]
  exact generalizedPhiTriple_ordered_nonnegative a b t r s u ht hr hs hu hij hjk

/-- All four union-cardinality packages are nonnegative under exactly the
parameter inequalities used in Theorem 4.1. -/
theorem generalizedPhi_all_weighted_ordered_nonnegative
    (a b t r s u : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hdelta : 0 ≤ b - a + t) (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    WeightedOrderedDet3Nonnegative (generalizedPhiZeroWeights a b t)
        (polynomialTripleCoefficients phiZeroTriples) ∧
      WeightedOrderedDet3Nonnegative (generalizedPhiSingletonWeights a b t r)
        (polynomialTripleCoefficients (phiSingletonTriples r)) ∧
      WeightedOrderedDet3Nonnegative (generalizedPhiPairWeights a b t r s)
        (polynomialTripleCoefficients (phiPairTriples r s)) ∧
      WeightedOrderedDet3Nonnegative (generalizedPhiTripleWeights a b t r s u)
        (polynomialTripleCoefficients (phiTripleTriples r s u)) := by
  refine ⟨generalizedPhiZero_weighted_ordered_nonnegative a b t ha hb, ?_⟩
  refine ⟨generalizedPhiSingleton_weighted_ordered_nonnegative a b t r ha hb ht hr, ?_⟩
  exact ⟨generalizedPhiPair_weighted_ordered_nonnegative
      a b t r s ha hb ht hdelta hr hs,
    generalizedPhiTriple_weighted_ordered_nonnegative a b t r s u ht hr hs hu⟩

theorem generalizedPhiZero_block_nonnegative {ι : Type*}
    (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (factors : Finset ι) (roots : ι → ℝ)
    (hroots : ∀ i ∈ factors, 0 ≤ roots i) :
    WeightedOrderedDet3Nonnegative (generalizedPhiZeroWeights a b t)
      (polynomialTripleCoefficients
        (fun q row ↦ phiZeroTriples q row * factorPolynomialOn factors roots)) :=
  weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    (generalizedPhiZeroWeights a b t) phiZeroTriples factors roots hroots
      (generalizedPhiZero_weighted_ordered_nonnegative a b t ha hb)

theorem generalizedPhiSingleton_block_nonnegative {ι : Type*}
    (a b t r : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hr : 0 ≤ r)
    (factors : Finset ι) (roots : ι → ℝ)
    (hroots : ∀ i ∈ factors, 0 ≤ roots i) :
    WeightedOrderedDet3Nonnegative (generalizedPhiSingletonWeights a b t r)
      (polynomialTripleCoefficients
        (fun q row ↦ phiSingletonTriples r q row * factorPolynomialOn factors roots)) :=
  weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    (generalizedPhiSingletonWeights a b t r) (phiSingletonTriples r)
      factors roots hroots
      (generalizedPhiSingleton_weighted_ordered_nonnegative a b t r ha hb ht hr)

theorem generalizedPhiPair_block_nonnegative {ι : Type*}
    (a b t r s : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hdelta : 0 ≤ b - a + t) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (factors : Finset ι) (roots : ι → ℝ)
    (hroots : ∀ i ∈ factors, 0 ≤ roots i) :
    WeightedOrderedDet3Nonnegative (generalizedPhiPairWeights a b t r s)
      (polynomialTripleCoefficients
        (fun q row ↦ phiPairTriples r s q row * factorPolynomialOn factors roots)) :=
  weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    (generalizedPhiPairWeights a b t r s) (phiPairTriples r s)
      factors roots hroots
      (generalizedPhiPair_weighted_ordered_nonnegative
        a b t r s ha hb ht hdelta hr hs)

theorem generalizedPhiTriple_block_nonnegative {ι : Type*}
    (a b t r s u : ℝ) (ht : 0 < t) (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (factors : Finset ι) (roots : ι → ℝ)
    (hroots : ∀ i ∈ factors, 0 ≤ roots i) :
    WeightedOrderedDet3Nonnegative (generalizedPhiTripleWeights a b t r s u)
      (polynomialTripleCoefficients
        (fun q row ↦ phiTripleTriples r s u q row * factorPolynomialOn factors roots)) :=
  weightedPolynomialTriple_mul_factorPolynomialOn_nonnegative
    (generalizedPhiTripleWeights a b t r s u) (phiTripleTriples r s u)
      factors roots hroots
      (generalizedPhiTriple_weighted_ordered_nonnegative a b t r s u ht hr hs hu)

/-- Simultaneous block form: after multiplying every row in every local
package by the same product of nonnegative linear factors, all four weighted
ordered-minor assertions remain nonnegative. -/
theorem generalizedPhi_all_blocks_nonnegative {ι : Type*}
    (a b t r s u : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hdelta : 0 ≤ b - a + t) (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ u)
    (factors : Finset ι) (roots : ι → ℝ)
    (hroots : ∀ i ∈ factors, 0 ≤ roots i) :
    WeightedOrderedDet3Nonnegative (generalizedPhiZeroWeights a b t)
        (polynomialTripleCoefficients
          (fun q row ↦ phiZeroTriples q row * factorPolynomialOn factors roots)) ∧
      WeightedOrderedDet3Nonnegative (generalizedPhiSingletonWeights a b t r)
        (polynomialTripleCoefficients
          (fun q row ↦ phiSingletonTriples r q row * factorPolynomialOn factors roots)) ∧
      WeightedOrderedDet3Nonnegative (generalizedPhiPairWeights a b t r s)
        (polynomialTripleCoefficients
          (fun q row ↦ phiPairTriples r s q row * factorPolynomialOn factors roots)) ∧
      WeightedOrderedDet3Nonnegative (generalizedPhiTripleWeights a b t r s u)
        (polynomialTripleCoefficients
          (fun q row ↦ phiTripleTriples r s u q row * factorPolynomialOn factors roots)) := by
  refine ⟨generalizedPhiZero_block_nonnegative
      a b t ha hb factors roots hroots, ?_⟩
  refine ⟨generalizedPhiSingleton_block_nonnegative
      a b t r ha hb ht hr factors roots hroots, ?_⟩
  exact ⟨generalizedPhiPair_block_nonnegative
      a b t r s ha hb ht hdelta hr hs factors roots hroots,
    generalizedPhiTriple_block_nonnegative
      a b t r s u ht hr hs hu factors roots hroots⟩

end LeanCo.EulerianTP3
