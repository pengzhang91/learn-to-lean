import LeanCo.CyclicBraidArrangement.ArrangementMainTheorem

/-!
# Sharpness example for cyclic compatibility

This file formalizes Remark 2.2.  The three-label deformation has one
nonzero entry, from label `1` to label `2` in zero-based notation.  We prove
directly that it is not cyclically compatible, record the two reduced
finite-field polynomials from the remark, and verify that translation by the
one-sided parameter misses the extended polynomial by the constant `1`.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace SharpnessExample

/-- The matrix in Remark 2.2 (paper labels are one-based). -/
def matrix : DeformationMatrix 3 where
  entry i j := if i = 1 ∧ j = 2 then 2 else 0
  diagonal_zero i := by
    split_ifs with h
    · omega
    · rfl

/-- The one-sided extension parameter `(1,0,0)`. -/
def alpha : Fin 3 → ℕ := ![1, 0, 0]

/-- The zero column parameter used in the remark. -/
def beta : Fin 3 → ℕ := fun _ ↦ 0

/-- Failure occurs at paper labels `(2,1,3)`, i.e. `(1,0,2)` here. -/
theorem not_cyclicallyCompatible : ¬matrix.CyclicallyCompatible := by
  intro h
  have hbad := h (1 : Fin 3) (0 : Fin 3) (2 : Fin 3)
    (by decide) (by decide) (by decide)
  change 2 ≤ 0 + 0 + 1 at hbad
  omega

/-- The normalized cyclic order `0,1,2`. -/
def cycle012 : DeformationMatrix.NormalizedCycle 3 :=
  ⟨Equiv.refl (Fin 3), rfl⟩

/-- The other normalized cyclic order, `0,2,1`. -/
def cycle021 : DeformationMatrix.NormalizedCycle 3 :=
  ⟨Equiv.neg (Fin 3), by decide⟩

private theorem distance_cycle012_21 {q : ℕ}
    (G : DeformationMatrix.GapVector 3 q) :
    (DeformationMatrix.CirclePlacement.mk cycle012.1 G).labelDistance 2 1 =
      (G.gap 2 + 1) + (G.gap 0 + 1) := by
  norm_num [DeformationMatrix.CirclePlacement.labelDistance,
    DeformationMatrix.CirclePlacement.labelSteps,
    DeformationMatrix.CirclePlacement.clockwiseDistance,
    DeformationMatrix.cyclicIndex, cycle012]
  rw [show (1 : Fin 3) - 2 = 2 by decide]
  norm_num [DeformationMatrix.cyclicIndex, Finset.sum_range_succ]
  apply congrArg G.gap
  decide

private theorem distance_cycle021_12 {q : ℕ}
    (G : DeformationMatrix.GapVector 3 q) :
    (DeformationMatrix.CirclePlacement.mk cycle021.1 G).labelDistance 1 2 =
      (G.gap 2 + 1) + (G.gap 0 + 1) := by
  have hneg0 : -(0 : Fin 3) = 0 := by decide
  have hneg1 : -(1 : Fin 3) = 2 := by decide
  have hneg2 : -(2 : Fin 3) = 1 := by decide
  norm_num [DeformationMatrix.CirclePlacement.labelDistance,
    DeformationMatrix.CirclePlacement.labelSteps,
    DeformationMatrix.CirclePlacement.clockwiseDistance,
    DeformationMatrix.cyclicIndex, cycle021, hneg0, hneg1, hneg2]
  rw [show -(2 : Fin 3) + 1 = 2 by decide,
    show -(1 : Fin 3) = 2 by decide]
  norm_num [DeformationMatrix.cyclicIndex, Finset.sum_range_succ]
  apply congrArg G.gap
  decide

private theorem clockwiseDistance_pos {n q : ℕ} [NeZero n]
    (P : DeformationMatrix.CirclePlacement n q) (k : Fin n) (s : ℕ)
    (hs : 0 < s) : 0 < P.clockwiseDistance k s := by
  have hzero : 0 ∈ Finset.range s := Finset.mem_range.mpr hs
  have hle : P.gaps.gap (DeformationMatrix.cyclicIndex n k 0) + 1 ≤
      ∑ r ∈ Finset.range s,
        (P.gaps.gap (DeformationMatrix.cyclicIndex n k r) + 1) :=
    Finset.single_le_sum
      (s := Finset.range s)
      (f := fun r ↦ P.gaps.gap (DeformationMatrix.cyclicIndex n k r) + 1)
      (fun _ _ ↦ Nat.zero_le _) hzero
  exact (Nat.zero_lt_succ _).trans_le hle

private theorem labelDistance_pos {n q : ℕ} [NeZero n]
    (P : DeformationMatrix.CirclePlacement n q) {a c : Fin n}
    (hac : a ≠ c) : 0 < P.labelDistance a c :=
  clockwiseDistance_pos P (P.order.symm a) (P.labelSteps a c)
    (DeformationMatrix.labelSteps_pos P hac)

private theorem safe_cycle012_iff {q : ℕ} (G : DeformationMatrix.GapVector 3 q) :
    (DeformationMatrix.CirclePlacement.mk cycle012.1 G).AvoidsEveryOrderedPair matrix ↔
      2 ≤ G.gap 1 := by
  constructor
  · intro h
    have h12 := h (1 : Fin 3) (2 : Fin 3) (by decide)
    change 2 < G.gap 1 + 1 at h12
    omega
  · intro h a c hac
    by_cases hpair : a = 1 ∧ c = 2
    · rcases hpair with ⟨rfl, rfl⟩
      change 2 < G.gap 1 + 1
      omega
    · have hzero : matrix.entry a c = 0 := by simp [matrix, hpair]
      rw [hzero]
      exact labelDistance_pos _ hac

private theorem safe_cycle021_iff {q : ℕ} (G : DeformationMatrix.GapVector 3 q) :
    (DeformationMatrix.CirclePlacement.mk cycle021.1 G).AvoidsEveryOrderedPair matrix ↔
      0 < G.gap 0 + G.gap 2 := by
  constructor
  · intro h
    have h12 := h (1 : Fin 3) (2 : Fin 3) (by decide)
    rw [distance_cycle021_12] at h12
    change 2 < (G.gap 2 + 1) + (G.gap 0 + 1) at h12
    omega
  · intro h a c hac
    by_cases hpair : a = 1 ∧ c = 2
    · rcases hpair with ⟨rfl, rfl⟩
      rw [distance_cycle021_12]
      change 2 < (G.gap 2 + 1) + (G.gap 0 + 1)
      omega
    · have hzero : matrix.entry a c = 0 := by simp [matrix, hpair]
      rw [hzero]
      exact labelDistance_pos _ hac

private theorem cycle012_ne_cycle021 : cycle012 ≠ cycle021 := by
  intro h
  have h1 := congrArg (fun w : DeformationMatrix.NormalizedCycle 3 ↦ w.1 (1 : Fin 3)) h
  change (1 : Fin 3) = 2 at h1
  exact (by decide : (1 : Fin 3) ≠ 2) h1

/-- There are exactly two normalized cyclic orders on three labels. -/
theorem normalizedCycles_three :
    (Finset.univ : Finset (DeformationMatrix.NormalizedCycle 3)) =
      {cycle012, cycle021} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, DeformationMatrix.card_normalizedCycle]
  norm_num [cycle012_ne_cycle021]

theorem matrix_cycleWeight_012 : matrix.cycleWeight cycle012.1 = 2 := by
  decide

theorem matrix_cycleWeight_021 : matrix.cycleWeight cycle021.1 = 0 := by
  decide

private theorem adjacent_cycle012_iff {q : ℕ}
    (G : DeformationMatrix.GapVector 3 q) :
    (DeformationMatrix.CirclePlacement.mk cycle012.1 G).AdjacentBounds matrix ↔
      2 ≤ G.gap 1 := by
  constructor
  · intro h
    have h1 := h (1 : Fin 3)
    change 2 ≤ G.gap 1 at h1
    exact h1
  · intro h k
    fin_cases k
    · change 0 ≤ G.gap 0
      omega
    · change 2 ≤ G.gap 1
      exact h
    · change 0 ≤ G.gap 2
      omega

private theorem matrix_cycle021_adjacent_zero (k : Fin 3) :
    matrix.entry (cycle021.1 k)
      (cycle021.1 (DeformationMatrix.nextPosition 3 k)) = 0 := by
  fin_cases k <;> decide

private theorem adjacent_cycle021 {q : ℕ}
    (G : DeformationMatrix.GapVector 3 q) :
    (DeformationMatrix.CirclePlacement.mk cycle021.1 G).AdjacentBounds matrix := by
  intro k
  rw [matrix_cycle021_adjacent_zero]
  exact Nat.zero_le _

private noncomputable def safe012EquivAdjacent (q : ℕ) :
    DeformationMatrix.FixedOrderSafeGaps matrix q cycle012.1 ≃
      DeformationMatrix.FixedOrderAdjacentGaps matrix q cycle012.1 :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun G ↦
    (safe_cycle012_iff G).trans (adjacent_cycle012_iff G).symm)

private noncomputable def adjacent021EquivGapVector (q : ℕ) :
    DeformationMatrix.FixedOrderAdjacentGaps matrix q cycle021.1 ≃
      DeformationMatrix.GapVector 3 q where
  toFun G := G.1
  invFun G := ⟨G, adjacent_cycle021 G⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact safe count for the order `0,1,2`. -/
theorem card_safe_cycle012 (q : ℕ) (hq : 5 ≤ q) :
    Fintype.card (DeformationMatrix.FixedOrderSafeGaps matrix q cycle012.1) =
      (q - 3).choose 2 := by
  have hfit : 3 + matrix.cycleWeight cycle012.1 ≤ q := by
    rw [matrix_cycleWeight_012]
    exact hq
  calc
    Fintype.card (DeformationMatrix.FixedOrderSafeGaps matrix q cycle012.1) =
        Fintype.card
          (DeformationMatrix.FixedOrderAdjacentGaps matrix q cycle012.1) :=
      Fintype.card_congr (safe012EquivAdjacent q)
    _ = Fintype.card (matrix.FixedCycleGaps q cycle012.1) :=
      (Fintype.card_congr
        (DeformationMatrix.fixedCycleGapsEquivAdjacent
          matrix q cycle012.1 hfit)).symm
    _ = (q - matrix.cycleWeight cycle012.1 - 1).choose (3 - 1) :=
      DeformationMatrix.card_fixedCycleGaps matrix q cycle012.1 hfit
    _ = (q - 3).choose 2 := by
      have hw : matrix.cycleWeight cycle012.1 = 2 := by decide
      have harg : q - matrix.cycleWeight cycle012.1 - 1 = q - 3 := by omega
      rw [harg]

/-- The sole bad gap vector for the order `0,2,1`: all slack lies between
labels `2` and `1`, so the clockwise distance from `1` to `2` is only two. -/
def badGap021 (q : ℕ) : DeformationMatrix.GapVector 3 q where
  gap := ![0, q - 3, 0]
  sum_eq := by simp [Fin.sum_univ_three]

private theorem badGap021_not_safe (q : ℕ) :
    ¬DeformationMatrix.CirclePlacement.AvoidsEveryOrderedPair matrix
      (DeformationMatrix.CirclePlacement.mk cycle021.1 (badGap021 q)) := by
  rw [safe_cycle021_iff]
  simp [badGap021]

private theorem not_safe_cycle021_unique {q : ℕ}
    (G : DeformationMatrix.GapVector 3 q)
    (hG : ¬DeformationMatrix.CirclePlacement.AvoidsEveryOrderedPair matrix
      (DeformationMatrix.CirclePlacement.mk cycle021.1 G)) :
    G = badGap021 q := by
  have hnot : ¬0 < G.gap 0 + G.gap 2 := by
    rwa [safe_cycle021_iff] at hG
  have h0 : G.gap 0 = 0 := by omega
  have h2 : G.gap 2 = 0 := by omega
  have hsum := G.sum_eq
  simp only [Fin.sum_univ_three] at hsum
  cases G with
  | mk gap sum_eq =>
    simp only at h0 h2 hsum ⊢
    congr
    funext k
    fin_cases k
    · simpa [badGap021] using h0
    · simp
      omega
    · simpa [badGap021] using h2

private theorem card_gapVector_three (q : ℕ) (hq : 3 ≤ q) :
    Fintype.card (DeformationMatrix.GapVector 3 q) = (q - 1).choose 2 := by
  have hfit : 3 + matrix.cycleWeight cycle021.1 ≤ q := by
    have hw : matrix.cycleWeight cycle021.1 = 0 := by decide
    omega
  calc
    Fintype.card (DeformationMatrix.GapVector 3 q) =
        Fintype.card
          (DeformationMatrix.FixedOrderAdjacentGaps matrix q cycle021.1) :=
      (Fintype.card_congr (adjacent021EquivGapVector q)).symm
    _ = Fintype.card (matrix.FixedCycleGaps q cycle021.1) :=
      (Fintype.card_congr
        (DeformationMatrix.fixedCycleGapsEquivAdjacent
          matrix q cycle021.1 hfit)).symm
    _ = (q - matrix.cycleWeight cycle021.1 - 1).choose (3 - 1) :=
      DeformationMatrix.card_fixedCycleGaps matrix q cycle021.1 hfit
    _ = (q - 1).choose 2 := by
      have hw : matrix.cycleWeight cycle021.1 = 0 := by decide
      have harg : q - matrix.cycleWeight cycle021.1 - 1 = q - 1 := by omega
      rw [harg]

/-- Exact safe count for the order `0,2,1`; the subtraction is the unique
non-adjacent obstruction exhibited by `badGap021`. -/
theorem card_safe_cycle021 (q : ℕ) (hq : 3 ≤ q) :
    Fintype.card (DeformationMatrix.FixedOrderSafeGaps matrix q cycle021.1) =
      (q - 1).choose 2 - 1 := by
  classical
  let safe : DeformationMatrix.GapVector 3 q → Prop := fun G ↦
    DeformationMatrix.CirclePlacement.AvoidsEveryOrderedPair matrix
      (DeformationMatrix.CirclePlacement.mk cycle021.1 G)
  have hcomplement := Fintype.card_subtype_compl (fun G :
    DeformationMatrix.GapVector 3 q ↦ ¬safe G)
  have hbad : Fintype.card {G : DeformationMatrix.GapVector 3 q // ¬safe G} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨badGap021 q, ?_⟩, ?_⟩
    · simpa [safe] using badGap021_not_safe q
    · intro G
      apply Subtype.ext
      apply not_safe_cycle021_unique G.1
      simpa [safe] using G.2
  have hcard : Fintype.card {G : DeformationMatrix.GapVector 3 q // safe G} =
      Fintype.card (DeformationMatrix.GapVector 3 q) - 1 := by
    rw [hbad] at hcomplement
    simpa only [not_not] using hcomplement
  change Fintype.card {G : DeformationMatrix.GapVector 3 q // safe G} = _
  rw [hcard, card_gapVector_three q hq]

/-- The all-pair complement-orbit count is the sum of the two exact order
counts.  No adjacent-gap replacement is used for the non-compatible order. -/
theorem base_complement_count (q : ℕ) (hq : 5 ≤ q) :
    matrix.finiteFieldComplementOrbitCount q =
      (q - 3).choose 2 + ((q - 1).choose 2 - 1) := by
  classical
  unfold DeformationMatrix.finiteFieldComplementOrbitCount
  rw [normalizedCycles_three]
  simp only [Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, cycle012_ne_cycle021, not_false_eq_true]
  rw [card_safe_cycle012 q hq, card_safe_cycle021 q (by omega)]

/-- The base reduced polynomial displayed in Remark 2.2. -/
noncomputable def basePolynomial : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.C 5 * Polynomial.X + Polynomial.C 6

/-- The reduced polynomial of the one-sided extension displayed there. -/
noncomputable def extendedPolynomial : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.C 7 * Polynomial.X + Polynomial.C 13

/-- The polynomial obtained by translating the base polynomial by one. -/
noncomputable def translatedBasePolynomial : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.C 7 * Polynomial.X + Polynomial.C 12

private theorem chooseTwo_cast (m : ℕ) (hm : 2 ≤ m) :
    ((m.choose 2 : ℕ) : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  rw [← generalizedChoose_natCast m 2 hm]
  norm_num [generalizedChoose, Finset.prod_range_succ]

@[simp] theorem eval_basePolynomial (t : ℚ) :
    Polynomial.eval t basePolynomial = t ^ 2 - 5 * t + 6 := by
  simp [basePolynomial]

@[simp] theorem eval_extendedPolynomial (t : ℚ) :
    Polynomial.eval t extendedPolynomial = t ^ 2 - 7 * t + 13 := by
  simp [extendedPolynomial]

@[simp] theorem eval_translatedBasePolynomial (t : ℚ) :
    Polynomial.eval t translatedBasePolynomial = t ^ 2 - 7 * t + 12 := by
  simp [translatedBasePolynomial]

/-- For every `q ≥ 5`, the displayed base polynomial evaluates to the actual
all-pair-safe complement-orbit count. -/
theorem eval_basePolynomial_eq_complement_count (q : ℕ) (hq : 5 ≤ q) :
    Polynomial.eval (q : ℚ) basePolynomial =
      (matrix.finiteFieldComplementOrbitCount q : ℚ) := by
  rw [base_complement_count q hq, Nat.cast_add]
  have hchoosePos : 0 < (q - 1).choose 2 :=
    Nat.choose_pos (by omega : 2 ≤ q - 1)
  have hchoose : 1 ≤ (q - 1).choose 2 := by omega
  rw [Nat.cast_sub hchoose]
  rw [chooseTwo_cast (q - 3) (by omega), chooseTwo_cast (q - 1) (by omega)]
  rw [eval_basePolynomial]
  push_cast [Nat.cast_sub (by omega : 3 ≤ q),
    Nat.cast_sub (by omega : 1 ≤ q)]
  ring

/-- The base polynomial has the independent all-natural finite-field
specification used for a reduced characteristic polynomial. -/
theorem base_isReducedFiniteFieldPolynomial :
    matrix.IsReducedFiniteFieldPolynomial basePolynomial :=
  ⟨5, eval_basePolynomial_eq_complement_count⟩

theorem base_isReducedPrimeFiniteFieldPolynomial :
    matrix.IsReducedPrimeFiniteFieldPolynomial basePolynomial :=
  DeformationMatrix.isReducedFiniteFieldPolynomial_toPrime matrix
    base_isReducedFiniteFieldPolynomial

/-- The one-sided deformation in the second displayed polynomial. -/
def extendedMatrix : DeformationMatrix 3 := matrix.extend alpha beta

/-- The added outgoing unit repairs the sole failed triangle inequality. -/
theorem extendedMatrix_cyclicallyCompatible :
    extendedMatrix.CyclicallyCompatible := by
  intro a b c hab hac hbc
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [extendedMatrix, matrix, alpha, beta,
      DeformationMatrix.extend, Fin.ext_iff] at *

theorem extendedMatrix_cycleWeight_012 :
    extendedMatrix.cycleWeight cycle012.1 = 3 := by
  decide

theorem extendedMatrix_cycleWeight_021 :
    extendedMatrix.cycleWeight cycle021.1 = 1 := by
  decide

/-- For the repaired matrix, the independently constructed cyclic polynomial
is exactly the extended polynomial displayed in Remark 2.2. -/
theorem cyclePolynomial_extendedMatrix :
    cyclePolynomial extendedMatrix = extendedPolynomial := by
  apply Polynomial.funext
  intro t
  rw [eval_cyclePolynomial, eval_extendedPolynomial]
  unfold cycleFormula
  rw [normalizedCycles_three]
  simp only [Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, cycle012_ne_cycle021, not_false_eq_true]
  rw [extendedMatrix_cycleWeight_012, extendedMatrix_cycleWeight_021]
  norm_num [generalizedChoose, Finset.prod_range_succ]
  ring

/-- Every sufficiently large natural finite field count for the repaired
matrix is evaluated by the displayed extension polynomial. -/
theorem eval_extendedPolynomial_eq_complement_count (q : ℕ) (hq : 6 ≤ q) :
    Polynomial.eval (q : ℚ) extendedPolynomial =
      (extendedMatrix.finiteFieldComplementOrbitCount q : ℚ) := by
  rw [← cyclePolynomial_extendedMatrix, eval_cyclePolynomial]
  symm
  apply DeformationMatrix.finiteFieldComplementOrbitCount_eq_cycleFormula
    extendedMatrix extendedMatrix_cyclicallyCompatible q
  intro w
  have hwmem : w ∈ ({cycle012, cycle021} :
      Finset (DeformationMatrix.NormalizedCycle 3)) := by
    rw [← normalizedCycles_three]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwmem
  rcases hwmem with rfl | rfl
  · rw [extendedMatrix_cycleWeight_012]
    omega
  · rw [extendedMatrix_cycleWeight_021]
    omega

/-- Thus the extension polynomial also has a direct all-natural finite-field
specification (and consequently the prime-only version). -/
theorem extended_isReducedFiniteFieldPolynomial :
    extendedMatrix.IsReducedFiniteFieldPolynomial extendedPolynomial := by
  exact ⟨6, eval_extendedPolynomial_eq_complement_count⟩

theorem extended_isReducedPrimeFiniteFieldPolynomial :
    extendedMatrix.IsReducedPrimeFiniteFieldPolynomial extendedPolynomial :=
  DeformationMatrix.isReducedFiniteFieldPolynomial_toPrime extendedMatrix
    extended_isReducedFiniteFieldPolynomial

/-- Any independently supplied reduced polynomial satisfying the finite-field
method for the base arrangement is forced to be the displayed polynomial. -/
theorem basePolynomial_unique {P : Polynomial ℚ}
    (hP : matrix.IsReducedPrimeFiniteFieldPolynomial P) :
    P = basePolynomial :=
  DeformationMatrix.isReducedPrimeFiniteFieldPolynomial_unique matrix hP
    base_isReducedPrimeFiniteFieldPolynomial

/-- The analogous uniqueness statement for the one-sided extension. -/
theorem extendedPolynomial_unique {P : Polynomial ℚ}
    (hP : extendedMatrix.IsReducedPrimeFiniteFieldPolynomial P) :
    P = extendedPolynomial :=
  DeformationMatrix.isReducedPrimeFiniteFieldPolynomial_unique extendedMatrix hP
    extended_isReducedPrimeFiniteFieldPolynomial

theorem alpha_sum : ∑ i, alpha i = 1 := by
  decide

theorem beta_sum : ∑ i, beta i = 0 := by
  simp [beta]

/-- Direct symbolic verification of the translation calculation in the paper. -/
theorem translate_base_by_one :
    translatePolynomial basePolynomial 1 = translatedBasePolynomial := by
  apply Polynomial.funext
  intro t
  simp [translatePolynomial, basePolynomial, translatedBasePolynomial]
  ring

/-- The extension polynomial is not the translated base polynomial. -/
theorem extended_ne_translatedBase :
    extendedPolynomial ≠ translatedBasePolynomial := by
  intro h
  have h0 := congrArg (Polynomial.eval (0 : ℚ)) h
  norm_num [extendedPolynomial, translatedBasePolynomial] at h0

/-- Hence the reduced shift identity in Theorem 1.2 fails for this matrix. -/
theorem shift_formula_fails :
    extendedPolynomial ≠
      translatePolynomial basePolynomial
        (((∑ i, alpha i) + ∑ i, beta i : ℕ) : ℚ) := by
  rw [alpha_sum, beta_sum]
  norm_num
  rw [translate_base_by_one]
  exact extended_ne_translatedBase

/-- Complete formal package for Remark 2.2: both displayed polynomials are
certified by actual all-pair placement counts, while the claimed shift is
false because its constant term is `12` instead of `13`. -/
theorem remark2_2_counterexample :
    ¬matrix.CyclicallyCompatible ∧
    matrix.IsReducedPrimeFiniteFieldPolynomial basePolynomial ∧
    (matrix.extend alpha beta).IsReducedPrimeFiniteFieldPolynomial
      extendedPolynomial ∧
    extendedPolynomial ≠
      translatePolynomial basePolynomial
        (((∑ i, alpha i) + ∑ i, beta i : ℕ) : ℚ) := by
  refine ⟨not_cyclicallyCompatible, base_isReducedPrimeFiniteFieldPolynomial,
    ?_, shift_formula_fails⟩
  simpa [extendedMatrix] using extended_isReducedPrimeFiniteFieldPolynomial

/-! ## Identification with the independently defined Whitney polynomial -/

/-- The first displayed polynomial in Remark 2.2 is literally the reduced
Whitney characteristic polynomial of the base arrangement. -/
theorem whitneyReduced_base_eq_basePolynomial :
    matrix.whitneyReducedCharacteristicPolynomial = basePolynomial := by
  have hfull : matrix.whitneyCharacteristicPolynomial =
      Polynomial.X * basePolynomial :=
    DeformationMatrix.full_eq_X_mul_reduced_of_finiteFieldSpecifications
      matrix matrix.whitney_isFullFiniteFieldPolynomial
        base_isReducedFiniteFieldPolynomial
  unfold DeformationMatrix.whitneyReducedCharacteristicPolynomial
  rw [hfull]
  ext k
  simp [Polynomial.coeff_divX]

/-- The second displayed polynomial in Remark 2.2 is literally the reduced
Whitney characteristic polynomial after the one-sided extension. -/
theorem whitneyReduced_extended_eq_extendedPolynomial :
    extendedMatrix.whitneyReducedCharacteristicPolynomial =
      extendedPolynomial := by
  have hfull : extendedMatrix.whitneyCharacteristicPolynomial =
      Polynomial.X * extendedPolynomial :=
    DeformationMatrix.full_eq_X_mul_reduced_of_finiteFieldSpecifications
      extendedMatrix extendedMatrix.whitney_isFullFiniteFieldPolynomial
        extended_isReducedFiniteFieldPolynomial
  unfold DeformationMatrix.whitneyReducedCharacteristicPolynomial
  rw [hfull]
  ext k
  simp [Polynomial.coeff_divX]

/-- Paper-exact failure statement for the independently defined reduced
characteristic polynomials, rather than auxiliary finite-field candidates. -/
theorem whitneyReduced_shift_formula_fails :
    (matrix.extend alpha beta).whitneyReducedCharacteristicPolynomial ≠
      translatePolynomial matrix.whitneyReducedCharacteristicPolynomial
        (((∑ i, alpha i) + ∑ i, beta i : ℕ) : ℚ) := by
  change extendedMatrix.whitneyReducedCharacteristicPolynomial ≠ _
  rw [whitneyReduced_extended_eq_extendedPolynomial,
    whitneyReduced_base_eq_basePolynomial]
  exact shift_formula_fails

end SharpnessExample

end CyclicBraidArrangement
