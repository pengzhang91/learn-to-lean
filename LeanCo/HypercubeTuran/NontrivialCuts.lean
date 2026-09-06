import LeanCo.HypercubeTuran.RandomBaseExistence
import LeanCo.HypercubeTuran.Alteration

/-!
# Removing the two trivial cuts from the random cut union bound

The generic cardinality-compressed Chernoff estimate includes the sizes zero
and `N`.  Their bad events are empty, but their raw exponential envelopes are
one.  This file records the sharpened union bound over genuinely nontrivial
cut sizes, which is the form needed by the numerical parameter argument.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Finset ProbabilityTheory unitInterval

namespace LeanCo.HypercubeTuran

noncomputable section

namespace RB

/-- The possible cardinalities of a nonempty proper shore of a cut. -/
def nontrivialCutSizes (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun u => 0 < u ∧ u < N

@[simp]
theorem mem_nontrivialCutSizes {N u : ℕ} :
    u ∈ nontrivialCutSizes N ↔ 0 < u ∧ u < N := by
  simp only [nontrivialCutSizes, Finset.mem_filter, Finset.mem_range]
  omega

/-- A bad cut can only have a nonempty proper shore. -/
theorem badCutEvent_eq_iUnion_nontrivial_size (N d : ℕ) :
    badCutEvent N d =
      {E | ∃ u ∈ nontrivialCutSizes N,
        E ∈ badCutEventAtSize N d u} := by
  rw [badCutEvent_eq_iUnion_size]
  ext E
  constructor
  · rintro ⟨u, hu, S, hS, hbad⟩
    have huN : u ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
    have hu0 : 0 < u := by
      by_contra h
      have : u = 0 := Nat.eq_zero_of_not_pos h
      subst u
      simp only [Nat.zero_mul, Nat.mul_zero] at hbad
      omega
    have hult : u < N := by
      by_contra h
      have : u = N := Nat.le_antisymm huN (Nat.le_of_not_gt h)
      subst u
      simp only [Nat.sub_self, Nat.mul_zero] at hbad
      omega
    exact ⟨u, mem_nontrivialCutSizes.mpr ⟨hu0, hult⟩, S, hS, hbad⟩
  · rintro ⟨u, hu, hbad⟩
    exact ⟨u, Finset.mem_range.mpr (Nat.lt_succ_of_lt
      (mem_nontrivialCutSizes.mp hu).2), hbad⟩

/-- Cardinality-compressed Chernoff bound with the two empty endpoint events
removed. -/
theorem measureReal_badCutEvent_le_chernoff_nontrivial_size_sum
    {N : ℕ} (hN : 0 < N) (d : ℕ) (p : unitInterval)
    {t : ℝ} (ht : t < 0) :
    (randomEdgeMeasure N p).real (badCutEvent N d) ≤
      ∑ u ∈ nontrivialCutSizes N,
        (N.choose u : ℝ) *
          (Real.exp (-t *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
              (u * (N - u))) := by
  rw [badCutEvent_eq_iUnion_nontrivial_size]
  calc
    (randomEdgeMeasure N p).real
        {E | ∃ u ∈ nontrivialCutSizes N,
          E ∈ badCutEventAtSize N d u} ≤
        ∑ u ∈ nontrivialCutSizes N,
          (randomEdgeMeasure N p).real (badCutEventAtSize N d u) :=
      measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ u ∈ nontrivialCutSizes N,
        (N.choose u : ℝ) *
          (Real.exp (-t *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
              (u * (N - u))) := by
      apply Finset.sum_le_sum
      intro u _
      exact measureReal_badCutEventAtSize_le_chernoff hN d u p ht

/-! ## Compression to the smaller shore -/

/-- The random cut count is unchanged on replacing a shore by its complement. -/
@[simp]
theorem randomGraphCutSize_compl {N : ℕ} (E : Set (RandomEdge N))
    (S : Finset (Fin N)) :
    randomGraphCutSize E Sᶜ = randomGraphCutSize E S := by
  classical
  rw [randomGraphCutSize_eq_cutSize, randomGraphCutSize_eq_cutSize,
    cutSize_compl]

/-- Sizes of nonempty shores which are no larger than their complement. -/
def smallShoreSizes (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun u => 0 < u ∧ 2 * u ≤ N

@[simp]
theorem mem_smallShoreSizes {N u : ℕ} :
    u ∈ smallShoreSizes N ↔ 0 < u ∧ 2 * u ≤ N := by
  simp only [smallShoreSizes, Finset.mem_filter, Finset.mem_range]
  omega

/-- Every bad cut has a nonempty shore of size at most half the vertices. -/
theorem badCutEvent_eq_iUnion_smallShore_size (N d : ℕ) :
    badCutEvent N d =
      {E | ∃ u ∈ smallShoreSizes N,
        E ∈ badCutEventAtSize N d u} := by
  ext E
  constructor
  · rintro ⟨S, hbad⟩
    have hSN : #S ≤ N := by
      simpa using Finset.card_le_univ S
    have hS0 : 0 < #S := by
      by_contra h
      have hz : #S = 0 := Nat.eq_zero_of_not_pos h
      simp only [hz, Nat.zero_mul, Nat.mul_zero] at hbad
      omega
    have hSlt : #S < N := by
      by_contra h
      have heq : #S = N := Nat.le_antisymm hSN (Nat.le_of_not_gt h)
      simp only [heq, Nat.sub_self, Nat.mul_zero] at hbad
      omega
    by_cases hsmall : 2 * #S ≤ N
    · refine ⟨#S, mem_smallShoreSizes.mpr ⟨hS0, hsmall⟩, S, ?_, hbad⟩
      exact mem_vertexSetsOfCard.mpr rfl
    · let T : Finset (Fin N) := Sᶜ
      have hcardT : #T = N - #S := by
        have hc := S.card_compl_add_card
        simp only [Fintype.card_fin] at hc
        dsimp only [T]
        omega
      have hT0 : 0 < #T := by
        rw [hcardT]
        omega
      have hTsmall : 2 * #T ≤ N := by
        rw [hcardT]
        omega
      refine ⟨#T, mem_smallShoreSizes.mpr ⟨hT0, hTsmall⟩, T,
        mem_vertexSetsOfCard.mpr rfl, ?_⟩
      have hsub : N - (N - #S) = #S := Nat.sub_sub_self hSN
      simpa only [T, randomGraphCutSize_compl, hcardT, hsub,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbad
  · rintro ⟨u, _hu, S, hS, hbad⟩
    have hcard : #S = u := mem_vertexSetsOfCard.mp hS
    exact ⟨S, by simpa only [hcard] using hbad⟩

/-- The useful cut union bound: only smaller nonempty shores occur. -/
theorem measureReal_badCutEvent_le_chernoff_smallShore_size_sum
    {N : ℕ} (hN : 0 < N) (d : ℕ) (p : unitInterval)
    {t : ℝ} (ht : t < 0) :
    (randomEdgeMeasure N p).real (badCutEvent N d) ≤
      ∑ u ∈ smallShoreSizes N,
        (N.choose u : ℝ) *
          (Real.exp (-t *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
              (u * (N - u))) := by
  rw [badCutEvent_eq_iUnion_smallShore_size]
  calc
    (randomEdgeMeasure N p).real
        {E | ∃ u ∈ smallShoreSizes N,
          E ∈ badCutEventAtSize N d u} ≤
        ∑ u ∈ smallShoreSizes N,
          (randomEdgeMeasure N p).real (badCutEventAtSize N d u) :=
      measureReal_exists_mem_finset_le _ _ _
    _ ≤ ∑ u ∈ smallShoreSizes N,
        (N.choose u : ℝ) *
          (Real.exp (-t *
              (((8 * d * u * (N - u) : ℕ) : ℝ) /
                ((5 * N : ℕ) : ℝ))) *
            (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^
              (u * (N - u))) := by
      apply Finset.sum_le_sum
      intro u _
      exact measureReal_badCutEventAtSize_le_chernoff hN d u p ht

end RB

end

end LeanCo.HypercubeTuran
