import Mathlib

/-!
# Generic probability helpers for the hypercube Turán argument

This module deliberately depends only on Mathlib.  It collects the small
finite-union, binomial-Chernoff, and set-Bernoulli lemmas used by the random
source construction, so that the latter does not depend on any unrelated
formalization in `LeanCo`.
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped ENNReal Finset ProbabilityTheory

namespace LeanCo.HypercubeTuran.RB

noncomputable section

/-- The selected elements of a fixed finite set. -/
noncomputable def selectedFinset {ι : Type*} (A : Finset ι) (E : Set ι) :
    Finset ι := by
  classical
  exact A.filter fun e => e ∈ E

@[simp]
theorem mem_selectedFinset {ι : Type*} {A : Finset ι} {E : Set ι} {e : ι} :
    e ∈ selectedFinset A E ↔ e ∈ A ∧ e ∈ E := by
  classical
  simp [selectedFinset]

/-- A finite union bound for real-valued measures. -/
theorem measureReal_exists_mem_finset_le {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (indices : Finset ι) (A : ι → Set Ω) :
    P.real {ω | ∃ i ∈ indices, ω ∈ A i} ≤
      ∑ i ∈ indices, P.real (A i) := by
  have heq : {ω | ∃ i ∈ indices, ω ∈ A i} = ⋃ i ∈ indices, A i := by
    ext ω
    simp
  rw [heq]
  exact measureReal_biUnion_finset_le indices A

/-- Exact moment-generating function of a binomial random variable. -/
private theorem integral_exp_nat_binomial (trials : ℕ) (p : I) (t : ℝ) :
    ∫ x : ℕ, Real.exp (t * x) ∂Bin(trials, p) =
      (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
  rw [integral_binomial]
  rw [← Nat.range_succ_eq_Iic]
  rw [show (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials =
    ((p : ℝ) * Real.exp t + (1 - (p : ℝ))) ^ trials by ring]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k _
  have hexp : Real.exp (t * (k : ℝ)) = Real.exp t ^ k := by
    rw [mul_comm, Real.exp_nat_mul]
  rw [hexp]
  ring

/-- Chernoff's exponential-transform upper-tail bound for a binomial law. -/
theorem binomial_chernoff_upper (trials : ℕ) (p : I)
    {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Bin(trials, p).real {x : ℕ | a ≤ x} ≤
      Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
  let f : ℕ → ℝ := fun x => Real.exp (t * x)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := Bin(trials, p)) (f := f)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (integrable_binomial f) (Real.exp (t * a))
  have hevent :
      {x : ℕ | Real.exp (t * a) ≤ f x} = {x : ℕ | a ≤ x} := by
    ext x
    simp only [Set.mem_setOf_eq, f, Real.exp_le_exp]
    exact mul_le_mul_iff_right₀ ht
  rw [hevent, integral_exp_nat_binomial] at hmarkov
  calc
    Bin(trials, p).real {x : ℕ | a ≤ x} ≤
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials /
          Real.exp (t * a) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      simpa [mul_comm] using hmarkov
    _ = Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
      rw [show -t * a = -(t * a) by ring, Real.exp_neg]
      ring

/-- Chernoff's exponential-transform lower-tail bound for a binomial law. -/
theorem binomial_chernoff_lower (trials : ℕ) (p : I)
    {t : ℝ} (ht : t < 0) (a : ℝ) :
    Bin(trials, p).real {x : ℕ | (x : ℝ) ≤ a} ≤
      Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
  let f : ℕ → ℝ := fun x => Real.exp (t * x)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := Bin(trials, p)) (f := f)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (integrable_binomial f) (Real.exp (t * a))
  have hevent :
      {x : ℕ | Real.exp (t * a) ≤ f x} = {x : ℕ | (x : ℝ) ≤ a} := by
    ext x
    simp only [Set.mem_setOf_eq, f, Real.exp_le_exp]
    constructor <;> intro h <;> nlinarith
  rw [hevent, integral_exp_nat_binomial] at hmarkov
  calc
    Bin(trials, p).real {x : ℕ | (x : ℝ) ≤ a} ≤
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials /
          Real.exp (t * a) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      simpa [mul_comm] using hmarkov
    _ = Real.exp (-t * a) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp t) ^ trials := by
      rw [show -t * a = -(t * a) by ring, Real.exp_neg]
      ring

/-- A small rational upper bound for `exp (-2)`. -/
theorem exp_neg_two_lt_one_six : Real.exp (-2) < (1 : ℝ) / 6 := by
  have hexpTwo : (6 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    nlinarith [Real.exp_one_gt_d9]
  rw [Real.exp_neg]
  simpa only [one_div] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 6) hexpTwo)

/-- Under a set-Bernoulli law, every member of a fixed finite set is present
with probability exactly `p ^ |A|`. -/
private theorem setBernoulli_superset_apply {ι : Type*} [Countable ι]
    (u : Set ι) (p : I) (A : Finset ι) (hA : (A : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | (A : Set ι) ⊆ s} =
      (toNNReal p : ℝ≥0∞) ^ #A := by
  rw [setBernoulli_apply']
  let S : Set ((i : A) → Prop) := {q | ∀ i, q i}
  have hevent :
      (fun q : ι → Prop => {i | q i}) ⁻¹'
          {s : Set ι | (A : Set ι) ⊆ s} = cylinder A S := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_cylinder, S]
    constructor
    · intro h i
      exact h i.property
    · intro h i hi
      exact h ⟨i, hi⟩
  rw [hevent, Measure.infinitePi_cylinder _ (by measurability : MeasurableSet S)]
  have hS : S = {fun _ => True} := by
    ext q
    simp [S, funext_iff]
  rw [hS, Measure.pi_singleton]
  have hfactor (i : A) :
      (toNNReal p • Measure.dirac ((i : ι) ∈ u) +
        toNNReal (σ p) • Measure.dirac False) {True} =
          (toNNReal p : ℝ≥0∞) := by
    simp [hA i.property]
  simp_rw [hfactor]
  simp

/-- Union-bound tail estimate for the number selected from a fixed finite
candidate set. -/
private theorem setBernoulli_fixedSet_tail {ι : Type*} [Countable ι]
    (u : Set ι) (p : I) (A : Finset ι) (hA : (A : Set ι) ⊆ u) (m : ℕ) :
    setBer(u, p) {E : Set ι | m ≤ #(selectedFinset A E)} ≤
      (A.card.choose m : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) ^ m := by
  classical
  let event : Finset ι → Set (Set ι) := fun B => {E | (B : Set ι) ⊆ E}
  have hsubset : {E : Set ι | m ≤ #(selectedFinset A E)} ⊆
      ⋃ B ∈ A.powersetCard m, event B := by
    intro E hE
    obtain ⟨B, hB, hBcard⟩ := Finset.exists_subset_card_eq hE
    have hBA : B ⊆ A := fun e he => (mem_selectedFinset.mp (hB he)).1
    have hBE : (B : Set ι) ⊆ E := by
      intro e he
      exact (mem_selectedFinset.mp (hB he)).2
    simp only [Set.mem_iUnion, event, Set.mem_setOf_eq]
    exact ⟨B, ⟨by simpa [Finset.mem_powersetCard] using And.intro hBA hBcard, hBE⟩⟩
  calc
    setBer(u, p) {E : Set ι | m ≤ #(selectedFinset A E)} ≤
        setBer(u, p) (⋃ B ∈ A.powersetCard m, event B) := measure_mono hsubset
    _ ≤ ∑ B ∈ A.powersetCard m, setBer(u, p) (event B) :=
      measure_biUnion_finset_le _ _
    _ = (A.card.choose m : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) ^ m := by
      have hterm (B : Finset ι) (hB : B ∈ A.powersetCard m) :
          setBer(u, p) (event B) = (toNNReal p : ℝ≥0∞) ^ m := by
        rw [setBernoulli_superset_apply]
        · congr 1
          exact (Finset.mem_powersetCard.mp hB).2
        · intro e he
          exact hA ((Finset.mem_powersetCard.mp hB).1 he)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
        Finset.card_powersetCard]

/-- Real-valued fixed-set selection tail estimate. -/
theorem setBernoulli_fixedSet_tail_real {ι : Type*} [Countable ι]
    (u : Set ι) (p : I) (A : Finset ι) (hA : (A : Set ι) ⊆ u) (m : ℕ) :
    setBer(u, p).real {E : Set ι | m ≤ #(selectedFinset A E)} ≤
      (A.card.choose m : ℝ) * (p : ℝ) ^ m := by
  rw [measureReal_def]
  calc
    (setBer(u, p) {E : Set ι | m ≤ #(selectedFinset A E)}).toReal ≤
        ((A.card.choose m : ℝ≥0∞) * (toNNReal p : ℝ≥0∞) ^ m).toReal := by
      rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)]
      exact setBernoulli_fixedSet_tail u p A hA m
    _ = (A.card.choose m : ℝ) * (p : ℝ) ^ m := by
      simp [unitInterval.coe_toNNReal]

end

end LeanCo.HypercubeTuran.RB
