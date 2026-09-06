import LeanCo.Rascoe.FormalSeries
import LeanCo.Rascoe.QPochhammer
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery

open Filter Finset PowerSeries
open scoped BigOperators Topology PowerSeries.WithPiTopology

namespace LeanCo.Rascoe

set_option maxHeartbeats 800000

noncomputable def eulerFactorNat (d : ℕ) : ℕ⟦X⟧ :=
  ∑' j : ℕ, X ^ (d * j)

theorem coeff_eulerFactorNat {d : ℕ} (hd : 0 < d) (n : ℕ) :
    coeff n (eulerFactorNat d) = if d ∣ n then 1 else 0 := by
  have hs : Summable (fun j : ℕ ↦ ((X : ℕ⟦X⟧) ^ d) ^ j) :=
    PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero (by simp [hd.ne'])
  have hm := hs.hasSum.map (coeff n) (PowerSeries.WithPiTopology.continuous_coeff ℕ n)
  have hcoeff : coeff n (eulerFactorNat d) =
      ∑' j : ℕ, coeff n ((X : ℕ⟦X⟧) ^ (d * j)) := by
    calc
      coeff n (eulerFactorNat d) =
          coeff n (∑' j : ℕ, ((X : ℕ⟦X⟧) ^ d) ^ j) := by
        apply congrArg (coeff n)
        rw [eulerFactorNat]
        apply tsum_congr
        intro j
        rw [pow_mul]
      _ = ∑' j : ℕ, coeff n (((X : ℕ⟦X⟧) ^ d) ^ j) := hm.tsum_eq.symm
      _ = ∑' j : ℕ, coeff n ((X : ℕ⟦X⟧) ^ (d * j)) := by
        congr 1
        funext j
        rw [pow_mul]
  rw [hcoeff]
  by_cases hdn : d ∣ n
  · obtain ⟨k, rfl⟩ := hdn
    rw [tsum_eq_single k]
    · simp
    · intro b hbk
      simp only [coeff_X_pow]
      split_ifs with h
      · exfalso
        apply hbk
        simpa [hd.ne'] using h.symm
      · rfl
  · have hz : ∀ j : ℕ, coeff n ((X : ℕ⟦X⟧) ^ (d * j)) = 0 := by
      intro j
      simp only [coeff_X_pow]
      split_ifs with h
      · exact False.elim (hdn ⟨j, h⟩)
      · rfl
    simp [hdn, hz]

noncomputable def finiteEulerPS (M : ℕ) : ℕ⟦X⟧ :=
  ∏ i ∈ Finset.range M, eulerFactorNat (i + 1)

theorem evalCoeff_mul (q : ℂ) (f g : ℕ⟦X⟧) (n : ℕ) :
    ((coeff n (f * g) : ℕ) : ℂ) * q ^ n =
      ∑ k ∈ Finset.range (n + 1),
        (((coeff k f : ℕ) : ℂ) * q ^ k) *
          (((coeff (n - k) g : ℕ) : ℂ) * q ^ (n - k)) := by
  rw [PowerSeries.coeff_mul]
  have hanti :
      (∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff p.2 g) =
        ∑ k ∈ Finset.range (n + 1), coeff k f * coeff (n - k) g :=
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l ↦ coeff k f * coeff l g) n
  rw [hanti]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : q ^ n = q ^ k * q ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hpow]
  ring

theorem finiteEulerPS_succ (M : ℕ) :
    finiteEulerPS (M + 1) = finiteEulerPS M * eulerFactorNat (M + 1) := by
  simp [finiteEulerPS, Finset.prod_range_succ]

theorem restrictedSeries_eq_finiteEulerPS (M : ℕ) :
    PowerSeries.mk (fun n ↦
      (Nat.Partition.restricted n (fun i ↦ i ≤ M)).card) = finiteEulerPS M := by
  calc
    PowerSeries.mk (fun n ↦
        (Nat.Partition.restricted n (fun i ↦ i ≤ M)).card) =
        ∏' i : ℕ, if i + 1 ≤ M then
          ∑' j : ℕ, (X : ℕ⟦X⟧) ^ ((i + 1) * j) else 1 := by
      simpa using
        (Nat.Partition.powerSeriesMk_card_restricted_eq_tprod ℕ
          (fun i ↦ i ≤ M))
    _ = finiteEulerPS M := by
      rw [tprod_eq_prod (s := Finset.range M)]
      · apply Finset.prod_congr rfl
        intro i hi
        have hil : i < M := Finset.mem_range.mp hi
        have him : i + 1 ≤ M := by omega
        simp [him, eulerFactorNat, finiteEulerPS]
      · intro i hi
        have him : ¬ i + 1 ≤ M := by
          simp only [Finset.mem_range] at hi
          omega
        simp [him]

theorem coeff_finiteEulerPS (M n : ℕ) :
    coeff n (finiteEulerPS M) =
      (Nat.Partition.restricted n (fun i ↦ i ≤ M)).card := by
  rw [← restrictedSeries_eq_finiteEulerPS]
  simp

theorem coeff_finiteEulerPS_eq_partitionNumber {M n : ℕ} (hn : n ≤ M) :
    coeff n (finiteEulerPS M) = partitionNumber n := by
  rw [coeff_finiteEulerPS, partitionNumber]
  apply congrArg Finset.card
  ext p
  simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro _
    trivial
  · intro _ i hi
    exact (Nat.Partition.le_of_mem_parts hi).trans hn

theorem coeff_finiteEulerPS_le_partitionNumber (M n : ℕ) :
    coeff n (finiteEulerPS M) ≤ partitionNumber n := by
  rw [coeff_finiteEulerPS, partitionNumber]
  exact Finset.card_le_univ _

theorem eulerFactor_hasSum (q : ℂ) (hq : ‖q‖ < 1) {d : ℕ} (hd : 0 < d) :
    HasSum (fun n : ℕ ↦ ((coeff n (eulerFactorNat d) : ℕ) : ℂ) * q ^ n)
      (1 - q ^ d)⁻¹ := by
  let f : ℕ → ℂ := fun n ↦ if d ∣ n then q ^ n else 0
  let g : ℕ → ℕ := fun k ↦ d * k
  have hg : Function.Injective g := by
    intro a b hab
    dsimp [g] at hab
    simpa [hd.ne'] using hab
  have hoff : ∀ n ∉ Set.range g, f n = 0 := by
    intro n hn
    simp only [f]
    split_ifs with hdn
    · exfalso
      apply hn
      obtain ⟨k, hk⟩ := hdn
      exact ⟨k, hk.symm⟩
    · rfl
  have hnorm : ‖q ^ d‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hd.ne'
  have hgeom : HasSum (fun k : ℕ ↦ (q ^ d) ^ k) (1 - q ^ d)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hnorm
  have hcomp : (f ∘ g) = fun k : ℕ ↦ (q ^ d) ^ k := by
    funext k
    simp [f, g, pow_mul]
  have hf : HasSum f (1 - q ^ d)⁻¹ := by
    rw [← hg.hasSum_iff hoff, hcomp]
    exact hgeom
  simpa only [coeff_eulerFactorNat hd, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, ite_mul, one_mul, zero_mul] using hf

theorem finiteEuler_summable_norm (q : ℂ) (hq : ‖q‖ < 1) (M : ℕ) :
    Summable (fun n : ℕ ↦
      ‖((coeff n (finiteEulerPS M) : ℕ) : ℂ) * q ^ n‖) := by
  induction M with
  | zero =>
      have hsingle := (hasSum_ite_eq 0 (1 : ℝ)).summable
      convert hsingle using 1
      funext n
      by_cases hn : n = 0
      · subst n
        simp [finiteEulerPS]
      · simp [finiteEulerPS, hn]
  | succ M ih =>
      have hfac := eulerFactor_hasSum q hq (d := M + 1) (by omega)
      have hnorm_fac : Summable (fun n : ℕ ↦
          ‖((coeff n (eulerFactorNat (M + 1)) : ℕ) : ℂ) * q ^ n‖) := by
        exact summable_norm_iff.mpr hfac.summable
      have hconv := summable_norm_sum_mul_range_of_summable_norm ih hnorm_fac
      rw [finiteEulerPS_succ]
      simpa only [evalCoeff_mul] using hconv

theorem finiteEuler_hasSum (q : ℂ) (hq : ‖q‖ < 1) (M : ℕ) :
    HasSum (fun n : ℕ ↦ ((coeff n (finiteEulerPS M) : ℕ) : ℂ) * q ^ n)
      (∏ i ∈ Finset.range M, (1 - q ^ (i + 1))⁻¹) := by
  induction M with
  | zero =>
      have hsingle := hasSum_ite_eq 0 (1 : ℂ)
      convert hsingle using 1
      · funext n
        by_cases hn : n = 0
        · subst n
          simp [finiteEulerPS]
        · simp [finiteEulerPS, hn]
      · simp
  | succ M ih =>
      have hfac := eulerFactor_hasSum q hq (d := M + 1) (by omega)
      have hnorm_ih : Summable (fun n : ℕ ↦
          ‖((coeff n (finiteEulerPS M) : ℕ) : ℂ) * q ^ n‖) := by
        exact finiteEuler_summable_norm q hq M
      have hnorm_fac : Summable (fun n : ℕ ↦
          ‖((coeff n (eulerFactorNat (M + 1)) : ℕ) : ℂ) * q ^ n‖) := by
        exact summable_norm_iff.mpr hfac.summable
      have hconv := hasSum_sum_range_mul_of_summable_norm hnorm_ih hnorm_fac
      have hconv' : HasSum
          (fun n ↦ ∑ k ∈ Finset.range (n + 1),
            (((coeff k (finiteEulerPS M) : ℕ) : ℂ) * q ^ k) *
              (((coeff (n - k) (eulerFactorNat (M + 1)) : ℕ) : ℂ) * q ^ (n - k)))
          ((∏ i ∈ Finset.range M, (1 - q ^ (i + 1))⁻¹) *
            (1 - q ^ (M + 1))⁻¹) := by
        simpa only [ih.tsum_eq, hfac.tsum_eq] using hconv
      rw [finiteEulerPS_succ, Finset.prod_range_succ]
      convert hconv' using 1
      funext n
      exact evalCoeff_mul q (finiteEulerPS M) (eulerFactorNat (M + 1)) n

theorem finiteEulerProduct_eq_inv_finiteQPochhammer (q : ℂ) (M : ℕ) :
    (∏ i ∈ Finset.range M, (1 - q ^ (i + 1))⁻¹) =
      (finiteQPochhammer q q M)⁻¹ := by
  rw [finiteQPochhammer, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  rw [pow_succ]
  ring

theorem tendsto_finiteEulerProduct (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun M ↦ ∏ i ∈ Finset.range M, (1 - q ^ (i + 1))⁻¹)
      atTop (𝓝 (analyticQPochhammer q q)⁻¹) := by
  simp_rw [finiteEulerProduct_eq_inv_finiteQPochhammer]
  have hne : analyticQPochhammer q q ≠ 0 := by
    simpa using
      (analyticQPochhammer_qPow_ne_zero q hq
        (s := 1) (by norm_num))
  exact (tendsto_finiteQPochhammer q q hq).inv₀ hne

theorem finiteEulerProduct_bounded (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ C : ℝ, ∀ M : ℕ,
      ‖∏ i ∈ Finset.range M, (1 - q ^ (i + 1))⁻¹‖ ≤ C := by
  have hb := Metric.isBounded_range_of_tendsto
    (fun M ↦ ∏ i ∈ Finset.range M, (1 - q ^ (i + 1))⁻¹)
    (tendsto_finiteEulerProduct q hq)
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  exact ⟨C, fun M ↦ hC _ ⟨M, rfl⟩⟩

theorem finiteEuler_hasSum_real (r : ℝ) (hr₀ : 0 ≤ r) (hr : r < 1) (M : ℕ) :
    HasSum (fun n : ℕ ↦ ((coeff n (finiteEulerPS M) : ℕ) : ℝ) * r ^ n)
      (∏ i ∈ Finset.range M, (1 - r ^ (i + 1))⁻¹) := by
  have hnorm : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_nonneg hr₀] using hr
  have hc := finiteEuler_hasSum (r : ℂ) hnorm M
  apply Complex.hasSum_ofReal.mp
  simpa using hc

theorem partition_summable_real (r : ℝ) (hr₀ : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ ↦ (partitionNumber n : ℝ) * r ^ n) := by
  have hnorm : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, abs_of_nonneg hr₀] using hr
  obtain ⟨C, hC⟩ := finiteEulerProduct_bounded (r : ℂ) hnorm
  apply summable_of_sum_le
  · intro n
    positivity
  · intro u
    let M : ℕ := (∑ n ∈ u, n) + 1
    have hnM : ∀ n ∈ u, n ≤ M := by
      intro n hn
      have hnsum : n ≤ ∑ k ∈ u, k := by
        exact Finset.single_le_sum (fun k _ ↦ Nat.zero_le k) hn
      dsimp [M]
      omega
    have hreal := finiteEuler_hasSum_real r hr₀ hr M
    calc
      ∑ n ∈ u, (partitionNumber n : ℝ) * r ^ n =
          ∑ n ∈ u, ((coeff n (finiteEulerPS M) : ℕ) : ℝ) * r ^ n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [coeff_finiteEulerPS_eq_partitionNumber (hnM n hn)]
      _ ≤ ∑' n : ℕ, ((coeff n (finiteEulerPS M) : ℕ) : ℝ) * r ^ n := by
        exact hreal.summable.sum_le_tsum u (fun n _ ↦ by positivity)
      _ = ∏ i ∈ Finset.range M, (1 - r ^ (i + 1))⁻¹ := hreal.tsum_eq
      _ ≤ C := by
        have hpow (i : ℕ) : r ^ (i + 1) ≤ 1 := by
          exact pow_le_one₀ hr₀ hr.le
        have hprod : 0 ≤ ∏ i ∈ Finset.range M, (1 - r ^ (i + 1))⁻¹ := by
          apply Finset.prod_nonneg
          intro i hi
          exact inv_nonneg.mpr (sub_nonneg.mpr (hpow i))
        have hfactor (i : ℕ) :
            ‖(1 - (r : ℂ) ^ (i + 1))⁻¹‖ = (1 - r ^ (i + 1))⁻¹ := by
          rw [norm_inv]
          simp only [← Complex.ofReal_pow, ← Complex.ofReal_one,
            ← Complex.ofReal_sub, Complex.norm_real]
          rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hpow i))]
        have hb := hC M
        simpa only [norm_prod, hfactor] using hb

theorem partition_summable_complex (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (partitionNumber n : ℂ) * q ^ n) := by
  apply summable_norm_iff.mp
  have hr := partition_summable_real ‖q‖ (norm_nonneg q) hq
  simpa only [norm_mul, Complex.norm_natCast, norm_pow] using hr

theorem partition_tsum_eq_inv_analyticQPochhammer (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (partitionNumber n : ℂ) * q ^ n) =
      (analyticQPochhammer q q)⁻¹ := by
  let f : ℕ → ℕ → ℂ := fun M n ↦
    ((coeff n (finiteEulerPS M) : ℕ) : ℂ) * q ^ n
  let g : ℕ → ℂ := fun n ↦ (partitionNumber n : ℂ) * q ^ n
  let bound : ℕ → ℝ := fun n ↦
    (partitionNumber n : ℝ) * ‖q‖ ^ n
  have hbound : Summable bound :=
    partition_summable_real ‖q‖ (norm_nonneg q) hq
  have hpoint (n : ℕ) : Tendsto (fun M ↦ f M n) atTop (𝓝 (g n)) := by
    apply tendsto_atTop_of_eventually_const (i₀ := n)
    intro M hMn
    dsimp [f, g]
    rw [coeff_finiteEulerPS_eq_partitionNumber hMn]
  have hdom : ∀ᶠ M in atTop, ∀ n, ‖f M n‖ ≤ bound n := by
    filter_upwards [] with M
    intro n
    simp only [f, g, bound, norm_mul, Complex.norm_natCast, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast coeff_finiteEulerPS_le_partitionNumber M n)
      (pow_nonneg (norm_nonneg q) n)
  have ht := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hvalues : (fun M ↦ ∑' n, f M n) =
      fun M ↦ ∏ i ∈ Finset.range M, (1 - q ^ (i + 1))⁻¹ := by
    funext M
    exact (finiteEuler_hasSum q hq M).tsum_eq
  rw [hvalues] at ht
  have hprod := tendsto_finiteEulerProduct q hq
  have heq := tendsto_nhds_unique ht hprod
  simpa [g] using heq

theorem partition_hasSum_inv_analyticQPochhammer (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (partitionNumber n : ℂ) * q ^ n)
      (analyticQPochhammer q q)⁻¹ := by
  have hs := partition_summable_complex q hq
  rw [← partition_tsum_eq_inv_analyticQPochhammer q hq]
  exact hs.hasSum

theorem partitionNumber_norm_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖(partitionNumber n : ℂ) * q ^ n‖) := by
  have hr := partition_summable_real ‖q‖ (norm_nonneg q) hq
  simpa only [norm_mul, Complex.norm_natCast, norm_pow] using hr

theorem analyticQPochhammer_q_shift (q : ℂ) (hq : ‖q‖ < 1) :
    analyticQPochhammer q q =
      (1 - q) * analyticQPochhammer (q ^ 2) q := by
  have heq : (fun k : ℕ ↦ 1 - q * q ^ (k + 1)) =
      (fun k : ℕ ↦ 1 - q ^ 2 * q ^ k) := by
    funext k
    rw [pow_succ]
    ring
  have htail : HasProd (fun k : ℕ ↦ 1 - q * q ^ (k + 1))
      (analyticQPochhammer (q ^ 2) q) := by
    rw [heq]
    exact analyticQPochhammer_hasProd (q ^ 2) q hq
  have hall := htail.zero_mul (f := fun k : ℕ ↦ 1 - q * q ^ k)
  have horig := analyticQPochhammer_hasProd q q hq
  exact horig.unique (by simpa using hall)

theorem noOneNumber_le_partitionNumber (n : ℕ) :
    noOneNumber n ≤ partitionNumber n := by
  simpa only [noOneNumber, partitionNumber] using
    (Fintype.card_subtype_le (fun p : Nat.Partition n ↦ HasNoOne p))

theorem rascoeNumber_le_partitionNumber (n : ℕ) :
    rascoeNumber n ≤ partitionNumber n := by
  simpa only [rascoeNumber, partitionNumber] using
    (Fintype.card_subtype_le (fun p : Nat.Partition n ↦ IsRascoe p))

theorem nonRascoeNumber_le_partitionNumber (n : ℕ) :
    nonRascoeNumber n ≤ partitionNumber n := by
  simpa only [nonRascoeNumber, partitionNumber] using
    (Fintype.card_subtype_le (fun p : Nat.Partition n ↦ IsNonRascoe p))

theorem noOneNumber_norm_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖(noOneNumber n : ℂ) * q ^ n‖) := by
  apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) ?_
    (partitionNumber_norm_summable q hq)
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast noOneNumber_le_partitionNumber n)
    (pow_nonneg (norm_nonneg q) n)

theorem noOneNumber_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (noOneNumber n : ℂ) * q ^ n) :=
  (noOneNumber_norm_summable q hq).of_norm

private theorem noOneNumber_hasSum_mul (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (noOneNumber n : ℂ) * q ^ n)
      ((1 - q) * (analyticQPochhammer q q)⁻¹) := by
  let shifted : ℕ → ℂ := fun n ↦
    if n = 0 then 0 else (partitionNumber (n - 1) : ℂ) * q ^ n
  have hp := partition_hasSum_inv_analyticQPochhammer q hq
  have hshifted : HasSum shifted
      (q * (analyticQPochhammer q q)⁻¹) := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa [shifted, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      hp.mul_left q
  have hpoint : (fun n : ℕ ↦ (noOneNumber n : ℂ) * q ^ n) =
      fun n ↦ (partitionNumber n : ℂ) * q ^ n - shifted n := by
    funext n
    cases n with
    | zero => simp [shifted]
    | succ n =>
        simp only [shifted, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
          partitionNumber_succ_eq_noOneNumber_add]
        push_cast
        ring
  rw [hpoint]
  simpa [sub_mul] using hp.sub hshifted

theorem noOneNumber_hasSum (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (noOneNumber n : ℂ) * q ^ n)
      (analyticQPochhammer (q ^ 2) q)⁻¹ := by
  have hq1 : 1 - q ≠ 0 := by
    simpa using one_sub_qPow_ne_zero q hq (n := 1) (by omega)
  have hshift := analyticQPochhammer_q_shift q hq
  convert noOneNumber_hasSum_mul q hq using 1
  rw [hshift]
  field_simp

theorem noOneNumber_tsum (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (noOneNumber n : ℂ) * q ^ n) =
      (analyticQPochhammer (q ^ 2) q)⁻¹ :=
  (noOneNumber_hasSum q hq).tsum_eq

private theorem rascoeNumber_hasSum_mul (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (rascoeNumber n : ℂ) * q ^ n)
      (q * ((1 - q) * (analyticQPochhammer q q)⁻¹)) := by
  have hn := noOneNumber_hasSum_mul q hq
  apply (hasSum_nat_add_iff' 1).mp
  simpa [rascoeNumber_succ_eq_noOneNumber, pow_succ,
    mul_assoc, mul_left_comm, mul_comm] using hn.mul_left q

theorem rascoeNumber_hasSum (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (rascoeNumber n : ℂ) * q ^ n)
      (q * (analyticQPochhammer (q ^ 2) q)⁻¹) := by
  have hq1 : 1 - q ≠ 0 := by
    simpa using one_sub_qPow_ne_zero q hq (n := 1) (by omega)
  have hshift := analyticQPochhammer_q_shift q hq
  convert rascoeNumber_hasSum_mul q hq using 1
  rw [hshift]
  field_simp

theorem rascoeNumber_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (rascoeNumber n : ℂ) * q ^ n) :=
  (rascoeNumber_hasSum q hq).summable

theorem rascoeNumber_norm_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖(rascoeNumber n : ℂ) * q ^ n‖) :=
  (rascoeNumber_summable q hq).norm

theorem rascoeNumber_tsum (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (rascoeNumber n : ℂ) * q ^ n) =
      q * (analyticQPochhammer (q ^ 2) q)⁻¹ :=
  (rascoeNumber_hasSum q hq).tsum_eq

theorem nonRascoeNumber_hasSum (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (nonRascoeNumber n : ℂ) * q ^ n)
      ((1 - q + q ^ 2) * (analyticQPochhammer q q)⁻¹) := by
  have hp := partition_hasSum_inv_analyticQPochhammer q hq
  have hc := rascoeNumber_hasSum_mul q hq
  have hpoint : (fun n : ℕ ↦ (nonRascoeNumber n : ℂ) * q ^ n) =
      fun n ↦ (partitionNumber n : ℂ) * q ^ n -
        (rascoeNumber n : ℂ) * q ^ n := by
    funext n
    have h := rascoeNumber_add_nonRascoeNumber n
    rw [← h]
    push_cast
    ring
  rw [hpoint]
  have hsum := hp.sub hc
  have hvalue :
      (analyticQPochhammer q q)⁻¹ -
          q * ((1 - q) * (analyticQPochhammer q q)⁻¹) =
        (1 - q + q ^ 2) * (analyticQPochhammer q q)⁻¹ := by
    ring
  rw [← hvalue]
  exact hsum

theorem nonRascoeNumber_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (nonRascoeNumber n : ℂ) * q ^ n) :=
  (nonRascoeNumber_hasSum q hq).summable

theorem nonRascoeNumber_norm_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖(nonRascoeNumber n : ℂ) * q ^ n‖) :=
  (nonRascoeNumber_summable q hq).norm

theorem nonRascoeNumber_tsum (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (nonRascoeNumber n : ℂ) * q ^ n) =
      (1 - q + q ^ 2) * (analyticQPochhammer q q)⁻¹ :=
  (nonRascoeNumber_hasSum q hq).tsum_eq

end LeanCo.Rascoe
