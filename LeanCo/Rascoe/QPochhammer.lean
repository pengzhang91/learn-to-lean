import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Finite, analytic, and formal q-Pochhammer symbols

This file supplies the elementary q-Pochhammer API needed for the Rascoe
partition identities.  The three realizations are deliberately kept separate:

* `finiteQPochhammer a q n` is the finite product `(a;q)ₙ` in a commutative ring;
* `analyticQPochhammer a q` is the complex infinite product `(a;q)∞`;
* `powerSeriesQPochhammer R s m` is `(Xˢ;X)ₘ` in `R⟦X⟧`.
-/

open Filter Finset PowerSeries
open scoped BigOperators Topology

namespace LeanCo.Rascoe

/-! ## Finite q-Pochhammer products -/

/-- The finite q-Pochhammer symbol `(a;q)ₙ = ∏_{k<n} (1-aqᵏ)`. -/
def finiteQPochhammer {R : Type*} [CommRing R] (a q : R) (n : ℕ) : R :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

@[simp] theorem finiteQPochhammer_zero {R : Type*} [CommRing R] (a q : R) :
    finiteQPochhammer a q 0 = 1 := by
  simp [finiteQPochhammer]

theorem finiteQPochhammer_succ {R : Type*} [CommRing R]
    (a q : R) (n : ℕ) :
    finiteQPochhammer a q (n + 1) =
      finiteQPochhammer a q n * (1 - a * q ^ n) := by
  simp [finiteQPochhammer, Finset.prod_range_succ]

/-- Split a finite q-Pochhammer product after its first `m` factors. -/
theorem finiteQPochhammer_add {R : Type*} [CommRing R]
    (a q : R) (m n : ℕ) :
    finiteQPochhammer a q (m + n) =
      finiteQPochhammer a q m * finiteQPochhammer (a * q ^ m) q n := by
  simp only [finiteQPochhammer, Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [pow_add]
  ring

/-- Moving the initial parameter by `qˢ` shifts every exponent by `s`. -/
theorem finiteQPochhammer_shift {R : Type*} [CommRing R]
    (a q : R) (s n : ℕ) :
    finiteQPochhammer (a * q ^ s) q n =
      ∏ k ∈ Finset.range n, (1 - a * q ^ (s + k)) := by
  apply Finset.prod_congr rfl
  intro k hk
  simp only [pow_add]
  ring

/-- The shifted product can equivalently be indexed by the interval `[s,s+n)`. -/
theorem finiteQPochhammer_shift_eq_prod_Ico {R : Type*} [CommRing R]
    (a q : R) (s n : ℕ) :
    finiteQPochhammer (a * q ^ s) q n =
      ∏ k ∈ Finset.Ico s (s + n), (1 - a * q ^ k) := by
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel_left]
  exact finiteQPochhammer_shift a q s n

/-! ## Analytic q-Pochhammer products -/

/-- The analytic complex q-Pochhammer product `(a;q)∞`. -/
noncomputable def analyticQPochhammer (a q : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - a * q ^ k)

/-- Absolute summability of the perturbations gives convergence of `(a;q)∞`
inside the open unit disc. -/
theorem analyticQPochhammer_multipliable (a q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable (fun k : ℕ ↦ 1 - a * q ^ k) := by
  have hs : Summable (fun k : ℕ ↦ ‖-(a * q ^ k)‖) := by
    simpa [norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

theorem analyticQPochhammer_hasProd (a q : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun k : ℕ ↦ 1 - a * q ^ k) (analyticQPochhammer a q) :=
  (analyticQPochhammer_multipliable a q hq).hasProd

/-- Finite q-Pochhammer products converge to the analytic one. -/
theorem tendsto_finiteQPochhammer (a q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun n ↦ finiteQPochhammer a q n) atTop
      (𝓝 (analyticQPochhammer a q)) := by
  exact (analyticQPochhammer_multipliable a q hq).tendsto_prod_tprod_nat

/-- A positive power of a point in the open unit disc is not one. -/
theorem one_sub_qPow_ne_zero (q : ℂ) (hq : ‖q‖ < 1)
    {n : ℕ} (hn : 0 < n) :
    1 - q ^ n ≠ 0 := by
  intro h
  have hpow : q ^ n = 1 := (sub_eq_zero.mp h).symm
  have heq : ‖q‖ ^ n = 1 := by
    rw [← norm_pow, hpow, norm_one]
  have hlt : ‖q‖ ^ n < 1 :=
    pow_lt_one₀ (norm_nonneg q) hq hn.ne'
  exact (ne_of_lt hlt) heq

/-- Every factor of `(qˢ;q)∞` is nonzero when `s > 0` and `‖q‖ < 1`. -/
theorem analyticQPochhammer_qPow_factor_ne_zero
    (q : ℂ) (hq : ‖q‖ < 1) {s : ℕ} (hs : 0 < s) (k : ℕ) :
    1 - q ^ s * q ^ k ≠ 0 := by
  rw [← pow_add]
  exact one_sub_qPow_ne_zero q hq (Nat.add_pos_left hs k)

/-- The shifted infinite q-Pochhammer product `(qˢ;q)∞` is nonzero for `s>0`. -/
theorem analyticQPochhammer_qPow_ne_zero
    (q : ℂ) (hq : ‖q‖ < 1) {s : ℕ} (hs : 0 < s) :
    analyticQPochhammer (q ^ s) q ≠ 0 := by
  have hsum : Summable (fun k : ℕ ↦ ‖-(q ^ (s + k))‖) := by
    simpa [norm_pow, pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left (‖q‖ ^ s)
  have hprod : ∏' k : ℕ, (1 + -(q ^ (s + k))) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable
      (fun k ↦ by
        simpa [sub_eq_add_neg] using
          one_sub_qPow_ne_zero q hq (Nat.add_pos_left hs k))
      hsum
  simpa [analyticQPochhammer, sub_eq_add_neg, pow_add] using hprod

/-- At the boundary point `q=0`, the shifted product is visibly `1` for `s>0`. -/
@[simp] theorem analyticQPochhammer_zero_qPow {s : ℕ} (hs : 0 < s) :
    analyticQPochhammer ((0 : ℂ) ^ s) 0 = 1 := by
  simp [analyticQPochhammer, zero_pow hs.ne']

/-! ## Formal power series q-Pochhammer products -/

/-- The formal finite product `(Xˢ;X)ₘ` in `R⟦X⟧`. -/
noncomputable def powerSeriesQPochhammer (R : Type*) [CommRing R] (s m : ℕ) : R⟦X⟧ :=
  finiteQPochhammer (X ^ s) X m

theorem powerSeriesQPochhammer_eq_prod (R : Type*) [CommRing R]
    (s m : ℕ) :
    powerSeriesQPochhammer R s m =
      ∏ k ∈ Finset.range m, (1 - (X : R⟦X⟧) ^ (s + k)) := by
  simpa [powerSeriesQPochhammer] using
    finiteQPochhammer_shift (1 : R⟦X⟧) X s m

@[simp] theorem powerSeriesQPochhammer_zero (R : Type*) [CommRing R] (s : ℕ) :
    powerSeriesQPochhammer R s 0 = 1 := by
  simp [powerSeriesQPochhammer]

theorem powerSeriesQPochhammer_succ (R : Type*) [CommRing R]
    (s m : ℕ) :
    powerSeriesQPochhammer R s (m + 1) =
      powerSeriesQPochhammer R s m * (1 - (X : R⟦X⟧) ^ (s + m)) := by
  rw [powerSeriesQPochhammer_eq_prod, powerSeriesQPochhammer_eq_prod]
  simp [Finset.prod_range_succ]

/-- `(Xˢ;X)ₘ` is a unit as soon as its initial exponent is positive. -/
theorem powerSeriesQPochhammer_isUnit (R : Type*) [CommRing R]
    {s : ℕ} (hs : 0 < s) (m : ℕ) :
    IsUnit (powerSeriesQPochhammer R s m) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [powerSeriesQPochhammer_eq_prod]
  simp [hs.ne']

/-- The bundled unit associated to `(Xˢ;X)ₘ`. -/
noncomputable def powerSeriesQPochhammerUnit (R : Type*) [CommRing R]
    (s m : ℕ) (hs : 0 < s) : R⟦X⟧ˣ :=
  (powerSeriesQPochhammer_isUnit R hs m).unit

@[simp] theorem coe_powerSeriesQPochhammerUnit (R : Type*) [CommRing R]
    (s m : ℕ) (hs : 0 < s) :
    (powerSeriesQPochhammerUnit R s m hs : R⟦X⟧) =
      powerSeriesQPochhammer R s m :=
  (powerSeriesQPochhammer_isUnit R hs m).unit_spec

end LeanCo.Rascoe
