import LeanCo.Rascoe.Complement
import LeanCo.Rascoe.NoOne
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher

/-!
# Formal generating series for unrestricted Rascoe partitions

All identities in this file live in the coefficientwise topology on formal
power series.  Consequently they have no hidden analytic convergence
hypothesis.  The analytic evaluation for a complex number in the open unit
disc is kept as a separate layer.
-/

open scoped BigOperators PowerSeries.WithPiTopology

namespace LeanCo.Rascoe

open PowerSeries

section Coefficients

variable (R : Type*) [CommSemiring R]

/-- Ordinary partition generating series. -/
noncomputable def partitionSeries : R⟦X⟧ :=
  PowerSeries.mk fun n => (partitionNumber n : R)

/-- Generating series `sum c(n) X^n`. -/
noncomputable def rascoeSeries : R⟦X⟧ :=
  PowerSeries.mk fun n => (rascoeNumber n : R)

/-- Generating series `sum e(n) X^n`. -/
noncomputable def nonRascoeSeries : R⟦X⟧ :=
  PowerSeries.mk fun n => (nonRascoeNumber n : R)

/-- Generating series for partitions with no part of size one. -/
noncomputable def noOneSeries : R⟦X⟧ :=
  PowerSeries.mk fun n => (noOneNumber n : R)

@[simp] theorem coeff_partitionSeries (n : ℕ) :
    coeff n (partitionSeries R) = (partitionNumber n : R) := by
  simp [partitionSeries]

@[simp] theorem coeff_rascoeSeries (n : ℕ) :
    coeff n (rascoeSeries R) = (rascoeNumber n : R) := by
  simp [rascoeSeries]

@[simp] theorem coeff_nonRascoeSeries (n : ℕ) :
    coeff n (nonRascoeSeries R) = (nonRascoeNumber n : R) := by
  simp [nonRascoeSeries]

@[simp] theorem coeff_noOneSeries (n : ℕ) :
    coeff n (noOneSeries R) = (noOneNumber n : R) := by
  simp [noOneSeries]

/-- The coefficientwise complement identity `C + E = P`. -/
theorem rascoeSeries_add_nonRascoeSeries :
    rascoeSeries R + nonRascoeSeries R = partitionSeries R := by
  ext n
  simp only [map_add, coeff_rascoeSeries, coeff_nonRascoeSeries,
    coeff_partitionSeries, ← Nat.cast_add]
  rw [rascoeNumber_add_nonRascoeNumber]

/-- The fundamental bijection, lifted to generating series: `C = X A`. -/
theorem rascoeSeries_eq_X_mul_noOneSeries :
    rascoeSeries R = X * noOneSeries R := by
  ext (_ | n)
  · simp
  · rw [coeff_rascoeSeries]
    have hcoeff := coeff_X_pow_mul (noOneSeries R) 1 n
    simp only [pow_one] at hcoeff
    rw [hcoeff]
    rw [coeff_noOneSeries, rascoeNumber_succ_eq_noOneNumber]

@[simp] theorem noOneNumber_zero : noOneNumber 0 = 1 := by
  let p0 : NoOnePartition 0 :=
    ⟨default, by simp [HasNoOne, Nat.Partition.partition_zero_parts]⟩
  letI : Unique (NoOnePartition 0) :=
    { default := p0
      uniq := fun p => Subtype.ext (Subsingleton.elim p.1 p0.1) }
  simp [noOneNumber]

end Coefficients

section RingCoefficients

variable (R : Type*) [CommRing R]

/-- Removing/adding a part `1`, coefficientwise: `A = (1-X)P`. -/
theorem noOneSeries_eq_one_sub_X_mul_partitionSeries :
    noOneSeries R = (1 - X) * partitionSeries R := by
  rw [sub_mul, one_mul]
  ext (_ | n)
  · simp [partitionSeries]
  · rw [map_sub, coeff_noOneSeries, coeff_partitionSeries]
    have hcoeff := coeff_X_pow_mul (partitionSeries R) 1 n
    simp only [pow_one] at hcoeff
    rw [hcoeff, coeff_partitionSeries,
      partitionNumber_succ_eq_noOneNumber_add]
    push_cast
    ring

/-- The Rascoe series in terms of the ordinary partition series. -/
theorem rascoeSeries_eq_X_one_sub_X_mul_partitionSeries :
    rascoeSeries R = X * (1 - X) * partitionSeries R := by
  rw [rascoeSeries_eq_X_mul_noOneSeries,
    noOneSeries_eq_one_sub_X_mul_partitionSeries]
  ring

/-- The non-Rascoe series in terms of the ordinary partition series. -/
theorem nonRascoeSeries_eq_one_sub_X_add_X_sq_mul_partitionSeries :
    nonRascoeSeries R = (1 - X + X ^ 2) * partitionSeries R := by
  have hcomp := rascoeSeries_add_nonRascoeSeries R
  have hrascoe := rascoeSeries_eq_X_one_sub_X_mul_partitionSeries R
  linear_combination hcomp - hrascoe

end RingCoefficients

section EulerProducts

variable (R : Type*) [CommSemiring R] [TopologicalSpace R] [T2Space R]
  [IsTopologicalSemiring R]

/-- The `i`th Euler factor `1 + X^(i+1) + X^(2(i+1)) + ...`. -/
noncomputable def partitionEulerFactor (i : ℕ) : R⟦X⟧ :=
  ∑' j : ℕ, X ^ ((i + 1) * j)

/-- The formal reciprocal Euler product `1 / (X;X)_infinity`. -/
noncomputable def partitionEulerProduct : R⟦X⟧ :=
  ∏' i : ℕ, partitionEulerFactor R i

/-- The formal reciprocal shifted Euler product `1 / (X^2;X)_infinity`. -/
noncomputable def noOneEulerProduct : R⟦X⟧ :=
  ∏' i : ℕ, if i + 1 ≠ 1 then partitionEulerFactor R i else 1

theorem partitionSeries_eq_genFun :
    partitionSeries R = Nat.Partition.genFun (fun _ _ => (1 : R)) := by
  ext n
  simp only [coeff_partitionSeries, Nat.Partition.coeff_genFun]
  rw [partitionNumber]
  simp

/-- Euler's partition product as an identity of formal power series. -/
theorem partitionSeries_eq_eulerProduct :
    partitionSeries R = partitionEulerProduct R := by
  calc
    partitionSeries R =
        PowerSeries.mk (fun n =>
          ((Nat.Partition.restricted n (fun _ => True)).card : R)) := by
      ext n
      simp [partitionSeries, partitionNumber, Nat.Partition.restricted]
    _ = ∏' i : ℕ, ∑' j : ℕ, X ^ ((i + 1) * j) := by
      simpa using
        (Nat.Partition.powerSeriesMk_card_restricted_eq_tprod R
          (fun _ => True))
    _ = partitionEulerProduct R := by
      simp only [partitionEulerProduct, partitionEulerFactor]

/-- The no-one series is the shifted Euler product. -/
theorem noOneSeries_eq_eulerProduct :
    noOneSeries R = noOneEulerProduct R := by
  classical
  calc
    noOneSeries R =
        PowerSeries.mk (fun n =>
          ((Nat.Partition.restricted n (fun i => i ≠ 1)).card : R)) := by
      ext n
      simp only [coeff_noOneSeries, PowerSeries.coeff_mk]
      congr 1
      rw [noOneNumber, Fintype.card_subtype]
      congr 1
      ext p
      simp only [Set.mem_toFinset, Set.mem_setOf_eq,
        Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ,
        true_and, HasNoOne]
      constructor
      · intro h i hi hi1
        exact h (hi1 ▸ hi)
      · intro h h1
        exact h 1 h1 rfl
    _ = ∏' i : ℕ, if i + 1 ≠ 1 then
          ∑' j : ℕ, X ^ ((i + 1) * j) else 1 := by
      simpa using
        (Nat.Partition.powerSeriesMk_card_restricted_eq_tprod R
          (fun i => i ≠ 1))
    _ = noOneEulerProduct R := by
      simp only [noOneEulerProduct, partitionEulerFactor]

/-- First rightmost identity of Theorem 1.1, as an unconditional FPS identity. -/
theorem rascoeSeries_eq_X_mul_noOneEulerProduct :
    rascoeSeries R = X * noOneEulerProduct R := by
  rw [rascoeSeries_eq_X_mul_noOneSeries, noOneSeries_eq_eulerProduct]

end EulerProducts

section RingEulerProduct

variable (R : Type*) [CommRing R] [TopologicalSpace R] [T2Space R]
  [IsTopologicalRing R]

/-- Second rightmost identity of Theorem 1.1, as an unconditional FPS identity. -/
theorem nonRascoeSeries_eq_polynomial_mul_partitionEulerProduct :
    nonRascoeSeries R = (1 - X + X ^ 2) * partitionEulerProduct R := by
  rw [nonRascoeSeries_eq_one_sub_X_add_X_sq_mul_partitionSeries,
    partitionSeries_eq_eulerProduct]

end RingEulerProduct

end LeanCo.Rascoe
