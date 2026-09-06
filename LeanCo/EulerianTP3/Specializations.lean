import LeanCo.EulerianTP3.GeneralizedRows
import LeanCo.EulerianTP3.Rows

/-!
# Canonical specializations of the Eulerian-type recurrence

This file records the four parameter choices following Theorem 4.1 of
arXiv:2608.29224.  The arrays are defined canonically as coefficient triangles
of `eulerianTypePoly`; no combinatorial model is needed.  We expose their
coefficient recurrences and verify the three parameter hypotheses of the
theorem.  The ordinary specialization is also identified pointwise with the
independently defined ordinary Eulerian triangle.
-/

namespace LeanCo.EulerianTP3

open scoped Polynomial
open Polynomial

/-! ## The uniform parameter condition -/

/-- The quantity called `alpha (n+1) - alpha n + beta` in Theorem 4.1. -/
def eulerianTypeDelta (beta : ℝ) (alpha : ℕ → ℝ) (n : ℕ) : ℝ :=
  alpha (n + 1) - alpha n + beta

/-- Exactly the three parameter hypotheses of Theorem 4.1. -/
structure EulerianTypeParameterConditions (beta : ℝ) (alpha : ℕ → ℝ) : Prop where
  beta_pos : 0 < beta
  alpha_pos : ∀ n, 0 < alpha n
  delta_nonneg : ∀ n, 0 ≤ eulerianTypeDelta beta alpha n

/-! ## Canonical parameter choices and coefficient triangles -/

/-- The constant `alpha` parameter for the ordinary Eulerian triangle. -/
def ordinaryEulerianAlpha : ℕ → ℝ := fun _ ↦ 1

/-- The constant `alpha` parameter for the type-B Eulerian triangle. -/
def typeBEulerianAlpha : ℕ → ℝ := fun _ ↦ 1

/-- The affine `alpha` parameter for the `m`-Stirling Eulerian triangle. -/
def mStirlingEulerianAlpha (m : ℕ) : ℕ → ℝ := fun n ↦
  ((m : ℝ) - 1) * (n : ℝ) + (m : ℝ)

/-- The constant `alpha` parameter for the `r`-colored Eulerian triangle. -/
def rColoredEulerianAlpha (r : ℕ) : ℕ → ℝ := fun _ ↦
  (r : ℝ) - 1

/-- The ordinary Eulerian specialization `(beta, alpha) = (1, 1)`. -/
noncomputable def ordinaryEulerianCanonicalTriangle : ℕ → ℕ → ℝ :=
  eulerianTypeTriangle 1 ordinaryEulerianAlpha

/-- The type-B specialization `(beta, alpha) = (2, 1)`. -/
noncomputable def typeBEulerianTriangle : ℕ → ℕ → ℝ :=
  eulerianTypeTriangle 2 typeBEulerianAlpha

/-- The `m`-Stirling specialization
`(beta, alpha n) = (1, (m-1)n+m)`. -/
noncomputable def mStirlingEulerianTriangle (m : ℕ) : ℕ → ℕ → ℝ :=
  eulerianTypeTriangle 1 (mStirlingEulerianAlpha m)

/-- The `r`-colored specialization `(beta, alpha) = (r, r-1)`. -/
noncomputable def rColoredEulerianTriangle (r : ℕ) : ℕ → ℕ → ℝ :=
  eulerianTypeTriangle (r : ℝ) (rColoredEulerianAlpha r)

/-! ## Initial rows and coefficient recurrences -/

@[simp] theorem ordinaryEulerianCanonicalTriangle_zero_zero :
    ordinaryEulerianCanonicalTriangle 0 0 = 1 := by
  simp [ordinaryEulerianCanonicalTriangle]

@[simp] theorem ordinaryEulerianCanonicalTriangle_zero_succ (k : ℕ) :
    ordinaryEulerianCanonicalTriangle 0 (k + 1) = 0 := by
  simp [ordinaryEulerianCanonicalTriangle]

theorem ordinaryEulerianCanonicalTriangle_succ_succ (n k : ℕ) :
    ordinaryEulerianCanonicalTriangle (n + 1) (k + 1) =
      (1 + (k + 1 : ℝ)) * ordinaryEulerianCanonicalTriangle n (k + 1) +
        (1 + (n - k : ℝ)) * ordinaryEulerianCanonicalTriangle n k := by
  simpa [ordinaryEulerianCanonicalTriangle, ordinaryEulerianAlpha] using
    eulerianTypeTriangle_succ_succ 1 ordinaryEulerianAlpha n k

@[simp] theorem typeBEulerianTriangle_zero_zero :
    typeBEulerianTriangle 0 0 = 1 := by
  simp [typeBEulerianTriangle]

@[simp] theorem typeBEulerianTriangle_zero_succ (k : ℕ) :
    typeBEulerianTriangle 0 (k + 1) = 0 := by
  simp [typeBEulerianTriangle]

theorem typeBEulerianTriangle_succ_succ (n k : ℕ) :
    typeBEulerianTriangle (n + 1) (k + 1) =
      (1 + 2 * (k + 1 : ℝ)) * typeBEulerianTriangle n (k + 1) +
        (1 + 2 * (n - k : ℝ)) * typeBEulerianTriangle n k := by
  simpa [typeBEulerianTriangle, typeBEulerianAlpha] using
    eulerianTypeTriangle_succ_succ 2 typeBEulerianAlpha n k

@[simp] theorem mStirlingEulerianTriangle_zero_zero (m : ℕ) :
    mStirlingEulerianTriangle m 0 0 = 1 := by
  simp [mStirlingEulerianTriangle]

@[simp] theorem mStirlingEulerianTriangle_zero_succ (m k : ℕ) :
    mStirlingEulerianTriangle m 0 (k + 1) = 0 := by
  simp [mStirlingEulerianTriangle]

theorem mStirlingEulerianTriangle_succ_succ (m n k : ℕ) :
    mStirlingEulerianTriangle m (n + 1) (k + 1) =
      (1 + (k + 1 : ℝ)) * mStirlingEulerianTriangle m n (k + 1) +
        (mStirlingEulerianAlpha m n + (n - k : ℝ)) *
          mStirlingEulerianTriangle m n k := by
  simpa [mStirlingEulerianTriangle] using
    eulerianTypeTriangle_succ_succ 1 (mStirlingEulerianAlpha m) n k

@[simp] theorem rColoredEulerianTriangle_zero_zero (r : ℕ) :
    rColoredEulerianTriangle r 0 0 = 1 := by
  simp [rColoredEulerianTriangle]

@[simp] theorem rColoredEulerianTriangle_zero_succ (r k : ℕ) :
    rColoredEulerianTriangle r 0 (k + 1) = 0 := by
  simp [rColoredEulerianTriangle]

theorem rColoredEulerianTriangle_succ_succ (r n k : ℕ) :
    rColoredEulerianTriangle r (n + 1) (k + 1) =
      (1 + (r : ℝ) * (k + 1 : ℝ)) * rColoredEulerianTriangle r n (k + 1) +
        (rColoredEulerianAlpha r n + (r : ℝ) * (n - k : ℝ)) *
          rColoredEulerianTriangle r n k := by
  exact eulerianTypeTriangle_succ_succ (r : ℝ) (rColoredEulerianAlpha r) n k

/-! ## Identification of the ordinary specialization -/

/-- The canonical generalized polynomial with `(beta, alpha) = (1, 1)` is
definitionally governed by the same recurrence as `eulerianPoly`. -/
theorem ordinaryEulerianTypePoly_eq_eulerianPoly (n : ℕ) :
    eulerianTypePoly 1 ordinaryEulerianAlpha n = eulerianPoly n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [eulerianTypePoly_succ, eulerianPoly_succ, ih]
      simp [ordinaryEulerianAlpha]

/-- The canonical ordinary coefficient triangle is pointwise equal to the
ordinary Eulerian triangle used by the main theorem. -/
theorem ordinaryEulerianCanonicalTriangle_eq_eulerianTriangle (n k : ℕ) :
    ordinaryEulerianCanonicalTriangle n k = eulerianTriangle n k := by
  simp [ordinaryEulerianCanonicalTriangle, eulerianTypeTriangle,
    eulerianTriangle, ordinaryEulerianTypePoly_eq_eulerianPoly]

/-! ## Verification of the hypotheses of Theorem 4.1 -/

@[simp] theorem ordinaryEulerian_delta (n : ℕ) :
    eulerianTypeDelta 1 ordinaryEulerianAlpha n = 1 := by
  simp [eulerianTypeDelta, ordinaryEulerianAlpha]

@[simp] theorem typeBEulerian_delta (n : ℕ) :
    eulerianTypeDelta 2 typeBEulerianAlpha n = 2 := by
  simp [eulerianTypeDelta, typeBEulerianAlpha]

@[simp] theorem mStirlingEulerian_delta (m n : ℕ) :
    eulerianTypeDelta 1 (mStirlingEulerianAlpha m) n = (m : ℝ) := by
  simp [eulerianTypeDelta, mStirlingEulerianAlpha]
  push_cast
  ring

@[simp] theorem rColoredEulerian_delta (r n : ℕ) :
    eulerianTypeDelta (r : ℝ) (rColoredEulerianAlpha r) n = (r : ℝ) := by
  simp [eulerianTypeDelta, rColoredEulerianAlpha]

theorem ordinaryEulerian_parameterConditions :
    EulerianTypeParameterConditions 1 ordinaryEulerianAlpha := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro n
    simp [ordinaryEulerianAlpha]
  · intro n
    simp

theorem typeBEulerian_parameterConditions :
    EulerianTypeParameterConditions 2 typeBEulerianAlpha := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro n
    simp [typeBEulerianAlpha]
  · intro n
    simp

theorem mStirlingEulerian_alpha_pos (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    0 < mStirlingEulerianAlpha m n := by
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  dsimp [mStirlingEulerianAlpha]
  nlinarith

theorem mStirlingEulerian_parameterConditions (m : ℕ) (hm : 1 ≤ m) :
    EulerianTypeParameterConditions 1 (mStirlingEulerianAlpha m) := by
  refine ⟨by norm_num, mStirlingEulerian_alpha_pos m hm, ?_⟩
  intro n
  rw [mStirlingEulerian_delta]
  positivity

theorem rColoredEulerian_alpha_pos (r : ℕ) (hr : 2 ≤ r) (n : ℕ) :
    0 < rColoredEulerianAlpha r n := by
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  dsimp [rColoredEulerianAlpha]
  linarith

theorem rColoredEulerian_parameterConditions (r : ℕ) (hr : 2 ≤ r) :
    EulerianTypeParameterConditions (r : ℝ) (rColoredEulerianAlpha r) := by
  refine ⟨?_, rColoredEulerian_alpha_pos r hr, ?_⟩
  · exact_mod_cast (show 0 < r by omega)
  · intro n
    rw [rColoredEulerian_delta]
    positivity

end LeanCo.EulerianTP3
