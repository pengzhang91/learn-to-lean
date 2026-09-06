import LeanCo.EulerianTP3.SolidThreeRegroup
import LeanCo.EulerianTP3.GeneralizedSolidThree
import LeanCo.EulerianTP3.SolidTwo
import LeanCo.EulerianTP3.Specializations

/-!
# End-to-end theorems for arXiv:2608.29224

This module assembles the solid-minor calculations with the explicit
order-three lower-triangular Fekete criterion.  It states the ordinary main
theorem, the uniform parameterized theorem (also for an arbitrary matrix
satisfying the row-polynomial recurrence), and the three named families in
the paper's corollary.
-/

namespace LeanCo.EulerianTP3

open Polynomial

/-! ## Theorem 1.1 -/

/-- All admissible solid minors of the ordinary Eulerian triangle through
order three are strictly positive. -/
theorem eulerianTriangle_solidStrictUpToThree :
    SolidStrictUpToThree eulerianTriangle where
  entry_pos := eulerianTriangle_entry_pos
  det2_pos := eulerianTriangle_det2_solid_pos
  det3_pos := eulerianTriangle_det3_solid_pos

/-- The strict-admissible part of Mao's Theorem 1.1. -/
theorem mao_theorem_1_1_admissibleStrict :
    AdmissibleStrictUpToThree eulerianTriangle :=
  admissibleStrictUpToThree_of_solid eulerianTriangle
    eulerianTriangle_lowerTriangular eulerianTriangle_solidStrictUpToThree

/-- The paper's `TP₃` conclusion.  Its terminology uses “totally positive”
for nonnegativity of all minors. -/
theorem mao_theorem_1_1_totallyPositiveOrderThree :
    TotallyNonnegativeUpToThree eulerianTriangle :=
  totallyNonnegativeUpToThree_of_solid eulerianTriangle
    eulerianTriangle_lowerTriangular eulerianTriangle_solidStrictUpToThree

/-- Mao's Theorem 1.1, including both total nonnegativity through order three
and strict positivity of every admissible minor through order three. -/
theorem mao_theorem_1_1 :
    TotallyNonnegativeUpToThree eulerianTriangle ∧
      AdmissibleStrictUpToThree eulerianTriangle :=
  ⟨mao_theorem_1_1_totallyPositiveOrderThree,
    mao_theorem_1_1_admissibleStrict⟩

/-! ## Theorem 4.1: the canonical parameterized triangle -/

/-- The solid-minor hypothesis for the canonical triangle of the uniform
recurrence. -/
theorem eulerianTypeTriangle_solidStrictUpToThree
    {β : ℝ} {alpha : ℕ → ℝ}
    (hparam : EulerianTypeParameterConditions β alpha) :
    SolidStrictUpToThree (eulerianTypeTriangle β alpha) where
  entry_pos := eulerianTypeTriangle_entry_pos hparam.beta_pos hparam.alpha_pos
  det2_pos := eulerianTypeTriangle_det2_solid_pos
    hparam.beta_pos hparam.alpha_pos
  det3_pos := eulerianTypeTriangle_det3_solid_pos
    hparam.beta_pos hparam.alpha_pos (fun n ↦ by
      simpa [eulerianTypeDelta] using hparam.delta_nonneg n)

theorem eulerianTypeTriangle_admissibleStrictUpToThree
    {β : ℝ} {alpha : ℕ → ℝ}
    (hparam : EulerianTypeParameterConditions β alpha) :
    AdmissibleStrictUpToThree (eulerianTypeTriangle β alpha) :=
  admissibleStrictUpToThree_of_solid (eulerianTypeTriangle β alpha)
    (eulerianTypeTriangle_lowerTriangular hparam.beta_pos hparam.alpha_pos)
    (eulerianTypeTriangle_solidStrictUpToThree hparam)

theorem eulerianTypeTriangle_totallyPositiveOrderThree
    {β : ℝ} {alpha : ℕ → ℝ}
    (hparam : EulerianTypeParameterConditions β alpha) :
    TotallyNonnegativeUpToThree (eulerianTypeTriangle β alpha) :=
  totallyNonnegativeUpToThree_of_solid (eulerianTypeTriangle β alpha)
    (eulerianTypeTriangle_lowerTriangular hparam.beta_pos hparam.alpha_pos)
    (eulerianTypeTriangle_solidStrictUpToThree hparam)

/-- Canonical coefficient-triangle form of Theorem 4.1. -/
theorem mao_theorem_4_1_canonical
    {β : ℝ} {alpha : ℕ → ℝ}
    (hparam : EulerianTypeParameterConditions β alpha) :
    TotallyNonnegativeUpToThree (eulerianTypeTriangle β alpha) ∧
      AdmissibleStrictUpToThree (eulerianTypeTriangle β alpha) :=
  ⟨eulerianTypeTriangle_totallyPositiveOrderThree hparam,
    eulerianTypeTriangle_admissibleStrictUpToThree hparam⟩

/-! ## Theorem 4.1 in the paper's arbitrary-matrix form -/

/-- The literal arbitrary-matrix version of Theorem 4.1.  The hypotheses say
that the finite row-generating polynomials of `M` start at `1` and satisfy
the displayed differential recurrence. -/
theorem mao_theorem_4_1
    {β : ℝ} {alpha : ℕ → ℝ} (M : ℕ → ℕ → ℝ)
    (htri : LowerTriangular M)
    (hzero : rowGeneratingPolynomial M 0 = 1)
    (hsucc : ∀ n, rowGeneratingPolynomial M (n + 1) =
      (1 + C ((n : ℝ) * β + alpha n) * X) * rowGeneratingPolynomial M n
        + C β * X * (1 - X) * (rowGeneratingPolynomial M n).derivative)
    (hparam : EulerianTypeParameterConditions β alpha) :
    TotallyNonnegativeUpToThree M ∧ AdmissibleStrictUpToThree M := by
  have hM : M = eulerianTypeTriangle β alpha :=
    matrix_eq_eulerianTypeTriangle β alpha M htri hzero hsucc
      hparam.beta_pos hparam.alpha_pos
  rw [hM]
  exact mao_theorem_4_1_canonical hparam

/-! ## Corollary 4.2 -/

theorem mao_corollary_4_2_typeB :
    TotallyNonnegativeUpToThree typeBEulerianTriangle ∧
      AdmissibleStrictUpToThree typeBEulerianTriangle :=
  mao_theorem_4_1_canonical typeBEulerian_parameterConditions

theorem mao_corollary_4_2_mStirling (m : ℕ) (hm : 1 ≤ m) :
    TotallyNonnegativeUpToThree (mStirlingEulerianTriangle m) ∧
      AdmissibleStrictUpToThree (mStirlingEulerianTriangle m) :=
  mao_theorem_4_1_canonical (mStirlingEulerian_parameterConditions m hm)

theorem mao_corollary_4_2_rColored (r : ℕ) (hr : 2 ≤ r) :
    TotallyNonnegativeUpToThree (rColoredEulerianTriangle r) ∧
      AdmissibleStrictUpToThree (rColoredEulerianTriangle r) :=
  mao_theorem_4_1_canonical (rColoredEulerian_parameterConditions r hr)

/-- The ordinary specialization of Theorem 4.1 agrees pointwise with the
independently proved title theorem. -/
theorem mao_theorem_4_1_specializes_to_theorem_1_1 :
    ordinaryEulerianCanonicalTriangle = eulerianTriangle := by
  funext n k
  exact ordinaryEulerianCanonicalTriangle_eq_eulerianTriangle n k

end LeanCo.EulerianTP3
