import LeanCo.CyclicBraidArrangement.FiniteFieldCount
import Mathlib.RingTheory.Polynomial.Basic

/-! The cyclic expression as an actual rational polynomial. -/

namespace CyclicBraidArrangement

open scoped BigOperators

/-- Polynomial version of the generalized binomial coefficient. -/
noncomputable def generalizedChoosePolynomial (k : ℕ) : Polynomial ℚ :=
  Polynomial.C ((k.factorial : ℚ)⁻¹) *
    ∏ i ∈ Finset.range k,
      ((Polynomial.X : Polynomial ℚ) - Polynomial.C (i : ℚ))

theorem eval_generalizedChoosePolynomial (x : ℚ) (k : ℕ) :
    Polynomial.eval x (generalizedChoosePolynomial k) = generalizedChoose x k := by
  classical
  simp [generalizedChoosePolynomial, generalizedChoose, div_eq_inv_mul,
    Polynomial.eval_prod]

/-- Translation of a polynomial by `c`, namely `P(t-c)`. -/
noncomputable def translatePolynomial (P : Polynomial ℚ) (c : ℚ) : Polynomial ℚ :=
  P.comp (Polynomial.X - Polynomial.C c)

theorem eval_translatePolynomial (P : Polynomial ℚ) (c t : ℚ) :
    Polynomial.eval t (translatePolynomial P c) = Polynomial.eval (t - c) P := by
  simp [translatePolynomial]

/-- The reduced characteristic-polynomial candidate supplied by the cyclic
formula in the main theorem. -/
noncomputable def cyclePolynomial {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) : Polynomial ℚ :=
  ∑ w : DeformationMatrix.NormalizedCycle n,
    (generalizedChoosePolynomial (n - 1)).comp
      (Polynomial.X - Polynomial.C ((M.cycleWeight w.1 + 1 : ℕ) : ℚ))

theorem eval_cyclePolynomial {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (t : ℚ) :
    Polynomial.eval t (cyclePolynomial M) = cycleFormula M t := by
  classical
  unfold cyclePolynomial cycleFormula
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    eval_generalizedChoosePolynomial]
  apply Finset.sum_congr rfl
  intro w hw
  apply congrArg (fun x : ℚ ↦ generalizedChoose x (n - 1))
  push_cast
  ring

theorem adjacentGapOrbitCount_eq_eval_cyclePolynomial {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (q : ℕ)
    (hfit : ∀ w : DeformationMatrix.NormalizedCycle n,
      n + M.cycleWeight w.1 ≤ q) :
    (M.adjacentGapOrbitCount q : ℚ) =
      Polynomial.eval (q : ℚ) (cyclePolynomial M) := by
  rw [eval_cyclePolynomial]
  exact M.adjacentGapOrbitCount_eq_cycleFormula q hfit

/-- The full-polynomial *candidate* furnished by the cyclic formula; the
factor `X` restores the diagonal translation direction.  This definition is
deliberately not called a characteristic polynomial: identifying it with the
arrangement invariant is a theorem from an independent finite-field
specification, proved in `CharacteristicBridge`. -/
noncomputable def fullCyclePolynomialCandidate {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) : Polynomial ℚ :=
  Polynomial.X * cyclePolynomial M

/-- At all sufficiently large finite-field sizes, the full polynomial
evaluates to `q` times the rotation-orbit complement count. -/
theorem eval_fullCyclePolynomialCandidate {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (q : ℕ)
    (hfit : ∀ w : DeformationMatrix.NormalizedCycle n,
      n + M.cycleWeight w.1 ≤ q) :
    Polynomial.eval (q : ℚ) (fullCyclePolynomialCandidate M) =
      (q : ℚ) * (M.adjacentGapOrbitCount q : ℚ) := by
  rw [fullCyclePolynomialCandidate, Polynomial.eval_mul, Polynomial.eval_X,
    ← adjacentGapOrbitCount_eq_eval_cyclePolynomial M q hfit]

/-- Polynomial form of the paper's two-sided shift theorem. -/
theorem cyclePolynomial_extend_shift {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (M : DeformationMatrix n) (α β : Fin n → ℕ) :
    cyclePolynomial (M.extend α β) =
      translatePolynomial (cyclePolynomial M) ((∑ i, α i) + ∑ i, β i) := by
  apply Polynomial.funext
  intro t
  rw [eval_cyclePolynomial, eval_translatePolynomial,
    eval_cyclePolynomial, cycleFormula_extend_shift hn]

/-- Equal total two-sided parameters give identical cycle polynomials. -/
theorem cyclePolynomial_redistribution {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (M : DeformationMatrix n) (α β α' β' : Fin n → ℕ)
    (h : (∑ i, α i) + ∑ i, β i = (∑ i, α' i) + ∑ i, β' i) :
    cyclePolynomial (M.extend α β) = cyclePolynomial (M.extend α' β') := by
  rw [cyclePolynomial_extend_shift hn, cyclePolynomial_extend_shift hn]
  apply congrArg (translatePolynomial (cyclePolynomial M))
  exact_mod_cast h

end CyclicBraidArrangement
