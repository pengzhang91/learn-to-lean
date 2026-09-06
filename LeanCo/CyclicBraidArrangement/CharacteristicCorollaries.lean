import LeanCo.CyclicBraidArrangement.ArrangementMainTheorem
import LeanCo.CyclicBraidArrangement.Graphical
import LeanCo.CyclicBraidArrangement.UniformEulerian

/-!
# Characteristic-polynomial forms of the uniform and graphical corollaries

The combinatorial identities in `UniformEulerian` and `Graphical` concern the
cyclic formula itself.  This file transports them to any independently
specified reduced characteristic polynomial through the prime finite-field
interface of `CharacteristicBridge`.  Thus none of the results below defines
the left-hand side to be the desired cyclic sum.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

/-- Corollary 4.1: the two-sided uniform interval formula, stated for an
independently supplied reduced characteristic polynomial. -/
theorem reduced_uniform_eulerian_of_primeFiniteFieldSpecification
    {n u v : ℕ} [NeZero n] (hn : 2 ≤ n)
    (α β : Fin n → ℕ) (P : Polynomial ℚ)
    (hP : ((uniform n u v).extend α β).IsReducedPrimeFiniteFieldPolynomial P)
    (t : ℚ) :
    Polynomial.eval t P =
      ∑ d ∈ Finset.range (n - 1),
        (cyclicEulerianNumber n d : ℚ) *
          generalizedChoose
            (t - ((∑ i, α i) + ∑ i, β i) -
              (((n : ℤ) * u + ((v : ℤ) - u) * (d + 1) : ℤ) : ℚ) - 1)
            (n - 1) := by
  rw [mainTheorem_reduced_eval_of_primeFiniteFieldSpecification
      ((uniform n u v).extend α β)
      (cyclicallyCompatible_extend _ (cyclicallyCompatible_uniform n u v) α β) hP,
    cycleFormula_extend_shift hn,
    cycleFormula_uniform_eulerian hn]

/-- Corollary 4.2, graphical Shi case, transported from the cyclic sum to an
independently specified reduced characteristic polynomial. -/
theorem reduced_graphicalShi_of_primeFiniteFieldSpecification
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (α β : Fin n → ℕ) (P : Polynomial ℚ)
    (hP : ((graphicalShi G).extend α β).IsReducedPrimeFiniteFieldPolynomial P)
    (t : ℚ) :
    Polynomial.eval t P =
      ∑ w : NormalizedCycle n,
        generalizedChoose
          (t - ((∑ i, α i) + ∑ i, β i) -
            graphicalCyclicDescents G w.1 - 1)
          (n - 1) := by
  rw [mainTheorem_reduced_eval_of_primeFiniteFieldSpecification
      ((graphicalShi G).extend α β)
      (cyclicallyCompatible_extend _ (cyclicallyCompatible_graphicalShi G) α β) hP,
    cycleFormula_graphicalShi_extend_explicit hn]

/-- Corollary 4.2, graphical Catalan case, transported from the cyclic sum to
an independently specified reduced characteristic polynomial. -/
theorem reduced_graphicalCatalan_of_primeFiniteFieldSpecification
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (α β : Fin n → ℕ) (P : Polynomial ℚ)
    (hP : ((graphicalCatalan G).extend α β).IsReducedPrimeFiniteFieldPolynomial P)
    (t : ℚ) :
    Polynomial.eval t P =
      ∑ w : NormalizedCycle n,
        generalizedChoose
          (t - ((∑ i, α i) + ∑ i, β i) -
            graphicalCyclicEdges G w.1 - 1)
          (n - 1) := by
  rw [mainTheorem_reduced_eval_of_primeFiniteFieldSpecification
      ((graphicalCatalan G).extend α β)
      (cyclicallyCompatible_extend _ (cyclicallyCompatible_graphicalCatalan G) α β) hP,
    cycleFormula_graphicalCatalan_extend_explicit hn]

/-! ## Unconditional Whitney-characteristic-polynomial endpoints -/

/-- Corollary 4.1 for the independently defined reduced characteristic
polynomial of the two-sided uniform deformation. -/
theorem whitneyReduced_uniform_eulerian
    {n u v : ℕ} [NeZero n] (hn : 2 ≤ n)
    (α β : Fin n → ℕ) (t : ℚ) :
    Polynomial.eval t
        ((uniform n u v).extend α β).whitneyReducedCharacteristicPolynomial =
      ∑ d ∈ Finset.range (n - 1),
        (cyclicEulerianNumber n d : ℚ) *
          generalizedChoose
            (t - ((∑ i, α i) + ∑ i, β i) -
              (((n : ℤ) * u + ((v : ℤ) - u) * (d + 1) : ℤ) : ℚ) - 1)
            (n - 1) := by
  rw [((uniform n u v).extend α β).whitney_mainTheorem_reduced
        ((uniform n u v).cyclicallyCompatible_extend
          (cyclicallyCompatible_uniform n u v) α β),
    eval_cyclePolynomial, cycleFormula_extend_shift hn,
    cycleFormula_uniform_eulerian hn]

/-- Corollary 4.2, graphical Shi case, for the independently defined reduced
characteristic polynomial. -/
theorem whitneyReduced_graphicalShi
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (α β : Fin n → ℕ) (t : ℚ) :
    Polynomial.eval t
        ((graphicalShi G).extend α β).whitneyReducedCharacteristicPolynomial =
      ∑ w : NormalizedCycle n,
        generalizedChoose
          (t - ((∑ i, α i) + ∑ i, β i) -
            graphicalCyclicDescents G w.1 - 1)
          (n - 1) := by
  rw [((graphicalShi G).extend α β).whitney_mainTheorem_reduced
        ((graphicalShi G).cyclicallyCompatible_extend
          (cyclicallyCompatible_graphicalShi G) α β),
    eval_cyclePolynomial,
    cycleFormula_graphicalShi_extend_explicit hn]

/-- Corollary 4.2, graphical Catalan case, for the independently defined
reduced characteristic polynomial. -/
theorem whitneyReduced_graphicalCatalan
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) (α β : Fin n → ℕ) (t : ℚ) :
    Polynomial.eval t
        ((graphicalCatalan G).extend α β).whitneyReducedCharacteristicPolynomial =
      ∑ w : NormalizedCycle n,
        generalizedChoose
          (t - ((∑ i, α i) + ∑ i, β i) -
            graphicalCyclicEdges G w.1 - 1)
          (n - 1) := by
  rw [((graphicalCatalan G).extend α β).whitney_mainTheorem_reduced
        ((graphicalCatalan G).cyclicallyCompatible_extend
          (cyclicallyCompatible_graphicalCatalan G) α β),
    eval_cyclePolynomial,
    cycleFormula_graphicalCatalan_extend_explicit hn]

end DeformationMatrix

end CyclicBraidArrangement
