import LeanCo.CyclicBraidArrangement.FiniteFieldPlacementCount
import LeanCo.CyclicBraidArrangement.CyclePolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Finite-field specification bridge

This file deliberately separates an independently supplied polynomial from
the cyclic polynomial constructed in `CyclePolynomial`.  The specification
below only says that the supplied polynomial eventually evaluates to the
all-ordered-pairs-safe circle-placement count from
`FiniteFieldPlacementCount`; it does not define the left-hand side to be the
cyclic gap sum.

To apply the results to an arrangement-theoretic characteristic polynomial,
one must separately prove that the latter satisfies this finite-field
specification.  That remaining bridge is exactly the general finite-field
method quoted as Lemma 2.1 in the paper.  Cyclic compatibility itself is not
external here: it is used below to prove that the all-pairs count equals the
adjacent-gap enumeration.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

/-- Two rational polynomials agreeing at every sufficiently large natural
argument are equal.  The proof exhibits an infinite set of evaluation points,
rather than using a degree bound. -/
theorem polynomial_eq_of_eventually_natCast_eval_eq
    (P Q : Polynomial ℚ)
    (h : ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      Polynomial.eval (q : ℚ) P = Polynomial.eval (q : ℚ) Q) :
    P = Q := by
  rcases h with ⟨N, hN⟩
  apply Polynomial.eq_of_infinite_eval_eq P Q
  let f : ℕ → ℚ := fun k ↦ ((N + k : ℕ) : ℚ)
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    norm_cast at hab
    omega
  refine (Set.infinite_range_of_injective hf).mono ?_
  rintro _ ⟨k, rfl⟩
  exact hN (N + k) (by omega)

/-- Two rational polynomials agreeing at every sufficiently large prime
natural argument are equal.  Unlike the stronger preceding lemma, the
infinite evaluation set here is obtained from Euclid's theorem. -/
theorem polynomial_eq_of_eventually_prime_natCast_eval_eq
    (P Q : Polynomial ℚ)
    (h : ∃ N : ℕ, ∀ q : ℕ, N ≤ q → Nat.Prime q →
      Polynomial.eval (q : ℚ) P = Polynomial.eval (q : ℚ) Q) :
    P = Q := by
  rcases h with ⟨N, hN⟩
  apply Polynomial.eq_of_infinite_eval_eq P Q
  let primesAbove : Set ℕ := {p | N ≤ p ∧ Nat.Prime p}
  have hprimes : primesAbove.Infinite := by
    apply Set.infinite_of_not_bddAbove
    intro hbounded
    rcases hbounded with ⟨B, hB⟩
    obtain ⟨p, hp, hpPrime⟩ :=
      Nat.exists_infinite_primes (max N (B + 1))
    have hpN : N ≤ p := (Nat.le_max_left N (B + 1)).trans hp
    have hpB : B + 1 ≤ p := (Nat.le_max_right N (B + 1)).trans hp
    have hpMem : p ∈ primesAbove := ⟨hpN, hpPrime⟩
    have := hB hpMem
    omega
  have hcast : ((fun p : ℕ ↦ (p : ℚ)) '' primesAbove).Infinite := by
    apply hprimes.image
    intro a ha b hb hab
    change (a : ℚ) = (b : ℚ) at hab
    exact_mod_cast hab
  refine hcast.mono ?_
  rintro _ ⟨p, hp, rfl⟩
  exact hN p hp.1 hp.2

namespace DeformationMatrix

/-- A non-circular finite-field specification for a candidate reduced
characteristic polynomial: at every sufficiently large natural argument it
equals the actual all-pairs-safe placement count modulo rotation. -/
def IsReducedFiniteFieldPolynomial {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (P : Polynomial ℚ) : Prop :=
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
    Polynomial.eval (q : ℚ) P = (M.finiteFieldComplementOrbitCount q : ℚ)

/-- The eventual reduced finite-field specification determines at most one
rational polynomial. -/
theorem isReducedFiniteFieldPolynomial_unique {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) {P Q : Polynomial ℚ}
    (hP : M.IsReducedFiniteFieldPolynomial P)
    (hQ : M.IsReducedFiniteFieldPolynomial Q) :
    P = Q := by
  rcases hP with ⟨NP, hP⟩
  rcases hQ with ⟨NQ, hQ⟩
  apply polynomial_eq_of_eventually_natCast_eval_eq
  refine ⟨max NP NQ, ?_⟩
  intro q hq
  rw [hP q ((Nat.le_max_left NP NQ).trans hq),
    hQ q ((Nat.le_max_right NP NQ).trans hq)]

/-- The cyclic polynomial constructed from the paper's gap formula satisfies
the non-circular eventual finite-field specification. -/
theorem cyclePolynomial_isReducedFiniteFieldPolynomial {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible) :
    M.IsReducedFiniteFieldPolynomial (cyclePolynomial M) := by
  classical
  let Q := n + ∑ w : NormalizedCycle n, M.cycleWeight w.1
  refine ⟨Q, ?_⟩
  intro q hq
  symm
  rw [eval_cyclePolynomial]
  apply finiteFieldComplementOrbitCount_eq_cycleFormula M hM q
  intro w
  have hw : M.cycleWeight w.1 ≤
      ∑ u : NormalizedCycle n, M.cycleWeight u.1 :=
    Finset.single_le_sum
      (f := fun u : NormalizedCycle n ↦ M.cycleWeight u.1)
      (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ w)
  have hwQ : n + M.cycleWeight w.1 ≤ Q := by
    dsimp [Q]
    exact Nat.add_le_add_left hw n
  exact hwQ.trans hq

/-- Main-theorem reduced polynomial identity, conditional only on an
independently supplied polynomial satisfying the finite-field specification. -/
theorem mainTheorem_reduced_of_finiteFieldSpecification
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    {P : Polynomial ℚ} (hP : M.IsReducedFiniteFieldPolynomial P) :
    P = cyclePolynomial M :=
  isReducedFiniteFieldPolynomial_unique M hP
    (cyclePolynomial_isReducedFiniteFieldPolynomial M hM)

/-- Evaluation form of the reduced main theorem. -/
theorem mainTheorem_reduced_eval_of_finiteFieldSpecification
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    {P : Polynomial ℚ} (hP : M.IsReducedFiniteFieldPolynomial P) (t : ℚ) :
    Polynomial.eval t P = cycleFormula M t := by
  rw [mainTheorem_reduced_of_finiteFieldSpecification M hM hP,
    eval_cyclePolynomial]

/-- Conditional two-sided extension shift for any independently supplied
base and extended reduced polynomials satisfying their finite-field
specifications. -/
theorem mainTheorem_extension_shift_of_finiteFieldSpecifications
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    (α β : Fin n → ℕ) {P Pext : Polynomial ℚ}
    (hP : M.IsReducedFiniteFieldPolynomial P)
    (hPext : (M.extend α β).IsReducedFiniteFieldPolynomial Pext) :
    Pext = translatePolynomial P ((∑ i, α i) + ∑ i, β i) := by
  calc
    Pext = cyclePolynomial (M.extend α β) :=
      mainTheorem_reduced_of_finiteFieldSpecification (M.extend α β)
        (cyclicallyCompatible_extend M hM α β) hPext
    _ = translatePolynomial (cyclePolynomial M)
        ((∑ i, α i) + ∑ i, β i) :=
      cyclePolynomial_extend_shift hn M α β
    _ = translatePolynomial P
        ((∑ i, α i) + ∑ i, β i) := by
      rw [mainTheorem_reduced_of_finiteFieldSpecification M hM hP]

/-- The paper-exact reduced finite-field specification: agreement with the
all-pairs-safe placement count is required only at every sufficiently large
prime. -/
def IsReducedPrimeFiniteFieldPolynomial {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (P : Polynomial ℚ) : Prop :=
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → Nat.Prime q →
    Polynomial.eval (q : ℚ) P = (M.finiteFieldComplementOrbitCount q : ℚ)

/-- The all-natural reduced specification implies its paper-exact prime-only
variant. -/
theorem isReducedFiniteFieldPolynomial_toPrime
    {n : ℕ} [NeZero n] (M : DeformationMatrix n) {P : Polynomial ℚ}
    (hP : M.IsReducedFiniteFieldPolynomial P) :
    M.IsReducedPrimeFiniteFieldPolynomial P := by
  rcases hP with ⟨Q, hQ⟩
  exact ⟨Q, fun q hq _ ↦ hQ q hq⟩

/-- The sufficiently-large-prime reduced specification determines at most
one rational polynomial. -/
theorem isReducedPrimeFiniteFieldPolynomial_unique
    {n : ℕ} [NeZero n] (M : DeformationMatrix n) {P Q : Polynomial ℚ}
    (hP : M.IsReducedPrimeFiniteFieldPolynomial P)
    (hQ : M.IsReducedPrimeFiniteFieldPolynomial Q) :
    P = Q := by
  rcases hP with ⟨NP, hP⟩
  rcases hQ with ⟨NQ, hQ⟩
  apply polynomial_eq_of_eventually_prime_natCast_eval_eq
  refine ⟨max NP NQ, ?_⟩
  intro q hq hqPrime
  rw [hP q ((Nat.le_max_left NP NQ).trans hq) hqPrime,
    hQ q ((Nat.le_max_right NP NQ).trans hq) hqPrime]

/-- The cyclic polynomial satisfies the paper-exact prime-only reduced
specification, by weakening its all-natural specification. -/
theorem cyclePolynomial_isReducedPrimeFiniteFieldPolynomial
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) :
    M.IsReducedPrimeFiniteFieldPolynomial (cyclePolynomial M) :=
  isReducedFiniteFieldPolynomial_toPrime M
    (cyclePolynomial_isReducedFiniteFieldPolynomial M hM)

/-- Main-theorem reduced polynomial identity using exactly the
sufficiently-large-prime finite-field hypothesis from the paper. -/
theorem mainTheorem_reduced_of_primeFiniteFieldSpecification
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    {P : Polynomial ℚ} (hP : M.IsReducedPrimeFiniteFieldPolynomial P) :
    P = cyclePolynomial M :=
  isReducedPrimeFiniteFieldPolynomial_unique M hP
    (cyclePolynomial_isReducedPrimeFiniteFieldPolynomial M hM)

/-- Evaluation form of the prime-specification reduced main theorem. -/
theorem mainTheorem_reduced_eval_of_primeFiniteFieldSpecification
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    {P : Polynomial ℚ} (hP : M.IsReducedPrimeFiniteFieldPolynomial P)
    (t : ℚ) :
    Polynomial.eval t P = cycleFormula M t := by
  rw [mainTheorem_reduced_of_primeFiniteFieldSpecification M hM hP,
    eval_cyclePolynomial]

/-- Paper-exact two-sided extension shift for independently supplied base and
extended reduced polynomials satisfying sufficiently-large-prime
specifications. -/
theorem mainTheorem_extension_shift_of_primeFiniteFieldSpecifications
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    (α β : Fin n → ℕ) {P Pext : Polynomial ℚ}
    (hP : M.IsReducedPrimeFiniteFieldPolynomial P)
    (hPext : (M.extend α β).IsReducedPrimeFiniteFieldPolynomial Pext) :
    Pext = translatePolynomial P ((∑ i, α i) + ∑ i, β i) := by
  calc
    Pext = cyclePolynomial (M.extend α β) :=
      mainTheorem_reduced_of_primeFiniteFieldSpecification
        (M.extend α β) (cyclicallyCompatible_extend M hM α β) hPext
    _ = translatePolynomial (cyclePolynomial M)
        ((∑ i, α i) + ∑ i, β i) :=
      cyclePolynomial_extend_shift hn M α β
    _ = translatePolynomial P
        ((∑ i, α i) + ∑ i, β i) := by
      rw [mainTheorem_reduced_of_primeFiniteFieldSpecification M hM hP]

/-- Eventual finite-field specification for a full polynomial.  This is
included only to express the diagonal factor without rebranding the
right-hand-side construction as an independently defined arrangement
characteristic polynomial. -/
def IsFullFiniteFieldPolynomial {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (P : Polynomial ℚ) : Prop :=
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
    Polynomial.eval (q : ℚ) P =
      (q : ℚ) * (M.finiteFieldComplementOrbitCount q : ℚ)

/-- Multiplication by `X` turns a reduced finite-field polynomial into a full
finite-field polynomial. -/
theorem X_mul_isFullFiniteFieldPolynomial_of_reduced
    {n : ℕ} [NeZero n] (M : DeformationMatrix n) {P : Polynomial ℚ}
    (hP : M.IsReducedFiniteFieldPolynomial P) :
    M.IsFullFiniteFieldPolynomial (Polynomial.X * P) := by
  rcases hP with ⟨Q, hP⟩
  refine ⟨Q, ?_⟩
  intro q hq
  rw [Polynomial.eval_mul, Polynomial.eval_X, hP q hq]

/-- The full cyclic candidate `X * cyclePolynomial M` satisfies the stronger
all-natural finite-field specification. -/
theorem X_mul_cyclePolynomial_isFullFiniteFieldPolynomial
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) :
    M.IsFullFiniteFieldPolynomial
      (Polynomial.X * cyclePolynomial M) :=
  X_mul_isFullFiniteFieldPolynomial_of_reduced M
    (cyclePolynomial_isReducedFiniteFieldPolynomial M hM)

/-- The eventual full finite-field specification also determines at most one
rational polynomial. -/
theorem isFullFiniteFieldPolynomial_unique {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) {P Q : Polynomial ℚ}
    (hP : M.IsFullFiniteFieldPolynomial P)
    (hQ : M.IsFullFiniteFieldPolynomial Q) :
    P = Q := by
  rcases hP with ⟨NP, hP⟩
  rcases hQ with ⟨NQ, hQ⟩
  apply polynomial_eq_of_eventually_natCast_eval_eq
  refine ⟨max NP NQ, ?_⟩
  intro q hq
  rw [hP q ((Nat.le_max_left NP NQ).trans hq),
    hQ q ((Nat.le_max_right NP NQ).trans hq)]

/-- Full-versus-reduced diagonal factor: independently supplied full and
reduced finite-field polynomials for the same matrix satisfy `full = X *
reduced`. -/
theorem full_eq_X_mul_reduced_of_finiteFieldSpecifications
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    {full reduced : Polynomial ℚ}
    (hfull : M.IsFullFiniteFieldPolynomial full)
    (hreduced : M.IsReducedFiniteFieldPolynomial reduced) :
    full = Polynomial.X * reduced :=
  isFullFiniteFieldPolynomial_unique M hfull
    (X_mul_isFullFiniteFieldPolynomial_of_reduced M hreduced)

/-- Full main-theorem identity for an independently supplied polynomial with
the full finite-field specification. -/
theorem mainTheorem_full_of_finiteFieldSpecification
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    {P : Polynomial ℚ} (hP : M.IsFullFiniteFieldPolynomial P) :
    P = Polynomial.X * cyclePolynomial M :=
  isFullFiniteFieldPolynomial_unique M hP
    (X_mul_isFullFiniteFieldPolynomial_of_reduced M
      (cyclePolynomial_isReducedFiniteFieldPolynomial M hM))

/-- Evaluation form of the full main theorem. -/
theorem mainTheorem_full_eval_of_finiteFieldSpecification
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    {P : Polynomial ℚ} (hP : M.IsFullFiniteFieldPolynomial P) (t : ℚ) :
    Polynomial.eval t P = t * cycleFormula M t := by
  rw [mainTheorem_full_of_finiteFieldSpecification M hM hP,
    Polynomial.eval_mul, Polynomial.eval_X, eval_cyclePolynomial]

/-- The paper-exact full finite-field specification: agreement with `q` times
the all-pairs-safe placement count is required only at every sufficiently
large prime. -/
def IsFullPrimeFiniteFieldPolynomial {n : ℕ} [NeZero n]
    (M : DeformationMatrix n) (P : Polynomial ℚ) : Prop :=
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → Nat.Prime q →
    Polynomial.eval (q : ℚ) P =
      (q : ℚ) * (M.finiteFieldComplementOrbitCount q : ℚ)

/-- The all-natural full specification implies its paper-exact prime-only
variant. -/
theorem isFullFiniteFieldPolynomial_toPrime
    {n : ℕ} [NeZero n] (M : DeformationMatrix n) {P : Polynomial ℚ}
    (hP : M.IsFullFiniteFieldPolynomial P) :
    M.IsFullPrimeFiniteFieldPolynomial P := by
  rcases hP with ⟨Q, hQ⟩
  exact ⟨Q, fun q hq _ ↦ hQ q hq⟩

/-- Multiplication by `X` turns a prime-specified reduced polynomial into a
prime-specified full polynomial. -/
theorem X_mul_isFullPrimeFiniteFieldPolynomial_of_reduced
    {n : ℕ} [NeZero n] (M : DeformationMatrix n) {P : Polynomial ℚ}
    (hP : M.IsReducedPrimeFiniteFieldPolynomial P) :
    M.IsFullPrimeFiniteFieldPolynomial (Polynomial.X * P) := by
  rcases hP with ⟨Q, hQ⟩
  refine ⟨Q, ?_⟩
  intro q hq hqPrime
  rw [Polynomial.eval_mul, Polynomial.eval_X, hQ q hq hqPrime]

/-- The full cyclic candidate satisfies the paper-exact prime-only
specification, obtained by weakening its all-natural specification. -/
theorem X_mul_cyclePolynomial_isFullPrimeFiniteFieldPolynomial
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) :
    M.IsFullPrimeFiniteFieldPolynomial
      (Polynomial.X * cyclePolynomial M) :=
  isFullFiniteFieldPolynomial_toPrime M
    (X_mul_cyclePolynomial_isFullFiniteFieldPolynomial M hM)

/-- The sufficiently-large-prime full specification determines at most one
rational polynomial. -/
theorem isFullPrimeFiniteFieldPolynomial_unique
    {n : ℕ} [NeZero n] (M : DeformationMatrix n) {P Q : Polynomial ℚ}
    (hP : M.IsFullPrimeFiniteFieldPolynomial P)
    (hQ : M.IsFullPrimeFiniteFieldPolynomial Q) :
    P = Q := by
  rcases hP with ⟨NP, hP⟩
  rcases hQ with ⟨NQ, hQ⟩
  apply polynomial_eq_of_eventually_prime_natCast_eval_eq
  refine ⟨max NP NQ, ?_⟩
  intro q hq hqPrime
  rw [hP q ((Nat.le_max_left NP NQ).trans hq) hqPrime,
    hQ q ((Nat.le_max_right NP NQ).trans hq) hqPrime]

/-- Paper-exact full-versus-reduced diagonal factor for independently
supplied finite-field polynomials. -/
theorem full_eq_X_mul_reduced_of_primeFiniteFieldSpecifications
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    {full reduced : Polynomial ℚ}
    (hfull : M.IsFullPrimeFiniteFieldPolynomial full)
    (hreduced : M.IsReducedPrimeFiniteFieldPolynomial reduced) :
    full = Polynomial.X * reduced :=
  isFullPrimeFiniteFieldPolynomial_unique M hfull
    (X_mul_isFullPrimeFiniteFieldPolynomial_of_reduced M hreduced)

/-- Full main-theorem identity using exactly the paper's
sufficiently-large-prime finite-field hypothesis. -/
theorem mainTheorem_full_of_primeFiniteFieldSpecification
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    {P : Polynomial ℚ} (hP : M.IsFullPrimeFiniteFieldPolynomial P) :
    P = Polynomial.X * cyclePolynomial M :=
  isFullPrimeFiniteFieldPolynomial_unique M hP
    (X_mul_cyclePolynomial_isFullPrimeFiniteFieldPolynomial M hM)

/-- Evaluation form of the prime-specification full main theorem. -/
theorem mainTheorem_full_eval_of_primeFiniteFieldSpecification
    {n : ℕ} [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible)
    {P : Polynomial ℚ} (hP : M.IsFullPrimeFiniteFieldPolynomial P)
    (t : ℚ) :
    Polynomial.eval t P = t * cycleFormula M t := by
  rw [mainTheorem_full_of_primeFiniteFieldSpecification M hM hP,
    Polynomial.eval_mul, Polynomial.eval_X, eval_cyclePolynomial]

end DeformationMatrix

end CyclicBraidArrangement
