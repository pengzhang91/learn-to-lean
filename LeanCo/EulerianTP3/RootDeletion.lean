import LeanCo.EulerianTP3.Toeplitz

/-!
# Deleting linear factors

This file formalizes the root-deletion identities used in arXiv:2608.29224.
All identities are polynomial equalities over `ℝ`, arranged so the later
coefficient-minor argument can rewrite with them directly.
-/

namespace LeanCo.EulerianTP3

open scoped BigOperators
open Polynomial

private lemma C_two : C (2 : ℝ) = (2 : ℝ[X]) := by
  exact (map_ofNat (C : ℝ →+* ℝ[X]) 2).symm.symm

private noncomputable def factorOn {n : ℕ} (r : Fin n → ℝ)
    (s : Finset (Fin n)) : ℝ[X] :=
  factorPolynomialOn s r

/-- The product obtained by deleting the factor indexed by `i`. -/
noncomputable def deletedFactorPolynomial {n : ℕ} (r : Fin n → ℝ)
    (i : Fin n) : ℝ[X] :=
  factorOn r (Finset.univ.erase i)

/-- The product obtained by deleting the two distinct factors indexed by
`i` and `j`.  The definition is harmless when the indices coincide as well. -/
noncomputable def deletedPairFactorPolynomial {n : ℕ} (r : Fin n → ℝ)
    (i j : Fin n) : ℝ[X] :=
  factorOn r ((Finset.univ.erase i).erase j)

theorem deletedFactorPolynomial_eq_factorPolynomialOn {n : ℕ}
    (r : Fin n → ℝ) (i : Fin n) :
    deletedFactorPolynomial r i =
      factorPolynomialOn (Finset.univ.erase i) r := by
  rfl

theorem deletedPairFactorPolynomial_eq_factorPolynomialOn {n : ℕ}
    (r : Fin n → ℝ) (i j : Fin n) :
    deletedPairFactorPolynomial r i j =
      factorPolynomialOn ((Finset.univ.erase i).erase j) r := by
  rfl

/-- The paper's first root-deletion polynomial. -/
noncomputable def G1 {n : ℕ} (r : Fin n → ℝ) : ℝ[X] :=
  ∑ i, C (1 + r i) * deletedFactorPolynomial r i

/-- The paper's second root-deletion polynomial.  An unordered pair sum is
encoded as one half of the ordered sum over distinct pairs. -/
noncomputable def G2 {n : ℕ} (r : Fin n → ℝ) : ℝ[X] :=
  C (1 / 2 : ℝ) *
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      C (1 + r i) *
        (C (1 + r j) * deletedPairFactorPolynomial r i j)

private lemma factorOn_eq_linear_mul_erase {n : ℕ} (r : Fin n → ℝ)
    (s : Finset (Fin n)) {i : Fin n} (hi : i ∈ s) :
    factorOn r s =
      (1 + C (r i) * X) * factorOn r (s.erase i) := by
  classical
  simpa [factorOn, factorPolynomialOn] using
    (Finset.mul_prod_erase s (fun j => (1 + C (r j) * X)) hi).symm

/-- Deleting two factors is symmetric in their indices. -/
theorem deletedPairFactorPolynomial_comm {n : ℕ} (r : Fin n → ℝ)
    (i j : Fin n) :
    deletedPairFactorPolynomial r i j =
      deletedPairFactorPolynomial r j i := by
  classical
  rw [deletedPairFactorPolynomial_eq_factorPolynomialOn,
    deletedPairFactorPolynomial_eq_factorPolynomialOn,
    Finset.erase_right_comm]

/-- Reconstruct the full product from a single deleted factor. -/
theorem factorPolynomial_eq_linear_mul_deletedFactor {n : ℕ}
    (r : Fin n → ℝ) (i : Fin n) :
    factorPolynomial r =
      (1 + C (r i) * X) * deletedFactorPolynomial r i := by
  rw [factorPolynomial_eq_factorPolynomialOn_univ]
  simpa [factorOn, deletedFactorPolynomial] using
    factorOn_eq_linear_mul_erase r Finset.univ (Finset.mem_univ i)

/-- Reconstruct a singly deleted product from a doubly deleted one. -/
theorem deletedFactorPolynomial_eq_linear_mul_deletedPair {n : ℕ}
    (r : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    deletedFactorPolynomial r i =
      (1 + C (r j) * X) * deletedPairFactorPolynomial r i j := by
  have hj : j ∈ Finset.univ.erase i := by simp [hij.symm]
  simpa [factorOn, deletedFactorPolynomial, deletedPairFactorPolynomial] using
    factorOn_eq_linear_mul_erase r (Finset.univ.erase i) hj

/-- Reconstruct the full product from two distinct deleted factors. -/
theorem factorPolynomial_eq_linear_mul_linear_mul_deletedPair {n : ℕ}
    (r : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    factorPolynomial r =
      (1 + C (r i) * X) * (1 + C (r j) * X) *
        deletedPairFactorPolynomial r i j := by
  rw [factorPolynomial_eq_linear_mul_deletedFactor r i,
    deletedFactorPolynomial_eq_linear_mul_deletedPair r i j hij]
  ring

private lemma factorOn_derivative {n : ℕ} (r : Fin n → ℝ)
    (s : Finset (Fin n)) :
    (factorOn r s).derivative =
      ∑ i ∈ s, C (r i) * factorOn r (s.erase i) := by
  classical
  unfold factorOn factorPolynomialOn
  rw [derivative_prod_finset]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [derivative_add, derivative_one, derivative_mul, derivative_C,
    derivative_X, zero_add, zero_mul, one_mul, mul_one, add_zero]
  ring

/-- Product-rule expansion of the derivative of `factorPolynomial`. -/
theorem factorPolynomial_derivative_eq_sum_deleted {n : ℕ}
    (r : Fin n → ℝ) :
    (factorPolynomial r).derivative =
      ∑ i, C (r i) * deletedFactorPolynomial r i := by
  classical
  rw [factorPolynomial_eq_factorPolynomialOn_univ]
  simpa [factorOn, deletedFactorPolynomial] using factorOn_derivative r Finset.univ

/-- Product-rule expansion after one specified factor has been deleted. -/
theorem deletedFactorPolynomial_derivative_eq_sum_deletedPair {n : ℕ}
    (r : Fin n → ℝ) (i : Fin n) :
    (deletedFactorPolynomial r i).derivative =
      ∑ j ∈ Finset.univ.erase i,
        C (r j) * deletedPairFactorPolynomial r i j := by
  classical
  simpa [deletedFactorPolynomial, deletedPairFactorPolynomial] using
    factorOn_derivative r (Finset.univ.erase i)

private lemma weightedDeletion_sum {n : ℕ} (r : Fin n → ℝ)
    (s : Finset (Fin n)) :
    (∑ i ∈ s, C (1 + r i) * factorOn r (s.erase i)) =
      (s.card : ℝ[X]) * factorOn r s +
        (1 - X) * (factorOn r s).derivative := by
  classical
  have hterm : ∀ i ∈ s,
      C (1 + r i) * factorOn r (s.erase i) =
        factorOn r s +
          (1 - X) * (C (r i) * factorOn r (s.erase i)) := by
    intro i hi
    rw [factorOn_eq_linear_mul_erase r s hi]
    simp only [map_add, map_one]
    ring
  calc
    (∑ i ∈ s, C (1 + r i) * factorOn r (s.erase i)) =
        ∑ i ∈ s, (factorOn r s +
          (1 - X) * (C (r i) * factorOn r (s.erase i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i hi
    _ = (s.card : ℝ[X]) * factorOn r s +
        (1 - X) * (∑ i ∈ s, C (r i) * factorOn r (s.erase i)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp
    _ = (s.card : ℝ[X]) * factorOn r s +
        (1 - X) * (factorOn r s).derivative := by
          rw [factorOn_derivative]

/-- The first root-deletion identity (Lemma 2.6 at `j = 0`). -/
theorem G1_eq_nat_mul_factorPolynomial_add_derivative {n : ℕ}
    (r : Fin n → ℝ) :
    G1 r = C (n : ℝ) * factorPolynomial r +
      (1 - X) * (factorPolynomial r).derivative := by
  classical
  rw [factorPolynomial_eq_factorPolynomialOn_univ]
  simpa [G1, deletedFactorPolynomial, factorOn] using
    weightedDeletion_sum r Finset.univ

private lemma G1_derivative_eq_sum {n : ℕ} (r : Fin n → ℝ) :
    (G1 r).derivative =
      ∑ i, C (1 + r i) * (deletedFactorPolynomial r i).derivative := by
  classical
  simp [G1]

private noncomputable def orderedG2Sum {n : ℕ} (r : Fin n → ℝ) : ℝ[X] :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    C (1 + r i) *
      (C (1 + r j) * deletedPairFactorPolynomial r i j)

private lemma G1_recurrence_rhs_eq_orderedG2Sum {n : ℕ}
    (r : Fin n → ℝ) :
    C ((n - 1 : ℕ) : ℝ) * G1 r + (1 - X) * (G1 r).derivative =
      orderedG2Sum r := by
  classical
  rw [G1_derivative_eq_sum, G1, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  unfold orderedG2Sum
  apply Finset.sum_congr rfl
  intro i hi
  have hdelete := weightedDeletion_sum r (Finset.univ.erase i)
  have hcard : (Finset.univ.erase i).card = n - 1 := by simp
  rw [hcard] at hdelete
  have hdelete' :
      (∑ j ∈ Finset.univ.erase i,
        C (1 + r j) * deletedPairFactorPolynomial r i j) =
        C ((n - 1 : ℕ) : ℝ) * deletedFactorPolynomial r i +
          (1 - X) * (deletedFactorPolynomial r i).derivative := by
    simpa [deletedFactorPolynomial, deletedPairFactorPolynomial, factorOn] using hdelete
  change
    C ((n - 1 : ℕ) : ℝ) *
          (C (1 + r i) * deletedFactorPolynomial r i) +
        (1 - X) *
          (C (1 + r i) * (deletedFactorPolynomial r i).derivative) = _
  calc
    _ = C (1 + r i) *
        (C ((n - 1 : ℕ) : ℝ) * deletedFactorPolynomial r i +
          (1 - X) * (deletedFactorPolynomial r i).derivative) := by ring
    _ = C (1 + r i) *
        (∑ j ∈ Finset.univ.erase i,
          C (1 + r j) * deletedPairFactorPolynomial r i j) := by
            rw [hdelete']
    _ = ∑ j ∈ Finset.univ.erase i,
        C (1 + r i) *
          (C (1 + r j) * deletedPairFactorPolynomial r i j) := by
            rw [Finset.mul_sum]

/-- The second root-deletion identity (Lemma 2.6 at `j = 1`). -/
theorem two_mul_G2_eq_nat_sub_one_mul_G1_add_derivative {n : ℕ}
    (r : Fin n → ℝ) :
    C (2 : ℝ) * G2 r =
      C ((n - 1 : ℕ) : ℝ) * G1 r +
        (1 - X) * (G1 r).derivative := by
  rw [G2]
  change C (2 : ℝ) * (C (1 / 2 : ℝ) * orderedG2Sum r) = _
  rw [G1_recurrence_rhs_eq_orderedG2Sum]
  rw [← mul_assoc, ← C_mul]
  norm_num

/-! ## The ordinary Eulerian `Q` and `R` formulas -/

/-- If `P` is the factor polynomial, one ordinary Eulerian differential
step is `(1 + X) P + X G1`.  This is equation (3.3) of the paper in a form
that can be used directly with `rw`. -/
theorem ordinaryEulerian_Q_formula {n : ℕ} (r : Fin n → ℝ) :
    (1 + C (n + 1 : ℝ) * X) * factorPolynomial r +
        X * (1 - X) * (factorPolynomial r).derivative =
      (1 + X) * factorPolynomial r + X * G1 r := by
  rw [G1_eq_nat_mul_factorPolynomial_add_derivative]
  have hn : C (n + 1 : ℝ) = C (n : ℝ) + 1 := by
    norm_num [Nat.cast_add]
  rw [hn]
  ring

/-- Given the `Q` formula, the next ordinary Eulerian differential step is
the paper's expression in `P`, `G1`, and `G2` (equation (3.4)). -/
theorem ordinaryEulerian_R_formula {n : ℕ} (r : Fin n → ℝ) (Q : ℝ[X])
    (hQ : Q = (1 + X) * factorPolynomial r + X * G1 r) :
    (1 + C (n + 2 : ℝ) * X) * Q + X * (1 - X) * Q.derivative =
      (1 + 4 * X + X ^ 2) * factorPolynomial r +
        3 * X * (1 + X) * G1 r + 2 * X ^ 2 * G2 r := by
  subst Q
  cases n with
  | zero =>
      simp [factorPolynomial, G1, G2, orderedG2Sum, deletedFactorPolynomial,
        deletedPairFactorPolynomial, factorOn]
      rw [C_two]
      ring
  | succ n =>
      have hPder :
          (1 - X) * (factorPolynomial r).derivative =
            G1 r - C (n + 1 : ℝ) * factorPolynomial r := by
        rw [G1_eq_nat_mul_factorPolynomial_add_derivative]
        norm_num [Nat.cast_add]
      have hGder :
          (1 - X) * (G1 r).derivative =
            C (2 : ℝ) * G2 r - C (n : ℝ) * G1 r := by
        rw [two_mul_G2_eq_nat_sub_one_mul_G1_add_derivative]
        simp only [Nat.add_sub_cancel]
        ring
      have hQder :
          ((1 + X) * factorPolynomial r + X * G1 r).derivative =
            factorPolynomial r + (1 + X) * (factorPolynomial r).derivative +
              G1 r + X * (G1 r).derivative := by
        simp
        ring
      rw [hQder]
      have hn : C (((n + 1 : ℕ) : ℝ) + 2) = C (n + 1 : ℝ) + 2 := by
        rw [map_add, C_two]
        norm_num [Nat.cast_add]
      rw [hn]
      have hn1 : C (n + 1 : ℝ) = C (n : ℝ) + 1 := by
        norm_num [Nat.cast_add]
      rw [hn1]
      rw [hn1] at hPder
      rw [C_two] at hGder
      linear_combination X * (1 + X) * hPder + X ^ 2 * hGder

end LeanCo.EulerianTP3
