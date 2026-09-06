import Mathlib

/-!
# Gaussian coefficients as finite rectangle-partition sums

The proof of Theorem 2.5 uses the standard interpretation of a Gaussian
coefficient as the weight enumerator of partitions in a rectangle.  Defining
the evaluation this way avoids the paper's quotient notation and therefore
works over every commutative semiring, including at `q = 1`.
-/

open scoped BigOperators

namespace LeanCo

/-- A partition with `rows` (zero-padded) parts, each at most `cols`. -/
def RectanglePartition (rows cols : ℕ) :=
  {p : Fin rows → Fin (cols + 1) // Antitone p}

namespace RectanglePartition

instance (rows cols : ℕ) : Finite (RectanglePartition rows cols) := by
  apply Finite.of_injective (f := fun p ↦ p.1)
  exact Subtype.val_injective

noncomputable instance (rows cols : ℕ) : Fintype (RectanglePartition rows cols) :=
  Fintype.ofFinite _

noncomputable instance (rows cols : ℕ) : DecidableEq (RectanglePartition rows cols) :=
  Classical.decEq _

/-- The number of cells of the Ferrers diagram. -/
def weight {rows cols : ℕ} (p : RectanglePartition rows cols) : ℕ :=
  ∑ i, (p.1 i).val

@[simp]
theorem weight_eq {rows cols : ℕ} (p : RectanglePartition rows cols) :
    p.weight = ∑ i, (p.1 i).val := rfl

end RectanglePartition

/--
The value of the Gaussian coefficient `n choose k` at `q`, expressed as the
finite generating function for partitions inside an `(n-k) x k` rectangle.
It is zero when `k > n`.
-/
noncomputable def qBinomialEval {R : Type*} [CommSemiring R]
    (q : R) (n k : ℕ) : R :=
  if _h : k ≤ n then
    ∑ p : RectanglePartition (n - k) k, q ^ p.weight
  else
    0

@[simp]
theorem qBinomialEval_of_lt {R : Type*} [CommSemiring R]
    (q : R) {n k : ℕ} (h : n < k) :
    qBinomialEval q n k = 0 := by
  simp [qBinomialEval, Nat.not_le.mpr h]

theorem qBinomialEval_eq_rectangle {R : Type*} [CommSemiring R]
    (q : R) {n k : ℕ} (h : k ≤ n) :
    qBinomialEval q n k =
      ∑ p : RectanglePartition (n - k) k, q ^ p.weight := by
  simp [qBinomialEval, h]

end LeanCo
