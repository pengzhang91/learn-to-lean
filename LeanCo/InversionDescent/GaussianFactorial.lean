import LeanCo.InversionDescent.Gaussian
import LeanCo.InversionDescent.QProduct

/-!
# Gaussian coefficients and q-factorials

This file supplies a division-free bridge between the rectangle-partition
definition of `qBinomialEval` and the usual product of q-integers.
-/

open scoped BigOperators

namespace LeanCo

/-- The polynomial q-integer `[n]_q = 1 + q + ... + q^(n-1)`. -/
def qIntegerGF {R : Type*} [CommSemiring R] (q : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range n, q ^ i

@[simp] theorem qIntegerGF_zero {R : Type*} [CommSemiring R] (q : R) :
    qIntegerGF q 0 = 0 := by simp [qIntegerGF]

theorem qIntegerGF_succ {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    qIntegerGF q (n + 1) = qIntegerGF q n + q ^ n := by
  simp [qIntegerGF, Finset.sum_range_succ]

/-- Splitting a geometric sum after `a` terms. -/
theorem qIntegerGF_add {R : Type*} [CommSemiring R] (q : R) (a b : ℕ) :
    qIntegerGF q (a + b) = qIntegerGF q a + q ^ a * qIntegerGF q b := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, qIntegerGF_succ, ih, qIntegerGF_succ]
      simp only [pow_add]
      ring

/-- The product `[n]_q! = [1]_q ... [n]_q`. -/
def qFactorialGF {R : Type*} [CommSemiring R] (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => qFactorialGF q n * qIntegerGF q (n + 1)

@[simp] theorem qFactorialGF_zero {R : Type*} [CommSemiring R] (q : R) :
    qFactorialGF q 0 = 1 := rfl

@[simp] theorem qFactorialGF_succ {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    qFactorialGF q (n + 1) = qFactorialGF q n * qIntegerGF q (n + 1) := rfl

namespace RectanglePartition

/-- Forget the first row of a rectangle partition. -/
def tail {rows cols : ℕ} (p : RectanglePartition (rows + 1) cols) :
    RectanglePartition rows cols :=
  ⟨fun i ↦ p.1 i.succ, fun _ _ h ↦ p.2 (Fin.succ_le_succ_iff.mpr h)⟩

/-- Regard a partition in a narrower rectangle as one in a wider rectangle. -/
def widen {rows cols : ℕ} (p : RectanglePartition rows cols) :
    RectanglePartition rows (cols + 1) :=
  ⟨fun i ↦ (p.1 i).castSucc, fun _ _ h ↦ by
    simpa using p.2 h⟩

/-- Lower the column bound when every part is strictly below the old bound. -/
def narrow {rows cols : ℕ} (p : RectanglePartition rows (cols + 1))
    (h : ∀ i, (p.1 i).val < cols + 1) : RectanglePartition rows cols :=
  ⟨fun i ↦ ⟨(p.1 i).val, h i⟩, fun _ _ hij ↦ by
    simpa using p.2 hij⟩

/-- Add a full first row. -/
def prependFull {rows cols : ℕ} (p : RectanglePartition rows (cols + 1)) :
    RectanglePartition (rows + 1) (cols + 1) := by
  refine ⟨Fin.cons (Fin.last (cols + 1)) p.1, ?_⟩
  intro i j hij
  obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
  · exact Fin.le_last _
  · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
    · simp at hij
    · simpa using p.2 (by simpa using hij)

/-- Pascal decomposition: either the first row is not full, or remove a full first row. -/
noncomputable def pascalEquiv (rows cols : ℕ) :
    RectanglePartition (rows + 1) (cols + 1) ≃
      RectanglePartition (rows + 1) cols ⊕ RectanglePartition rows (cols + 1) where
  toFun p :=
    if h : p.1 0 = Fin.last (cols + 1) then
      Sum.inr p.tail
    else
      Sum.inl (p.narrow (by
        intro i
        have hi : (p.1 i).val ≤ (p.1 0).val := p.2 (Fin.zero_le i)
        have hne : (p.1 0).val ≠ cols + 1 := by
          intro he
          apply h
          apply Fin.ext
          simpa using he
        omega))
  invFun s := match s with
    | Sum.inl p => p.widen
    | Sum.inr p => p.prependFull
  left_inv p := by
    dsimp
    split_ifs with h
    · apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa [prependFull] using h.symm
      · simp [prependFull, tail]
    · apply Subtype.ext
      funext i
      simp [widen, narrow]
  right_inv s := by
    cases s with
    | inl p =>
        simp only
        have hnot : (widen p).1 0 ≠ Fin.last (cols + 1) := by
          intro h
          have hv := congrArg Fin.val h
          have hp := (p.1 0).isLt
          simp [widen] at hv
          omega
        simp [hnot]
        apply Subtype.ext
        funext i
        simp [widen, narrow]
    | inr p =>
        simp [prependFull, tail]

@[simp] theorem weight_widen {rows cols : ℕ} (p : RectanglePartition rows cols) :
    (widen p).weight = p.weight := by
  simp [weight, widen]

@[simp] theorem weight_narrow {rows cols : ℕ}
    (p : RectanglePartition rows (cols + 1))
    (h : ∀ i, (p.1 i).val < cols + 1) :
    (narrow p h).weight = p.weight := by
  simp [weight, narrow]

@[simp] theorem weight_prependFull {rows cols : ℕ}
    (p : RectanglePartition rows (cols + 1)) :
    (prependFull p).weight = cols + 1 + p.weight := by
  simp [weight, prependFull, Fin.sum_univ_succ]

/-- The partition enumerators satisfy the Gaussian Pascal recurrence. -/
theorem sum_pascal {R : Type*} [CommSemiring R] (q : R) (rows cols : ℕ) :
    (∑ p : RectanglePartition (rows + 1) (cols + 1), q ^ p.weight) =
      (∑ p : RectanglePartition (rows + 1) cols, q ^ p.weight) +
        q ^ (cols + 1) * (∑ p : RectanglePartition rows (cols + 1), q ^ p.weight) := by
  rw [Fintype.sum_equiv (pascalEquiv rows cols)
    (fun p : RectanglePartition (rows + 1) (cols + 1) ↦ q ^ p.weight)
    (fun s ↦ q ^ ((pascalEquiv rows cols).symm s).weight) (by simp)]
  simp only [Fintype.sum_sum_type]
  congr 1
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro p
  change q ^ (prependFull p).weight = q ^ (cols + 1) * q ^ p.weight
  rw [weight_prependFull, pow_add]

end RectanglePartition

@[simp] theorem qBinomialEval_zero_right {R : Type*} [CommSemiring R]
    (q : R) (n : ℕ) : qBinomialEval q n 0 = 1 := by
  rw [qBinomialEval_eq_rectangle q (Nat.zero_le n)]
  letI : Unique (RectanglePartition n 0) :=
    { default := ⟨fun _ ↦ 0, antitone_const⟩
      uniq := fun p ↦ by
        apply Subtype.ext
        funext i
        exact Fin.eq_zero _ }
  rw [Fintype.sum_unique]
  simp [RectanglePartition.weight]

@[simp] theorem qBinomialEval_self {R : Type*} [CommSemiring R]
    (q : R) (n : ℕ) : qBinomialEval q n n = 1 := by
  have hs : n - n = 0 := Nat.sub_self n
  rw [qBinomialEval_eq_rectangle q le_rfl]
  rw [hs]
  letI : Unique (RectanglePartition 0 n) :=
    { default := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
      uniq := fun p ↦ by
        apply Subtype.ext
        funext i
        exact Fin.elim0 i }
  rw [Fintype.sum_unique]
  have hw (p : RectanglePartition 0 n) : p.weight = 0 := by
    simp [RectanglePartition.weight]
  rw [hw]
  simp

/-- Pascal recurrence, in rectangle coordinates. -/
theorem qBinomialEval_pascal {R : Type*} [CommSemiring R]
    (q : R) (rows cols : ℕ) :
    qBinomialEval q (rows + cols + 2) (cols + 1) =
      qBinomialEval q (rows + cols + 1) cols +
        q ^ (cols + 1) * qBinomialEval q (rows + cols + 1) (cols + 1) := by
  rw [qBinomialEval_eq_rectangle q (by omega),
    qBinomialEval_eq_rectangle q (by omega),
    qBinomialEval_eq_rectangle q (by omega)]
  have h₀ : rows + cols + 2 - (cols + 1) = rows + 1 := by omega
  have h₁ : rows + cols + 1 - cols = rows + 1 := by omega
  have h₂ : rows + cols + 1 - (cols + 1) = rows := by omega
  rw [h₀, h₁, h₂]
  exact RectanglePartition.sum_pascal q rows cols

/-- Pascal recurrence in the usual `(n,k)` coordinates. -/
theorem qBinomialEval_succ_succ {R : Type*} [CommSemiring R]
    (q : R) {n k : ℕ} (h : k < n) :
    qBinomialEval q (n + 1) (k + 1) =
      qBinomialEval q n k + q ^ (k + 1) * qBinomialEval q n (k + 1) := by
  have h₀ : n - k - 1 + k + 2 = n + 1 := by omega
  have h₁ : n - k - 1 + k + 1 = n := by omega
  simpa only [h₀, h₁] using qBinomialEval_pascal q (n - k - 1) k

/--
Division-free Gaussian factorial identity.  This is the cross-multiplied
form of `[n choose k]_q = [n]_q! / ([k]_q! [n-k]_q!)`; hence it remains valid
in every commutative semiring, without invertibility assumptions.
-/
theorem qBinomialEval_mul_factorials {R : Type*} [CommSemiring R]
    (q : R) {n k : ℕ} (hkn : k ≤ n) :
    qBinomialEval q n k * qFactorialGF q k * qFactorialGF q (n - k) =
      qFactorialGF q n := by
  induction n generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      rcases hkn.eq_or_lt with rfl | hlt
      · simp
      · cases k with
        | zero => simp
        | succ k =>
            have hk : k < n := by omega
            have h₀ := ih (k := k) (Nat.le_of_lt hk)
            have h₁ := ih (k := k + 1) (by omega)
            have hb : n - k = (n - (k + 1)) + 1 := by omega
            have h₀' :
                qBinomialEval q n k * qFactorialGF q k *
                    (qFactorialGF q (n - (k + 1)) * qIntegerGF q (n - k)) =
                  qFactorialGF q n := by
              simpa [hb] using h₀
            rw [qBinomialEval_succ_succ q hk, Nat.succ_sub_succ_eq_sub]
            calc
              (qBinomialEval q n k + q ^ (k + 1) * qBinomialEval q n (k + 1)) *
                    qFactorialGF q (k + 1) * qFactorialGF q (n - k) =
                  (qBinomialEval q n k * qFactorialGF q k *
                      (qFactorialGF q (n - (k + 1)) * qIntegerGF q (n - k))) *
                        qIntegerGF q (k + 1) +
                    q ^ (k + 1) *
                      (qBinomialEval q n (k + 1) * qFactorialGF q (k + 1) *
                        qFactorialGF q (n - (k + 1))) * qIntegerGF q (n - k) := by
                    rw [qFactorialGF_succ, hb, qFactorialGF_succ]
                    ring
              _ = qFactorialGF q n * qIntegerGF q (k + 1) +
                    q ^ (k + 1) * qFactorialGF q n * qIntegerGF q (n - k) := by
                    rw [h₀', h₁]
              _ = qFactorialGF q n *
                    (qIntegerGF q (k + 1) + q ^ (k + 1) * qIntegerGF q (n - k)) := by
                    ring
              _ = qFactorialGF q n * qIntegerGF q (n + 1) := by
                    rw [← qIntegerGF_add]
                    congr 2
                    omega
              _ = qFactorialGF q (n + 1) := rfl

/-- Our geometric-sum q-integer is the one used by the power-series model. -/
theorem qIntegerGF_eq_qInteger {R : Type*} [CommSemiring R]
    (q : R) (n : ℕ) :
    qIntegerGF q n = QExponential.qInteger q n := rfl

/-- The factorial in this file agrees with `QProduct.qFactorial`. -/
theorem qFactorialGF_eq_QProduct_qFactorial {R : Type*} [CommSemiring R]
    (q : R) (n : ℕ) :
    qFactorialGF q n = QProduct.qFactorial q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [qFactorialGF_succ, QProduct.qFactorial_succ, ih,
        qIntegerGF_eq_qInteger]

end LeanCo
