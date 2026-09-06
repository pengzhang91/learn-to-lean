import LeanCo.InversionDescent.LehmerEquiv
import LeanCo.InversionDescent.Recurrence
import LeanCo.InversionDescent.QDifference
import LeanCo.InversionDescent.GeneratingFunction
import LeanCo.InversionDescent.SetPartition
import LeanCo.InversionDescent.RestrictedGrowth
import LeanCo.InversionDescent.QProduct
import LeanCo.InversionDescent.GaussianFactorial

/-!
# End-to-end statements for Pan's inversion--descent enumerator

The other files prove the individual combinatorial and algebraic steps.  This
file closes the loop by defining the enumerator on the literal permutation
avoidance class from Definition 1.1 and transporting it, with both statistics,
through the reverse Lehmer code.  Consequently the recurrence and the
q-difference identities below are statements about the paper's actual
permutations, rather than about an auxiliary recursively defined type.
-/

open scoped BigOperators PowerSeries.WithPiTopology
open Filter Topology

namespace LeanCo

/-! ## The literal permutation enumerator -/

/-- The paper's genuine `32-1`-avoiding permutations. -/
abbrev AvoidingPermutations (n : ℕ) :=
  {σ : Equiv.Perm (Fin n) // Permutation.Avoids32_1 σ}

/-- The inversion--descent enumerator from Definition 1.1, restricted to the
literal vincular-pattern avoidance class. -/
noncomputable def permutationEnumerator {R : Type*} [CommSemiring R]
    (q t : R) (n : ℕ) : R :=
  ∑ σ : AvoidingPermutations n,
    q ^ Permutation.inversionNumber σ.1 * t ^ Permutation.descentNumber σ.1

/-- Proposition 2.3 and Proposition 2.4, bundled as an equivalence from the
literal permutation avoidance class to the rise-from-zero presentation used
by the last-zero recurrence. -/
noncomputable def avoidingPermutationRestrictedEquiv (n : ℕ) :
    AvoidingPermutations n ≃ RestrictedInversionSequences n :=
  (Permutation.avoidingReverseLehmerEquiv n).trans
    (restrictedAvoidingEquiv n).symm

@[simp]
theorem avoidingPermutationRestrictedEquiv_apply_val
    (n : ℕ) (σ : AvoidingPermutations n) :
    (avoidingPermutationRestrictedEquiv n σ).1.1 =
      Permutation.reverseLehmerCode σ.1 :=
  rfl

theorem avoidingPermutationRestrictedEquiv_preserves_inversionWeight
    {n : ℕ} (σ : AvoidingPermutations n) :
    Permutation.inversionNumber σ.1 =
      sequenceInversionWeight (avoidingPermutationRestrictedEquiv n σ).1 := by
  simpa [Permutation.inversionSequenceWeight, sequenceInversionWeight] using
    Permutation.avoidingReverseLehmerEquiv_preserves_inversionNumber σ

/-! The two files use equivalent, but differently indexed, presentations of
the adjacent-rise statistic.  The following finite-set identity is the exact
bridge between them. -/

theorem riseSet_eq_map_risePositions {n : ℕ}
    (a : Permutation.InversionSequences (n + 1)) :
    riseSet a.1 =
      (Permutation.inversionSequenceRisePositions a).map Fin.castSuccEmb := by
  classical
  ext i
  constructor
  · intro hi
    rw [riseSet, Finset.mem_filter] at hi
    obtain ⟨_, j, hij, hrise⟩ := hi
    have hin : i.1 < n := by
      change j.1 = i.1 + 1 at hij
      omega
    let k : Fin n := ⟨i.1, hin⟩
    have hki : k.castSucc = i := Fin.ext rfl
    have hkj : k.succ = j := by
      apply Fin.ext
      change i.1 + 1 = j.1
      exact hij.symm
    rw [Finset.mem_map]
    refine ⟨k, ?_, ?_⟩
    · rw [Permutation.mem_inversionSequenceRisePositions]
      simpa [hki, hkj] using hrise
    · exact hki
  · intro hi
    rw [Finset.mem_map] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    rw [Permutation.mem_inversionSequenceRisePositions] at hk
    rw [riseSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, k.succ, ?_, hk⟩
    rfl

theorem sequenceDescentWeight_eq_riseNumber {n : ℕ}
    (a : Permutation.InversionSequences (n + 1)) :
    sequenceDescentWeight a =
      Permutation.inversionSequenceRiseNumber a := by
  rw [sequenceDescentWeight, riseSet_eq_map_risePositions,
    Permutation.inversionSequenceRiseNumber, Finset.card_map]

theorem avoidingPermutationRestrictedEquiv_preserves_descentWeight
    {n : ℕ} (σ : AvoidingPermutations n) :
    Permutation.descentNumber σ.1 =
      sequenceDescentWeight (avoidingPermutationRestrictedEquiv n σ).1 := by
  cases n with
  | zero =>
      simp [Permutation.descentNumber, Permutation.descentSet,
        sequenceDescentWeight, riseSet]
  | succ n =>
      rw [sequenceDescentWeight_eq_riseNumber]
      exact Permutation.avoidingReverseLehmerEquiv_preserves_descentNumber σ

/-- Transport of the literal permutation enumerator to the literal avoiding
inversion-sequence sum. -/
theorem permutationEnumerator_eq_avoidingSequenceEnumerator
    {R : Type*} [CommSemiring R] (q t : R) (n : ℕ) :
    permutationEnumerator q t n = avoidingSequenceEnumerator q t n := by
  classical
  rw [permutationEnumerator, avoidingSequenceEnumerator,
    ← (avoidingPermutationRestrictedEquiv n).sum_comp]
  apply Fintype.sum_congr
  intro σ
  rw [
    avoidingPermutationRestrictedEquiv_preserves_inversionWeight σ,
    avoidingPermutationRestrictedEquiv_preserves_descentWeight σ]

/-- The full reverse-Lehmer/last-zero transport: the enumerator defined on
literal avoiding permutations is the recursively decomposed enumerator of
Theorem 2.5. -/
theorem permutationEnumerator_eq_inversionDescentEnumerator
    {R : Type*} [CommSemiring R] (q t : R) (n : ℕ) :
    permutationEnumerator q t n = inversionDescentEnumerator q t n := by
  rw [permutationEnumerator_eq_avoidingSequenceEnumerator,
    avoidingSequenceEnumerator_eq_inversionDescentEnumerator]

@[simp]
theorem permutationEnumerator_zero
    {R : Type*} [CommSemiring R] (q t : R) :
    permutationEnumerator q t 0 = 1 := by
  rw [permutationEnumerator_eq_inversionDescentEnumerator,
    inversionDescentEnumerator_zero]

/-- Theorem 2.5 directly on the paper's literal permutation enumerator, in
the convenient successor indexing. -/
theorem permutationEnumerator_succ
    {R : Type*} [CommSemiring R] (q t : R) (n : ℕ) :
    permutationEnumerator q t (n + 1) =
      permutationEnumerator q t n +
        ∑ k : Fin n, (t * q ^ (n - k.1)) *
          qBinomialEval q n k.1 * permutationEnumerator q t k.1 := by
  simpa only [permutationEnumerator_eq_inversionDescentEnumerator] using
    inversionDescentEnumerator_succ q t n

/-- The paper's original `n ≥ 1` indexing of Theorem 2.5, now with `I_n`
definitionally equal to a sum over literal avoiding permutations. -/
theorem theorem_2_5_permutations
    {R : Type*} [CommSemiring R] (q t : R) {n : ℕ} (hn : 1 ≤ n) :
    permutationEnumerator q t n =
      permutationEnumerator q t (n - 1) +
        ∑ k : Fin (n - 1), (t * q ^ (n - k.1 - 1)) *
          qBinomialEval q (n - 1) k.1 * permutationEnumerator q t k.1 := by
  simpa only [permutationEnumerator_eq_inversionDescentEnumerator] using
    theorem_2_5 q t hn

/-! ## Equations (5) and (6) for the literal permutation enumerator -/

/-- Theorem 2.5 in the `Finset.range` form consumed by the q-exponential
Cauchy product. -/
theorem permutationEnumerator_succ_range
    {R : Type*} [CommSemiring R] (q t : R) (n : ℕ) :
    permutationEnumerator q t (n + 1) =
      permutationEnumerator q t n +
        t * ∑ k ∈ Finset.range n,
          qBinomialEval q n k * permutationEnumerator q t k * q ^ (n - k) := by
  calc
    permutationEnumerator q t (n + 1) =
        permutationEnumerator q t n +
          ∑ k : Fin n, (t * q ^ (n - k.1)) *
            qBinomialEval q n k.1 * permutationEnumerator q t k.1 :=
      permutationEnumerator_succ q t n
    _ = permutationEnumerator q t n +
        t * ∑ k ∈ Finset.range n,
          qBinomialEval q n k * permutationEnumerator q t k * q ^ (n - k) := by
      congr 1
      rw [show
        (∑ k : Fin n, (t * q ^ (n - k.1)) *
          qBinomialEval q n k.1 * permutationEnumerator q t k.1) =
        ∑ k ∈ Finset.range n, (t * q ^ (n - k)) *
          qBinomialEval q n k * permutationEnumerator q t k by
            simpa using Fin.sum_univ_eq_sum_range
              (fun k : ℕ ↦ ((t * q ^ (n - k)) *
                qBinomialEval q n k * permutationEnumerator q t k : R)) n]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ac_rfl

/-- Equation (5), coefficientwise in the q-divided-power basis, for the
genuine permutation enumerator. -/
theorem equation_5_permutations
    {R : Type*} [CommSemiring R] (q t : R) :
    QExponential.qDerivative (permutationEnumerator q t) =
      fun n ↦ permutationEnumerator q t n +
        t * QExponential.qCauchy q (permutationEnumerator q t)
          (QExponential.scaledQExpTail q) n := by
  apply QExponential.theorem_3_1_coefficient_equation
  exact permutationEnumerator_succ_range q t

/-- Equation (6) in its division-free form.  In particular this identity is
valid at `q = 1`; no illicit cancellation by `(q-1)x` is used. -/
theorem equation_6_permutations_no_division
    {R : Type*} [CommRing R] (q t : R) :
    QExponential.qRescale q (permutationEnumerator q t) = fun n ↦
      permutationEnumerator q t n + (q - 1) * QExponential.qMulX q
        (fun m ↦ permutationEnumerator q t m +
          t * QExponential.qCauchy q (permutationEnumerator q t)
            (QExponential.scaledQExpTail q) m) n := by
  apply QExponential.equation_6_no_division
  exact equation_5_permutations q t

/-! ## Theorem 3.1 as an actual formal-power-series product -/

/-- Interpret q-divided-power coefficients as an ordinary formal power
series.  The inverse is totalized by the field; results identifying Cauchy
products therefore explicitly assume that every q-factorial is nonzero. -/
noncomputable def qDividedPowerSeries
    {K : Type*} [Field K] (q : K) (f : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n ↦ f n * (QProduct.qFactorial q n)⁻¹

@[simp]
theorem coeff_qDividedPowerSeries
    {K : Type*} [Field K] (q : K) (f : ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (qDividedPowerSeries q f) =
      f n * (QProduct.qFactorial q n)⁻¹ := by
  simp [qDividedPowerSeries]

/-- Gaussian coefficients clear the three q-factorials. -/
theorem qBinomialEval_mul_qFactorials
    {K : Type*} [Field K] (q : K) {n k : ℕ} (hkn : k ≤ n) :
    qBinomialEval q n k * QProduct.qFactorial q k *
        QProduct.qFactorial q (n - k) =
      QProduct.qFactorial q n := by
  rw [← qFactorialGF_eq_QProduct_qFactorial q k,
    ← qFactorialGF_eq_QProduct_qFactorial q (n - k),
    ← qFactorialGF_eq_QProduct_qFactorial q n]
  exact qBinomialEval_mul_factorials q hkn

theorem qDividedPowerSeries_add_const_mul
    {K : Type*} [Field K] (q a : K) (f g : ℕ → K) :
    qDividedPowerSeries q (fun n ↦ f n + a * g n) =
      qDividedPowerSeries q f +
        PowerSeries.C a * qDividedPowerSeries q g := by
  ext n
  simp only [coeff_qDividedPowerSeries, map_add, PowerSeries.coeff_C_mul]
  ring

theorem qDividedPowerSeries_qRescale
    {K : Type*} [Field K] (q : K) (f : ℕ → K) :
    qDividedPowerSeries q (QExponential.qRescale q f) =
      PowerSeries.rescale q (qDividedPowerSeries q f) := by
  ext n
  simp [QExponential.qRescale]
  ac_rfl

/-- Multiplication in the q-divided-power basis becomes ordinary formal
power-series multiplication. -/
theorem qDividedPowerSeries_qCauchy
    {K : Type*} [Field K] (q : K)
    (hfac : ∀ n, QProduct.qFactorial q n ≠ 0) (f g : ℕ → K) :
    qDividedPowerSeries q (QExponential.qCauchy q f g) =
      qDividedPowerSeries q f * qDividedPowerSeries q g := by
  ext n
  rw [coeff_qDividedPowerSeries, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [QExponential.qCauchy, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  simp only [coeff_qDividedPowerSeries]
  have hbin := qBinomialEval_mul_qFactorials q hkn
  have hk0 := hfac k
  have hnk0 := hfac (n - k)
  have hn0 := hfac n
  field_simp [hk0, hnk0, hn0]
  rw [← hbin]
  ring

/-- Multiplication by `X` is the normalized form of `qMulX`. -/
theorem qDividedPowerSeries_qMulX
    {K : Type*} [Field K] (q : K)
    (hfac : ∀ n, QProduct.qFactorial q n ≠ 0) (f : ℕ → K) :
    qDividedPowerSeries q (QExponential.qMulX q f) =
      PowerSeries.X * qDividedPowerSeries q f := by
  ext n
  cases n with
  | zero => simp [QExponential.qMulX]
  | succ n =>
      rw [coeff_qDividedPowerSeries, PowerSeries.coeff_succ_X_mul,
        coeff_qDividedPowerSeries]
      simp only [QExponential.qMulX]
      rw [QProduct.qFactorial_succ]
      have hqint : QExponential.qInteger q (n + 1) ≠ 0 := by
        intro hz
        apply hfac (n + 1)
        rw [QProduct.qFactorial_succ, hz, mul_zero]
      field_simp [hfac n, hqint]

/-- The divided-power series of the scaled q-exponential tail is the literal
formal series `exp_q(qX)-1`. -/
theorem qDividedPowerSeries_scaledQExpTail
    {K : Type*} [Field K] (q : K) :
    qDividedPowerSeries q (QExponential.scaledQExpTail q) =
      PowerSeries.rescale q (QProduct.qExponential q) - 1 := by
  ext n
  cases n with
  | zero =>
      have hc : PowerSeries.constantCoeff
          (PowerSeries.rescale q (QProduct.qExponential q)) = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        simp [QProduct.coeff_qExponential]
      simp [hc]
  | succ n =>
      simp [QExponential.scaledQExpTail,
        QProduct.coeff_qExponential]

/-- The q-exponential generating series whose divided-power coefficients are
the literal permutation enumerators. -/
noncomputable def permutationQGeneratingSeries
    {K : Type*} [Field K] (q t : K) : PowerSeries K :=
  qDividedPowerSeries q (permutationEnumerator q t)

@[simp]
theorem coeff_permutationQGeneratingSeries
    {K : Type*} [Field K] (q t : K) (n : ℕ) :
    PowerSeries.coeff n (permutationQGeneratingSeries q t) =
      permutationEnumerator q t n * (QProduct.qFactorial q n)⁻¹ := by
  simp [permutationQGeneratingSeries]

@[simp]
theorem constantCoeff_permutationQGeneratingSeries
    {K : Type*} [Field K] (q t : K) :
    PowerSeries.constantCoeff (permutationQGeneratingSeries q t) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

/-- Equation (6) as an equality of honest formal power series for the actual
permutation q-EGF.  Nonvanishing q-factorials are exactly what is needed to
interpret the divided-power denominators without totalized-inverse artifacts. -/
theorem equation_6_permutations_powerSeries
    {K : Type*} [Field K] (q t : K)
    (hfac : ∀ n, QProduct.qFactorial q n ≠ 0) :
    PowerSeries.rescale q (permutationQGeneratingSeries q t) =
      permutationQGeneratingSeries q t * QProduct.paperFactor q t 0 := by
  let I : ℕ → K := permutationEnumerator q t
  let T : ℕ → K := QExponential.scaledQExpTail q
  let H : ℕ → K := fun n ↦
    I n + t * QExponential.qCauchy q I T n
  have heq : QExponential.qRescale q I = fun n ↦
      I n + (q - 1) * QExponential.qMulX q H n := by
    simpa [I, T, H] using equation_6_permutations_no_division q t
  have hH : qDividedPowerSeries q H =
      qDividedPowerSeries q I + PowerSeries.C t *
        (qDividedPowerSeries q I *
          (PowerSeries.rescale q (QProduct.qExponential q) - 1)) := by
    calc
      qDividedPowerSeries q H =
          qDividedPowerSeries q I + PowerSeries.C t *
            qDividedPowerSeries q (QExponential.qCauchy q I T) := by
        exact qDividedPowerSeries_add_const_mul q t I
          (QExponential.qCauchy q I T)
      _ = qDividedPowerSeries q I + PowerSeries.C t *
          (qDividedPowerSeries q I * qDividedPowerSeries q T) := by
        rw [qDividedPowerSeries_qCauchy q hfac]
      _ = qDividedPowerSeries q I + PowerSeries.C t *
          (qDividedPowerSeries q I *
            (PowerSeries.rescale q (QProduct.qExponential q) - 1)) := by
        dsimp [T]
        rw [qDividedPowerSeries_scaledQExpTail]
  have hmapped := congrArg (qDividedPowerSeries q) heq
  calc
    PowerSeries.rescale q (permutationQGeneratingSeries q t) =
        qDividedPowerSeries q (QExponential.qRescale q I) := by
      change PowerSeries.rescale q
          (qDividedPowerSeries q (permutationEnumerator q t)) =
        qDividedPowerSeries q
          (QExponential.qRescale q (permutationEnumerator q t))
      exact (qDividedPowerSeries_qRescale q
        (permutationEnumerator q t)).symm
    _ = qDividedPowerSeries q
        (fun n ↦ I n + (q - 1) * QExponential.qMulX q H n) := hmapped
    _ = qDividedPowerSeries q I + PowerSeries.C (q - 1) *
        qDividedPowerSeries q (QExponential.qMulX q H) := by
      exact qDividedPowerSeries_add_const_mul q (q - 1) I
        (QExponential.qMulX q H)
    _ = qDividedPowerSeries q I + PowerSeries.C (q - 1) *
        (PowerSeries.X * qDividedPowerSeries q H) := by
      rw [qDividedPowerSeries_qMulX q hfac]
    _ = qDividedPowerSeries q I + PowerSeries.C (q - 1) *
        (PowerSeries.X *
          (qDividedPowerSeries q I + PowerSeries.C t *
            (qDividedPowerSeries q I *
              (PowerSeries.rescale q (QProduct.qExponential q) - 1)))) := by
      rw [hH]
    _ = permutationQGeneratingSeries q t * QProduct.paperFactor q t 0 := by
      have hfactor : QProduct.paperFactor q t 0 = QProduct.baseFactor q t := by
        simp [QProduct.paperFactor]
      rw [hfactor, QProduct.baseFactor]
      dsimp [I]
      rw [permutationQGeneratingSeries]
      ring

/-- The unconditional finite iteration in Theorem 3.1, specialized to the
actual permutation q-EGF.  The formal-power-series form of equation (6) is
derived above from the literal permutation recurrence. -/
theorem theorem_3_1_finite_permutations
    {K : Type*} [Field K] (q t : K)
    (hfac : ∀ n, QProduct.qFactorial q n ≠ 0)
    (N : ℕ) :
    PowerSeries.rescale (q ^ N) (permutationQGeneratingSeries q t) =
      permutationQGeneratingSeries q t *
        ∏ k ∈ Finset.range N, QProduct.paperFactor q t k := by
  exact QProduct.finite_product_of_equation_six q t
    (permutationQGeneratingSeries q t)
    (equation_6_permutations_powerSeries q t hfac) N

/-- The reciprocal finite-product conclusion when a finite rescaling of the
actual q-EGF is exactly one. -/
theorem theorem_3_1_finite_inverse_permutations
    {K : Type*} [Field K] (q t : K)
    (hfac : ∀ n, QProduct.qFactorial q n ≠ 0)
    (N : ℕ)
    (hN : PowerSeries.rescale (q ^ N) (permutationQGeneratingSeries q t) = 1) :
    permutationQGeneratingSeries q t =
      (∏ k ∈ Finset.range N, QProduct.paperFactor q t k)⁻¹ := by
  exact QProduct.eq_inverse_finite_product_of_rescale_eq_one q t
    (permutationQGeneratingSeries q t)
    (equation_6_permutations_powerSeries q t hfac) N hN

/-- The literal infinite-product claim of Theorem 3.1 for the actual q-EGF.
The two convergence hypotheses are explicit; they are absent from the paper
and cannot be inferred in a bare formal-power-series ring. -/
theorem theorem_3_1_infinite_permutations
    {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] (q t : K)
    (hfac : ∀ n, QProduct.qFactorial q n ≠ 0)
    (hI : Tendsto
      (QProduct.rescaledUnit q (permutationQGeneratingSeries q t)
        (constantCoeff_permutationQGeneratingSeries q t))
      atTop (nhds 1))
    (hF : Multipliable (QProduct.paperFactorUnit q t)) :
    QProduct.seriesUnit (permutationQGeneratingSeries q t)
        (constantCoeff_permutationQGeneratingSeries q t) =
      (∏' k, QProduct.paperFactorUnit q t k)⁻¹ := by
  exact QProduct.infinite_product_of_equation_six q t
    (permutationQGeneratingSeries q t)
    (constantCoeff_permutationQGeneratingSeries q t)
    (equation_6_permutations_powerSeries q t hfac) hI hF

/-! ## The Laurent restricted-growth enumerator -/

open SetPartition
open SetPartition.CanonicalPartition
open RestrictedGrowth

/-- The paper's `J_n(q,t)`.  Integer exponents are essential here: for
example the all-singleton restricted-growth word has inversion number `0`
and largest label `n`.  Thus the exponent `inv(w) - L(w)` is genuinely
negative, and must not be represented by truncated subtraction on `ℕ`. -/
noncomputable def laurentRestrictedGrowthEnumerator
    {K : Type*} [Field K] (q t : K) (n : ℕ) : K :=
  ∑ w : LiteralRGW n,
    q ^ ((RestrictedGrowth.inversionNumber w : ℤ) -
      (RestrictedGrowth.largestLabelPlusOne w : ℤ)) *
      t ^ RestrictedGrowth.repeatedLabelNumber w

/-- A literal restricted-growth word of length `n` uses at most `n` labels. -/
theorem largestLabelPlusOne_le (w : LiteralRGW n) :
    RestrictedGrowth.largestLabelPlusOne w ≤ n := by
  rw [← RestrictedGrowth.LiteralRGW.toLiteralRGW_toCanonical w,
    RestrictedGrowth.largestLabelPlusOne_toLiteralRGW]
  change w.toCanonical.representatives.card ≤ n
  simpa using w.toCanonical.representatives.card_le_univ

/-- The positive-exponent weight in Theorem 4.5 is `q^n` times the Laurent
weight defining `J_n`. -/
theorem qpow_mul_laurentRestrictedGrowthEnumerator
    {K : Type*} [Field K] (q t : K) (hq : q ≠ 0) (n : ℕ) :
    q ^ n * laurentRestrictedGrowthEnumerator q t n =
      ∑ w : LiteralRGW n, RestrictedGrowth.restrictedGrowthWeight q t w := by
  classical
  rw [laurentRestrictedGrowthEnumerator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have hlabel : RestrictedGrowth.largestLabelPlusOne w ≤ n :=
    largestLabelPlusOne_le w
  have hexponent :
      (n : ℤ) + ((RestrictedGrowth.inversionNumber w : ℤ) -
        (RestrictedGrowth.largestLabelPlusOne w : ℤ)) =
        (RestrictedGrowth.inversionNumber w + n -
          RestrictedGrowth.largestLabelPlusOne w : ℕ) := by
    omega
  rw [RestrictedGrowth.restrictedGrowthWeight]
  calc
    q ^ n *
        (q ^ ((RestrictedGrowth.inversionNumber w : ℤ) -
          (RestrictedGrowth.largestLabelPlusOne w : ℤ)) *
          t ^ RestrictedGrowth.repeatedLabelNumber w) =
        (q ^ n *
          q ^ ((RestrictedGrowth.inversionNumber w : ℤ) -
            (RestrictedGrowth.largestLabelPlusOne w : ℤ))) *
          t ^ RestrictedGrowth.repeatedLabelNumber w := by ac_rfl
    _ = q ^ ((n : ℤ) +
          ((RestrictedGrowth.inversionNumber w : ℤ) -
            (RestrictedGrowth.largestLabelPlusOne w : ℤ))) *
          t ^ RestrictedGrowth.repeatedLabelNumber w := by
      rw [← zpow_natCast q n, ← zpow_add₀ hq]
    _ = q ^ (RestrictedGrowth.inversionNumber w + n -
          RestrictedGrowth.largestLabelPlusOne w) *
          t ^ RestrictedGrowth.repeatedLabelNumber w := by
      rw [hexponent, zpow_natCast]

/-- Theorem 4.5 with its left side identified definitionally as the same
literal permutation enumerator used in Sections 2 and 3. -/
theorem permutationEnumerator_eq_restrictedGrowthEnumerator
    {R : Type*} [CommSemiring R] (q t : R) (n : ℕ) :
    permutationEnumerator q t n =
      ∑ w : LiteralRGW n, RestrictedGrowth.restrictedGrowthWeight q t w := by
  exact RestrictedGrowth.theorem_4_5 q t

/-- The exact scaling identity `I_n(q,t) = q^n J_n(q,t)`, now derived from
the actual permutation Theorem 4.5 rather than postulated. -/
theorem permutationEnumerator_eq_qpow_mul_laurentRestrictedGrowthEnumerator
    {K : Type*} [Field K] (q t : K) (hq : q ≠ 0) (n : ℕ) :
    permutationEnumerator q t n =
      q ^ n * laurentRestrictedGrowthEnumerator q t n := by
  rw [permutationEnumerator_eq_restrictedGrowthEnumerator]
  exact (qpow_mul_laurentRestrictedGrowthEnumerator q t hq n).symm

/-! ## The cancellation step behind Corollary 4.6 -/

/-- If `I_n = q^n J_n`, the last-zero recurrence for `I` cancels a common
nonzero factor `q^n` and becomes the recurrence stated in Corollary 4.6.

This algebraic lemma isolates the only extra hypothesis hidden in the paper's
passage from Theorems 2.5 and 4.5: powers of `q` must be cancellable. -/
theorem corollary_4_6_of_scaled_recurrence
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (q t : R) (I J : ℕ → R) (hq : q ≠ 0)
    (hscale : ∀ n, I n = q ^ n * J n)
    (hrec : ∀ n,
      I (n + 1) = I n +
        ∑ k : Fin n, (t * q ^ (n - k.1)) *
          qBinomialEval q n k.1 * I k.1) :
    ∀ n, q * J (n + 1) =
      t * (∑ k : Fin n, qBinomialEval q n k.1 * J k.1) + J n := by
  classical
  intro n
  have h := hrec n
  simp_rw [hscale] at h
  have hsummand (k : Fin n) :
      (t * q ^ (n - k.1)) * qBinomialEval q n k.1 *
          (q ^ k.1 * J k.1) =
        q ^ n * (t * qBinomialEval q n k.1 * J k.1) := by
    have hpow : q ^ (n - k.1) * q ^ k.1 = q ^ n := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (t * q ^ (n - k.1)) * qBinomialEval q n k.1 *
          (q ^ k.1 * J k.1) =
        (q ^ (n - k.1) * q ^ k.1) *
          (t * qBinomialEval q n k.1 * J k.1) := by ac_rfl
      _ = q ^ n * (t * qBinomialEval q n k.1 * J k.1) := by rw [hpow]
  have hfactored :
      q ^ n * (q * J (n + 1)) =
        q ^ n *
          (J n + ∑ k : Fin n, t * qBinomialEval q n k.1 * J k.1) := by
    calc
      q ^ n * (q * J (n + 1)) = q ^ (n + 1) * J (n + 1) := by
        rw [pow_succ]
        ac_rfl
      _ = q ^ n * J n +
          ∑ k : Fin n, (t * q ^ (n - k.1)) *
            qBinomialEval q n k.1 * (q ^ k.1 * J k.1) := h
      _ = q ^ n * J n +
          ∑ k : Fin n,
            q ^ n * (t * qBinomialEval q n k.1 * J k.1) := by
        congr 1
        apply Fintype.sum_congr
        exact fun k ↦ hsummand k
      _ = q ^ n *
          (J n + ∑ k : Fin n, t * qBinomialEval q n k.1 * J k.1) := by
        rw [mul_add]
        congr 1
        exact (Finset.mul_sum Finset.univ _ _).symm
  have hcancel := mul_left_cancel₀ (pow_ne_zero n hq) hfactored
  calc
    q * J (n + 1) =
        J n + ∑ k : Fin n, t * qBinomialEval q n k.1 * J k.1 := hcancel
    _ = J n + t *
        (∑ k : Fin n, qBinomialEval q n k.1 * J k.1) := by
      congr 1
      calc
        (∑ k : Fin n, t * qBinomialEval q n k.1 * J k.1) =
            ∑ k : Fin n, t * (qBinomialEval q n k.1 * J k.1) := by
          apply Fintype.sum_congr
          intro k
          ac_rfl
        _ = t * (∑ k : Fin n, qBinomialEval q n k.1 * J k.1) :=
          (Finset.mul_sum (Finset.univ : Finset (Fin n))
            (fun k : Fin n ↦ qBinomialEval q n k.1 * J k.1) t).symm
    _ = t * (∑ k : Fin n, qBinomialEval q n k.1 * J k.1) + J n := by
      ac_rfl

/-- Corollary 4.6 for the actual Laurent restricted-growth enumerator, in
successor indexing. -/
theorem corollary_4_6_succ
    {K : Type*} [Field K] (q t : K) (hq : q ≠ 0) (n : ℕ) :
    q * laurentRestrictedGrowthEnumerator q t (n + 1) =
      t * (∑ k : Fin n, qBinomialEval q n k.1 *
        laurentRestrictedGrowthEnumerator q t k.1) +
      laurentRestrictedGrowthEnumerator q t n := by
  exact corollary_4_6_of_scaled_recurrence q t
    (permutationEnumerator q t)
    (laurentRestrictedGrowthEnumerator q t) hq
    (permutationEnumerator_eq_qpow_mul_laurentRestrictedGrowthEnumerator q t hq)
    (permutationEnumerator_succ q t) n

/-- **Corollary 4.6**, with the paper's `n ≥ 1` indexing. -/
theorem corollary_4_6
    {K : Type*} [Field K] (q t : K) (hq : q ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) :
    q * laurentRestrictedGrowthEnumerator q t n =
      t * (∑ k : Fin (n - 1), qBinomialEval q (n - 1) k.1 *
        laurentRestrictedGrowthEnumerator q t k.1) +
      laurentRestrictedGrowthEnumerator q t (n - 1) := by
  have h := corollary_4_6_succ q t hq (n - 1)
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at h
  exact h

@[simp]
theorem laurentRestrictedGrowthEnumerator_zero
    {K : Type*} [Field K] (q t : K) (hq : q ≠ 0) :
    laurentRestrictedGrowthEnumerator q t 0 = 1 := by
  have h :=
    permutationEnumerator_eq_qpow_mul_laurentRestrictedGrowthEnumerator
      q t hq 0
  rw [permutationEnumerator_zero] at h
  simpa using h.symm

end LeanCo
