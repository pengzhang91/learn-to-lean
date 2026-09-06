import LeanCo.LaplacianLFunctions.RiemannRochConsequences
import LeanCo.LaplacianLFunctions.Zeta
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Rationality of the two-variable graph zeta function

This file formalizes Proposition 3.3 of arXiv:2608.29981 over the integral
coefficient ring `ℤ[u]`.  Its image under `ℤ → ℂ` is the complex-coefficient
zeta series used by the character-theoretic development.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- Integral coefficient of the intrinsic zeta function. -/
def integralZetaCoefficient (G : LooplessMultigraph V)
    [Fintype G.Jacobian] (d : ℕ) : Polynomial ℤ :=
  ∑ C : G.PicardDegree (d : ℤ),
    geometricPolynomial (R := ℤ) (G.h (C : G.Picard))

/-- The integral two-variable zeta series. -/
def integralZeta (G : LooplessMultigraph V) [Fintype G.Jacobian] :
    PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk G.integralZetaCoefficient

@[simp]
theorem coeff_integralZeta (G : LooplessMultigraph V)
    [Fintype G.Jacobian] (d : ℕ) :
    PowerSeries.coeff d G.integralZeta = G.integralZetaCoefficient d := by
  simp [integralZeta]

/-- A constant value of `h` on a fixed-degree torsor turns the zeta
coefficient into `|J|` copies of one geometric polynomial. -/
theorem integralZetaCoefficient_eq_card_nsmul_of_h_constant
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (d n : ℕ)
    (hconstant : ∀ a : G.Jacobian,
      G.h (G.classInDegree D₁ (d : ℤ) a) = n) :
    G.integralZetaCoefficient d =
      Fintype.card G.Jacobian • geometricPolynomial (R := ℤ) n := by
  classical
  rw [integralZetaCoefficient]
  calc
    (∑ C : G.PicardDegree (d : ℤ),
        geometricPolynomial (R := ℤ) (G.h (C : G.Picard))) =
        ∑ a : G.Jacobian,
          geometricPolynomial (R := ℤ)
            (G.h (G.classInDegree D₁ (d : ℤ) a)) := by
      symm
      exact Fintype.sum_equiv
        (G.jacobianEquivPicardDegree D₁ (d : ℤ))
        (fun a : G.Jacobian ↦
          geometricPolynomial (R := ℤ)
            (G.h (G.classInDegree D₁ (d : ℤ) a)))
        (fun C : G.PicardDegree (d : ℤ) ↦
          geometricPolynomial (R := ℤ) (G.h (C : G.Picard)))
        (fun _ ↦ rfl)
    _ = Fintype.card G.Jacobian • geometricPolynomial (R := ℤ) n := by
      simp only [hconstant, Finset.sum_const, Finset.card_univ]

/-- Twice the (nonnegative) genus is the numerator's natural `t`-degree
bound. -/
def zetaNumeratorBound (G : LooplessMultigraph V) : ℕ :=
  2 * G.genus.toNat

/-- The denominator `(1-t)(1-ut)`, expanded as a power series in `t`. -/
def zetaDenominator : PowerSeries (Polynomial ℤ) :=
  1 - PowerSeries.X -
    PowerSeries.C Polynomial.X * PowerSeries.X +
    PowerSeries.C Polynomial.X * PowerSeries.X ^ 2

theorem zetaDenominator_eq_factored :
    zetaDenominator =
      (1 - PowerSeries.X) *
        (1 - PowerSeries.C (Polynomial.X : Polynomial ℤ) *
          PowerSeries.X) := by
  rw [zetaDenominator]
  ring

/-- Candidate numerator, obtained by truncating the denominator times the
integral zeta series through degree `2g`. -/
def integralZetaNumerator (G : LooplessMultigraph V)
    [Fintype G.Jacobian] : Polynomial (Polynomial ℤ) :=
  PowerSeries.trunc (G.zetaNumeratorBound + 1)
    (zetaDenominator * G.integralZeta)

@[simp]
theorem coeff_integralZetaNumerator (G : LooplessMultigraph V)
    [Fintype G.Jacobian] (d : ℕ) :
    G.integralZetaNumerator.coeff d =
      if d ≤ G.zetaNumeratorBound then
        PowerSeries.coeff d (zetaDenominator * G.integralZeta)
      else 0 := by
  rw [integralZetaNumerator, PowerSeries.coeff_trunc]
  simp only [Nat.lt_add_one_iff]

/-- Multiplication by `(1-t)(1-ut)` takes the expected second finite
difference of zeta coefficients. -/
theorem coeff_zetaDenominator_mul_integralZeta_of_two_le
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (d : ℕ) (hd : 2 ≤ d) :
    PowerSeries.coeff d (zetaDenominator * G.integralZeta) =
      G.integralZetaCoefficient d -
        (1 + Polynomial.X) * G.integralZetaCoefficient (d - 1) +
        Polynomial.X * G.integralZetaCoefficient (d - 2) := by
  simp only [zetaDenominator, add_mul, sub_mul, one_mul,
    map_add, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rw [show PowerSeries.X * G.integralZeta =
      PowerSeries.X ^ 1 * G.integralZeta by simp]
  simp only [PowerSeries.coeff_X_pow_mul',
    if_pos (show 1 ≤ d by omega), if_pos hd, G.coeff_integralZeta]
  ring

/-- The degree-one coefficient is the first-order difference of the first
two zeta coefficients. -/
theorem coeff_zetaDenominator_mul_integralZeta_one
    (G : LooplessMultigraph V) [Fintype G.Jacobian] :
    PowerSeries.coeff 1 (zetaDenominator * G.integralZeta) =
      G.integralZetaCoefficient 1 -
        (1 + Polynomial.X) * G.integralZetaCoefficient 0 := by
  simp only [zetaDenominator, add_mul, sub_mul, one_mul,
    map_add, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rw [show PowerSeries.X * G.integralZeta =
      PowerSeries.X ^ 1 * G.integralZeta by simp]
  simp only [PowerSeries.coeff_X_pow_mul', if_pos (show 1 ≤ 1 by omega),
    if_neg (show ¬2 ≤ 1 by omega), G.coeff_integralZeta]
  ring

/-- The constant term is unchanged by the zeta denominator. -/
theorem coeff_zetaDenominator_mul_integralZeta_zero
    (G : LooplessMultigraph V) [Fintype G.Jacobian] :
    PowerSeries.coeff 0 (zetaDenominator * G.integralZeta) =
      G.integralZetaCoefficient 0 := by
  simp [zetaDenominator]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact G.coeff_integralZeta 0

/-- In high degree every Jacobian coordinate has the same `h` as the zero
coordinate. -/
theorem h_classInDegree_eq_zeroCoordinate_of_gt
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (D₁ : G.PicardDegree 1) (d : ℕ)
    (hdegree : 2 * G.genus - 2 < (d : ℤ)) (a : G.Jacobian) :
    G.h (G.classInDegree D₁ (d : ℤ) a) =
      G.h (G.classInDegree D₁ (d : ℤ) 0) := by
  obtain ⟨n, hn⟩ :=
    G.h_classInDegree_constant_of_riemannRoch hRR D₁ d hdegree
  exact (hn a).trans (hn 0).symm

/-- A high-degree Riemann--Roch value gives an explicit zeta coefficient. -/
theorem integralZetaCoefficient_eq_card_nsmul_of_riemannRoch_of_gt
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (d n : ℕ) (hdegree : 2 * G.genus - 2 < (d : ℤ))
    (hn : (n : ℤ) = (d : ℤ) - G.genus + 1) :
    G.integralZetaCoefficient d =
      Fintype.card G.Jacobian • geometricPolynomial (R := ℤ) n := by
  apply G.integralZetaCoefficient_eq_card_nsmul_of_h_constant D₁ d n
  intro a
  apply Int.ofNat_injective
  calc
    (G.h (G.classInDegree D₁ (d : ℤ) a) : ℤ) =
        (d : ℤ) - G.genus + 1 := by
      simpa using G.intCast_h_eq_degree_sub_genus_add_one_of_gt hRR
        (G.classInDegree D₁ (d : ℤ) a) (by simpa using hdegree)
    _ = (n : ℤ) := hn.symm

/-- In positive genus, the canonical degree is exactly two below the zeta
numerator bound. -/
theorem riemannRochBound_add_two_eq_zetaNumeratorBound_of_genus_pos
    (G : LooplessMultigraph V) (hgenus : 1 ≤ G.genus) :
    G.riemannRochBound + 2 = G.zetaNumeratorBound := by
  unfold riemannRochBound zetaNumeratorBound
  let gn : ℕ := G.genus.toNat
  change (2 * G.genus - 2).toNat + 2 = 2 * gn
  have hcast : (gn : ℤ) = G.genus :=
    Int.toNat_of_nonneg (by omega)
  rw [← hcast, Int.toNat_of_nonneg (by omega)]
  omega

/-- Cast form of the zeta numerator bound. -/
theorem intCast_zetaNumeratorBound_of_genus_nonneg
    (G : LooplessMultigraph V) (hgenus : 0 ≤ G.genus) :
    (G.zetaNumeratorBound : ℤ) = 2 * G.genus := by
  simp [zetaNumeratorBound, Int.toNat_of_nonneg hgenus]

/-- The zeta coefficient in degree `2g` is the common high-degree torsor
value. -/
theorem integralZetaCoefficient_zetaNumeratorBound
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (hgenus : 1 ≤ G.genus) :
    G.integralZetaCoefficient G.zetaNumeratorBound =
      Fintype.card G.Jacobian •
        geometricPolynomial (R := ℤ) (G.genus.toNat + 1) := by
  have hgenusNonneg : 0 ≤ G.genus := by omega
  have hboundCast := G.intCast_zetaNumeratorBound_of_genus_nonneg hgenusNonneg
  have hgenusCast : (G.genus.toNat : ℤ) = G.genus :=
    Int.toNat_of_nonneg hgenusNonneg
  apply G.integralZetaCoefficient_eq_card_nsmul_of_riemannRoch_of_gt
    hRR D₁ G.zetaNumeratorBound (G.genus.toNat + 1)
  · omega
  · norm_num only [Nat.cast_add, Nat.cast_one]
    omega

/-- The preceding high-degree zeta coefficient, in degree `2g-1`. -/
theorem integralZetaCoefficient_zetaNumeratorBound_sub_one
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (hgenus : 1 ≤ G.genus) :
    G.integralZetaCoefficient (G.zetaNumeratorBound - 1) =
      Fintype.card G.Jacobian •
        geometricPolynomial (R := ℤ) G.genus.toNat := by
  have hgenusNonneg : 0 ≤ G.genus := by omega
  have hboundCast := G.intCast_zetaNumeratorBound_of_genus_nonneg hgenusNonneg
  have hgenusCast : (G.genus.toNat : ℤ) = G.genus :=
    Int.toNat_of_nonneg hgenusNonneg
  have hboundTwo : 2 ≤ G.zetaNumeratorBound := by
    unfold zetaNumeratorBound
    omega
  have hsubCast : ((G.zetaNumeratorBound - 1 : ℕ) : ℤ) =
      (G.zetaNumeratorBound : ℤ) - 1 := by omega
  apply G.integralZetaCoefficient_eq_card_nsmul_of_riemannRoch_of_gt
    hRR D₁ (G.zetaNumeratorBound - 1) G.genus.toNat
  · omega
  · omega

/-- Above degree `2g`, the denominator times zeta has zero coefficient. -/
theorem coeff_zetaDenominator_mul_integralZeta_eq_zero_of_bound_lt
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (d : ℕ) (hd : G.zetaNumeratorBound < d) :
    PowerSeries.coeff d (zetaDenominator * G.integralZeta) = 0 := by
  let gn : ℕ := G.genus.toNat
  have hgenusNonneg := G.genus_nonneg_of_riemannRoch hRR
  have hgenusCast : (gn : ℤ) = G.genus := by
    exact Int.toNat_of_nonneg hgenusNonneg
  have hbound : 2 * gn < d := by simpa [zetaNumeratorBound, gn] using hd
  by_cases hdTwo : 2 ≤ d
  · have hcastSubOne : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
    have hcastSubTwo : ((d - 2 : ℕ) : ℤ) = (d : ℤ) - 2 := by omega
    have hhigh0 : 2 * G.genus - 2 < (d : ℤ) := by omega
    have hhigh1 : 2 * G.genus - 2 < ((d - 1 : ℕ) : ℤ) := by omega
    have hhigh2 : 2 * G.genus - 2 < ((d - 2 : ℕ) : ℤ) := by omega
    let n : ℕ := G.h (G.classInDegree D₁ ((d - 2 : ℕ) : ℤ) 0)
    have hnCast : (n : ℤ) = ((d - 2 : ℕ) : ℤ) - G.genus + 1 := by
      simpa [n] using G.intCast_h_eq_degree_sub_genus_add_one_of_gt hRR
        (G.classInDegree D₁ ((d - 2 : ℕ) : ℤ) 0) (by simpa using hhigh2)
    have hnOneCast :
        (G.h (G.classInDegree D₁ ((d - 1 : ℕ) : ℤ) 0) : ℤ) =
          ((d - 1 : ℕ) : ℤ) - G.genus + 1 := by
      simpa using G.intCast_h_eq_degree_sub_genus_add_one_of_gt hRR
        (G.classInDegree D₁ ((d - 1 : ℕ) : ℤ) 0) (by simpa using hhigh1)
    have hnTwoCast :
        (G.h (G.classInDegree D₁ (d : ℤ) 0) : ℤ) =
          (d : ℤ) - G.genus + 1 := by
      simpa using G.intCast_h_eq_degree_sub_genus_add_one_of_gt hRR
        (G.classInDegree D₁ (d : ℤ) 0) (by simpa using hhigh0)
    have hnOne :
        G.h (G.classInDegree D₁ ((d - 1 : ℕ) : ℤ) 0) = n + 1 := by
      apply Int.ofNat_injective
      calc
        (G.h (G.classInDegree D₁ ((d - 1 : ℕ) : ℤ) 0) : ℤ) =
            ((d - 1 : ℕ) : ℤ) - G.genus + 1 := hnOneCast
        _ = (((d - 2 : ℕ) : ℤ) - G.genus + 1) + 1 := by omega
        _ = (n : ℤ) + 1 := by rw [hnCast]
        _ = ((n + 1 : ℕ) : ℤ) := by simp
    have hnTwo :
        G.h (G.classInDegree D₁ (d : ℤ) 0) = n + 2 := by
      apply Int.ofNat_injective
      calc
        (G.h (G.classInDegree D₁ (d : ℤ) 0) : ℤ) =
            (d : ℤ) - G.genus + 1 := hnTwoCast
        _ = (((d - 2 : ℕ) : ℤ) - G.genus + 1) + 2 := by omega
        _ = (n : ℤ) + 2 := by rw [hnCast]
        _ = ((n + 2 : ℕ) : ℤ) := by simp
    have hconst0 : ∀ a : G.Jacobian,
        G.h (G.classInDegree D₁ (d : ℤ) a) = n + 2 := by
      intro a
      rw [G.h_classInDegree_eq_zeroCoordinate_of_gt hRR D₁ d hhigh0 a,
        hnTwo]
    have hconst1 : ∀ a : G.Jacobian,
        G.h (G.classInDegree D₁ ((d - 1 : ℕ) : ℤ) a) = n + 1 := by
      intro a
      rw [G.h_classInDegree_eq_zeroCoordinate_of_gt hRR D₁ (d - 1) hhigh1 a,
        hnOne]
    have hconst2 : ∀ a : G.Jacobian,
        G.h (G.classInDegree D₁ ((d - 2 : ℕ) : ℤ) a) = n := by
      intro a
      exact G.h_classInDegree_eq_zeroCoordinate_of_gt
        hRR D₁ (d - 2) hhigh2 a
    rw [G.coeff_zetaDenominator_mul_integralZeta_of_two_le d hdTwo,
      G.integralZetaCoefficient_eq_card_nsmul_of_h_constant D₁ d (n + 2) hconst0,
      G.integralZetaCoefficient_eq_card_nsmul_of_h_constant D₁ (d - 1) (n + 1) hconst1,
      G.integralZetaCoefficient_eq_card_nsmul_of_h_constant D₁ (d - 2) n hconst2]
    have hrec := congrArg
      (fun p : Polynomial ℤ ↦
        (Fintype.card G.Jacobian : Polynomial ℤ) * p)
      (geometricPolynomial_quadratic_recurrence (R := ℤ) n)
    simp only [mul_zero] at hrec
    simp only [nsmul_eq_mul]
    linear_combination hrec

  · have hdOne : d = 1 := by omega
    subst d
    have hgnZero : gn = 0 := by omega
    have hgenusZero : G.genus = 0 := by omega
    have hconst0 : ∀ a : G.Jacobian,
        G.h (G.classInDegree D₁ (0 : ℤ) a) = 1 := by
      intro a
      have ha := G.jacobian_eq_zero_of_riemannRoch_of_genus_zero
        hRR hgenusZero a
      subst a
      simpa [classInDegree] using G.h_zero
    have hconst1 : ∀ a : G.Jacobian,
        G.h (G.classInDegree D₁ (1 : ℤ) a) = 2 := by
      intro a
      apply Int.ofNat_injective
      have hhigh : 2 * G.genus - 2 <
          G.picardDegree (G.classInDegree D₁ (1 : ℤ) a) := by
        rw [G.picardDegree_classInDegree, hgenusZero]
        omega
      calc
        (G.h (G.classInDegree D₁ (1 : ℤ) a) : ℤ) =
            G.picardDegree (G.classInDegree D₁ (1 : ℤ) a) -
              G.genus + 1 :=
          G.intCast_h_eq_degree_sub_genus_add_one_of_gt hRR _ hhigh
        _ = 2 := by
          rw [G.picardDegree_classInDegree, hgenusZero]
          norm_num
        _ = ((2 : ℕ) : ℤ) := by simp
    rw [G.coeff_zetaDenominator_mul_integralZeta_one,
      G.integralZetaCoefficient_eq_card_nsmul_of_h_constant D₁ 1 2 hconst1,
      G.integralZetaCoefficient_eq_card_nsmul_of_h_constant D₁ 0 1 hconst0]
    have hrec := congrArg
      (fun p : Polynomial ℤ ↦
        (Fintype.card G.Jacobian : Polynomial ℤ) * p)
      (geometricPolynomial_quadratic_recurrence (R := ℤ) 0)
    simp only [geometricPolynomial_zero, mul_zero, add_zero] at hrec
    simp only [nsmul_eq_mul]
    linear_combination hrec

/-- The partial sums of the denominator product telescope to a first
difference of zeta coefficients. -/
theorem sum_coeff_zetaDenominator_mul_integralZeta
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ d ∈ Finset.range (N + 1),
        PowerSeries.coeff d (zetaDenominator * G.integralZeta)) =
      G.integralZetaCoefficient N -
        Polynomial.X * G.integralZetaCoefficient (N - 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hzero : N = 0
      · subst N
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [Finset.sum_range_zero, zero_add]
        rw [G.coeff_zetaDenominator_mul_integralZeta_zero,
          G.coeff_zetaDenominator_mul_integralZeta_one]
        ring
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hzero
        have htwo : 2 ≤ N + 1 := by omega
        rw [Finset.sum_range_succ, ih hNpos,
          G.coeff_zetaDenominator_mul_integralZeta_of_two_le (N + 1) htwo]
        have hsubOne : N + 1 - 1 = N := by omega
        have hsubTwo : N + 1 - 2 = N - 1 := by omega
        rw [hsubOne, hsubTwo]
        ring

/-- At canonical degree the unique canonical class contributes one extra
top monomial beyond the common contribution of the Jacobian torsor. -/
theorem integralZetaCoefficient_riemannRochBound
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (hgenus : 1 ≤ G.genus) :
    G.integralZetaCoefficient G.riemannRochBound =
      Fintype.card G.Jacobian •
          geometricPolynomial (R := ℤ) (G.genus.toNat - 1) +
        Polynomial.X ^ (G.genus.toNat - 1) := by
  classical
  let k : G.Jacobian := G.canonicalCoordinate D₁
  let gn : ℕ := G.genus.toNat
  have hk : G.h (G.classInDegree D₁ (G.riemannRochBound : ℤ) k) = gn := by
    simpa [k, gn] using
      G.h_classInDegree_canonicalCoordinate_of_riemannRoch hRR D₁ hgenus
  have hother : ∀ a ∈ Finset.univ.erase k,
      G.h (G.classInDegree D₁ (G.riemannRochBound : ℤ) a) = gn - 1 := by
    intro a ha
    have hak : a ≠ k := (Finset.mem_erase.mp ha).1
    simpa [k, gn] using
      G.h_classInDegree_eq_genus_toNat_sub_one_of_ne_canonicalCoordinate
        hRR D₁ hgenus a hak
  rw [integralZetaCoefficient]
  calc
    (∑ C : G.PicardDegree (G.riemannRochBound : ℤ),
        geometricPolynomial (R := ℤ) (G.h (C : G.Picard))) =
        ∑ a : G.Jacobian,
          geometricPolynomial (R := ℤ)
            (G.h (G.classInDegree D₁
              (G.riemannRochBound : ℤ) a)) := by
      symm
      exact Fintype.sum_equiv
        (G.jacobianEquivPicardDegree D₁ (G.riemannRochBound : ℤ))
        (fun a : G.Jacobian ↦
          geometricPolynomial (R := ℤ)
            (G.h (G.classInDegree D₁
              (G.riemannRochBound : ℤ) a)))
        (fun C : G.PicardDegree (G.riemannRochBound : ℤ) ↦
          geometricPolynomial (R := ℤ) (G.h (C : G.Picard)))
        (fun _ ↦ rfl)
    _ = geometricPolynomial (R := ℤ) gn +
        ∑ a ∈ Finset.univ.erase k,
          geometricPolynomial (R := ℤ) (gn - 1) := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun a : G.Jacobian ↦
          geometricPolynomial (R := ℤ)
            (G.h (G.classInDegree D₁
              (G.riemannRochBound : ℤ) a)))
        (Finset.mem_univ k), hk]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [hother a ha]
    _ = geometricPolynomial (R := ℤ) gn +
        (Fintype.card G.Jacobian - 1) •
          geometricPolynomial (R := ℤ) (gn - 1) := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
        Finset.card_univ]
    _ = Fintype.card G.Jacobian •
          geometricPolynomial (R := ℤ) (gn - 1) +
        Polynomial.X ^ (gn - 1) := by
      have hgnPos : 0 < gn := by
        have hcast : (gn : ℤ) = G.genus :=
          Int.toNat_of_nonneg (by omega)
        omega
      have hgeo : geometricPolynomial (R := ℤ) gn =
          geometricPolynomial (gn - 1) + Polynomial.X ^ (gn - 1) := by
        have hsubadd : gn - 1 + 1 = gn := Nat.sub_add_cancel hgnPos
        simpa only [hsubadd] using
          geometricPolynomial_succ (R := ℤ) (gn - 1)
      have hcardPos : 0 < Fintype.card G.Jacobian := Fintype.card_pos
      have hsum :
          (Fintype.card G.Jacobian - 1) •
              geometricPolynomial (R := ℤ) (gn - 1) +
            geometricPolynomial (R := ℤ) (gn - 1) =
          Fintype.card G.Jacobian •
            geometricPolynomial (R := ℤ) (gn - 1) := by
        conv_lhs =>
          rhs
          rw [← one_nsmul
            (geometricPolynomial (R := ℤ) (gn - 1))]
        rw [← add_nsmul, Nat.sub_add_cancel hcardPos]
      rw [hgeo]
      calc
        geometricPolynomial (R := ℤ) (gn - 1) +
              Polynomial.X ^ (gn - 1) +
              (Fintype.card G.Jacobian - 1) •
                geometricPolynomial (R := ℤ) (gn - 1) =
            ((Fintype.card G.Jacobian - 1) •
                geometricPolynomial (R := ℤ) (gn - 1) +
              geometricPolynomial (R := ℤ) (gn - 1)) +
                Polynomial.X ^ (gn - 1) := by abel
        _ = Fintype.card G.Jacobian •
              geometricPolynomial (R := ℤ) (gn - 1) +
            Polynomial.X ^ (gn - 1) := by rw [hsum]

/-- The `t^(2g)` coefficient of the zeta numerator is the monomial `u^g`.
This supplies the exact-degree assertion of Proposition 3.3. -/
theorem coeff_integralZetaNumerator_zetaNumeratorBound_of_genus_pos
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (hgenus : 1 ≤ G.genus) :
    G.integralZetaNumerator.coeff G.zetaNumeratorBound =
      Polynomial.X ^ G.genus.toNat := by
  let gn : ℕ := G.genus.toNat
  have hgenusNonneg : 0 ≤ G.genus := by omega
  have hgenusCast : (gn : ℤ) = G.genus :=
    Int.toNat_of_nonneg hgenusNonneg
  have hgnPos : 0 < gn := by omega
  have hboundTwo : 2 ≤ G.zetaNumeratorBound := by
    unfold zetaNumeratorBound
    omega
  have hboundRelation :=
    G.riemannRochBound_add_two_eq_zetaNumeratorBound_of_genus_pos hgenus
  have hminusTwo : G.zetaNumeratorBound - 2 = G.riemannRochBound := by
    omega
  rw [G.coeff_integralZetaNumerator, if_pos le_rfl,
    G.coeff_zetaDenominator_mul_integralZeta_of_two_le
      G.zetaNumeratorBound hboundTwo,
    G.integralZetaCoefficient_zetaNumeratorBound hRR D₁ hgenus,
    G.integralZetaCoefficient_zetaNumeratorBound_sub_one hRR D₁ hgenus,
    hminusTwo,
    G.integralZetaCoefficient_riemannRochBound hRR D₁ hgenus]
  have hsubOne : gn - 1 + 1 = gn := Nat.sub_add_cancel hgnPos
  have hsubTwo : gn - 1 + 2 = gn + 1 := by omega
  have hrec := congrArg
    (fun p : Polynomial ℤ ↦
      (Fintype.card G.Jacobian : Polynomial ℤ) * p)
    (geometricPolynomial_quadratic_recurrence (R := ℤ) (gn - 1))
  simp only [hsubOne, hsubTwo, mul_zero] at hrec
  have hpow : Polynomial.X * Polynomial.X ^ (gn - 1) =
      (Polynomial.X : Polynomial ℤ) ^ gn := by
    rw [← pow_succ']
    congr
  rw [mul_add, hpow]
  simp only [nsmul_eq_mul]
  linear_combination hrec

/-- A genus-zero graph satisfying Riemann--Roch has trivial Jacobian. -/
theorem card_jacobian_eq_one_of_riemannRoch_of_genus_zero
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (hgenus : G.genus = 0) :
    Fintype.card G.Jacobian = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  exact ⟨0, fun a ↦
    G.jacobian_eq_zero_of_riemannRoch_of_genus_zero hRR hgenus a⟩

/-- The genus-zero numerator is the constant polynomial one. -/
theorem coeff_integralZetaNumerator_zero_of_genus_zero
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (hgenus : G.genus = 0) :
    G.integralZetaNumerator.coeff 0 = 1 := by
  have hboundZero : G.zetaNumeratorBound = 0 := by
    simp [zetaNumeratorBound, hgenus]
  have hconst0 : ∀ a : G.Jacobian,
      G.h (G.classInDegree D₁ (0 : ℤ) a) = 1 := by
    intro a
    have ha := G.jacobian_eq_zero_of_riemannRoch_of_genus_zero
      hRR hgenus a
    subst a
    simpa [classInDegree] using G.h_zero
  rw [G.coeff_integralZetaNumerator, if_pos (by omega),
    G.coeff_zetaDenominator_mul_integralZeta_zero,
    G.integralZetaCoefficient_eq_card_nsmul_of_h_constant D₁ 0 1 hconst0,
    G.card_jacobian_eq_one_of_riemannRoch_of_genus_zero hRR hgenus]
  simp [geometricPolynomial_succ]

/-- Uniform leading-coefficient formula, including the genus-zero boundary
case. -/
theorem coeff_integralZetaNumerator_zetaNumeratorBound
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1) :
    G.integralZetaNumerator.coeff G.zetaNumeratorBound =
      Polynomial.X ^ G.genus.toNat := by
  have hgenusNonneg := G.genus_nonneg_of_riemannRoch hRR
  by_cases hgenusPos : 1 ≤ G.genus
  · exact G.coeff_integralZetaNumerator_zetaNumeratorBound_of_genus_pos
      hRR D₁ hgenusPos
  · have hgenusZero : G.genus = 0 := by omega
    have hboundZero : G.zetaNumeratorBound = 0 := by
      simp [zetaNumeratorBound, hgenusZero]
    rw [hboundZero, G.coeff_integralZetaNumerator_zero_of_genus_zero
      hRR D₁ hgenusZero, hgenusZero]
    simp

/-- The numerator has exact `t`-degree `2g`. -/
theorem natDegree_integralZetaNumerator
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1) :
    G.integralZetaNumerator.natDegree = G.zetaNumeratorBound := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · have hlt := PowerSeries.natDegree_trunc_lt
      (zetaDenominator * G.integralZeta) G.zetaNumeratorBound
    change G.integralZetaNumerator.natDegree <
      G.zetaNumeratorBound + 1 at hlt
    omega
  · rw [G.coeff_integralZetaNumerator_zetaNumeratorBound hRR D₁]
    exact pow_ne_zero _ Polynomial.X_ne_zero

/-- Evaluating the numerator at `t = 1` gives the Jacobian order, the final
normalization assertion in Proposition 3.3. -/
theorem eval_one_integralZetaNumerator
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1) :
    Polynomial.eval 1 G.integralZetaNumerator =
      (Fintype.card G.Jacobian : Polynomial ℤ) := by
  have hgenusNonneg : 0 ≤ G.genus :=
    G.genus_nonneg_of_riemannRoch hRR
  by_cases hgenusZero : G.genus = 0
  · have hboundZero : G.zetaNumeratorBound = 0 := by
      simp [zetaNumeratorBound, hgenusZero]
    have hconst0 : ∀ a : G.Jacobian,
        G.h (G.classInDegree D₁ (0 : ℤ) a) = 1 := by
      intro a
      have ha := G.jacobian_eq_zero_of_riemannRoch_of_genus_zero
        hRR hgenusZero a
      subst a
      simpa [classInDegree] using G.h_zero
    have heval :
        Polynomial.eval 1 G.integralZetaNumerator =
          ∑ i ∈ Finset.range 1,
            PowerSeries.coeff i
              (zetaDenominator * G.integralZeta) := by
      simpa only [integralZetaNumerator, hboundZero, zero_add,
          Polynomial.eval₂_id, RingHom.id_apply, one_pow, mul_one] using
        (PowerSeries.eval₂_trunc_eq_sum_range
          (1 : Polynomial ℤ) (RingHom.id (Polynomial ℤ)) 1
          (zetaDenominator * G.integralZeta))
    rw [heval]
    simp only [Finset.sum_range_one]
    rw [G.coeff_zetaDenominator_mul_integralZeta_zero,
      G.integralZetaCoefficient_eq_card_nsmul_of_h_constant
        D₁ 0 1 hconst0]
    simp [geometricPolynomial]
  · have hgenusPos : 1 ≤ G.genus := by omega
    have hboundPos : 1 ≤ G.zetaNumeratorBound := by
      unfold zetaNumeratorBound
      have htoNat : 1 ≤ G.genus.toNat := by omega
      omega
    have heval :
        Polynomial.eval 1 G.integralZetaNumerator =
          ∑ i ∈ Finset.range (G.zetaNumeratorBound + 1),
            PowerSeries.coeff i
              (zetaDenominator * G.integralZeta) := by
      simpa only [integralZetaNumerator,
          Polynomial.eval₂_id, RingHom.id_apply,
          one_pow, mul_one] using
        (PowerSeries.eval₂_trunc_eq_sum_range
          (1 : Polynomial ℤ) (RingHom.id (Polynomial ℤ))
          (G.zetaNumeratorBound + 1)
          (zetaDenominator * G.integralZeta))
    rw [heval,
      G.sum_coeff_zetaDenominator_mul_integralZeta
        G.zetaNumeratorBound hboundPos,
      G.integralZetaCoefficient_zetaNumeratorBound
        hRR D₁ hgenusPos,
      G.integralZetaCoefficient_zetaNumeratorBound_sub_one
        hRR D₁ hgenusPos]
    have hrec := congrArg
      (fun p : Polynomial ℤ ↦
        (Fintype.card G.Jacobian : Polynomial ℤ) * p)
      (geometricPolynomial_succ_sub_X_mul
        (R := ℤ) G.genus.toNat)
    simp only [mul_one] at hrec
    simp only [nsmul_eq_mul]
    linear_combination hrec

/-- The truncated candidate is the actual numerator: multiplication by the
paper's denominator has no terms beyond degree `2g`. -/
theorem zetaDenominator_mul_integralZeta_eq_integralZetaNumerator
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1) :
    zetaDenominator * G.integralZeta =
      (G.integralZetaNumerator : PowerSeries (Polynomial ℤ)) := by
  apply PowerSeries.ext
  intro d
  rw [Polynomial.coeff_coe, G.coeff_integralZetaNumerator]
  by_cases hd : d ≤ G.zetaNumeratorBound
  · simp only [if_pos hd]
  · simp only [if_neg hd]
    exact G.coeff_zetaDenominator_mul_integralZeta_eq_zero_of_bound_lt
      hRR D₁ d (Nat.lt_of_not_ge hd)

/-- Integral rationality identity in the factored form stated in
Proposition 3.3. -/
theorem integralZeta_rationality
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1) :
    (1 - PowerSeries.X) *
        (1 - PowerSeries.C (Polynomial.X : Polynomial ℤ) * PowerSeries.X) *
        G.integralZeta =
      (G.integralZetaNumerator : PowerSeries (Polynomial ℤ)) := by
  rw [← zetaDenominator_eq_factored]
  exact G.zetaDenominator_mul_integralZeta_eq_integralZetaNumerator hRR D₁

/-- Proposition 3.3 in paper-facing form.  For a connected graph, the
explicit integral numerator has degree `2g`, evaluates at `t = 1` to the
Jacobian order, and gives the required rationality identity. -/
theorem proposition_3_3
    (G : LooplessMultigraph V) [Fact G.Connected] :
    ∃ f : Polynomial (Polynomial ℤ),
      (1 - PowerSeries.X) *
          (1 - PowerSeries.C (Polynomial.X : Polynomial ℤ) *
            PowerSeries.X) *
          G.integralZeta = (f : PowerSeries (Polynomial ℤ)) ∧
        f.natDegree = G.zetaNumeratorBound ∧
        Polynomial.eval 1 f =
          (Fintype.card G.Jacobian : Polynomial ℤ) := by
  let v : V := Classical.choice (inferInstance : Nonempty V)
  let D₁ : G.PicardDegree 1 := G.vertexClass v
  have hRR : G.RiemannRochFormula :=
    G.riemannRochFormula_of_connected (Fact.out : G.Connected)
  refine ⟨G.integralZetaNumerator,
    G.integralZeta_rationality hRR D₁,
    G.natDegree_integralZetaNumerator hRR D₁,
    G.eval_one_integralZetaNumerator hRR D₁⟩

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
