import LeanCo.LaplacianLFunctions.RiemannRochBridge
import LeanCo.LaplacianLFunctions.LFunctionPolynomial
import LeanCo.LaplacianLFunctions.PicardSplitting

/-!
# Consequences of graph Riemann--Roch

This module gives a paper-facing formulation of Theorem 2.6 and proves the
high-degree consequence used in Propositions 3.3 and 3.8.  The theorem's
combinatorial proof is supplied separately; all downstream generating-series
arguments can depend on the compact `RiemannRochFormula` interface here.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- The Picard class of the canonical divisor. -/
def canonicalClass (G : LooplessMultigraph V) : G.Picard :=
  G.divisorClass G.canonicalDivisor

@[simp]
theorem picardDegree_canonicalClass (G : LooplessMultigraph V) :
    G.picardDegree G.canonicalClass = 2 * G.genus - 2 := by
  rw [canonicalClass, G.picardDegree_divisorClass,
    G.degree_canonicalDivisor]

/-- The class-level form of the Baker--Norine Riemann--Roch formula used in
arXiv:2608.29981, Theorem 2.6. -/
def RiemannRochFormula (G : LooplessMultigraph V) : Prop :=
  ∀ C : G.Picard,
    (G.h C : ℤ) - (G.h (G.canonicalClass - C) : ℤ) =
      G.picardDegree C - G.genus + 1

/-- Every connected loopless multigraph satisfies the class-level
Baker--Norine Riemann--Roch formula. -/
theorem riemannRochFormula_of_connected
    (G : LooplessMultigraph V) (hconn : G.Connected) :
    G.RiemannRochFormula := by
  intro C
  refine Submodule.Quotient.induction_on G.laplacianLattice C ?_
  intro D
  change (G.h (G.divisorClass D) : ℤ) -
      (G.h (G.canonicalClass - G.divisorClass D) : ℤ) =
    Divisor.degree D - G.genus + 1
  simpa [canonicalClass, LinearMap.map_sub] using G.riemann_roch_h hconn D

/-- The zero class has `h = 1`. -/
theorem h_zero (G : LooplessMultigraph V) : G.h 0 = 1 := by
  classical
  have hpos : 0 < G.h 0 :=
    (G.h_pos_iff_hasEffectiveRepresentative 0).2
      ⟨(0 : Divisor V), Divisor.isEffective_zero, by simp⟩
  let v : V := Classical.choice (inferInstance : Nonempty V)
  have hadmissible : G.HAdmissible 0 1 := by
    refine ⟨Divisor.vertexDivisor v,
      Divisor.isEffective_vertexDivisor v,
      Divisor.degree_vertexDivisor v, ?_⟩
    apply G.not_hasEffectiveRepresentative_of_picardDegree_neg
    rw [LinearMap.map_sub, LinearMap.map_zero,
      G.picardDegree_divisorClass, Divisor.degree_vertexDivisor]
    omega
  have hle : G.h 0 ≤ 1 := G.h_min 0 hadmissible
  omega

/-- In degree zero, the only effective Picard class is zero. -/
theorem hasEffectiveRepresentative_of_degree_zero_iff
    (G : LooplessMultigraph V) (C : G.Picard)
    (hdegree : G.picardDegree C = 0) :
    G.HasEffectiveRepresentative C ↔ C = 0 := by
  constructor
  · rintro ⟨D, hD, hclass⟩
    have hDdegree : Divisor.degree D = 0 := by
      calc
        Divisor.degree D = G.picardDegree (G.divisorClass D) :=
          (G.picardDegree_divisorClass D).symm
        _ = G.picardDegree C := congrArg G.picardDegree hclass
        _ = 0 := hdegree
    have hDzero : D = 0 := hD.eq_zero_of_degree_eq_zero hDdegree
    simpa [hDzero] using hclass.symm
  · rintro rfl
    exact ⟨(0 : Divisor V), Divisor.isEffective_zero, by simp⟩

/-- A nonzero degree-zero class has `h = 0`. -/
theorem h_eq_zero_of_degree_zero_of_ne_zero
    (G : LooplessMultigraph V) (C : G.Picard)
    (hdegree : G.picardDegree C = 0) (hC : C ≠ 0) :
    G.h C = 0 := by
  have hnone : ¬ G.HasEffectiveRepresentative C := by
    intro heffective
    exact hC ((G.hasEffectiveRepresentative_of_degree_zero_iff
      C hdegree).1 heffective)
  exact G.h_eq_zero_of_not_hasEffectiveRepresentative C hnone

/-- The Riemann--Roch formula itself forces the graph genus to be
nonnegative. -/
theorem genus_nonneg_of_riemannRoch
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula) :
    0 ≤ G.genus := by
  have hformula := hRR 0
  rw [G.h_zero, sub_zero, LinearMap.map_zero] at hformula
  omega

/-- In genus zero, Riemann--Roch forces every Jacobian element to be zero. -/
theorem jacobian_eq_zero_of_riemannRoch_of_genus_zero
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (hgenus : G.genus = 0) (a : G.Jacobian) :
    a = 0 := by
  apply Subtype.ext
  by_contra hne
  have hdegree : G.picardDegree (a : G.Picard) = 0 := a.2
  have hha := G.h_eq_zero_of_degree_zero_of_ne_zero
    (a : G.Picard) hdegree hne
  have hformula := hRR (a : G.Picard)
  rw [hha, hdegree, hgenus] at hformula
  omega

/-- A nontrivial character can exist only in positive genus. -/
theorem genus_pos_of_riemannRoch_of_nontrivial_character
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (chi : AddChar G.Jacobian ℂ) (hchi : chi ≠ 1) :
    1 ≤ G.genus := by
  have hnonneg := G.genus_nonneg_of_riemannRoch hRR
  by_contra hnot
  have hzero : G.genus = 0 := by omega
  apply hchi
  ext a
  have ha := G.jacobian_eq_zero_of_riemannRoch_of_genus_zero hRR hzero a
  subst a
  simp

/-- Riemann--Roch makes `h(C)` equal to `deg(C)-g+1` above canonical
degree. -/
theorem intCast_h_eq_degree_sub_genus_add_one_of_gt
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (C : G.Picard)
    (hdegree : 2 * G.genus - 2 < G.picardDegree C) :
    (G.h C : ℤ) = G.picardDegree C - G.genus + 1 := by
  have hresDegree : G.picardDegree (G.canonicalClass - C) < 0 := by
    rw [LinearMap.map_sub, G.picardDegree_canonicalClass]
    omega
  have hresNone :=
    G.not_hasEffectiveRepresentative_of_picardDegree_neg
      (G.canonicalClass - C) hresDegree
  have hresZero :=
    G.h_eq_zero_of_not_hasEffectiveRepresentative
      (G.canonicalClass - C) hresNone
  have hformula := hRR C
  simpa [hresZero] using hformula

/-- Riemann--Roch determines `h` of the canonical class. -/
theorem h_canonicalClass_of_riemannRoch
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (hgenus : 0 ≤ G.genus) :
    G.h G.canonicalClass = G.genus.toNat := by
  have hformula := hRR G.canonicalClass
  have hgenusCast : (G.genus.toNat : ℤ) = G.genus :=
    Int.toNat_of_nonneg hgenus
  rw [sub_self, G.h_zero, G.picardDegree_canonicalClass] at hformula
  omega

/-- At canonical degree, every class other than the canonical class has
`h = g-1`. -/
theorem h_eq_genus_toNat_sub_one_of_degree_eq_canonical_of_ne
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (hgenus : 1 ≤ G.genus) (C : G.Picard)
    (hdegree : G.picardDegree C = 2 * G.genus - 2)
    (hne : C ≠ G.canonicalClass) :
    G.h C = G.genus.toNat - 1 := by
  have hresDegree : G.picardDegree (G.canonicalClass - C) = 0 := by
    rw [LinearMap.map_sub, G.picardDegree_canonicalClass, hdegree]
    simp
  have hresNe : G.canonicalClass - C ≠ 0 := by
    simpa [sub_eq_zero] using Ne.symm hne
  have hresZero := G.h_eq_zero_of_degree_zero_of_ne_zero
    (G.canonicalClass - C) hresDegree hresNe
  have hformula := hRR C
  have hgenusNonneg : 0 ≤ G.genus := le_trans (by omega) hgenus
  have hgenusCast : (G.genus.toNat : ℤ) = G.genus :=
    Int.toNat_of_nonneg hgenusNonneg
  rw [hresZero, hdegree] at hformula
  omega

/-- Above canonical degree, `h` is constant across every fixed-degree
Picard torsor. -/
theorem h_classInDegree_constant_of_riemannRoch
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (D₁ : G.PicardDegree 1) (d : ℕ)
    (hdegree : 2 * G.genus - 2 < (d : ℤ)) :
    ∃ n : ℕ, ∀ a : G.Jacobian,
      G.h (G.classInDegree D₁ (d : ℤ) a) = n := by
  let n := G.h (G.classInDegree D₁ (d : ℤ) 0)
  refine ⟨n, ?_⟩
  intro a
  apply Int.ofNat_injective
  calc
    (G.h (G.classInDegree D₁ (d : ℤ) a) : ℤ) =
        (d : ℤ) - G.genus + 1 := by
      have ha := G.intCast_h_eq_degree_sub_genus_add_one_of_gt hRR
        (G.classInDegree D₁ (d : ℤ) a) (by simpa using hdegree)
      simpa using ha
    _ = (G.h (G.classInDegree D₁ (d : ℤ) 0) : ℤ) := by
      symm
      have hzero := G.intCast_h_eq_degree_sub_genus_add_one_of_gt hRR
        (G.classInDegree D₁ (d : ℤ) 0) (by simpa using hdegree)
      simpa using hzero

/-- The natural-number truncation bound corresponding to canonical degree
`2g-2`. -/
def riemannRochBound (G : LooplessMultigraph V) : ℕ :=
  (2 * G.genus - 2).toNat

/-- Jacobian coordinate of the canonical class relative to `D₁`. -/
def canonicalCoordinate (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) : G.Jacobian :=
  G.jacobianCoordinate D₁ G.canonicalClass

theorem intCast_riemannRochBound_of_genus_pos
    (G : LooplessMultigraph V) (hgenus : 1 ≤ G.genus) :
    (G.riemannRochBound : ℤ) = 2 * G.genus - 2 := by
  rw [riemannRochBound, Int.toNat_of_nonneg (by omega)]

/-- In canonical degree, the canonical Jacobian coordinate reconstructs the
canonical Picard class. -/
theorem classInDegree_riemannRochBound_canonicalCoordinate
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (hgenus : 1 ≤ G.genus) :
    G.classInDegree D₁ (G.riemannRochBound : ℤ)
        (G.canonicalCoordinate D₁) = G.canonicalClass := by
  rw [classInDegree, canonicalCoordinate,
    G.intCast_riemannRochBound_of_genus_pos hgenus,
    ← G.picardDegree_canonicalClass]
  exact G.jacobianCoordinate_add_degree D₁ G.canonicalClass

/-- No other Jacobian coordinate represents the canonical class in
canonical degree. -/
theorem classInDegree_riemannRochBound_ne_canonicalClass
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (a : G.Jacobian) (hne : a ≠ G.canonicalCoordinate D₁) :
    G.classInDegree D₁ (G.riemannRochBound : ℤ) a ≠
      G.canonicalClass := by
  intro heq
  apply hne
  calc
    a = G.jacobianCoordinate D₁
        (G.classInDegree D₁ (G.riemannRochBound : ℤ) a) := by
      symm
      exact G.jacobianCoordinate_jacobian_add_zsmul D₁ a _
    _ = G.jacobianCoordinate D₁ G.canonicalClass :=
      congrArg (G.jacobianCoordinate D₁) heq
    _ = G.canonicalCoordinate D₁ := rfl

/-- At the distinguished canonical coordinate, `h=g`. -/
theorem h_classInDegree_canonicalCoordinate_of_riemannRoch
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (D₁ : G.PicardDegree 1) (hgenus : 1 ≤ G.genus) :
    G.h (G.classInDegree D₁ (G.riemannRochBound : ℤ)
      (G.canonicalCoordinate D₁)) = G.genus.toNat := by
  rw [G.classInDegree_riemannRochBound_canonicalCoordinate D₁ hgenus]
  exact G.h_canonicalClass_of_riemannRoch hRR (by omega)

/-- At every other coordinate of canonical degree, `h=g-1`. -/
theorem h_classInDegree_eq_genus_toNat_sub_one_of_ne_canonicalCoordinate
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (D₁ : G.PicardDegree 1) (hgenus : 1 ≤ G.genus)
    (a : G.Jacobian) (hne : a ≠ G.canonicalCoordinate D₁) :
    G.h (G.classInDegree D₁ (G.riemannRochBound : ℤ) a) =
      G.genus.toNat - 1 := by
  apply G.h_eq_genus_toNat_sub_one_of_degree_eq_canonical_of_ne
    hRR hgenus
  · rw [G.picardDegree_classInDegree,
      G.intCast_riemannRochBound_of_genus_pos hgenus]
  · exact G.classInDegree_riemannRochBound_ne_canonicalClass D₁ a hne

theorem canonicalDegree_lt_intCast_of_bound_lt
    (G : LooplessMultigraph V) {d : ℕ}
    (hd : G.riemannRochBound < d) :
    2 * G.genus - 2 < (d : ℤ) := by
  unfold riemannRochBound at hd
  by_cases hcanonical : 0 ≤ 2 * G.genus - 2
  · rw [← Int.toNat_of_nonneg hcanonical]
    exact_mod_cast hd
  · exact lt_of_lt_of_le (lt_of_not_ge hcanonical) (Int.ofNat_zero_le d)

/-- Riemann--Roch plus character cancellation proves the polynomiality part
of Proposition 3.8. -/
theorem lFunction_eq_lPolynomial_of_riemannRoch
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula)
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (hchi : chi ≠ 1) :
    G.lFunction D₁ chi =
      (G.lPolynomial D₁ chi G.riemannRochBound :
        PowerSeries (Polynomial ℂ)) := by
  apply G.lFunction_eq_lPolynomial_of_h_constant_above
    D₁ chi G.riemannRochBound hchi
  intro d hd
  exact G.h_classInDegree_constant_of_riemannRoch hRR D₁ d
    (G.canonicalDegree_lt_intCast_of_bound_lt hd)

/-- An additive character takes only nonzero values. -/
theorem addChar_apply_ne_zero
    {A : Type*} [AddGroup A] (chi : AddChar A ℂ) (a : A) :
    chi a ≠ 0 := by
  intro hzero
  have hone : (1 : ℂ) = 0 := by
    calc
      1 = chi (a + -a) := by simp
      _ = chi a * chi (-a) := chi.map_add_eq_mul a (-a)
      _ = 0 := by rw [hzero, zero_mul]
  exact one_ne_zero hone

/-- The coefficient in canonical degree is the single monomial computed in
the proof of Proposition 3.8. -/
theorem lCoefficient_riemannRochBound
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula)
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (hchi : chi ≠ 1) (hgenus : 1 ≤ G.genus) :
    G.lCoefficient D₁ chi G.riemannRochBound =
      Polynomial.C (chi (G.canonicalCoordinate D₁)) *
        Polynomial.X ^ (G.genus.toNat - 1) := by
  classical
  let k : G.Jacobian := G.canonicalCoordinate D₁
  let gn : ℕ := G.genus.toNat
  have hk : G.h (G.classInDegree D₁ (G.riemannRochBound : ℤ) k) = gn := by
    simpa [k, gn] using
      G.h_classInDegree_canonicalCoordinate_of_riemannRoch hRR D₁ hgenus
  have hother : ∀ a ∈ (Finset.univ.erase k),
      G.h (G.classInDegree D₁ (G.riemannRochBound : ℤ) a) = gn - 1 := by
    intro a ha
    have hak : a ≠ k := (Finset.mem_erase.mp ha).1
    simpa [k, gn] using
      G.h_classInDegree_eq_genus_toNat_sub_one_of_ne_canonicalCoordinate
        hRR D₁ hgenus a hak
  have hsumComplex : ∑ a : G.Jacobian, chi a = 0 :=
    sum_addChar_eq_zero_of_ne_one chi hchi
  have hsumPolynomial : ∑ a : G.Jacobian, Polynomial.C (chi a) = 0 := by
    rw [← map_sum, hsumComplex, map_zero]
  have hsumErase :
      ∑ a ∈ (Finset.univ.erase k), Polynomial.C (chi a) =
        -Polynomial.C (chi k) := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun a ↦ Polynomial.C (chi a)) (Finset.mem_univ k)] at hsumPolynomial
    exact eq_neg_of_add_eq_zero_right hsumPolynomial
  have hgnCast : (gn : ℤ) = G.genus := by
    exact Int.toNat_of_nonneg (by omega)
  have hgnPos : 0 < gn := by omega
  rw [lCoefficient,
    ← Finset.add_sum_erase Finset.univ
      (fun a ↦ Polynomial.C (chi a) *
        geometricPolynomial
          (G.h (G.classInDegree D₁ (G.riemannRochBound : ℤ) a)))
      (Finset.mem_univ k), hk]
  have herase :
      (∑ a ∈ Finset.univ.erase k,
        Polynomial.C (chi a) *
          geometricPolynomial
            (G.h (G.classInDegree D₁
              (G.riemannRochBound : ℤ) a))) =
        (∑ a ∈ Finset.univ.erase k, Polynomial.C (chi a)) *
          geometricPolynomial (gn - 1) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hother a ha]
  rw [herase, hsumErase]
  change Polynomial.C (chi k) * geometricPolynomial gn +
      (-Polynomial.C (chi k)) * geometricPolynomial (gn - 1) =
    Polynomial.C (chi k) * Polynomial.X ^ (gn - 1)
  have hgeo : geometricPolynomial (R := ℂ) gn =
      geometricPolynomial (gn - 1) + Polynomial.X ^ (gn - 1) := by
    have hsubadd : gn - 1 + 1 = gn := Nat.sub_add_cancel hgnPos
    simpa only [hsubadd] using
      geometricPolynomial_succ (R := ℂ) (gn - 1)
  rw [hgeo]
  ring

/-- Hence the leading coefficient at canonical degree is nonzero. -/
theorem lCoefficient_riemannRochBound_ne_zero
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula)
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (hchi : chi ≠ 1) (hgenus : 1 ≤ G.genus) :
    G.lCoefficient D₁ chi G.riemannRochBound ≠ 0 := by
  rw [G.lCoefficient_riemannRochBound hRR D₁ chi hchi hgenus]
  exact mul_ne_zero
    (Polynomial.C_ne_zero.mpr
      (addChar_apply_ne_zero chi (G.canonicalCoordinate D₁)))
    (pow_ne_zero _ Polynomial.X_ne_zero)

/-- Full nontrivial-character part of Proposition 3.8: the `L`-series is a
polynomial and its `t`-degree is exactly `2g-2` (expressed by the equal
natural truncation bound). -/
theorem nontrivial_lFunction_polynomial_of_riemannRoch
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula)
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (hchi : chi ≠ 1) :
    G.lFunction D₁ chi =
        (G.lPolynomial D₁ chi G.riemannRochBound :
          PowerSeries (Polynomial ℂ)) ∧
      (G.lPolynomial D₁ chi G.riemannRochBound).natDegree =
        G.riemannRochBound := by
  have hgenus :=
    G.genus_pos_of_riemannRoch_of_nontrivial_character hRR chi hchi
  refine ⟨G.lFunction_eq_lPolynomial_of_riemannRoch hRR D₁ chi hchi, ?_⟩
  exact G.natDegree_lPolynomial_eq_of_leading_coeff_ne_zero
    D₁ chi G.riemannRochBound
    (G.lCoefficient_riemannRochBound_ne_zero hRR D₁ chi hchi hgenus)

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
