import LeanCo.LaplacianLFunctions.Proposition38
import LeanCo.LaplacianLFunctions.ZetaRationality

/-!
# Low-genus formulas

This file formalizes the generic genus-zero and genus-one formulas displayed
after Proposition 3.3 and Proposition 3.8 of arXiv:2608.29981.  The two
polynomial variables are represented by nested polynomial rings: the outer
variable is `t`, while the inner variable is `u`.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- In genus zero the numerator from Proposition 3.3 is exactly `1`. -/
theorem integralZetaNumerator_eq_one_of_genus_zero
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (hgenus : G.genus = 0) :
    G.integralZetaNumerator = 1 := by
  apply Polynomial.ext
  intro d
  have hbound : G.zetaNumeratorBound = 0 := by
    simp [zetaNumeratorBound, hgenus]
  by_cases hd : d = 0
  · subst d
    simpa using
      G.coeff_integralZetaNumerator_zero_of_genus_zero hRR D₁ hgenus
  · rw [G.coeff_integralZetaNumerator]
    have hnot : ¬d ≤ G.zetaNumeratorBound := by
      simpa only [hbound, Nat.le_zero] using hd
    simp [hnot, Polynomial.coeff_one, hd]

/-- The genus-zero zeta identity in the division-free formal-series form
corresponding to `zeta = 1 / ((1-t)(1-ut))`. -/
theorem integralZeta_genus_zero
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (hgenus : G.genus = 0) :
    (1 - PowerSeries.X) *
        (1 - PowerSeries.C (Polynomial.X : Polynomial ℤ) *
          PowerSeries.X) *
        G.integralZeta = 1 := by
  rw [G.integralZeta_rationality hRR D₁,
    G.integralZetaNumerator_eq_one_of_genus_zero hRR D₁ hgenus]
  simp

/-- The numerator `1 + (κ-(u+1))t + ut²` from the genus-one example. -/
def genusOneZetaNumerator (G : LooplessMultigraph V)
    [Fintype G.Jacobian] : Polynomial (Polynomial ℤ) :=
  1 +
    Polynomial.C
        ((Fintype.card G.Jacobian : Polynomial ℤ) -
          (Polynomial.X + 1)) * Polynomial.X +
    Polynomial.C (Polynomial.X : Polynomial ℤ) * Polynomial.X ^ 2

theorem coeff_genusOneZetaNumerator
    (G : LooplessMultigraph V) [Fintype G.Jacobian] (d : ℕ) :
    G.genusOneZetaNumerator.coeff d =
      if d = 0 then 1
      else if d = 1 then
        (Fintype.card G.Jacobian : Polynomial ℤ) -
          (Polynomial.X + 1)
      else if d = 2 then Polynomial.X else 0 := by
  rw [genusOneZetaNumerator, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_one, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  split_ifs <;> simp_all

/-- In genus one, Proposition 3.3's canonical numerator has the paper's
explicit three-term formula. -/
theorem integralZetaNumerator_eq_genusOneZetaNumerator
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (hgenus : G.genus = 1) :
    G.integralZetaNumerator = G.genusOneZetaNumerator := by
  have hgenusPos : 1 ≤ G.genus := by omega
  have hbound : G.zetaNumeratorBound = 2 := by
    simp [zetaNumeratorBound, hgenus]
  have hRRBound : G.riemannRochBound = 0 := by
    simp [riemannRochBound, hgenus]
  have hzetaZero : G.integralZetaCoefficient 0 = 1 := by
    have hcanonical :=
      G.integralZetaCoefficient_riemannRochBound hRR D₁ hgenusPos
    rw [hRRBound] at hcanonical
    simpa [hgenus, geometricPolynomial] using hcanonical
  have hzetaOne :
      G.integralZetaCoefficient 1 =
        (Fintype.card G.Jacobian : Polynomial ℤ) := by
    have hhigh :=
      G.integralZetaCoefficient_eq_card_nsmul_of_riemannRoch_of_gt
        hRR D₁ 1 1 (by omega) (by omega)
    simpa [hgenus, geometricPolynomial] using hhigh
  have hcoeffZero : G.integralZetaNumerator.coeff 0 = 1 := by
    rw [G.coeff_integralZetaNumerator, if_pos (by omega),
      G.coeff_zetaDenominator_mul_integralZeta_zero, hzetaZero]
  have hcoeffOne :
      G.integralZetaNumerator.coeff 1 =
        (Fintype.card G.Jacobian : Polynomial ℤ) -
          (Polynomial.X + 1) := by
    rw [G.coeff_integralZetaNumerator, if_pos (by omega),
      G.coeff_zetaDenominator_mul_integralZeta_one, hzetaOne, hzetaZero]
    ring
  have hcoeffTwo :
      G.integralZetaNumerator.coeff 2 = Polynomial.X := by
    have hlead :=
      G.coeff_integralZetaNumerator_zetaNumeratorBound hRR D₁
    simpa [hbound, hgenus] using hlead
  apply Polynomial.ext
  intro d
  by_cases hd : d ≤ 2
  · interval_cases d
    · rw [hcoeffZero]
      simp [G.coeff_genusOneZetaNumerator]
    · rw [hcoeffOne]
      simp [G.coeff_genusOneZetaNumerator]
    · rw [hcoeffTwo]
      simp [G.coeff_genusOneZetaNumerator]
  · have hnot : ¬d ≤ G.zetaNumeratorBound := by
      simpa only [hbound] using hd
    rw [G.coeff_integralZetaNumerator, if_neg hnot]
    rw [G.coeff_genusOneZetaNumerator]
    simp only [if_neg (by omega : d ≠ 0),
      if_neg (by omega : d ≠ 1), if_neg (by omega : d ≠ 2)]

/-- The genus-one zeta formula, expressed without division in the formal
power-series ring. -/
theorem integralZeta_genus_one
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (hgenus : G.genus = 1) :
    (1 - PowerSeries.X) *
        (1 - PowerSeries.C (Polynomial.X : Polynomial ℤ) *
          PowerSeries.X) *
        G.integralZeta =
      (G.genusOneZetaNumerator : PowerSeries (Polynomial ℤ)) := by
  rw [G.integralZeta_rationality hRR D₁,
    G.integralZetaNumerator_eq_genusOneZetaNumerator hRR D₁ hgenus]

/-- In genus one the canonical divisor class is zero. -/
theorem canonicalClass_eq_zero_of_riemannRoch_of_genus_one
    (G : LooplessMultigraph V) (hRR : G.RiemannRochFormula)
    (hgenus : G.genus = 1) :
    G.canonicalClass = 0 := by
  have hvalue : G.h G.canonicalClass = 1 := by
    simpa [hgenus] using
      G.h_canonicalClass_of_riemannRoch hRR (by omega)
  have heffective : G.HasEffectiveRepresentative G.canonicalClass :=
    (G.h_pos_iff_hasEffectiveRepresentative G.canonicalClass).1 (by omega)
  apply (G.hasEffectiveRepresentative_of_degree_zero_iff
    G.canonicalClass (by simp [G.picardDegree_canonicalClass, hgenus])).1
  exact heffective

/-- The genus-one truncation of a nontrivial `L`-function is the constant
polynomial `1`. -/
theorem lPolynomial_eq_one_of_genus_one
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (chi : AddChar G.Jacobian ℂ) (hchi : chi ≠ 1)
    (hgenus : G.genus = 1) :
    G.lPolynomial D₁ chi G.riemannRochBound = 1 := by
  have hbound : G.riemannRochBound = 0 := by
    simp [riemannRochBound, hgenus]
  have hcanonical : G.canonicalClass = 0 :=
    G.canonicalClass_eq_zero_of_riemannRoch_of_genus_one hRR hgenus
  have hcoordinate : G.canonicalCoordinate D₁ = 0 := by
    rw [canonicalCoordinate, hcanonical]
    exact G.jacobianCoordinate_zero D₁
  have hcoefficient : G.lCoefficient D₁ chi 0 = 1 := by
    have hlead := G.lCoefficient_riemannRochBound hRR D₁ chi hchi (by omega)
    rw [hbound, hcoordinate] at hlead
    simpa [hgenus] using hlead
  apply Polynomial.ext
  intro d
  rw [G.coeff_lPolynomial]
  by_cases hd : d = 0
  · subst d
    simp [hbound, hcoefficient]
  · have hnot : ¬d ≤ G.riemannRochBound := by
      simpa only [hbound, Nat.le_zero] using hd
    simp [hnot, Polynomial.coeff_one, hd]

/-- The nontrivial-character genus-one example from Proposition 3.8:
`L(t,u,G,chi) = 1`. -/
theorem nontrivial_lFunction_eq_one_of_genus_one
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (D₁ : G.PicardDegree 1)
    (chi : AddChar G.Jacobian ℂ) (hchi : chi ≠ 1)
    (hgenus : G.genus = 1) :
    G.lFunction D₁ chi = 1 := by
  rw [G.lFunction_eq_lPolynomial_of_riemannRoch hRR D₁ chi hchi,
    G.lPolynomial_eq_one_of_genus_one hRR D₁ chi hchi hgenus]
  simp

/-- Connected-graph form of the genus-zero example, with no separately
exposed Riemann--Roch premise. -/
theorem genus_zero_zeta_example
    (G : LooplessMultigraph V) [Fact G.Connected]
    (hgenus : G.genus = 0) :
    G.integralZetaNumerator = 1 ∧
      (1 - PowerSeries.X) *
          (1 - PowerSeries.C (Polynomial.X : Polynomial ℤ) *
            PowerSeries.X) *
          G.integralZeta = 1 := by
  let v : V := Classical.choice (inferInstance : Nonempty V)
  let D₁ : G.PicardDegree 1 := G.vertexClass v
  have hRR := G.riemannRochFormula_of_connected (Fact.out : G.Connected)
  exact ⟨G.integralZetaNumerator_eq_one_of_genus_zero hRR D₁ hgenus,
    G.integralZeta_genus_zero hRR D₁ hgenus⟩

/-- Connected-graph form of the genus-one zeta example. -/
theorem genus_one_zeta_example
    (G : LooplessMultigraph V) [Fact G.Connected]
    (hgenus : G.genus = 1) :
    G.integralZetaNumerator = G.genusOneZetaNumerator ∧
      (1 - PowerSeries.X) *
          (1 - PowerSeries.C (Polynomial.X : Polynomial ℤ) *
            PowerSeries.X) *
          G.integralZeta =
        (G.genusOneZetaNumerator : PowerSeries (Polynomial ℤ)) := by
  let v : V := Classical.choice (inferInstance : Nonempty V)
  let D₁ : G.PicardDegree 1 := G.vertexClass v
  have hRR := G.riemannRochFormula_of_connected (Fact.out : G.Connected)
  exact ⟨G.integralZetaNumerator_eq_genusOneZetaNumerator hRR D₁ hgenus,
    G.integralZeta_genus_one hRR D₁ hgenus⟩

/-- Connected-graph form of the genus-one nontrivial-character example. -/
theorem genus_one_nontrivial_lFunction_example
    (G : LooplessMultigraph V) [Fact G.Connected]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (hchi : chi ≠ 1) (hgenus : G.genus = 1) :
    G.lFunction D₁ chi = 1 := by
  exact G.nontrivial_lFunction_eq_one_of_genus_one
    (G.riemannRochFormula_of_connected (Fact.out : G.Connected))
    D₁ chi hchi hgenus

/-! ## The generic genus-two nontrivial-character formula -/

/-- A loopless multigraph on a subsingleton vertex type has no edges. -/
theorem edgeCount_eq_zero_of_subsingleton
    (G : LooplessMultigraph V) [Subsingleton V] :
    G.edgeCount = 0 := by
  classical
  rw [edgeCount]
  apply Finset.sum_eq_zero
  intro e he
  rcases e with ⟨v, w⟩
  have hvw : v = w := Subsingleton.elim v w
  subst w
  simp

/-- A genus-two loopless multigraph necessarily has at least two vertices. -/
theorem nontrivial_of_genus_eq_two
    (G : LooplessMultigraph V) (hgenus : G.genus = 2) :
    Nontrivial V := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsubsingleton
  letI : Subsingleton V := hsubsingleton
  have hedge : G.edgeCount = 0 := G.edgeCount_eq_zero_of_subsingleton
  have hcard : Fintype.card V = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    exact ⟨Classical.choice (inferInstance : Nonempty V),
      fun v ↦ Subsingleton.elim v _⟩
  rw [genus, hedge, hcard] at hgenus
  norm_num at hgenus

/-- On a bridge-free graph with at least two vertices, every vertex class
has Baker--Norine `h` equal to one. -/
theorem h_vertexClass_eq_one_of_bridgeFree
    (G : LooplessMultigraph V) (hbridge : G.BridgeFree)
    [Nontrivial V] (v : V) :
    G.h (G.vertexClass v : G.Picard) = 1 := by
  have hpositive : 0 < G.h (G.vertexClass v : G.Picard) :=
    (G.h_pos_iff_hasEffectiveRepresentative
      (G.vertexClass v : G.Picard)).2
      (G.hasEffectiveRepresentative_divisorClass_of_effective
        (Divisor.isEffective_vertexDivisor v))
  obtain ⟨w, hw⟩ := exists_ne v
  have hle : G.h (G.vertexClass v : G.Picard) ≤ 1 := by
    apply G.h_min
    refine ⟨Divisor.vertexDivisor w,
      Divisor.isEffective_vertexDivisor w,
      Divisor.degree_vertexDivisor w, ?_⟩
    intro heffective
    have hdegree :
        G.picardDegree
            ((G.vertexClass v : G.Picard) -
              G.divisorClass (Divisor.vertexDivisor w)) = 0 := by
      rw [LinearMap.map_sub, (G.vertexClass v).2,
        G.picardDegree_divisorClass,
        Divisor.degree_vertexDivisor]
      simp
    have hzero :=
      (G.hasEffectiveRepresentative_of_degree_zero_iff _ hdegree).1
        heffective
    have hclasses : G.vertexClass v = G.vertexClass w := by
      apply Subtype.ext
      simpa only [G.vertexClass_coe] using
        (sub_eq_zero.mp hzero)
    exact hw (G.vertexClass_injective_of_bridgeFree hbridge hclasses).symm
  omega

/-- Jacobian coordinate of a vertex class relative to `D₁`; this is the
paper's element `v-D₁`. -/
def vertexCoordinate (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (v : V) : G.Jacobian :=
  G.jacobianCoordinate D₁ (G.vertexClass v : G.Picard)

/-- Bridge-freeness makes the vertex-coordinate map injective. -/
theorem vertexCoordinate_injective_of_bridgeFree
    (G : LooplessMultigraph V) (hbridge : G.BridgeFree)
    (D₁ : G.PicardDegree 1) :
    Function.Injective (G.vertexCoordinate D₁) := by
  intro v w hvw
  apply G.vertexClass_injective_of_bridgeFree hbridge
  apply Subtype.ext
  have hv := G.jacobianCoordinate_add_degree D₁
    (G.vertexClass v : G.Picard)
  have hw := G.jacobianCoordinate_add_degree D₁
    (G.vertexClass w : G.Picard)
  rw [(G.vertexClass v).2] at hv
  rw [(G.vertexClass w).2] at hw
  calc
    (G.vertexClass v : G.Picard) =
        (G.vertexCoordinate D₁ v : G.Picard) +
          (1 : ℤ) • (D₁ : G.Picard) := hv.symm
    _ = (G.vertexCoordinate D₁ w : G.Picard) +
          (1 : ℤ) • (D₁ : G.Picard) := by rw [hvw]
    _ = (G.vertexClass w : G.Picard) := hw

/-- The set of degree-one effective classes, written in Jacobian
coordinates. -/
def vertexCoordinates (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) : Finset G.Jacobian := by
  classical
  exact Finset.univ.image (G.vertexCoordinate D₁)

/-- Recombining the coordinate of a vertex class in degree one recovers the
vertex class. -/
theorem classInDegree_one_vertexCoordinate
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1) (v : V) :
    G.classInDegree D₁ 1 (G.vertexCoordinate D₁ v) =
      (G.vertexClass v : G.Picard) := by
  have h := G.jacobianCoordinate_add_degree D₁
    (G.vertexClass v : G.Picard)
  rw [(G.vertexClass v).2] at h
  exact h

/-- Membership in the vertex-coordinate image is exactly effectiveness of
the corresponding degree-one Picard class. -/
theorem mem_vertexCoordinates_iff_hasEffectiveRepresentative
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (a : G.Jacobian) :
    a ∈ G.vertexCoordinates D₁ ↔
      G.HasEffectiveRepresentative (G.classInDegree D₁ 1 a) := by
  classical
  constructor
  · rw [vertexCoordinates, Finset.mem_image]
    rintro ⟨v, hv, rfl⟩
    rw [G.classInDegree_one_vertexCoordinate]
    exact G.hasEffectiveRepresentative_divisorClass_of_effective
      (Divisor.isEffective_vertexDivisor v)
  · intro heffective
    let C : G.PicardDegree 1 :=
      ⟨G.classInDegree D₁ 1 a, G.picardDegree_classInDegree D₁ 1 a⟩
    obtain ⟨v, hv⟩ :=
      (G.hasEffectiveRepresentative_degree_one_iff C).1 heffective
    have hv' : (C : G.Picard) = (G.vertexClass v : G.Picard) :=
      congrArg Subtype.val hv
    have hcoordinate : G.vertexCoordinate D₁ v = a := by
      have h := congrArg (G.jacobianCoordinate D₁) hv'
      simpa only [C, vertexCoordinate,
        G.jacobianCoordinate_jacobian_add_zsmul, classInDegree] using h.symm
    rw [vertexCoordinates, Finset.mem_image]
    exact ⟨v, Finset.mem_univ v, hcoordinate⟩

/-- A degree-one class in the vertex-coordinate image has `h=1` on a
bridge-free graph with at least two vertices. -/
theorem h_classInDegree_one_eq_one_of_mem_vertexCoordinates
    (G : LooplessMultigraph V) (hbridge : G.BridgeFree)
    [Nontrivial V] (D₁ : G.PicardDegree 1) (a : G.Jacobian)
    (hmem : a ∈ G.vertexCoordinates D₁) :
    G.h (G.classInDegree D₁ 1 a) = 1 := by
  classical
  rw [vertexCoordinates, Finset.mem_image] at hmem
  obtain ⟨v, hv, hva⟩ := hmem
  rw [← hva, G.classInDegree_one_vertexCoordinate]
  exact G.h_vertexClass_eq_one_of_bridgeFree hbridge v

/-- A degree-one class outside the vertex-coordinate image has `h=0`. -/
theorem h_classInDegree_one_eq_zero_of_not_mem_vertexCoordinates
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (a : G.Jacobian) (hmem : a ∉ G.vertexCoordinates D₁) :
    G.h (G.classInDegree D₁ 1 a) = 0 := by
  apply G.h_eq_zero_of_not_hasEffectiveRepresentative
  intro heffective
  exact hmem
    ((G.mem_vertexCoordinates_iff_hasEffectiveRepresentative D₁ a).2
      heffective)

/-- For a bridge-free graph, the coefficient of `t` in a twisted
`L`-function is the character sum over vertices appearing in the paper. -/
theorem lCoefficient_one_eq_sum_vertexCoordinate
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hbridge : G.BridgeFree) [Nontrivial V]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ) :
    G.lCoefficient D₁ chi 1 =
      Polynomial.C (∑ v : V, chi (G.vertexCoordinate D₁ v)) := by
  classical
  rw [lCoefficient]
  calc
    (∑ a : G.Jacobian,
        Polynomial.C (chi a) *
          geometricPolynomial (R := ℂ)
            (G.h (G.classInDegree D₁ 1 a))) =
        ∑ a : G.Jacobian,
          if a ∈ G.vertexCoordinates D₁ then
            Polynomial.C (chi a) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hmem : a ∈ G.vertexCoordinates D₁
      · rw [G.h_classInDegree_one_eq_one_of_mem_vertexCoordinates
          hbridge D₁ a hmem]
        simp [hmem, geometricPolynomial]
      · rw [G.h_classInDegree_one_eq_zero_of_not_mem_vertexCoordinates
          D₁ a hmem]
        simp [hmem, geometricPolynomial]
    _ = ∑ a ∈ G.vertexCoordinates D₁, Polynomial.C (chi a) := by
      simp
    _ = ∑ v : V, Polynomial.C (chi (G.vertexCoordinate D₁ v)) := by
      rw [vertexCoordinates,
        Finset.sum_image (G.vertexCoordinate_injective_of_bridgeFree
          hbridge D₁).injOn]
    _ = Polynomial.C (∑ v : V, chi (G.vertexCoordinate D₁ v)) := by
      rw [map_sum]

/-- The constant-in-`t` coefficient of every twisted `L`-function is one. -/
theorem lCoefficient_zero_eq_one
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ) :
    G.lCoefficient D₁ chi 0 = 1 := by
  classical
  rw [lCoefficient]
  have hzeroTerm :
      Polynomial.C (chi (0 : G.Jacobian)) *
          geometricPolynomial (R := ℂ)
            (G.h (G.classInDegree D₁ ((0 : ℕ) : ℤ)
              (0 : G.Jacobian))) = 1 := by
    simp [classInDegree, G.h_zero, geometricPolynomial]
  rw [← Finset.add_sum_erase Finset.univ
    (fun a : G.Jacobian ↦
        Polynomial.C (chi a) *
          geometricPolynomial (R := ℂ)
            (G.h (G.classInDegree D₁ ((0 : ℕ) : ℤ) a)))
    (Finset.mem_univ (0 : G.Jacobian)), hzeroTerm]
  have herase :
      (∑ a ∈ (Finset.univ.erase (0 : G.Jacobian)),
        Polynomial.C (chi a) *
          geometricPolynomial (R := ℂ)
            (G.h (G.classInDegree D₁ ((0 : ℕ) : ℤ) a))) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hane : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have hcoeNe : (a : G.Picard) ≠ 0 := by
      intro hzero
      apply hane
      apply Subtype.ext
      exact hzero
    have hh :
        G.h (G.classInDegree D₁ ((0 : ℕ) : ℤ) a) = 0 := by
      apply G.h_eq_zero_of_degree_zero_of_ne_zero
      · exact G.picardDegree_classInDegree D₁ 0 a
      · simpa [classInDegree] using hcoeNe
    rw [hh, geometricPolynomial_zero, mul_zero]
  rw [herase, add_zero]

/-- The polynomial displayed for a nontrivial character in genus two:
`1 + (∑ᵥ chi(v-D₁))t + chi(K-2D₁)ut²`. -/
def genusTwoLPolynomial (G : LooplessMultigraph V)
    [Fintype G.Jacobian] (D₁ : G.PicardDegree 1)
    (chi : AddChar G.Jacobian ℂ) : Polynomial (Polynomial ℂ) :=
  1 +
    Polynomial.C
        (Polynomial.C (∑ v : V, chi (G.vertexCoordinate D₁ v))) *
      Polynomial.X +
    Polynomial.C
        (Polynomial.C (chi (G.canonicalCoordinate D₁)) * Polynomial.X) *
      Polynomial.X ^ 2

theorem coeff_genusTwoLPolynomial
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ) (d : ℕ) :
    (G.genusTwoLPolynomial D₁ chi).coeff d =
      if d = 0 then 1
      else if d = 1 then
        Polynomial.C (∑ v : V, chi (G.vertexCoordinate D₁ v))
      else if d = 2 then
        Polynomial.C (chi (G.canonicalCoordinate D₁)) * Polynomial.X
      else 0 := by
  rw [genusTwoLPolynomial, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_one, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  split_ifs <;> simp_all

/-- In genus two, on a bridge-free graph, the finite polynomial furnished
by Proposition 3.8 is exactly the three-term polynomial displayed in the
paper. -/
theorem lPolynomial_eq_genusTwoLPolynomial
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (hbridge : G.BridgeFree)
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (hchi : chi ≠ 1) (hgenus : G.genus = 2) :
    G.lPolynomial D₁ chi G.riemannRochBound =
      G.genusTwoLPolynomial D₁ chi := by
  letI : Nontrivial V := G.nontrivial_of_genus_eq_two hgenus
  have hbound : G.riemannRochBound = 2 := by
    simp [riemannRochBound, hgenus]
  have hcoeffZero :
      (G.lPolynomial D₁ chi G.riemannRochBound).coeff 0 = 1 := by
    rw [G.coeff_lPolynomial, if_pos (by omega),
      G.lCoefficient_zero_eq_one]
  have hcoeffOne :
      (G.lPolynomial D₁ chi G.riemannRochBound).coeff 1 =
        Polynomial.C (∑ v : V, chi (G.vertexCoordinate D₁ v)) := by
    rw [G.coeff_lPolynomial, if_pos (by omega),
      G.lCoefficient_one_eq_sum_vertexCoordinate hbridge]
  have hcoeffTwo :
      (G.lPolynomial D₁ chi G.riemannRochBound).coeff 2 =
        Polynomial.C (chi (G.canonicalCoordinate D₁)) * Polynomial.X := by
    rw [G.coeff_lPolynomial, if_pos (by omega)]
    have hlead :=
      G.lCoefficient_riemannRochBound hRR D₁ chi hchi (by omega)
    simpa [hbound, hgenus] using hlead
  apply Polynomial.ext
  intro d
  by_cases hd : d ≤ 2
  · interval_cases d
    · rw [hcoeffZero]
      simp [G.coeff_genusTwoLPolynomial]
    · rw [hcoeffOne]
      simp [G.coeff_genusTwoLPolynomial]
    · rw [hcoeffTwo]
      simp [G.coeff_genusTwoLPolynomial]
  · rw [G.coeff_lPolynomial, if_neg (by simpa only [hbound] using hd),
      G.coeff_genusTwoLPolynomial]
    simp only [if_neg (by omega : d ≠ 0),
      if_neg (by omega : d ≠ 1), if_neg (by omega : d ≠ 2)]

/-- The full genus-two nontrivial-character `L`-function formula. -/
theorem nontrivial_lFunction_eq_genusTwoLPolynomial
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (hRR : G.RiemannRochFormula) (hbridge : G.BridgeFree)
    (D₁ : G.PicardDegree 1) (chi : AddChar G.Jacobian ℂ)
    (hchi : chi ≠ 1) (hgenus : G.genus = 2) :
    G.lFunction D₁ chi =
      (G.genusTwoLPolynomial D₁ chi :
        PowerSeries (Polynomial ℂ)) := by
  rw [G.lFunction_eq_lPolynomial_of_riemannRoch hRR D₁ chi hchi,
    G.lPolynomial_eq_genusTwoLPolynomial hRR hbridge D₁ chi hchi hgenus]

/-- Connected-graph version of the genus-two formula, exposing only the
paper's graph hypotheses. -/
theorem genus_two_nontrivial_lFunction_example
    (G : LooplessMultigraph V) [Fact G.Connected]
    (hbridge : G.BridgeFree) (D₁ : G.PicardDegree 1)
    (chi : AddChar G.Jacobian ℂ) (hchi : chi ≠ 1)
    (hgenus : G.genus = 2) :
    G.lFunction D₁ chi =
      (G.genusTwoLPolynomial D₁ chi :
        PowerSeries (Polynomial ℂ)) := by
  exact G.nontrivial_lFunction_eq_genusTwoLPolynomial
    (G.riemannRochFormula_of_connected (Fact.out : G.Connected))
    hbridge D₁ chi hchi hgenus


end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
