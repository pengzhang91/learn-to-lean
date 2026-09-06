import LeanCo.LaplacianLFunctions.RiemannRochConsequences
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# The two-vertex triple-edge graph (Example 3.10)

This module gives kernel-checkable certificates for every explicit claim in
Example 3.10 of arXiv:2608.29981: genus two, Jacobian `ZMod 3`, the three
classes of `Pic¹`, and the six displayed twisted `L`-function formulas.
-/

open scoped BigOperators
namespace LeanCo.LaplacianLFunctions
noncomputable section

def example310Mult : Fin 2 → Fin 2 → ℕ := ![![0, 3], ![3, 0]]

def example310 : LooplessMultigraph (Fin 2) where
  multiplicity := example310Mult
  multiplicity_symm i j := by fin_cases i <;> fin_cases j <;> rfl
  multiplicity_self i := by fin_cases i <;> rfl

theorem example310_laplacian_apply (D : Divisor (Fin 2)) :
    example310.laplacian D = ![3 * (D 0 - D 1), 3 * (D 1 - D 0)] := by
  funext i
  fin_cases i <;>
    simp [LooplessMultigraph.laplacian_apply, example310, example310Mult,
      Fin.sum_univ_succ] <;> ring

theorem example310_valency (i : Fin 2) : example310.valency i = 3 := by
  fin_cases i <;>
    simp [LooplessMultigraph.valency, example310, example310Mult,
      Fin.sum_univ_succ]

theorem example310_edgeCount : example310.edgeCount = 3 := by
  have h := example310.sum_valency_eq_two_mul_edgeCount
  simp [example310_valency, Fin.sum_univ_succ] at h
  omega

theorem example310_genus : example310.genus = 2 := by
  simp [LooplessMultigraph.genus, example310_edgeCount]

theorem example310_support_eq_top : example310.support = ⊤ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LooplessMultigraph.support_adj, example310, example310Mult]

theorem example310_connected : example310.Connected := by
  rw [LooplessMultigraph.Connected, example310_support_eq_top]
  simp

theorem example310_bridgeFree : example310.BridgeFree := by
  intro S hS hproper
  fin_cases S <;>
    simp [LooplessMultigraph.cutWeight, example310, example310Mult,
      Fin.sum_univ_succ] at hS hproper ⊢ <;>
    first | omega | exact hproper (by decide)

theorem example310_mem_lattice_iff (D : Divisor (Fin 2)) :
    D ∈ example310.laplacianLattice ↔
      ∃ k : ℤ, D = ![3 * k, -3 * k] := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨f 0 - f 1, ?_⟩
    rw [example310_laplacian_apply]
    funext i
    fin_cases i <;> simp <;> ring
  · rintro ⟨k, rfl⟩
    refine ⟨(![k, 0] : Divisor (Fin 2)), ?_⟩
    rw [example310_laplacian_apply]
    funext i
    fin_cases i <;> simp

def example310GeneratorDivisor : Divisor (Fin 2) := ![-1, 1]

theorem example310GeneratorDivisor_degree :
    Divisor.degree example310GeneratorDivisor = 0 := by
  simp [Divisor.degree, example310GeneratorDivisor, Fin.sum_univ_succ]

def example310Generator : example310.Jacobian :=
  example310.jacobianClass ⟨example310GeneratorDivisor,
    example310GeneratorDivisor_degree⟩

theorem example310_three_zsmul_generator :
    (3 : ℤ) • example310Generator = 0 := by
  apply Subtype.ext
  change example310.divisorClass (3 • example310GeneratorDivisor) = 0
  change Submodule.Quotient.mk (3 • example310GeneratorDivisor) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  rw [example310_mem_lattice_iff]
  refine ⟨-1, ?_⟩
  funext i
  fin_cases i <;> simp [example310GeneratorDivisor]

def example310GeneratorIntHom : ℤ →+ example310.Jacobian where
  toFun n := n • example310Generator
  map_zero' := zero_zsmul _
  map_add' m n := add_zsmul example310Generator m n

def example310FromZMod : ZMod 3 →+ example310.Jacobian :=
  ZMod.lift 3 ⟨example310GeneratorIntHom, by
    simpa [example310GeneratorIntHom] using example310_three_zsmul_generator⟩

@[simp]
theorem example310FromZMod_intCast (n : ℤ) :
    example310FromZMod (n : ZMod 3) = n • example310Generator := by
  simp [example310FromZMod, example310GeneratorIntHom]

def example310CoeffOneModThree : Divisor (Fin 2) →ₗ[ℤ] ZMod 3 where
  toFun D := (D 1 : ZMod 3)
  map_add' D E := by simp
  map_smul' n D := by
    change ((n * D 1 : ℤ) : ZMod 3) = n • (D 1 : ZMod 3)
    simp

theorem example310_lattice_le_coeffOneModThree_ker :
    example310.laplacianLattice ≤ LinearMap.ker example310CoeffOneModThree := by
  rintro D hD
  rw [example310_mem_lattice_iff] at hD
  obtain ⟨k, rfl⟩ := hD
  change ((-3 * k : ℤ) : ZMod 3) = 0
  rw [Int.cast_mul]
  have hthree : ((-3 : ℤ) : ZMod 3) = 0 := by
    apply neg_eq_zero.mpr
    exact ZMod.natCast_self 3
  rw [hthree, zero_mul]

def example310PicardCoord : example310.Picard →ₗ[ℤ] ZMod 3 :=
  example310.laplacianLattice.liftQ example310CoeffOneModThree
    example310_lattice_le_coeffOneModThree_ker

def example310JacobianCoord : example310.Jacobian →+ ZMod 3 where
  toFun a := example310PicardCoord a.1
  map_zero' := by simp
  map_add' a b := by simp

@[simp]
theorem example310JacobianCoord_generator :
    example310JacobianCoord example310Generator = 1 := by
  rfl

theorem example310JacobianCoord_fromZMod (z : ZMod 3) :
    example310JacobianCoord (example310FromZMod z) = z := by
  rw [← ZMod.intCast_zmod_cast z]
  rw [example310FromZMod_intCast]
  change example310JacobianCoord (z.cast • example310Generator) = (z.cast : ZMod 3)
  rw [map_zsmul, example310JacobianCoord_generator]
  simp

theorem example310_every_jacobian_eq_zsmul_generator (a : example310.Jacobian) :
    ∃ n : ℤ, a = n • example310Generator := by
  obtain ⟨D, hD⟩ := Submodule.Quotient.mk_surjective
    example310.laplacianLattice a.1
  have hdeg : Divisor.degree D = 0 := by
    calc
      Divisor.degree D = example310.picardDegree (example310.divisorClass D) :=
        (example310.picardDegree_divisorClass D).symm
      _ = example310.picardDegree a.1 := congrArg example310.picardDegree hD
      _ = 0 := a.2
  have hsum : D 0 + D 1 = 0 := by
    simpa [Divisor.degree, Fin.sum_univ_succ] using hdeg
  refine ⟨D 1, ?_⟩
  apply Subtype.ext
  change a.1 = example310.divisorClass (D 1 • example310GeneratorDivisor)
  rw [← hD]
  apply (example310.divisorClass_eq_iff_sub_mem _ _).mpr
  rw [example310_mem_lattice_iff]
  refine ⟨0, ?_⟩
  funext i
  fin_cases i <;> simp [example310GeneratorDivisor] <;> omega

theorem example310FromZMod_surjective : Function.Surjective example310FromZMod := by
  intro a
  obtain ⟨n, rfl⟩ := example310_every_jacobian_eq_zsmul_generator a
  refine ⟨(n : ZMod 3), ?_⟩
  exact example310FromZMod_intCast n

theorem example310FromZMod_injective : Function.Injective example310FromZMod := by
  intro x y hxy
  have := congrArg example310JacobianCoord hxy
  simpa [example310JacobianCoord_fromZMod] using this

def example310JacobianEquiv : ZMod 3 ≃+ example310.Jacobian :=
  AddEquiv.ofBijective example310FromZMod
    ⟨example310FromZMod_injective, example310FromZMod_surjective⟩

noncomputable instance example310JacobianFintype : Fintype example310.Jacobian :=
  Fintype.ofEquiv (ZMod 3) example310JacobianEquiv.toEquiv

def example310Base0 : example310.PicardDegree 1 := example310.vertexClass 0

def example310Base1 : example310.PicardDegree 1 := example310.vertexClass 1

def example310Base2Divisor : Divisor (Fin 2) := ![2, -1]

theorem example310Base2Divisor_degree :
    Divisor.degree example310Base2Divisor = 1 := by
  simp [Divisor.degree, example310Base2Divisor, Fin.sum_univ_succ]

def example310Base2 : example310.PicardDegree 1 :=
  ⟨example310.divisorClass example310Base2Divisor, by
    rw [example310.picardDegree_divisorClass]
    exact example310Base2Divisor_degree⟩

theorem example310Base2_ne_base0 : example310Base2 ≠ example310Base0 := by
  intro h
  have hpic : example310.divisorClass example310Base2Divisor =
      example310.divisorClass (Divisor.vertexDivisor (0 : Fin 2)) :=
    congrArg Subtype.val h
  rw [example310.divisorClass_eq_iff_sub_mem, example310_mem_lattice_iff] at hpic
  obtain ⟨k, hk⟩ := hpic
  have hk0 := congrFun hk 0
  simp [example310Base2Divisor, Divisor.vertexDivisor] at hk0
  omega

theorem example310Base2_ne_base1 : example310Base2 ≠ example310Base1 := by
  intro h
  have hpic : example310.divisorClass example310Base2Divisor =
      example310.divisorClass (Divisor.vertexDivisor (1 : Fin 2)) :=
    congrArg Subtype.val h
  rw [example310.divisorClass_eq_iff_sub_mem, example310_mem_lattice_iff] at hpic
  obtain ⟨k, hk⟩ := hpic
  have hk0 := congrFun hk 0
  simp [example310Base2Divisor, Divisor.vertexDivisor] at hk0
  omega

theorem example310Base0_ne_base1 : example310Base0 ≠ example310Base1 := by
  intro h
  have hv := example310.vertexClass_injective_of_bridgeFree example310_bridgeFree h
  exact Fin.zero_ne_one hv

theorem example310_h_base0 : example310.h (example310Base0 : example310.Picard) = 1 := by
  have hpos : 0 < example310.h (example310Base0 : example310.Picard) :=
    (example310.h_pos_degree_one_iff_vertexClass example310Base0).2 ⟨0, rfl⟩
  have hadm : example310.HAdmissible (example310Base0 : example310.Picard) 1 := by
    refine ⟨Divisor.vertexDivisor (1 : Fin 2),
      Divisor.isEffective_vertexDivisor 1,
      Divisor.degree_vertexDivisor 1, ?_⟩
    rw [example310.hasEffectiveRepresentative_of_degree_zero_iff]
    · intro heq
      apply example310Base0_ne_base1
      apply Subtype.ext
      simpa [example310Base0, example310Base1, sub_eq_zero] using heq
    · change example310.picardDegree
          (example310.divisorClass (Divisor.vertexDivisor (0 : Fin 2))) -
          example310.picardDegree
          (example310.divisorClass (Divisor.vertexDivisor (1 : Fin 2))) = 0
      rw [example310.picardDegree_divisorClass,
        example310.picardDegree_divisorClass]
      simp
  have hle := example310.h_min (example310Base0 : example310.Picard) hadm
  omega

theorem example310_h_base1 : example310.h (example310Base1 : example310.Picard) = 1 := by
  have hpos : 0 < example310.h (example310Base1 : example310.Picard) :=
    (example310.h_pos_degree_one_iff_vertexClass example310Base1).2 ⟨1, rfl⟩
  have hadm : example310.HAdmissible (example310Base1 : example310.Picard) 1 := by
    refine ⟨Divisor.vertexDivisor (0 : Fin 2),
      Divisor.isEffective_vertexDivisor 0,
      Divisor.degree_vertexDivisor 0, ?_⟩
    rw [example310.hasEffectiveRepresentative_of_degree_zero_iff]
    · intro heq
      apply example310Base0_ne_base1
      apply Subtype.ext
      exact (sub_eq_zero.mp heq).symm
    · change example310.picardDegree
          (example310.divisorClass (Divisor.vertexDivisor (1 : Fin 2))) -
          example310.picardDegree
          (example310.divisorClass (Divisor.vertexDivisor (0 : Fin 2))) = 0
      rw [example310.picardDegree_divisorClass,
        example310.picardDegree_divisorClass]
      simp
  have hle := example310.h_min (example310Base1 : example310.Picard) hadm
  omega

theorem example310_h_base2 : example310.h (example310Base2 : example310.Picard) = 0 := by
  apply example310.h_eq_zero_of_not_hasEffectiveRepresentative
  rw [example310.hasEffectiveRepresentative_degree_one_iff]
  rintro ⟨v, hv⟩
  fin_cases v
  · exact example310Base2_ne_base0 hv
  · exact example310Base2_ne_base1 hv

theorem example310_classInDegree_base0_zero :
    example310.classInDegree example310Base0 1 (example310FromZMod 0) =
      (example310Base0 : example310.Picard) := by
  simp [LooplessMultigraph.classInDegree, example310Base0, example310FromZMod,
    example310GeneratorIntHom]

theorem example310_classInDegree_base0_one :
    example310.classInDegree example310Base0 1 (example310FromZMod 1) =
      (example310Base1 : example310.Picard) := by
  rw [show example310FromZMod (1 : ZMod 3) = example310Generator by
    simpa using example310FromZMod_intCast (1 : ℤ)]
  simp only [LooplessMultigraph.classInDegree, one_zsmul]
  change example310.divisorClass example310GeneratorDivisor +
      example310.divisorClass (Divisor.vertexDivisor (0 : Fin 2)) =
    example310.divisorClass (Divisor.vertexDivisor (1 : Fin 2))
  rw [← map_add]
  rw [example310.divisorClass_eq_iff_sub_mem, example310_mem_lattice_iff]
  refine ⟨0, ?_⟩
  funext i
  fin_cases i
  · change (-1 : ℤ) + (if (0 : Fin 2) = 0 then 1 else 0) -
        (if (0 : Fin 2) = 1 then 1 else 0) = 0
    norm_num
  · change (1 : ℤ) + (if (1 : Fin 2) = 0 then 1 else 0) -
        (if (1 : Fin 2) = 1 then 1 else 0) = 0
    norm_num

theorem example310_classInDegree_base0_two :
    example310.classInDegree example310Base0 1 (example310FromZMod 2) =
      (example310Base2 : example310.Picard) := by
  rw [show example310FromZMod (2 : ZMod 3) = (2 : ℤ) • example310Generator by
    simpa using example310FromZMod_intCast (2 : ℤ)]
  simp only [LooplessMultigraph.classInDegree, one_zsmul]
  change ((2 : ℤ) • example310.divisorClass example310GeneratorDivisor) +
      example310.divisorClass (Divisor.vertexDivisor (0 : Fin 2)) =
    example310.divisorClass example310Base2Divisor
  rw [← map_zsmul, ← map_add]
  rw [example310.divisorClass_eq_iff_sub_mem, example310_mem_lattice_iff]
  refine ⟨-1, ?_⟩
  funext i
  fin_cases i
  · change (2 : ℤ) * (-1) +
        (if (0 : Fin 2) = 0 then 1 else 0) - 2 = -3
    norm_num
  · change (2 : ℤ) * 1 +
        (if (1 : Fin 2) = 0 then 1 else 0) - (-1) = 3
    norm_num

theorem example310_sum_zmod_three {R : Type*} [AddCommMonoid R]
    (f : ZMod 3 → R) :
    ∑ z : ZMod 3, f z = f 0 + f 1 + f 2 := by
  change ∑ z : Fin 3, f z = _
  simp only [Fin.sum_univ_succ, Fin.val_zero, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero]
  rw [add_assoc]
  apply congrArg₂ (fun x y : R ↦ x + y)
  · rfl
  · apply congrArg₂ (fun x y : R ↦ x + y)
    · apply congrArg f
      apply Fin.ext
      rfl
    · apply congrArg f
      apply Fin.ext
      rfl

theorem example310_h_classInDegree_zero_fromZMod
    (D₁ : example310.PicardDegree 1) (z : ZMod 3) :
    example310.h (example310.classInDegree D₁ 0 (example310FromZMod z)) =
      if z = 0 then 1 else 0 := by
  by_cases hz : z = 0
  · subst z
    simp [LooplessMultigraph.classInDegree, example310.h_zero]
  · rw [if_neg hz]
    apply example310.h_eq_zero_of_degree_zero_of_ne_zero
    · exact example310.picardDegree_classInDegree D₁ 0 (example310FromZMod z)
    · intro heq
      apply hz
      apply example310FromZMod_injective
      simpa [LooplessMultigraph.classInDegree] using heq

theorem example310_lCoefficient_zero
    (D₁ : example310.PicardDegree 1) (chi : AddChar example310.Jacobian ℂ) :
    example310.lCoefficient D₁ chi 0 = 1 := by
  classical
  rw [LooplessMultigraph.lCoefficient]
  calc
    (∑ a : example310.Jacobian,
        Polynomial.C (chi a) *
          geometricPolynomial
            (example310.h (example310.classInDegree D₁ (0 : ℤ) a))) =
        ∑ z : ZMod 3,
          Polynomial.C (chi (example310JacobianEquiv z)) *
            geometricPolynomial
              (example310.h (example310.classInDegree D₁ (0 : ℤ)
                (example310JacobianEquiv z))) := by
      symm
      exact Fintype.sum_equiv example310JacobianEquiv.toEquiv _ _ (fun _ ↦ rfl)
    _ = 1 := by
      rw [example310_sum_zmod_three]
      change Polynomial.C (chi (example310FromZMod 0)) *
          geometricPolynomial
            (example310.h (example310.classInDegree D₁ 0 (example310FromZMod 0))) +
        Polynomial.C (chi (example310FromZMod 1)) *
          geometricPolynomial
            (example310.h (example310.classInDegree D₁ 0 (example310FromZMod 1))) +
        Polynomial.C (chi (example310FromZMod 2)) *
          geometricPolynomial
            (example310.h (example310.classInDegree D₁ 0 (example310FromZMod 2))) = 1
      rw [example310_h_classInDegree_zero_fromZMod,
        example310_h_classInDegree_zero_fromZMod,
        example310_h_classInDegree_zero_fromZMod]
      have htwo : (2 : ZMod 3) ≠ 0 := by decide
      rw [if_neg htwo]
      simp [example310FromZMod, geometricPolynomial]

@[simp] theorem example310_h_classInDegree_base0_zero :
    example310.h (example310.classInDegree example310Base0 1
      (example310FromZMod 0)) = 1 := by
  rw [example310_classInDegree_base0_zero, example310_h_base0]

@[simp] theorem example310_h_classInDegree_base0_one :
    example310.h (example310.classInDegree example310Base0 1
      (example310FromZMod 1)) = 1 := by
  rw [example310_classInDegree_base0_one, example310_h_base1]

@[simp] theorem example310_h_classInDegree_base0_two :
    example310.h (example310.classInDegree example310Base0 1
      (example310FromZMod 2)) = 0 := by
  rw [example310_classInDegree_base0_two, example310_h_base2]

theorem example310_lCoefficient_one_base0
    (chi : AddChar example310.Jacobian ℂ) :
    example310.lCoefficient example310Base0 chi 1 =
      Polynomial.C (1 + chi example310Generator) := by
  classical
  rw [LooplessMultigraph.lCoefficient]
  calc
    (∑ a : example310.Jacobian,
        Polynomial.C (chi a) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base0 (1 : ℤ) a))) =
        ∑ z : ZMod 3,
          Polynomial.C (chi (example310JacobianEquiv z)) *
            geometricPolynomial
              (example310.h (example310.classInDegree example310Base0 (1 : ℤ)
                (example310JacobianEquiv z))) := by
      symm
      exact Fintype.sum_equiv example310JacobianEquiv.toEquiv _ _ (fun _ ↦ rfl)
    _ = Polynomial.C (1 + chi example310Generator) := by
      rw [example310_sum_zmod_three]
      change Polynomial.C (chi (example310FromZMod 0)) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base0 1
              (example310FromZMod 0))) +
        Polynomial.C (chi (example310FromZMod 1)) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base0 1
              (example310FromZMod 1))) +
        Polynomial.C (chi (example310FromZMod 2)) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base0 1
              (example310FromZMod 2))) = _
      rw [example310_h_classInDegree_base0_zero,
        example310_h_classInDegree_base0_one,
        example310_h_classInDegree_base0_two]
      rw [show example310FromZMod (1 : ZMod 3) = example310Generator by
        simpa using example310FromZMod_intCast (1 : ℤ)]
      simp [geometricPolynomial, example310FromZMod]

theorem example310_classInDegree_base1_zero :
    example310.classInDegree example310Base1 1 (example310FromZMod 0) =
      (example310Base1 : example310.Picard) := by
  simp [LooplessMultigraph.classInDegree, example310FromZMod,
    example310GeneratorIntHom]

theorem example310_classInDegree_base1_one :
    example310.classInDegree example310Base1 1 (example310FromZMod 1) =
      (example310Base2 : example310.Picard) := by
  rw [show example310FromZMod (1 : ZMod 3) = example310Generator by
    simpa using example310FromZMod_intCast (1 : ℤ)]
  simp only [LooplessMultigraph.classInDegree, one_zsmul]
  change example310.divisorClass example310GeneratorDivisor +
      example310.divisorClass (Divisor.vertexDivisor (1 : Fin 2)) =
    example310.divisorClass example310Base2Divisor
  rw [← map_add, example310.divisorClass_eq_iff_sub_mem,
    example310_mem_lattice_iff]
  refine ⟨-1, ?_⟩
  funext i
  fin_cases i
  · change (-1 : ℤ) + (if (0 : Fin 2) = 1 then 1 else 0) - 2 = -3
    norm_num
  · change (1 : ℤ) + (if (1 : Fin 2) = 1 then 1 else 0) - (-1) = 3
    norm_num

theorem example310_classInDegree_base1_two :
    example310.classInDegree example310Base1 1 (example310FromZMod 2) =
      (example310Base0 : example310.Picard) := by
  rw [show example310FromZMod (2 : ZMod 3) = (2 : ℤ) • example310Generator by
    simpa using example310FromZMod_intCast (2 : ℤ)]
  simp only [LooplessMultigraph.classInDegree, one_zsmul]
  change ((2 : ℤ) • example310.divisorClass example310GeneratorDivisor) +
      example310.divisorClass (Divisor.vertexDivisor (1 : Fin 2)) =
    example310.divisorClass (Divisor.vertexDivisor (0 : Fin 2))
  rw [← map_zsmul, ← map_add, example310.divisorClass_eq_iff_sub_mem,
    example310_mem_lattice_iff]
  refine ⟨-1, ?_⟩
  funext i
  fin_cases i
  · change (2 : ℤ) * (-1) +
        (if (0 : Fin 2) = 1 then 1 else 0) -
        (if (0 : Fin 2) = 0 then 1 else 0) = -3
    norm_num
  · change (2 : ℤ) * 1 +
        (if (1 : Fin 2) = 1 then 1 else 0) -
        (if (1 : Fin 2) = 0 then 1 else 0) = 3
    norm_num

theorem example310_classInDegree_base2_zero :
    example310.classInDegree example310Base2 1 (example310FromZMod 0) =
      (example310Base2 : example310.Picard) := by
  simp [LooplessMultigraph.classInDegree, example310FromZMod,
    example310GeneratorIntHom]

theorem example310_classInDegree_base2_one :
    example310.classInDegree example310Base2 1 (example310FromZMod 1) =
      (example310Base0 : example310.Picard) := by
  rw [show example310FromZMod (1 : ZMod 3) = example310Generator by
    simpa using example310FromZMod_intCast (1 : ℤ)]
  simp only [LooplessMultigraph.classInDegree, one_zsmul]
  change example310.divisorClass example310GeneratorDivisor +
      example310.divisorClass example310Base2Divisor =
    example310.divisorClass (Divisor.vertexDivisor (0 : Fin 2))
  rw [← map_add, example310.divisorClass_eq_iff_sub_mem,
    example310_mem_lattice_iff]
  refine ⟨0, ?_⟩
  funext i
  fin_cases i
  · change (-1 : ℤ) + 2 -
        (if (0 : Fin 2) = 0 then 1 else 0) = 0
    norm_num
  · change (1 : ℤ) + (-1) -
        (if (1 : Fin 2) = 0 then 1 else 0) = 0
    norm_num

theorem example310_classInDegree_base2_two :
    example310.classInDegree example310Base2 1 (example310FromZMod 2) =
      (example310Base1 : example310.Picard) := by
  rw [show example310FromZMod (2 : ZMod 3) = (2 : ℤ) • example310Generator by
    simpa using example310FromZMod_intCast (2 : ℤ)]
  simp only [LooplessMultigraph.classInDegree, one_zsmul]
  change ((2 : ℤ) • example310.divisorClass example310GeneratorDivisor) +
      example310.divisorClass example310Base2Divisor =
    example310.divisorClass (Divisor.vertexDivisor (1 : Fin 2))
  rw [← map_zsmul, ← map_add, example310.divisorClass_eq_iff_sub_mem,
    example310_mem_lattice_iff]
  refine ⟨0, ?_⟩
  funext i
  fin_cases i
  · change (2 : ℤ) * (-1) + 2 -
        (if (0 : Fin 2) = 1 then 1 else 0) = 0
    norm_num
  · change (2 : ℤ) * 1 + (-1) -
        (if (1 : Fin 2) = 1 then 1 else 0) = 0
    norm_num

theorem example310_two_zsmul_generator_eq_neg :
    (2 : ℤ) • example310Generator = -example310Generator := by
  apply eq_neg_of_add_eq_zero_right
  calc
    example310Generator + (2 : ℤ) • example310Generator =
        (3 : ℤ) • example310Generator := by
      calc
        example310Generator + (2 : ℤ) • example310Generator =
            (1 : ℤ) • example310Generator +
              (2 : ℤ) • example310Generator := by rw [one_zsmul]
        _ = ((1 + 2 : ℤ) • example310Generator) := by rw [add_zsmul]
        _ = (3 : ℤ) • example310Generator := by norm_num
    _ = 0 := example310_three_zsmul_generator

@[simp] theorem example310_h_classInDegree_base1_zero :
    example310.h (example310.classInDegree example310Base1 1
      (example310FromZMod 0)) = 1 := by
  rw [example310_classInDegree_base1_zero, example310_h_base1]

@[simp] theorem example310_h_classInDegree_base1_one :
    example310.h (example310.classInDegree example310Base1 1
      (example310FromZMod 1)) = 0 := by
  rw [example310_classInDegree_base1_one, example310_h_base2]

@[simp] theorem example310_h_classInDegree_base1_two :
    example310.h (example310.classInDegree example310Base1 1
      (example310FromZMod 2)) = 1 := by
  rw [example310_classInDegree_base1_two, example310_h_base0]

@[simp] theorem example310_h_classInDegree_base2_zero :
    example310.h (example310.classInDegree example310Base2 1
      (example310FromZMod 0)) = 0 := by
  rw [example310_classInDegree_base2_zero, example310_h_base2]

@[simp] theorem example310_h_classInDegree_base2_one :
    example310.h (example310.classInDegree example310Base2 1
      (example310FromZMod 1)) = 1 := by
  rw [example310_classInDegree_base2_one, example310_h_base0]

@[simp] theorem example310_h_classInDegree_base2_two :
    example310.h (example310.classInDegree example310Base2 1
      (example310FromZMod 2)) = 1 := by
  rw [example310_classInDegree_base2_two, example310_h_base1]

theorem example310_lCoefficient_one_base1
    (chi : AddChar example310.Jacobian ℂ) :
    example310.lCoefficient example310Base1 chi 1 =
      Polynomial.C (1 + chi (-example310Generator)) := by
  classical
  rw [LooplessMultigraph.lCoefficient]
  calc
    (∑ a : example310.Jacobian,
        Polynomial.C (chi a) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base1 (1 : ℤ) a))) =
        ∑ z : ZMod 3,
          Polynomial.C (chi (example310JacobianEquiv z)) *
            geometricPolynomial
              (example310.h (example310.classInDegree example310Base1 (1 : ℤ)
                (example310JacobianEquiv z))) := by
      symm
      exact Fintype.sum_equiv example310JacobianEquiv.toEquiv _ _ (fun _ ↦ rfl)
    _ = Polynomial.C (1 + chi (-example310Generator)) := by
      rw [example310_sum_zmod_three]
      change Polynomial.C (chi (example310FromZMod 0)) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base1 1
              (example310FromZMod 0))) +
        Polynomial.C (chi (example310FromZMod 1)) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base1 1
              (example310FromZMod 1))) +
        Polynomial.C (chi (example310FromZMod 2)) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base1 1
              (example310FromZMod 2))) = _
      rw [example310_h_classInDegree_base1_zero,
        example310_h_classInDegree_base1_one,
        example310_h_classInDegree_base1_two]
      rw [show example310FromZMod (2 : ZMod 3) = (2 : ℤ) • example310Generator by
        simpa using example310FromZMod_intCast (2 : ℤ),
        example310_two_zsmul_generator_eq_neg]
      simp [geometricPolynomial, example310FromZMod]

theorem example310_lCoefficient_one_base2
    (chi : AddChar example310.Jacobian ℂ) :
    example310.lCoefficient example310Base2 chi 1 =
      Polynomial.C (chi example310Generator + chi (-example310Generator)) := by
  classical
  rw [LooplessMultigraph.lCoefficient]
  calc
    (∑ a : example310.Jacobian,
        Polynomial.C (chi a) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base2 (1 : ℤ) a))) =
        ∑ z : ZMod 3,
          Polynomial.C (chi (example310JacobianEquiv z)) *
            geometricPolynomial
              (example310.h (example310.classInDegree example310Base2 (1 : ℤ)
                (example310JacobianEquiv z))) := by
      symm
      exact Fintype.sum_equiv example310JacobianEquiv.toEquiv _ _ (fun _ ↦ rfl)
    _ = Polynomial.C
        (chi example310Generator + chi (-example310Generator)) := by
      rw [example310_sum_zmod_three]
      change Polynomial.C (chi (example310FromZMod 0)) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base2 1
              (example310FromZMod 0))) +
        Polynomial.C (chi (example310FromZMod 1)) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base2 1
              (example310FromZMod 1))) +
        Polynomial.C (chi (example310FromZMod 2)) *
          geometricPolynomial
            (example310.h (example310.classInDegree example310Base2 1
              (example310FromZMod 2))) = _
      rw [example310_h_classInDegree_base2_zero,
        example310_h_classInDegree_base2_one,
        example310_h_classInDegree_base2_two]
      rw [show example310FromZMod (1 : ZMod 3) = example310Generator by
        simpa using example310FromZMod_intCast (1 : ℤ),
        show example310FromZMod (2 : ZMod 3) = (2 : ℤ) • example310Generator by
          simpa using example310FromZMod_intCast (2 : ℤ),
        example310_two_zsmul_generator_eq_neg]
      simp [geometricPolynomial]

theorem example310_canonicalDivisor :
    example310.canonicalDivisor = (![1, 1] : Divisor (Fin 2)) := by
  funext i
  fin_cases i <;> simp [LooplessMultigraph.canonicalDivisor_apply,
    example310_valency]

theorem example310_riemannRochBound : example310.riemannRochBound = 2 := by
  simp [LooplessMultigraph.riemannRochBound, example310_genus]

theorem example310_canonicalCoordinate_base0 :
    example310.canonicalCoordinate example310Base0 = example310Generator := by
  apply Subtype.ext
  change (example310.jacobianCoordinate example310Base0 example310.canonicalClass :
      example310.Picard) = (example310Generator : example310.Picard)
  rw [LooplessMultigraph.jacobianCoordinate_coe,
    example310.picardDegree_canonicalClass, example310_genus]
  norm_num
  change example310.divisorClass example310.canonicalDivisor -
      (2 : ℤ) • example310.divisorClass (Divisor.vertexDivisor (0 : Fin 2)) =
    example310.divisorClass example310GeneratorDivisor
  rw [← map_zsmul, ← map_sub, example310.divisorClass_eq_iff_sub_mem,
    example310_mem_lattice_iff]
  refine ⟨0, ?_⟩
  rw [example310_canonicalDivisor]
  funext i
  fin_cases i
  · change (1 : ℤ) - 2 * (if (0 : Fin 2) = 0 then 1 else 0) - (-1) = 0
    norm_num
  · change (1 : ℤ) - 2 * (if (1 : Fin 2) = 0 then 1 else 0) - 1 = 0
    norm_num

theorem example310_canonicalCoordinate_base1 :
    example310.canonicalCoordinate example310Base1 = -example310Generator := by
  apply Subtype.ext
  change (example310.jacobianCoordinate example310Base1 example310.canonicalClass :
      example310.Picard) = (-example310Generator : example310.Jacobian)
  rw [LooplessMultigraph.jacobianCoordinate_coe,
    example310.picardDegree_canonicalClass, example310_genus]
  norm_num
  change example310.divisorClass example310.canonicalDivisor -
      (2 : ℤ) • example310.divisorClass (Divisor.vertexDivisor (1 : Fin 2)) =
    -example310.divisorClass example310GeneratorDivisor
  rw [← map_zsmul, ← map_sub, ← map_neg,
    example310.divisorClass_eq_iff_sub_mem, example310_mem_lattice_iff]
  refine ⟨0, ?_⟩
  rw [example310_canonicalDivisor]
  funext i
  fin_cases i
  · change (1 : ℤ) - 2 * (if (0 : Fin 2) = 1 then 1 else 0) - (-(-1)) = 0
    norm_num
  · change (1 : ℤ) - 2 * (if (1 : Fin 2) = 1 then 1 else 0) - (-1) = 0
    norm_num

theorem example310_canonicalCoordinate_base2 :
    example310.canonicalCoordinate example310Base2 = 0 := by
  apply Subtype.ext
  change (example310.jacobianCoordinate example310Base2 example310.canonicalClass :
      example310.Picard) = (0 : example310.Picard)
  rw [LooplessMultigraph.jacobianCoordinate_coe,
    example310.picardDegree_canonicalClass, example310_genus]
  norm_num
  change example310.divisorClass example310.canonicalDivisor -
      (2 : ℤ) • example310.divisorClass example310Base2Divisor = 0
  rw [← map_zsmul, ← map_sub]
  change example310.divisorClass
      (example310.canonicalDivisor - (2 : ℤ) • example310Base2Divisor) = 0
  change Submodule.Quotient.mk
      (example310.canonicalDivisor - (2 : ℤ) • example310Base2Divisor) = 0
  rw [Submodule.Quotient.mk_eq_zero, example310_mem_lattice_iff]
  refine ⟨-1, ?_⟩
  rw [example310_canonicalDivisor]
  funext i
  fin_cases i <;> norm_num [example310Base2Divisor]

theorem example310_lCoefficient_two_base0
    (chi : AddChar example310.Jacobian ℂ) (hchi : chi ≠ 1) :
    example310.lCoefficient example310Base0 chi 2 =
      Polynomial.C (chi example310Generator) * Polynomial.X := by
  have h := example310.lCoefficient_riemannRochBound
    (example310.riemannRochFormula_of_connected example310_connected)
    example310Base0 chi hchi (by rw [example310_genus]; norm_num)
  rw [example310_riemannRochBound, example310_genus,
    example310_canonicalCoordinate_base0] at h
  simpa using h

theorem example310_lCoefficient_two_base1
    (chi : AddChar example310.Jacobian ℂ) (hchi : chi ≠ 1) :
    example310.lCoefficient example310Base1 chi 2 =
      Polynomial.C (chi (-example310Generator)) * Polynomial.X := by
  have h := example310.lCoefficient_riemannRochBound
    (example310.riemannRochFormula_of_connected example310_connected)
    example310Base1 chi hchi (by rw [example310_genus]; norm_num)
  rw [example310_riemannRochBound, example310_genus,
    example310_canonicalCoordinate_base1] at h
  simpa using h

theorem example310_lCoefficient_two_base2
    (chi : AddChar example310.Jacobian ℂ) (hchi : chi ≠ 1) :
    example310.lCoefficient example310Base2 chi 2 = Polynomial.X := by
  have h := example310.lCoefficient_riemannRochBound
    (example310.riemannRochFormula_of_connected example310_connected)
    example310Base2 chi hchi (by rw [example310_genus]; norm_num)
  rw [example310_riemannRochBound, example310_genus,
    example310_canonicalCoordinate_base2] at h
  simpa using h

def example310ExplicitLPolynomial (A B : Polynomial ℂ) :
    Polynomial (Polynomial ℂ) :=
  Polynomial.C 1 + Polynomial.C A * Polynomial.X +
    Polynomial.C B * Polynomial.X ^ 2

theorem example310_lFunction_of_three_coefficients
    (D₁ : example310.PicardDegree 1)
    (chi : AddChar example310.Jacobian ℂ) (hchi : chi ≠ 1)
    (A B : Polynomial ℂ)
    (hzero : example310.lCoefficient D₁ chi 0 = 1)
    (hone : example310.lCoefficient D₁ chi 1 = A)
    (htwo : example310.lCoefficient D₁ chi 2 = B) :
    example310.lFunction D₁ chi =
      (example310ExplicitLPolynomial A B : PowerSeries (Polynomial ℂ)) := by
  have hseries := example310.lFunction_eq_lPolynomial_of_riemannRoch
    (example310.riemannRochFormula_of_connected example310_connected) D₁ chi hchi
  calc
    example310.lFunction D₁ chi =
        (example310.lPolynomial D₁ chi example310.riemannRochBound :
          PowerSeries (Polynomial ℂ)) := hseries
    _ = (example310ExplicitLPolynomial A B : PowerSeries (Polynomial ℂ)) := by
      apply congrArg (fun P : Polynomial (Polynomial ℂ) ↦
        (P : PowerSeries (Polynomial ℂ)))
      apply Polynomial.ext
      intro d
      rw [example310.coeff_lPolynomial, example310_riemannRochBound]
      by_cases hd : d ≤ 2
      · interval_cases d
        · rw [if_pos (by omega), hzero]
          simp [example310ExplicitLPolynomial, Polynomial.coeff_one,
            Polynomial.coeff_X, Polynomial.coeff_X_pow]
        · rw [if_pos (by omega), hone]
          simp [example310ExplicitLPolynomial, Polynomial.coeff_one,
            Polynomial.coeff_X, Polynomial.coeff_X_pow]
        · rw [if_pos (by omega), htwo]
          simp [example310ExplicitLPolynomial, Polynomial.coeff_one,
            Polynomial.coeff_X, Polynomial.coeff_X_pow]
      · rw [if_neg hd]
        have hd0 : d ≠ 0 := by omega
        have hd1 : d ≠ 1 := by omega
        have hd1' : 1 ≠ d := Ne.symm hd1
        have hd2 : d ≠ 2 := by omega
        simp [example310ExplicitLPolynomial, Polynomial.coeff_one,
          Polynomial.coeff_X, Polynomial.coeff_X_pow, hd0, hd1, hd1', hd2]

theorem example310_lFunction_base0
    (chi : AddChar example310.Jacobian ℂ) (hchi : chi ≠ 1) :
    example310.lFunction example310Base0 chi =
      (example310ExplicitLPolynomial
        (Polynomial.C (1 + chi example310Generator))
        (Polynomial.C (chi example310Generator) * Polynomial.X) :
        PowerSeries (Polynomial ℂ)) := by
  apply example310_lFunction_of_three_coefficients example310Base0 chi hchi
  · exact example310_lCoefficient_zero example310Base0 chi
  · exact example310_lCoefficient_one_base0 chi
  · exact example310_lCoefficient_two_base0 chi hchi

theorem example310_lFunction_base1
    (chi : AddChar example310.Jacobian ℂ) (hchi : chi ≠ 1) :
    example310.lFunction example310Base1 chi =
      (example310ExplicitLPolynomial
        (Polynomial.C (1 + chi (-example310Generator)))
        (Polynomial.C (chi (-example310Generator)) * Polynomial.X) :
        PowerSeries (Polynomial ℂ)) := by
  apply example310_lFunction_of_three_coefficients example310Base1 chi hchi
  · exact example310_lCoefficient_zero example310Base1 chi
  · exact example310_lCoefficient_one_base1 chi
  · exact example310_lCoefficient_two_base1 chi hchi

theorem example310_lFunction_base2
    (chi : AddChar example310.Jacobian ℂ) (hchi : chi ≠ 1) :
    example310.lFunction example310Base2 chi =
      (example310ExplicitLPolynomial
        (Polynomial.C (chi example310Generator + chi (-example310Generator)))
        Polynomial.X : PowerSeries (Polynomial ℂ)) := by
  apply example310_lFunction_of_three_coefficients example310Base2 chi hchi
  · exact example310_lCoefficient_zero example310Base2 chi
  · exact example310_lCoefficient_one_base2 chi
  · exact example310_lCoefficient_two_base2 chi hchi

def example310Omega : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 3)

theorem example310Omega_isPrimitiveRoot :
    IsPrimitiveRoot example310Omega 3 := by
  exact Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem example310Omega_cube : example310Omega ^ 3 = 1 :=
  example310Omega_isPrimitiveRoot.pow_eq_one

theorem example310Omega_ne_one : example310Omega ≠ 1 :=
  example310Omega_isPrimitiveRoot.ne_one (by norm_num)

theorem example310Omega_sq_ne_one : example310Omega ^ 2 ≠ 1 := by
  intro hsquare
  apply example310Omega_ne_one
  calc
    example310Omega = example310Omega * 1 := by simp
    _ = example310Omega * example310Omega ^ 2 := by rw [hsquare]
    _ = example310Omega ^ 3 := by ring
    _ = 1 := example310Omega_cube

theorem example310Omega_sq_cube : (example310Omega ^ 2) ^ 3 = 1 := by
  calc
    (example310Omega ^ 2) ^ 3 = (example310Omega ^ 3) ^ 2 := by ring
    _ = 1 := by rw [example310Omega_cube]; simp

theorem example310Omega_inv : example310Omega⁻¹ = example310Omega ^ 2 := by
  symm
  apply eq_inv_of_mul_eq_one_right
  calc
    example310Omega * example310Omega ^ 2 = example310Omega ^ 3 := by ring
    _ = 1 := example310Omega_cube

theorem example310Omega_sq_inv : (example310Omega ^ 2)⁻¹ = example310Omega := by
  symm
  apply eq_inv_of_mul_eq_one_right
  calc
    example310Omega ^ 2 * example310Omega = example310Omega ^ 3 := by ring
    _ = 1 := example310Omega_cube

theorem example310Omega_add_sq :
    example310Omega + example310Omega ^ 2 = -1 := by
  have hfactor : (example310Omega - 1) *
      (example310Omega ^ 2 + example310Omega + 1) = 0 := by
    calc
      (example310Omega - 1) *
          (example310Omega ^ 2 + example310Omega + 1) =
        example310Omega ^ 3 - 1 := by ring
      _ = 0 := by rw [example310Omega_cube]; ring
  have hlinear : example310Omega ^ 2 + example310Omega + 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left
      (sub_ne_zero.mpr example310Omega_ne_one)
  linear_combination hlinear

def example310Chi0 : AddChar example310.Jacobian ℂ :=
  (AddChar.zmodChar 3 example310Omega_cube).compAddMonoidHom
    example310JacobianCoord

def example310Chi1 : AddChar example310.Jacobian ℂ :=
  (AddChar.zmodChar 3 example310Omega_sq_cube).compAddMonoidHom
    example310JacobianCoord

@[simp] theorem example310Chi0_generator :
    example310Chi0 example310Generator = example310Omega := by
  rw [example310Chi0, AddChar.compAddMonoidHom_apply,
    example310JacobianCoord_generator]
  simpa using (AddChar.zmodChar_apply' example310Omega_cube 1)

@[simp] theorem example310Chi1_generator :
    example310Chi1 example310Generator = example310Omega ^ 2 := by
  rw [example310Chi1, AddChar.compAddMonoidHom_apply,
    example310JacobianCoord_generator]
  simpa using (AddChar.zmodChar_apply' example310Omega_sq_cube 1)

@[simp] theorem example310Chi0_neg_generator :
    example310Chi0 (-example310Generator) = example310Omega ^ 2 := by
  rw [AddChar.map_neg_eq_inv, example310Chi0_generator, example310Omega_inv]

@[simp] theorem example310Chi1_neg_generator :
    example310Chi1 (-example310Generator) = example310Omega := by
  rw [AddChar.map_neg_eq_inv, example310Chi1_generator, example310Omega_sq_inv]

theorem example310Chi0_ne_one : example310Chi0 ≠ 1 := by
  intro h
  have hg := DFunLike.congr_fun h example310Generator
  simp only [example310Chi0_generator, AddChar.one_apply] at hg
  exact example310Omega_ne_one hg

theorem example310Chi1_ne_one : example310Chi1 ≠ 1 := by
  intro h
  have hg := DFunLike.congr_fun h example310Generator
  simp only [example310Chi1_generator, AddChar.one_apply] at hg
  exact example310Omega_sq_ne_one hg

theorem example310_lFunction_chi0_base0 :
    example310.lFunction example310Base0 example310Chi0 =
      (example310ExplicitLPolynomial
        (Polynomial.C (1 + example310Omega))
        (Polynomial.C example310Omega * Polynomial.X) :
        PowerSeries (Polynomial ℂ)) := by
  simpa using example310_lFunction_base0 example310Chi0 example310Chi0_ne_one

theorem example310_lFunction_chi1_base1 :
    example310.lFunction example310Base1 example310Chi1 =
      (example310ExplicitLPolynomial
        (Polynomial.C (1 + example310Omega))
        (Polynomial.C example310Omega * Polynomial.X) :
        PowerSeries (Polynomial ℂ)) := by
  simpa using example310_lFunction_base1 example310Chi1 example310Chi1_ne_one

theorem example310_lFunction_chi1_base0 :
    example310.lFunction example310Base0 example310Chi1 =
      (example310ExplicitLPolynomial
        (Polynomial.C (1 + example310Omega ^ 2))
        (Polynomial.C (example310Omega ^ 2) * Polynomial.X) :
        PowerSeries (Polynomial ℂ)) := by
  simpa using example310_lFunction_base0 example310Chi1 example310Chi1_ne_one

theorem example310_lFunction_chi0_base1 :
    example310.lFunction example310Base1 example310Chi0 =
      (example310ExplicitLPolynomial
        (Polynomial.C (1 + example310Omega ^ 2))
        (Polynomial.C (example310Omega ^ 2) * Polynomial.X) :
        PowerSeries (Polynomial ℂ)) := by
  simpa using example310_lFunction_base1 example310Chi0 example310Chi0_ne_one

theorem example310_lFunction_chi0_base2 :
    example310.lFunction example310Base2 example310Chi0 =
      (example310ExplicitLPolynomial (Polynomial.C (-1)) Polynomial.X :
        PowerSeries (Polynomial ℂ)) := by
  rw [example310_lFunction_base2 example310Chi0 example310Chi0_ne_one]
  rw [example310Chi0_generator, example310Chi0_neg_generator,
    example310Omega_add_sq]

theorem example310_lFunction_chi1_base2 :
    example310.lFunction example310Base2 example310Chi1 =
      (example310ExplicitLPolynomial (Polynomial.C (-1)) Polynomial.X :
        PowerSeries (Polynomial ℂ)) := by
  rw [example310_lFunction_base2 example310Chi1 example310Chi1_ne_one]
  rw [example310Chi1_generator, example310Chi1_neg_generator]
  congr 3
  rw [add_comm, example310Omega_add_sq]
end
end LeanCo.LaplacianLFunctions
