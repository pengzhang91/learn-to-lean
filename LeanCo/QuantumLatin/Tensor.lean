import LeanCo.QuantumLatin.Defs
import Mathlib.Tactic

/-!
# Tensor products of resolvable quantum Latin squares

The paper repeatedly uses pure tensors and, for order 90, the ordinary
direct product.  Everything here is proved by expanding finite coordinates;
no Hilbert-space facts beyond `mathlib` are assumed.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

universe u v

/-- Coordinate realization of a pure tensor. -/
def tensorKet {ι : Type u} {κ : Type v} (x : Ket ι) (y : Ket κ) :
    Ket (ι × κ) := fun p ↦ x p.1 * y p.2

theorem dot_tensorKet {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (x x' : Ket ι) (y y' : Ket κ) :
    dot (tensorKet x y) (tensorKet x' y') = dot x x' * dot y y' := by
  classical
  simp only [dot, tensorKet, Fintype.sum_prod_type, map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dot_smul_smul {ι : Type u} [Fintype ι]
    (a b : ℂ) (x y : Ket ι) :
    dot (a • x) (b • y) = conj a * b * dot x y := by
  classical
  simp only [dot, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem exists_apply_ne_zero_of_dot_self_eq_one
    {ι : Type u} [Fintype ι] (x : Ket ι) (hx : dot x x = 1) :
    ∃ i, x i ≠ 0 := by
  by_contra h
  push_neg at h
  have hz : x = 0 := funext h
  rw [hz] at hx
  simp [dot] at hx

private theorem norm_eq_one_of_conj_mul_self_eq_one (z : ℂ)
    (hz : conj z * z = 1) : ‖z‖ = 1 := by
  have hs : Complex.normSq z = 1 := by
    apply Complex.ofReal_injective
    simpa [Complex.normSq_eq_conj_mul_self] using hz
  rw [Complex.norm_def, hs]
  simp

/-- Equality up to phase of two nonzero pure tensors forces equality up to
phase of both factors.  Unit Gram norms ensure that the two factor scalars
also have norm one. -/
theorem phaseEquivalent_tensorKet_factors
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    {x x' : Ket ι} {y y' : Ket κ}
    (hxx : dot x x = 1) (hxx' : dot x' x' = 1)
    (hyy : dot y y = 1) (hyy' : dot y' y' = 1)
    (h : PhaseEquivalent (tensorKet x y) (tensorKet x' y')) :
    PhaseEquivalent x x' ∧ PhaseEquivalent y y' := by
  rcases h with ⟨z, hz, hxy⟩
  obtain ⟨a₀, ha₀⟩ := exists_apply_ne_zero_of_dot_self_eq_one x hxx
  obtain ⟨b₀, hb₀⟩ := exists_apply_ne_zero_of_dot_self_eq_one y hyy
  have hpoint (a : ι) (b : κ) :
      x a * y b = z * (x' a * y' b) := by
    have := congrFun hxy (a, b)
    simpa [tensorKet, Pi.smul_apply, smul_eq_mul] using this
  have hz0 : z ≠ 0 := by
    intro h0
    simp [h0] at hz
  have ha₀' : x' a₀ ≠ 0 := by
    intro h0
    have hp := hpoint a₀ b₀
    have hp0 : x a₀ * y b₀ = 0 := by simpa [h0] using hp
    exact (mul_ne_zero ha₀ hb₀) hp0
  have hb₀' : y' b₀ ≠ 0 := by
    intro h0
    have hp := hpoint a₀ b₀
    have hp0 : x a₀ * y b₀ = 0 := by simpa [h0] using hp
    exact (mul_ne_zero ha₀ hb₀) hp0
  let α : ℂ := z * y' b₀ / y b₀
  let β : ℂ := z * x' a₀ / x a₀
  have hxscalar : x = α • x' := by
    funext a
    change x a = α * x' a
    apply (mul_right_cancel₀ hb₀)
    rw [hpoint]
    dsimp [α]
    field_simp
    <;> ring
  have hyscalar : y = β • y' := by
    funext b
    change y b = β * y' b
    apply (mul_left_cancel₀ ha₀)
    rw [hpoint]
    dsimp [β]
    field_simp
    <;> ring
  have hα : conj α * α = 1 := by
    calc
      conj α * α = conj α * α * dot x' x' := by rw [hxx', mul_one]
      _ = dot (α • x') (α • x') := (dot_smul_smul α α x' x').symm
      _ = dot x x := by rw [hxscalar]
      _ = 1 := hxx
  have hβ : conj β * β = 1 := by
    calc
      conj β * β = conj β * β * dot y' y' := by rw [hyy', mul_one]
      _ = dot (β • y') (β • y') := (dot_smul_smul β β y' y').symm
      _ = dot y y := by rw [hyscalar]
      _ = 1 := hyy
  exact ⟨⟨α, norm_eq_one_of_conj_mul_self_eq_one α hα, hxscalar⟩,
    ⟨β, norm_eq_one_of_conj_mul_self_eq_one β hβ, hyscalar⟩⟩

/-- Cartesian tensor product of two QLSs. -/
def QuantumLatinSquare.tensor {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : QuantumLatinSquare ι) (B : QuantumLatinSquare κ) :
    QuantumLatinSquare (ι × κ) where
  entry p q := tensorKet (A.entry p.1 q.1) (B.entry p.2 q.2)
  row_orthonormal p q q' := by
    rw [dot_tensorKet, A.row_orthonormal, B.row_orthonormal]
    by_cases h₁ : q.1 = q'.1 <;> by_cases h₂ : q.2 = q'.2
    · simp [Prod.ext h₁ h₂]
    · simp [h₁, h₂, Prod.ext_iff]
    · simp [h₁, h₂, Prod.ext_iff]
    · simp [h₁, h₂, Prod.ext_iff]
  col_orthonormal q p p' := by
    rw [dot_tensorKet, A.col_orthonormal, B.col_orthonormal]
    by_cases h₁ : p.1 = p'.1 <;> by_cases h₂ : p.2 = p'.2
    · simp [Prod.ext h₁ h₂]
    · simp [h₁, h₂, Prod.ext_iff]
    · simp [h₁, h₂, Prod.ext_iff]
    · simp [h₁, h₂, Prod.ext_iff]

namespace QuantumLatinSquare.Resolution

variable {ι : Type u} {κ : Type v}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {A : QuantumLatinSquare ι} {B : QuantumLatinSquare κ}

/-- Product of two resolutions. -/
def tensor (RA : A.Resolution) (RB : B.Resolution) :
    (A.tensor B).Resolution where
  column t := (RA.column t.1).prodCongr (RB.column t.2)
  covers p := by
    let eA : ι ≃ ι := Equiv.ofBijective
      (fun t ↦ RA.column t p.1) (RA.covers p.1)
    let eB : κ ≃ κ := Equiv.ofBijective
      (fun t ↦ RB.column t p.2) (RB.covers p.2)
    change Function.Bijective
      (fun t : ι × κ ↦ (RA.column t.1 p.1, RB.column t.2 p.2))
    change Function.Bijective ⇑(eA.prodCongr eB)
    exact (eA.prodCongr eB).bijective
  orthonormal t p p' := by
    rw [QuantumLatinSquare.tensor, dot_tensorKet]
    change dot (A.entry p.1 (RA.column t.1 p.1))
        (A.entry p'.1 (RA.column t.1 p'.1)) *
      dot (B.entry p.2 (RB.column t.2 p.2))
        (B.entry p'.2 (RB.column t.2 p'.2)) =
      if p = p' then 1 else 0
    rw [RA.orthonormal, RB.orthonormal]
    by_cases h₁ : p.1 = p'.1 <;> by_cases h₂ : p.2 = p'.2
    · simp [Prod.ext h₁ h₂]
    · simp [h₁, h₂, Prod.ext_iff]
    · simp [h₁, h₂, Prod.ext_iff]
    · simp [h₁, h₂, Prod.ext_iff]

end QuantumLatinSquare.Resolution

/-- Ordinary direct product preserves maximal cardinality and resolvability. -/
def MaximalRQLS.tensor {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : MaximalRQLS ι) (B : MaximalRQLS κ) : MaximalRQLS (ι × κ) where
  square := A.square.tensor B.square
  resolution := A.resolution.tensor B.resolution
  maximal := by
    intro p q p' q' h
    rcases phaseEquivalent_tensorKet_factors
      (A.square.row_norm p.1 q.1) (A.square.row_norm p'.1 q'.1)
      (B.square.row_norm p.2 q.2) (B.square.row_norm p'.2 q'.2) h with
      ⟨hA, hB⟩
    rcases A.maximal hA with ⟨hp₁, hq₁⟩
    rcases B.maximal hB with ⟨hp₂, hq₂⟩
    exact ⟨Prod.ext hp₁ hp₂, Prod.ext hq₁ hq₂⟩

theorem existsMaximalRQLS_mul {m n : ℕ}
    (hm : ExistsMaximalRQLS m) (hn : ExistsMaximalRQLS n) :
    ExistsMaximalRQLS (m * n) := by
  rcases hm with ⟨A⟩
  rcases hn with ⟨B⟩
  simpa [Fintype.card_prod] using existsMaximalRQLS_card (A.tensor B)

end LeanCo.QuantumLatin
