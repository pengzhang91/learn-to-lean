import LeanCo.Negami.CategoricalBoundary
import LeanCo.Negami.BoundaryQuotient
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# The splitting matrix and inverse-kernel formula

This file connects the categorical boundary sectors with the quotient-vector
presentation of Sections 5 and 7 of arXiv:2608.30053.  It proves `q = T F`
from quotient witnesses and then derives the final splitting identity from a
left inverse of the symmetric connectivity matrix.
-/

open scoped BigOperators Matrix

namespace LeanCo.Negami
namespace BoundaryData

variable {P : Type} [Fintype P] [DecidableEq P]

/-- The connectivity matrix `T`, evaluated at a scalar `t`. -/
def connectivityMatrix {R : Type*} [Semiring R]
    (ρ : P → P → ℕ) (t : R) : Matrix P P R :=
  fun π σ ↦ t ^ ρ π σ

omit [Fintype P] [DecidableEq P] in
/-- Symmetry of generated boundary connectivity makes `T` symmetric. -/
theorem connectivityMatrix_transpose {R : Type*} [Semiring R]
    (ρ : P → P → ℕ) (t : R) (hρ : ∀ π σ, ρ π σ = ρ σ π) :
    (connectivityMatrix ρ t)ᵀ = connectivityMatrix ρ t := by
  ext π σ
  simp [connectivityMatrix, hρ]

/-- Hilbert polynomials of the individual boundary sectors, assembled as a
column vector. -/
noncomputable def boundaryStateVector {R : Type*} [CommSemiring R]
    (K : BoundaryData P) (t x y : R) : P → R :=
  fun π ↦ (K.boundaryObject π).hilbert t x y

/-- State sums of a partition-indexed family of boundary quotients. -/
noncomputable def quotientStateVector {R : Type*} [CommSemiring R]
    (Q : P → NegamiData) (t x y : R) : P → R :=
  fun α ↦ (Q α).stateSum t x y

/-- Scalar bilinear pairing represented by a matrix. -/
noncomputable def boundaryPairing {R : Type*} [CommSemiring R]
    (T : Matrix P P R) (F H : P → R) : R :=
  F ⬝ᵥ (T *ᵥ H)

/-- Expansion of the connectivity pairing into its boundary-sector sum. -/
theorem boundaryPairing_connectivity_eq_pair_sum
    {R : Type*} [CommSemiring R] (ρ : P → P → ℕ)
    (K H : BoundaryData P) (t x y : R) :
    boundaryPairing (connectivityMatrix ρ t)
        (boundaryStateVector K t x y) (boundaryStateVector H t x y) =
      ∑ p : P × P, t ^ ρ p.1 p.2 *
        (K.boundaryObject p.1).hilbert t x y *
        (H.boundaryObject p.2).hilbert t x y := by
  classical
  rw [Fintype.sum_prod_type]
  simp [boundaryPairing, connectivityMatrix, boundaryStateVector,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro σ _
  ac_rfl

/-- The categorical gluing equivalence decategorifies to the matrix
boundary pairing. -/
theorem Gluing.stateSum_eq_boundaryPairing
    {G : NegamiData} {K H : BoundaryData P} {ρ : P → P → ℕ}
    (W : Gluing G K H ρ) {R : Type*} [CommSemiring R] (t x y : R) :
    G.stateSum t x y =
      boundaryPairing (connectivityMatrix ρ t)
        (boundaryStateVector K t x y) (boundaryStateVector H t x y) := by
  calc
    G.stateSum t x y = G.stateObject.hilbert t x y :=
      (G.hilbert_stateObject t x y).symm
    _ = ∑ p : P × P, t ^ ρ p.1 p.2 *
        (K.boundaryObject p.1).hilbert t x y *
        (H.boundaryObject p.2).hilbert t x y :=
      W.hilbert_categoricalPairing t x y
    _ = boundaryPairing (connectivityMatrix ρ t)
        (boundaryStateVector K t x y) (boundaryStateVector H t x y) :=
      (boundaryPairing_connectivity_eq_pair_sum ρ K H t x y).symm

/-- Scalar state sum written on the original boundary graph after imposing
one boundary partition. -/
noncomputable def quotientBoundarySum {R : Type*} [CommSemiring R]
    (K : BoundaryData P) (ρ : P → P → ℕ) (α : P) (t x y : R) : R :=
  ∑ S : Finset K.Edge,
    t ^ (K.internalComponents S + ρ α (K.boundaryType S)) *
      x ^ S.card * y ^ (Nat.card K.Edge - S.card)

/-- A quotient witness transports its state sum back to the original edge
states and the quotient component formula. -/
theorem Quotient.stateSum_eq_quotientBoundarySum
    {K : BoundaryData P} {Q : NegamiData} {ρ : P → P → ℕ} {α : P}
    (W : Quotient K Q ρ α) {R : Type*} [CommSemiring R] (t x y : R) :
    Q.stateSum t x y = quotientBoundarySum K ρ α t x y := by
  classical
  unfold NegamiData.stateSum quotientBoundarySum
  exact Fintype.sum_equiv W.states _ _ fun S ↦ by
    rw [W.component_formula, W.selected_card, W.edge_card]

/-- Regrouping the quotient state sum by boundary type gives one row of
`T F`. -/
theorem quotientBoundarySum_eq_mulVec
    {R : Type*} [CommSemiring R] (K : BoundaryData P)
    (ρ : P → P → ℕ) (α : P) (t x y : R) :
    quotientBoundarySum K ρ α t x y =
      (connectivityMatrix ρ t *ᵥ boundaryStateVector K t x y) α := by
  classical
  let e := (Equiv.sigmaFiberEquiv K.boundaryType).symm
  calc
    quotientBoundarySum K ρ α t x y =
        ∑ z : (π : P) × {S : Finset K.Edge // K.boundaryType S = π},
          t ^ (K.internalComponents z.2.1 + ρ α z.1) *
            x ^ z.2.1.card * y ^ (Nat.card K.Edge - z.2.1.card) := by
      unfold quotientBoundarySum
      exact Fintype.sum_equiv e _ _ fun S ↦ by rfl
    _ = ∑ π : P, t ^ ρ α π *
        (K.boundaryObject π).hilbert t x y := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro π _
      change (∑ S : {S : Finset K.Edge // K.boundaryType S = π},
          t ^ (K.internalComponents S.1 + ρ α π) *
            x ^ S.1.card * y ^ (Nat.card K.Edge - S.1.card)) =
        t ^ ρ α π *
          ∑ S : {S : Finset K.Edge // K.boundaryType S = π},
            t ^ K.internalComponents S.1 * x ^ S.1.card *
              y ^ (Nat.card K.Edge - S.1.card)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      simp [pow_add]
      ring
    _ = (connectivityMatrix ρ t *ᵥ boundaryStateVector K t x y) α := by
      simp [connectivityMatrix, Matrix.mulVec, dotProduct]
      rfl

/-- Lemma 5.1 in vector form at a single boundary partition. -/
theorem Quotient.stateSum_eq_mulVec
    {K : BoundaryData P} {Q : NegamiData} {ρ : P → P → ℕ} {α : P}
    (W : Quotient K Q ρ α) {R : Type*} [CommSemiring R] (t x y : R) :
    Q.stateSum t x y =
      (connectivityMatrix ρ t *ᵥ boundaryStateVector K t x y) α := by
  rw [W.stateSum_eq_quotientBoundarySum]
  exact quotientBoundarySum_eq_mulVec K ρ α t x y

/-- Lemma 5.1 simultaneously for all boundary partitions: `q = T F`. -/
theorem quotientStateVector_eq_mulVec
    {K : BoundaryData P} (Q : P → NegamiData) (ρ : P → P → ℕ)
    (W : ∀ α, Quotient K (Q α) ρ α)
    {R : Type*} [CommSemiring R] (t x y : R) :
    quotientStateVector Q t x y =
      connectivityMatrix ρ t *ᵥ boundaryStateVector K t x y := by
  funext α
  exact (W α).stateSum_eq_mulVec t x y

/-- Pure linear algebra behind the inverse-kernel splitting formula.  A left
inverse suffices because the connectivity matrix is symmetric. -/
theorem inverseKernel_splitting
    {F : Type*} [Field F] (T B : Matrix P P F)
    (f h qf qh : P → F) (hT : Tᵀ = T) (hBT : B * T = 1)
    (hqf : qf = T *ᵥ f) (hqh : qh = T *ᵥ h) :
    boundaryPairing T f h = qf ⬝ᵥ (B *ᵥ qh) := by
  rw [hqf, hqh, Matrix.mulVec_mulVec, hBT, Matrix.one_mulVec]
  rw [boundaryPairing]
  calc
    f ⬝ᵥ (T *ᵥ h) = f ⬝ᵥ (Tᵀ *ᵥ h) := by rw [hT]
    _ = h ⬝ᵥ (T *ᵥ f) := Matrix.dotProduct_transpose_mulVec T f h
    _ = (T *ᵥ f) ⬝ᵥ h := dotProduct_comm _ _

/-- The full scalar Negami splitting formula obtained from categorical
gluing, the two quotient vectors, and an inverse kernel. -/
theorem Gluing.negami_splitting
    {G : NegamiData} {K H : BoundaryData P} {ρ : P → P → ℕ}
    (WG : Gluing G K H ρ) (QK QH : P → NegamiData)
    (WK : ∀ α, Quotient K (QK α) ρ α)
    (WH : ∀ α, Quotient H (QH α) ρ α)
    {F : Type*} [Field F] (t x y : F)
    (B : Matrix P P F) (hρ : ∀ π σ, ρ π σ = ρ σ π)
    (hBT : B * connectivityMatrix ρ t = 1) :
    G.stateSum t x y =
      quotientStateVector QK t x y ⬝ᵥ
        (B *ᵥ quotientStateVector QH t x y) := by
  rw [WG.stateSum_eq_boundaryPairing]
  apply inverseKernel_splitting
  · exact connectivityMatrix_transpose ρ t hρ
  · exact hBT
  · exact quotientStateVector_eq_mulVec QK ρ WK t x y
  · exact quotientStateVector_eq_mulVec QH ρ WH t x y

end BoundaryData
end LeanCo.Negami
