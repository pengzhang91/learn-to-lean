import LeanCo.QuantumLatin.SingularInputs
import LeanCo.QuantumLatin.SingularResolution

/-!
# The completed singular direct-product construction

This file packages the three independently verified parts of Construction 4.6:
the quantum Latin square, its resolution, and its maximal-cardinality proof.
It also gives the numerical `mn + h` form used by the order argument.
-/

namespace LeanCo.QuantumLatin

universe u v w x

variable {α : Type u} {β : Type v} {ρ : Type w} {γ : Type x}
  [Fintype α] [Fintype β] [Fintype ρ] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq ρ] [DecidableEq γ]

/-- Construction 4.6, packaged end to end: regular ordinary and pointed
inputs supply the separated copies, and the resulting singular square has
both a resolution and maximal cardinality. -/
theorem existsMaximalRQLS_singularProduct
    (A : ClassicalBiresolution α) (split : α ≃ (γ ⊕ ρ))
    (R : MaximalRQLS β) (P : PointedMaximalRQLS β)
    (D : MaximalRQLS ρ) {d e : β}
    (hR : ∀ i j, R.square.entry i j d ≠ 0 ∧
      R.square.entry i j e ≠ 0)
    (hP : P.RegularAt d e) :
    ExistsMaximalRQLS
      (Fintype.card α * Fintype.card β + Fintype.card ρ) := by
  classical
  obtain ⟨X, hX⟩ := SingularProductData.exists_data_and_separation
    A split R P D hR hP
  let M : MaximalRQLS ((α × β) ⊕ ρ) := {
    square := X.square
    resolution := X.resolution
    maximal := X.square_hasMaximalCardinality hX }
  simpa [Fintype.card_sum, Fintype.card_prod] using
    existsMaximalRQLS_card M

/-- Numerical form of the singular construction.  A biresolution of order
`n`, regular inner data of order `m`, and an exceptional square of order
`h ≤ n` produce a maximal resolvable square of order `n * m + h`. -/
theorem existsMaximalRQLS_singularProduct_fin
    {n m h : ℕ} (hhn : h ≤ n)
    (A : ClassicalBiresolution (Fin n))
    (R : MaximalRQLS (Fin m)) (P : PointedMaximalRQLS (Fin m))
    (D : MaximalRQLS (Fin h)) {d e : Fin m}
    (hR : ∀ i j, R.square.entry i j d ≠ 0 ∧
      R.square.entry i j e ≠ 0)
    (hP : P.RegularAt d e) :
    ExistsMaximalRQLS (n * m + h) := by
  let split : Fin n ≃ (Fin (n - h) ⊕ Fin h) :=
    Fintype.equivOfCardEq (by simp [Nat.sub_add_cancel hhn])
  simpa using existsMaximalRQLS_singularProduct
    (α := Fin n) (β := Fin m) (ρ := Fin h) (γ := Fin (n - h))
    A split R P D hR hP

end LeanCo.QuantumLatin
