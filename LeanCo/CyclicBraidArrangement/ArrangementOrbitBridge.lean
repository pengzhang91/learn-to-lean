import LeanCo.CyclicBraidArrangement.ArrangementCharacteristic
import Mathlib.Data.ZMod.Basic

/-!
# Translation orbits of the genuine finite-field complement

The defining equations depend only on coordinate differences.  This file
removes the diagonal translation direction by choosing the unique translate
whose coordinate at label `0` vanishes.
-/

namespace CyclicBraidArrangement

namespace DeformationMatrix

variable {n : ℕ} [NeZero n]

/-- Complement points normalized by translating the coordinate of label `0`
to zero. -/
def AnchoredFiniteFieldComplement (M : DeformationMatrix n)
    (R : Type*) [Ring R] :=
  {x : M.FiniteFieldComplement R // x.1 (0 : Fin n) = 0}

noncomputable instance anchoredFiniteFieldComplementFintype
    (M : DeformationMatrix n) (R : Type*) [Ring R] [Fintype R] :
    Fintype (M.AnchoredFiniteFieldComplement R) := by
  letI : Finite R := Finite.of_fintype R
  letI : Finite (Fin n → R) := by infer_instance
  letI : Finite (M.FiniteFieldComplement R) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (M.AnchoredFiniteFieldComplement R) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Every complement point is uniquely a scalar translate of an anchored
complement point. -/
noncomputable def finiteFieldComplementEquivTranslateAnchor
    (M : DeformationMatrix n) (R : Type*) [CommRing R] :
    M.FiniteFieldComplement R ≃ R × M.AnchoredFiniteFieldComplement R where
  toFun x :=
    let c := x.1 (0 : Fin n)
    (c, ⟨⟨fun i ↦ x.1 i - c, by
      intro e he
      apply x.2 e
      unfold SatisfiesEquation at he ⊢
      linear_combination he⟩, by simp [c]⟩)
  invFun cx := ⟨fun i ↦ cx.2.1.1 i + cx.1, by
    intro e he
    apply cx.2.1.2 e
    unfold SatisfiesEquation at he ⊢
    linear_combination he⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp
  right_inv cx := by
    rcases cx with ⟨c, x⟩
    apply Prod.ext
    · change x.1.1 (0 : Fin n) + c = c
      rw [x.2, zero_add]
    · apply Subtype.ext
      apply Subtype.ext
      funext i
      change x.1.1 i + c - (x.1.1 (0 : Fin n) + c) = x.1.1 i
      rw [x.2]
      simp

/-- Cardinal form of freeness of the simultaneous-translation action. -/
theorem card_finiteFieldComplement_eq_card_mul_anchor
    (M : DeformationMatrix n) (R : Type*) [CommRing R] [Fintype R] :
    Fintype.card (M.FiniteFieldComplement R) =
      Fintype.card R * Fintype.card (M.AnchoredFiniteFieldComplement R) := by
  classical
  rw [Fintype.card_congr (M.finiteFieldComplementEquivTranslateAnchor R),
    Fintype.card_prod]

/-- For a prime modulus the full complement has `q` points in every free
translation orbit. -/
theorem card_zmodComplement_eq_prime_mul_anchor
    (M : DeformationMatrix n) (q : ℕ) [NeZero q] (_hq : Nat.Prime q) :
    Fintype.card (M.FiniteFieldComplement (ZMod q)) =
      q * Fintype.card (M.AnchoredFiniteFieldComplement (ZMod q)) := by
  rw [M.card_finiteFieldComplement_eq_card_mul_anchor (ZMod q), ZMod.card q]

end DeformationMatrix

end CyclicBraidArrangement
