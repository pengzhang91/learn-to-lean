import LeanCo.QuantumLatin.Fourier

/-!
# The cyclic certificates in odd order

This file formalizes the two piecewise complete mappings in Huang--Li,
Lemma 2.8.  Writing the odd order as `4*q+1` or `4*q+3` removes all divisions
from the paper's formulas.
-/

namespace LeanCo.QuantumLatin

/-! ## The `4*q+1` map -/

/-- The natural-number representative of Huang--Li's map in order `4*q+1`.
The argument is intended to lie in `[0,4*q]`. -/
def oddMuOneNat (q k : ℕ) : ℕ :=
  if k ≤ 2 * q - 2 then k
  else if k = 2 * q - 1 then k + 1
  else if k = 4 * q then k - 1
  else if k % 2 = 0 then k + 2
  else k - 2

theorem oddMuOneNat_lt (hq : 2 ≤ q) {k : ℕ} (hk : k < 4 * q + 1) :
    oddMuOneNat q k < 4 * q + 1 := by
  simp only [oddMuOneNat]
  split_ifs <;> omega

theorem oddMuOneNat_injective_on (hq : 2 ≤ q) {k l : ℕ}
    (hk : k < 4 * q + 1) (hl : l < 4 * q + 1)
    (h : oddMuOneNat q k = oddMuOneNat q l) : k = l := by
  simp only [oddMuOneNat] at h
  split_ifs at h <;> omega

/-- Huang--Li's complete mapping for orders congruent to one modulo four. -/
def oddMuOne (q : ℕ) (x : ZMod (4 * q + 1)) : ZMod (4 * q + 1) :=
  oddMuOneNat q x.val

theorem oddMuOne_val (hq : 2 ≤ q) (x : ZMod (4 * q + 1)) :
    (oddMuOne q x).val = oddMuOneNat q x.val := by
  exact ZMod.val_cast_of_lt (oddMuOneNat_lt hq x.val_lt)

theorem oddMuOne_bijective (hq : 2 ≤ q) :
    Function.Bijective (oddMuOne q) := by
  apply Function.Injective.bijective_of_finite
  intro x y hxy
  apply ZMod.val_injective
  have hv := congrArg ZMod.val hxy
  rw [oddMuOne_val hq, oddMuOne_val hq] at hv
  exact oddMuOneNat_injective_on hq x.val_lt y.val_lt hv

/-! The following function is the least nonnegative representative of
`oddMuOne q x + x`.  Keeping it explicit makes the second permutation check a
finite piecewise-linear calculation. -/
def oddCompleteOneNat (q k : ℕ) : ℕ :=
  if k ≤ 2 * q - 2 then 2 * k
  else if k = 2 * q - 1 then 4 * q - 1
  else if k = 4 * q then 4 * q - 2
  else if k % 2 = 0 then 2 * k - 4 * q + 1
  else if k = 2 * q + 1 then 4 * q
  else 2 * k - 4 * q - 3

theorem oddCompleteOneNat_lt (hq : 2 ≤ q) {k : ℕ} (hk : k < 4 * q + 1) :
    oddCompleteOneNat q k < 4 * q + 1 := by
  simp only [oddCompleteOneNat]
  split_ifs <;> omega

theorem oddCompleteOneNat_injective_on (hq : 2 ≤ q) {k l : ℕ}
    (hk : k < 4 * q + 1) (hl : l < 4 * q + 1)
    (h : oddCompleteOneNat q k = oddCompleteOneNat q l) : k = l := by
  simp only [oddCompleteOneNat] at h
  split_ifs at h <;> omega

theorem oddMuOne_add_val (hq : 2 ≤ q) (x : ZMod (4 * q + 1)) :
    (oddMuOne q x + x).val = oddCompleteOneNat q x.val := by
  by_cases hs : (oddMuOne q x).val + x.val < 4 * q + 1
  · rw [ZMod.val_add_of_lt hs, oddMuOne_val hq]
    rw [oddMuOne_val hq] at hs
    simp only [oddMuOneNat, oddCompleteOneNat] at hs ⊢
    split_ifs at hs ⊢ <;> omega
  · rw [ZMod.val_add_of_le (by omega), oddMuOne_val hq]
    rw [oddMuOne_val hq] at hs
    simp only [oddMuOneNat, oddCompleteOneNat] at hs ⊢
    split_ifs at hs ⊢ <;> omega

theorem oddMuOne_add_bijective (hq : 2 ≤ q) :
    Function.Bijective (fun x : ZMod (4 * q + 1) ↦ oddMuOne q x + x) := by
  apply Function.Injective.bijective_of_finite
  intro x y hxy
  apply ZMod.val_injective
  have hv := congrArg ZMod.val hxy
  rw [oddMuOne_add_val hq, oddMuOne_add_val hq] at hv
  exact oddCompleteOneNat_injective_on hq x.val_lt y.val_lt hv

@[simp] theorem oddMuOne_zero (hq : 2 ≤ q) :
    oddMuOne q 0 = 0 := by
  apply ZMod.val_injective
  rw [oddMuOne_val hq]
  simp [oddMuOneNat]

@[simp] theorem oddMuOne_one (hq : 2 ≤ q) :
    oddMuOne q 1 = 1 := by
  apply ZMod.val_injective
  rw [oddMuOne_val hq]
  letI : Fact (1 < 4 * q + 1) := ⟨by omega⟩
  have hval : (1 : ZMod (4 * q + 1)).val = 1 := ZMod.val_one _
  rw [hval]
  simp only [oddMuOneNat]
  split_ifs <;> omega

theorem oddMuOne_last (hq : 2 ≤ q) :
    oddMuOne q ((4 * q : ℕ) : ZMod (4 * q + 1)) =
      (4 * q - 1 : ℕ) := by
  apply ZMod.val_injective
  rw [oddMuOne_val hq, ZMod.val_cast_of_lt (by omega),
    ZMod.val_cast_of_lt (by omega)]
  simp only [oddMuOneNat]
  split_ifs <;> omega

theorem oddMuOne_separating (hq : 2 ≤ q) :
    ∀ a b : ZMod (4 * q + 1),
      (∀ t, a * oddMuOne q t + b * t = a * oddMuOne q 0) →
        a = 0 ∧ b = 0 := by
  intro a b h
  have h₁ := h 1
  have hlast := h ((4 * q : ℕ) : ZMod (4 * q + 1))
  rw [oddMuOne_zero hq, oddMuOne_one hq] at h₁
  rw [oddMuOne_zero hq, oddMuOne_last hq] at hlast
  have harg : ((4 * q : ℕ) : ZMod (4 * q + 1)) = -1 := by
    rw [show 4 * q = (4 * q + 1) - 1 by omega, Nat.cast_sub (by omega)]
    have hz : ((4 * q + 1 : ℕ) : ZMod (4 * q + 1)) = 0 :=
      ZMod.natCast_self _
    norm_num
  have hout : ((4 * q - 1 : ℕ) : ZMod (4 * q + 1)) = -2 := by
    rw [show 4 * q - 1 = (4 * q + 1) - 2 by omega, Nat.cast_sub (by omega)]
    have hz : ((4 * q + 1 : ℕ) : ZMod (4 * q + 1)) = 0 :=
      ZMod.natCast_self _
    norm_num
  rw [harg, hout] at hlast
  constructor
  · linear_combination -h₁ - hlast
  · have ha : a = 0 := by linear_combination -h₁ - hlast
    rw [ha] at h₁
    simpa using h₁

theorem oddMuOne_certificate (hq : 2 ≤ q) :
    CyclicCertificate (4 * q + 1) (oddMuOne q) where
  perm := oddMuOne_bijective hq
  complete := oddMuOne_add_bijective hq
  separating := oddMuOne_separating hq

/-! ## The `4*q+3` map -/

/-- The natural-number representative of Huang--Li's map in order `4*q+3`.
The argument is intended to lie in `[0,4*q+2]`. -/
def oddMuThreeNat (q k : ℕ) : ℕ :=
  if k ≤ 2 * q - 1 then k
  else if k = 2 * q then k + 1
  else if k = 4 * q + 1 then k + 1
  else if k % 2 = 1 then k + 2
  else k - 2

theorem oddMuThreeNat_lt (hq : 1 ≤ q) {k : ℕ} (hk : k < 4 * q + 3) :
    oddMuThreeNat q k < 4 * q + 3 := by
  simp only [oddMuThreeNat]
  split_ifs <;> omega

theorem oddMuThreeNat_injective_on (hq : 1 ≤ q) {k l : ℕ}
    (hk : k < 4 * q + 3) (hl : l < 4 * q + 3)
    (h : oddMuThreeNat q k = oddMuThreeNat q l) : k = l := by
  simp only [oddMuThreeNat] at h
  split_ifs at h <;> omega

/-- Huang--Li's complete mapping for orders congruent to three modulo four. -/
def oddMuThree (q : ℕ) (x : ZMod (4 * q + 3)) : ZMod (4 * q + 3) :=
  oddMuThreeNat q x.val

theorem oddMuThree_val (hq : 1 ≤ q) (x : ZMod (4 * q + 3)) :
    (oddMuThree q x).val = oddMuThreeNat q x.val := by
  exact ZMod.val_cast_of_lt (oddMuThreeNat_lt hq x.val_lt)

theorem oddMuThree_bijective (hq : 1 ≤ q) :
    Function.Bijective (oddMuThree q) := by
  apply Function.Injective.bijective_of_finite
  intro x y hxy
  apply ZMod.val_injective
  have hv := congrArg ZMod.val hxy
  rw [oddMuThree_val hq, oddMuThree_val hq] at hv
  exact oddMuThreeNat_injective_on hq x.val_lt y.val_lt hv

/-- The least nonnegative representative of `oddMuThree q x + x`. -/
def oddCompleteThreeNat (q k : ℕ) : ℕ :=
  if k ≤ 2 * q - 1 then 2 * k
  else if k = 2 * q then 4 * q + 1
  else if k = 4 * q + 1 then 4 * q
  else if k % 2 = 1 then 2 * k - 4 * q - 1
  else if k = 2 * q + 2 then 4 * q + 2
  else if k = 4 * q + 2 then 4 * q - 1
  else 2 * k - 4 * q - 5

theorem oddCompleteThreeNat_lt (hq : 1 ≤ q) {k : ℕ} (hk : k < 4 * q + 3) :
    oddCompleteThreeNat q k < 4 * q + 3 := by
  simp only [oddCompleteThreeNat]
  split_ifs <;> omega

theorem oddCompleteThreeNat_injective_on (hq : 1 ≤ q) {k l : ℕ}
    (hk : k < 4 * q + 3) (hl : l < 4 * q + 3)
    (h : oddCompleteThreeNat q k = oddCompleteThreeNat q l) : k = l := by
  simp only [oddCompleteThreeNat] at h
  split_ifs at h <;> omega

theorem oddMuThree_add_val (hq : 1 ≤ q) (x : ZMod (4 * q + 3)) :
    (oddMuThree q x + x).val = oddCompleteThreeNat q x.val := by
  by_cases hs : (oddMuThree q x).val + x.val < 4 * q + 3
  · rw [ZMod.val_add_of_lt hs, oddMuThree_val hq]
    rw [oddMuThree_val hq] at hs
    simp only [oddMuThreeNat, oddCompleteThreeNat] at hs ⊢
    split_ifs at hs ⊢ <;> omega
  · rw [ZMod.val_add_of_le (by omega), oddMuThree_val hq]
    rw [oddMuThree_val hq] at hs
    simp only [oddMuThreeNat, oddCompleteThreeNat] at hs ⊢
    split_ifs at hs ⊢ <;> omega

theorem oddMuThree_add_bijective (hq : 1 ≤ q) :
    Function.Bijective (fun x : ZMod (4 * q + 3) ↦ oddMuThree q x + x) := by
  apply Function.Injective.bijective_of_finite
  intro x y hxy
  apply ZMod.val_injective
  have hv := congrArg ZMod.val hxy
  rw [oddMuThree_add_val hq, oddMuThree_add_val hq] at hv
  exact oddCompleteThreeNat_injective_on hq x.val_lt y.val_lt hv

@[simp] theorem oddMuThree_zero (hq : 1 ≤ q) :
    oddMuThree q 0 = 0 := by
  apply ZMod.val_injective
  rw [oddMuThree_val hq]
  simp [oddMuThreeNat]

@[simp] theorem oddMuThree_one (hq : 1 ≤ q) :
    oddMuThree q 1 = 1 := by
  apply ZMod.val_injective
  rw [oddMuThree_val hq]
  letI : Fact (1 < 4 * q + 3) := ⟨by omega⟩
  have hval : (1 : ZMod (4 * q + 3)).val = 1 := ZMod.val_one _
  rw [hval]
  simp only [oddMuThreeNat]
  split_ifs <;> omega

theorem oddMuThree_last (hq : 1 ≤ q) :
    oddMuThree q ((4 * q + 2 : ℕ) : ZMod (4 * q + 3)) =
      (4 * q : ℕ) := by
  apply ZMod.val_injective
  rw [oddMuThree_val hq, ZMod.val_cast_of_lt (by omega),
    ZMod.val_cast_of_lt (by omega)]
  simp only [oddMuThreeNat]
  split_ifs <;> omega

theorem oddMuThree_separating (hq : 1 ≤ q) :
    ∀ a b : ZMod (4 * q + 3),
      (∀ t, a * oddMuThree q t + b * t = a * oddMuThree q 0) →
        a = 0 ∧ b = 0 := by
  intro a b h
  have h₁ := h 1
  have hlast := h ((4 * q + 2 : ℕ) : ZMod (4 * q + 3))
  rw [oddMuThree_zero hq, oddMuThree_one hq] at h₁
  rw [oddMuThree_zero hq, oddMuThree_last hq] at hlast
  have harg : ((4 * q + 2 : ℕ) : ZMod (4 * q + 3)) = -1 := by
    rw [show 4 * q + 2 = (4 * q + 3) - 1 by omega, Nat.cast_sub (by omega)]
    have hz : ((4 * q + 3 : ℕ) : ZMod (4 * q + 3)) = 0 :=
      ZMod.natCast_self _
    norm_num
  have hout : ((4 * q : ℕ) : ZMod (4 * q + 3)) = -3 := by
    rw [show 4 * q = (4 * q + 3) - 3 by omega, Nat.cast_sub (by omega)]
    have hz : ((4 * q + 3 : ℕ) : ZMod (4 * q + 3)) = 0 :=
      ZMod.natCast_self _
    norm_num
  rw [harg, hout] at hlast
  have ha2 : a + a = 0 := by
    linear_combination -h₁ - hlast
  have hodd : Odd (4 * q + 3) := ⟨2 * q + 1, by omega⟩
  have ha : a = 0 := (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp ha2
  refine ⟨ha, ?_⟩
  rw [ha] at h₁
  simpa using h₁

theorem oddMuThree_certificate (hq : 1 ≤ q) :
    CyclicCertificate (4 * q + 3) (oddMuThree q) where
  perm := oddMuThree_bijective hq
  complete := oddMuThree_add_bijective hq
  separating := oddMuThree_separating hq

/-! ## Every odd order at least seven -/

theorem odd_eq_four_mul_add_one_or_three {N : ℕ} (hN : Odd N) :
    ∃ q, N = 4 * q + 1 ∨ N = 4 * q + 3 := by
  rcases hN with ⟨k, hk⟩
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' k
  · exact ⟨q, Or.inl (by omega)⟩
  · exact ⟨q, Or.inr (by omega)⟩

/-- Huang--Li Lemma 2.8 at the algebraic-certificate level: every odd order
at least seven admits the complete and separating mapping needed by the
cyclic Fourier construction. -/
theorem exists_odd_cyclicCertificate (N : ℕ) [NeZero N]
    (hN : 7 ≤ N) (hodd : Odd N) :
    Nonempty { μ : ZMod N → ZMod N // CyclicCertificate N μ } := by
  obtain ⟨q, hq | hq⟩ := odd_eq_four_mul_add_one_or_three hodd
  · subst N
    have hq2 : 2 ≤ q := by omega
    exact ⟨⟨oddMuOne q, oddMuOne_certificate hq2⟩⟩
  · subst N
    have hq1 : 1 ≤ q := by omega
    exact ⟨⟨oddMuThree q, oddMuThree_certificate hq1⟩⟩

end LeanCo.QuantumLatin
