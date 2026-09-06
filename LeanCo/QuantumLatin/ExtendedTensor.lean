import LeanCo.QuantumLatin.Tensor

/-!
# Extended and parameterized tensor products

Literal coordinate implementations of the two operations in Section 4 of
Zhang--Cao.  The target coordinates are `(α × β) ⊕ ρ`, i.e. an `|α||β|`
tensor block followed by `|ρ|` exceptional coordinates.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

universe u v w

/-- Inner product after deleting the distinguished `none` coordinate. -/
def projectedDot {β : Type v} [Fintype β]
    (x y : Ket (Option β)) : ℂ :=
  ∑ b : β, conj (x (some b)) * y (some b)

theorem dot_option_decompose {β : Type v} [Fintype β]
    (x y : Ket (Option β)) :
    dot x y = conj (x none) * y none + projectedDot x y := by
  classical
  rw [dot, Fintype.sum_option]
  rfl

/-- Paper's `a ⊗₊ b`: an ordinary pure tensor followed by zero exceptional
coordinates. -/
def extendedTensor {α : Type u} {β : Type v} {ρ : Type w}
    (x : Ket α) (y : Ket β) : Ket ((α × β) ⊕ ρ)
  | Sum.inl p => x p.1 * y p.2
  | Sum.inr _ => 0

/-- Paper's `a ⊗ᵣ c`: tensor the first `β` coordinates of `c` with `a`
and place the distinguished coordinate of `c` in exceptional coordinate
`r`. -/
def parameterTensor {α : Type u} {β : Type v} {ρ : Type w}
    [DecidableEq ρ] (r : ρ) (x : Ket α) (c : Ket (Option β)) :
    Ket ((α × β) ⊕ ρ)
  | Sum.inl p => x p.1 * c (some p.2)
  | Sum.inr s => if s = r then c none else 0

theorem dot_extendedTensor {α : Type u} {β : Type v} {ρ : Type w}
    [Fintype α] [Fintype β] [Fintype ρ]
    (x x' : Ket α) (y y' : Ket β) :
    dot (extendedTensor (ρ := ρ) x y) (extendedTensor (ρ := ρ) x' y') =
      dot x x' * dot y y' := by
  classical
  rw [dot, Fintype.sum_sum_type]
  simp only [extendedTensor, map_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fintype.sum_prod_type, map_mul]
  simpa only [dot, tensorKet, Fintype.sum_prod_type, map_mul] using
    dot_tensorKet x x' y y'

theorem dot_extended_parameter {α : Type u} {β : Type v} {ρ : Type w}
    [Fintype α] [Fintype β] [Fintype ρ] [DecidableEq ρ]
    (r : ρ) (x x' : Ket α) (y : Ket β) (c : Ket (Option β)) :
    dot (extendedTensor (ρ := ρ) x y) (parameterTensor r x' c) =
      dot x x' * (∑ b : β, conj (y b) * c (some b)) := by
  classical
  rw [dot, Fintype.sum_sum_type]
  simp only [extendedTensor, parameterTensor, map_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fintype.sum_prod_type, map_mul]
  simpa only [dot, tensorKet, Fintype.sum_prod_type, map_mul] using
    dot_tensorKet x x' y (fun b ↦ c (some b))

theorem dot_parameter_extended {α : Type u} {β : Type v} {ρ : Type w}
    [Fintype α] [Fintype β] [Fintype ρ] [DecidableEq ρ]
    (r : ρ) (x x' : Ket α) (c : Ket (Option β)) (y : Ket β) :
    dot (parameterTensor r x c) (extendedTensor (ρ := ρ) x' y) =
      dot x x' * (∑ b : β, conj (c (some b)) * y b) := by
  classical
  rw [dot, Fintype.sum_sum_type]
  simp only [extendedTensor, parameterTensor, map_zero, mul_zero,
    Finset.sum_const_zero, add_zero, Fintype.sum_prod_type, map_mul]
  simpa only [dot, tensorKet, Fintype.sum_prod_type, map_mul] using
    dot_tensorKet x x' (fun b ↦ c (some b)) y

theorem dot_parameterTensor {α : Type u} {β : Type v} {ρ : Type w}
    [Fintype α] [Fintype β] [Fintype ρ] [DecidableEq ρ]
    (r s : ρ) (x x' : Ket α) (c d : Ket (Option β)) :
    dot (parameterTensor r x c) (parameterTensor s x' d) =
      dot x x' * projectedDot c d +
        if r = s then conj (c none) * d none else 0 := by
  classical
  rw [dot, Fintype.sum_sum_type]
  simp only [parameterTensor, Fintype.sum_prod_type, map_mul]
  have htop :
      (∑ a : α, ∑ b : β,
        (conj (x a) * conj (c (some b))) * (x' a * d (some b))) =
        dot x x' * projectedDot c d := by
    simpa only [dot, tensorKet, projectedDot, Fintype.sum_prod_type, map_mul]
      using dot_tensorKet x x' (fun b ↦ c (some b))
        (fun b ↦ d (some b))
  rw [htop]
  by_cases hrs : r = s
  · subst s
    simp
  · have hsr : s ≠ r := Ne.symm hrs
    rw [if_neg hrs]
    apply congrArg (dot x x' * projectedDot c d + ·)
    apply Finset.sum_eq_zero
    intro t _
    by_cases htr : t = r
    · subst t
      simp [hrs]
    · simp [htr]

theorem dot_parameterTensor_same {α : Type u} {β : Type v} {ρ : Type w}
    [Fintype α] [Fintype β] [Fintype ρ] [DecidableEq ρ]
    (r : ρ) (x x' : Ket α) (c d : Ket (Option β))
    (hxx' : dot x x' = 1) :
    dot (parameterTensor r x c) (parameterTensor r x' d) = dot c d := by
  rw [dot_parameterTensor, if_pos rfl, hxx', one_mul, dot_option_decompose]
  ac_rfl

theorem dot_parameterTensor_basis {α : Type u} {β : Type v} {ρ : Type w}
    [Fintype α] [Fintype β] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]
    (r s : ρ) (a a' : α) (c d : Ket (Option β)) :
    dot (parameterTensor r (basis a) c)
      (parameterTensor s (basis a') d) =
      (if a = a' then projectedDot c d else 0) +
        if r = s then conj (c none) * d none else 0 := by
  rw [dot_parameterTensor]
  rw [show dot (basis a) (basis a') = if a = a' then 1 else 0 from
    dot_basis_basis a a']
  by_cases haa : a = a' <;> simp [haa]

end LeanCo.QuantumLatin
