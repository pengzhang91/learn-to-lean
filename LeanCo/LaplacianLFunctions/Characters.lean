import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Fourier recovery on a finite abelian group

This file isolates the character-theoretic step used in the proof that the
two-variable `L`-functions of a graph recover its rank function.  It is stated
for arbitrary complex-valued coefficient functions on a finite abelian group.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The (unnormalized) Fourier transform, with the convention used by the
graph `L`-function in arXiv:2608.29981. -/
def characterWeightedSum (f : A → ℂ) (chi : AddChar A ℂ) : ℂ :=
  ∑ a : A, f a * chi a

/-- Character orthogonality gives an explicit inverse for
`characterWeightedSum`. -/
theorem sum_character_mul_characterWeightedSum (f : A → ℂ) (b : A) :
    ∑ chi : AddChar A ℂ, chi (-b) * characterWeightedSum f chi =
      (Fintype.card A : ℂ) * f b := by
  classical
  calc
    ∑ chi : AddChar A ℂ, chi (-b) * characterWeightedSum f chi =
        ∑ chi : AddChar A ℂ, ∑ a : A, chi (-b) * (f a * chi a) := by
          simp only [characterWeightedSum, Finset.mul_sum]
    _ = ∑ a : A, ∑ chi : AddChar A ℂ, chi (-b) * (f a * chi a) :=
      Finset.sum_comm
    _ = ∑ a : A, f a * (∑ chi : AddChar A ℂ, chi (a - b)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      calc
        chi (-b) * (f a * chi a) = f a * (chi (-b) * chi a) := by ring
        _ = f a * chi (-b + a) := by rw [AddChar.map_add_eq_mul]
        _ = f a * chi (a - b) := by rw [add_comm, sub_eq_add_neg]
    _ = (Fintype.card A : ℂ) * f b := by
      simp only [AddChar.sum_apply_eq_ite]
      simp [sub_eq_zero, mul_comm]

/-- A function on a finite abelian group is determined by all of its
character-weighted sums.  This is the finite Fourier-recovery step in the main
theorem of arXiv:2608.29981. -/
theorem eq_of_characterWeightedSum_eq (f g : A → ℂ)
    (h : ∀ chi : AddChar A ℂ,
      characterWeightedSum f chi = characterWeightedSum g chi) :
    f = g := by
  funext b
  have hsums :
      (∑ chi : AddChar A ℂ, chi (-b) * characterWeightedSum f chi) =
        ∑ chi : AddChar A ℂ, chi (-b) * characterWeightedSum g chi := by
    apply Finset.sum_congr rfl
    intro chi _
    rw [h chi]
  rw [sum_character_mul_characterWeightedSum,
    sum_character_mul_characterWeightedSum] at hsums
  exact (mul_left_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hsums)

/-- Direct-sum spelling of `eq_of_characterWeightedSum_eq`, convenient when
the Fourier sums occur literally in a coefficient computation. -/
theorem eq_of_forall_sum_mul_addChar_eq (f g : A → ℂ)
    (h : ∀ chi : AddChar A ℂ,
      (∑ a : A, f a * chi a) = ∑ a : A, g a * chi a) :
    f = g := by
  apply eq_of_characterWeightedSum_eq
  simpa only [characterWeightedSum] using h

/-- Natural-number-valued coefficients are also recovered by their complex
character sums.  This is useful after evaluating the geometric polynomial
`1 + u + ⋯ + u^(h - 1)` at `u = 1`, where its value is `h`. -/
theorem nat_eq_of_forall_sum_mul_addChar_eq (f g : A → ℕ)
    (h : ∀ chi : AddChar A ℂ,
      (∑ a : A, (f a : ℂ) * chi a) =
        ∑ a : A, (g a : ℂ) * chi a) :
    f = g := by
  have hcomplex : (fun a : A ↦ (f a : ℂ)) = fun a : A ↦ (g a : ℂ) :=
    eq_of_forall_sum_mul_addChar_eq _ _ h
  funext a
  exact Nat.cast_injective (congrFun hcomplex a)

/-- Fourier recovery transported across an additive equivalence.  This is the
form used when the two graph Jacobians are identified by the isomorphism in
Theorem 4.3. -/
theorem eq_comp_addEquiv_of_forall_character_sum_eq
    {B : Type*} [AddCommGroup B] [Fintype B]
    (e : B ≃+ A) (f : A → ℂ) (g : B → ℂ)
    (h : ∀ chi : AddChar A ℂ,
      (∑ a : A, f a * chi a) =
        ∑ b : B, g b * chi (e b)) :
    ∀ b : B, f (e b) = g b := by
  let gOnA : A → ℂ := fun a ↦ g (e.symm a)
  have htransform : ∀ chi : AddChar A ℂ,
      (∑ a : A, f a * chi a) = ∑ a : A, gOnA a * chi a := by
    intro chi
    rw [h chi]
    exact Fintype.sum_equiv e
      (fun b : B ↦ g b * chi (e b))
      (fun a : A ↦ gOnA a * chi a)
      (fun b ↦ by simp [gOnA])
  have hfg : f = gOnA :=
    eq_of_forall_sum_mul_addChar_eq f gOnA htransform
  intro b
  have := congrFun hfg (e b)
  simpa [gOnA] using this

end

end LeanCo.LaplacianLFunctions
