import LeanCo.LaplacianLFunctions.LFunction

/-!
# Recovering the complete rank function from graph L-functions

This file gives the cross-graph Fourier-recovery statement behind Theorem 4.3
of arXiv:2608.29981.  An additive equivalence of Jacobians transports all
character `L`-functions if and only if it transports the Baker--Norine `h`
invariant in every nonnegative degree.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V V' : Type*}
  [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype V'] [Nonempty V'] [DecidableEq V']

/-- Equality of all character-twisted full `L`-functions recovers `h` in
every nonnegative degree, after transporting Jacobian coordinates by `φ`.
This is the full rank-recovery statement; the headline theorem only needs its
degree-one positivity consequence. -/
theorem h_classInDegree_transport_of_lFunction_eq
    (G : LooplessMultigraph V) (G' : LooplessMultigraph V')
    [Fintype G.Jacobian] [Fintype G'.Jacobian]
    (D₁ : G.PicardDegree 1) (D₁' : G'.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian)
    (hL : ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁' (chi.compAddMonoidHom φ.toAddMonoidHom)) :
    ∀ (d : ℕ) (a' : G'.Jacobian),
      G.h (G.classInDegree D₁ (d : ℤ) (φ a')) =
        G'.h (G'.classInDegree D₁' (d : ℤ) a') := by
  intro d
  let f : G.Jacobian → ℂ := fun a ↦
    (G.h (G.classInDegree D₁ (d : ℤ) a) : ℂ)
  let g : G'.Jacobian → ℂ := fun a' ↦
    (G'.h (G'.classInDegree D₁' (d : ℤ) a') : ℂ)
  have hFourier : ∀ chi : AddChar G.Jacobian ℂ,
      (∑ a : G.Jacobian, f a * chi a) =
        ∑ a' : G'.Jacobian, g a' * chi (φ a') := by
    intro chi
    dsimp only [f, g]
    have heval :
        Polynomial.eval 1 (G.lCoefficient D₁ chi d) =
          Polynomial.eval 1
            (G'.lCoefficient D₁'
              (chi.compAddMonoidHom φ.toAddMonoidHom) d) := by
      have hcoeff := congrArg (PowerSeries.coeff d) (hL chi)
      exact congrArg (Polynomial.eval (1 : ℂ))
        (by simpa only [coeff_lFunction] using hcoeff)
    calc
      (∑ a : G.Jacobian,
          (G.h (G.classInDegree D₁ (d : ℤ) a) : ℂ) * chi a) =
          Polynomial.eval 1 (G.lCoefficient D₁ chi d) :=
        (G.eval_one_lCoefficient D₁ chi d).symm
      _ = Polynomial.eval 1
          (G'.lCoefficient D₁'
            (chi.compAddMonoidHom φ.toAddMonoidHom) d) := heval
      _ = ∑ a' : G'.Jacobian,
          (G'.h (G'.classInDegree D₁' (d : ℤ) a') : ℂ) *
            (chi.compAddMonoidHom φ.toAddMonoidHom) a' :=
        G'.eval_one_lCoefficient D₁'
          (chi.compAddMonoidHom φ.toAddMonoidHom) d
      _ = ∑ a' : G'.Jacobian,
          (G'.h (G'.classInDegree D₁' (d : ℤ) a') : ℂ) *
            chi (φ a') := by
        simp only [AddChar.compAddMonoidHom_apply,
          AddEquiv.coe_toAddMonoidHom]
  have hpoint :=
    eq_comp_addEquiv_of_forall_character_sum_eq φ f g hFourier
  intro a'
  have hcast := hpoint a'
  exact Nat.cast_injective hcast

/-- Conversely, preservation of the complete `h` function in split Picard
coordinates implies equality of all transported `L`-functions. -/
theorem lFunction_eq_of_h_classInDegree_transport
    (G : LooplessMultigraph V) (G' : LooplessMultigraph V')
    [Fintype G.Jacobian] [Fintype G'.Jacobian]
    (D₁ : G.PicardDegree 1) (D₁' : G'.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian)
    (hh : ∀ (d : ℕ) (a' : G'.Jacobian),
      G.h (G.classInDegree D₁ (d : ℤ) (φ a')) =
        G'.h (G'.classInDegree D₁' (d : ℤ) a')) :
    ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁' (chi.compAddMonoidHom φ.toAddMonoidHom) := by
  intro chi
  apply PowerSeries.ext
  intro d
  rw [G.coeff_lFunction D₁ chi d,
    G'.coeff_lFunction D₁'
      (chi.compAddMonoidHom φ.toAddMonoidHom) d]
  simp only [lCoefficient]
  symm
  exact Fintype.sum_equiv φ
    (fun a' : G'.Jacobian ↦
      Polynomial.C
          ((chi.compAddMonoidHom φ.toAddMonoidHom) a') *
        geometricPolynomial (R := ℂ)
          (G'.h (G'.classInDegree D₁' (d : ℤ) a')))
    (fun a : G.Jacobian ↦
      Polynomial.C (chi a) *
        geometricPolynomial (R := ℂ)
          (G.h (G.classInDegree D₁ (d : ℤ) a)))
    (fun a' ↦ by
      simp only [AddChar.compAddMonoidHom_apply,
        AddEquiv.coe_toAddMonoidHom]
      rw [← hh d a']
      rfl)

/-- Full cross-graph version of Proposition 3.7: transported `L`-functions
are equal exactly when the complete nonnegative-degree rank functions agree. -/
theorem lFunction_transport_iff_h_classInDegree_eq
    (G : LooplessMultigraph V) (G' : LooplessMultigraph V')
    [Fintype G.Jacobian] [Fintype G'.Jacobian]
    (D₁ : G.PicardDegree 1) (D₁' : G'.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) :
    (∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁' (chi.compAddMonoidHom φ.toAddMonoidHom)) ↔
      ∀ (d : ℕ) (a' : G'.Jacobian),
        G.h (G.classInDegree D₁ (d : ℤ) (φ a')) =
          G'.h (G'.classInDegree D₁' (d : ℤ) a') := by
  constructor
  · exact G.h_classInDegree_transport_of_lFunction_eq G' D₁ D₁' φ
  · exact G.lFunction_eq_of_h_classInDegree_transport G' D₁ D₁' φ

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
