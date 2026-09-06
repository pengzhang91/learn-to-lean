import LeanCo.LaplacianLFunctions.LFunction

/-!
# Changing the degree-one base class of the graph L-function

This file proves Proposition 3.7 of arXiv:2608.29981.  For two choices
`D₁,D₁' ∈ Pic¹(G)`, all character-twisted `L`-functions agree exactly when
the Baker--Norine `h` invariant agrees in every Jacobian coordinate and every
nonnegative degree.

The forward implication evaluates each `u`-polynomial at `u = 1`, then uses
finite Fourier recovery.  The reverse implication is coefficientwise.
-/

open scoped BigOperators

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]

/-- Proposition 3.7: changing the degree-one base class leaves every
character `L`-function unchanged if and only if it leaves `h` unchanged in
every nonnegative-degree Jacobian coordinate. -/
theorem lFunction_baseChange_iff_h_eq
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ D₁' : G.PicardDegree 1) :
    (∀ chi : AddChar G.Jacobian ℂ,
        G.lFunction D₁ chi = G.lFunction D₁' chi) ↔
      ∀ (d : ℕ) (a : G.Jacobian),
        G.h (G.classInDegree D₁ (d : ℤ) a) =
          G.h (G.classInDegree D₁' (d : ℤ) a) := by
  constructor
  · intro hL d
    let f : G.Jacobian → ℕ :=
      fun a ↦ G.h (G.classInDegree D₁ (d : ℤ) a)
    let g : G.Jacobian → ℕ :=
      fun a ↦ G.h (G.classInDegree D₁' (d : ℤ) a)
    have hFourier : ∀ chi : AddChar G.Jacobian ℂ,
        (∑ a : G.Jacobian, (f a : ℂ) * chi a) =
          ∑ a : G.Jacobian, (g a : ℂ) * chi a := by
      intro chi
      rw [← G.eval_one_lCoefficient D₁ chi d,
        ← G.eval_one_lCoefficient D₁' chi d]
      have hcoeff := congrArg (PowerSeries.coeff d) (hL chi)
      have heval := congrArg (Polynomial.eval (1 : ℂ)) hcoeff
      simpa only [coeff_lFunction] using heval
    have hfg : f = g :=
      nat_eq_of_forall_sum_mul_addChar_eq f g hFourier
    intro a
    exact congrFun hfg a
  · intro hh chi
    apply PowerSeries.ext
    intro d
    rw [G.coeff_lFunction D₁ chi d,
      G.coeff_lFunction D₁' chi d]
    simp only [lCoefficient]
    apply Finset.sum_congr rfl
    intro a _
    rw [hh d a]

/-- Function-valued restatement of Proposition 3.7, convenient for Fourier
arguments that naturally produce an equality of rank functions. -/
theorem lFunction_baseChange_iff_h_function_eq
    (G : LooplessMultigraph V) [Fintype G.Jacobian]
    (D₁ D₁' : G.PicardDegree 1) :
    (∀ chi : AddChar G.Jacobian ℂ,
        G.lFunction D₁ chi = G.lFunction D₁' chi) ↔
      ∀ d : ℕ,
        (fun a : G.Jacobian ↦
          G.h (G.classInDegree D₁ (d : ℤ) a)) =
        (fun a : G.Jacobian ↦
          G.h (G.classInDegree D₁' (d : ℤ) a)) := by
  rw [G.lFunction_baseChange_iff_h_eq D₁ D₁']
  constructor
  · intro h d
    funext a
    exact h d a
  · intro h d a
    exact congrFun (h d) a

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
