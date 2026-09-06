import LeanCo.LaplacianLFunctions.RankRecovery
import LeanCo.LaplacianLFunctions.PicardSplitting

/-!
# Rank preservation by the Picard extension

The Fourier statement in `RankRecovery` is expressed in Jacobian coordinates.
This file packages it in the intrinsic Picard-group form used in the proof of
Theorem 4.3 of arXiv:2608.29981.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V V' : Type*}
  [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype V'] [Nonempty V'] [DecidableEq V']

/-- Under equality of all transported `L`-functions, the degree-preserving
Picard extension from Lemma 4.1 preserves `h` on every class of nonnegative
degree. -/
theorem h_picardTransport_of_degree_nonneg
    (G : LooplessMultigraph V) (G' : LooplessMultigraph V')
    [Fintype G.Jacobian] [Fintype G'.Jacobian]
    (D₁ : G.PicardDegree 1) (D₁' : G'.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian)
    (hL : ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁' (chi.compAddMonoidHom φ.toAddMonoidHom))
    (C' : G'.Picard) (hdeg : 0 ≤ G'.picardDegree C') :
    G.h (picardTransport G' G D₁' D₁ φ C') = G'.h C' := by
  let d : ℕ := (G'.picardDegree C').toNat
  let a' : G'.Jacobian := G'.jacobianCoordinate D₁' C'
  have hd : (d : ℤ) = G'.picardDegree C' := by
    exact Int.toNat_of_nonneg hdeg
  have hcoordinate : G'.classInDegree D₁' (d : ℤ) a' = C' := by
    change (a' : G'.Picard) + (d : ℤ) • (D₁' : G'.Picard) = C'
    rw [hd]
    exact G'.jacobianCoordinate_add_degree D₁' C'
  have hrank :=
    G.h_classInDegree_transport_of_lFunction_eq
      G' D₁ D₁' φ hL d a'
  rw [← hcoordinate]
  change G.h (picardTransport G' G D₁' D₁ φ
      ((a' : G'.Picard) + (d : ℤ) • (D₁' : G'.Picard))) =
    G'.h (G'.classInDegree D₁' (d : ℤ) a')
  rw [picardTransport_jacobian_add_zsmul]
  exact hrank

/-- Fixed-integer-degree subtype form of rank preservation. -/
theorem h_picardDegreeTransport_of_nonneg
    (G : LooplessMultigraph V) (G' : LooplessMultigraph V')
    [Fintype G.Jacobian] [Fintype G'.Jacobian]
    (D₁ : G.PicardDegree 1) (D₁' : G'.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian)
    (hL : ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁' (chi.compAddMonoidHom φ.toAddMonoidHom))
    (d : ℤ) (hd : 0 ≤ d) (C' : G'.PicardDegree d) :
    G.h ((picardDegreeTransport G' G D₁' D₁ φ d C' :
      G.PicardDegree d) : G.Picard) = G'.h (C' : G'.Picard) := by
  apply G.h_picardTransport_of_degree_nonneg G' D₁ D₁' φ hL
  rw [C'.2]
  exact hd

/-- Natural-degree form; nonnegativity is automatic. -/
theorem h_picardDegreeTransport_nat
    (G : LooplessMultigraph V) (G' : LooplessMultigraph V')
    [Fintype G.Jacobian] [Fintype G'.Jacobian]
    (D₁ : G.PicardDegree 1) (D₁' : G'.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian)
    (hL : ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁' (chi.compAddMonoidHom φ.toAddMonoidHom))
    (d : ℕ) (C' : G'.PicardDegree (d : ℤ)) :
    G.h ((picardDegreeTransport G' G D₁' D₁ φ (d : ℤ) C' :
      G.PicardDegree (d : ℤ)) : G.Picard) = G'.h (C' : G'.Picard) := by
  exact G.h_picardDegreeTransport_of_nonneg G' D₁ D₁' φ hL
    (d : ℤ) (by positivity) C'

/-- Degree-one specialization used to recover the embedded vertex classes. -/
theorem h_picardDegreeTransport_one
    (G : LooplessMultigraph V) (G' : LooplessMultigraph V')
    [Fintype G.Jacobian] [Fintype G'.Jacobian]
    (D₁ : G.PicardDegree 1) (D₁' : G'.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian)
    (hL : ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁' (chi.compAddMonoidHom φ.toAddMonoidHom))
    (C' : G'.PicardDegree 1) :
    G.h ((picardDegreeTransport G' G D₁' D₁ φ 1 C' :
      G.PicardDegree 1) : G.Picard) = G'.h (C' : G'.Picard) := by
  exact G.h_picardDegreeTransport_nat G' D₁ D₁' φ hL 1 C'

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
