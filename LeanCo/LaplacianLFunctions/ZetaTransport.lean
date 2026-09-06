import LeanCo.LaplacianLFunctions.Zeta

/-!
# Type-correct transport of graph zeta functions

The proof of Proposition 3.5 in arXiv:2608.29981 changes the summation index
from one Picard group to another and then applies a map in the wrong
direction.  This file isolates the corrected argument: a degree- and
`h`-preserving Picard equivalence induces equivalences of every fixed-degree
slice, along which the finite sums are reindexed.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V W : Type*}
  [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype W] [Nonempty W] [DecidableEq W]

/-- A degree-preserving Picard equivalence restricts to an equivalence of
fixed-degree slices. -/
def picardDegreeEquivOfDegreePreserving
    (G : LooplessMultigraph V) (H : LooplessMultigraph W)
    (F : G.Picard ≃+ H.Picard)
    (hdegree : ∀ C : G.Picard,
      H.picardDegree (F C) = G.picardDegree C)
    (d : ℤ) : G.PicardDegree d ≃ H.PicardDegree d where
  toFun C := ⟨F C.1, by rw [hdegree, C.2]⟩
  invFun C := ⟨F.symm C.1, by
    have h := hdegree (F.symm C.1)
    rw [F.apply_symm_apply] at h
    exact h.symm.trans C.2⟩
  left_inv C := by
    apply Subtype.ext
    exact F.symm_apply_apply C.1
  right_inv C := by
    apply Subtype.ext
    exact F.apply_symm_apply C.1

@[simp]
theorem picardDegreeEquivOfDegreePreserving_coe
    (G : LooplessMultigraph V) (H : LooplessMultigraph W)
    (F : G.Picard ≃+ H.Picard)
    (hdegree : ∀ C : G.Picard,
      H.picardDegree (F C) = G.picardDegree C)
    (d : ℤ) (C : G.PicardDegree d) :
    (picardDegreeEquivOfDegreePreserving G H F hdegree d C : H.Picard) =
      F (C : G.Picard) :=
  rfl

/-- Corrected reindexing argument for Proposition 3.5: any degree- and
`h`-preserving Picard equivalence preserves the intrinsic two-variable zeta
function. -/
theorem zeta_eq_of_picardEquiv
    (G : LooplessMultigraph V) (H : LooplessMultigraph W)
    [Fintype G.Jacobian] [Fintype H.Jacobian]
    (F : G.Picard ≃+ H.Picard)
    (hdegree : ∀ C : G.Picard,
      H.picardDegree (F C) = G.picardDegree C)
    (hh : ∀ C : G.Picard, H.h (F C) = G.h C) :
    G.zeta = H.zeta := by
  apply PowerSeries.ext
  intro d
  rw [G.coeff_zeta d, H.coeff_zeta d]
  simp only [zetaCoefficient]
  exact Fintype.sum_equiv
    (picardDegreeEquivOfDegreePreserving G H F hdegree (d : ℤ))
    (fun C : G.PicardDegree (d : ℤ) ↦
      geometricPolynomial (R := ℂ) (G.h (C : G.Picard)))
    (fun C : H.PicardDegree (d : ℤ) ↦
      geometricPolynomial (R := ℂ) (H.h (C : H.Picard)))
    (fun C ↦ by rw [picardDegreeEquivOfDegreePreserving_coe, hh])

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
