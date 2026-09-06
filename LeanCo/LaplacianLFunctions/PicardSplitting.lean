import LeanCo.LaplacianLFunctions.Picard
import Mathlib.Tactic

/-!
# Splitting the Picard group by degree

Fixing a degree-one divisor class `D₁` identifies the Picard group with the
product of the Jacobian and `ℤ`.  This gives the degree-preserving extension of
a Jacobian isomorphism used in Lemma 4.1 of arXiv:2608.29981.
-/

namespace LeanCo.LaplacianLFunctions

namespace LooplessMultigraph

variable {V V' : Type*} [Fintype V] [Fintype V']

/-- The Jacobian coordinate of a Picard class relative to a degree-one base
class `D₁`: subtract `deg(C) D₁` from `C`. -/
def jacobianCoordinate (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (C : G.Picard) : G.Jacobian :=
  ⟨C - G.picardDegree C • (D₁ : G.Picard), by
    change G.picardDegree
      (C - G.picardDegree C • (D₁ : G.Picard)) = 0
    rw [LinearMap.map_sub, map_zsmul]
    rw [D₁.2]
    simp⟩

@[simp]
theorem jacobianCoordinate_coe (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (C : G.Picard) :
    (G.jacobianCoordinate D₁ C : G.Picard) =
      C - G.picardDegree C • (D₁ : G.Picard) :=
  rfl

/-- Recombining the Jacobian coordinate and degree recovers the original
Picard class. -/
@[simp]
theorem jacobianCoordinate_add_degree (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (C : G.Picard) :
    (G.jacobianCoordinate D₁ C : G.Picard) +
        G.picardDegree C • (D₁ : G.Picard) = C := by
  exact sub_add_cancel C _

@[simp]
theorem jacobianCoordinate_zero (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) :
    G.jacobianCoordinate D₁ 0 = 0 := by
  apply Subtype.ext
  simp

@[simp]
theorem jacobianCoordinate_add (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (C E : G.Picard) :
    G.jacobianCoordinate D₁ (C + E) =
      G.jacobianCoordinate D₁ C + G.jacobianCoordinate D₁ E := by
  apply Subtype.ext
  simp only [jacobianCoordinate_coe, Submodule.coe_add, LinearMap.map_add]
  module

/-- Coordinates `C ↦ (C - deg(C)D₁, deg(C))` split the Picard group as
`J_G × ℤ`. -/
def picardSplitting (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) : G.Picard ≃+ G.Jacobian × ℤ where
  toFun C := (G.jacobianCoordinate D₁ C, G.picardDegree C)
  invFun p := (p.1 : G.Picard) + p.2 • (D₁ : G.Picard)
  left_inv C := by
    simp only [jacobianCoordinate_coe]
    exact sub_add_cancel C _
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      have hp : G.picardDegree (p.1 : G.Picard) = 0 := p.1.2
      change ((p.1 : G.Picard) + p.2 • (D₁ : G.Picard)) -
          G.picardDegree ((p.1 : G.Picard) + p.2 • (D₁ : G.Picard)) •
            (D₁ : G.Picard) = (p.1 : G.Picard)
      rw [LinearMap.map_add, map_zsmul, D₁.2, hp]
      simp
    · change G.picardDegree
        ((p.1 : G.Picard) + p.2 • (D₁ : G.Picard)) = p.2
      have hp : G.picardDegree (p.1 : G.Picard) = 0 := p.1.2
      rw [LinearMap.map_add, map_zsmul, D₁.2]
      simp [hp]
  map_add' C E := by
    apply Prod.ext
    · exact G.jacobianCoordinate_add D₁ C E
    · exact LinearMap.map_add G.picardDegree C E

@[simp]
theorem picardSplitting_apply (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (C : G.Picard) :
    G.picardSplitting D₁ C =
      (G.jacobianCoordinate D₁ C, G.picardDegree C) :=
  rfl

@[simp]
theorem picardSplitting_symm_apply (G : LooplessMultigraph V)
    (D₁ : G.PicardDegree 1) (p : G.Jacobian × ℤ) :
    (G.picardSplitting D₁).symm p =
      (p.1 : G.Picard) + p.2 • (D₁ : G.Picard) :=
  rfl

/-- The Jacobian coordinate of `a + d D₁` is `a`. -/
@[simp]
theorem jacobianCoordinate_jacobian_add_zsmul
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (a : G.Jacobian) (d : ℤ) :
    G.jacobianCoordinate D₁
        ((a : G.Picard) + d • (D₁ : G.Picard)) = a := by
  have h := congrArg Prod.fst
    ((G.picardSplitting D₁).apply_symm_apply (a, d))
  exact h

/-- The degree of `a + d D₁` is `d`. -/
@[simp]
theorem picardDegree_jacobian_add_zsmul
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (a : G.Jacobian) (d : ℤ) :
    G.picardDegree ((a : G.Picard) + d • (D₁ : G.Picard)) = d := by
  have h := congrArg Prod.snd
    ((G.picardSplitting D₁).apply_symm_apply (a, d))
  exact h

/-- Lemma 4.1: an isomorphism of Jacobians extends, after choosing
degree-one base classes, to a degree-preserving isomorphism of Picard groups. -/
def picardTransport (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) :
    G'.Picard ≃+ G.Picard :=
  (G'.picardSplitting D₁').trans
    ((φ.prodCongr (AddEquiv.refl ℤ)).trans
      (G.picardSplitting D₁).symm)

@[simp]
theorem picardTransport_apply (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (C : G'.Picard) :
    picardTransport G' G D₁' D₁ φ C =
      (φ (G'.jacobianCoordinate D₁' C) : G.Picard) +
        G'.picardDegree C • (D₁ : G.Picard) :=
  rfl

/-- The extension from Lemma 4.1 preserves degree. -/
@[simp]
theorem picardDegree_picardTransport (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (C : G'.Picard) :
    G.picardDegree (picardTransport G' G D₁' D₁ φ C) =
      G'.picardDegree C := by
  rw [picardTransport_apply, LinearMap.map_add, map_zsmul, D₁.2]
  have hφ : G.picardDegree
      (φ (G'.jacobianCoordinate D₁' C) : G.Picard) = 0 :=
    (φ (G'.jacobianCoordinate D₁' C)).2
  simp [hφ]

/-- The transport intertwines the Jacobian-coordinate projections. -/
@[simp]
theorem jacobianCoordinate_picardTransport
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (C : G'.Picard) :
    G.jacobianCoordinate D₁ (picardTransport G' G D₁' D₁ φ C) =
      φ (G'.jacobianCoordinate D₁' C) := by
  apply Subtype.ext
  rw [jacobianCoordinate_coe, picardDegree_picardTransport,
    picardTransport_apply]
  exact add_sub_cancel_right _ _

/-- In split coordinates, Lemma 4.1 acts as `(a,d) ↦ (φ(a),d)`. -/
@[simp]
theorem picardTransport_jacobian_add_zsmul
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (a : G'.Jacobian) (d : ℤ) :
    picardTransport G' G D₁' D₁ φ
        ((a : G'.Picard) + d • (D₁' : G'.Picard)) =
      (φ a : G.Picard) + d • (D₁ : G.Picard) := by
  rw [picardTransport_apply,
    G'.jacobianCoordinate_jacobian_add_zsmul,
    G'.picardDegree_jacobian_add_zsmul]

/-- On the Jacobian, the Picard extension is the original isomorphism. -/
@[simp]
theorem picardTransport_jacobian (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (a : G'.Jacobian) :
    picardTransport G' G D₁' D₁ φ (a : G'.Picard) =
      (φ a : G.Picard) := by
  rw [picardTransport_apply]
  have hdeg : G'.picardDegree (a : G'.Picard) = 0 := a.2
  simp [hdeg, jacobianCoordinate]

/-- The chosen degree-one base class is sent to the chosen target base
class. -/
@[simp]
theorem picardTransport_baseClass (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) :
    picardTransport G' G D₁' D₁ φ (D₁' : G'.Picard) =
      (D₁ : G.Picard) := by
  rw [picardTransport_apply]
  simp [D₁'.2, jacobianCoordinate]

/-- Coordinate formula for the inverse extension. -/
@[simp]
theorem picardTransport_symm_apply (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (C : G.Picard) :
    (picardTransport G' G D₁' D₁ φ).symm C =
      (φ.symm (G.jacobianCoordinate D₁ C) : G'.Picard) +
        G.picardDegree C • (D₁' : G'.Picard) :=
  rfl

@[simp]
theorem picardTransport_symm_eq (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) :
    (picardTransport G' G D₁' D₁ φ).symm =
      picardTransport G G' D₁ D₁' φ.symm :=
  rfl

/-- The inverse extension also preserves degree. -/
@[simp]
theorem picardDegree_picardTransport_symm (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (C : G.Picard) :
    G'.picardDegree ((picardTransport G' G D₁' D₁ φ).symm C) =
      G.picardDegree C := by
  rw [picardTransport_symm_apply, LinearMap.map_add,
    map_zsmul, D₁'.2]
  have hφ : G'.picardDegree
      (φ.symm (G.jacobianCoordinate D₁ C) : G'.Picard) = 0 :=
    (φ.symm (G.jacobianCoordinate D₁ C)).2
  simp [hφ]

/-- The degree-preserving Picard equivalence restricts to every fixed-degree
slice. -/
def picardDegreeTransport (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (d : ℤ) :
    G'.PicardDegree d ≃ G.PicardDegree d where
  toFun C :=
    ⟨picardTransport G' G D₁' D₁ φ (C : G'.Picard), by
      rw [picardDegree_picardTransport]
      exact C.2⟩
  invFun C :=
    ⟨(picardTransport G' G D₁' D₁ φ).symm (C : G.Picard), by
      rw [picardDegree_picardTransport_symm]
      exact C.2⟩
  left_inv C := by
    apply Subtype.ext
    exact (picardTransport G' G D₁' D₁ φ).symm_apply_apply C.1
  right_inv C := by
    apply Subtype.ext
    exact (picardTransport G' G D₁' D₁ φ).apply_symm_apply C.1

@[simp]
theorem picardDegreeTransport_coe (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (d : ℤ)
    (C : G'.PicardDegree d) :
    (picardDegreeTransport G' G D₁' D₁ φ d C : G.Picard) =
      picardTransport G' G D₁' D₁ φ (C : G'.Picard) :=
  rfl

@[simp]
theorem picardDegreeTransport_symm_coe (G' : LooplessMultigraph V')
    (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (φ : G'.Jacobian ≃+ G.Jacobian) (d : ℤ)
    (C : G.PicardDegree d) :
    ((picardDegreeTransport G' G D₁' D₁ φ d).symm C : G'.Picard) =
      (picardTransport G' G D₁' D₁ φ).symm (C : G.Picard) :=
  rfl

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
