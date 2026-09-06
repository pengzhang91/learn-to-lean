import LeanCo.QuantumLatin.Incomplete
import LeanCo.QuantumLatin.OrderEight
import LeanCo.QuantumLatin.SeparatedCopies
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-!
# A regular pointed order-eight square

We puncture the basis-zero cell of `maximalRQLSEight`.  Before puncturing we
apply a rational Householder reflection which fixes basis zero and acts only
on its seven-dimensional orthogonal complement.  Two rows of this exact
unitary avoid every one of the other sixty-three vectors; this supplies the
two fixed nonzero surviving coordinates required by `RegularAt`.
-/

open scoped BigOperators ComplexConjugate Matrix

namespace LeanCo.QuantumLatin

attribute [local instance] Fintype.decidableForallFintype

/-! ## An exact rational Householder reflection -/

/-- The vector `(3,1,3,3,1,1,2)` in the coordinates `1,...,7`, extended by
zero in coordinate zero.  Its squared length is `34`. -/
def pointedEightWeight (i : Fin 8) : ℚ :=
  match i.1 with
  | 1 => 3
  | 2 => 1
  | 3 => 3
  | 4 => 3
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | _ => 0

def exactRational (q : ℚ) : ExactComplex :=
  ExactComplex.mk4 q 0 0 0

/-- The exact matrix `I - wwᵀ/17`.  Since `wᵀw=34`, this is the
Householder reflection `I - 2wwᵀ/(wᵀw)`. -/
def pointedEightHouseholderExact (a b : Fin 8) : ExactComplex :=
  if a.1 = 0 then
    if b.1 = 0 then ExactComplex.one else ExactComplex.zero
  else if b.1 = 0 then
    ExactComplex.zero
  else
    exactRational
      ((if a = b then 1 else 0) -
        pointedEightWeight a * pointedEightWeight b / 17)

/-- The complex matrix obtained from the exact coefficient matrix. -/
noncomputable def pointedEightHouseholder : Matrix (Fin 8) (Fin 8) ℂ :=
  fun a b ↦ ExactComplex.embed (pointedEightHouseholderExact a b)

/-- Exact column orthonormality of the Householder matrix. -/
theorem pointedEightHouseholder_colGram :
    ∀ a b : Fin 8,
      exactDot8
          (fun k ↦ pointedEightHouseholderExact k a)
          (fun k ↦ pointedEightHouseholderExact k b) =
        if a = b then ExactComplex.one else ExactComplex.zero := by
  intro a
  fin_cases a <;> decide +kernel

/-- Exact row orthonormality, also serving as an independently checked
certificate of the symmetric Householder formula. -/
theorem pointedEightHouseholder_rowGram :
    ∀ a b : Fin 8,
      exactDot8
          (pointedEightHouseholderExact a)
          (pointedEightHouseholderExact b) =
        if a = b then ExactComplex.one else ExactComplex.zero := by
  intro a
  fin_cases a <;> decide +kernel

/-- Symbolic multiplication of the Householder matrix by an exact ket. -/
def pointedEightHouseholderExactApply
    (x : Fin 8 → ExactComplex) (a : Fin 8) : ExactComplex :=
  exactDot8
    (fun k ↦ ExactComplex.conjugate (pointedEightHouseholderExact a k)) x

theorem pointedEightHouseholder_apply_exact
    (x : Fin 8 → ExactComplex) (a : Fin 8) :
    (pointedEightHouseholder *ᵥ
      (fun k ↦ ExactComplex.embed (x k))) a =
      ExactComplex.embed (pointedEightHouseholderExactApply x a) := by
  unfold pointedEightHouseholderExactApply
  rw [← dot_embed_exact8]
  simp [pointedEightHouseholder, dot, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- The two selected output coordinates, `1` and `2`, are nonzero on every
entry except the basis-zero entry in cell `(0,0)`. -/
theorem pointedEightHouseholder_regular_exact :
    ∀ i j : Fin 8, (i, j) ≠ (0, 0) →
      pointedEightHouseholderExactApply (orderEightExactEntry i j) 1 ≠
          ExactComplex.zero ∧
        pointedEightHouseholderExactApply (orderEightExactEntry i j) 2 ≠
          ExactComplex.zero := by
  intro i
  fin_cases i <;> decide +kernel

/-! ## The corresponding common coordinate isometry -/

theorem pointedEightHouseholder_conjTranspose_mul :
    pointedEightHouseholderᴴ * pointedEightHouseholder = 1 := by
  ext a b
  change dot
      (fun k ↦ ExactComplex.embed (pointedEightHouseholderExact k a))
      (fun k ↦ ExactComplex.embed (pointedEightHouseholderExact k b)) =
    if a = b then 1 else 0
  rw [dot_embed_exact8, pointedEightHouseholder_colGram]
  by_cases h : a = b <;> simp [h]

/-- The rational Householder reflection as the common-coordinate isometry
interface used to transport QLSs, resolutions, and maximality. -/
noncomputable def pointedEightIsometry : CommonCoordinateIsometry (Fin 8) where
  toFun x := pointedEightHouseholder *ᵥ x
  map_smul := by
    intro z x
    funext a
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  dot_map := by
    intro x y
    change star (pointedEightHouseholder *ᵥ x) ⬝ᵥ
        (pointedEightHouseholder *ᵥ y) = star x ⬝ᵥ y
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, pointedEightHouseholder_conjTranspose_mul]
    simp
  injective := by
    intro x y hxy
    have h := congrArg
      (fun v ↦ pointedEightHouseholderᴴ *ᵥ v) hxy
    simpa [Matrix.mulVec_mulVec,
      pointedEightHouseholder_conjTranspose_mul] using h

theorem pointedEightIsometry_zero_coordinate (x : Ket (Fin 8)) :
    pointedEightIsometry x 0 = x 0 := by
  change (pointedEightHouseholder *ᵥ x) 0 = x 0
  simp [pointedEightHouseholder, pointedEightHouseholderExact,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem pointedEightIsometry_basis_zero :
    pointedEightIsometry (basis (0 : Fin 8)) = basis 0 := by
  funext a
  change (pointedEightHouseholder *ᵥ basis (0 : Fin 8)) a = basis 0 a
  by_cases ha : a = 0
  · subst a
    simp [pointedEightHouseholder, pointedEightHouseholderExact,
      Matrix.mulVec, dotProduct, basis_apply]
  · have hzeroa : (0 : Fin 8) ≠ a := Ne.symm ha
    simp [pointedEightHouseholder, pointedEightHouseholderExact,
      Matrix.mulVec, dotProduct, basis_apply, ha, hzeroa]

/-! ## Puncturing the fixed basis-zero cell -/

/-- The standard equivalence sends coordinate zero to the hole and coordinate
`k+1` to surviving coordinate `k`. -/
def finEightEquivOptionSeven : Fin 8 ≃ Option (Fin 7) :=
  finSuccEquiv 7

noncomputable def transformedMaximalRQLSEight : MaximalRQLS (Fin 8) :=
  pointedEightIsometry.mapMaximalRQLS maximalRQLSEight

noncomputable def pointedEightFull : MaximalRQLS (Option (Fin 7)) :=
  transformedMaximalRQLSEight.reindex finEightEquivOptionSeven

theorem orderEightExactEntry_zero_zero :
    ∀ k : Fin 8, orderEightExactEntry 0 0 k =
      if k = 0 then ExactComplex.one else ExactComplex.zero := by
  decide +kernel

theorem maximalRQLSEight_entry_zero_zero :
    maximalRQLSEight.square.entry 0 0 = basis (0 : Fin 8) := by
  funext k
  change ExactComplex.embed (orderEightExactEntry 0 0 k) = basis 0 k
  rw [orderEightExactEntry_zero_zero]
  by_cases hk : k = 0
  · subst k
    simp [basis_apply]
  · have hzero : (0 : Fin 8) ≠ k := Ne.symm hk
    simp [hk, hzero, basis_apply]

theorem transformedMaximalRQLSEight_entry_zero_zero :
    transformedMaximalRQLSEight.square.entry 0 0 = basis (0 : Fin 8) := by
  change pointedEightIsometry (maximalRQLSEight.square.entry 0 0) = basis 0
  rw [maximalRQLSEight_entry_zero_zero]
  exact pointedEightIsometry_basis_zero

theorem pointedEightFull_hole_entry :
    pointedEightFull.square.entry none none = basis none := by
  change reindexKet finEightEquivOptionSeven
      (transformedMaximalRQLSEight.square.entry
        (finEightEquivOptionSeven.symm none)
        (finEightEquivOptionSeven.symm none)) = basis none
  rw [show finEightEquivOptionSeven.symm none = (0 : Fin 8) by
    simp [finEightEquivOptionSeven]]
  rw [transformedMaximalRQLSEight_entry_zero_zero]
  funext k
  cases k with
  | none => simp [reindexKet, finEightEquivOptionSeven, basis_apply]
  | some k =>
      have hzero : (0 : Fin 8) ≠ k.succ := Ne.symm (Fin.succ_ne_zero k)
      simp [reindexKet, finEightEquivOptionSeven, basis_apply, hzero]

theorem transformedMaximalRQLSEight_column_zero :
    transformedMaximalRQLSEight.resolution.column 0 0 = 0 := by
  change maximalRQLSEight.resolution.column 0 0 = 0
  rfl

theorem pointedEightFull_hole_transversal :
    pointedEightFull.resolution.column none none = none := by
  change finEightEquivOptionSeven
      (transformedMaximalRQLSEight.resolution.column
        (finEightEquivOptionSeven.symm none)
        (finEightEquivOptionSeven.symm none)) = none
  rw [show finEightEquivOptionSeven.symm none = (0 : Fin 8) by
    simp [finEightEquivOptionSeven]]
  rw [transformedMaximalRQLSEight_column_zero]
  simp [finEightEquivOptionSeven]

/-- The transformed and reindexed example, pointed at its basis-zero cell. -/
noncomputable def pointedMaximalRQLSEight : PointedMaximalRQLS (Fin 7) where
  full := pointedEightFull
  hole_entry := pointedEightFull_hole_entry
  hole_transversal := pointedEightFull_hole_transversal

theorem pointedEightFull_entry_exact (r c k : Option (Fin 7)) :
    pointedEightFull.square.entry r c k =
      ExactComplex.embed
        (pointedEightHouseholderExactApply
          (orderEightExactEntry
            (finEightEquivOptionSeven.symm r)
            (finEightEquivOptionSeven.symm c))
          (finEightEquivOptionSeven.symm k)) := by
  change (pointedEightHouseholder *ᵥ
      (fun q ↦ ExactComplex.embed
        (orderEightExactEntry
          (finEightEquivOptionSeven.symm r)
          (finEightEquivOptionSeven.symm c) q)))
      (finEightEquivOptionSeven.symm k) = _
  exact pointedEightHouseholder_apply_exact _ _

theorem nonhole_preimages_ne_zero {r c : Option (Fin 7)}
    (h : PointedMaximalRQLS.IsNonholeCell r c) :
    (finEightEquivOptionSeven.symm r,
      finEightEquivOptionSeven.symm c) ≠ ((0 : Fin 8), 0) := by
  intro hpair
  have hr : finEightEquivOptionSeven.symm r = (0 : Fin 8) :=
    congrArg Prod.fst hpair
  have hc : finEightEquivOptionSeven.symm c = (0 : Fin 8) :=
    congrArg Prod.snd hpair
  have hrnone : r = none := by
    calc
      r = finEightEquivOptionSeven (finEightEquivOptionSeven.symm r) :=
        (finEightEquivOptionSeven.apply_symm_apply r).symm
      _ = finEightEquivOptionSeven 0 := congrArg finEightEquivOptionSeven hr
      _ = none := by simp [finEightEquivOptionSeven]
  have hcnone : c = none := by
    calc
      c = finEightEquivOptionSeven (finEightEquivOptionSeven.symm c) :=
        (finEightEquivOptionSeven.apply_symm_apply c).symm
      _ = finEightEquivOptionSeven 0 := congrArg finEightEquivOptionSeven hc
      _ = none := by simp [finEightEquivOptionSeven]
  subst r
  subst c
  simp [PointedMaximalRQLS.IsNonholeCell] at h

/-- Coordinates zero and one of the punctured seven-dimensional space are
nonzero in every surviving entry. -/
theorem pointedMaximalRQLSEight_regular :
    pointedMaximalRQLSEight.RegularAt (0 : Fin 7) (1 : Fin 7) := by
  constructor
  · decide
  · intro r c hnonhole
    have hcert := pointedEightHouseholder_regular_exact
      (finEightEquivOptionSeven.symm r)
      (finEightEquivOptionSeven.symm c)
      (nonhole_preimages_ne_zero hnonhole)
    constructor
    · change pointedEightFull.square.entry r c (some (0 : Fin 7)) ≠ 0
      rw [pointedEightFull_entry_exact]
      simpa [finEightEquivOptionSeven] using
        ExactComplex.embed_ne_zero hcert.1
    · change pointedEightFull.square.entry r c (some (1 : Fin 7)) ≠ 0
      rw [pointedEightFull_entry_exact]
      simpa [finEightEquivOptionSeven] using
        ExactComplex.embed_ne_zero hcert.2

/-- A regular pointed maximal RQLS obtained from the paper's order-eight
example by an exact rational unitary fixing the deleted basis state. -/
theorem regularPointedEight :
    ∃ (P : PointedMaximalRQLS (Fin 7)) (d e : Fin 7), P.RegularAt d e := by
  exact ⟨pointedMaximalRQLSEight, 0, 1,
    pointedMaximalRQLSEight_regular⟩

end LeanCo.QuantumLatin
