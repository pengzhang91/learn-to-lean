import LeanCo.QuantumLatin.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Unitary copies with pairwise disjoint projective entries

This file supplies the separated-copy step used in Zhang--Cao Lemmas 4.8 and
4.9.  A common diagonal unitary is applied to every entry of a maximal RQLS.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

universe u v

/-! ## Common coordinate isometries -/

/-- A complex-linear-on-rays isometry of the common coordinate space.  This
is the exact interface needed when the same transformation is applied to all
entries of a quantum Latin square. -/
structure CommonCoordinateIsometry (ι : Type u) [Fintype ι] where
  toFun : Ket ι → Ket ι
  map_smul : ∀ (z : ℂ) (x : Ket ι), toFun (z • x) = z • toFun x
  dot_map : ∀ x y, dot (toFun x) (toFun y) = dot x y
  injective : Function.Injective toFun

namespace CommonCoordinateIsometry

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

instance : CoeFun (CommonCoordinateIsometry ι) (fun _ ↦ Ket ι → Ket ι) :=
  ⟨CommonCoordinateIsometry.toFun⟩

/-- Apply the same coordinate isometry to every cell. -/
def mapSquare (U : CommonCoordinateIsometry ι) (L : QuantumLatinSquare ι) :
    QuantumLatinSquare ι where
  entry i j := U (L.entry i j)
  row_orthonormal i a b := by
    rw [U.dot_map]
    exact L.row_orthonormal i a b
  col_orthonormal j a b := by
    rw [U.dot_map]
    exact L.col_orthonormal j a b

@[simp] theorem mapSquare_entry (U : CommonCoordinateIsometry ι)
    (L : QuantumLatinSquare ι) (i j : ι) :
    (U.mapSquare L).entry i j = U (L.entry i j) := rfl

theorem phaseEquivalent_map_iff (U : CommonCoordinateIsometry ι)
    (x y : Ket ι) : PhaseEquivalent (U x) (U y) ↔ PhaseEquivalent x y := by
  constructor
  · rintro ⟨z, hz, hxy⟩
    refine ⟨z, hz, U.injective ?_⟩
    rw [U.map_smul]
    exact hxy
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, U.map_smul z y⟩

/-- A resolution transported by a common coordinate isometry.  Its cell
partition is unchanged. -/
def mapResolution (U : CommonCoordinateIsometry ι) (L : QuantumLatinSquare ι)
    (r : L.Resolution) : (U.mapSquare L).Resolution where
  column := r.column
  covers := r.covers
  orthonormal t a b := by
    change dot (U (L.entry a (r.column t a)))
      (U (L.entry b (r.column t b))) = _
    rw [U.dot_map]
    exact r.orthonormal t a b

/-- Common coordinate isometries preserve maximal projective cardinality. -/
theorem map_hasMaximalCardinality (U : CommonCoordinateIsometry ι)
    (L : QuantumLatinSquare ι) (hL : L.HasMaximalCardinality) :
    (U.mapSquare L).HasMaximalCardinality := by
  intro i j i' j' h
  exact hL ((U.phaseEquivalent_map_iff _ _).mp h)

/-- Common coordinate isometries preserve resolvability and maximal projective
cardinality, hence act on maximal RQLSs. -/
def mapMaximalRQLS (U : CommonCoordinateIsometry ι) (R : MaximalRQLS ι) :
    MaximalRQLS ι where
  square := U.mapSquare R.square
  resolution := U.mapResolution R.square R.resolution
  maximal := U.map_hasMaximalCardinality R.square R.maximal

@[simp] theorem mapMaximalRQLS_entry (U : CommonCoordinateIsometry ι)
    (R : MaximalRQLS ι) (i j : ι) :
    (U.mapMaximalRQLS R).square.entry i j = U (R.square.entry i j) := rfl

end CommonCoordinateIsometry

/-! ## A one-coordinate phase rotation -/

section Rotation

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Multiply coordinate `d` by a circle phase and leave every other
coordinate fixed. -/
def rotateCoordinate (d : ι) (u : Circle) (x : Ket ι) : Ket ι :=
  fun c ↦ if c = d then (u : ℂ) * x c else x c

@[simp] theorem rotateCoordinate_apply_same (d : ι) (u : Circle) (x : Ket ι) :
    rotateCoordinate d u x d = (u : ℂ) * x d := by
  simp [rotateCoordinate]

@[simp] theorem rotateCoordinate_apply_of_ne (d : ι) (u : Circle) (x : Ket ι)
    {c : ι} (hcd : c ≠ d) : rotateCoordinate d u x c = x c := by
  simp [rotateCoordinate, hcd]

theorem rotateCoordinate_smul (d : ι) (u : Circle) (z : ℂ) (x : Ket ι) :
    rotateCoordinate d u (z • x) = z • rotateCoordinate d u x := by
  funext c
  by_cases hcd : c = d
  · subst c
    simp [rotateCoordinate, mul_assoc, mul_left_comm]
  · simp [rotateCoordinate, hcd]

theorem dot_rotateCoordinate (d : ι) (u : Circle) (x y : Ket ι) :
    dot (rotateCoordinate d u x) (rotateCoordinate d u y) = dot x y := by
  classical
  simp only [dot]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hcd : c = d
  · subst c
    simp only [rotateCoordinate_apply_same, map_mul]
    have hu : conj (u : ℂ) * (u : ℂ) = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast Circle.normSq_coe u
    calc
      conj (u : ℂ) * conj (x d) * ((u : ℂ) * y d) =
          (conj (u : ℂ) * (u : ℂ)) * (conj (x d) * y d) := by ring
      _ = conj (x d) * y d := by rw [hu, one_mul]
  · simp [rotateCoordinate_apply_of_ne d u x hcd,
      rotateCoordinate_apply_of_ne d u y hcd]

theorem rotateCoordinate_injective (d : ι) (u : Circle) :
    Function.Injective (rotateCoordinate d u) := by
  intro x y hxy
  funext c
  by_cases hcd : c = d
  · subst c
    have h := congrFun hxy d
    apply mul_left_cancel₀ (Circle.coe_ne_zero u)
    simpa using h
  · have h := congrFun hxy c
    simpa [rotateCoordinate_apply_of_ne d u x hcd,
      rotateCoordinate_apply_of_ne d u y hcd] using h

/-- The diagonal unitary which rotates exactly coordinate `d`. -/
def coordinateRotation (d : ι) (u : Circle) : CommonCoordinateIsometry ι where
  toFun := rotateCoordinate d u
  map_smul := rotateCoordinate_smul d u
  dot_map := dot_rotateCoordinate d u
  injective := rotateCoordinate_injective d u

/-- The resulting maximal RQLS copy. -/
def MaximalRQLS.rotateCoordinate (R : MaximalRQLS ι) (d : ι) (u : Circle) :
    MaximalRQLS ι :=
  (coordinateRotation d u).mapMaximalRQLS R

@[simp] theorem MaximalRQLS.rotateCoordinate_entry (R : MaximalRQLS ι)
    (d : ι) (u : Circle) (i j c : ι) :
    (R.rotateCoordinate d u).square.entry i j c =
      LeanCo.QuantumLatin.rotateCoordinate d u (R.square.entry i j) c := rfl

end Rotation

noncomputable local instance : Infinite Circle :=
  Infinite.of_injective
    (fun x : ℝ ↦ Circle.exp (Real.arctan x)) (by
      intro x y hxy
      apply Real.arctan_injective
      exact Circle.exp_injOn_Icc (by nlinarith [Real.pi_pos])
        ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩
        ⟨(Real.neg_pi_div_two_lt_arctan y).le, (Real.arctan_lt_pi_div_two y).le⟩ hxy)

/-! ## Separating different rotated copies -/

section Separation

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Projective equivalence between two one-coordinate rotations forces this
cross-multiplication identity.  The second coordinate `e` is used to eliminate
the otherwise unknown global phase. -/
theorem cross_eq_of_phaseEquivalent_rotations {d e : ι} (hde : d ≠ e)
    {u v : Circle} {x y : Ket ι}
    (h : PhaseEquivalent
      (LeanCo.QuantumLatin.rotateCoordinate d u x)
      (LeanCo.QuantumLatin.rotateCoordinate d v y)) :
    (u : ℂ) * x d * y e = (v : ℂ) * y d * x e := by
  rcases h with ⟨z, -, hxy⟩
  have hd := congrFun hxy d
  have he := congrFun hxy e
  simp only [rotateCoordinate_apply_same, Pi.smul_apply, smul_eq_mul] at hd
  have hed : e ≠ d := Ne.symm hde
  simp only [rotateCoordinate_apply_of_ne d u x hed,
    rotateCoordinate_apply_of_ne d v y hed, Pi.smul_apply, smul_eq_mul] at he
  calc
    (u : ℂ) * x d * y e = (z * ((v : ℂ) * y d)) * y e := by rw [hd]
    _ = (v : ℂ) * y d * (z * y e) := by ring
    _ = (v : ℂ) * y d * x e := by rw [← he]

/-- For fixed target phase and fixed source/target vectors having the two
specified nonzero coordinates, at most one source phase can give projectively
equivalent rotations. -/
theorem unique_rotation_parameter {d e : ι} (hde : d ≠ e)
    {u u' v : Circle} {x y : Ket ι} (hxd : x d ≠ 0) (hye : y e ≠ 0)
    (hu : PhaseEquivalent
      (LeanCo.QuantumLatin.rotateCoordinate d u x)
      (LeanCo.QuantumLatin.rotateCoordinate d v y))
    (hu' : PhaseEquivalent
      (LeanCo.QuantumLatin.rotateCoordinate d u' x)
      (LeanCo.QuantumLatin.rotateCoordinate d v y)) : u = u' := by
  apply Circle.coe_injective
  apply mul_right_cancel₀ (mul_ne_zero hxd hye)
  have h₁ := cross_eq_of_phaseEquivalent_rotations hde hu
  have h₂ := cross_eq_of_phaseEquivalent_rotations hde hu'
  calc
    (u : ℂ) * (x d * y e) = (u : ℂ) * x d * y e := by ring
    _ = (v : ℂ) * y d * x e := h₁
    _ = (u' : ℂ) * x d * y e := h₂.symm
    _ = (u' : ℂ) * (x d * y e) := by ring

/-- A canonical representative of the (at most singleton) set of phases
which make the rotated `x` projectively equal to the `v`-rotation of `y`.
If that set is empty, the arbitrary value `1` is returned. -/
noncomputable def forbiddenPhase (d : ι) (v : Circle) (x y : Ket ι) : Circle :=
  by
    classical
    exact if h : ∃ u : Circle, PhaseEquivalent
        (LeanCo.QuantumLatin.rotateCoordinate d u x)
        (LeanCo.QuantumLatin.rotateCoordinate d v y)
      then Classical.choose h
      else 1

theorem eq_forbiddenPhase_of_phaseEquivalent {d e : ι} (hde : d ≠ e)
    {u v : Circle} {x y : Ket ι} (hxd : x d ≠ 0) (hye : y e ≠ 0)
    (h : PhaseEquivalent
      (LeanCo.QuantumLatin.rotateCoordinate d u x)
      (LeanCo.QuantumLatin.rotateCoordinate d v y)) :
    u = forbiddenPhase d v x y := by
  classical
  let hex : ∃ w : Circle, PhaseEquivalent
      (LeanCo.QuantumLatin.rotateCoordinate d w x)
      (LeanCo.QuantumLatin.rotateCoordinate d v y) := ⟨u, h⟩
  rw [forbiddenPhase, dif_pos hex]
  apply unique_rotation_parameter hde hxd hye h
  exact Classical.choose_spec hex

/-- Two phases are separated for `R` when no cell of the first rotated copy
is projectively equal to any cell of the second. -/
def RotatedCopiesDisjoint (R : MaximalRQLS ι) (d : ι) (u v : Circle) : Prop :=
  ∀ i j i' j' : ι, ¬ PhaseEquivalent
    (LeanCo.QuantumLatin.rotateCoordinate d u (R.square.entry i j))
    (LeanCo.QuantumLatin.rotateCoordinate d v (R.square.entry i' j'))

/-- Pairwise separation of all distinct phases in a finite set. -/
def PhaseSetSeparated (R : MaximalRQLS ι) (d : ι) (s : Finset Circle) : Prop :=
  ∀ ⦃u : Circle⦄, u ∈ s → ∀ ⦃v : Circle⦄, v ∈ s → u ≠ v →
    RotatedCopiesDisjoint R d u v

/-- The finite set containing the sole possible bad new phase for every old
phase and every ordered pair of cells. -/
noncomputable def forbiddenSet (R : MaximalRQLS ι) (d : ι)
    (s : Finset Circle) : Finset Circle :=
  by
    classical
    exact (((s ×ˢ (Finset.univ : Finset (ι × ι))) ×ˢ
        (Finset.univ : Finset (ι × ι))).image fun q ↦
      forbiddenPhase d q.1.1
        (R.square.entry q.1.2.1 q.1.2.2)
        (R.square.entry q.2.1 q.2.2))

theorem mem_forbiddenSet_of_phaseEquivalent (R : MaximalRQLS ι)
    {d e : ι} (hde : d ≠ e)
    (hnz : ∀ i j, R.square.entry i j d ≠ 0 ∧ R.square.entry i j e ≠ 0)
    {s : Finset Circle} {u v : Circle} (hv : v ∈ s)
    {i j i' j' : ι}
    (h : PhaseEquivalent
      (LeanCo.QuantumLatin.rotateCoordinate d u (R.square.entry i j))
      (LeanCo.QuantumLatin.rotateCoordinate d v (R.square.entry i' j'))) :
    u ∈ forbiddenSet R d s := by
  classical
  rw [forbiddenSet, Finset.mem_image]
  refine ⟨((v, (i, j)), (i', j')), ?_, ?_⟩
  · simp [hv]
  · exact (eq_forbiddenPhase_of_phaseEquivalent hde
      (hnz i j).1 (hnz i' j').2 h).symm

/-- Finite avoidance on the infinite circle produces a separated phase set
of every prescribed finite cardinality. -/
theorem exists_phaseSetSeparated_card (R : MaximalRQLS ι)
    {d e : ι} (hde : d ≠ e)
    (hnz : ∀ i j, R.square.entry i j d ≠ 0 ∧ R.square.entry i j e ≠ 0) :
    ∀ k : ℕ, ∃ s : Finset Circle, s.card = k ∧ PhaseSetSeparated R d s := by
  classical
  intro k
  induction k with
  | zero =>
      exact ⟨∅, by simp, by simp [PhaseSetSeparated]⟩
  | succ k ih =>
      obtain ⟨s, hcard, hsep⟩ := ih
      obtain ⟨u, hu⟩ := Infinite.exists_notMem_finset (forbiddenSet R d s ∪ s)
      have huBad : u ∉ forbiddenSet R d s := fun hmem ↦
        hu (Finset.mem_union_left s hmem)
      have huS : u ∉ s := fun hmem ↦
        hu (Finset.mem_union_right (forbiddenSet R d s) hmem)
      refine ⟨insert u s, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem huS, hcard]
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact (hab rfl).elim
          · intro i j i' j' hphase
            exact huBad (mem_forbiddenSet_of_phaseEquivalent R hde hnz hb hphase)
        · rcases hb with rfl | hb
          · intro i j i' j' hphase
            exact huBad (mem_forbiddenSet_of_phaseEquivalent R hde hnz ha
              hphase.symm)
          · exact hsep ha hb hab

/-! ## Family interface for product constructions -/

/-- A family of maximal RQLSs whose projective entry sets are pairwise
disjoint.  This is the interface needed by the singular direct-product
construction: no choice of cells from two different family members can
represent the same ray. -/
structure PhaseDisjointMaximalRQLSFamily (κ : Type v) (ι : Type u)
    [Fintype ι] [DecidableEq ι] where
  copy : κ → MaximalRQLS ι
  pairwise_disjoint : ∀ ⦃a b : κ⦄, a ≠ b → ∀ i j i' j' : ι,
    ¬ PhaseEquivalent
      ((copy a).square.entry i j)
      ((copy b).square.entry i' j')

/-- The explicit phase-parameter version of the separated-copy theorem. -/
theorem MaximalRQLS.exists_separated_rotation_parameters (R : MaximalRQLS ι)
    {d e : ι} (hde : d ≠ e)
    (hnz : ∀ i j, R.square.entry i j d ≠ 0 ∧ R.square.entry i j e ≠ 0)
    (k : ℕ) :
    ∃ phase : Fin k → Circle, Function.Injective phase ∧
      ∀ ⦃a b : Fin k⦄, a ≠ b → RotatedCopiesDisjoint R d (phase a) (phase b) := by
  classical
  obtain ⟨s, hcard, hsep⟩ := exists_phaseSetSeparated_card R hde hnz k
  let idx : {u // u ∈ s} ≃ Fin k :=
    Fintype.equivFinOfCardEq ((Fintype.card_coe s).trans hcard)
  let phase : Fin k → Circle := fun a ↦ (idx.symm a).1
  refine ⟨phase, ?_, ?_⟩
  · intro a b hab
    apply idx.symm.injective
    exact Subtype.ext hab
  · intro a b hab
    apply hsep (idx.symm a).2 (idx.symm b).2
    intro huv
    apply hab
    apply idx.symm.injective
    exact Subtype.ext huv

/-- For every `k`, a maximal RQLS whose entries have two common nonzero
coordinates admits `k` pairwise phase-disjoint maximal RQLS copies. -/
theorem MaximalRQLS.exists_phaseDisjoint_copies (R : MaximalRQLS ι)
    {d e : ι} (hde : d ≠ e)
    (hnz : ∀ i j, R.square.entry i j d ≠ 0 ∧ R.square.entry i j e ≠ 0)
    (k : ℕ) : Nonempty (PhaseDisjointMaximalRQLSFamily (Fin k) ι) := by
  classical
  obtain ⟨phase, -, hphase⟩ :=
    R.exists_separated_rotation_parameters hde hnz k
  refine ⟨{
    copy := fun a ↦ R.rotateCoordinate d (phase a)
    pairwise_disjoint := ?_ }⟩
  intro a b hab i j i' j'
  exact hphase hab i j i' j'

end Separation

end LeanCo.QuantumLatin
