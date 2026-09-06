import Mathlib

/-!
# Rotation systems for finite simple graphs

This file supplies the combinatorial-map foundation needed for planar
discharging arguments.  A rotation system is a permutation of the darts that
preserves the initial vertex and is transitive on the darts with any fixed
initial vertex.  Composing dart reversal with the rotation gives the facial
permutation.

The definitions here are purely combinatorial.  In particular, no topological
planarity library is assumed.
-/

open scoped BigOperators SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- Reversal of oriented edges, packaged as a permutation of the darts. -/
def dartFlip : Equiv.Perm G.Dart where
  toFun := Dart.symm
  invFun := Dart.symm
  left_inv := Dart.symm_symm
  right_inv := Dart.symm_symm

@[simp]
theorem dartFlip_apply (d : G.Dart) : dartFlip G d = d.symm := rfl

@[simp]
theorem dartFlip_symm (G : SimpleGraph V) : (dartFlip G).symm = dartFlip G := rfl

theorem dartFlip_ne_self (d : G.Dart) : dartFlip G d ≠ d := by
  simpa using d.symm_ne

/-- A rotation system gives a cyclic order of the outgoing darts at every
vertex.  `rotation_transitive` records cyclicity without choosing a numerical
degree or an enumeration of the neighbour set. -/
structure RotationSystem where
  rotation : Equiv.Perm G.Dart
  rotation_fst (d : G.Dart) : (rotation d).fst = d.fst
  rotation_transitive (d e : G.Dart) (h : d.fst = e.fst) :
    ∃ n : ℤ, (rotation ^ n) d = e

namespace RotationSystem

variable {G : SimpleGraph V} (R : RotationSystem G)

/-- The inverse rotation also preserves the initial vertex of every dart. -/
theorem rotation_symm_fst (d : G.Dart) : (R.rotation.symm d).fst = d.fst := by
  have h := R.rotation_fst (R.rotation.symm d)
  have h' : d.fst = (R.rotation.symm d).fst := by
    simpa only [Equiv.apply_symm_apply] using h
  exact h'.symm

/-- Every integral iterate of a vertex rotation stays at the same initial
vertex. -/
theorem rotation_zpow_fst (n : ℤ) (d : G.Dart) :
    ((R.rotation ^ n) d).fst = d.fst := by
  induction n using Int.induction_on generalizing d with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, ih, R.rotation_fst]
  | pred n ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      change (R.rotation.symm d).fst = d.fst
      exact R.rotation_symm_fst d

/-- The cycles of the rotation permutation are exactly the fibres of the
initial-vertex projection. -/
theorem rotation_sameCycle_iff_fst_eq (d e : G.Dart) :
    R.rotation.SameCycle d e ↔ d.fst = e.fst := by
  constructor
  · rintro ⟨n, hn⟩
    rw [← hn]
    exact (R.rotation_zpow_fst n d).symm
  · exact R.rotation_transitive d e

/-- First reverse a dart and then take the successor at its new initial
vertex.  The orbits of this permutation are the facial boundary walks. -/
def faceStep : Equiv.Perm G.Dart :=
  (dartFlip G).trans R.rotation

@[simp]
theorem faceStep_apply (d : G.Dart) : R.faceStep d = R.rotation d.symm := rfl

/-- A facial step never fixes a dart.  This only uses that rotation preserves
the initial vertex; cyclicity of each vertex rotation is not needed. -/
theorem faceStep_ne_self (d : G.Dart) : R.faceStep d ≠ d := by
  intro h
  have hs : R.rotation d.symm = d := by
    simpa only [faceStep_apply] using h
  have hfst : d.snd = d.fst := by
    calc
      d.snd = d.symm.fst := rfl
      _ = (R.rotation d.symm).fst := (R.rotation_fst d.symm).symm
      _ = d.fst := congrArg (fun x : G.Dart ↦ x.fst) hs
  exact d.snd_ne_fst hfst

/-- The handshaking identity for darts, exposed under the terminology used by
the rotation-system API. -/
theorem card_darts_eq_two_mul_card_edges [Fintype V] [DecidableRel G.Adj] :
    Fintype.card G.Dart = 2 * G.edgeFinset.card :=
  G.dart_card_eq_twice_card_edges

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The nontrivial cycles of the facial permutation.  Since `faceStep` has no
fixed points, these cycles partition all darts. -/
def faceCycles : Finset (Equiv.Perm G.Dart) :=
  R.faceStep.cycleFactorsFinset

/-- A face is a cycle factor of the facial permutation. -/
abbrev Face := {c : Equiv.Perm G.Dart // c ∈ R.faceCycles}

/-- Length of a face, counting dart occurrences in its boundary walk. -/
def faceLength (f : R.Face) : ℕ :=
  f.1.support.card

/-- Number of facial boundary cycles. -/
def faceCount : ℕ :=
  R.faceCycles.card

@[simp]
theorem mem_faceCycles_iff {c : Equiv.Perm G.Dart} :
    c ∈ R.faceCycles ↔ c ∈ R.faceStep.cycleFactorsFinset := Iff.rfl

theorem face_isCycle (f : R.Face) : (f.1 : Equiv.Perm G.Dart).IsCycle := by
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp f.2).1

/-- Every facial boundary cycle contains at least two darts.  Length two is
possible: a bridge is traversed in both directions by the same face. -/
theorem two_le_faceLength (f : R.Face) : 2 ≤ R.faceLength f := by
  simpa only [faceLength] using (R.face_isCycle f).two_le_card_support

/-- The face containing a dart, represented by the corresponding cycle factor
of the facial permutation. -/
def faceOfDart (d : G.Dart) : R.Face :=
  ⟨R.faceStep.cycleOf d, by
    apply Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
    exact Equiv.Perm.mem_support.mpr (R.faceStep_ne_self d)⟩

@[simp]
theorem coe_faceOfDart (d : G.Dart) :
    (R.faceOfDart d : Equiv.Perm G.Dart) = R.faceStep.cycleOf d := rfl

/-- A dart occurs on the boundary of its associated face. -/
theorem mem_support_faceOfDart (d : G.Dart) :
    d ∈ (R.faceOfDart d : Equiv.Perm G.Dart).support := by
  change d ∈ (R.faceStep.cycleOf d).support
  rw [Equiv.Perm.mem_support_cycleOf_iff' (R.faceStep_ne_self d)]

/-- Two darts determine the same face exactly when they are in the same orbit
of the facial permutation. -/
theorem faceOfDart_eq_iff_sameCycle (d e : G.Dart) :
    R.faceOfDart d = R.faceOfDart e ↔ R.faceStep.SameCycle d e := by
  have horbit := Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
    (Equiv.Perm.mem_support.mpr (R.faceStep_ne_self d))
    (Equiv.Perm.mem_support.mpr (R.faceStep_ne_self e))
  constructor
  · intro h
    apply horbit.mpr
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact horbit.mp h

/-- An edge is two-sided in the combinatorial embedding when its two
orientations lie on distinct facial boundary cycles. -/
def IsTwoSidedDart (d : G.Dart) : Prop :=
  R.faceOfDart d ≠ R.faceOfDart d.symm

theorem isTwoSidedDart_iff_not_sameCycle (d : G.Dart) :
    R.IsTwoSidedDart d ↔ ¬R.faceStep.SameCycle d d.symm := by
  rw [IsTwoSidedDart, Ne, R.faceOfDart_eq_iff_sameCycle]

/-- On the support of a face cycle, that cycle agrees with `faceStep`. -/
theorem face_apply_eq_faceStep (f : R.Face) {d : G.Dart}
    (hd : d ∈ (f.1 : Equiv.Perm G.Dart).support) :
    f.1 d = R.faceStep d := by
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp f.2).2 d hd

/-- A facial step stays on the same facial boundary cycle. -/
theorem faceStep_mem_support (f : R.Face) {d : G.Dart}
    (hd : d ∈ (f.1 : Equiv.Perm G.Dart).support) :
    R.faceStep d ∈ (f.1 : Equiv.Perm G.Dart).support := by
  rw [← R.face_apply_eq_faceStep f hd]
  exact Equiv.Perm.apply_mem_support.mpr hd

theorem faceCount_eq_card_face : R.faceCount = Fintype.card R.Face := by
  simpa only [faceCount] using (Fintype.card_coe R.faceCycles).symm

/-- Every dart lies in the support of the facial permutation. -/
theorem support_faceStep : R.faceStep.support = Finset.univ := by
  ext d
  simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
  exact R.faceStep_ne_self d

/-- Supports of distinct facial cycles are disjoint. -/
theorem faceCycles_pairwiseDisjoint_support :
    (R.faceCycles : Set (Equiv.Perm G.Dart)).PairwiseDisjoint
      (fun c ↦ c.support) := by
  intro c hc d hd hcd
  exact (R.faceStep.cycleFactorsFinset_pairwise_disjoint hc hd hcd).disjoint_support

/-- The union of the supports of the facial cycles is the full dart set. -/
theorem biUnion_faceCycles_support :
    R.faceCycles.biUnion (fun c ↦ c.support) = Finset.univ := by
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  have hd : d ∈ R.faceStep.support := by
    rw [R.support_faceStep]
    simp
  exact Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hd

/-- The sum of face lengths is the number of darts. -/
theorem sum_faceLength_eq_card_darts :
    ∑ f : R.Face, R.faceLength f = Fintype.card G.Dart := by
  calc
    ∑ f : R.Face, R.faceLength f =
        ∑ c ∈ R.faceCycles, c.support.card := by
      simpa only [faceLength] using
        (Finset.sum_subtype R.faceCycles (fun _ ↦ Iff.rfl)
          (fun c ↦ c.support.card)).symm
    _ = (R.faceCycles.biUnion (fun c ↦ c.support)).card :=
      (Finset.card_biUnion R.faceCycles_pairwiseDisjoint_support).symm
    _ = Finset.univ.card := congrArg Finset.card R.biUnion_faceCycles_support
    _ = Fintype.card G.Dart := Finset.card_univ

/-- Each edge occurs exactly twice among all facial boundary walks. -/
theorem sum_faceLength_eq_two_mul_card_edges :
    ∑ f : R.Face, R.faceLength f = 2 * G.edgeFinset.card := by
  rw [R.sum_faceLength_eq_card_darts, card_darts_eq_two_mul_card_edges]

/-- Euler's equality for a connected spherical combinatorial map.  Isolated
vertices are deliberately treated separately by downstream component-level
definitions, since they have no darts and hence no facial cycle. -/
def IsSpherical : Prop :=
  Fintype.card V + R.faceCount = G.edgeFinset.card + 2

end Finite

end RotationSystem

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A connected nontrivial graph has a spherical rotation certificate when it
admits a rotation system satisfying Euler's equality. -/
def HasSphericalRotation : Prop :=
  ∃ R : RotationSystem G, R.IsSpherical

/-- Graph-level combinatorial planarity, defined componentwise.  Every
component containing an edge must have a spherical rotation certificate;
isolated vertices are accepted directly because they have no darts from which
to form a facial cycle. -/
def IsCombinatoriallyPlanar : Prop :=
  ∀ C : G.ConnectedComponent,
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    C.toSimpleGraph.edgeSet.Nonempty → HasSphericalRotation C.toSimpleGraph

end Finite

end

end LeanCo.PackingEdgeColoring
