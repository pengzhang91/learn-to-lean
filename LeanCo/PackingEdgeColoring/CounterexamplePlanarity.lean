import LeanCo.PackingEdgeColoring.Counterexamples
import LeanCo.PackingEdgeColoring.PlanarDeletion

/-!
# Planarity certificates for the two lower-bound graphs

The finite obstruction graphs in `Counterexamples` are supplied here with
explicit spherical rotation systems.  The rotation at each vertex is the
cyclic order of its neighbours in a fixed planar drawing.  Face labels are
then checked by finite computation, while the passage from those labels to
Euler's face count is proved abstractly.
-/

open scoped SimpleGraph
open SimpleGraph

namespace LeanCo.PackingEdgeColoring

namespace RotationSystem

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A label which is constant under one facial step is constant on a whole
facial orbit. -/
theorem label_eq_of_sameCycle (R : RotationSystem G) {L : Type*}
    (label : G.Dart → L)
    (hstep : ∀ d, label (R.faceStep d) = label d)
    {d e : G.Dart} (hde : R.faceStep.SameCycle d e) :
    label d = label e := by
  have hstepSymm : ∀ d, label (R.faceStep.symm d) = label d := by
    intro d
    have h := hstep (R.faceStep.symm d)
    exact (by simpa only [Equiv.apply_symm_apply] using h.symm)
  rcases hde with ⟨n, hn⟩
  have hpow : ∀ (m : ℤ) (a : G.Dart),
      label ((R.faceStep ^ m) a) = label a := by
    intro m
    induction m using Int.induction_on with
    | zero => intro a; rfl
    | succ m ih =>
        intro a
        rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hstep]
    | pred m ih =>
        intro a
        rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
        change label (R.faceStep.symm a) = label a
        exact hstepSymm a
  have h := hpow n d
  rw [hn] at h
  exact h.symm

/-- If finite labels classify the facial orbits exactly, their number is the
number of faces.  The difficult direction may be provided by a bounded-orbit
certificate, as done below for the two explicit graphs. -/
theorem faceCount_eq_of_labels (R : RotationSystem G) (n : ℕ)
    (label : G.Dart → Fin n)
    (hstep : ∀ d, label (R.faceStep d) = label d)
    (horbit : ∀ d e, label d = label e → R.faceStep.SameCycle d e)
    (hsurj : Function.Surjective label) :
    R.faceCount = n := by
  classical
  let representative : R.Face → G.Dart := fun f ↦
    Classical.choose (R.face_isCycle f).nonempty_support
  have representative_mem (f : R.Face) :
      representative f ∈ (f.1 : Equiv.Perm G.Dart).support :=
    Classical.choose_spec (R.face_isCycle f).nonempty_support
  have faceOf_representative (f : R.Face) :
      R.faceOfDart (representative f) = f := by
    apply Subtype.ext
    exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
      R.faceStep f.1 f.2 (representative f)).2 (representative_mem f) |>.symm
  let toLabel : R.Face → Fin n := fun f ↦ label (representative f)
  have hinj : Function.Injective toLabel := by
    intro f g hfg
    have hsame : R.faceStep.SameCycle (representative f) (representative g) :=
      horbit _ _ hfg
    calc
      f = R.faceOfDart (representative f) := (faceOf_representative f).symm
      _ = R.faceOfDart (representative g) :=
        (R.faceOfDart_eq_iff_sameCycle _ _).2 hsame
      _ = g := faceOf_representative g
  have hsurjective : Function.Surjective toLabel := by
    intro i
    obtain ⟨d, hd⟩ := hsurj i
    refine ⟨R.faceOfDart d, ?_⟩
    change label (representative (R.faceOfDart d)) = i
    rw [← hd]
    apply R.label_eq_of_sameCycle label hstep
    apply (R.faceOfDart_eq_iff_sameCycle _ _).mp
    exact (faceOf_representative (R.faceOfDart d))
  calc
    R.faceCount = Fintype.card R.Face := R.faceCount_eq_card_face
    _ = Fintype.card (Fin n) :=
      Fintype.card_congr (Equiv.ofBijective toLabel ⟨hinj, hsurjective⟩)
    _ = n := Fintype.card_fin n

/-- A transparent enumeration of the outgoing darts of a graph on `Fin n`.
Unlike `Finset.toList`, this list reduces in the kernel, which makes the
finite certificates below checkable by ordinary `decide`. -/
@[reducible] def finOutDarts {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) : List (OutDart G v) :=
  (List.finRange n).filterMap fun w ↦
    if h : G.Adj v w then some ⟨⟨(v, w), h⟩, rfl⟩ else none

theorem finOutDarts_nodup {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) : (finOutDarts G v).Nodup := by
  apply (List.nodup_finRange n).filterMap
  intro a b d ha hb
  split at ha
  · split at hb
    · rw [Option.mem_some_iff] at ha hb
      exact congrArg (fun q : OutDart G v ↦ q.1.snd) (ha.trans hb.symm)
    · simp at hb
  · simp at ha

theorem mem_finOutDarts {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) (d : OutDart G v) :
    d ∈ finOutDarts G v := by
  apply List.mem_filterMap.mpr
  refine ⟨d.1.snd, List.mem_finRange _, ?_⟩
  have hadj : G.Adj v d.1.snd := by
    convert d.1.adj using 1
    exact d.2.symm
  rw [dif_pos hadj]
  congr
  exact d.2.symm

/-- At vertices selected by `mask`, reverse the cyclic order induced by the
increasing enumeration `List.finRange`. -/
@[reducible] def finMaskedVertexPerm {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (mask : ℕ) (v : Fin n) : Equiv.Perm (OutDart G v) :=
  let p := (finOutDarts G v).formPerm
  if mask.testBit v.val then p.symm else p

theorem finMaskedVertexPerm_isCycleOn {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (mask : ℕ) (v : Fin n) :
    (finMaskedVertexPerm G mask v).IsCycleOn Set.univ := by
  let p : Equiv.Perm (OutDart G v) := (finOutDarts G v).formPerm
  have hp : p.IsCycleOn Set.univ := by
    have hcycle := (finOutDarts_nodup G v).isCycleOn_formPerm
    have hset : {d : OutDart G v | d ∈ finOutDarts G v} = Set.univ := by
      ext d
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact mem_finOutDarts G v d
    rw [hset] at hcycle
    simpa only [p] using hcycle
  simp only [finMaskedVertexPerm]
  split
  · exact hp.inv
  · exact hp

/-- Rotation system associated with `finMaskedVertexPerm`. -/
@[reducible] def finMaskedRotation {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (mask : ℕ) : RotationSystem G :=
  RotationSystem.ofVertexPermutations (finMaskedVertexPerm G mask)
    (finMaskedVertexPerm_isCycleOn G mask)

end RotationSystem

namespace Counterexamples

open RotationSystem

@[reducible] private def labelledDarts {V : Type*} {n : ℕ} (i : Fin n)
    (ds : List (V × V)) : List ((V × V) × Fin n) :=
  ds.map fun d ↦ (d, i)

@[reducible] private def lookupDartLabel {V : Type*} [DecidableEq V] {n : ℕ}
    (fallback : Fin n) (table : List ((V × V) × Fin n)) (d : V × V) : Fin n :=
  match table.find? (fun entry ↦ entry.1 = d) with
  | some entry => entry.2
  | none => fallback

@[reducible] private def G₁FaceTable : List ((G₁Vertex × G₁Vertex) × Fin 7) :=
  labelledDarts 0 [(0, 1), (1, 2), (2, 3), (3, 0)] ++
  labelledDarts 1 [(0, 3), (3, 9), (9, 10), (10, 4), (4, 0)] ++
  labelledDarts 2 [(0, 4), (4, 5), (5, 6), (6, 1), (1, 0)] ++
  labelledDarts 3 [(1, 6), (6, 7), (7, 2), (2, 1)] ++
  labelledDarts 4 [(2, 7), (7, 8), (8, 9), (9, 3), (3, 2)] ++
  labelledDarts 5 [(4, 10), (10, 9), (9, 8), (8, 5), (5, 4)] ++
  labelledDarts 6 [(5, 8), (8, 7), (7, 6), (6, 5)]

@[reducible] private def G₂FaceTable : List ((G₂Vertex × G₂Vertex) × Fin 8) :=
  labelledDarts 0 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] ++
  labelledDarts 1 [(0, 4), (4, 13), (13, 14), (14, 5), (5, 0)] ++
  labelledDarts 2 [(0, 5), (5, 6), (6, 7), (7, 1), (1, 0)] ++
  labelledDarts 3 [(1, 7), (7, 8), (8, 9), (9, 2), (2, 1)] ++
  labelledDarts 4 [(2, 9), (9, 10), (10, 11), (11, 3), (3, 2)] ++
  labelledDarts 5 [(3, 11), (11, 12), (12, 13), (13, 4), (4, 3)] ++
  labelledDarts 6
    [(5, 14), (14, 13), (13, 12), (12, 8), (8, 7), (7, 6), (6, 5)] ++
  labelledDarts 7 [(8, 12), (12, 11), (11, 10), (10, 9), (9, 8)]

/-- The seven explicit facial boundary labels for `G₁`. -/
@[reducible] def G₁FaceLabel (d : G₁.Dart) : Fin 7 :=
  lookupDartLabel 0 G₁FaceTable d.toProd

/-- The eight explicit facial boundary labels for `G₂`. -/
@[reducible] def G₂FaceLabel (d : G₂.Dart) : Fin 8 :=
  lookupDartLabel 0 G₂FaceTable d.toProd

/-- The rotation from the displayed planar drawing of `G₁`. -/
@[reducible] def G₁Rotation : RotationSystem G₁ :=
  finMaskedRotation G₁ 713

/-- The rotation from the displayed planar drawing of `G₂`. -/
@[reducible] def G₂Rotation : RotationSystem G₂ :=
  finMaskedRotation G₂ 10897

set_option maxHeartbeats 10000000 in
private theorem G₁FaceLabel_step :
    ∀ d, G₁FaceLabel (G₁Rotation.faceStep d) = G₁FaceLabel d := by
  decide

set_option maxHeartbeats 10000000 in
private theorem G₂FaceLabel_step :
    ∀ d, G₂FaceLabel (G₂Rotation.faceStep d) = G₂FaceLabel d := by
  decide

set_option maxHeartbeats 10000000 in
private theorem G₁FaceLabel_surjective : Function.Surjective G₁FaceLabel := by
  change ∀ i : Fin 7, ∃ d : G₁.Dart, G₁FaceLabel d = i
  decide

set_option maxHeartbeats 10000000 in
private theorem G₂FaceLabel_surjective : Function.Surjective G₂FaceLabel := by
  change ∀ i : Fin 8, ∃ d : G₂.Dart, G₂FaceLabel d = i
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem G₁FaceLabel_boundedOrbit :
    ∀ d e : G₁.Dart, G₁FaceLabel d = G₁FaceLabel e →
      ∃ k : Fin 32, (G₁Rotation.faceStep ^ k.val) d = e := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem G₂FaceLabel_boundedOrbit :
    ∀ d e : G₂.Dart, G₂FaceLabel d = G₂FaceLabel e →
      ∃ k : Fin 42, (G₂Rotation.faceStep ^ k.val) d = e := by
  decide

private theorem G₁FaceLabel_orbit (d e : G₁.Dart)
    (h : G₁FaceLabel d = G₁FaceLabel e) :
    G₁Rotation.faceStep.SameCycle d e := by
  obtain ⟨k, hk⟩ := G₁FaceLabel_boundedOrbit d e h
  refine ⟨Int.ofNat k.val, ?_⟩
  convert hk using 1 <;> simp

private theorem G₂FaceLabel_orbit (d e : G₂.Dart)
    (h : G₂FaceLabel d = G₂FaceLabel e) :
    G₂Rotation.faceStep.SameCycle d e := by
  obtain ⟨k, hk⟩ := G₂FaceLabel_boundedOrbit d e h
  refine ⟨Int.ofNat k.val, ?_⟩
  convert hk using 1 <;> simp

theorem G₁Rotation_faceCount : G₁Rotation.faceCount = 7 :=
  G₁Rotation.faceCount_eq_of_labels 7 G₁FaceLabel G₁FaceLabel_step
    G₁FaceLabel_orbit G₁FaceLabel_surjective

theorem G₂Rotation_faceCount : G₂Rotation.faceCount = 8 :=
  G₂Rotation.faceCount_eq_of_labels 8 G₂FaceLabel G₂FaceLabel_step
    G₂FaceLabel_orbit G₂FaceLabel_surjective

theorem G₁Rotation_isSpherical : G₁Rotation.IsSpherical := by
  unfold RotationSystem.IsSpherical
  rw [G₁Rotation_faceCount, G₁_edge_count]
  decide

theorem G₂Rotation_isSpherical : G₂Rotation.IsSpherical := by
  unfold RotationSystem.IsSpherical
  rw [G₂Rotation_faceCount, G₂_edge_count]
  decide

set_option maxHeartbeats 10000000 in
theorem G₁_preconnected : G₁.Preconnected := by
  decide

set_option maxHeartbeats 10000000 in
theorem G₂_preconnected : G₂.Preconnected := by
  decide

/-- The first lower-bound graph is planar. -/
theorem G₁_planar : IsCombinatoriallyPlanar G₁ := by
  intro C
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  intro _
  exact ⟨G₁Rotation.restrictComponent C,
    G₁Rotation.restrictComponent_isSpherical_of_preconnected
      G₁Rotation_isSpherical G₁_preconnected C⟩

/-- The second lower-bound graph is planar. -/
theorem G₂_planar : IsCombinatoriallyPlanar G₂ := by
  intro C
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  intro _
  exact ⟨G₂Rotation.restrictComponent C,
    G₂Rotation.restrictComponent_isSpherical_of_preconnected
      G₂Rotation_isSpherical G₂_preconnected C⟩

end Counterexamples

end LeanCo.PackingEdgeColoring
