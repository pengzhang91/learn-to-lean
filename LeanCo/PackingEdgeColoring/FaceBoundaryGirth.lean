import LeanCo.PackingEdgeColoring.SectionFourStructure

/-!
# Short facial boundary walks below the girth

This file isolates the embedding-side input behind
`RotationSystem.FaceShortBoundaryPaths`.  A facial boundary is always a walk,
but it need not be a path: bridges can make a face traverse the same edge in
both directions.  Accordingly, the general girth theorem below states the
extra hypothesis honestly, as `FaceEdgeSimple`.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable (R : RotationSystem G)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The dart occurrence at offset `i` from `a` on a facial boundary. -/
def faceDartAt (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) : G.Dart :=
  (((R.faceBoundaryPerm f) ^ i) a).1

@[simp]
theorem faceDartAt_zero (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    R.faceDartAt f a 0 = a.1 := by
  simp [faceDartAt]

/-- Restricting the face cycle to its support does not change its action. -/
theorem coe_faceBoundaryPerm_apply (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    ((R.faceBoundaryPerm f) a).1 = f.1 a.1 := by
  rfl

/-- The next restricted boundary occurrence is the ambient facial step. -/
theorem coe_faceBoundaryPerm_apply_eq_faceStep (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    ((R.faceBoundaryPerm f) a).1 = R.faceStep a.1 := by
  rw [R.coe_faceBoundaryPerm_apply f a]
  exact R.face_apply_eq_faceStep f a.2

/-- Consecutive facial darts join head-to-tail. -/
theorem faceBoundaryPerm_fst (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    ((R.faceBoundaryPerm f) a).1.fst = a.1.snd := by
  rw [R.coe_faceBoundaryPerm_apply_eq_faceStep f a]
  exact R.rotation_fst a.1.symm

theorem faceDartAt_succ_fst (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) :
    (R.faceDartAt f a (i + 1)).fst = (R.faceDartAt f a i).snd := by
  unfold faceDartAt
  rw [pow_succ']
  exact R.faceBoundaryPerm_fst f (((R.faceBoundaryPerm f) ^ i) a)

/-- The restricted and ambient powers of the facial cycle agree. -/
theorem faceDartAt_eq_face_pow (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) :
    R.faceDartAt f a i = (f.1 ^ i) a.1 := by
  exact Equiv.Perm.subtypePerm_apply_pow_of_mem
    (g := f.1) (s := f.1.support) (fun _ ↦ Equiv.Perm.apply_mem_support) a.2

/-- Before one complete turn around a face, its dart occurrences do not
repeat. -/
theorem faceDartAt_injective_before_length (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) {i j : ℕ}
    (hi : i < R.faceLength f) (hj : j < R.faceLength f)
    (hij : R.faceDartAt f a i = R.faceDartAt f a j) :
    i = j := by
  have hcycleOn : f.1.IsCycleOn (↑f.1.support : Set G.Dart) := by
    rw [show (↑f.1.support : Set G.Dart) = {d | f.1 d ≠ d} by
      ext d
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Equiv.Perm.mem_support]]
    exact (R.face_isCycle f).isCycleOn
  have hpows : (f.1 ^ i) a.1 = (f.1 ^ j) a.1 := by
    simpa only [R.faceDartAt_eq_face_pow f a] using hij
  have hmod : i ≡ j [MOD f.1.support.card] :=
    (hcycleOn.pow_apply_eq_pow_apply a.2).mp hpows
  exact hmod.eq_of_lt_of_lt hi hj

theorem faceDartAt_mem_support (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) :
    R.faceDartAt f a i ∈ f.1.support := by
  exact (((R.faceBoundaryPerm f) ^ i) a).2

/-- After `faceLength` steps, a facial dart occurrence returns to itself. -/
theorem faceDartAt_faceLength (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    R.faceDartAt f a (R.faceLength f) = a.1 := by
  have hcycleOn : f.1.IsCycleOn (↑f.1.support : Set G.Dart) := by
    rw [show (↑f.1.support : Set G.Dart) = {d | f.1 d ≠ d} by
      ext d
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Equiv.Perm.mem_support]]
    exact (R.face_isCycle f).isCycleOn
  rw [R.faceDartAt_eq_face_pow f a]
  exact hcycleOn.pow_card_apply a.2

@[simp]
theorem faceVertexAt_eq_faceDartAt_fst (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) :
    R.faceVertexAt f a i = (R.faceDartAt f a i).fst := rfl

/-- Successive boundary vertex occurrences are adjacent in the graph. -/
theorem faceVertexAt_adj_succ (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) :
    G.Adj (R.faceVertexAt f a i) (R.faceVertexAt f a (i + 1)) := by
  rw [R.faceVertexAt_eq_faceDartAt_fst f a i,
    R.faceVertexAt_eq_faceDartAt_fst f a (i + 1),
    R.faceDartAt_succ_fst f a i]
  exact (R.faceDartAt f a i).adj

/-- The actual graph walk traced by the first `n` facial darts. -/
def faceBoundaryWalk (R : RotationSystem G) (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    (n : ℕ) → G.Walk (R.faceVertexAt f a 0) (R.faceVertexAt f a n)
  | 0 => .nil
  | n + 1 =>
      (faceBoundaryWalk R f a n).concat (R.faceVertexAt_adj_succ f a n)

@[simp]
theorem faceBoundaryWalk_length (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (n : ℕ) :
    (R.faceBoundaryWalk f a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [faceBoundaryWalk, Walk.length_concat, ih]

/-- The darts of `faceBoundaryWalk` are precisely the successive facial
occurrences. -/
theorem faceBoundaryWalk_darts (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (n : ℕ) :
    (R.faceBoundaryWalk f a n).darts =
      List.ofFn (fun i : Fin n ↦ R.faceDartAt f a i) := by
  induction n with
  | zero => simp [faceBoundaryWalk]
  | succ n ih =>
      rw [faceBoundaryWalk, Walk.darts_concat, ih, List.ofFn_succ']
      congr 1
      apply Dart.ext
      apply Prod.ext
      · rfl
      · simp only [faceDartAt, Fin.last, Fin.val_mk]
        rw [R.faceVertexAt_eq_faceDartAt_fst f a (n + 1)]
        exact R.faceDartAt_succ_fst f a n

/-- Every indexed vertex of the constructed walk is the corresponding facial
boundary occurrence. -/
theorem faceBoundaryWalk_getVert (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (n i : ℕ) (hi : i ≤ n) :
    (R.faceBoundaryWalk f a n).getVert i = R.faceVertexAt f a i := by
  induction n generalizing i with
  | zero =>
      have : i = 0 := by omega
      subst i
      simp [faceBoundaryWalk]
  | succ n ih =>
      rw [faceBoundaryWalk, Walk.concat_eq_append, Walk.getVert_append]
      simp only [faceBoundaryWalk_length]
      split_ifs with hlt
      · exact ih i (by omega)
      · have hi' : i = n ∨ i = n + 1 := by omega
        rcases hi' with rfl | rfl
        · simp only [Nat.sub_self, Walk.getVert]
        · have hsub : n + 1 - n = 1 := by omega
          rw [hsub]
          rfl

/-- No unoriented edge occurs twice on the boundary of this face.  Since a
cycle support already contains each oriented dart at most once, it is enough
to exclude the reversed dart.  This is the precise local no-bridge/two-sided
condition needed below. -/
def FaceEdgeSimple (f : R.Face) : Prop :=
  ∀ d : G.Dart, d ∈ f.1.support → d.symm ∉ f.1.support

/-- A face all of whose darts are two-sided is edge-simple. -/
theorem faceEdgeSimple_of_isTwoSided (f : R.Face)
    (htwo : ∀ d : G.Dart, d ∈ f.1.support → R.IsTwoSidedDart d) :
    R.FaceEdgeSimple f := by
  intro d hd hds
  have hdface : R.faceOfDart d = f := by
    apply Subtype.ext
    exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
      R.faceStep f.1 f.2 d).mpr hd |>.symm
  have hdsface : R.faceOfDart d.symm = f := by
    apply Subtype.ext
    exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
      R.faceStep f.1 f.2 d.symm).mpr hds |>.symm
  exact htwo d hd (hdface.trans hdsface.symm)

/-- An initial facial segment shorter than one full turn is a trail whenever
the face does not use both orientations of an edge. -/
theorem faceBoundaryWalk_isTrail (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (n : ℕ)
    (hn : n ≤ R.faceLength f) (hsimple : R.FaceEdgeSimple f) :
    (R.faceBoundaryWalk f a n).IsTrail := by
  constructor
  rw [Walk.edges, R.faceBoundaryWalk_darts f a n, List.map_ofFn,
    List.nodup_ofFn]
  intro i j hedge
  rcases (dart_edge_eq_iff (R.faceDartAt f a i)
    (R.faceDartAt f a j)).mp hedge with hdart | hreverse
  · apply Fin.ext
    exact R.faceDartAt_injective_before_length f a
      (lt_of_lt_of_le i.isLt hn) (lt_of_lt_of_le j.isLt hn) hdart
  · exfalso
    have hnot := hsimple (R.faceDartAt f a i)
      (R.faceDartAt_mem_support f a i)
    apply hnot
    have : (R.faceDartAt f a i).symm = R.faceDartAt f a j := by
      rw [hreverse, Dart.symm_symm]
    rw [this]
    exact R.faceDartAt_mem_support f a j

/-- An edge-simple facial boundary has length at least the graph's girth.  We
prove this through the cycle obtained by bypassing repeated vertices of the
closed facial trail; no assumption that a face boundary is itself a simple
cycle is hidden here. -/
theorem sixteen_le_faceLength_of_faceEdgeSimple
    (f : R.Face) (hsimple : R.FaceEdgeSimple f)
    (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    16 ≤ R.faceLength f := by
  let a : {d : G.Dart // d ∈ f.1.support} :=
    ⟨Classical.choose (R.face_isCycle f).nonempty_support,
      Classical.choose_spec (R.face_isCycle f).nonempty_support⟩
  have hclose : R.faceVertexAt f a (R.faceLength f) =
      R.faceVertexAt f a 0 := by
    rw [R.faceVertexAt_eq_faceDartAt_fst f a (R.faceLength f),
      R.faceDartAt_faceLength f a, R.faceVertexAt_eq_faceDartAt_fst f a 0,
      R.faceDartAt_zero f a]
  let q : G.Walk (R.faceVertexAt f a 0) (R.faceVertexAt f a 0) :=
    (R.faceBoundaryWalk f a (R.faceLength f)).copy rfl hclose
  have htrail : q.IsTrail := by
    apply (Walk.isTrail_copy _ rfl hclose).mpr
    exact R.faceBoundaryWalk_isTrail f a (R.faceLength f) le_rfl hsimple
  have hqLen : q.length = R.faceLength f := by
    simp only [q, Walk.length_copy, R.faceBoundaryWalk_length f a]
  have hqne : q ≠ Walk.nil := by
    intro hnil
    have hzero : q.length = 0 := congrArg Walk.length hnil
    rw [hqLen] at hzero
    have := R.two_le_faceLength f
    omega
  have hcycle : q.cycleBypass.IsCycle := htrail.isCycle_cycleBypass hqne
  have hsixteenE : (16 : ℕ∞) ≤ (q.cycleBypass.length : ℕ∞) :=
    (le_egirth.mp hgirth) _ q.cycleBypass hcycle
  have hsixteen : 16 ≤ q.cycleBypass.length := by
    exact_mod_cast hsixteenE
  have hcycleLen := Walk.length_cycleBypass_le_length q
  omega

/-- A facial trail of at most four edges is a path when the graph has
extended girth at least five. -/
theorem faceBoundaryWalk_isPath_of_five_le_egirth (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (n : ℕ)
    (hnface : n ≤ R.faceLength f) (hnfour : n ≤ 4)
    (hsimple : R.FaceEdgeSimple f) (hgirth : (5 : ℕ∞) ≤ G.egirth) :
    (R.faceBoundaryWalk f a n).IsPath := by
  have htrail := R.faceBoundaryWalk_isTrail f a n hnface hsimple
  rw [htrail.isPath_iff_isSubwalk_imp_not_isCycle]
  intro v w hsub hcycle
  have hfiveE : (5 : ℕ∞) ≤ (w.length : ℕ∞) :=
    (le_egirth.mp hgirth) v w hcycle
  have hfive : 5 ≤ w.length := by
    exact_mod_cast hfiveE
  have hwle : w.length ≤ n := by
    simpa only [R.faceBoundaryWalk_length f a n] using
      Walk.length_le_of_isSubwalk hsub
  omega

/-- The precise short-boundary conclusion used by Section 4.  The numerical
premises are deliberately only the required ones: four available facial
edges and girth at least five. -/
theorem faceShortBoundaryPaths_of_faceEdgeSimple
    (f : R.Face) (hface : 4 ≤ R.faceLength f)
    (hsimple : R.FaceEdgeSimple f) (hgirth : (5 : ℕ∞) ≤ G.egirth) :
    R.FaceShortBoundaryPaths f := by
  intro a n hn
  refine ⟨R.faceVertexAt f a n, R.faceBoundaryWalk f a n, ?_,
    R.faceBoundaryWalk_length f a n, ?_⟩
  · exact R.faceBoundaryWalk_isPath_of_five_le_egirth f a n
      (hn.trans hface) hn hsimple hgirth
  · intro i hi
    exact R.faceBoundaryWalk_getVert f a n i hi

/-- Girth-16 specialization matching the hypotheses of the paper's planar
theorem.  Notice that the local two-sidedness premise remains explicit;
girth and minimum degree alone do not rule out bridges. -/
theorem faceShortBoundaryPaths_of_sixteen_le
    (f : R.Face) (hface : 16 ≤ R.faceLength f)
    (hsimple : R.FaceEdgeSimple f) (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    R.FaceShortBoundaryPaths f := by
  apply R.faceShortBoundaryPaths_of_faceEdgeSimple f (by omega) hsimple
  exact (by norm_num : (5 : ℕ∞) ≤ 16).trans hgirth

/-- The girth-16 theorem with no separate face-length premise: edge
simplicity first forces the face to have length at least sixteen. -/
theorem faceShortBoundaryPaths_of_girth_sixteen
    (f : R.Face) (hsimple : R.FaceEdgeSimple f)
    (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    R.FaceShortBoundaryPaths f := by
  exact R.faceShortBoundaryPaths_of_sixteen_le f
    (R.sixteen_le_faceLength_of_faceEdgeSimple f hsimple hgirth)
    hsimple hgirth

/-- Convenient form using the rotation system's existing two-sided-dart
predicate. -/
theorem faceShortBoundaryPaths_of_sixteen_le_of_twoSided
    (f : R.Face) (hface : 16 ≤ R.faceLength f)
    (htwo : ∀ d : G.Dart, d ∈ f.1.support → R.IsTwoSidedDart d)
    (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    R.FaceShortBoundaryPaths f := by
  exact R.faceShortBoundaryPaths_of_sixteen_le f hface
    (R.faceEdgeSimple_of_isTwoSided f htwo) hgirth

/-- The direct rotation-system formulation: girth sixteen plus two-sidedness
of the face's darts gives all short facial boundary paths. -/
theorem faceShortBoundaryPaths_of_girth_sixteen_of_twoSided
    (f : R.Face)
    (htwo : ∀ d : G.Dart, d ∈ f.1.support → R.IsTwoSidedDart d)
    (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    R.FaceShortBoundaryPaths f := by
  exact R.faceShortBoundaryPaths_of_girth_sixteen f
    (R.faceEdgeSimple_of_isTwoSided f htwo) hgirth

end Finite

end RotationSystem

end

end LeanCo.PackingEdgeColoring
