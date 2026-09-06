import LeanCo.PackingEdgeColoring.FaceDischarging
import LeanCo.PackingEdgeColoring.SectionFourWindows
import LeanCo.PackingEdgeColoring.Threads

/-!
# The structural interface for the six-window argument in Section 4

This file separates the finite cyclic combinatorics of Lemma 4.12 from the
reducibility arguments that rule out graph configurations.  Boundary
positions are darts, rather than vertices, so repeated occurrences on a
facial walk are counted correctly.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

/-! ## Honest graph-theoretic forbidden configurations -/

/-- Two threads of prescribed lengths leave the same vertex through distinct
first neighbours.  The distinctness clause records that these are genuinely
two different incident arms, rather than merely two existential witnesses. -/
def HasDistinctThreadsAt [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (u : V) (k l : ℕ) : Prop :=
  ∃ (v w : V) (p : G.Walk u v) (q : G.Walk u w),
    IsKThread G p k ∧ IsKThread G q l ∧
      p.getVert 1 ≠ q.getVert 1

/-- The configuration used in the prose summary of Lemmas 4.4--4.11: a
degree-three vertex is incident with a 3-thread and, through another edge,
a 2-thread. -/
def HasThreeAndTwoThreadsAt [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (u : V) : Prop :=
  HasDistinctThreadsAt (G := G) u 3 2

/-- The slightly stronger family actually needed when a six-window is read
literally: the other arm can extend one position outside the window and be a
3-thread as well. -/
def HasThreeAndLongThreadAt [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (u : V) : Prop :=
  HasDistinctThreadsAt (G := G) u 3 2 ∨
    HasDistinctThreadsAt (G := G) u 3 3

namespace RotationSystem

variable (R : RotationSystem G)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The vertex occurrence at offset `i` from a chosen dart occurrence of a
face. -/
def faceVertexAt (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) : V :=
  (((R.faceBoundaryPerm f) ^ i) a).1.fst

/-- The first `n` facial steps from `a` are realised by a simple graph walk,
with every indexed walk vertex equal to the corresponding boundary
occurrence.  Keeping the occurrence matching in the definition prevents an
unrelated path with the same endpoints from serving as a witness. -/
def FaceBoundaryPathAt (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (n : ℕ) : Prop :=
  ∃ (v : V) (p : G.Walk (R.faceVertexAt f a 0) v),
    p.IsPath ∧ p.length = n ∧
      ∀ i, i ≤ n → p.getVert i = R.faceVertexAt f a i

/-- All facial segments of at most four edges are simple paths.  This is the
precise embedding/girth-side input required to turn the local boundary words
below into `IsKChain` and `IsKThread` witnesses. -/
def FaceShortBoundaryPaths (f : R.Face) : Prop :=
  ∀ (a : {a : G.Dart // a ∈ f.1.support}) (n : ℕ),
    n ≤ 4 → R.FaceBoundaryPathAt f a n

/-- `faceThreeMarked` is the marking predicate used throughout the section. -/
def faceThreeMarked (f : R.Face) :
    {a : G.Dart // a ∈ f.1.support} → Prop :=
  fun a ↦ G.degree a.1.fst = 3

/-- No four consecutive boundary occurrences are all non-degree-three. -/
def FaceFourWindowHasThree (f : R.Face) : Prop :=
  FourWindowMarked (R.faceBoundaryPerm f) (R.faceThreeMarked f)

/-- The `2+3` exceptional six-window, expressed directly on facial boundary
occurrences. -/
def FaceTwoThreePatternAt (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) : Prop :=
  TwoThreePatternAt (R.faceBoundaryPerm f) (R.faceThreeMarked f) a

/-- The reverse `3+2` exceptional six-window. -/
def FaceThreeTwoPatternAt (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) : Prop :=
  ThreeTwoPatternAt (R.faceBoundaryPerm f) (R.faceThreeMarked f) a

/-- A structural bridge expected from the local graph lemmas: either
exceptional facial pattern supplies a genuine forbidden pair of thread arms
at its unique degree-three occurrence. -/
def FaceExceptionalPatternsFormLongThreads (f : R.Face) : Prop :=
  (∀ a, R.FaceTwoThreePatternAt f a →
      HasThreeAndLongThreadAt (G := G) (R.faceVertexAt f a 2)) ∧
    (∀ a, R.FaceThreeTwoPatternAt f a →
      HasThreeAndLongThreadAt (G := G) (R.faceVertexAt f a 3))

/-! ## Boundary paths really produce chains and threads -/

/-- Four degree-two occurrences on a simple three-edge facial segment give
an actual 4-chain in the ambient graph. -/
theorem exists_four_chain_of_faceBoundaryPathAt
    (f : R.Face) (a : {a : G.Dart // a ∈ f.1.support})
    (hpath : R.FaceBoundaryPathAt f a 3)
    (hdeg : ∀ i, i ≤ 3 → G.degree (R.faceVertexAt f a i) = 2) :
    ∃ (v : V) (p : G.Walk (R.faceVertexAt f a 0) v),
      IsKChain G p 4 := by
  obtain ⟨v, p, hp, hlen, hverts⟩ := hpath
  refine ⟨v, p, hp, ?_, ?_⟩
  · rw [p.length_support, hlen]
  · intro x hx
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hx
    obtain ⟨i, rfl, hi⟩ := hx
    unfold IsTwoVertex
    rw [hverts i (by omega)]
    exact hdeg i (by omega)

/-- A simple facial segment with degree-three endpoints and degree-two
internal occurrences is an actual thread. -/
theorem exists_thread_of_faceBoundaryPathAt
    (f : R.Face) (a : {a : G.Dart // a ∈ f.1.support}) (k : ℕ)
    (hpath : R.FaceBoundaryPathAt f a (k + 1))
    (hstart : G.degree (R.faceVertexAt f a 0) = 3)
    (hend : G.degree (R.faceVertexAt f a (k + 1)) = 3)
    (hint : ∀ i, 0 < i → i < k + 1 →
      G.degree (R.faceVertexAt f a i) = 2) :
    ∃ (v : V) (p : G.Walk (R.faceVertexAt f a 0) v),
      IsKThread G p k ∧
        (∀ i, i ≤ k + 1 → p.getVert i = R.faceVertexAt f a i) := by
  obtain ⟨v, p, hp, hlen, hverts⟩ := hpath
  refine ⟨v, p, ⟨hp, hlen, hstart, ?_, ?_⟩, hverts⟩
  · unfold IsThreeVertex
    have hv : v = R.faceVertexAt f a (k + 1) := by
      calc
        v = p.getVert p.length := p.getVert_length.symm
        _ = p.getVert (k + 1) := by rw [hlen]
        _ = R.faceVertexAt f a (k + 1) := hverts _ le_rfl
    rw [hv]
    exact hend
  · intro i hi0 hil
    unfold IsTwoVertex
    rw [hverts i (by omega)]
    exact hint i hi0 (by simpa only [hlen] using hil)

/-- Excluding genuine 4-chains forces a degree-three occurrence in every
four-position facial window, once short boundary segments are known to be
simple paths and all boundary vertices have degree two or three. -/
theorem faceFourWindowHasThree_of_no_four_chain
    (f : R.Face) (hshort : R.FaceShortBoundaryPaths f)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hno4 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 4) :
    R.FaceFourWindowHasThree f := by
  unfold FaceFourWindowHasThree FourWindowMarked faceThreeMarked
  intro a
  by_cases h₀ : G.degree a.1.fst = 3
  · exact Or.inl h₀
  by_cases h₁ : G.degree ((R.faceBoundaryPerm f) a).1.fst = 3
  · exact Or.inr (Or.inl h₁)
  by_cases h₂ : G.degree (((R.faceBoundaryPerm f) ^ 2) a).1.fst = 3
  · exact Or.inr (Or.inr (Or.inl h₂))
  by_cases h₃ : G.degree (((R.faceBoundaryPerm f) ^ 3) a).1.fst = 3
  · exact Or.inr (Or.inr (Or.inr h₃))
  exfalso
  have htwo : ∀ i, i ≤ 3 → G.degree (R.faceVertexAt f a i) = 2 := by
    intro i hi
    interval_cases i
    · unfold faceVertexAt
      rw [show ((R.faceBoundaryPerm f) ^ (0 : ℕ)) a = a by simp]
      exact (hdeg a.1.fst).resolve_right h₀
    · unfold faceVertexAt
      rw [show ((R.faceBoundaryPerm f) ^ (1 : ℕ)) a =
          (R.faceBoundaryPerm f) a by simp]
      exact (hdeg ((R.faceBoundaryPerm f) a).1.fst).resolve_right h₁
    · exact (hdeg _).resolve_right h₂
    · exact (hdeg _).resolve_right h₃
  obtain ⟨v, p, hp⟩ := R.exists_four_chain_of_faceBoundaryPathAt
    f a (hshort a 3 (by omega)) htwo
  exact hno4 p hp

/-! ## The pure six-window bridge -/

/-- The exact local conclusion needed by the face-incidence double count. -/
theorem two_le_faceSixWindowThreeCount
    (f : R.Face) (hfour : R.FaceFourWindowHasThree f)
    (h₂₃ : ∀ a, ¬ R.FaceTwoThreePatternAt f a)
    (h₃₂ : ∀ a, ¬ R.FaceThreeTwoPatternAt f a)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    2 ≤ R.faceSixWindowThreeCount f a := by
  change 2 ≤ cyclicWindowCount (R.faceBoundaryPerm f)
    (fun b ↦ G.degree b.1.fst = 3) 6 a
  exact two_le_cyclicWindowCount_six
    (R.faceBoundaryPerm f) (fun b ↦ G.degree b.1.fst = 3)
    hfour h₂₃ h₃₂ a

/-- If the two exceptional patterns are known to produce forbidden thread
configurations, excluding those configurations gives the six-window bound. -/
theorem two_le_faceSixWindowThreeCount_of_no_long_thread_pair
    (f : R.Face) (hfour : R.FaceFourWindowHasThree f)
    (hclose : R.FaceExceptionalPatternsFormLongThreads f)
    (hforbid : ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    2 ≤ R.faceSixWindowThreeCount f a := by
  apply R.two_le_faceSixWindowThreeCount f hfour
  · intro x hx
    exact hforbid _ (hclose.1 x hx)
  · intro x hx
    exact hforbid _ (hclose.2 x hx)

/-- Section 4's structural hypotheses feed directly into the already proved
face double count. -/
theorem sixPathDensity_of_forbidden_face_patterns
    (f : R.Face) (hfour : R.FaceFourWindowHasThree f)
    (h₂₃ : ∀ a, ¬ R.FaceTwoThreePatternAt f a)
    (h₃₂ : ∀ a, ¬ R.FaceThreeTwoPatternAt f a) :
    2 * R.faceLength f ≤
      6 * (R.faceDegreeOccurrences f 3).card := by
  apply R.sixPathDensity_of_two_le_faceSixWindowThreeCount f
  exact R.two_le_faceSixWindowThreeCount f hfour h₂₃ h₃₂

/-- A graph-theoretic version of the preceding interface. -/
theorem sixPathDensity_of_no_long_thread_pair
    (f : R.Face) (hfour : R.FaceFourWindowHasThree f)
    (hclose : R.FaceExceptionalPatternsFormLongThreads f)
    (hforbid : ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u) :
    2 * R.faceLength f ≤
      6 * (R.faceDegreeOccurrences f 3).card := by
  apply R.sixPathDensity_of_two_le_faceSixWindowThreeCount f
  exact R.two_le_faceSixWindowThreeCount_of_no_long_thread_pair
    f hfour hclose hforbid

/-- The complete structural-to-numerical interface for one face.  The only
embedding-specific premise left explicit is that the two exceptional words
close up to the stated honest thread configurations. -/
theorem sixPathDensity_of_no_four_chain_and_no_long_thread_pair
    (f : R.Face) (hshort : R.FaceShortBoundaryPaths f)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hno4 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 4)
    (hclose : R.FaceExceptionalPatternsFormLongThreads f)
    (hforbid : ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u) :
    2 * R.faceLength f ≤
      6 * (R.faceDegreeOccurrences f 3).card := by
  apply R.sixPathDensity_of_no_long_thread_pair f
  · exact R.faceFourWindowHasThree_of_no_four_chain
      f hshort hdeg hno4
  · exact hclose
  · exact hforbid

end Finite

end RotationSystem

end

end LeanCo.PackingEdgeColoring
