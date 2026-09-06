import LeanCo.PackingEdgeColoring.RotationSystem
import LeanCo.PackingEdgeColoring.MaximumAverageDegree
import LeanCo.PackingEdgeColoring.CyclicDensity

/-!
# Face-incidence counting and the numerical end of the girth-16 discharging

Faces are permutation cycles of darts.  Filtering a face support by the
degree of the dart's initial vertex counts boundary *occurrences*, so the
definitions remain correct when a facial walk revisits a cut vertex.
-/

open scoped BigOperators SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable (R : RotationSystem G)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Boundary occurrences of vertices of degree `d` on a face.  A repeated
vertex contributes once for each corresponding dart. -/
noncomputable def faceDegreeOccurrences (f : R.Face) (d : ℕ) :
    Finset G.Dart := by
  classical
  exact f.1.support.filter fun a ↦ G.degree a.fst = d

@[simp] theorem mem_faceDegreeOccurrences (f : R.Face) (d : ℕ)
    (a : G.Dart) :
    a ∈ R.faceDegreeOccurrences f d ↔
      a ∈ f.1.support ∧ G.degree a.fst = d := by
  classical
  simp [faceDegreeOccurrences]

/-- If all vertices have degree two or three, those two kinds of boundary
occurrence partition every face support. -/
theorem card_faceDegreeOccurrences_two_add_three
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (f : R.Face) :
    (R.faceDegreeOccurrences f 2).card +
        (R.faceDegreeOccurrences f 3).card = R.faceLength f := by
  classical
  have hdisj : Disjoint (R.faceDegreeOccurrences f 2)
      (R.faceDegreeOccurrences f 3) := by
    rw [Finset.disjoint_left]
    intro a ha₂ ha₃
    have h₂ := (R.mem_faceDegreeOccurrences f 2 a).mp ha₂ |>.2
    have h₃ := (R.mem_faceDegreeOccurrences f 3 a).mp ha₃ |>.2
    omega
  have hunion :
      R.faceDegreeOccurrences f 2 ∪ R.faceDegreeOccurrences f 3 =
        f.1.support := by
    ext a
    simp only [Finset.mem_union, R.mem_faceDegreeOccurrences]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩)
      · exact ha
      · exact ha
    · intro ha
      rcases hdeg a.fst with h₂ | h₃
      · exact Or.inl ⟨ha, h₂⟩
      · exact Or.inr ⟨ha, h₃⟩
  calc
    (R.faceDegreeOccurrences f 2).card +
        (R.faceDegreeOccurrences f 3).card =
        (R.faceDegreeOccurrences f 2 ∪
          R.faceDegreeOccurrences f 3).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = f.1.support.card := congrArg Finset.card hunion
    _ = R.faceLength f := rfl

/-- Filtering all face supports and summing still counts every dart exactly
once. -/
theorem sum_card_faceSupport_filter (P : G.Dart → Prop)
    [DecidablePred P] :
    (∑ f : R.Face, (f.1.support.filter P).card) =
      (Finset.univ.filter P).card := by
  have hdisj :
      (R.faceCycles : Set (Equiv.Perm G.Dart)).PairwiseDisjoint
        (fun c ↦ c.support.filter P) := by
    intro c hc d hd hcd
    exact (R.faceCycles_pairwiseDisjoint_support hc hd hcd).mono
      (Finset.filter_subset P c.support) (Finset.filter_subset P d.support)
  have hunion :
      R.faceCycles.biUnion (fun c ↦ c.support.filter P) =
        Finset.univ.filter P := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_biUnion] at ha
      obtain ⟨c, hc, hac⟩ := ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ a, (Finset.mem_filter.mp hac).2⟩
    · intro ha
      have hPa := (Finset.mem_filter.mp ha).2
      have hall : a ∈ R.faceCycles.biUnion (fun c ↦ c.support) := by
        rw [R.biUnion_faceCycles_support]
        exact Finset.mem_univ a
      rw [Finset.mem_biUnion] at hall
      obtain ⟨c, hc, hac⟩ := hall
      rw [Finset.mem_biUnion]
      exact ⟨c, hc, Finset.mem_filter.mpr ⟨hac, hPa⟩⟩
  calc
    (∑ f : R.Face, (f.1.support.filter P).card) =
        ∑ c ∈ R.faceCycles, (c.support.filter P).card := by
      simpa only using
        (Finset.sum_subtype R.faceCycles (fun _ ↦ Iff.rfl)
          (fun c ↦ (c.support.filter P).card)).symm
    _ = (R.faceCycles.biUnion (fun c ↦ c.support.filter P)).card :=
      (Finset.card_biUnion hdisj).symm
    _ = (Finset.univ.filter P).card := congrArg Finset.card hunion

/-- The number of darts whose initial vertex has degree `d`. -/
theorem card_darts_fst_degree (d : ℕ) :
    (Finset.univ.filter fun a : G.Dart ↦ G.degree a.fst = d).card =
      d * (degreeClass G d).card := by
  classical
  let S := Finset.univ.filter fun a : G.Dart ↦ G.degree a.fst = d
  have hmap : (S : Set G.Dart).MapsTo (fun a : G.Dart ↦ a.fst)
      (degreeClass G d) := by
    intro a ha
    have had : G.degree a.fst = d := by simpa [S] using ha
    exact (mem_degreeClass (G := G)).mpr had
  calc
    (Finset.univ.filter fun a : G.Dart ↦ G.degree a.fst = d).card = S.card := rfl
    _ = ∑ v ∈ degreeClass G d, (S.filter fun a ↦ a.fst = v).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ v ∈ degreeClass G d, G.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← G.dart_fst_fiber_card_eq_degree v]
      congr 1
      ext a
      have hvd : G.degree v = d := (mem_degreeClass (G := G)).mp hv
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h ↦ h.2
      · intro hav
        refine ⟨?_, hav⟩
        rw [hav]
        exact hvd
    _ = d * (degreeClass G d).card := sum_degree_degreeClass (G := G) d

/-- Globally, degree-`d` boundary occurrences are `d` times the number of
degree-`d` vertices. -/
theorem sum_card_faceDegreeOccurrences (d : ℕ) :
    (∑ f : R.Face, (R.faceDegreeOccurrences f d).card) =
      d * (degreeClass G d).card := by
  rw [← card_darts_fst_degree (G := G) d]
  exact R.sum_card_faceSupport_filter (fun a ↦ G.degree a.fst = d)

/-! ## Cyclic six-window counting -/

/-- The boundary successor permutation restricted to one face support. -/
def faceBoundaryPerm (f : R.Face) :
    Equiv.Perm {a : G.Dart // a ∈ f.1.support} :=
  f.1.subtypePermOfSupport

/-- Number of degree-three occurrences in the six positions beginning at a
chosen occurrence of a facial boundary. -/
noncomputable def faceSixWindowThreeCount (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) : ℕ := by
  classical
  exact cyclicWindowCount (R.faceBoundaryPerm f)
    (fun b ↦ G.degree b.1.fst = 3) 6 a

/-- Filtering the subtype of a finite set has the same cardinality as
filtering the original finite set. -/
private theorem card_filter_univ_subtype_finset {A : Type*} [DecidableEq A]
    (s : Finset A) (P : A → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x : s ↦ P x.1).card = (s.filter P).card := by
  classical
  rw [show (Finset.univ : Finset s) = s.attach by ext; simp]
  rw [Finset.filter_attach]
  simp

/-- Lemma 4.12's double count: if every cyclic six-window contains at
least two degree-three occurrences, then `2 length ≤ 6 n₃`. -/
theorem sixPathDensity_of_two_le_faceSixWindowThreeCount (f : R.Face)
    (hwindow : ∀ a : {a : G.Dart // a ∈ f.1.support},
      2 ≤ R.faceSixWindowThreeCount f a) :
    2 * R.faceLength f ≤
      6 * (R.faceDegreeOccurrences f 3).card := by
  classical
  have hcount :=
    mul_card_le_window_mul_marked_of_window_lower_bound
      (R.faceBoundaryPerm f)
      (fun b : {a : G.Dart // a ∈ f.1.support} ↦ G.degree b.1.fst = 3)
      6 2 hwindow
  have hsupport :
      Fintype.card {a : G.Dart // a ∈ f.1.support} = f.1.support.card := by
    exact Fintype.card_coe f.1.support
  have hmarked :
      (Finset.univ.filter fun b : {a : G.Dart // a ∈ f.1.support} ↦
        G.degree b.1.fst = 3).card =
        (R.faceDegreeOccurrences f 3).card := by
    simpa only [faceDegreeOccurrences] using
      card_filter_univ_subtype_finset f.1.support
        (fun a : G.Dart ↦ G.degree a.fst = 3)
  rw [hsupport, hmarked] at hcount
  exact hcount

/-- Six-path density as used in Lemma 4.12 implies at least six degree-three
occurrences on a face of length at least sixteen.  This integer form avoids
ceilings and division. -/
theorem six_le_threeOccurrences_of_sixPathDensity (f : R.Face)
    (hlen : 16 ≤ R.faceLength f)
    (hdensity : 2 * R.faceLength f ≤
      6 * (R.faceDegreeOccurrences f 3).card) :
    6 ≤ (R.faceDegreeOccurrences f 3).card := by
  omega

/-- All charges are multiplied by three.  A face starts with
`3(length-16)`, receives `5` per degree-three occurrence, and sends `3` per
degree-two occurrence. -/
def scaledFaceFinalCharge (f : R.Face) : ℤ :=
  3 * (R.faceLength f : ℤ) - 48 +
    5 * ((R.faceDegreeOccurrences f 3).card : ℤ) -
    3 * ((R.faceDegreeOccurrences f 2).card : ℤ)

/-- The numerical face check at the end of the paper's girth-16 proof. -/
theorem scaledFaceFinalCharge_nonneg
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (f : R.Face)
    (hsix : 6 ≤ (R.faceDegreeOccurrences f 3).card) :
    0 ≤ R.scaledFaceFinalCharge f := by
  have hpartition := R.card_faceDegreeOccurrences_two_add_three hdeg f
  unfold scaledFaceFinalCharge
  omega

/-- Lemma 4.12's six-path count plus girth sixteen gives the face
nonnegativity condition directly. -/
theorem scaledFaceFinalCharge_nonneg_of_sixPathDensity
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (f : R.Face)
    (hlen : 16 ≤ R.faceLength f)
    (hdensity : 2 * R.faceLength f ≤
      6 * (R.faceDegreeOccurrences f 3).card) :
    0 ≤ R.scaledFaceFinalCharge f :=
  R.scaledFaceFinalCharge_nonneg hdeg f
    (R.six_le_threeOccurrences_of_sixPathDensity f hlen hdensity)

/-! ## The global Euler charge -/

/-- Vertex initial charge, multiplied by three to make the transfer
`5/3` integral. -/
def scaledVertexInitialCharge (v : V) : ℤ :=
  21 * (G.degree v : ℤ) - 48

/-- Face initial charge under the same scaling. -/
def scaledFaceInitialCharge (f : R.Face) : ℤ :=
  3 * (R.faceLength f : ℤ) - 48

/-- The total scaled vertex charge in terms of vertices and edges. -/
theorem sum_scaledVertexInitialCharge :
    ∑ v : V, scaledVertexInitialCharge (G := G) v =
      21 * (2 * G.edgeFinset.card : ℤ) - 48 * (Fintype.card V : ℤ) := by
  simpa [scaledVertexInitialCharge] using
    (scaledDegreeCharge_sum (G := G) (p := 48) (q := 21))

/-- With degrees in `{2,3}`, the scaled vertex charge is `-6` per
degree-two vertex and `15` per degree-three vertex. -/
theorem sum_scaledVertexInitialCharge_eq_degreeClasses
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    ∑ v : V, scaledVertexInitialCharge (G := G) v =
      -6 * ((degreeClass G 2).card : ℤ) +
        15 * ((degreeClass G 3).card : ℤ) := by
  rw [sum_scaledVertexInitialCharge (G := G)]
  have hedge :
      (2 * (G.edgeFinset.card : ℤ)) =
        ∑ v : V, (G.degree v : ℤ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges.symm
  have hdegree :
      (∑ v : V, (G.degree v : ℤ)) =
        2 * ((degreeClass G 2).card : ℤ) +
          3 * ((degreeClass G 3).card : ℤ) := by
    exact_mod_cast
      sum_degrees_eq_two_mul_degreeTwo_add_three_mul_degreeThree
        (G := G) hdeg
  have hcard := card_degreeClass_two_add_three (G := G) hdeg
  have hcardZ :
      (Fintype.card V : ℤ) = ((degreeClass G 2).card : ℤ) +
        ((degreeClass G 3).card : ℤ) := by
    exact_mod_cast hcard.symm
  rw [hedge, hdegree, hcardZ]
  ring

/-- The total scaled face charge in terms of faces and edges. -/
theorem sum_scaledFaceInitialCharge :
    ∑ f : R.Face, R.scaledFaceInitialCharge f =
      3 * (2 * G.edgeFinset.card : ℤ) - 48 * (R.faceCount : ℤ) := by
  have hlength :
      (∑ f : R.Face, (R.faceLength f : ℤ)) =
        (2 * G.edgeFinset.card : ℕ) := by
    exact_mod_cast R.sum_faceLength_eq_two_mul_card_edges
  simp only [scaledFaceInitialCharge, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hlength]
  simp [faceCount, mul_comm]

/-- Euler's equality forces total scaled initial charge `-96`, i.e. the
paper's unscaled total `-32`. -/
theorem total_scaled_initialCharge_eq_neg_ninetySix
    (hspherical : R.IsSpherical) :
    (∑ v : V, scaledVertexInitialCharge (G := G) v) +
        ∑ f : R.Face, R.scaledFaceInitialCharge f = -96 := by
  rw [sum_scaledVertexInitialCharge (G := G),
    R.sum_scaledFaceInitialCharge]
  have heuler :
      (Fintype.card V : ℤ) + (R.faceCount : ℤ) =
        (G.edgeFinset.card : ℤ) + 2 := by
    exact_mod_cast hspherical
  omega

/-- Summed face-final charge equals the entire initial charge: the vertex
charges have all been transferred to their incident faces. -/
theorem sum_scaledFaceFinalCharge_eq_total_initialCharge
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    (∑ f : R.Face, R.scaledFaceFinalCharge f) =
      (∑ v : V, scaledVertexInitialCharge (G := G) v) +
        ∑ f : R.Face, R.scaledFaceInitialCharge f := by
  have htwo := R.sum_card_faceDegreeOccurrences 2
  have hthree := R.sum_card_faceDegreeOccurrences 3
  have hvertex := sum_scaledVertexInitialCharge_eq_degreeClasses (G := G) hdeg
  have htwoZ :
      (∑ f : R.Face, ((R.faceDegreeOccurrences f 2).card : ℤ)) =
        2 * ((degreeClass G 2).card : ℤ) := by
    exact_mod_cast htwo
  have hthreeZ :
      (∑ f : R.Face, ((R.faceDegreeOccurrences f 3).card : ℤ)) =
        3 * ((degreeClass G 3).card : ℤ) := by
    exact_mod_cast hthree
  simp only [scaledFaceFinalCharge, scaledFaceInitialCharge,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [htwoZ, hthreeZ, hvertex]
  ring

/-- The abstract closing contradiction for the girth-16 discharging. -/
theorem not_all_scaledFaceFinalCharge_nonnegative
    (hspherical : R.IsSpherical)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hnonneg : ∀ f : R.Face, 0 ≤ R.scaledFaceFinalCharge f) : False := by
  have hsum_nonneg : 0 ≤ ∑ f : R.Face, R.scaledFaceFinalCharge f :=
    Finset.sum_nonneg fun f _ ↦ hnonneg f
  have hsum_neg : (∑ f : R.Face, R.scaledFaceFinalCharge f) = -96 := by
    rw [R.sum_scaledFaceFinalCharge_eq_total_initialCharge hdeg,
      R.total_scaled_initialCharge_eq_neg_ninetySix hspherical]
  omega

/-- Direct endpoint: spherical Euler data, degree partition, face length at
least sixteen, and Lemma 4.12's six-path density are inconsistent. -/
theorem no_spherical_map_of_girth16_face_density
    (hspherical : R.IsSpherical)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlen : ∀ f : R.Face, 16 ≤ R.faceLength f)
    (hdensity : ∀ f : R.Face, 2 * R.faceLength f ≤
      6 * (R.faceDegreeOccurrences f 3).card) : False := by
  apply R.not_all_scaledFaceFinalCharge_nonnegative hspherical hdeg
  intro f
  exact R.scaledFaceFinalCharge_nonneg_of_sixPathDensity
    hdeg f (hlen f) (hdensity f)

/-- Same contradiction with the local six-window hypothesis that is proved
from the paper's reducible configurations. -/
theorem no_spherical_map_of_girth16_sixWindow
    (hspherical : R.IsSpherical)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlen : ∀ f : R.Face, 16 ≤ R.faceLength f)
    (hwindow : ∀ f : R.Face,
      ∀ a : {a : G.Dart // a ∈ f.1.support},
        2 ≤ R.faceSixWindowThreeCount f a) : False := by
  apply R.no_spherical_map_of_girth16_face_density hspherical hdeg hlen
  intro f
  exact R.sixPathDensity_of_two_le_faceSixWindowThreeCount f (hwindow f)

end Finite

end RotationSystem

end

end LeanCo.PackingEdgeColoring
