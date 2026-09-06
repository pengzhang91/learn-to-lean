import LeanCo.HypercubeTuran.Concentration
import LeanCo.HypercubeTuran.Hypercube
import LeanCo.HypercubeTuran.MaxDegreeTwo
import LeanCo.HypercubeTuran.QuarterSelection

/-!
# The local parity lemma

This file develops the local combinatorial argument behind Lemma 2.2 of
Axenovich--Pejic.  A monochromatic copy of the one-subdivision in the parity
colouring gives an injective placement of the original vertices (the poles)
in a cube.  The first results below record the pole and subdivision-vertex
images, their cube directions, and the resulting distance-two placement.
-/

open scoped SimpleGraph symmDiff

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u v

variable {V : Type u} {ι : Type v}
variable [DecidableEq ι] [LinearOrder ι]
variable {G : SimpleGraph V} {c : Fin 2}

/-- The image of an original vertex (a pole) under a subdivision copy. -/
noncomputable def poleImage
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (v : V) : Finset ι :=
  f (Sum.inl v)

/-- The image of the subdivision vertex belonging to an edge. -/
noncomputable def subdivisionImage
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (e : G.edgeSet) : Finset ι :=
  f (Sum.inr e)

/-- The edge of `G` regarded as a vertex of its one-subdivision. -/
def subdivisionEdgeVertex (v w : V) (h : G.Adj v w) : G.edgeSet :=
  ⟨s(v, w), h⟩

@[simp]
theorem left_mem_subdivisionEdgeVertex (v w : V) (h : G.Adj v w) :
    v ∈ (subdivisionEdgeVertex v w h).1 :=
  Sym2.mem_mk_left v w

@[simp]
theorem right_mem_subdivisionEdgeVertex (v w : V) (h : G.Adj v w) :
    w ∈ (subdivisionEdgeVertex v w h).1 :=
  Sym2.mem_mk_right v w

/-- Incidence in the source subdivision maps to adjacency in the selected
monochromatic graph. -/
theorem copy_adj_pole_subdivisionImage
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (v : V) (e : G.edgeSet) (hv : v ∈ e.1) :
    ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c).Adj
      (poleImage f v) (subdivisionImage f e) := by
  exact f.toHom.map_adj (oneSubdivision_adj_pole_edge v e |>.2 hv)

/-- Every mapped incidence edge is, in particular, an edge of the cube. -/
theorem cube_adj_pole_subdivisionImage
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (v : V) (e : G.edgeSet) (hv : v ∈ e.1) :
    (hypercubeGraph ι).Adj (poleImage f v) (subdivisionImage f e) := by
  exact EdgeLabeling.labelGraph_le parityColoring
    (copy_adj_pole_subdivisionImage f v e hv)

/-- Direction of the incidence edge from a pole to a subdivision vertex. -/
noncomputable def incidenceDirection
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (v : V) (e : G.edgeSet) (hv : v ∈ e.1) : ι :=
  cubeDirection (cube_adj_pole_subdivisionImage f v e hv)

theorem pole_symmDiff_subdivisionImage_eq_singleton
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (v : V) (e : G.edgeSet) (hv : v ∈ e.1) :
    poleImage f v ∆ subdivisionImage f e = {incidenceDirection f v e hv} :=
  symmDiff_eq_singleton_cubeDirection (cube_adj_pole_subdivisionImage f v e hv)

/-- The pole map is injective because the entire subdivision copy is
injective. -/
theorem poleImage_injective
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c)) :
    Function.Injective (poleImage f) := by
  intro v w h
  exact Sum.inl_injective (f.injective h)

/-- Two distinct cube vertices with a common cube neighbor are at Hamming
distance two. -/
theorem symmDiff_card_eq_two_of_common_cube_neighbor
    {A B M : Finset ι} (hAM : (hypercubeGraph ι).Adj A M)
    (hBM : (hypercubeGraph ι).Adj B M) (hAB : A ≠ B) :
    #(A ∆ B) = 2 := by
  let i := cubeDirection hAM
  let j := cubeDirection hBM
  have hi : A ∆ M = {i} := symmDiff_eq_singleton_cubeDirection hAM
  have hj : B ∆ M = {j} := symmDiff_eq_singleton_cubeDirection hBM
  have hij : i ≠ j := by
    intro hij
    apply hAB
    have hAM' : A = M ∆ {i} := by
      calc
        A = (A ∆ M) ∆ M := (symmDiff_symmDiff_cancel_right M A).symm
        _ = {i} ∆ M := by rw [hi]
        _ = M ∆ {i} := symmDiff_comm _ _
    have hBM' : B = M ∆ {j} := by
      calc
        B = (B ∆ M) ∆ M := (symmDiff_symmDiff_cancel_right M B).symm
        _ = {j} ∆ M := by rw [hj]
        _ = M ∆ {j} := symmDiff_comm _ _
    rw [hAM', hBM', hij]
  have hABset : A ∆ B = {i} ∆ {j} := by
    calc
      A ∆ B = (A ∆ M) ∆ (B ∆ M) := by
        simp only [symmDiff_assoc]
        rw [symmDiff_left_comm M B M, symmDiff_self, symmDiff_bot,
          symmDiff_comm A B]
      _ = {i} ∆ {j} := by rw [hi, hj]
  rw [hABset]
  rw [symmDiff_eq_union]
  · exact Finset.card_pair hij
  · exact Finset.disjoint_singleton.mpr hij

/-- Adjacent base-graph poles land at Hamming distance two. -/
theorem poleImage_edge_distance_two
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    {v w : V} (hvw : G.Adj v w) :
    #(poleImage f v ∆ poleImage f w) = 2 := by
  let e := subdivisionEdgeVertex v w hvw
  apply symmDiff_card_eq_two_of_common_cube_neighbor
      (M := subdivisionImage f e)
  · exact cube_adj_pole_subdivisionImage f v e (Sym2.mem_mk_left v w)
  · exact cube_adj_pole_subdivisionImage f w e (Sym2.mem_mk_right v w)
  · exact fun h => hvw.ne (poleImage_injective f h)

/-- A monochromatic subdivision copy supplies the pole placement used by the
global concentration argument. -/
theorem poleImage_isPolePlacement
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c)) :
    IsPolePlacement G (poleImage f) := by
  exact ⟨poleImage_injective f, fun _ _ h => poleImage_edge_distance_two f h⟩

/-! ## Shifting the copy to a chosen pole -/

/-- Translate a pole image by the image of a fixed centre pole. -/
noncomputable def shiftedPole
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w v : V) : Finset ι :=
  poleImage f v ∆ poleImage f w

/-- Translate a subdivision image by the image of a fixed centre pole. -/
noncomputable def shiftedSubdivision
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) (e : G.edgeSet) : Finset ι :=
  subdivisionImage f e ∆ poleImage f w

@[simp]
theorem shiftedPole_self
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) : shiftedPole f w w = ∅ := by
  simp [shiftedPole]

theorem shiftedPole_card_eq_two_iff
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w v : V) :
    #(shiftedPole f w v) = 2 ↔
      #(poleImage f v ∆ poleImage f w) = 2 :=
  Iff.rfl

@[simp]
theorem mem_secondPoleLayer_poleImage
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w v : V) :
    v ∈ secondPoleLayer (poleImage f) w ↔ #(shiftedPole f w v) = 2 := by
  simp [secondPoleLayer, shiftedPole]

/-- Symmetric-difference translation is an automorphism of every hypercube. -/
theorem symmDiff_translate_symmDiff (A B C : Finset ι) :
    (A ∆ C) ∆ (B ∆ C) = A ∆ B := by
  simp only [symmDiff_assoc]
  rw [symmDiff_left_comm C B C, symmDiff_self, symmDiff_bot]

theorem cube_adj_symmDiff_translate {A B : Finset ι}
    (h : (hypercubeGraph ι).Adj A B) (C : Finset ι) :
    (hypercubeGraph ι).Adj (A ∆ C) (B ∆ C) := by
  rw [hypercubeGraph_adj, symmDiff_translate_symmDiff]
  exact (hypercubeGraph_adj A B).mp h

/-- A shifted pole remains adjacent to the corresponding shifted subdivision
vertex. -/
theorem cube_adj_shiftedPole_shiftedSubdivision
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w v : V) (e : G.edgeSet) (hv : v ∈ e.1) :
    (hypercubeGraph ι).Adj (shiftedPole f w v) (shiftedSubdivision f w e) := by
  exact cube_adj_symmDiff_translate
    (cube_adj_pole_subdivisionImage f v e hv) (poleImage f w)

theorem shifted_pole_subdivision_symmDiff_eq_singleton
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w v : V) (e : G.edgeSet) (hv : v ∈ e.1) :
    shiftedPole f w v ∆ shiftedSubdivision f w e =
      {incidenceDirection f v e hv} := by
  rw [shiftedPole, shiftedSubdivision, symmDiff_translate_symmDiff]
  exact pole_symmDiff_subdivisionImage_eq_singleton f v e hv

/-- Each incidence edge of the copy has the selected monochromatic colour. -/
theorem pole_subdivision_color
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (v : V) (e : G.edgeSet) (hv : v ∈ e.1) :
    (parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).get
      (poleImage f v) (subdivisionImage f e)
      (cube_adj_pole_subdivisionImage f v e hv) = c := by
  obtain ⟨hcube, hcolour⟩ :=
    (EdgeLabeling.labelGraph_adj (C :=
      (parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)))
      (k := c) (poleImage f v) (subdivisionImage f e)).mp
      (copy_adj_pole_subdivisionImage f v e hv)
  simpa [EdgeLabeling.get_eq] using hcolour

/-- Prefix-parity form of monochromaticity for a mapped incidence. -/
theorem incidence_prefixParity_eq_color
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (v : V) (e : G.edgeSet) (hv : v ∈ e.1) :
    prefixParity (poleImage f v) (incidenceDirection f v e hv) = c := by
  exact pole_subdivision_color f v e hv

/-! ## Local edge geometry in the shifted second layer -/

/-- The shifted images of adjacent poles have the same Hamming distance as
the original images. -/
theorem shiftedPole_edge_distance_two
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) {u v : V} (huv : G.Adj u v) :
    #(shiftedPole f w u ∆ shiftedPole f w v) = 2 := by
  rw [shiftedPole, shiftedPole, symmDiff_translate_symmDiff]
  exact poleImage_edge_distance_two f huv

/-- Two two-element sets at Hamming distance two meet in one coordinate and
have a three-element union. -/
theorem card_inter_eq_one_and_card_union_eq_three
    {P Q : Finset ι} (hP : #P = 2) (hQ : #Q = 2)
    (hPQ : #(P ∆ Q) = 2) :
    #(P ∩ Q) = 1 ∧ #(P ∪ Q) = 3 := by
  have hdis : Disjoint (P \ Q) (Q \ P) := by
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    exact (Finset.mem_sdiff.mp hxP).2 (Finset.mem_sdiff.mp hxQ).1
  have hdiff : #(P \ Q) + #(Q \ P) = 2 := by
    simpa [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis] using hPQ
  have heq : #(P \ Q) = #(Q \ P) := by
    exact Finset.card_sdiff_comm (hP.trans hQ.symm)
  have hpart := Finset.card_sdiff_add_card_inter P Q
  have hunion := Finset.card_union_add_card_inter P Q
  omega

private theorem eq_singleton_of_card_eq_one_of_mem
    {S : Finset ι} {x : ι} (hcard : #S = 1) (hx : x ∈ S) : S = {x} := by
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hcard
  have hxy : x = y := by simpa using hx
  simp [hxy]

/-- A common neighbor contains every common coordinate of two distinct cube
vertices. -/
theorem inter_subset_common_cube_neighbor
    {P Q M : Finset ι} (hPM : (hypercubeGraph ι).Adj P M)
    (hQM : (hypercubeGraph ι).Adj Q M) (hPQ : P ≠ Q) :
    P ∩ Q ⊆ M := by
  intro x hx
  by_contra hxM
  have hxP : x ∈ P := (Finset.mem_inter.mp hx).1
  have hxQ : x ∈ Q := (Finset.mem_inter.mp hx).2
  have hxPM : x ∈ P ∆ M := Finset.mem_symmDiff.mpr (Or.inl ⟨hxP, hxM⟩)
  have hxQM : x ∈ Q ∆ M := Finset.mem_symmDiff.mpr (Or.inl ⟨hxQ, hxM⟩)
  have hPMset : P ∆ M = {x} :=
    eq_singleton_of_card_eq_one_of_mem ((hypercubeGraph_adj P M).mp hPM) hxPM
  have hQMset : Q ∆ M = {x} :=
    eq_singleton_of_card_eq_one_of_mem ((hypercubeGraph_adj Q M).mp hQM) hxQM
  apply hPQ
  calc
    P = (P ∆ M) ∆ M := (symmDiff_symmDiff_cancel_right M P).symm
    _ = (Q ∆ M) ∆ M := by rw [hPMset, hQMset]
    _ = Q := symmDiff_symmDiff_cancel_right M Q

/-- A common neighbor has no coordinate outside the union of two distinct
cube vertices. -/
theorem common_cube_neighbor_subset_union
    {P Q M : Finset ι} (hPM : (hypercubeGraph ι).Adj P M)
    (hQM : (hypercubeGraph ι).Adj Q M) (hPQ : P ≠ Q) :
    M ⊆ P ∪ Q := by
  intro x hxM
  by_contra hx
  have hxP : x ∉ P := fun hxP => hx (Finset.mem_union_left Q hxP)
  have hxQ : x ∉ Q := fun hxQ => hx (Finset.mem_union_right P hxQ)
  have hxPM : x ∈ P ∆ M := Finset.mem_symmDiff.mpr (Or.inr ⟨hxM, hxP⟩)
  have hxQM : x ∈ Q ∆ M := Finset.mem_symmDiff.mpr (Or.inr ⟨hxM, hxQ⟩)
  have hPMset : P ∆ M = {x} :=
    eq_singleton_of_card_eq_one_of_mem ((hypercubeGraph_adj P M).mp hPM) hxPM
  have hQMset : Q ∆ M = {x} :=
    eq_singleton_of_card_eq_one_of_mem ((hypercubeGraph_adj Q M).mp hQM) hxQM
  apply hPQ
  calc
    P = (P ∆ M) ∆ M := (symmDiff_symmDiff_cancel_right M P).symm
    _ = (Q ∆ M) ∆ M := by rw [hPMset, hQMset]
    _ = Q := symmDiff_symmDiff_cancel_right M Q

/-- A cube neighbor of a two-element set has cardinality one or three. -/
theorem common_neighbor_card_one_or_three
    {P M : Finset ι} (hP : #P = 2)
    (hPM : (hypercubeGraph ι).Adj P M) :
    #M = 1 ∨ #M = 3 := by
  have hdis : Disjoint (P \ M) (M \ P) := by
    rw [Finset.disjoint_left]
    intro x hxP hxM
    exact (Finset.mem_sdiff.mp hxP).2 (Finset.mem_sdiff.mp hxM).1
  have hdiff : #(P \ M) + #(M \ P) = 1 := by
    simpa [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis] using
      ((hypercubeGraph_adj P M).mp hPM)
  have hPpart := Finset.card_sdiff_add_card_inter P M
  have hMpart := Finset.card_sdiff_add_card_inter M P
  rw [Finset.inter_comm M P] at hMpart
  omega

/-- The only common cube neighbors of two distance-two vertices in the same
layer are their intersection and union. -/
theorem common_cube_neighbor_eq_inter_or_union
    {P Q M : Finset ι} (hP : #P = 2) (hQ : #Q = 2)
    (hPQdist : #(P ∆ Q) = 2)
    (hPM : (hypercubeGraph ι).Adj P M)
    (hQM : (hypercubeGraph ι).Adj Q M) :
    M = P ∩ Q ∨ M = P ∪ Q := by
  have hPQ : P ≠ Q := by
    intro h
    subst Q
    simp at hPQdist
  obtain ⟨hinter, hunion⟩ :=
    card_inter_eq_one_and_card_union_eq_three hP hQ hPQdist
  rcases common_neighbor_card_one_or_three hP hPM with hM | hM
  · left
    exact (Finset.eq_of_subset_of_card_le
      (inter_subset_common_cube_neighbor hPM hQM hPQ) (by omega)).symm
  · right
    exact Finset.eq_of_subset_of_card_le
      (common_cube_neighbor_subset_union hPM hQM hPQ) (by omega)

/-- For an edge inside the second pole layer, its shifted subdivision image
is exactly the intersection or the union of the two shifted pole images. -/
theorem shiftedSubdivision_eq_inter_or_union
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) {u v : V}
    (hu : u ∈ secondPoleLayer (poleImage f) w)
    (hv : v ∈ secondPoleLayer (poleImage f) w)
    (huv : G.Adj u v) :
    shiftedSubdivision f w (subdivisionEdgeVertex u v huv) =
        shiftedPole f w u ∩ shiftedPole f w v ∨
      shiftedSubdivision f w (subdivisionEdgeVertex u v huv) =
        shiftedPole f w u ∪ shiftedPole f w v := by
  apply common_cube_neighbor_eq_inter_or_union
  · exact (mem_secondPoleLayer_poleImage f w u).mp hu
  · exact (mem_secondPoleLayer_poleImage f w v).mp hv
  · exact shiftedPole_edge_distance_two f w huv
  · exact cube_adj_shiftedPole_shiftedSubdivision f w u _
      (Sym2.mem_mk_left u v)
  · exact cube_adj_shiftedPole_shiftedSubdivision f w v _
      (Sym2.mem_mk_right u v)

/-- Predicate selecting the local edges whose shifted subdivision vertex is
the intersection common neighbor. -/
def IsLocalIntersectionEdge
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u v : V) : Prop :=
  u ∈ secondPoleLayer (poleImage f) w ∧
    v ∈ secondPoleLayer (poleImage f) w ∧
    ∃ h : G.Adj u v,
      shiftedSubdivision f w (subdivisionEdgeVertex u v h) =
        shiftedPole f w u ∩ shiftedPole f w v

/-- Predicate selecting the local edges whose shifted subdivision vertex is
the union common neighbor. -/
def IsLocalUnionEdge
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u v : V) : Prop :=
  u ∈ secondPoleLayer (poleImage f) w ∧
    v ∈ secondPoleLayer (poleImage f) w ∧
    ∃ h : G.Adj u v,
      shiftedSubdivision f w (subdivisionEdgeVertex u v h) =
        shiftedPole f w u ∪ shiftedPole f w v

private theorem subdivisionEdgeVertex_comm
    (u v : V) (huv : G.Adj u v) :
    subdivisionEdgeVertex u v huv = subdivisionEdgeVertex v u huv.symm := by
  apply Subtype.ext
  exact Sym2.eq_swap

theorem isLocalIntersectionEdge_comm
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u v : V) :
    IsLocalIntersectionEdge f w u v ↔ IsLocalIntersectionEdge f w v u := by
  constructor
  · rintro ⟨hu, hv, huv, heq⟩
    refine ⟨hv, hu, huv.symm, ?_⟩
    rw [← subdivisionEdgeVertex_comm u v huv, Finset.inter_comm]
    exact heq
  · rintro ⟨hv, hu, hvu, heq⟩
    refine ⟨hu, hv, hvu.symm, ?_⟩
    rw [subdivisionEdgeVertex_comm u v hvu.symm, Finset.inter_comm]
    exact heq

theorem isLocalUnionEdge_comm
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u v : V) :
    IsLocalUnionEdge f w u v ↔ IsLocalUnionEdge f w v u := by
  constructor
  · rintro ⟨hu, hv, huv, heq⟩
    refine ⟨hv, hu, huv.symm, ?_⟩
    rw [← subdivisionEdgeVertex_comm u v huv, Finset.union_comm]
    exact heq
  · rintro ⟨hv, hu, hvu, heq⟩
    refine ⟨hu, hv, hvu.symm, ?_⟩
    rw [subdivisionEdgeVertex_comm u v hvu.symm, Finset.union_comm]
    exact heq

/-- The intersection half of the paper's partition of `G[L_w]`. -/
noncomputable def localIntersectionGraph
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) : SimpleGraph V :=
  SimpleGraph.fromRel (IsLocalIntersectionEdge f w)

/-- The union half of the paper's partition of `G[L_w]`. -/
noncomputable def localUnionGraph
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) : SimpleGraph V :=
  SimpleGraph.fromRel (IsLocalUnionEdge f w)

@[simp]
theorem localIntersectionGraph_adj
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u v : V) :
    (localIntersectionGraph f w).Adj u v ↔ IsLocalIntersectionEdge f w u v := by
  rw [localIntersectionGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact (isLocalIntersectionEdge_comm f w v u).mp h
  · intro h
    exact ⟨h.2.2.choose.ne, Or.inl h⟩

@[simp]
theorem localUnionGraph_adj
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u v : V) :
    (localUnionGraph f w).Adj u v ↔ IsLocalUnionEdge f w u v := by
  rw [localUnionGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact (isLocalUnionEdge_comm f w v u).mp h
  · intro h
    exact ⟨h.2.2.choose.ne, Or.inl h⟩

/-- Every base edge induced by the second pole layer lies in one of the two
local graphs. -/
theorem local_edge_partition
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) {u v : V}
    (hu : u ∈ secondPoleLayer (poleImage f) w)
    (hv : v ∈ secondPoleLayer (poleImage f) w)
    (huv : G.Adj u v) :
    (localIntersectionGraph f w).Adj u v ∨
      (localUnionGraph f w).Adj u v := by
  rcases shiftedSubdivision_eq_inter_or_union f w hu hv huv with h | h
  · left
    exact (localIntersectionGraph_adj f w u v).mpr ⟨hu, hv, huv, h⟩
  · right
    exact (localUnionGraph_adj f w u v).mpr ⟨hu, hv, huv, h⟩

/-! ## The intersection graph has maximum degree two -/

private noncomputable def localIntersectionBaseAdj
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u : V) (v : (localIntersectionGraph f w).neighborSet u) :
    G.Adj u v :=
  ((localIntersectionGraph_adj f w u v).mp v.property).2.2.choose

/-- The coordinate deleted from a pole to reach the intersection-type
subdivision vertex associated with a local neighbor. -/
private noncomputable def localIntersectionDirection
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u : V) (v : (localIntersectionGraph f w).neighborSet u) : ι :=
  incidenceDirection f u
    (subdivisionEdgeVertex u v (localIntersectionBaseAdj f w u v))
    (Sym2.mem_mk_left u v)

private theorem shifted_incidence_symmDiff_eq_singleton
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u : V) (v : (localIntersectionGraph f w).neighborSet u) :
    shiftedPole f w u ∆
        shiftedSubdivision f w
          (subdivisionEdgeVertex u v (localIntersectionBaseAdj f w u v)) =
      {localIntersectionDirection f w u v} := by
  rw [shiftedPole, shiftedSubdivision, symmDiff_translate_symmDiff]
  exact pole_symmDiff_subdivisionImage_eq_singleton f u _ _

private theorem localIntersectionDirection_mem
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u : V) (v : (localIntersectionGraph f w).neighborSet u) :
    localIntersectionDirection f w u v ∈ shiftedPole f w u := by
  let hlocal := (localIntersectionGraph_adj f w u v).mp v.property
  let huv : G.Adj u v := localIntersectionBaseAdj f w u v
  let e := subdivisionEdgeVertex u v huv
  let i := localIntersectionDirection f w u v
  have hmid : shiftedSubdivision f w e =
      shiftedPole f w u ∩ shiftedPole f w v := by
    exact hlocal.2.2.choose_spec
  have hiSD : i ∈ shiftedPole f w u ∆ shiftedSubdivision f w e := by
    rw [shifted_incidence_symmDiff_eq_singleton f w u v]
    simp [i]
  rcases Finset.mem_symmDiff.mp hiSD with hi | hi
  · exact hi.1
  · exfalso
    exact hi.2 ((Finset.mem_inter.mp (hmid ▸ hi.1)).1)

private theorem shiftedSubdivision_eq_toggle_localIntersectionDirection
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u : V) (v : (localIntersectionGraph f w).neighborSet u) :
    shiftedSubdivision f w
        (subdivisionEdgeVertex u v (localIntersectionBaseAdj f w u v)) =
      shiftedPole f w u ∆ {localIntersectionDirection f w u v} := by
  calc
    shiftedSubdivision f w
        (subdivisionEdgeVertex u v (localIntersectionBaseAdj f w u v)) =
        shiftedPole f w u ∆
          (shiftedPole f w u ∆
            shiftedSubdivision f w
              (subdivisionEdgeVertex u v (localIntersectionBaseAdj f w u v))) :=
      (symmDiff_symmDiff_cancel_left _ _).symm
    _ = shiftedPole f w u ∆ {localIntersectionDirection f w u v} := by
      rw [shifted_incidence_symmDiff_eq_singleton f w u v]

private theorem localIntersectionDirection_injective
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u : V) :
    Function.Injective (localIntersectionDirection f w u) := by
  intro v z hdir
  apply Subtype.ext
  let hv : G.Adj u v := localIntersectionBaseAdj f w u v
  let hz : G.Adj u z := localIntersectionBaseAdj f w u z
  let ev := subdivisionEdgeVertex u v hv
  let ez := subdivisionEdgeVertex u z hz
  have hshift : shiftedSubdivision f w ev = shiftedSubdivision f w ez := by
    rw [shiftedSubdivision_eq_toggle_localIntersectionDirection f w u v,
      shiftedSubdivision_eq_toggle_localIntersectionDirection f w u z, hdir]
  have himage : subdivisionImage f ev = subdivisionImage f ez := by
    calc
      subdivisionImage f ev =
          (subdivisionImage f ev ∆ poleImage f w) ∆ poleImage f w :=
        (symmDiff_symmDiff_cancel_right _ _).symm
      _ = (subdivisionImage f ez ∆ poleImage f w) ∆ poleImage f w := by
        rw [← shiftedSubdivision, ← shiftedSubdivision, hshift]
      _ = subdivisionImage f ez := symmDiff_symmDiff_cancel_right _ _
  have he : ev = ez := Sum.inr_injective (f.injective himage)
  have hedge : s(u, (v : V)) = s(u, (z : V)) := congrArg Subtype.val he
  have hvMem : (v : V) ∈ s(u, (z : V)) := by
    rw [← hedge]
    exact Sym2.mem_mk_right u v
  rcases Sym2.mem_iff.mp hvMem with hvu | hvz
  · exact False.elim (hv.ne hvu.symm)
  · exact hvz

/-- Every vertex of the intersection graph has at most two neighbors. -/
theorem localIntersectionGraph_degree_le_two
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w u : V) [DecidableRel (localIntersectionGraph f w).Adj]
    (hu : u ∈ secondPoleLayer (poleImage f) w) :
    #((localIntersectionGraph f w).neighborFinset u) ≤ 2 := by
  classical
  let D : (localIntersectionGraph f w).neighborSet u →
      {i // i ∈ shiftedPole f w u} :=
    fun v => ⟨localIntersectionDirection f w u v,
      localIntersectionDirection_mem f w u v⟩
  have hD : Function.Injective D := by
    intro v z h
    apply localIntersectionDirection_injective f w u
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective D hD
  have huCard : #(shiftedPole f w u) = 2 :=
    (mem_secondPoleLayer_poleImage f w u).mp hu
  rw [SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree] at hcard
  simpa [huCard] using hcard

/-! ## The bit target used for the union graph -/

/-- The other coordinate of a two-element finite set. -/
noncomputable def otherCoordinate (P : Finset ι) (i : ι)
    (hi : i ∈ P) (hP : #P = 2) : ι :=
  (Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hi, hP])).choose

theorem erase_eq_singleton_otherCoordinate (P : Finset ι) (i : ι)
    (hi : i ∈ P) (hP : #P = 2) :
    P.erase i = {otherCoordinate P i hi hP} :=
  (Finset.card_eq_one.mp (by rw [Finset.card_erase_of_mem hi, hP])).choose_spec

theorem otherCoordinate_mem (P : Finset ι) (i : ι)
    (hi : i ∈ P) (hP : #P = 2) :
    otherCoordinate P i hi hP ∈ P := by
  have hmem : otherCoordinate P i hi hP ∈ P.erase i := by
    rw [erase_eq_singleton_otherCoordinate P i hi hP]
    simp
  exact (Finset.mem_erase.mp hmem).2

theorem otherCoordinate_ne (P : Finset ι) (i : ι)
    (hi : i ∈ P) (hP : #P = 2) :
    otherCoordinate P i hi hP ≠ i := by
  have hmem : otherCoordinate P i hi hP ∈ P.erase i := by
    rw [erase_eq_singleton_otherCoordinate P i hi hP]
    simp
  exact (Finset.mem_erase.mp hmem).1

theorem pair_eq_insert_otherCoordinate (P : Finset ι) (i : ι)
    (hi : i ∈ P) (hP : #P = 2) :
    P = {i, otherCoordinate P i hi hP} := by
  ext x
  constructor
  · intro hx
    by_cases hxi : x = i
    · simp [hxi]
    · have hxErase : x ∈ P.erase i := Finset.mem_erase.mpr ⟨hxi, hx⟩
      rw [erase_eq_singleton_otherCoordinate P i hi hP] at hxErase
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (by simpa using hxErase)
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi
    · exact otherCoordinate_mem P i hi hP

/-- Required value of the random bit at a coordinate of a shifted pole pair.
For a pair `{i,j}`, it is the prefix parity of the unshifted pole at the
other coordinate `j`, plus the monochromatic colour.  This is equivalent to
the target displayed in the paper, but avoids a separate min/max definition. -/
noncomputable def localSelectionTarget
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w v : V) (i : ι) : Fin 2 :=
  if hP : #(shiftedPole f w v) = 2 then
    if hi : i ∈ shiftedPole f w v then
      prefixParity (poleImage f v)
        (otherCoordinate (shiftedPole f w v) i hi hP) + c
    else 0
  else 0

theorem localSelectionTarget_eq
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w v : V) {i j : ι} (hij : i ≠ j)
    (hpair : shiftedPole f w v = {i, j}) :
    localSelectionTarget f w v i = prefixParity (poleImage f v) j + c := by
  have hP : #(shiftedPole f w v) = 2 := by rw [hpair, Finset.card_pair hij]
  have hi : i ∈ shiftedPole f w v := by rw [hpair]; simp
  rw [localSelectionTarget, dif_pos hP, dif_pos hi]
  have herase : (shiftedPole f w v).erase i = {j} := by
    rw [hpair]
    simp [hij, hij.symm]
  have hother : otherCoordinate (shiftedPole f w v) i hi hP = j := by
    apply Finset.singleton_injective
    rw [← herase]
    exact (erase_eq_singleton_otherCoordinate _ _ _ _).symm
  rw [hother]

/-- Below the smaller of two changed coordinates, the two cube vertices
have identical prefixes. -/
theorem prefixParity_eq_of_symmDiff_pair_at_lower
    {A B : Finset ι} {b b' : ι} (hbb' : b < b')
    (hAB : A ∆ B = {b, b'}) :
    prefixParity A b = prefixParity B b := by
  have hpref : cubePrefix A b = cubePrefix B b := by
    ext x
    simp only [cubePrefix, Finset.mem_filter]
    constructor
    · rintro ⟨hxA, hxb⟩
      refine ⟨?_, hxb⟩
      by_contra hxB
      have hxSD : x ∈ A ∆ B :=
        Finset.mem_symmDiff.mpr (Or.inl ⟨hxA, hxB⟩)
      rw [hAB] at hxSD
      have hx : x = b ∨ x = b' := by simpa using hxSD
      rcases hx with hxeq | hxeq
      · exact (ne_of_lt hxb) hxeq
      · exact (not_lt_of_ge hbb'.le) (hxeq ▸ hxb)
    · rintro ⟨hxB, hxb⟩
      refine ⟨?_, hxb⟩
      by_contra hxA
      have hxSD : x ∈ A ∆ B :=
        Finset.mem_symmDiff.mpr (Or.inr ⟨hxB, hxA⟩)
      rw [hAB] at hxSD
      have hx : x = b ∨ x = b' := by simpa using hxSD
      rcases hx with hxeq | hxeq
      · exact (ne_of_lt hxb) hxeq
      · exact (not_lt_of_ge hbb'.le) (hxeq ▸ hxb)
  simp [prefixParity, hpref]

private theorem prefix_symmDiff_eq_singleton_at_upper
    {A B : Finset ι} {b b' : ι} (hbb' : b < b')
    (hAB : A ∆ B = {b, b'}) :
    cubePrefix A b' ∆ cubePrefix B b' = {b} := by
  ext x
  simp only [Finset.mem_symmDiff, cubePrefix, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro (hx | hx)
    · have hxSD : x ∈ A ∆ B :=
        Finset.mem_symmDiff.mpr (Or.inl ⟨hx.1.1, fun hxB => hx.2 ⟨hxB, hx.1.2⟩⟩)
      rw [hAB] at hxSD
      have hxb : x = b ∨ x = b' := by simpa using hxSD
      exact hxb.resolve_right (ne_of_lt hx.1.2)
    · have hxSD : x ∈ A ∆ B :=
        Finset.mem_symmDiff.mpr (Or.inr ⟨hx.1.1, fun hxA => hx.2 ⟨hxA, hx.1.2⟩⟩)
      rw [hAB] at hxSD
      have hxb : x = b ∨ x = b' := by simpa using hxSD
      exact hxb.resolve_right (ne_of_lt hx.1.2)
  · intro hxb
    subst x
    have hbSD : b ∈ A ∆ B := by rw [hAB]; simp
    rcases Finset.mem_symmDiff.mp hbSD with hb | hb
    · exact Or.inl ⟨⟨hb.1, hbb'⟩, fun h => hb.2 h.1⟩
    · exact Or.inr ⟨⟨hb.1, hbb'⟩, fun h => hb.2 h.1⟩

private theorem card_mod_two_ne_of_symmDiff_singleton
    {S T : Finset ι} {x : ι} (hST : S ∆ T = {x}) :
    S.card % 2 ≠ T.card % 2 := by
  have hxSD : x ∈ S ∆ T := by rw [hST]; simp
  rcases Finset.mem_symmDiff.mp hxSD with hx | hx
  · have hS : S = insert x T := by
      ext y
      by_cases hyx : y = x
      · subst y; simp [hx.1]
      · have hyNotSD : y ∉ S ∆ T := by rw [hST]; simpa
        simp only [Finset.mem_insert, Finset.mem_singleton, hyx, false_or]
        constructor
        · intro hyS
          by_contra hyT
          exact hyNotSD (Finset.mem_symmDiff.mpr (Or.inl ⟨hyS, hyT⟩))
        · intro hyT
          by_contra hyS
          exact hyNotSD (Finset.mem_symmDiff.mpr (Or.inr ⟨hyT, hyS⟩))
    rw [hS, Finset.card_insert_of_notMem hx.2]
    omega
  · have hT : T = insert x S := by
      ext y
      by_cases hyx : y = x
      · subst y; simp [hx.1]
      · have hyNotSD : y ∉ S ∆ T := by rw [hST]; simpa
        simp only [Finset.mem_insert, Finset.mem_singleton, hyx, false_or]
        constructor
        · intro hyT
          by_contra hyS
          exact hyNotSD (Finset.mem_symmDiff.mpr (Or.inr ⟨hyT, hyS⟩))
        · intro hyS
          by_contra hyT
          exact hyNotSD (Finset.mem_symmDiff.mpr (Or.inl ⟨hyS, hyT⟩))
    rw [hT, Finset.card_insert_of_notMem hx.2]
    omega

/-- At the larger of two changed coordinates, the prefix parities are
opposite. -/
theorem prefixParity_ne_of_symmDiff_pair_at_upper
    {A B : Finset ι} {b b' : ι} (hbb' : b < b')
    (hAB : A ∆ B = {b, b'}) :
    prefixParity A b' ≠ prefixParity B b' := by
  intro heq
  have hval := congrArg Fin.val heq
  exact card_mod_two_ne_of_symmDiff_singleton
    (prefix_symmDiff_eq_singleton_at_upper hbb' hAB) (by
      simpa [prefixParity] using hval)

private theorem pair_symmDiff_pair_same_left
    {a b b' : ι} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') :
    ({a, b} : Finset ι) ∆ {a, b'} = {b, b'} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  aesop

private theorem pair_symmDiff_triple_eq_right
    {a b b' : ι} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') :
    ({a, b} : Finset ι) ∆ ({a, b} ∪ {a, b'}) = {b'} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  aesop

private theorem pair_symmDiff_triple_eq_left
    {a b b' : ι} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') :
    ({a, b'} : Finset ι) ∆ ({a, b} ∪ {a, b'}) = {b} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  aesop

/-- In an oriented union-type edge, the target values at the shared
coordinate are different.  This is the parity-colouring core of Lemma 2.2. -/
private theorem localSelectionTarget_ne_of_oriented_union
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) {u v : V} {a b b' : ι}
    (hlocal : IsLocalUnionEdge f w u v)
    (hPu : shiftedPole f w u = {a, b})
    (hPv : shiftedPole f w v = {a, b'})
    (hbb' : b < b') :
    localSelectionTarget f w u a ≠ localSelectionTarget f w v a := by
  obtain ⟨hu, hv, huv, hmid⟩ := hlocal
  have hPucard : #(shiftedPole f w u) = 2 :=
    (mem_secondPoleLayer_poleImage f w u).mp hu
  have hPvcard : #(shiftedPole f w v) = 2 :=
    (mem_secondPoleLayer_poleImage f w v).mp hv
  have hab : a ≠ b := by
    intro h
    rw [h, Finset.pair_eq_singleton] at hPu
    rw [hPu] at hPucard
    simp at hPucard
  have hab' : a ≠ b' := by
    intro h
    rw [h, Finset.pair_eq_singleton] at hPv
    rw [hPv] at hPvcard
    simp at hPvcard
  have hbbne : b ≠ b' := ne_of_lt hbb'
  let e := subdivisionEdgeVertex u v huv
  have hdirU : incidenceDirection f u e (Sym2.mem_mk_left u v) = b' := by
    apply Finset.singleton_injective
    calc
      {incidenceDirection f u e (Sym2.mem_mk_left u v)} =
          shiftedPole f w u ∆ shiftedSubdivision f w e :=
        (shifted_pole_subdivision_symmDiff_eq_singleton f w u e _).symm
      _ = {a, b} ∆ ({a, b} ∪ {a, b'}) := by rw [hPu, hmid, hPu, hPv]
      _ = {b'} := pair_symmDiff_triple_eq_right hab hab' hbbne
  have hdirV : incidenceDirection f v e (Sym2.mem_mk_right u v) = b := by
    apply Finset.singleton_injective
    calc
      {incidenceDirection f v e (Sym2.mem_mk_right u v)} =
          shiftedPole f w v ∆ shiftedSubdivision f w e :=
        (shifted_pole_subdivision_symmDiff_eq_singleton f w v e _).symm
      _ = {a, b'} ∆ ({a, b} ∪ {a, b'}) := by rw [hPv, hmid, hPu, hPv]
      _ = {b} := pair_symmDiff_triple_eq_left hab hab' hbbne
  have hcolourU : prefixParity (poleImage f u) b' = c := by
    rw [← hdirU]
    exact incidence_prefixParity_eq_color f u e (Sym2.mem_mk_left u v)
  have hcolourV : prefixParity (poleImage f v) b = c := by
    rw [← hdirV]
    exact incidence_prefixParity_eq_color f v e (Sym2.mem_mk_right u v)
  have hPoleDiff : poleImage f u ∆ poleImage f v = {b, b'} := by
    calc
      poleImage f u ∆ poleImage f v =
          shiftedPole f w u ∆ shiftedPole f w v :=
        (symmDiff_translate_symmDiff _ _ _).symm
      _ = {a, b} ∆ {a, b'} := by rw [hPu, hPv]
      _ = {b, b'} := pair_symmDiff_pair_same_left hab hab' hbbne
  have hlower : prefixParity (poleImage f u) b =
      prefixParity (poleImage f v) b :=
    prefixParity_eq_of_symmDiff_pair_at_lower hbb' hPoleDiff
  have hupper : prefixParity (poleImage f u) b' ≠
      prefixParity (poleImage f v) b' :=
    prefixParity_ne_of_symmDiff_pair_at_upper hbb' hPoleDiff
  rw [localSelectionTarget_eq f w u hab hPu,
    localSelectionTarget_eq f w v hab' hPv]
  intro htarget
  have hlowColour : prefixParity (poleImage f u) b = c := hlower.trans hcolourV
  rw [hlowColour] at htarget
  have hvUpper : c = prefixParity (poleImage f v) b' :=
    add_right_cancel htarget
  exact hupper (hcolourU.trans hvUpper)

/-- Every edge of the union graph has a shared coordinate at which its two
endpoint targets disagree. -/
theorem exists_common_coordinate_target_ne_of_localUnionGraph_adj
    [Fintype V] [DecidableEq V]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) {u v : V} (huv : (localUnionGraph f w).Adj u v) :
    ∃ a : ι,
      a ∈ shiftedPole f w u ∧ a ∈ shiftedPole f w v ∧
        localSelectionTarget f w u a ≠ localSelectionTarget f w v a := by
  let hlocal := (localUnionGraph_adj f w u v).mp huv
  have hu : u ∈ secondPoleLayer (poleImage f) w := hlocal.1
  have hv : v ∈ secondPoleLayer (poleImage f) w := hlocal.2.1
  have hbase : G.Adj u v := hlocal.2.2.choose
  have hPucard : #(shiftedPole f w u) = 2 :=
    (mem_secondPoleLayer_poleImage f w u).mp hu
  have hPvcard : #(shiftedPole f w v) = 2 :=
    (mem_secondPoleLayer_poleImage f w v).mp hv
  have hdist : #(shiftedPole f w u ∆ shiftedPole f w v) = 2 :=
    shiftedPole_edge_distance_two f w hbase
  obtain ⟨hinterCard, _⟩ :=
    card_inter_eq_one_and_card_union_eq_three hPucard hPvcard hdist
  obtain ⟨a, hinter⟩ := Finset.card_eq_one.mp hinterCard
  have haInter : a ∈ shiftedPole f w u ∩ shiftedPole f w v := by
    rw [hinter]
    simp
  have hau : a ∈ shiftedPole f w u := (Finset.mem_inter.mp haInter).1
  have hav : a ∈ shiftedPole f w v := (Finset.mem_inter.mp haInter).2
  let b := otherCoordinate (shiftedPole f w u) a hau hPucard
  let b' := otherCoordinate (shiftedPole f w v) a hav hPvcard
  have hPu : shiftedPole f w u = {a, b} :=
    pair_eq_insert_otherCoordinate _ _ hau hPucard
  have hPv : shiftedPole f w v = {a, b'} :=
    pair_eq_insert_otherCoordinate _ _ hav hPvcard
  have hbbne : b ≠ b' := by
    intro h
    rw [hPu, hPv, h] at hdist
    simp at hdist
  refine ⟨a, hau, hav, ?_⟩
  by_cases hbb : b < b'
  · exact localSelectionTarget_ne_of_oriented_union f w hlocal hPu hPv hbb
  · have hb'b : b' < b := lt_of_le_of_ne (le_of_not_gt hbb) hbbne.symm
    exact (localSelectionTarget_ne_of_oriented_union f w
      ((isLocalUnionEdge_comm f w u v).mp hlocal) hPv hPu hb'b).symm

/-- Every assignment-selected set is independent in the union half of the
local edge partition. -/
theorem keptByAssignment_isIndepSet_localUnionGraph
    [Fintype V] [DecidableEq V] [Fintype ι]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) (r : ι → Fin 2) :
    (localUnionGraph f w).IsIndepSet
      (keptByAssignment (secondPoleLayer (poleImage f) w)
        (shiftedPole f w) (localSelectionTarget f w) r : Finset V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro u hu v hv huv
  intro hadj
  obtain ⟨a, hau, hav, htarget⟩ :=
    exists_common_coordinate_target_ne_of_localUnionGraph_adj f w hadj
  have hru := (mem_keptByAssignment.mp hu).2 a hau
  have hrv := (mem_keptByAssignment.mp hv).2 a hav
  exact htarget (hru.symm.trans hrv)

/-- Lemma 2.2: in every shifted second pole layer, at least one twelfth of
the vertices form an independent set of the base graph. -/
theorem localParity_independent_extraction
    [Fintype V] [DecidableEq V] [Fintype ι]
    (f : SimpleGraph.Copy (oneSubdivision G)
      ((parityColoring : (hypercubeGraph ι).EdgeLabeling (Fin 2)).labelGraph c))
    (w : V) :
    ∃ I : Finset V,
      I ⊆ secondPoleLayer (poleImage f) w ∧
        G.IsIndepSet (I : Set V) ∧
        #(secondPoleLayer (poleImage f) w) ≤ 12 * #I := by
  classical
  let L := secondPoleLayer (poleImage f) w
  obtain ⟨r, hquarter⟩ :=
    exists_assignment_card_le_four_mul_kept L (shiftedPole f w)
      (localSelectionTarget f w) (by
        intro v hv
        exact (mem_secondPoleLayer_poleImage f w v).mp hv)
  let K := keptByAssignment L (shiftedPole f w) (localSelectionTarget f w) r
  have hKsub : K ⊆ L := by
    intro v hv
    exact (mem_keptByAssignment.mp hv).1
  have hKunion : (localUnionGraph f w).IsIndepSet (K : Set V) :=
    keptByAssignment_isIndepSet_localUnionGraph f w r
  letI : DecidableRel (localIntersectionGraph f w).Adj := Classical.decRel _
  obtain ⟨I, hIK, hIcap, hthird⟩ :=
    exists_indepSet_card_third (localIntersectionGraph f w) K (by
      intro v hv
      have hvL : v ∈ L := hKsub hv
      calc
        #((localIntersectionGraph f w).neighborFinset v ∩ K) ≤
            #((localIntersectionGraph f w).neighborFinset v) :=
          Finset.card_le_card Finset.inter_subset_left
        _ ≤ 2 := localIntersectionGraph_degree_le_two f w v hvL)
  refine ⟨I, hIK.trans hKsub, ?_, ?_⟩
  · rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv huv
    intro hG
    have huK : u ∈ K := hIK hu
    have hvK : v ∈ K := hIK hv
    have huL : u ∈ L := hKsub huK
    have hvL : v ∈ L := hKsub hvK
    rcases local_edge_partition f w huL hvL hG with hcap | hunion
    · exact ((SimpleGraph.isIndepSet_iff (localIntersectionGraph f w)).mp hIcap)
        hu hv huv hcap
    · exact ((SimpleGraph.isIndepSet_iff (localUnionGraph f w)).mp hKunion)
        huK hvK huv hunion
  · change #L ≤ 4 * #K at hquarter
    change #(secondPoleLayer (poleImage f) w) ≤ 12 * #I
    dsimp [L] at hquarter
    omega

/-- Proposition-2.3 core: an avoidance base has no monochromatic copy of its
one-subdivision in either class of the explicit parity colouring. -/
theorem parityColoring_free_oneSubdivision_of_isAvoidanceBase
    {κ : Type u} [Fintype κ] [LinearOrder κ]
    [Fintype V] [DecidableEq V]
    (hbase : IsAvoidanceBase G) (c : Fin 2) :
    (oneSubdivision G).Free
      ((parityColoring : (hypercubeGraph κ).EdgeLabeling (Fin 2)).labelGraph c) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  exact false_of_hasPoleConcentration_and_extraction G hbase.concentrated
    hbase.ten_le_card hbase.small_independent (poleImage f)
    (poleImage_isPolePlacement f) (localParity_independent_extraction f)

end LeanCo.HypercubeTuran
