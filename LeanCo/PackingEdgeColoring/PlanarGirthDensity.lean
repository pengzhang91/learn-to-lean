import LeanCo.PackingEdgeColoring.EulerBound
import LeanCo.PackingEdgeColoring.FaceBoundaryMinimumDegree
import LeanCo.PackingEdgeColoring.ComponentColoring
import LeanCo.PackingEdgeColoring.PlanarDeletion
import LeanCo.PackingEdgeColoring.PlanarHeredity

/-!
# Density of planar graphs of girth twelve

This file supplies the planar corollary needed to turn the maximum-average-
degree theorem from Section 3 into the first headline theorem of the paper.
The key inequality is proved directly from the spherical rotation
certificate, including faces incident with bridges.
-/

open scoped BigOperators SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace ConnectedComponent

/-- Darts whose first vertex lies outside a component are exactly the darts
of the graph induced on the complementary vertex set. -/
def complementDartEquiv (C : G.ConnectedComponent) :
    (G.induce C.suppᶜ).Dart ≃ {d : G.Dart // ¬ d.fst ∈ C.supp} where
  toFun d := ⟨⟨(d.fst.1, d.snd.1), d.adj⟩, d.fst.2⟩
  invFun d := by
    have hsnd : ¬ d.1.snd ∈ C.supp := by
      intro hsnd
      exact d.2 (C.mem_supp_of_adj_mem_supp hsnd d.1.adj.symm)
    exact ⟨(⟨d.1.fst, d.2⟩, ⟨d.1.snd, hsnd⟩), d.1.adj⟩
  left_inv d := by
    apply Dart.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv d := by
    apply Subtype.ext
    apply Dart.ext
    apply Prod.ext <;> rfl

/-- A component and the graph induced on its vertex complement partition
all ambient darts. -/
def dartSumComplementEquiv (C : G.ConnectedComponent) :
    C.toSimpleGraph.Dart ⊕ (G.induce C.suppᶜ).Dart ≃ G.Dart := by
  classical
  exact (Equiv.sumCongr (RotationSystem.componentDartEquiv C)
      (complementDartEquiv C)).trans
        (Equiv.sumCompl (fun d : G.Dart ↦ d.fst ∈ C.supp))

/-- The vertices of a component and the vertices outside it partition the
ambient vertex type.  This explicit equivalence avoids any dependence on
the particular `Fintype` instance carried by the component subtype. -/
def vertexSumComplementEquiv (C : G.ConnectedComponent) :
    C ⊕ ↥(C.suppᶜ : Set V) ≃ V := by
  classical
  exact
    { toFun := fun x ↦ match x with
        | Sum.inl y => y.1
        | Sum.inr y => y.1
      invFun := fun v ↦ if hv : v ∈ C.supp then Sum.inl ⟨v, hv⟩
        else Sum.inr ⟨v, hv⟩
      left_inv := by
        intro x
        rcases x with x | x
        · simp [x.2]
        · have hx : ¬ x.1 ∈ C.supp := x.2
          simp [hx]
      right_inv := by
        intro v
        by_cases hv : v ∈ C.supp <;> simp [hv] }

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Edge cardinality splits over one connected component and the graph on
the complementary vertex set. -/
theorem card_edges_eq_add_component_complement (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    [DecidableRel (G.induce C.suppᶜ).Adj] :
    G.edgeFinset.card = C.toSimpleGraph.edgeFinset.card +
      (G.induce C.suppᶜ).edgeFinset.card := by
  have hcard := Fintype.card_congr (dartSumComplementEquiv C)
  simp only [Fintype.card_sum] at hcard
  rw [RotationSystem.card_darts_eq_two_mul_card_edges,
    RotationSystem.card_darts_eq_two_mul_card_edges,
    RotationSystem.card_darts_eq_two_mul_card_edges] at hcard
  omega

/-- Vertex cardinality splits over one connected component and its
complement. -/
theorem card_vertices_eq_add_component_complement (C : G.ConnectedComponent)
    [Fintype C] :
    Fintype.card V = Fintype.card C +
      Fintype.card ↥(C.suppᶜ : Set V) := by
  have hcard := Fintype.card_congr (vertexSumComplementEquiv C)
  simpa only [Fintype.card_sum] using hcard.symm

end Finite

end ConnectedComponent

namespace RotationSystem

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Euler's equality and girth twelve force the strict density bound needed
for `mad < 12 / 5`, provided every vertex has degree at least two.  The
minimum-degree hypothesis is what makes the face-length bound valid even in
the presence of bridges. -/
theorem five_mul_card_edges_lt_six_mul_card_vertices_of_girth_twelve
    (R : RotationSystem G) (hR : R.IsSpherical)
    (hdeg : ∀ v, 2 ≤ G.degree v)
    (hgirth : (12 : ℕ∞) ≤ G.egirth) :
    5 * G.edgeFinset.card < 6 * Fintype.card V := by
  have hface : ∀ f : R.Face, 12 ≤ R.faceLength f :=
    fun f ↦ R.le_faceLength_of_two_le_degree 12 hdeg hgirth f
  have hsum : 12 * R.faceCount ≤
      ∑ f : R.Face, R.faceLength f := by
    rw [R.faceCount_eq_card_face]
    calc
      12 * Fintype.card R.Face = ∑ _f : R.Face, 12 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ f : R.Face, R.faceLength f := by
        exact Finset.sum_le_sum fun f _ ↦ hface f
  rw [R.sum_faceLength_eq_two_mul_card_edges] at hsum
  unfold IsSpherical at hR
  omega

end Finite

end RotationSystem

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Connected component form of the girth-twelve density inequality. -/
theorem five_mul_card_edges_lt_six_mul_card_vertices_of_connected_planar_girth_twelve
    (hconn : G.Connected) (hplan : IsCombinatoriallyPlanar G)
    (hdeg : ∀ v, 2 ≤ G.degree v)
    (hgirth : (12 : ℕ∞) ≤ G.egirth) :
    5 * G.edgeFinset.card < 6 * Fintype.card V := by
  let v : V := Classical.choice hconn.nonempty
  let C : G.ConnectedComponent := G.connectedComponentMk v
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have hall : ∀ w : V, w ∈ C.supp :=
    RotationSystem.forall_mem_connectedComponent_of_preconnected
      hconn.preconnected C
  have hCedge : C.toSimpleGraph.edgeSet.Nonempty := by
    have hvpos : 0 < G.degree v := by have := hdeg v; omega
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hvpos
    exact ⟨s(⟨v, hall v⟩, ⟨w, hall w⟩), hvw⟩
  obtain ⟨R, hR⟩ := hplan C hCedge
  have hdegC : ∀ w : C, 2 ≤ C.toSimpleGraph.degree w := by
    intro w
    rw [degree_toSimpleGraph_connectedComponent G C w]
    exact hdeg w
  have hgirthC : (12 : ℕ∞) ≤ C.toSimpleGraph.egirth :=
    girth_lowerBound_connectedComponent G hgirth C
  have hdensity :=
    R.five_mul_card_edges_lt_six_mul_card_vertices_of_girth_twelve
      hR hdegC hgirthC
  have hvertices : Fintype.card C = Fintype.card V :=
    Fintype.card_congr
      (RotationSystem.componentVertexEquivOfForallMem C hall)
  have hedges : C.toSimpleGraph.edgeFinset.card = G.edgeFinset.card :=
    RotationSystem.restrictComponent_card_edges_eq_of_forall_mem C hall
  omega

/-- Every nonempty finite combinatorially planar graph of girth at least
twelve satisfies the density inequality `5 |E| < 6 |V|`.  The proof is a
strong induction on the vertex count.  A connected graph either has a
vertex of degree at most one, which is peeled, or has minimum degree two and
is handled by the facial Euler argument above.  A disconnected graph is
split into one component and its induced complement. -/
theorem five_mul_card_edges_lt_six_mul_card_vertices_of_planar_girth_twelve
    [Nonempty V] (hplan : IsCombinatoriallyPlanar G)
    (hgirth : (12 : ℕ∞) ≤ G.egirth) :
    5 * G.edgeFinset.card < 6 * Fintype.card V := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      have hnpos : 0 < n := by
        rw [← hn]
        exact @Fintype.card_pos V _ inferInstance
      by_cases hnOne : n = 1
      · have hedge : G.edgeFinset.card = 0 := by
          have hle := G.card_edgeFinset_le_card_choose_two
          have hchoose : (Fintype.card V).choose 2 = 0 := by
            simp [hn, hnOne]
          omega
        omega
      have hntwo : 2 ≤ n := by omega
      by_cases hconn : G.Connected
      · by_cases hdeg : ∀ v, 2 ≤ G.degree v
        · have hdensity :=
            five_mul_card_edges_lt_six_mul_card_vertices_of_connected_planar_girth_twelve
              (G := G) hconn hplan hdeg hgirth
          omega
        · push_neg at hdeg
          obtain ⟨v, hv⟩ := hdeg
          have hvle : G.degree v ≤ 1 := by omega
          haveI : Nontrivial V :=
            Fintype.one_lt_card_iff_nontrivial.mp (by omega)
          obtain ⟨w, hw⟩ := exists_ne v
          let s : Set V := {v}ᶜ
          let H : SimpleGraph s := G.induce s
          letI : Fintype s := inferInstance
          letI : DecidableEq s := Classical.decEq s
          letI : DecidableRel H.Adj := inferInstance
          letI : Nonempty s := ⟨⟨w, by simpa [s] using hw⟩⟩
          have hcardlt : Fintype.card s < n := by
            rw [← hn]
            exact Fintype.card_subtype_lt (p := fun x : V ↦ x ∈ s)
              (x := v) (by simp [s])
          have hplanH : IsCombinatoriallyPlanar H := by
            simpa only [H] using hplan.induce s
          have hgirthH : (12 : ℕ∞) ≤ H.egirth := by
            exact hgirth.trans
              (SimpleGraph.Embedding.induce s).isContained.egirth_le
          have hdensityH := ih (Fintype.card s) hcardlt
            (V := s) (G := H) hplanH hgirthH rfl
          have hinduce : H.edgeFinset.card =
              (G.deleteIncidenceSet v).edgeFinset.card := by
            calc
              H.edgeFinset.card =
                  (G.induce ({v}ᶜ : Set V)).edgeFinset.card := by
                    simp only [SimpleGraph.edgeFinset_card]
                    rfl
              _ = (G.deleteIncidenceSet v).edgeFinset.card :=
                G.card_edgeFinset_induce_compl_singleton v
          have hdelete : (G.deleteIncidenceSet v).edgeFinset.card =
              G.edgeFinset.card - G.degree v :=
            G.card_edgeFinset_deleteIncidenceSet v
          have hvEdge : G.degree v ≤ G.edgeFinset.card :=
            G.degree_le_card_edgeFinset v
          omega
      · have hnpre : ¬ G.Preconnected := by
          intro hp
          exact hconn ⟨hp⟩
        unfold SimpleGraph.Preconnected at hnpre
        push_neg at hnpre
        obtain ⟨u, v, huv⟩ := hnpre
        let C : G.ConnectedComponent := G.connectedComponentMk u
        have huC : u ∈ C.supp := by rfl
        have hvC : ¬ v ∈ C.supp := by
          intro hv
          apply huv
          exact (ConnectedComponent.exact hv).symm
        let K : SimpleGraph ↥(C.suppᶜ : Set V) := G.induce C.suppᶜ
        letI : Fintype C := Fintype.ofFinite C
        letI : DecidableEq C := Classical.decEq C
        letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
        letI : Fintype ↥(C.suppᶜ : Set V) := inferInstance
        letI : DecidableEq ↥(C.suppᶜ : Set V) := Classical.decEq _
        letI : DecidableRel K.Adj := inferInstance
        letI : Nonempty C := ⟨⟨u, huC⟩⟩
        letI : Nonempty ↥(C.suppᶜ : Set V) := ⟨⟨v, hvC⟩⟩
        have hCcardlt : Fintype.card C < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (p := fun x : V ↦ x ∈ C.supp)
            (x := v) hvC
        have hKcardlt : Fintype.card ↥(C.suppᶜ : Set V) < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt
            (p := fun x : V ↦ x ∈ C.suppᶜ) (x := u) (by simpa)
        have hplanC : IsCombinatoriallyPlanar C.toSimpleGraph := by
          simpa only [ConnectedComponent.toSimpleGraph] using hplan.induce C.supp
        have hplanK : IsCombinatoriallyPlanar K := by
          simpa only [K] using hplan.induce C.suppᶜ
        have hgirthC : (12 : ℕ∞) ≤ C.toSimpleGraph.egirth :=
          girth_lowerBound_connectedComponent G hgirth C
        have hgirthK : (12 : ℕ∞) ≤ K.egirth := by
          exact hgirth.trans
            (SimpleGraph.Embedding.induce C.suppᶜ).isContained.egirth_le
        have hdensityC := ih (Fintype.card C) hCcardlt
          (V := C) (G := C.toSimpleGraph) hplanC hgirthC rfl
        have hdensityK := ih (Fintype.card ↥(C.suppᶜ : Set V)) hKcardlt
          (V := ↥(C.suppᶜ : Set V)) (G := K) hplanK hgirthK rfl
        have hedges :=
          ConnectedComponent.card_edges_eq_add_component_complement
            (G := G) C
        have hvertices :=
          ConnectedComponent.card_vertices_eq_add_component_complement
            (G := G) C
        have hKedges : (G.induce C.suppᶜ).edgeFinset.card =
            K.edgeFinset.card := by
          simp only [SimpleGraph.edgeFinset_card]
          rfl
        change 5 * G.edgeFinset.card < 6 * n
        omega

/-- Planarity and girth twelve imply the strict maximum-average-degree
bound used by the Section 3 theorem. -/
theorem maximumAverageDegreeLT_twelve_five_of_planar_girth_twelve
    (hplan : IsCombinatoriallyPlanar G)
    (hgirth : (12 : ℕ∞) ≤ G.egirth) :
    MaximumAverageDegreeLT G 12 5 := by
  intro s hs
  let H : SimpleGraph s := G.induce s
  letI : Fintype s := inferInstance
  letI : DecidableEq s := Classical.decEq s
  letI : DecidableRel H.Adj := inferInstance
  letI : Nonempty s := hs.to_subtype
  have hplanH : IsCombinatoriallyPlanar H := by
    simpa only [H] using hplan.induce (s : Set V)
  have hgirthH : (12 : ℕ∞) ≤ H.egirth := by
    exact hgirth.trans
      (SimpleGraph.Embedding.induce (s : Set V)).isContained.egirth_le
  have hdensity :=
    five_mul_card_edges_lt_six_mul_card_vertices_of_planar_girth_twelve
      (G := H) hplanH hgirthH
  have hcard : Fintype.card s = s.card := Fintype.card_coe s
  change 5 * (2 * H.edgeFinset.card) < 12 * s.card
  omega

end Finite

end

end LeanCo.PackingEdgeColoring
