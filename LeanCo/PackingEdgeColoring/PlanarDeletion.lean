import LeanCo.PackingEdgeColoring.EulerBound

/-!
# Edge deletion in spherical rotation systems

This file combines the local face-surgery results with the Euler upper bound.
Its first consequence is that every non-bridge edge of a connected spherical
rotation system is incident with two distinct faces.  Hence deleting such an
edge preserves sphericality.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- If every ambient vertex belongs to a component, its vertex subtype is
canonically equivalent to the ambient vertex type. -/
def componentVertexEquivOfForallMem (C : G.ConnectedComponent)
    (hall : ∀ v : V, v ∈ C.supp) : C ≃ V where
  toFun v := v.1
  invFun v := ⟨v, hall v⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- If a component contains every vertex, its darts are canonically all
ambient darts. -/
def componentDartEquivOfForallMem (C : G.ConnectedComponent)
    (hall : ∀ v : V, v ∈ C.supp) : C.toSimpleGraph.Dart ≃ G.Dart where
  toFun d := (componentDartEquiv C d).1
  invFun d := (componentDartEquiv C).symm ⟨d, hall d.fst⟩
  left_inv d := by
    apply (componentDartEquiv C).injective
    exact (componentDartEquiv C).apply_symm_apply _
  right_inv d := by
    exact congrArg Subtype.val ((componentDartEquiv C).apply_symm_apply
      ⟨d, hall d.fst⟩)

/-- Restriction to a component containing every vertex preserves the face
count. -/
theorem restrictComponent_faceCount_eq_of_forall_mem
    (R : RotationSystem G) (C : G.ConnectedComponent)
    (hall : ∀ v : V, v ∈ C.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj] :
    (R.restrictComponent C).faceCount = R.faceCount := by
  let E := componentDartEquivOfForallMem C hall
  have hperm : E.permCongr (R.restrictComponent C).faceStep =
      R.faceStep := by
    apply Equiv.ext
    intro d
    rw [Equiv.permCongr_apply]
    change ((componentDartEquiv C
      ((R.restrictComponent C).faceStep (E.symm d))).1 : G.Dart) =
      R.faceStep d
    rw [R.componentDartEquiv_faceStep C]
    exact congrArg R.faceStep (E.apply_symm_apply d)
  change (R.restrictComponent C).faceStep.cycleFactorsFinset.card =
    R.faceStep.cycleFactorsFinset.card
  rw [← PermRestriction.card_cycleFactorsFinset_permCongr E
    (R.restrictComponent C).faceStep, hperm]

/-- Restriction to a component containing every vertex preserves the number
of edges. -/
theorem restrictComponent_card_edges_eq_of_forall_mem
    (C : G.ConnectedComponent) (hall : ∀ v : V, v ∈ C.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj] :
    C.toSimpleGraph.edgeFinset.card = G.edgeFinset.card := by
  have hcard := Fintype.card_congr
    (componentDartEquivOfForallMem C hall)
  rw [card_darts_eq_two_mul_card_edges,
    card_darts_eq_two_mul_card_edges] at hcard
  omega

/-- A spherical rotation remains spherical after restricting to a component
that contains every ambient vertex. -/
theorem restrictComponent_isSpherical_of_forall_mem
    (R : RotationSystem G) (hR : R.IsSpherical)
    (C : G.ConnectedComponent) (hall : ∀ v : V, v ∈ C.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj] :
    (R.restrictComponent C).IsSpherical := by
  have hvertices := Fintype.card_congr
    (componentVertexEquivOfForallMem C hall)
  have hedges := restrictComponent_card_edges_eq_of_forall_mem
    (G := G) C hall
  have hfaces := R.restrictComponent_faceCount_eq_of_forall_mem C hall
  unfold IsSpherical at hR ⊢
  omega

/-- In a preconnected graph every connected component contains every
vertex.  This form is convenient for transporting a rotation certificate to
the component graph used by `IsCombinatoriallyPlanar`. -/
theorem forall_mem_connectedComponent_of_preconnected
    (hG : G.Preconnected) (C : G.ConnectedComponent) :
    ∀ v : V, v ∈ C.supp := by
  obtain ⟨w, hw⟩ := C.nonempty_supp
  intro v
  rw [ConnectedComponent.mem_supp_iff] at hw ⊢
  exact (ConnectedComponent.sound (hG v w)).trans hw

/-- A spherical rotation on a preconnected graph supplies the spherical
certificate on its (unique) connected component. -/
theorem restrictComponent_isSpherical_of_preconnected
    (R : RotationSystem G) (hR : R.IsSpherical) (hG : G.Preconnected)
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj] :
    (R.restrictComponent C).IsSpherical :=
  R.restrictComponent_isSpherical_of_forall_mem hR C
    (forall_mem_connectedComponent_of_preconnected hG C)

/-- The component of an isolated vertex has exactly one vertex, no edge,
and every rotation system on it has no (nontrivial) facial cycle. -/
theorem isolatedComponent_rotation_data
    (v : V) (hv : G.IsIsolated v)
    [Fintype (G.connectedComponentMk v)]
    [DecidableEq (G.connectedComponentMk v)]
    [DecidableRel (G.connectedComponentMk v).toSimpleGraph.Adj]
    (S : RotationSystem (G.connectedComponentMk v).toSimpleGraph) :
    Fintype.card (G.connectedComponentMk v) = 1 ∧
      (G.connectedComponentMk v).toSimpleGraph.edgeFinset.card = 0 ∧
      S.faceCount = 0 := by
  letI : Unique (G.connectedComponentMk v) :=
    { default := ⟨v, ConnectedComponent.connectedComponentMk_mem⟩
      uniq := fun x ↦ by
        apply Subtype.ext
        by_contra hx
        have hreach : G.Reachable x.1 v := ConnectedComponent.exact x.2
        exact (not_reachable_of_neighborSet_right_eq_empty hx
          hv.neighborSet_eq_empty) hreach }
  have hvertices : Fintype.card (G.connectedComponentMk v) = 1 :=
    Fintype.card_unique
  haveI : Subsingleton
      (SimpleGraph (G.connectedComponentMk v)) :=
    SimpleGraph.subsingleton_iff.mpr inferInstance
  have hgraph : (G.connectedComponentMk v).toSimpleGraph = ⊥ :=
    Subsingleton.elim _ _
  have hedges :
      (G.connectedComponentMk v).toSimpleGraph.edgeFinset.card = 0 := by
    rw [Finset.card_eq_zero, SimpleGraph.edgeFinset_eq_empty]
    exact hgraph
  have hface := S.faceCount_le_card_edges
  rw [hedges] at hface
  exact ⟨hvertices, hedges, Nat.eq_zero_of_le_zero hface⟩

/-- If two connected components partition a rotation system whose total
Euler characteristic is four, each component attains the connected Euler
upper bound and is spherical. -/
theorem restrictComponents_isSpherical_of_eulerCharacteristic_eq_four
    (R : RotationSystem G) (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬v ∈ C.supp ↔ v ∈ D.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    [Fintype D] [DecidableEq D] [DecidableRel D.toSimpleGraph.Adj]
    (hchi : Fintype.card V + R.faceCount = G.edgeFinset.card + 4) :
    (R.restrictComponent C).IsSpherical ∧
      (R.restrictComponent D).IsSpherical := by
  have hvertices := card_vertices_eq_add_restrictComponents
    (G := G) C D hCD
  have hedges := card_edges_eq_add_restrictComponents
    (G := G) C D hCD
  have hfaces := R.faceCount_eq_add_restrictComponent_of_complement C D hCD
  have hEulerC := (R.restrictComponent C).eulerCharacteristic_le_two
    C.toSimpleGraph C.connected_toSimpleGraph
  have hEulerD := (R.restrictComponent D).eulerCharacteristic_le_two
    D.toSimpleGraph D.connected_toSimpleGraph
  constructor <;> unfold IsSpherical <;> omega

/-- If complementary components have total Euler characteristic three and
the first component is an isolated singleton (Euler characteristic one), the
second component is spherical. -/
theorem restrictComponent_right_isSpherical_of_eulerCharacteristic_eq_three
    (R : RotationSystem G) (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬v ∈ C.supp ↔ v ∈ D.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    [Fintype D] [DecidableEq D] [DecidableRel D.toSimpleGraph.Adj]
    (hchi : Fintype.card V + R.faceCount = G.edgeFinset.card + 3)
    (hCv : Fintype.card C = 1)
    (hCe : C.toSimpleGraph.edgeFinset.card = 0)
    (hCf : (R.restrictComponent C).faceCount = 0) :
    (R.restrictComponent D).IsSpherical := by
  have hvertices := card_vertices_eq_add_restrictComponents
    (G := G) C D hCD
  have hedges := card_edges_eq_add_restrictComponents
    (G := G) C D hCD
  have hfaces := R.faceCount_eq_add_restrictComponent_of_complement C D hCD
  unfold IsSpherical
  omega

/-- Symmetric form of the preceding isolated-component calculation. -/
theorem restrictComponent_left_isSpherical_of_eulerCharacteristic_eq_three
    (R : RotationSystem G) (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬v ∈ C.supp ↔ v ∈ D.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    [Fintype D] [DecidableEq D] [DecidableRel D.toSimpleGraph.Adj]
    (hchi : Fintype.card V + R.faceCount = G.edgeFinset.card + 3)
    (hDv : Fintype.card D = 1)
    (hDe : D.toSimpleGraph.edgeFinset.card = 0)
    (hDf : (R.restrictComponent D).faceCount = 0) :
    (R.restrictComponent C).IsSpherical := by
  have hvertices := card_vertices_eq_add_restrictComponents
    (G := G) C D hCD
  have hedges := card_edges_eq_add_restrictComponents
    (G := G) C D hCD
  have hfaces := R.faceCount_eq_add_restrictComponent_of_complement C D hCD
  unfold IsSpherical
  omega

/-- In a connected spherical rotation system, a non-bridge edge cannot have
both of its darts on the same face.  Otherwise deleting it would split that
face, while the graph remains connected, contradicting the Euler upper bound.
-/
theorem isTwoSidedDart_of_isSpherical_of_connected_of_not_isBridge
    (R : RotationSystem G) (hR : R.IsSpherical) (hG : G.Connected)
    (a : G.Dart) (hnot : ¬G.IsBridge a.edge) :
    R.IsTwoSidedDart a := by
  by_contra htwo
  have hsame : R.faceStep.SameCycle a a.symm := by
    rw [R.isTwoSidedDart_iff_not_sameCycle] at htwo
    exact not_not.mp htwo
  let H : SimpleGraph V := G.deleteEdges {a.edge}
  let R' : RotationSystem H := R.deleteEdge a.edge a rfl
  have hpre : H.Preconnected := by
    simpa only [H, Dart.edge] using
      (deleteEdge_preconnected_of_not_isBridge hG.preconnected
        (by simpa only [Dart.edge] using hnot))
  letI : Nontrivial V := ⟨⟨a.fst, a.snd, a.fst_ne_snd⟩⟩
  have hconn : H.Connected := ⟨hpre⟩
  have hfst : ¬H.IsIsolated a.fst := hpre.not_isIsolated a.fst
  have hsnd : ¬H.IsIsolated a.snd := hpre.not_isIsolated a.snd
  have hleft : R.faceStep a ≠ a.symm := by
    intro h
    exact hsnd ((R.faceStep_eq_symm_iff_deleteEdge_isIsolated_snd
      a.edge a rfl).mp h)
  have hright : R.faceStep a.symm ≠ a := by
    intro h
    exact hfst ((R.faceStep_symm_eq_iff_deleteEdge_isIsolated_fst
      a.edge a rfl).mp h)
  have hface : R'.faceCount = R.faceCount + 1 := by
    exact R.deleteEdge_faceCount_eq_add_one_of_sameCycle
      a.edge a rfl hsame hleft hright
  have heuler := R'.eulerCharacteristic_le_two H hconn
  have hedge := edgeFinset_deleteEdge_card_add_one (G := G) a.edge a rfl
  change H.edgeFinset.card + 1 = G.edgeFinset.card at hedge
  unfold IsSpherical at hR
  omega

/-- Deleting a non-bridge edge from a connected spherical rotation system
produces another connected spherical rotation system. -/
theorem deleteEdge_isSpherical_of_connected_of_not_isBridge
    (R : RotationSystem G) (hR : R.IsSpherical) (hG : G.Connected)
    (a : G.Dart) (hnot : ¬G.IsBridge a.edge) :
    (R.deleteEdge a.edge a rfl).IsSpherical := by
  exact R.deleteEdge_isSpherical_of_isTwoSidedDart a.edge a rfl hR
    (R.isTwoSidedDart_of_isSpherical_of_connected_of_not_isBridge
      hR hG a hnot)

/-- Deleting a non-bridge edge from a connected spherical rotation gives a
componentwise combinatorial-planarity certificate. -/
theorem deleteEdge_isCombinatoriallyPlanar_of_connected_of_not_isBridge
    (R : RotationSystem G) (hR : R.IsSpherical) (hG : G.Connected)
    (a : G.Dart) (hnot : ¬G.IsBridge a.edge) :
    IsCombinatoriallyPlanar (G.deleteEdges {a.edge}) := by
  let H : SimpleGraph V := G.deleteEdges {a.edge}
  let R' : RotationSystem H := R.deleteEdge a.edge a rfl
  have hR' : R'.IsSpherical :=
    R.deleteEdge_isSpherical_of_connected_of_not_isBridge hR hG a hnot
  have hpre : H.Preconnected := by
    simpa only [H, Dart.edge] using
      (deleteEdge_preconnected_of_not_isBridge hG.preconnected
        (by simpa only [Dart.edge] using hnot))
  intro C
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  intro _
  exact ⟨R'.restrictComponent C,
    R'.restrictComponent_isSpherical_of_preconnected hR' hpre C⟩

/-- Deleting a bridge from a connected spherical rotation system gives a
componentwise combinatorial-planarity certificate.  If neither new endpoint
is isolated, the two new components have total Euler characteristic four;
if one endpoint is isolated, its singleton component contributes one and the
other component contributes two. -/
theorem deleteEdge_isCombinatoriallyPlanar_of_connected_of_isBridge
    (R : RotationSystem G) (hR : R.IsSpherical) (hG : G.Connected)
    (a : G.Dart) (hbridge : G.IsBridge a.edge) :
    IsCombinatoriallyPlanar (G.deleteEdges {a.edge}) := by
  let H : SimpleGraph V := G.deleteEdges {a.edge}
  let R' : RotationSystem H := R.deleteEdge a.edge a rfl
  let C₁ : H.ConnectedComponent := H.connectedComponentMk a.fst
  let C₂ : H.ConnectedComponent := H.connectedComponentMk a.snd
  letI : Fintype C₁ := Fintype.ofFinite C₁
  letI : DecidableEq C₁ := Classical.decEq C₁
  letI : DecidableRel C₁.toSimpleGraph.Adj := Classical.decRel _
  letI : Fintype C₂ := Fintype.ofFinite C₂
  letI : DecidableEq C₂ := Classical.decEq C₂
  letI : DecidableRel C₂.toSimpleGraph.Adj := Classical.decRel _
  have hpart : ∀ v : V, ¬v ∈ C₁.supp ↔ v ∈ C₂.supp := by
    intro v
    simpa only [C₁, C₂, H, Dart.edge] using
      (not_mem_deleteEdge_fstComponent_iff_mem_sndComponent
        hG.preconnected (by simpa only [Dart.edge] using hbridge) (x := v))
  have hedge := edgeFinset_deleteEdge_card_add_one (G := G) a.edge a rfl
  change H.edgeFinset.card + 1 = G.edgeFinset.card at hedge
  intro C
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  intro hCedge
  have hcases : C = C₁ ∨ C = C₂ := by
    obtain ⟨v, hvC⟩ := C.nonempty_supp
    by_cases hv₁ : v ∈ C₁.supp
    · exact Or.inl (ConnectedComponent.eq_of_common_vertex hvC hv₁)
    · exact Or.inr (ConnectedComponent.eq_of_common_vertex hvC
        ((hpart v).mp hv₁))
  rcases hcases with rfl | rfl
  · refine ⟨R'.restrictComponent C₁, ?_⟩
    have hfst : ¬H.IsIsolated a.fst := by
      intro hiso
      have hdata := isolatedComponent_rotation_data (G := H) a.fst hiso
        (R'.restrictComponent C₁)
      have hnonempty : C₁.toSimpleGraph.edgeFinset.Nonempty := by
        obtain ⟨e, he⟩ := hCedge
        exact ⟨e, by simpa only [SimpleGraph.mem_edgeFinset] using he⟩
      exact (Finset.card_ne_zero.mpr hnonempty) hdata.2.1
    by_cases hsnd : H.IsIsolated a.snd
    · have hface : R'.faceCount = R.faceCount := by
        exact R.deleteEdge_faceCount_eq_of_isBridge_of_snd_isolated
          a.edge a rfl hbridge hfst hsnd
      have hchi : Fintype.card V + R'.faceCount =
          H.edgeFinset.card + 3 := by
        unfold IsSpherical at hR
        omega
      have hdata := isolatedComponent_rotation_data (G := H) a.snd hsnd
        (R'.restrictComponent C₂)
      exact R'.restrictComponent_left_isSpherical_of_eulerCharacteristic_eq_three
        C₁ C₂ hpart hchi hdata.1 hdata.2.1 hdata.2.2
    · have hface : R'.faceCount = R.faceCount + 1 := by
        exact R.deleteEdge_faceCount_eq_add_one_of_isBridge_of_endpoints_nonisolated
          a.edge a rfl hbridge hfst hsnd
      have hchi : Fintype.card V + R'.faceCount =
          H.edgeFinset.card + 4 := by
        unfold IsSpherical at hR
        omega
      exact (R'.restrictComponents_isSpherical_of_eulerCharacteristic_eq_four
        C₁ C₂ hpart hchi).1
  · refine ⟨R'.restrictComponent C₂, ?_⟩
    have hsnd : ¬H.IsIsolated a.snd := by
      intro hiso
      have hdata := isolatedComponent_rotation_data (G := H) a.snd hiso
        (R'.restrictComponent C₂)
      have hnonempty : C₂.toSimpleGraph.edgeFinset.Nonempty := by
        obtain ⟨e, he⟩ := hCedge
        exact ⟨e, by simpa only [SimpleGraph.mem_edgeFinset] using he⟩
      exact (Finset.card_ne_zero.mpr hnonempty) hdata.2.1
    by_cases hfst : H.IsIsolated a.fst
    · have hface : R'.faceCount = R.faceCount := by
        exact R.deleteEdge_faceCount_eq_of_isBridge_of_fst_isolated
          a.edge a rfl hbridge hfst hsnd
      have hchi : Fintype.card V + R'.faceCount =
          H.edgeFinset.card + 3 := by
        unfold IsSpherical at hR
        omega
      have hdata := isolatedComponent_rotation_data (G := H) a.fst hfst
        (R'.restrictComponent C₁)
      exact R'.restrictComponent_right_isSpherical_of_eulerCharacteristic_eq_three
        C₁ C₂ hpart hchi hdata.1 hdata.2.1 hdata.2.2
    · have hface : R'.faceCount = R.faceCount + 1 := by
        exact R.deleteEdge_faceCount_eq_add_one_of_isBridge_of_endpoints_nonisolated
          a.edge a rfl hbridge hfst hsnd
      have hchi : Fintype.card V + R'.faceCount =
          H.edgeFinset.card + 4 := by
        unfold IsSpherical at hR
        omega
      exact (R'.restrictComponents_isSpherical_of_eulerCharacteristic_eq_four
        C₁ C₂ hpart hchi).2

/-- Every single-edge deletion from a connected spherical rotation system
is combinatorially planar, with bridges and non-bridges handled uniformly. -/
theorem deleteEdge_isCombinatoriallyPlanar_of_connected
    (R : RotationSystem G) (hR : R.IsSpherical) (hG : G.Connected)
    (a : G.Dart) : IsCombinatoriallyPlanar (G.deleteEdges {a.edge}) := by
  by_cases hbridge : G.IsBridge a.edge
  · exact R.deleteEdge_isCombinatoriallyPlanar_of_connected_of_isBridge
      hR hG a hbridge
  · exact R.deleteEdge_isCombinatoriallyPlanar_of_connected_of_not_isBridge
      hR hG a hbridge

end Finite

end RotationSystem

end


end LeanCo.PackingEdgeColoring
