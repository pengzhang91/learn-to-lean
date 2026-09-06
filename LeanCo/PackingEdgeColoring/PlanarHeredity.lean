import LeanCo.PackingEdgeColoring.PlanarDeletion

/-!
# Combinatorial planarity is hereditary

The first part of this file transports rotation systems along graph
isomorphisms.  The second part uses that transport together with the
single-edge deletion theorem to prove graph-level deletion heredity.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

namespace IsoTransport

/-- A graph isomorphism induces an equivalence of oriented darts. -/
def dartEquivOfIso (φ : G ≃g H) : G.Dart ≃ H.Dart where
  toFun d := φ.toHom.mapDart d
  invFun d := φ.symm.toHom.mapDart d
  left_inv d := by
    apply Dart.ext
    apply Prod.ext
    · exact φ.symm_apply_apply d.fst
    · exact φ.symm_apply_apply d.snd
  right_inv d := by
    apply Dart.ext
    apply Prod.ext
    · exact φ.apply_symm_apply d.fst
    · exact φ.apply_symm_apply d.snd

@[simp]
theorem dartEquivOfIso_apply_fst (φ : G ≃g H) (d : G.Dart) :
    (dartEquivOfIso φ d).fst = φ d.fst := rfl

@[simp]
theorem dartEquivOfIso_apply_snd (φ : G ≃g H) (d : G.Dart) :
    (dartEquivOfIso φ d).snd = φ d.snd := rfl

@[simp]
theorem dartEquivOfIso_apply_symm (φ : G ≃g H) (d : G.Dart) :
    dartEquivOfIso φ d.symm = (dartEquivOfIso φ d).symm := rfl

@[simp]
theorem dartEquivOfIso_symm_apply_fst (φ : G ≃g H) (d : H.Dart) :
    ((dartEquivOfIso φ).symm d).fst = φ.symm d.fst := rfl

@[simp]
theorem dartEquivOfIso_symm_apply_symm (φ : G ≃g H) (d : H.Dart) :
    (dartEquivOfIso φ).symm d.symm =
      ((dartEquivOfIso φ).symm d).symm := rfl

end IsoTransport

namespace ComponentEmbedding

variable {A B : Type*} {L : SimpleGraph A} {M : SimpleGraph B}

/-- For an embedding whose vertex range is closed under ambient adjacency,
every vertex reachable from an image vertex has a reachable preimage. -/
theorem exists_preimage_reachable_of_closed
    (φ : L ↪g M)
    (hclosed : ∀ (x : A) (y : B), M.Adj (φ x) y →
      ∃ z : A, φ z = y)
    {x : A} {y : B} (hxy : M.Reachable (φ x) y) :
    ∃ z : A, L.Reachable x z ∧ φ z = y := by
  rw [reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact ⟨x, SimpleGraph.Reachable.refl x, rfl⟩
  | @tail b c hab hbc ih =>
      obtain ⟨z, hxz, hzb⟩ := ih
      have hzc : M.Adj (φ z) c := by simpa only [hzb] using hbc
      obtain ⟨z', hz'⟩ := hclosed z c hzc
      have hzz' : L.Adj z z' := φ.map_rel_iff.mp (by simpa only [hz'] using hzc)
      exact ⟨z', hxz.trans hzz'.reachable, hz'⟩

/-- Existence of a preimage in the correct domain component. -/
theorem exists_componentPreimage
    (φ : L ↪g M)
    (hclosed : ∀ (x : A) (y : B), M.Adj (φ x) y →
      ∃ z : A, φ z = y)
    (K : L.ConnectedComponent)
    (y : K.map φ.toHom) :
    ∃ z : A, L.connectedComponentMk z = K ∧ φ z = y.1 := by
  let x₀ : A := K.out
  have hx₀ : L.connectedComponentMk x₀ = K := K.out_eq
  have hmapx₀ : M.connectedComponentMk (φ.toHom x₀) =
      K.map φ.toHom := by
    simpa only [x₀, ConnectedComponent.map_mk] using
      congrArg (fun Q : L.ConnectedComponent ↦ Q.map φ.toHom) hx₀
  have hreach : M.Reachable (φ.toHom x₀) y.1 :=
    ConnectedComponent.exact (hmapx₀.trans y.2.symm)
  obtain ⟨z, hxz, hzy⟩ := exists_preimage_reachable_of_closed
    φ hclosed hreach
  exact ⟨z, (ConnectedComponent.sound hxz).symm.trans hx₀, hzy⟩

/-- A chosen preimage, in the same domain component, of a vertex in the
mapped ambient component. -/
noncomputable def componentPreimage
    (φ : L ↪g M)
    (hclosed : ∀ (x : A) (y : B), M.Adj (φ x) y →
      ∃ z : A, φ z = y)
    (K : L.ConnectedComponent)
    (y : K.map φ.toHom) : K :=
  ⟨Classical.choose (exists_componentPreimage φ hclosed K y),
    (Classical.choose_spec
      (exists_componentPreimage φ hclosed K y)).1⟩

@[simp]
theorem componentPreimage_apply
    (φ : L ↪g M)
    (hclosed : ∀ (x : A) (y : B), M.Adj (φ x) y →
      ∃ z : A, φ z = y)
    (K : L.ConnectedComponent) (y : K.map φ.toHom) :
    φ (componentPreimage φ hclosed K y).1 = y.1 := by
  exact (Classical.choose_spec
    (exists_componentPreimage φ hclosed K y)).2

/-- A closed graph embedding restricts to an isomorphism between every
domain component and its mapped ambient component. -/
noncomputable def componentGraphIso
    (φ : L ↪g M)
    (hclosed : ∀ (x : A) (y : B), M.Adj (φ x) y →
      ∃ z : A, φ z = y)
    (K : L.ConnectedComponent) :
    K.toSimpleGraph ≃g (K.map φ.toHom).toSimpleGraph where
  toFun x := ⟨φ x.1, by
    have hx := congrArg (fun Q : L.ConnectedComponent ↦ Q.map φ.toHom) x.2
    change M.connectedComponentMk (φ.toHom x.1) = K.map φ.toHom
    simpa only [ConnectedComponent.map_mk] using hx⟩
  invFun := componentPreimage φ hclosed K
  left_inv x := by
    apply Subtype.ext
    apply φ.injective
    exact componentPreimage_apply φ hclosed K _
  right_inv y := by
    apply Subtype.ext
    exact componentPreimage_apply φ hclosed K y
  map_rel_iff' := by
    intro x y
    change M.Adj (φ x.1) (φ y.1) ↔ L.Adj x.1 y.1
    exact φ.map_rel_iff

end ComponentEmbedding

namespace ComponentDeletion

variable {A : Type*} {Q : SimpleGraph A}

/-- A vertex of a component of a spanning subgraph lies in the corresponding
ambient component. -/
def vertexInMappedComponent {Q' : SimpleGraph A} (h : Q' ≤ Q)
    (C : Q'.ConnectedComponent) (x : C) :
    C.map (SimpleGraph.Hom.ofLE h) :=
  ⟨x.1, by
    have hx := congrArg
      (fun K : Q'.ConnectedComponent ↦
        K.map (SimpleGraph.Hom.ofLE h)) x.2
    change Q.connectedComponentMk x.1 =
      C.map (SimpleGraph.Hom.ofLE h)
    change Q.connectedComponentMk x.1 =
      C.map (SimpleGraph.Hom.ofLE h) at hx
    exact hx⟩

/-- Component inclusion along a graph inequality, as a graph homomorphism. -/
def componentHomOfLE {Q' : SimpleGraph A} (h : Q' ≤ Q)
    (C : Q'.ConnectedComponent) :
    C.toSimpleGraph →g
      (C.map (SimpleGraph.Hom.ofLE h)).toSimpleGraph where
  toFun := vertexInMappedComponent h C
  map_rel' := by
    intro x y hxy
    exact h hxy

/-- An edgeful component of a spanning subgraph maps to an edgeful ambient
component. -/
theorem mappedComponent_edgeSet_nonempty {Q' : SimpleGraph A} (h : Q' ≤ Q)
    (C : Q'.ConnectedComponent) (hC : C.toSimpleGraph.edgeSet.Nonempty) :
    (C.map (SimpleGraph.Hom.ofLE h)).toSimpleGraph.edgeSet.Nonempty := by
  obtain ⟨e, he⟩ := hC
  let ee : C.toSimpleGraph.edgeSet := ⟨e, he⟩
  let ee' := (componentHomOfLE h C).mapEdgeSet ee
  exact ⟨ee'.1, ee'.2⟩

/-- Regard an ambient dart as a dart in the induced graph of the component
containing its first vertex. -/
def dartInComponent (D : Q.ConnectedComponent) (a : Q.Dart)
    (ha : a.fst ∈ D.supp) : D.toSimpleGraph.Dart :=
  (RotationSystem.componentDartEquiv D).symm ⟨a, ha⟩

@[simp]
theorem componentDartEquiv_dartInComponent
    (D : Q.ConnectedComponent) (a : Q.Dart) (ha : a.fst ∈ D.supp) :
    ((RotationSystem.componentDartEquiv D (dartInComponent D a ha)).1 :
      Q.Dart) = a := by
  exact congrArg Subtype.val
    ((RotationSystem.componentDartEquiv D).apply_symm_apply ⟨a, ha⟩)

theorem map_edge_dartInComponent
    (D : Q.ConnectedComponent) (a : Q.Dart) (ha : a.fst ∈ D.supp) :
    Sym2.map (fun x : D ↦ x.1) (dartInComponent D a ha).edge = a.edge := by
  have h := congrArg Dart.edge
    (componentDartEquiv_dartInComponent D a ha)
  simpa only [Dart.edge, Sym2.map_mk,
    RotationSystem.componentDartEquiv_apply_fst,
    RotationSystem.componentDartEquiv_apply_snd] using h

/-- The deletion inside one original component embeds into the ambient edge
deletion. -/
def deleteEdgeEmbedding (D : Q.ConnectedComponent) (a : Q.Dart)
    (ha : a.fst ∈ D.supp) :
    (D.toSimpleGraph.deleteEdges {(dartInComponent D a ha).edge}) ↪g
      (Q.deleteEdges {a.edge}) where
  toFun x := x.1
  inj' := Subtype.val_injective
  map_rel_iff' := by
    intro x y
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    change (Q.Adj x.1 y.1 ∧ s(x.1, y.1) ≠ a.edge) ↔
      (Q.Adj x.1 y.1 ∧ s(x, y) ≠ (dartInComponent D a ha).edge)
    have hinj : Function.Injective (Sym2.map (fun z : D ↦ z.1)) :=
      Sym2.map.injective Subtype.val_injective
    have heq : s(x.1, y.1) = a.edge ↔
        s(x, y) = (dartInComponent D a ha).edge := by
      constructor
      · intro h
        apply hinj
        change s(x.1, y.1) =
          Sym2.map (fun z : D ↦ z.1) (dartInComponent D a ha).edge
        rw [map_edge_dartInComponent D a ha]
        exact h
      · intro h
        calc
          s(x.1, y.1) = Sym2.map (fun z : D ↦ z.1) s(x, y) := rfl
          _ = Sym2.map (fun z : D ↦ z.1)
              (dartInComponent D a ha).edge := congrArg _ h
          _ = a.edge := map_edge_dartInComponent D a ha
    exact and_congr Iff.rfl (not_congr heq)

/-- The image of `deleteEdgeEmbedding` is closed under adjacency in the
ambient deleted graph. -/
theorem deleteEdgeEmbedding_closed
    (D : Q.ConnectedComponent) (a : Q.Dart)
    (ha : a.fst ∈ D.supp) :
    ∀ (x : D) (y : A),
      (Q.deleteEdges {a.edge}).Adj (deleteEdgeEmbedding D a ha x) y →
        ∃ z : D, deleteEdgeEmbedding D a ha z = y := by
  intro x y hxy
  have hQ : Q.Adj x.1 y := (SimpleGraph.deleteEdges_adj.mp hxy).1
  have hy : y ∈ D.supp := D.mem_supp_of_adj_mem_supp x.2 hQ
  exact ⟨⟨y, hy⟩, rfl⟩

/-- If the deleted edge lies outside a component, that unchanged component
embeds into the ambient deleted graph. -/
def outsideEdgeEmbedding (D : Q.ConnectedComponent) (a : Q.Dart)
    (hout : a.fst ∉ D.supp) :
    D.toSimpleGraph ↪g (Q.deleteEdges {a.edge}) where
  toFun x := x.1
  inj' := Subtype.val_injective
  map_rel_iff' := by
    intro x y
    change (Q.deleteEdges {a.edge}).Adj x.1 y.1 ↔ Q.Adj x.1 y.1
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · exact And.left
    · intro hxy
      refine ⟨hxy, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hedge
      rw [Dart.edge, Sym2.eq_iff] at hedge
      rcases hedge with h | h
      · exact hout (h.1 ▸ x.2)
      · exact hout (h.2 ▸ y.2)

/-- The image of an unchanged outside component is closed under adjacency
after deletion. -/
theorem outsideEdgeEmbedding_closed
    (D : Q.ConnectedComponent) (a : Q.Dart)
    (hout : a.fst ∉ D.supp) :
    ∀ (x : D) (y : A),
      (Q.deleteEdges {a.edge}).Adj (outsideEdgeEmbedding D a hout x) y →
        ∃ z : D, outsideEdgeEmbedding D a hout z = y := by
  intro x y hxy
  have hQ : Q.Adj x.1 y := (SimpleGraph.deleteEdges_adj.mp hxy).1
  have hy : y ∈ D.supp := D.mem_supp_of_adj_mem_supp x.2 hQ
  exact ⟨⟨y, hy⟩, rfl⟩

end ComponentDeletion

namespace RotationSystem

open IsoTransport

/-- Transport a rotation system along a graph isomorphism. -/
def transportIso (R : RotationSystem G) (φ : G ≃g H) :
    RotationSystem H where
  rotation := (dartEquivOfIso φ).permCongr R.rotation
  rotation_fst d := by
    rw [Equiv.permCongr_apply]
    calc
      (dartEquivOfIso φ
          (R.rotation ((dartEquivOfIso φ).symm d))).fst =
          φ (R.rotation ((dartEquivOfIso φ).symm d)).fst := rfl
      _ = φ ((dartEquivOfIso φ).symm d).fst :=
        congrArg φ (R.rotation_fst ((dartEquivOfIso φ).symm d))
      _ = d.fst := by
        have hd := congrArg (fun z : H.Dart ↦ z.fst)
          ((dartEquivOfIso φ).apply_symm_apply d)
        exact hd
  rotation_transitive d e hde := by
    let d' : G.Dart := (dartEquivOfIso φ).symm d
    let e' : G.Dart := (dartEquivOfIso φ).symm e
    have hd : φ d'.fst = d.fst := by
      have := congrArg (fun z : H.Dart ↦ z.fst)
        ((dartEquivOfIso φ).apply_symm_apply d)
      exact this
    have he : φ e'.fst = e.fst := by
      have := congrArg (fun z : H.Dart ↦ z.fst)
        ((dartEquivOfIso φ).apply_symm_apply e)
      exact this
    have hde' : d'.fst = e'.fst := by
      apply φ.injective
      exact hd.trans (hde.trans he.symm)
    obtain ⟨n, hn⟩ := R.rotation_transitive d' e' hde'
    refine ⟨n, ?_⟩
    have hp := (dartEquivOfIso φ).permCongrHom.toMonoidHom.map_zpow
      R.rotation n
    change (((dartEquivOfIso φ).permCongrHom.toMonoidHom R.rotation) ^ n) d = e
    rw [← hp]
    change ((dartEquivOfIso φ).permCongr (R.rotation ^ n)) d = e
    rw [Equiv.permCongr_apply, hn]
    exact (dartEquivOfIso φ).apply_symm_apply e

/-- The transported vertex rotation is conjugate to the original global
rotation. -/
theorem transportIso_rotation (R : RotationSystem G) (φ : G ≃g H) :
    (R.transportIso φ).rotation =
      (dartEquivOfIso φ).permCongr R.rotation := rfl

/-- Dart reversal commutes with the dart equivalence of a graph
isomorphism. -/
theorem transportIso_faceStep (R : RotationSystem G) (φ : G ≃g H) :
    (R.transportIso φ).faceStep =
      (dartEquivOfIso φ).permCongr R.faceStep := by
  apply Equiv.ext
  intro d
  rw [Equiv.permCongr_apply]
  change dartEquivOfIso φ
      (R.rotation ((dartEquivOfIso φ).symm d).symm) =
    dartEquivOfIso φ
      (R.rotation ((dartEquivOfIso φ).symm d.symm))
  rw [dartEquivOfIso_symm_apply_symm]

/-- Isomorphic finite graphs have the same number of edges, proved through
their dart equivalence. -/
theorem card_edges_eq_of_iso [Fintype V] [Fintype W]
    [DecidableRel G.Adj] [DecidableRel H.Adj] (φ : G ≃g H) :
    G.edgeFinset.card = H.edgeFinset.card := by
  have hcard := Fintype.card_congr (dartEquivOfIso φ)
  rw [card_darts_eq_two_mul_card_edges,
    card_darts_eq_two_mul_card_edges] at hcard
  omega

/-- Transport along an isomorphism preserves the facial cycle count. -/
theorem transportIso_faceCount [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (R : RotationSystem G) (φ : G ≃g H) :
    (R.transportIso φ).faceCount = R.faceCount := by
  change (R.transportIso φ).faceStep.cycleFactorsFinset.card =
    R.faceStep.cycleFactorsFinset.card
  rw [R.transportIso_faceStep φ,
    PermRestriction.card_cycleFactorsFinset_permCongr]

/-- Sphericality is invariant under graph isomorphism. -/
theorem transportIso_isSpherical [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (R : RotationSystem G) (φ : G ≃g H) (hR : R.IsSpherical) :
    (R.transportIso φ).IsSpherical := by
  have hvertices := φ.card_eq
  have hedges := card_edges_eq_of_iso φ
  have hfaces := R.transportIso_faceCount φ
  unfold IsSpherical at hR ⊢
  omega

/-- A spherical-rotation certificate transports across graph
isomorphisms. -/
theorem hasSphericalRotation_iff_iso [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (φ : G ≃g H) : HasSphericalRotation G ↔ HasSphericalRotation H := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R.transportIso φ, R.transportIso_isSpherical φ hR⟩
  · rintro ⟨R, hR⟩
    exact ⟨R.transportIso φ.symm, R.transportIso_isSpherical φ.symm hR⟩

end RotationSystem

section FiniteHeredity

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Graph-level single-edge deletion heredity.  The proof works component by
component: the affected ambient component uses the connected deletion
theorem, while every other component is transported unchanged. -/
theorem IsCombinatoriallyPlanar.deleteEdgeOfDart
    (hplan : IsCombinatoriallyPlanar G) (a : G.Dart) :
    IsCombinatoriallyPlanar (G.deleteEdges {a.edge}) := by
  let Q : SimpleGraph V := G.deleteEdges {a.edge}
  letI : DecidableRel Q.Adj := Classical.decRel _
  have hQG : Q ≤ G := by
    simpa only [Q] using G.deleteEdges_le ({a.edge} : Set (Sym2 V))
  intro C
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  intro hCedge
  let D : G.ConnectedComponent :=
    C.map (SimpleGraph.Hom.ofLE hQG)
  letI : Fintype D := Fintype.ofFinite D
  letI : DecidableEq D := Classical.decEq D
  letI : DecidableRel D.toSimpleGraph.Adj := Classical.decRel _
  have hDedge : D.toSimpleGraph.edgeSet.Nonempty := by
    exact ComponentDeletion.mappedComponent_edgeSet_nonempty hQG C hCedge
  have hDcert : HasSphericalRotation D.toSimpleGraph := by
    simpa only [D] using hplan D hDedge
  obtain ⟨RD, hRD⟩ := hDcert
  obtain ⟨v, hvC⟩ := C.nonempty_supp
  let vC : C := ⟨v, hvC⟩
  let vD : D := ComponentDeletion.vertexInMappedComponent hQG C vC
  by_cases haD : a.fst ∈ D.supp
  · let aD : D.toSimpleGraph.Dart :=
      ComponentDeletion.dartInComponent D a haD
    let L : SimpleGraph D := D.toSimpleGraph.deleteEdges {aD.edge}
    let emb : L ↪g Q := ComponentDeletion.deleteEdgeEmbedding D a haD
    have hembClosed : ∀ (x : D) (y : V), Q.Adj (emb x) y →
        ∃ z : D, emb z = y := by
      simpa only [emb, L, Q, aD] using
        ComponentDeletion.deleteEdgeEmbedding_closed D a haD
    let K : L.ConnectedComponent := L.connectedComponentMk vD
    have hmap : K.map emb.toHom = C := by
      calc
        K.map emb.toHom = Q.connectedComponentMk (emb.toHom vD) := by
          simp only [K, ConnectedComponent.map_mk]
        _ = Q.connectedComponentMk v := rfl
        _ = C := hvC
    letI : Fintype K := Fintype.ofFinite K
    letI : DecidableEq K := Classical.decEq K
    letI : DecidableRel K.toSimpleGraph.Adj := Classical.decRel _
    letI : Fintype (K.map emb.toHom) := Fintype.ofFinite _
    letI : DecidableEq (K.map emb.toHom) := Classical.decEq _
    letI : DecidableRel (K.map emb.toHom).toSimpleGraph.Adj :=
      Classical.decRel _
    let κ : K.toSimpleGraph ≃g (K.map emb.toHom).toSimpleGraph :=
      ComponentEmbedding.componentGraphIso emb hembClosed K
    have htargetEdge :
        (K.map emb.toHom).toSimpleGraph.edgeSet.Nonempty := by
      rw [hmap]
      exact hCedge
    have hKedge : K.toSimpleGraph.edgeSet.Nonempty := by
      obtain ⟨e, he⟩ := htargetEdge
      let ee : (K.map emb.toHom).toSimpleGraph.edgeSet := ⟨e, he⟩
      let eeK := κ.mapEdgeSet.symm ee
      exact ⟨eeK.1, eeK.2⟩
    have hlocal : IsCombinatoriallyPlanar L := by
      simpa only [L, aD] using
        RD.deleteEdge_isCombinatoriallyPlanar_of_connected
          hRD D.connected_toSimpleGraph aD
    have hKcert : HasSphericalRotation K.toSimpleGraph := by
      simpa only [K] using hlocal K hKedge
    have htargetCert :
        HasSphericalRotation (K.map emb.toHom).toSimpleGraph :=
      (RotationSystem.hasSphericalRotation_iff_iso κ).mp hKcert
    exact hmap ▸ htargetCert
  · let emb : D.toSimpleGraph ↪g Q :=
      ComponentDeletion.outsideEdgeEmbedding D a haD
    have hembClosed : ∀ (x : D) (y : V), Q.Adj (emb x) y →
        ∃ z : D, emb z = y := by
      simpa only [emb, Q] using
        ComponentDeletion.outsideEdgeEmbedding_closed D a haD
    let K : D.toSimpleGraph.ConnectedComponent :=
      D.toSimpleGraph.connectedComponentMk vD
    have hmap : K.map emb.toHom = C := by
      calc
        K.map emb.toHom = Q.connectedComponentMk (emb.toHom vD) := by
          simp only [K, ConnectedComponent.map_mk]
        _ = Q.connectedComponentMk v := rfl
        _ = C := hvC
    letI : Fintype K := Fintype.ofFinite K
    letI : DecidableEq K := Classical.decEq K
    letI : DecidableRel K.toSimpleGraph.Adj := Classical.decRel _
    letI : Fintype (K.map emb.toHom) := Fintype.ofFinite _
    letI : DecidableEq (K.map emb.toHom) := Classical.decEq _
    letI : DecidableRel (K.map emb.toHom).toSimpleGraph.Adj :=
      Classical.decRel _
    let κ : K.toSimpleGraph ≃g (K.map emb.toHom).toSimpleGraph :=
      ComponentEmbedding.componentGraphIso emb hembClosed K
    have hKcert : HasSphericalRotation K.toSimpleGraph :=
      ⟨RD.restrictComponent K,
        RD.restrictComponent_isSpherical_of_preconnected hRD
          D.connected_toSimpleGraph.preconnected K⟩
    have htargetCert :
        HasSphericalRotation (K.map emb.toHom).toSimpleGraph :=
      (RotationSystem.hasSphericalRotation_iff_iso κ).mp hKcert
    exact hmap ▸ htargetCert

/-- Combinatorial planarity is preserved by deleting a finite set of edges.
Edges in the deletion set that are not present are skipped; each present edge
is represented by a dart and handled by `deleteEdgeOfDart`. -/
theorem IsCombinatoriallyPlanar.deleteEdgesFinset
    (hplan : IsCombinatoriallyPlanar G) (s : Finset (Sym2 V)) :
    IsCombinatoriallyPlanar (G.deleteEdges s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.coe_empty, SimpleGraph.deleteEdges_empty] using hplan
  | @insert e s hes ih =>
      let Q : SimpleGraph V := G.deleteEdges s
      letI : DecidableRel Q.Adj := Classical.decRel _
      have hseq : Q.deleteEdges {e} = G.deleteEdges (↑(insert e s) :
          Set (Sym2 V)) := by
        ext u v
        simp only [Q, SimpleGraph.deleteEdges_adj,
          Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_insert]
        tauto
      by_cases heQ : e ∈ Q.edgeSet
      · obtain ⟨a, ha⟩ :=
          RotationSystem.exists_dart_edge_eq_of_mem_edgeSet (G := Q) e heQ
        have hdel := ih.deleteEdgeOfDart a
        rw [ha, hseq] at hdel
        exact hdel
      · have hskip : Q.deleteEdges {e} = Q := by
          ext u v
          simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
          constructor
          · exact And.left
          · intro huv
            refine ⟨huv, ?_⟩
            intro hedge
            apply heQ
            rw [← hedge, SimpleGraph.mem_edgeSet]
            exact huv
        rw [← hseq, hskip]
        exact ih

/-- Combinatorial planarity is hereditary for arbitrary spanning subgraphs
on the same finite vertex type. -/
theorem IsCombinatoriallyPlanar.mono
    (hplan : IsCombinatoriallyPlanar G) {G' : SimpleGraph V}
    (hG'G : G' ≤ G) : IsCombinatoriallyPlanar G' := by
  classical
  let s : Finset (Sym2 V) := G.edgeFinset \ G'.edgeFinset
  have hs : (↑s : Set (Sym2 V)) = G.edgeSet \ G'.edgeSet := by
    ext e
    simp only [s, Finset.mem_coe, Finset.mem_sdiff,
      SimpleGraph.mem_edgeFinset, Set.mem_diff]
  have hdel : G.deleteEdges (↑s : Set (Sym2 V)) = G' := by
    rw [hs]
    exact SimpleGraph.deleteEdges_sdiff_eq_of_le hG'G
  have hp := hplan.deleteEdgesFinset s
  exact hdel ▸ hp

end FiniteHeredity

section ClosedEmbeddingHeredity

variable {A B : Type*} {L : SimpleGraph A} {M : SimpleGraph B}
variable [Fintype A] [DecidableEq A] [DecidableRel L.Adj]
variable [Fintype B] [DecidableEq B] [DecidableRel M.Adj]

/-- Planarity pulls back along a graph embedding whose image is closed under
ambient adjacency.  Such an embedding is a union of connected components,
and `componentGraphIso` identifies the corresponding component graphs. -/
theorem IsCombinatoriallyPlanar.ofClosedEmbedding
    (hplan : IsCombinatoriallyPlanar M) (φ : L ↪g M)
    (hclosed : ∀ (x : A) (y : B), M.Adj (φ x) y →
      ∃ z : A, φ z = y) : IsCombinatoriallyPlanar L := by
  intro K
  letI : Fintype K := Fintype.ofFinite K
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableRel K.toSimpleGraph.Adj := Classical.decRel _
  intro hKedge
  let C : M.ConnectedComponent := K.map φ.toHom
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let κ : K.toSimpleGraph ≃g C.toSimpleGraph :=
    ComponentEmbedding.componentGraphIso φ hclosed K
  have hCedge : C.toSimpleGraph.edgeSet.Nonempty := by
    obtain ⟨e, he⟩ := hKedge
    let ee : K.toSimpleGraph.edgeSet := ⟨e, he⟩
    let eeC := κ.mapEdgeSet ee
    exact ⟨eeC.1, eeC.2⟩
  have hCcert : HasSphericalRotation C.toSimpleGraph := by
    simpa only [C] using hplan C hCedge
  exact (RotationSystem.hasSphericalRotation_iff_iso κ).mpr hCcert

end ClosedEmbeddingHeredity

section InducedHeredity

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Combinatorial planarity is hereditary under induced subgraphs, including
when the induced graph has a different (subtype) vertex type. -/
theorem IsCombinatoriallyPlanar.induce
    (hplan : IsCombinatoriallyPlanar G) (s : Set V) [Fintype s] :
    IsCombinatoriallyPlanar (G.induce s) := by
  classical
  let L : SimpleGraph s := G.induce s
  let P : SimpleGraph V := L.spanningCoe
  letI : DecidableEq s := Classical.decEq s
  letI : DecidableRel L.Adj := Classical.decRel _
  letI : DecidableRel P.Adj := Classical.decRel _
  have hP : IsCombinatoriallyPlanar P := by
    apply hplan.mono
    simpa only [P, L] using G.spanningCoe_induce_le s
  let emb : L ↪g P := SimpleGraph.Embedding.spanningCoe L
  have hclosed : ∀ (x : s) (y : V), P.Adj (emb x) y →
      ∃ z : s, emb z = y := by
    intro x y hxy
    change L.spanningCoe.Adj x.1 y at hxy
    rw [SimpleGraph.map_adj] at hxy
    obtain ⟨u, v, huv, hu, hv⟩ := hxy
    exact ⟨v, hv⟩
  exact IsCombinatoriallyPlanar.ofClosedEmbedding hP emb hclosed

end InducedHeredity

end


end LeanCo.PackingEdgeColoring
