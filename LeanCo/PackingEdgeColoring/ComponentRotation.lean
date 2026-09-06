import LeanCo.PackingEdgeColoring.BridgeFaceSurgery

/-!
# Restricting a rotation system to a connected component

The induced graph on a connected component contains every edge incident with
one of its vertices.  Consequently each local outgoing-dart fibre is
canonically equivalent to the corresponding fibre in the ambient graph, and
a rotation system restricts without any further edge surgery.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

namespace PermRestriction

variable {alpha : Type*}

/-- If a finite permutation preserves a decidable predicate, its nontrivial
cycle count is the sum of the cycle counts on that predicate and its
complement.  This is the cycle-count bookkeeping needed to split facial
orbits over graph components. -/
theorem card_cycleFactorsFinset_eq_add_of_invariant
    [Fintype alpha] [DecidableEq alpha]
    (f : Equiv.Perm alpha) (p : alpha → Prop) [DecidablePred p]
    (hp : ∀ x, p (f x) ↔ p x) :
    f.cycleFactorsFinset.card =
      (f.subtypePerm hp).cycleFactorsFinset.card +
      (f.subtypePerm (p := fun x ↦ ¬ p x)
        (fun x ↦ not_congr (hp x))).cycleFactorsFinset.card := by
  let fp : Equiv.Perm alpha := Equiv.Perm.ofSubtype (f.subtypePerm hp)
  let hn : ∀ x, (¬ p (f x)) ↔ ¬ p x := fun x ↦ not_congr (hp x)
  let fn : Equiv.Perm alpha := Equiv.Perm.ofSubtype
    (f.subtypePerm (p := fun x ↦ ¬ p x) hn)
  have hdisjoint : Equiv.Perm.Disjoint fp fn := by
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro x
    by_cases hx : p x
    · right
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (not_not.mpr hx)
    · left
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hx
  have hmul : fp * fn = f := by
    apply Equiv.ext
    intro x
    by_cases hx : p x
    · have hfn : fn x = x := by
        dsimp [fn]
        exact Equiv.Perm.ofSubtype_apply_of_not_mem
          (p := fun y ↦ ¬ p y) _ (not_not.mpr hx)
      rw [Equiv.Perm.mul_apply, hfn]
      dsimp [fp]
      rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx,
        Equiv.Perm.subtypePerm_apply]
    · have hfx : ¬ p (f x) := (hn x).2 hx
      have hfn : fn x = f x := by
        dsimp [fn]
        rw [Equiv.Perm.ofSubtype_apply_of_mem
            (p := fun y ↦ ¬ p y) _ hx,
          Equiv.Perm.subtypePerm_apply]
      rw [Equiv.Perm.mul_apply, hfn]
      dsimp [fp]
      exact Equiv.Perm.ofSubtype_apply_of_not_mem (p := p) _ hfx
  calc
    f.cycleFactorsFinset.card =
        (fp * fn).cycleFactorsFinset.card :=
      congrArg (fun g : Equiv.Perm alpha ↦ g.cycleFactorsFinset.card) hmul.symm
    _ = (fp * fn).cycleType.card :=
      card_cycleFactorsFinset_eq_card_cycleType _
    _ = (fp.cycleType + fn.cycleType).card := by
      rw [hdisjoint.cycleType_mul]
    _ = fp.cycleType.card + fn.cycleType.card := Multiset.card_add _ _
    _ = (f.subtypePerm hp).cycleType.card +
        (f.subtypePerm (p := fun x ↦ ¬ p x) hn).cycleType.card := by
      dsimp [fp, fn]
      rw [Equiv.Perm.cycleType_ofSubtype,
        Equiv.Perm.cycleType_ofSubtype]
    _ = (f.subtypePerm hp).cycleFactorsFinset.card +
        (f.subtypePerm (p := fun x ↦ ¬ p x) hn).cycleFactorsFinset.card := by
      rw [card_cycleFactorsFinset_eq_card_cycleType,
        card_cycleFactorsFinset_eq_card_cycleType]
    _ = _ := rfl

end PermRestriction

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

/-- Darts of a component graph are exactly ambient darts whose first vertex
belongs to that component. -/
def componentDartEquiv (C : G.ConnectedComponent) :
    C.toSimpleGraph.Dart ≃ {d : G.Dart // d.fst ∈ C.supp} where
  toFun d := ⟨⟨(d.fst.1, d.snd.1), d.adj⟩, d.fst.2⟩
  invFun d := by
    have hsnd : d.1.snd ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp d.2 d.1.adj
    exact ⟨(⟨d.1.fst, d.2⟩, ⟨d.1.snd, hsnd⟩), d.1.adj⟩
  left_inv d := by
    apply Dart.ext
    apply Prod.ext <;> rfl
  right_inv d := by
    apply Subtype.ext
    apply Dart.ext
    apply Prod.ext <;> rfl

@[simp]
theorem componentDartEquiv_apply_fst (C : G.ConnectedComponent)
    (d : C.toSimpleGraph.Dart) :
    ((componentDartEquiv C d : {d : G.Dart // d.fst ∈ C.supp}) : G.Dart).fst =
      d.fst.1 := rfl

@[simp]
theorem componentDartEquiv_apply_snd (C : G.ConnectedComponent)
    (d : C.toSimpleGraph.Dart) :
    ((componentDartEquiv C d : {d : G.Dart // d.fst ∈ C.supp}) : G.Dart).snd =
      d.snd.1 := rfl

/-- Every ambient outgoing dart based at a component vertex has its other
endpoint in the same component. -/
def componentOutDartEquiv (C : G.ConnectedComponent) (v : C) :
    OutDart C.toSimpleGraph v ≃ OutDart G v.1 where
  toFun d := ⟨⟨(d.1.fst.1, d.1.snd.1), d.1.adj⟩,
    congrArg Subtype.val d.2⟩
  invFun d := by
    have hfst : d.1.fst ∈ C.supp := by
      rw [d.2]
      exact v.2
    have hsnd : d.1.snd ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp hfst d.1.adj
    let d' : C.toSimpleGraph.Dart :=
      ⟨(⟨d.1.fst, hfst⟩, ⟨d.1.snd, hsnd⟩), d.1.adj⟩
    exact ⟨d', by
      apply Subtype.ext
      exact d.2⟩
  left_inv d := by
    apply Subtype.ext
    apply Dart.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv d := by
    apply Subtype.ext
    apply Dart.ext
    apply Prod.ext <;> rfl

/-- Local cyclic order induced on a component. -/
def restrictComponentVertexPerm (R : RotationSystem G)
    (C : G.ConnectedComponent) (v : C) :
    Equiv.Perm (OutDart C.toSimpleGraph v) :=
  (componentOutDartEquiv C v).symm.permCongr (R.atVertex v.1)

theorem restrictComponentVertexPerm_isCycleOn (R : RotationSystem G)
    (C : G.ConnectedComponent) (v : C) :
    (R.restrictComponentVertexPerm C v).IsCycleOn Set.univ := by
  apply (PermRestriction.isCycleOn_univ_permCongr
    (componentOutDartEquiv C v).symm (R.atVertex v.1)).mpr
  exact R.atVertex_isCycleOn v.1

/-- Restriction of a rotation system to the induced graph of one connected
component. -/
def restrictComponent (R : RotationSystem G) (C : G.ConnectedComponent) :
    RotationSystem C.toSimpleGraph :=
  ofVertexPermutations (R.restrictComponentVertexPerm C)
    (R.restrictComponentVertexPerm_isCycleOn C)

@[simp]
theorem restrictComponent_atVertex (R : RotationSystem G)
    (C : G.ConnectedComponent) (v : C) :
    (R.restrictComponent C).atVertex v =
      R.restrictComponentVertexPerm C v := by
  apply atVertex_ofVertexPermutations

@[simp]
theorem componentDartEquiv_symm (C : G.ConnectedComponent)
    (d : C.toSimpleGraph.Dart) :
    ((componentDartEquiv C d.symm :
        {d : G.Dart // d.fst ∈ C.supp}) : G.Dart) =
      ((componentDartEquiv C d :
        {d : G.Dart // d.fst ∈ C.supp}) : G.Dart).symm := by
  rfl

/-- Component restriction commutes with forgetting the subtype vertices. -/
theorem componentDartEquiv_rotation (R : RotationSystem G)
    (C : G.ConnectedComponent) (d : C.toSimpleGraph.Dart) :
    ((componentDartEquiv C ((R.restrictComponent C).rotation d) :
        {d : G.Dart // d.fst ∈ C.supp}) : G.Dart) =
      R.rotation
        ((componentDartEquiv C d :
          {d : G.Dart // d.fst ∈ C.supp}) : G.Dart) := by
  unfold restrictComponent
  rw [ofVertexPermutations_rotation_apply_eq
    (R.restrictComponentVertexPerm C)
    (R.restrictComponentVertexPerm_isCycleOn C) d d.fst rfl]
  rfl

/-- The component facial step is the ambient facial step under the canonical
dart embedding. -/
theorem componentDartEquiv_faceStep (R : RotationSystem G)
    (C : G.ConnectedComponent) (d : C.toSimpleGraph.Dart) :
    ((componentDartEquiv C ((R.restrictComponent C).faceStep d) :
        {d : G.Dart // d.fst ∈ C.supp}) : G.Dart) =
      R.faceStep
        ((componentDartEquiv C d :
          {d : G.Dart // d.fst ∈ C.supp}) : G.Dart) := by
  change ((componentDartEquiv C
      ((R.restrictComponent C).rotation d.symm) :
        {d : G.Dart // d.fst ∈ C.supp}) : G.Dart) =
    R.rotation
      ((componentDartEquiv C d :
        {d : G.Dart // d.fst ∈ C.supp}) : G.Dart).symm
  rw [R.componentDartEquiv_rotation C d.symm]
  rfl

/-- A facial step remains in the connected component containing its input
dart. -/
theorem faceStep_fst_mem_component_iff (R : RotationSystem G)
    (C : G.ConnectedComponent) (d : G.Dart) :
    (R.faceStep d).fst ∈ C.supp ↔ d.fst ∈ C.supp := by
  have hfst : (R.faceStep d).fst = d.snd := by
    calc
      (R.faceStep d).fst = (R.rotation d.symm).fst := rfl
      _ = d.symm.fst := R.rotation_fst d.symm
      _ = d.snd := rfl
  rw [hfst]
  exact (C.mem_supp_congr_adj d.adj).symm

/-- Ambient facial permutation restricted to darts in one component. -/
def componentFaceStepSubtype (R : RotationSystem G)
    (C : G.ConnectedComponent) :
    Equiv.Perm {d : G.Dart // d.fst ∈ C.supp} :=
  R.faceStep.subtypePerm (R.faceStep_fst_mem_component_iff C)

/-- Reinterpret the complement of one component's dart set as the dart set
of a second component, when their vertex supports partition the graph. -/
def complementComponentDartEquiv (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬ v ∈ C.supp ↔ v ∈ D.supp) :
    {d : G.Dart // ¬ d.fst ∈ C.supp} ≃
      {d : G.Dart // d.fst ∈ D.supp} where
  toFun d := ⟨d.1, (hCD d.1.fst).mp d.2⟩
  invFun d := ⟨d.1, (hCD d.1.fst).mpr d.2⟩
  left_inv d := Subtype.ext rfl
  right_inv d := Subtype.ext rfl

/-- The ambient facial permutation restricted to the complement of one
component's darts. -/
def componentFaceStepComplementSubtype (R : RotationSystem G)
    (C : G.ConnectedComponent) :
    Equiv.Perm {d : G.Dart // ¬ d.fst ∈ C.supp} :=
  R.faceStep.subtypePerm
    (p := fun d ↦ ¬ d.fst ∈ C.supp)
    (fun d ↦ not_congr (R.faceStep_fst_mem_component_iff C d))

/-- Under a two-component partition, the complementary facial restriction
is the facial restriction to the second component, up to relabelling. -/
theorem complementComponent_faceStep_permCongr (R : RotationSystem G)
    (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬ v ∈ C.supp ↔ v ∈ D.supp) :
    (complementComponentDartEquiv C D hCD).permCongr
        (R.componentFaceStepComplementSubtype C) =
      R.componentFaceStepSubtype D := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [Equiv.permCongr_apply]
  rfl

/-- The two component vertex types sum to the ambient vertex type when their
supports are complementary. -/
def componentVertexSumEquiv (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬ v ∈ C.supp ↔ v ∈ D.supp) :
    C ⊕ D ≃ V := by
  classical
  exact
    (Equiv.sumCongr (Equiv.refl C)
      (Equiv.setCongr (Set.ext hCD)).symm).trans
      (Equiv.sumCompl (fun v : V ↦ v ∈ C.supp))

/-- The two component dart types sum to the ambient dart type when their
supports are complementary. -/
def componentDartSumEquiv (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬ v ∈ C.supp ↔ v ∈ D.supp) :
    C.toSimpleGraph.Dart ⊕ D.toSimpleGraph.Dart ≃ G.Dart := by
  classical
  exact (Equiv.sumCongr (componentDartEquiv C)
      ((componentDartEquiv D).trans
        (complementComponentDartEquiv C D hCD).symm)).trans
    (Equiv.sumCompl (fun d : G.Dart ↦ d.fst ∈ C.supp))

/-- Relabelling the component facial permutation by `componentDartEquiv`
gives the corresponding subtype restriction of the ambient facial
permutation. -/
theorem component_faceStep_permCongr (R : RotationSystem G)
    (C : G.ConnectedComponent) :
    (componentDartEquiv C).permCongr (R.restrictComponent C).faceStep =
      R.componentFaceStepSubtype C := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [Equiv.permCongr_apply]
  let d : C.toSimpleGraph.Dart := (componentDartEquiv C).symm x
  change (((componentDartEquiv C)
    ((R.restrictComponent C).faceStep d) :
      {d : G.Dart // d.fst ∈ C.supp}) : G.Dart) = R.faceStep x.1
  rw [R.componentDartEquiv_faceStep C d]
  exact congrArg R.faceStep (congrArg Subtype.val
    ((componentDartEquiv C).apply_symm_apply x))

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Vertex cardinality is additive across two complementary connected
components. -/
theorem card_vertices_eq_add_restrictComponents
    (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬ v ∈ C.supp ↔ v ∈ D.supp)
    [Fintype C] [Fintype D] :
    Fintype.card V = Fintype.card C + Fintype.card D := by
  rw [← Fintype.card_sum]
  exact (Fintype.card_congr (componentVertexSumEquiv C D hCD)).symm

/-- Edge cardinality is additive across two complementary connected
components.  The proof partitions darts and cancels the factor two. -/
theorem card_edges_eq_add_restrictComponents
    (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬ v ∈ C.supp ↔ v ∈ D.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    [Fintype D] [DecidableEq D] [DecidableRel D.toSimpleGraph.Adj] :
    G.edgeFinset.card = C.toSimpleGraph.edgeFinset.card +
      D.toSimpleGraph.edgeFinset.card := by
  have hcard := Fintype.card_congr (componentDartSumEquiv C D hCD)
  simp only [Fintype.card_sum] at hcard
  rw [card_darts_eq_two_mul_card_edges,
    card_darts_eq_two_mul_card_edges,
    card_darts_eq_two_mul_card_edges] at hcard
  omega

/-- Face count of a restricted component equals the cycle count of the
ambient facial permutation restricted to that component's darts. -/
theorem restrictComponent_faceCount (R : RotationSystem G)
    (C : G.ConnectedComponent) [Fintype C] [DecidableEq C]
    [DecidableRel C.toSimpleGraph.Adj] :
    (R.restrictComponent C).faceCount =
      (R.componentFaceStepSubtype C).cycleFactorsFinset.card := by
  change (R.restrictComponent C).faceStep.cycleFactorsFinset.card = _
  rw [← PermRestriction.card_cycleFactorsFinset_permCongr
    (componentDartEquiv C) (R.restrictComponent C).faceStep]
  rw [R.component_faceStep_permCongr C]

/-- If two component supports partition the vertices, the facial count is
the sum of the facial counts of their restricted rotation systems. -/
theorem faceCount_eq_add_restrictComponent_of_complement
    (R : RotationSystem G) (C D : G.ConnectedComponent)
    (hCD : ∀ v, ¬ v ∈ C.supp ↔ v ∈ D.supp)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    [Fintype D] [DecidableEq D] [DecidableRel D.toSimpleGraph.Adj] :
    R.faceCount =
      (R.restrictComponent C).faceCount +
      (R.restrictComponent D).faceCount := by
  change R.faceStep.cycleFactorsFinset.card = _
  rw [PermRestriction.card_cycleFactorsFinset_eq_add_of_invariant
    R.faceStep (fun d ↦ d.fst ∈ C.supp)
    (R.faceStep_fst_mem_component_iff C)]
  change (R.componentFaceStepSubtype C).cycleFactorsFinset.card +
      (R.componentFaceStepComplementSubtype C).cycleFactorsFinset.card = _
  rw [R.restrictComponent_faceCount C,
    R.restrictComponent_faceCount D]
  congr 1
  rw [← PermRestriction.card_cycleFactorsFinset_permCongr
    (complementComponentDartEquiv C D hCD)
    (R.componentFaceStepComplementSubtype C)]
  rw [R.complementComponent_faceStep_permCongr C D hCD]

end Finite

end RotationSystem

end

end LeanCo.PackingEdgeColoring
