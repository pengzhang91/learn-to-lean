import LeanCo.PackingEdgeColoring.MinimalCounterexample
import LeanCo.PackingEdgeColoring.FaceBoundaryGirth
import LeanCo.PackingEdgeColoring.ComponentGoodFour

/-!
# Minimal-counterexample interface for Section 4

This file fixes the exact graph predicate and good-colouring predicate used
by the girth-sixteen theorem.  It also proves that `GoodFour` is independent
of the implementation chosen to decide adjacency.  That bookkeeping is
needed because the semantic predicates below deliberately use canonical
classical instances, while deletion lemmas use the instances inherited from
the ambient graph.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

/-- Eligibility for the stronger Section 4 statement. -/
def SectionFourEligible [Fintype V] (G : SimpleGraph V) : Prop := by
  classical
  exact IsSubcubic G ∧ IsCombinatoriallyPlanar G ∧
    (16 : ℕ∞) ≤ G.egirth

/-- Existence of a colouring satisfying all three Section 4 invariants. -/
def HasGoodFour [Fintype V] (G : SimpleGraph V) : Prop := by
  classical
  exact ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour

section Basic

variable [Fintype V] [DecidableEq V]

/-- The edgeless graph has the unique vacuous Section 4 good colouring. -/
theorem hasGoodFour_bot : HasGoodFour (⊥ : SimpleGraph V) := by
  classical
  let colour : (⊥ : SimpleGraph V).edgeSet → OneTwoColor 4 :=
    fun e ↦ False.elim (by simpa using e.2)
  rw [HasGoodFour]
  refine ⟨colour, ?_, ?_, ?_, ?_⟩
  · intro e _
    exact False.elim (by simpa using e.2)
  · intro e _
    exact False.elim (by simpa using e.2)
  · intro u hu
    simp [IsTwoVertex] at hu
  · intro u₁ u₂ p hp
    have hu := hp.2.2.1
    simp [IsThreeVertex] at hu

/-- A Section 4 good colouring gives the paper's original packing
edge-colouring after forgetting the auxiliary invariants. -/
theorem HasGoodFour.hasOneTwoPackingEdgeColoring
    [DecidableRel G.Adj] (h : HasGoodFour G) :
    HasOneTwoPackingEdgeColoring G 4 := by
  classical
  rw [hasOneTwoPackingEdgeColoring_iff_exists_local]
  rw [HasGoodFour] at h
  obtain ⟨colour, hgood⟩ := h
  exact ⟨colour, hgood.1⟩

/-- It is enough to construct a Section 4 good colouring separately on
each connected component.  The auxiliary invariants need not be glued:
after forgetting them, the semantic packing colourings glue directly. -/
theorem hasOneTwoPackingEdgeColoring_four_of_components_goodFour
    [DecidableRel G.Adj]
    (hcomp : ∀ C : G.ConnectedComponent,
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
      HasGoodFour C.toSimpleGraph) :
    HasOneTwoPackingEdgeColoring G 4 := by
  apply hasOneTwoPackingEdgeColoring_of_connectedComponents G
  intro C
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  exact (hcomp C).hasOneTwoPackingEdgeColoring

/-- Unlike the final packing statement, the strengthened `GoodFour`
predicate itself also glues across connected components. -/
theorem hasGoodFour_of_connectedComponents
    [DecidableRel G.Adj]
    (hcomp : ∀ C : G.ConnectedComponent,
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
      HasGoodFour C.toSimpleGraph) :
    HasGoodFour G := by
  classical
  letI : DecidableEq V := Classical.decEq V
  letI : DecidableRel G.Adj := Classical.decRel _
  rw [HasGoodFour]
  choose colour hgood using fun C : G.ConnectedComponent ↦ by
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    simpa only [HasGoodFour] using hcomp C
  exact ⟨glueComponentColoring G colour,
    goodFour_of_connectedComponents G colour hgood⟩

/-- All graph-theoretic inputs required by the connected Section 4 proof
pass from the ambient graph to a nontrivial connected component. -/
theorem connectedComponent_sectionFour_inputs
    [DecidableRel G.Adj]
    (hsub : IsSubcubic G) (hplanar : IsCombinatoriallyPlanar G)
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    (C : G.ConnectedComponent)
    (hedge : C.toSimpleGraph.edgeSet.Nonempty) :
    letI : Fintype C := Fintype.ofFinite C
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    IsSubcubic C.toSimpleGraph ∧
      HasSphericalRotation C.toSimpleGraph ∧
      (16 : ℕ∞) ≤ C.toSimpleGraph.egirth := by
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  refine ⟨hsub.connectedComponent G C, ?_,
    girth_lowerBound_connectedComponent G hgirth C⟩
  simpa [IsCombinatoriallyPlanar] using hplanar C hedge

/-- To prove the original Section 4 packing statement for an arbitrary
eligible graph, it is enough to solve the nontrivial connected case with a
spherical rotation system.  Isolated components are discharged by the
vacuous good colouring, while nontrivial component colourings are forgotten
to semantic packing colourings and glued by `ComponentColoring`. -/
theorem sectionFourPacking_of_connected_component_solver
    (heligible : SectionFourEligible G)
    (hsolver : ∀ C : G.ConnectedComponent,
      letI : Fintype C := Fintype.ofFinite C
      letI : DecidableEq C := Classical.decEq C
      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
      C.toSimpleGraph.edgeSet.Nonempty →
        C.toSimpleGraph.Connected →
        IsSubcubic C.toSimpleGraph →
        HasSphericalRotation C.toSimpleGraph →
        (16 : ℕ∞) ≤ C.toSimpleGraph.egirth →
        HasGoodFour C.toSimpleGraph) :
    HasOneTwoPackingEdgeColoring G 4 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  rcases heligible with ⟨hsub, hplanar, hgirth⟩
  apply hasOneTwoPackingEdgeColoring_four_of_components_goodFour
  intro C
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  by_cases hedge : C.toSimpleGraph.edgeSet.Nonempty
  · obtain ⟨hsubC, hrotationC, hgirthC⟩ :=
      connectedComponent_sectionFour_inputs hsub hplanar hgirth C hedge
    exact hsolver C hedge C.connected_toSimpleGraph hsubC hrotationC hgirthC
  · have hedgeEmpty : C.toSimpleGraph.edgeSet = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hedge
    have hbot : C.toSimpleGraph = ⊥ :=
      SimpleGraph.edgeSet_eq_empty.mp hedgeEmpty
    rw [hbot]
    exact hasGoodFour_bot

end Basic

section DecidableIrrel

variable [Fintype V] [DecidableEq V]

/-- Two-vertex status is decision-procedure independent. -/
theorem isTwoVertex_change_decidableRel (d₁ d₂ : DecidableRel G.Adj)
    {v : V} (h : @IsTwoVertex V G _ d₁ v) :
    @IsTwoVertex V G _ d₂ v := by
  have hvCard : Nat.card (G.neighborSet v) = 2 := by
    letI : DecidableRel G.Adj := d₁
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
    exact h
  letI : DecidableRel G.Adj := d₂
  rw [IsTwoVertex, ← G.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card]
  exact hvCard

/-- Three-vertex status is decision-procedure independent. -/
theorem isThreeVertex_change_decidableRel (d₁ d₂ : DecidableRel G.Adj)
    {v : V} (h : @IsThreeVertex V G _ d₁ v) :
    @IsThreeVertex V G _ d₂ v := by
  have hvCard : Nat.card (G.neighborSet v) = 3 := by
    letI : DecidableRel G.Adj := d₁
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
    exact h
  letI : DecidableRel G.Adj := d₂
  rw [IsThreeVertex, ← G.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card]
  exact hvCard

/-- Thread certificates are independent of adjacency decidability. -/
theorem isKThread_change_decidableRel
    (d₁ d₂ : DecidableRel G.Adj)
    {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : @IsKThread V G _ d₁ u v p k) :
    @IsKThread V G _ d₂ u v p k := by
  rcases h with ⟨hpath, hlen, hu, hv, hint⟩
  refine ⟨hpath, hlen,
    isThreeVertex_change_decidableRel d₁ d₂ hu,
    isThreeVertex_change_decidableRel d₁ d₂ hv, ?_⟩
  intro i hi hil
  exact isTwoVertex_change_decidableRel d₁ d₂ (hint i hi hil)

/-- `GoodFour` is independent of the algorithm used to decide adjacency. -/
theorem goodFour_change_decidableRel
    (d₁ d₂ : DecidableRel G.Adj)
    (colour : G.edgeSet → OneTwoColor 4)
    (h : @GoodFour V G _ _ d₁ colour) :
    @GoodFour V G _ _ d₂ colour := by
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro u hu hmatching hall
    have huOld : @IsTwoVertex V G _ d₁ u :=
      isTwoVertex_change_decidableRel d₂ d₁ hu
    have hconditionOld : @ConditionTwo V G _ d₁ colour := h.2.2.1
    exact hconditionOld u huOld hmatching hall
  · intro u₁ u₂ p hp hleft hright
    have hpOld : @IsKThread V G _ d₁ u₁ u₂ p 2 :=
      isKThread_change_decidableRel d₂ d₁ hp
    have hfirst :
        @threadFirstEdge V G _ _ d₁ u₁ u₂ p 2 hpOld =
          @threadFirstEdge V G _ _ d₂ u₁ u₂ p 2 hp := by
      apply Subtype.ext
      rfl
    have hlast :
        @threadLastEdge V G _ _ d₁ u₁ u₂ p 2 hpOld =
          @threadLastEdge V G _ _ d₂ u₁ u₂ p 2 hp := by
      apply Subtype.ext
      rfl
    have hleftOld : ExternalEdgesInduced G colour u₁
        (@threadFirstEdge V G _ _ d₁ u₁ u₂ p 2 hpOld) := by
      rw [hfirst]
      exact hleft
    have hrightOld : ExternalEdgesInduced G colour u₂
        (@threadLastEdge V G _ _ d₁ u₁ u₂ p 2 hpOld) := by
      rw [hlast]
      exact hright
    have hconditionThreeOld : @ConditionThree V G _ _ d₁ colour :=
      h.2.2.2
    have hne := hconditionThreeOld u₁ u₂ p hpOld hleftOld hrightOld
    simpa only [hfirst, hlast] using hne

end DecidableIrrel

end

end LeanCo.PackingEdgeColoring
