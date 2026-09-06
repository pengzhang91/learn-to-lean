import LeanCo.PackingEdgeColoring.SectionFourDischarging
import LeanCo.PackingEdgeColoring.ComponentGoodFour
import LeanCo.PackingEdgeColoring.SectionFourReduction

/-!
# Section 4 structural facts on connected components

The planar hypothesis is componentwise, whereas a minimal bad graph is not
assumed connected.  This module transports chains and thread-pair
configurations from an induced connected component back to the ambient graph,
so the closed discharging contradiction can be run on any edge-bearing
component.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A chain in an induced connected component maps to an ambient chain. -/
theorem IsKChain.map_connectedComponent
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    {u v : C} {p : C.toSimpleGraph.Walk u v} {k : ℕ}
    (hp : IsKChain C.toSimpleGraph p k) :
    IsKChain G (p.map C.toSimpleGraph_hom) k := by
  refine ⟨Walk.map_isPath_of_injective Subtype.coe_injective hp.1,
    ?_, ?_⟩
  · simpa only [Walk.support_map, List.length_map] using hp.2.1
  · intro x hx
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change G.degree (y : V) = 2
    rw [← degree_toSimpleGraph_connectedComponent G C y]
    exact hp.2.2 y hy

/-- A thread in an induced connected component maps to an ambient thread. -/
theorem IsKThread.map_connectedComponent
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    {u v : C} {p : C.toSimpleGraph.Walk u v} {k : ℕ}
    (hp : IsKThread C.toSimpleGraph p k) :
    IsKThread G (p.map C.toSimpleGraph_hom) k := by
  refine ⟨Walk.map_isPath_of_injective Subtype.coe_injective hp.1,
    ?_, ?_, ?_, ?_⟩
  · simpa only [Walk.length_map] using hp.length
  · change G.degree (u : V) = 3
    rw [← degree_toSimpleGraph_connectedComponent G C u]
    exact hp.start_three
  · change G.degree (v : V) = 3
    rw [← degree_toSimpleGraph_connectedComponent G C v]
    exact hp.end_three
  · intro i hi hil
    rw [Walk.getVert_map]
    change G.degree ((p.getVert i : C) : V) = 2
    rw [← degree_toSimpleGraph_connectedComponent G C (p.getVert i)]
    apply IsKThread.internal_two C.toSimpleGraph hp hi
    simpa only [Walk.length_map] using hil

/-- Distinct thread arms in a component remain distinct ambient thread
arms. -/
theorem HasDistinctThreadsAt.map_connectedComponent
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (u : C) {k l : ℕ}
    (h : HasDistinctThreadsAt (G := C.toSimpleGraph) u k l) :
    HasDistinctThreadsAt (G := G) u.1 k l := by
  obtain ⟨v, w, p, q, hp, hq, hfirst⟩ := h
  refine ⟨v.1, w.1, p.map C.toSimpleGraph_hom,
    q.map C.toSimpleGraph_hom,
    hp.map_connectedComponent G C, hq.map_connectedComponent G C, ?_⟩
  intro hEq
  apply hfirst
  apply Subtype.ext
  have hpv := Walk.getVert_map C.toSimpleGraph_hom p 1
  have hqv := Walk.getVert_map C.toSimpleGraph_hom q 1
  exact hpv.symm.trans (hEq.trans hqv)

/-- The long-thread-pair obstruction transports from a component to the
ambient graph. -/
theorem HasThreeAndLongThreadAt.map_connectedComponent
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (u : C)
    (h : HasThreeAndLongThreadAt (G := C.toSimpleGraph) u) :
    HasThreeAndLongThreadAt (G := G) u.1 := by
  rcases h with h | h
  · exact Or.inl (h.map_connectedComponent G C u)
  · exact Or.inr (h.map_connectedComponent G C u)

/-- An ambient four-chain exclusion restricts to each connected component. -/
theorem no_four_chain_connectedComponent
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (hno4 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 4) :
    ∀ {u v : C} (p : C.toSimpleGraph.Walk u v),
      ¬ IsKChain C.toSimpleGraph p 4 := by
  intro u v p hp
  exact hno4 (p.map C.toSimpleGraph_hom)
    (hp.map_connectedComponent G C)

/-- An ambient long-thread-pair exclusion restricts to each connected
component. -/
theorem no_threeAndLongThread_connectedComponent
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (hforbid : ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u) :
    ∀ u, ¬ HasThreeAndLongThreadAt (G := C.toSimpleGraph) u := by
  intro u hu
  exact hforbid u.1 (hu.map_connectedComponent G C u)

/-- On an edge-bearing component, active minimum degree two and ambient
subcubicity force every degree to be exactly two or three. -/
theorem degree_eq_two_or_three_connectedComponent
    (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (hedge : C.toSimpleGraph.edgeSet.Nonempty)
    (hsub : IsSubcubic G)
    (hmindeg : ∀ v, 0 < G.degree v → 2 ≤ G.degree v) :
    ∀ v : C,
      C.toSimpleGraph.degree v = 2 ∨ C.toSimpleGraph.degree v = 3 := by
  have hnontrivial : Nontrivial C := by
    obtain ⟨e, he⟩ := hedge
    have hadj : C.toSimpleGraph.Adj e.out.1 e.out.2 := by
      rw [← SimpleGraph.mem_edgeSet, Sym2.mk, e.out_eq]
      exact he
    exact nontrivial_iff.mpr ⟨e.out.1, e.out.2, hadj.ne⟩
  letI : Nontrivial C := hnontrivial
  intro v
  have hpos : 0 < C.toSimpleGraph.degree v :=
    C.connected_toSimpleGraph.preconnected.degree_pos_of_nontrivial v
  have hlo : 2 ≤ C.toSimpleGraph.degree v := by
    apply activeMinDegree_connectedComponent G hmindeg C v hpos
  have hhi : C.toSimpleGraph.degree v ≤ 3 :=
    hsub.connectedComponent G C v
  omega

/-- Componentwise planarity plus the three structural exclusions already
contradicts the existence of any edge.  This is the global bridge from the
minimal-counterexample lemmas to the closed facial discharging theorem. -/
theorem false_of_sectionFour_forbidden_configurations
    (hsub : IsSubcubic G)
    (hplanar : IsCombinatoriallyPlanar G)
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    (hmindeg : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hno4 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 4)
    (hforbid : ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u)
    (hedge : G.edgeSet.Nonempty) : False := by
  obtain ⟨e, he⟩ := hedge
  let edge : G.edgeSet := ⟨e, he⟩
  let C : G.ConnectedComponent := edgeComponent G edge
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableEq C := Classical.decEq C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have hedgeC : C.toSimpleGraph.edgeSet.Nonempty :=
    ⟨edgeInComponent G edge, (edgeInComponent G edge).2⟩
  have hrotation : HasSphericalRotation C.toSimpleGraph := by
    exact hplanar C hedgeC
  obtain ⟨R, hspherical⟩ := hrotation
  have hdegC : ∀ v : C,
      C.toSimpleGraph.degree v = 2 ∨ C.toSimpleGraph.degree v = 3 :=
    degree_eq_two_or_three_connectedComponent G C hedgeC hsub hmindeg
  have hgirthC : (16 : ℕ∞) ≤ C.toSimpleGraph.egirth :=
    girth_lowerBound_connectedComponent G hgirth C
  have hno4C : ∀ {u v : C} (p : C.toSimpleGraph.Walk u v),
      ¬ IsKChain C.toSimpleGraph p 4 :=
    no_four_chain_connectedComponent G C hno4
  have hforbidC : ∀ u : C,
      ¬ HasThreeAndLongThreadAt (G := C.toSimpleGraph) u :=
    no_threeAndLongThread_connectedComponent G C hforbid
  exact R.no_spherical_map_of_girth16_forbidden_threads_of_minDegree
    hspherical hdegC hgirthC hno4C hforbidC

/-- Exact Section 4 minimal-counterexample reduction.  Once the three local
reducibility conclusions are available, componentwise spherical discharging
rules out a bad graph and hence yields a good four-colouring. -/
theorem hasGoodFour_of_minimal_forbidden_configurations
    (hreducible : ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
      IsEdgeMinimalBad SectionFourEligible HasGoodFour H →
      (∀ v, 0 < H.degree v → 2 ≤ H.degree v) ∧
      (∀ {u v : V} (p : H.Walk u v), ¬ IsKChain H p 4) ∧
      (∀ u, ¬ HasThreeAndLongThreadAt (G := H) u)) :
    ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
      SectionFourEligible H → HasGoodFour H := by
  intro H d hEligible
  have hd : d = Classical.decRel H.Adj := Subsingleton.elim _ _
  subst d
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  by_contra hbad
  obtain ⟨K, hmin⟩ :=
    exists_edgeMinimalBad (V := V) (Eligible := SectionFourEligible)
      (Good := HasGoodFour) ⟨H, hEligible, hbad⟩
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨hmindeg, hno4, hforbid⟩ := hreducible K hmin
  have hEligibleK : IsSubcubic K ∧ IsCombinatoriallyPlanar K ∧
      (16 : ℕ∞) ≤ K.egirth := by
    simpa [SectionFourEligible] using hmin.eligible
  have hedge : K.edgeSet.Nonempty := by
    by_contra hempty
    have hedgeEmpty : K.edgeSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have hbot : K = ⊥ := SimpleGraph.edgeSet_eq_empty.mp hedgeEmpty
    apply hmin.not_good
    simpa [hbot] using (hasGoodFour_bot (V := V))
  exact false_of_sectionFour_forbidden_configurations K
    hEligibleK.1 hEligibleK.2.1 hEligibleK.2.2
    hmindeg hno4 hforbid hedge

end Finite

end

end LeanCo.PackingEdgeColoring
