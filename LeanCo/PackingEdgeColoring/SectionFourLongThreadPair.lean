import LeanCo.PackingEdgeColoring.SectionFourReduction
import LeanCo.PackingEdgeColoring.SectionFourStructure
import LeanCo.PackingEdgeColoring.SectionThreeNoThreeChain
import LeanCo.PackingEdgeColoring.GoodExtension
import LeanCo.PackingEdgeColoring.AvailabilityMultiplicity

/-!
# The long-thread-pair reductions in Section 4

This module develops the common graph-theoretic and deletion infrastructure
behind Lemmas 4.4--4.11 of Kim--Liu--Xu.  All seven reductions delete the
middle vertex of a certified 3-thread.  The definitions below retain the
ordered vertices of that thread, so that every later recolouring statement
is tied to the original walk rather than to an unrelated path with the same
endpoints.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-! ## Ordered data on the 3-thread selected for the reduction -/

/-- The ordered local data carried by a 3-thread
`u-v₁-v₂-v₃-z`.  Only inequalities needed by incidence deletion are
stored; all of them follow from path simplicity. -/
structure ThreeThreadCore (u v₁ v₂ v₃ z : V) : Prop where
  start_three : IsThreeVertex G u
  end_three : IsThreeVertex G z
  first_two : IsTwoVertex G v₁
  middle_two : IsTwoVertex G v₂
  third_two : IsTwoVertex G v₃
  first_adj : G.Adj u v₁
  left_adj : G.Adj v₁ v₂
  right_adj : G.Adj v₂ v₃
  last_adj : G.Adj v₃ z
  first_ne_third : v₁ ≠ v₃
  middle_ne_start : v₂ ≠ u
  middle_ne_end : v₂ ≠ z

/-- Extract the ordered five-vertex core from a certified 3-thread. -/
theorem IsKThread.threeThreadCore {u z : V} {p : G.Walk u z}
    (hp : IsKThread G p 3) :
    ThreeThreadCore G u (p.getVert 1) (p.getVert 2) (p.getVert 3) z := by
  have hlen : p.length = 4 := by simpa using hp.length
  have hget (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) (hij : i ≠ j) :
      p.getVert i ≠ p.getVert j := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show i ∈ {r : ℕ | r ≤ p.length} by simpa [hlen] using hi)
      (show j ∈ {r : ℕ | r ≤ p.length} by simpa [hlen] using hj)
      heq
    exact hij hinj
  have hend : p.getVert 4 = z := by
    rw [← hlen]
    exact p.getVert_length
  have hfirst : G.Adj u (p.getVert 1) := hp.first_step_adj
  have hleft : G.Adj (p.getVert 1) (p.getVert 2) :=
    p.adj_getVert_succ (i := 1) (by omega)
  have hright : G.Adj (p.getVert 2) (p.getVert 3) :=
    p.adj_getVert_succ (i := 2) (by omega)
  have hlast : G.Adj (p.getVert 3) z := by
    simpa using hp.last_step_adj
  have hv₁ : IsTwoVertex G (p.getVert 1) :=
    IsKThread.internal_two G hp (by omega) (by omega)
  have hv₂ : IsTwoVertex G (p.getVert 2) :=
    IsKThread.internal_two G hp (by omega) (by omega)
  have hv₃ : IsTwoVertex G (p.getVert 3) :=
    IsKThread.internal_two G hp (by omega) (by omega)
  refine ⟨hp.start_three, hp.end_three, hv₁, hv₂, hv₃,
    hfirst, hleft, hright, hlast, ?_, ?_, ?_⟩
  · exact hget 1 3 (by omega) (by omega) (by omega)
  · simpa using hget 2 0 (by omega) (by omega) (by omega)
  · simpa [hend] using hget 2 4 (by omega) (by omega) (by omega)

/-! ## The common incidence deletion -/

/-- The smaller graph used in every one of Lemmas 4.4--4.11. -/
abbrev deleteThreeThreadMiddle (v₂ : V) : SimpleGraph V :=
  G.deleteIncidenceSet v₂

/-- The two missing edges, together with the retained edges, exhaust the
ambient edge set. -/
theorem insert_threeThread_gap_retained_eq_univ
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z) :
    insert (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)
      (insert (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet)
        (RetainedEdges (deleteThreeThreadMiddle G v₂) G)) = Set.univ := by
  exact insert_chain_edges_retained_eq_univ G h.middle_two h.left_adj
    h.right_adj h.first_ne_third

/-- A valid colouring of the smaller graph transports honestly on all
retained ambient edges. -/
theorem transport_deleteThreeThreadMiddle_valid {k : ℕ}
    {u v₁ v₂ v₃ z : V}
    (_h : ThreeThreadCore G u v₁ v₂ v₃ z)
    {small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor k}
    (hsmall : IsOneTwoColoring (deleteThreeThreadMiddle G v₂) small) :
    IsOneTwoColoringOn G
      (RetainedEdges (deleteThreeThreadMiddle G v₂) G)
      (transportColoringToSupergraph
        (G.deleteIncidenceSet_le v₂) small) := by
  exact transport_deleteIncidenceSet_valid (G := G) v₂ hsmall

/-- The chosen middle vertex really has an incident edge, so its incidence
deletion is strictly smaller. -/
theorem threeThreadMiddle_has_incident_edge
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z) :
    ∃ e : G.edgeSet, v₂ ∈ (e : Sym2 V) := by
  exact ⟨⟨s(v₁, v₂), h.left_adj⟩, by simp⟩

/-- Subcubicity is inherited by the common incidence deletion. -/
theorem isSubcubic_deleteThreeThreadMiddle
    (hsub : IsSubcubic G) (v₂ : V) :
    IsSubcubic (deleteThreeThreadMiddle G v₂) := by
  intro x
  exact ((G.deleteIncidenceSet v₂).degree_le_of_le
      (G.deleteIncidenceSet_le v₂)).trans
    (hsub x)

/-- The extended girth is monotone under the common incidence deletion. -/
theorem girth_deleteThreeThreadMiddle
    (hgirth : (16 : ℕ∞) ≤ G.egirth) (v₂ : V) :
    (16 : ℕ∞) ≤ (deleteThreeThreadMiddle G v₂).egirth := by
  exact hgirth.trans (SimpleGraph.egirth_anti (G.deleteIncidenceSet_le v₂))

/-! ## Ambient 2-threads avoid the deleted 3-thread core -/

/-- A certified 2-thread cannot contain a degree-two vertex whose two
neighbours are themselves degree two: at either internal position one of
the endpoints of the 2-thread would then have degree two. -/
theorem twoThread_avoids_twoVertex_between_twoTwo
    {r s a x b : V} {p : G.Walk r s}
    (hp : IsKThread G p 2)
    (hx : IsTwoVertex G x)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (ha : IsTwoVertex G a) (hb : IsTwoVertex G b) :
    x ∉ p.support := by
  intro hxmem
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hxmem
  obtain ⟨i, hi, hibound⟩ := hxmem
  have hlen : p.length = 3 := by simpa using hp.length
  have hend : p.getVert 3 = s := by
    rw [← hlen]
    exact p.getVert_length
  have hdegree_ne (y : V) (hy : IsTwoVertex G y) : r ≠ y := by
    intro hry
    have hrthree := hp.start_three
    unfold IsThreeVertex at hrthree
    unfold IsTwoVertex at hy
    rw [hry] at hrthree
    omega
  have hend_degree_ne (y : V) (hy : IsTwoVertex G y) : s ≠ y := by
    intro hsy
    have hsthree := hp.end_three
    unfold IsThreeVertex at hsthree
    unfold IsTwoVertex at hy
    rw [hsy] at hsthree
    omega
  rw [hlen] at hibound
  interval_cases i
  · exact hdegree_ne x hx (by simpa using hi)
  · have hrx : G.Adj r x := by
      have hadj := p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
      simpa [hi] using hadj
    have hrmem : r ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x r).mpr hrx.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxb hab] at hrmem
    have hr : r = a ∨ r = b := by simpa using hrmem
    exact hr.elim (hdegree_ne a ha) (hdegree_ne b hb)
  · have hxs : G.Adj x s := by
      have hadj := p.adj_getVert_succ (i := 2) (by omega : 2 < p.length)
      simpa [hi, hend] using hadj
    have hsmem : s ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x s).mpr hxs
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxb hab] at hsmem
    have hs : s = a ∨ s = b := by simpa using hsmem
    exact hs.elim (hend_degree_ne a ha) (hend_degree_ne b hb)
  · exact hend_degree_ne x hx (by simpa [hend] using hi)

/-- If one neighbour `b` of a degree-two vertex `x` is absent from a
certified 2-thread, then `x` is absent as well.  Were `x` internal, its two
distinct predecessor/successor vertices would have to be the same remaining
neighbour `a`. -/
theorem twoThread_avoids_twoVertex_of_neighbor_avoided
    {r s a x b : V} {p : G.Walk r s}
    (hp : IsKThread G p 2)
    (hx : IsTwoVertex G x)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b)
    (hb : b ∉ p.support) :
    x ∉ p.support := by
  intro hxmem
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hxmem
  obtain ⟨i, hi, hibound⟩ := hxmem
  have hlen : p.length = 3 := by simpa using hp.length
  have hend : p.getVert 3 = s := by
    rw [← hlen]
    exact p.getVert_length
  have hstartNe : r ≠ x := by
    intro hrx
    have hrthree := hp.start_three
    unfold IsThreeVertex at hrthree
    unfold IsTwoVertex at hx
    rw [hrx] at hrthree
    omega
  have hendNe : s ≠ x := by
    intro hsx
    have hsthree := hp.end_three
    unfold IsThreeVertex at hsthree
    unfold IsTwoVertex at hx
    rw [hsx] at hsthree
    omega
  have hne02 : p.getVert 0 ≠ p.getVert 2 := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show 0 ∈ {j : ℕ | j ≤ p.length} by simp)
      (show 2 ∈ {j : ℕ | j ≤ p.length} by simp [hlen]) heq
    omega
  have hne13 : p.getVert 1 ≠ p.getVert 3 := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show 1 ∈ {j : ℕ | j ≤ p.length} by simp [hlen])
      (show 3 ∈ {j : ℕ | j ≤ p.length} by simp [hlen]) heq
    omega
  rw [hlen] at hibound
  interval_cases i
  · exact hstartNe (by simpa using hi)
  · have hrx : G.Adj x r := by
      have hadj := p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
      simpa [hi] using hadj.symm
    have hxy : G.Adj x (p.getVert 2) := by
      have hadj := p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
      simpa [hi] using hadj
    have hrmem : r ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x r).mpr hrx
    have hymem : p.getVert 2 ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x (p.getVert 2)).mpr hxy
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hxa hxb hab] at hrmem hymem
    have hr : r = a := by
      have hrCases : r = a ∨ r = b := by simpa using hrmem
      exact hrCases.resolve_right (fun e ↦ hb (e ▸ p.start_mem_support))
    have hy : p.getVert 2 = a := by
      have hyCases : p.getVert 2 = a ∨ p.getVert 2 = b := by simpa using hymem
      exact hyCases.resolve_right (fun e ↦ hb (e ▸ p.getVert_mem_support 2))
    exact hne02 (by simpa [hr, hy])
  · have hyx : G.Adj x (p.getVert 1) := by
      have hadj := p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
      simpa [hi] using hadj.symm
    have hxs : G.Adj x s := by
      have hadj := p.adj_getVert_succ (i := 2) (by omega : 2 < p.length)
      simpa [hi, hend] using hadj
    have hymem : p.getVert 1 ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x (p.getVert 1)).mpr hyx
    have hsmem : s ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x s).mpr hxs
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hxa hxb hab] at hymem hsmem
    have hy : p.getVert 1 = a := by
      have hyCases : p.getVert 1 = a ∨ p.getVert 1 = b := by simpa using hymem
      exact hyCases.resolve_right (fun e ↦ hb (e ▸ p.getVert_mem_support 1))
    have hs : s = a := by
      have hsCases : s = a ∨ s = b := by simpa using hsmem
      exact hsCases.resolve_right (fun e ↦ hb (e ▸ p.end_mem_support))
    exact hne13 (by simpa [hy, hs, hend])
  · exact hendNe (by simpa [hend] using hi)

/-- Every certified ambient 2-thread avoids all three internal vertices of
the selected 3-thread. -/
theorem twoThread_avoids_threeThread_internal
    {r s : V} {q : G.Walk r s} (hq : IsKThread G q 2)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z) :
    v₁ ∉ q.support ∧ v₂ ∉ q.support ∧ v₃ ∉ q.support := by
  have hv₂ : v₂ ∉ q.support :=
    twoThread_avoids_twoVertex_between_twoTwo G hq h.middle_two
      h.left_adj h.right_adj h.first_ne_third h.first_two h.third_two
  have hv₁ : v₁ ∉ q.support :=
    twoThread_avoids_twoVertex_of_neighbor_avoided G hq h.first_two
      h.first_adj.symm h.left_adj (by
        intro huz
        subst u
        have hthree := h.start_three
        have htwo := h.middle_two
        unfold IsThreeVertex at hthree
        unfold IsTwoVertex at htwo
        omega) hv₂
  have hv₃ : v₃ ∉ q.support :=
    twoThread_avoids_twoVertex_of_neighbor_avoided G hq h.third_two
      h.last_adj h.right_adj.symm (by
        intro hzv₂
        subst z
        have hthree := h.end_three
        have htwo := h.middle_two
        unfold IsThreeVertex at hthree
        unfold IsTwoVertex at htwo
        omega) hv₂
  exact ⟨hv₁, hv₂, hv₃⟩

/-- Every vertex occurrence of an ambient 2-thread is different from, and
nonadjacent to, the deleted middle vertex. -/
theorem twoThread_vertex_far_from_threeThread_middle
    {r s : V} {q : G.Walk r s} (hq : IsKThread G q 2)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    {y : V} (hy : y ∈ q.support) :
    y ≠ v₂ ∧ ¬ G.Adj y v₂ := by
  have havoid := twoThread_avoids_threeThread_internal G hq h
  have hy₂ : y ≠ v₂ := fun e ↦ havoid.2.1 (e ▸ hy)
  refine ⟨hy₂, ?_⟩
  intro hyv₂
  have hymem : y ∈ G.neighborFinset v₂ :=
    (G.mem_neighborFinset v₂ y).mpr hyv₂.symm
  rw [neighborFinset_eq_pair_of_isTwoVertex G h.middle_two
    h.left_adj.symm h.right_adj h.first_ne_third] at hymem
  have hycases : y = v₁ ∨ y = v₃ := by simpa using hymem
  exact hycases.elim (fun e ↦ havoid.1 (e ▸ hy))
    (fun e ↦ havoid.2.2 (e ▸ hy))

/-- Every edge of an ambient 2-thread survives deletion of the selected
3-thread's middle vertex. -/
theorem twoThread_edges_avoid_threeThread_middle
    {r s : V} {q : G.Walk r s} (hq : IsKThread G q 2)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z) :
    ∀ e, e ∈ q.edges → e ∉ G.incidenceSet v₂ := by
  intro e he heInc
  let eG : G.edgeSet := ⟨e, q.edges_subset_edgeSet he⟩
  have hv₂e : v₂ ∈ e := by
    exact (G.edge_mem_incidenceSet_iff (e := eG)).mp heInc
  have hv₂support : v₂ ∈ q.support :=
    SimpleGraph.Walk.mem_support_of_mem_edges he hv₂e
  exact (twoThread_avoids_threeThread_internal G hq h).2.1 hv₂support

/-- A certified ambient 2-thread transfers to the incidence-deleted graph,
with its underlying walk unchanged when mapped back to `G`. -/
theorem exists_twoThread_deleteThreeThreadMiddle
    {r s : V} {q : G.Walk r s} (hq : IsKThread G q 2)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z) :
    ∃ qH : (deleteThreeThreadMiddle G v₂).Walk r s,
      IsKThread (deleteThreeThreadMiddle G v₂) qH 2 ∧
        ∀ i, qH.getVert i = q.getVert i := by
  let havoid := twoThread_edges_avoid_threeThread_middle G hq h
  let htransfer : ∀ e, e ∈ q.edges →
      e ∈ (deleteThreeThreadMiddle G v₂).edgeSet := by
    intro e he
    rw [edgeSet_deleteIncidenceSet]
    exact ⟨q.edges_subset_edgeSet he, havoid e he⟩
  let qH : (deleteThreeThreadMiddle G v₂).Walk r s :=
    q.transfer (deleteThreeThreadMiddle G v₂) htransfer
  have hget (i : ℕ) : qH.getVert i = q.getVert i := by
    change (q.transfer (deleteThreeThreadMiddle G v₂) htransfer).getVert i =
      q.getVert i
    rw [SimpleGraph.Walk.getVert_eq_getD_support,
      SimpleGraph.Walk.getVert_eq_getD_support,
      SimpleGraph.Walk.support_transfer]
  have hlength : qH.length = q.length := by
    change (q.transfer (deleteThreeThreadMiddle G v₂) htransfer).length =
      q.length
    exact SimpleGraph.Walk.length_transfer q htransfer
  have hstartFar := twoThread_vertex_far_from_threeThread_middle G hq h
    q.start_mem_support
  have hendFar := twoThread_vertex_far_from_threeThread_middle G hq h
    q.end_mem_support
  refine ⟨qH, ?_, hget⟩
  refine ⟨hq.1.transfer htransfer, by simpa [hlength] using hq.length,
    ?_, ?_, ?_⟩
  · have hthree := hq.start_three
    unfold IsThreeVertex at hthree ⊢
    rw [degree_deleteIncidenceSet_eq_of_not_adj G hstartFar.1 hstartFar.2]
    exact hthree
  · have hthree := hq.end_three
    unfold IsThreeVertex at hthree ⊢
    rw [degree_deleteIncidenceSet_eq_of_not_adj G hendFar.1 hendFar.2]
    exact hthree
  · intro i hi0 hil
    have hilG : i < q.length := by simpa [hlength] using hil
    have hfar := twoThread_vertex_far_from_threeThread_middle G hq h
      (q.getVert_mem_support i)
    unfold IsTwoVertex
    rw [hget i, degree_deleteIncidenceSet_eq_of_not_adj G hfar.1 hfar.2]
    exact IsKThread.internal_two G hq hi0 hilG

/-! ## External endpoint data across incidence deletion -/

/-- Every ambient edge incident with a vertex different from and
nonadjacent to `x` survives deletion of the incidence set of `x`. -/
theorem edge_mem_deleteIncidenceSet_of_incident_far
    {x u : V} (hux : u ≠ x) (hnadj : ¬ G.Adj u x)
    (e : G.edgeSet) (hue : u ∈ (e : Sym2 V)) :
    e.1 ∈ (G.deleteIncidenceSet x).edgeSet := by
  rw [edgeSet_deleteIncidenceSet]
  refine ⟨e.2, ?_⟩
  intro heInc
  have hxe : x ∈ (e : Sym2 V) :=
    (G.edge_mem_incidenceSet_iff (e := e)).mp heInc
  have huxAdj : G.Adj u x :=
    G.adj_of_mem_incidenceSet hux
      ((G.edge_mem_incidenceSet_iff (e := e)).mpr hue)
      ((G.edge_mem_incidenceSet_iff (e := e)).mpr hxe)
  exact hnadj huxAdj

/-- External-inducedness descends from a transported ambient colouring to
the smaller graph when the two designated thread edges correspond. -/
theorem externalEdgesInduced_small_of_transport
    {x u : V}
    (small : (G.deleteIncidenceSet x).edgeSet → OneTwoColor 4)
    {threadH : (G.deleteIncidenceSet x).edgeSet}
    {threadG : G.edgeSet}
    (hthread : edgeEmbeddingOfLE (G.deleteIncidenceSet_le x) threadH =
      threadG)
    (hamb : ExternalEdgesInduced G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le x) small)
      u threadG) :
    ExternalEdgesInduced (G.deleteIncidenceSet x) small u threadH := by
  intro e he
  let eG : G.edgeSet := edgeEmbeddingOfLE (G.deleteIncidenceSet_le x) e
  have heG : IsExternalAt G u threadG eG := by
    refine ⟨he.1, ?_⟩
    intro heq
    apply he.2
    apply (edgeEmbeddingOfLE (G.deleteIncidenceSet_le x)).injective
    exact heq.trans hthread.symm
  obtain ⟨i, hi⟩ := hamb eG heG
  refine ⟨i, ?_⟩
  simpa [eG] using hi

/-- At an endpoint far from the deleted vertex, the external induced-colour
set of a surviving thread edge is exactly the corresponding ambient set
under the transported colouring. -/
theorem externalInducedColors_deleteIncidenceSet_eq_transport
    {x u : V} (hux : u ≠ x) (hnadj : ¬ G.Adj u x)
    (small : (G.deleteIncidenceSet x).edgeSet → OneTwoColor 4)
    {threadH : (G.deleteIncidenceSet x).edgeSet}
    {threadG : G.edgeSet}
    (hthread : edgeEmbeddingOfLE (G.deleteIncidenceSet_le x) threadH =
      threadG) :
    ExternalInducedColors (G.deleteIncidenceSet x) small u threadH =
      ExternalInducedColors G
        (transportColoringToSupergraph (G.deleteIncidenceSet_le x) small)
        u threadG := by
  ext i
  constructor
  · rintro ⟨e, he, hi⟩
    let eG : G.edgeSet := edgeEmbeddingOfLE (G.deleteIncidenceSet_le x) e
    refine ⟨eG, ?_, ?_⟩
    · refine ⟨he.1, ?_⟩
      intro heq
      apply he.2
      apply (edgeEmbeddingOfLE (G.deleteIncidenceSet_le x)).injective
      exact heq.trans hthread.symm
    · simpa [eG] using hi
  · rintro ⟨e, he, hi⟩
    have heH : e.1 ∈ (G.deleteIncidenceSet x).edgeSet :=
      edge_mem_deleteIncidenceSet_of_incident_far G hux hnadj e he.1
    let eH : (G.deleteIncidenceSet x).edgeSet := ⟨e.1, heH⟩
    have heEmbed :
        edgeEmbeddingOfLE (G.deleteIncidenceSet_le x) eH = e := by
      apply Subtype.ext
      rfl
    refine ⟨eH, ?_, ?_⟩
    · refine ⟨he.1, ?_⟩
      intro heq
      apply he.2
      have heqG : edgeEmbeddingOfLE (G.deleteIncidenceSet_le x) eH =
          edgeEmbeddingOfLE (G.deleteIncidenceSet_le x) threadH :=
        congrArg (edgeEmbeddingOfLE (G.deleteIncidenceSet_le x)) heq
      exact heEmbed.symm.trans (heqG.trans hthread)
    ·
      rw [← heEmbed] at hi
      simpa [eH] using hi

/-- Condition 3 transports completely across deletion of the middle vertex
of a certified 3-thread.  The key structural point is that an ambient
2-thread cannot meet any of the three internal vertices of that 3-thread. -/
theorem conditionThree_transport_deleteThreeThreadMiddle
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : ConditionThree (deleteThreeThreadMiddle G v₂) small) :
    ConditionThree G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) := by
  intro r s q hq hleft hright
  obtain ⟨qH, hqH, hget⟩ :=
    exists_twoThread_deleteThreeThreadMiddle G hq h
  let firstH : (G.deleteIncidenceSet v₂).edgeSet :=
    threadFirstEdge (G.deleteIncidenceSet v₂) qH hqH
  let firstG : G.edgeSet := threadFirstEdge G q hq
  let lastH : (G.deleteIncidenceSet v₂).edgeSet :=
    threadLastEdge (G.deleteIncidenceSet v₂) qH hqH
  let lastG : G.edgeSet := threadLastEdge G q hq
  have hfirst : edgeEmbeddingOfLE (G.deleteIncidenceSet_le v₂) firstH =
      firstG := by
    apply Subtype.ext
    simp [firstH, firstG, threadFirstEdge, hget]
  have hlast : edgeEmbeddingOfLE (G.deleteIncidenceSet_le v₂) lastH =
      lastG := by
    apply Subtype.ext
    simp [lastH, lastG, threadLastEdge, hget]
  have hleftH : ExternalEdgesInduced (G.deleteIncidenceSet v₂) small r
      firstH := by
    apply externalEdgesInduced_small_of_transport G small hfirst
    simpa [firstG] using hleft
  have hrightH : ExternalEdgesInduced (G.deleteIncidenceSet v₂) small s
      lastH := by
    apply externalEdgesInduced_small_of_transport G small hlast
    simpa [lastG] using hright
  have hneH := hsmall r s qH hqH hleftH hrightH
  have hrFar := twoThread_vertex_far_from_threeThread_middle G hq h
    q.start_mem_support
  have hsFar := twoThread_vertex_far_from_threeThread_middle G hq h
    q.end_mem_support
  have hleftEq := externalInducedColors_deleteIncidenceSet_eq_transport G
    hrFar.1 hrFar.2 small hfirst
  have hrightEq := externalInducedColors_deleteIncidenceSet_eq_transport G
    hsFar.1 hsFar.2 small hlast
  simpa [firstH, firstG, lastH, lastG, hleftEq, hrightEq] using hneH

/-! ## Locality of Condition 3

Unlike Condition 2, Condition 3 is indexed by certified 2-threads.  A
recolouring can change its conclusion only if it changes an external edge
at one of the two endpoints.  The following support predicate and locality
theorem make this finite obligation explicit. -/

/-- A recolouring support meets one of the external edge sets occurring in
Condition 3 for a fixed certified 2-thread. -/
def ThreadConditionAffectedBy (S : Set G.edgeSet)
    {u₁ u₂ : V} (p : G.Walk u₁ u₂) (hp : IsKThread G p 2) : Prop :=
  (∃ e, e ∈ S ∧ IsExternalAt G u₁ (threadFirstEdge G p hp) e) ∨
    (∃ e, e ∈ S ∧ IsExternalAt G u₂ (threadLastEdge G p hp) e)

/-- Agreement away from `S` preserves the assertion that every external
edge is induced, provided `S` misses that external edge set. -/
theorem externalEdgesInduced_of_agreeOff
    {S : Set G.edgeSet} {old new : G.edgeSet → OneTwoColor 4}
    (hagree : ColoringsAgreeOff G S old new)
    {u : V} {threadEdge : G.edgeSet}
    (hmiss : ∀ e, IsExternalAt G u threadEdge e → e ∉ S)
    (hold : ExternalEdgesInduced G old u threadEdge) :
    ExternalEdgesInduced G new u threadEdge := by
  intro e he
  obtain ⟨i, hi⟩ := hold e he
  exact ⟨i, (hagree e (hmiss e he)).symm.trans hi⟩

/-- Under the same support-disjointness hypothesis, the unordered external
induced-colour set is unchanged. -/
theorem externalInducedColors_eq_of_agreeOff
    {S : Set G.edgeSet} {old new : G.edgeSet → OneTwoColor 4}
    (hagree : ColoringsAgreeOff G S old new)
    {u : V} {threadEdge : G.edgeSet}
    (hmiss : ∀ e, IsExternalAt G u threadEdge e → e ∉ S) :
    ExternalInducedColors G old u threadEdge =
      ExternalInducedColors G new u threadEdge := by
  ext i
  constructor
  · rintro ⟨e, he, hi⟩
    exact ⟨e, he, (hagree e (hmiss e he)).symm.trans hi⟩
  · rintro ⟨e, he, hi⟩
    exact ⟨e, he, (hagree e (hmiss e he)).trans hi⟩

/-- To preserve Condition 3 under a local recolouring, it is enough to
check the certified 2-threads whose external edge sets meet the support. -/
theorem ConditionThree.of_agreeOff
    {S : Set G.edgeSet} {old new : G.edgeSet → OneTwoColor 4}
    (hold : ConditionThree G old)
    (hagree : ColoringsAgreeOff G S old new)
    (hcheck : ∀ (u₁ u₂ : V) (p : G.Walk u₁ u₂)
        (hp : IsKThread G p 2),
      ThreadConditionAffectedBy G S p hp →
      ExternalEdgesInduced G new u₁ (threadFirstEdge G p hp) →
      ExternalEdgesInduced G new u₂ (threadLastEdge G p hp) →
      ExternalInducedColors G new u₁ (threadFirstEdge G p hp) ≠
        ExternalInducedColors G new u₂ (threadLastEdge G p hp)) :
    ConditionThree G new := by
  intro u₁ u₂ p hp hleft hright
  by_cases haffect : ThreadConditionAffectedBy G S p hp
  · exact hcheck u₁ u₂ p hp haffect hleft hright
  · have hmissLeft : ∀ e,
        IsExternalAt G u₁ (threadFirstEdge G p hp) e → e ∉ S := by
      intro e he heS
      exact haffect (Or.inl ⟨e, heS, he⟩)
    have hmissRight : ∀ e,
        IsExternalAt G u₂ (threadLastEdge G p hp) e → e ∉ S := by
      intro e he heS
      exact haffect (Or.inr ⟨e, heS, he⟩)
    have hleftOld :
        ExternalEdgesInduced G old u₁ (threadFirstEdge G p hp) := by
      exact externalEdgesInduced_of_agreeOff G
        (S := S) (old := new) (new := old)
        (fun e he ↦ (hagree e he).symm) hmissLeft hleft
    have hrightOld :
        ExternalEdgesInduced G old u₂ (threadLastEdge G p hp) := by
      exact externalEdgesInduced_of_agreeOff G
        (S := S) (old := new) (new := old)
        (fun e he ↦ (hagree e he).symm) hmissRight hright
    have hne := hold u₁ u₂ p hp hleftOld hrightOld
    rw [externalInducedColors_eq_of_agreeOff G hagree hmissLeft,
      externalInducedColors_eq_of_agreeOff G hagree hmissRight] at hne
    exact hne

/-! ## Transporting the two elementary goodness conditions -/

/-- A degree-two vertex whose two neighbours are degree two sees at most
four ambient edges. -/
theorem longPair_card_visible_le_four
    {q a b : V} (hq : IsTwoVertex G q)
    (hqa : G.Adj q a) (hqb : G.Adj q b) (hab : a ≠ b)
    (ha : IsTwoVertex G a) (hb : IsTwoVertex G b) :
    (vertexVisibleEdgeFinset G q).card ≤ 4 := by
  classical
  have hN : G.neighborFinset q = {a, b} :=
    neighborFinset_eq_pair_of_isTwoVertex G hq hqa hqb hab
  calc
    (vertexVisibleEdgeFinset G q).card ≤
        ∑ v ∈ G.neighborFinset q, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = G.degree a + G.degree b := by
      rw [hN]
      simp [hab, SimpleGraph.card_incidenceFinset_eq_degree]
    _ = 4 := by rw [ha, hb]

/-- One visible matching edge and all four induced colours require five
different visible graph edges. -/
theorem longPair_five_le_card_visible_of_full_palette
    {colour : G.edgeSet → OneTwoColor 4} {q : V}
    (hmatch : VertexSeesMatching G colour q)
    (hall : ∀ i : Fin 4, VertexSeesInduced G colour q i) :
    5 ≤ (vertexVisibleEdgeFinset G q).card := by
  classical
  obtain ⟨m, hm, hqm⟩ := (vertexSeesMatching_iff G colour q).mp hmatch
  choose f hf v hv hclose using fun i ↦
    (vertexSeesInduced_iff G colour q i).mp (hall i)
  let witness : OneTwoColor 4 → G.edgeSet
    | none => m
    | some i => f i
  have hwcolour (c : OneTwoColor 4) : colour (witness c) = c := by
    cases c with
    | none => exact hm
    | some i => exact hf i
  have hwmem (c : OneTwoColor 4) :
      (witness c : Sym2 V) ∈ vertexVisibleEdgeFinset G q := by
    cases c with
    | none =>
        exact mem_vertexVisibleEdgeFinset_of_endpoint_close G hqm (Or.inl rfl)
    | some i =>
        exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (hv i) (hclose i)
  let intoVisible : OneTwoColor 4 ↪
      {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q} :=
    { toFun := fun c => ⟨witness c, hwmem c⟩
      inj' := by
        intro r s hrs
        have hval : (witness r : Sym2 V) = (witness s : Sym2 V) :=
          congrArg (fun e : {e : Sym2 V //
            e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs
        have hedge : witness r = witness s := Subtype.ext hval
        exact (hwcolour r).symm.trans
          ((congrArg colour hedge).trans (hwcolour s)) }
  have hcard := Fintype.card_le_of_injective intoVisible intoVisible.injective
  simpa using hcard

/-- At a degree-two vertex with two degree-two neighbours, Condition 2 is
automatic whenever the matching colour is visible. -/
theorem longPair_paletteCondition_at_two_two_neighbours
    {colour : G.edgeSet → OneTwoColor 4}
    {q a b : V} (hq : IsTwoVertex G q)
    (hqa : G.Adj q a) (hqb : G.Adj q b) (hab : a ≠ b)
    (ha : IsTwoVertex G a) (hb : IsTwoVertex G b)
    (hmatch : VertexSeesMatching G colour q) :
    ¬ ∀ i : Fin 4, VertexSeesInduced G colour q i := by
  intro hall
  have hfive := longPair_five_le_card_visible_of_full_palette G hmatch hall
  have hfour := longPair_card_visible_le_four G hq hqa hqb hab ha hb
  omega

/-- Two distinct visible matching edges together with all four induced
colours require six distinct visible graph edges. -/
theorem longPair_six_le_card_visible_of_two_matching
    {colour : G.edgeSet → OneTwoColor 4} {q : V}
    (m n : G.edgeSet) (hmn : m ≠ n)
    (hm : colour m = none) (hn : colour n = none)
    (hmvis : (m : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hnvis : (n : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hall : ∀ i : Fin 4, VertexSeesInduced G colour q i) :
    6 ≤ (vertexVisibleEdgeFinset G q).card := by
  classical
  choose f hfcolour v hv hclose using fun i ↦
    (vertexSeesInduced_iff G colour q i).mp (hall i)
  have hfvis (i : Fin 4) :
      (f i : Sym2 V) ∈ vertexVisibleEdgeFinset G q :=
    mem_vertexVisibleEdgeFinset_of_endpoint_close G (hv i) (hclose i)
  let witness : Option (Option (Fin 4)) →
      {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G q}
    | none => ⟨m, hmvis⟩
    | some none => ⟨n, hnvis⟩
    | some (some i) => ⟨f i, hfvis i⟩
  have hinj : Function.Injective witness := by
    intro r s hrs
    cases r with
    | none =>
      cases s with
      | none => rfl
      | some s =>
        cases s with
        | none =>
          exfalso
          apply hmn
          apply Subtype.ext
          exact congrArg (fun e : {e : Sym2 V //
            e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs
        | some j =>
          exfalso
          have hedge : m = f j := by
            apply Subtype.ext
            exact congrArg (fun e : {e : Sym2 V //
              e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs
          have hc := hm.symm.trans
            ((congrArg colour hedge).trans (hfcolour j))
          simp at hc
    | some r =>
      cases r with
      | none =>
        cases s with
        | none =>
          exfalso
          apply hmn
          apply Subtype.ext
          exact (congrArg (fun e : {e : Sym2 V //
            e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs).symm
        | some s =>
          cases s with
          | none => rfl
          | some j =>
            exfalso
            have hedge : n = f j := by
              apply Subtype.ext
              exact congrArg (fun e : {e : Sym2 V //
                e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs
            have hc := hn.symm.trans
              ((congrArg colour hedge).trans (hfcolour j))
            simp at hc
      | some i =>
        cases s with
        | none =>
          exfalso
          have hedge : f i = m := by
            apply Subtype.ext
            exact congrArg (fun e : {e : Sym2 V //
              e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs
          have hc := (hfcolour i).symm.trans
            ((congrArg colour hedge).trans hm)
          simp at hc
        | some s =>
          cases s with
          | none =>
            exfalso
            have hedge : f i = n := by
              apply Subtype.ext
              exact congrArg (fun e : {e : Sym2 V //
                e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs
            have hc := (hfcolour i).symm.trans
              ((congrArg colour hedge).trans hn)
            simp at hc
          | some j =>
            congr
            have hedge : f i = f j := by
              apply Subtype.ext
              exact congrArg (fun e : {e : Sym2 V //
                e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs
            exact Option.some.inj ((hfcolour i).symm.trans
              ((congrArg colour hedge).trans (hfcolour j)))
  have hcard := Fintype.card_le_of_injective witness hinj
  simpa using hcard

/-- At a degree-two vertex adjacent to a degree-two vertex, two distinct
visible matching edges force Condition 2. -/
theorem longPair_paletteCondition_at_two_visible_matching
    (hsub : IsSubcubic G) {colour : G.edgeSet → OneTwoColor 4}
    {q r : V} (hq : IsTwoVertex G q) (hqr : G.Adj q r)
    (hr : IsTwoVertex G r)
    (m n : G.edgeSet) (hmn : m ≠ n)
    (hm : colour m = none) (hn : colour n = none)
    (hmvis : (m : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hnvis : (n : Sym2 V) ∈ vertexVisibleEdgeFinset G q) :
    ¬ ∀ i : Fin 4, VertexSeesInduced G colour q i := by
  intro hall
  have hsix := longPair_six_le_card_visible_of_two_matching G
    m n hmn hm hn hmvis hnvis hall
  have hfive := card_vertexVisibleEdgeFinset_le_five G hsub hq hqr hr
  omega

/-- Inclusion-maximality of the matching class survives the common middle
deletion: transported non-retained edges are matching-coloured, and every
retained induced edge keeps the retained matching witness supplied by the
smaller saturated colouring. -/
theorem oneSaturated_transport_deleteThreeThreadMiddle
    {u v₁ v₂ v₃ z : V}
    (_h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : OneSaturated (deleteThreeThreadMiddle G v₂) small) :
    OneSaturated G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) := by
  intro e he
  have heH : e.1 ∈ (G.deleteIncidenceSet v₂).edgeSet := by
    by_contra hnot
    apply he
    simp [transportColoringToSupergraph, hnot]
  let eH : (G.deleteIncidenceSet v₂).edgeSet := ⟨e.1, heH⟩
  have hecolour : small eH ≠ none := by
    intro hnone
    apply he
    rw [transportColoringToSupergraph_of_mem
      (G.deleteIncidenceSet_le v₂) small heH]
    exact hnone
  obtain ⟨f, hf, v, hve, hvf⟩ := hsmall eH hecolour
  let fG : G.edgeSet := edgeEmbeddingOfLE (G.deleteIncidenceSet_le v₂) f
  refine ⟨fG, ?_, v, hve, hvf⟩
  simpa [fG] using hf

/-- The default matching colours on the two deleted edges make Condition 2
valid at all three changed vertices.  Away from those vertices degree and
colour visibility transport exactly from the smaller graph. -/
theorem conditionTwo_transport_deleteThreeThreadMiddle
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : ConditionTwo (deleteThreeThreadMiddle G v₂) small) :
    ConditionTwo G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) := by
  classical
  let base := transportColoringToSupergraph
    (G.deleteIncidenceSet_le v₂) small
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  have hAnot : A ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [A] using left_chain_edge_not_retained G h.left_adj
  have hBnot : B ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [B] using right_chain_edge_not_retained G h.right_adj
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hAedge : A.1 ∉ (G.deleteIncidenceSet v₂).edgeSet := by
    simpa [RetainedEdges] using hAnot
  have hBedge : B.1 ∉ (G.deleteIncidenceSet v₂).edgeSet := by
    simpa [RetainedEdges] using hBnot
  have hA : base A = none := by
    simp [base, transportColoringToSupergraph, hAedge]
  have hB : base B = none := by
    simp [base, transportColoringToSupergraph, hBedge]
  intro q hq hmatch hall
  by_cases hq₁ : q = v₁
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub h.first_two
      h.left_adj h.middle_two A B hAB hA hB
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [A])
        (Or.inl rfl)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
        (Or.inr h.left_adj)
    · exact hall
  by_cases hq₂ : q = v₂
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  by_cases hq₃ : q = v₃
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub h.third_two
      h.right_adj.symm h.middle_two B A hAB.symm hB hA
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
        (Or.inl rfl)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [A])
        (Or.inr h.right_adj.symm)
    · exact hall
  have hn₂ : ¬ G.Adj q v₂ := by
    intro hadj
    have hmem : q ∈ G.neighborFinset v₂ :=
      (G.mem_neighborFinset v₂ q).mpr hadj.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third] at hmem
    have hcases : q = v₁ ∨ q = v₃ := by simpa using hmem
    exact hcases.elim hq₁ hq₃
  have hqSmall : IsTwoVertex (deleteThreeThreadMiddle G v₂) q := by
    unfold IsTwoVertex at hq ⊢
    rw [degree_deleteIncidenceSet_eq_of_not_adj G hq₂ hn₂]
    exact hq
  apply hsmall q hqSmall
  · exact (vertexSeesMatching_transport_deleteIncidenceSet_iff_of_not_adj G
      hq₂ hn₂ small).mp hmatch
  · intro i
    exact (vertexSeesInduced_transport_deleteIncidenceSet_iff_of_not_adj G
      hq₂ hn₂ small i).mp (hall i)

/-! ## The prepared ambient gap -/

/-- All information supplied by a smaller good colouring before the two
gap edges are restored.  Validity is deliberately restricted to retained
edges; the three global auxiliary conditions already hold on the ambient
graph. -/
def PreparedThreeThreadGap
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (base : G.edgeSet → OneTwoColor 4) : Prop :=
  IsOneTwoColoringOn G
      (RetainedEdges (deleteThreeThreadMiddle G v₂) G) base ∧
    OneSaturated G base ∧ ConditionTwo G base ∧ ConditionThree G base

/-- A good colouring of the incidence-deleted graph produces a prepared
ambient gap. -/
theorem preparedThreeThreadGap_of_goodFour
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small) :
    PreparedThreeThreadGap G h
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) := by
  refine ⟨transport_deleteThreeThreadMiddle_valid G h hsmall.valid,
    oneSaturated_transport_deleteThreeThreadMiddle G h small hsmall.oneSaturated,
    conditionTwo_transport_deleteThreeThreadMiddle G hsub h small
      hsmall.paletteCondition,
    conditionThree_transport_deleteThreeThreadMiddle G h small
      hsmall.conditionThree⟩

/-! ## Local obligations for a gap-only recolouring -/

theorem isThreeVertex_ne_isTwoVertex
    {a b : V} (ha : IsThreeVertex G a) (hb : IsTwoVertex G b) : a ≠ b := by
  intro hab
  unfold IsThreeVertex at ha
  unfold IsTwoVertex at hb
  rw [hab] at ha
  omega

/-- Only the five displayed vertices can see a change supported on the two
gap edges. -/
theorem paletteAffectedBy_threeThread_gap
    {u v₁ v₂ v₃ z q : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (haffect : PaletteAffectedBy G
      ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet) q) :
    q = u ∨ q = v₁ ∨ q = v₂ ∨ q = v₃ ∨ q = z := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, he, y, hye, hqy⟩ := haffect
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  have nearV₁ (hadj : G.Adj q v₁) : q = u ∨ q = v₂ := by
    have hqN : q ∈ G.neighborFinset v₁ :=
      (G.mem_neighborFinset v₁ q).mpr hadj.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
      h.first_adj.symm h.left_adj h.middle_ne_start.symm] at hqN
    simpa using hqN
  have nearV₂ (hadj : G.Adj q v₂) : q = v₁ ∨ q = v₃ := by
    have hqN : q ∈ G.neighborFinset v₂ :=
      (G.mem_neighborFinset v₂ q).mpr hadj.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third] at hqN
    simpa using hqN
  have nearV₃ (hadj : G.Adj q v₃) : q = z ∨ q = v₂ := by
    have hqN : q ∈ G.neighborFinset v₃ :=
      (G.mem_neighborFinset v₃ q).mpr hadj.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G h.third_two
      h.last_adj h.right_adj.symm h.middle_ne_end.symm] at hqN
    simpa using hqN
  rcases he with rfl | rfl
  · have hy : y = v₁ ∨ y = v₂ := by simpa using hye
    rcases hqy with rfl | hqy
    · rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · rcases hy with rfl | rfl
      · rcases nearV₁ hqy with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases nearV₂ hqy with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · have hy : y = v₃ ∨ y = v₂ := by simpa using hye
    rcases hqy with rfl | hqy
    · rcases hy with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inl rfl))
    · rcases hy with rfl | rfl
      · rcases nearV₃ hqy with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases nearV₂ hqy with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-- If the affected vertex is degree two, the two degree-three endpoints
drop out of the preceding five-vertex list. -/
theorem twoVertex_paletteAffectedBy_threeThread_gap
    {u v₁ v₂ v₃ z q : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet) q) :
    q = v₁ ∨ q = v₂ ∨ q = v₃ := by
  rcases paletteAffectedBy_threeThread_gap G h haffect with
    rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((isThreeVertex_ne_isTwoVertex G h.start_three hq) rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact False.elim ((isThreeVertex_ne_isTwoVertex G h.end_three hq) rfl)

/-- A gap edge cannot be external to an endpoint of a certified 2-thread,
because both endpoints of each gap edge have degree two. -/
theorem not_threadConditionAffectedBy_threeThread_gap
    {u v₁ v₂ v₃ z r s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (p : G.Walk r s) (hp : IsKThread G p 2) :
    ¬ ThreadConditionAffectedBy G
      ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet) p hp := by
  intro haffect
  rcases haffect with ⟨e, he, her⟩ | ⟨e, he, hes⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · have hr : r = v₁ ∨ r = v₂ := by simpa using her.1
      exact hr.elim (isThreeVertex_ne_isTwoVertex G hp.start_three h.first_two)
        (isThreeVertex_ne_isTwoVertex G hp.start_three h.middle_two)
    · have hr : r = v₃ ∨ r = v₂ := by simpa using her.1
      exact hr.elim (isThreeVertex_ne_isTwoVertex G hp.start_three h.third_two)
        (isThreeVertex_ne_isTwoVertex G hp.start_three h.middle_two)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · have hs : s = v₁ ∨ s = v₂ := by simpa using hes.1
      exact hs.elim (isThreeVertex_ne_isTwoVertex G hp.end_three h.first_two)
        (isThreeVertex_ne_isTwoVertex G hp.end_three h.middle_two)
    · have hs : s = v₃ ∨ s = v₂ := by simpa using hes.1
      exact hs.elim (isThreeVertex_ne_isTwoVertex G hp.end_three h.third_two)
        (isThreeVertex_ne_isTwoVertex G hp.end_three h.middle_two)

/-! ## A complete gap-only assembly theorem -/

/-- Once a colouring of the two gap edges is packing-valid, only three
Condition-2 checks and saturation witnesses for induced-coloured gap edges
remain.  Condition 3 is automatic because a gap edge has only degree-two
endpoints and therefore cannot be external to a certified 2-thread. -/
theorem goodFour_of_threeThread_gap_recolour
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (final : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoring G final)
    (hagree : ColoringsAgreeOff G
      ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet)
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small)
      final)
    (hnewSaturated : ∀ e : G.edgeSet,
      e ∈ ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet) →
      final e ≠ none →
      ∃ f, final f = none ∧
        ∃ y, y ∈ (e : Sym2 V) ∧ y ∈ (f : Sym2 V))
    (hpalette : ∀ q : V, q = v₁ ∨ q = v₂ ∨ q = v₃ →
      VertexSeesMatching G final q →
      ¬ ∀ i : Fin 4, VertexSeesInduced G final q i) :
    GoodFour G final := by
  classical
  let H := deleteThreeThreadMiddle G v₂
  let D : Set G.edgeSet := RetainedEdges H G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let S : Set G.edgeSet := {A, B}
  have hprepared : PreparedThreeThreadGap G h base := by
    exact preparedThreeThreadGap_of_goodFour G hsub h small hsmall
  have hAD : A ∉ D := by
    simpa [H, D, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ D := by
    simpa [H, D, B] using right_chain_edge_not_retained G h.right_adj
  have hcover : insert B (insert A D) = Set.univ := by
    simpa [H, D, A, B] using insert_threeThread_gap_retained_eq_univ G h
  refine ⟨hvalid, ?_, ?_, ?_⟩
  · intro e he
    by_cases heS : e ∈ S
    · exact hnewSaturated e (by simpa [S, A, B] using heS) he
    · have heA : e ≠ A := by
        intro hEq
        subst e
        exact heS (by simp [S])
      have heB : e ≠ B := by
        intro hEq
        subst e
        exact heS (by simp [S])
      have heD : e ∈ D := by
        have heCover : e ∈ insert B (insert A D) := by rw [hcover]; simp
        simpa [heA, heB] using heCover
      have hbaseE : base e ≠ none := by
        intro hnone
        apply he
        exact (hagree e (by simpa [S, A, B] using heS)).symm.trans hnone
      let eH : H.edgeSet := ⟨e.1, heD⟩
      have hbaseApply : base e = small eH := by
        change e.1 ∈ H.edgeSet at heD
        dsimp [base]
        rw [transportColoringToSupergraph_of_mem
          (G.deleteIncidenceSet_le v₂) small heD]
      have heH : small eH ≠ none := by
        intro hnone
        exact hbaseE (hbaseApply.trans hnone)
      have hsatH : OneSaturated H small := by
        exact GoodFour.oneSaturated (deleteThreeThreadMiddle G v₂) hsmall
      obtain ⟨fH, hfH, y, hye, hyf⟩ := hsatH eH heH
      let f : G.edgeSet := edgeEmbeddingOfLE (G.deleteIncidenceSet_le v₂) fH
      have hfD : f ∈ D := by
        exact edgeEmbeddingOfLE_mem_retained (G.deleteIncidenceSet_le v₂) fH
      have hfA : f ≠ A := fun hEq ↦ hAD (hEq ▸ hfD)
      have hfB : f ≠ B := fun hEq ↦ hBD (hEq ▸ hfD)
      have hbaseF : base f = none := by simpa [H, base, f] using hfH
      have hfinalF : final f = none :=
        (hagree f (by
          intro hf
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
          rcases hf with hf | hf
          · exact hfA (by simpa [A] using hf)
          · exact hfB (by simpa [B] using hf))).symm.trans hbaseF
      exact ⟨f, hfinalF, y, hye, hyf⟩
  · apply hprepared.2.2.1.of_agreeOff G (S := S)
    · simpa [S, A, B, base] using hagree
    · intro q hq haffect hmatch hall
      have hqcase : q = v₁ ∨ q = v₂ ∨ q = v₃ := by
        apply twoVertex_paletteAffectedBy_threeThread_gap G h hq
        simpa [S, A, B] using haffect
      exact hpalette q hqcase hmatch hall
  · apply hprepared.2.2.2.of_agreeOff G (S := S)
    · simpa [S, A, B, base] using hagree
    · intro r s p hp haffect
      exfalso
      apply not_threadConditionAffectedBy_threeThread_gap G h p hp
      simpa [S, A, B] using haffect

/-! ## The four easy outer-colour cases -/

/-- The geometric blocker description from the three-chain API is
independent of the palette size. -/
theorem longPair_inducedBlockerEdgesOn_left_subset {k : ℕ}
    {a x b u w : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hau : G.Adj a u) (hxu : x ≠ u)
    (hbw : G.Adj b w) (hxw : x ≠ w)
    {colour : G.edgeSet → OneTwoColor k} :
    inducedBlockerEdgesOn G (RetainedEdges (G.deleteIncidenceSet x) G)
        colour (⟨s(a, x), hax⟩ : G.edgeSet) ⊆
      insert (⟨s(b, w), hbw⟩ : G.edgeSet) (incidentEdgeFinset G u) := by
  have h := inducedBlockerEdgesOn_left_subset G ha hx hb hax hxb hab hau hxu
    hbw hxw (colour := fun _ ↦ (none : OneTwoColor 5))
  simpa only [inducedBlockerEdgesOn] using h

/-- Reverse the ordered core of a 3-thread. -/
def ThreeThreadCore.reverse
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z) :
    ThreeThreadCore G z v₃ v₂ v₁ u where
  start_three := h.end_three
  end_three := h.start_three
  first_two := h.third_two
  middle_two := h.middle_two
  third_two := h.first_two
  first_adj := h.last_adj.symm
  left_adj := h.right_adj.symm
  right_adj := h.left_adj.symm
  last_adj := h.first_adj.symm
  first_ne_third := h.first_ne_third.symm
  middle_ne_start := h.middle_ne_end
  middle_ne_end := h.middle_ne_start

/-- Saturation in the smaller graph supplies a retained matching edge at
the far endpoint of the selected 3-thread.  If the outer thread edge is
already matching it is the witness; otherwise its saturation witness must
lie at the degree-three endpoint, since the other endpoint has degree one
after deletion. -/
theorem exists_retained_matching_incident_threeThread_end
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsat : OneSaturated (deleteThreeThreadMiddle G v₂) small) :
    ∃ f : G.edgeSet,
      f ∈ RetainedEdges (deleteThreeThreadMiddle G v₂) G ∧
      transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small f = none ∧
      z ∈ (f : Sym2 V) := by
  let H := deleteThreeThreadMiddle G v₂
  have hRmem : s(v₃, z) ∈ H.edgeSet := by
    rw [edgeSet_deleteIncidenceSet]
    refine ⟨h.last_adj, ?_⟩
    intro hinc
    have hv₂ : v₂ ∈ (s(v₃, z) : Sym2 V) :=
      (G.edge_mem_incidenceSet_iff
        (e := (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))).mp hinc
    have hcases : v₂ = v₃ ∨ v₂ = z := by simpa using hv₂
    exact hcases.elim h.right_adj.ne h.middle_ne_end
  let RH : H.edgeSet := ⟨s(v₃, z), hRmem⟩
  let R : G.edgeSet := edgeEmbeddingOfLE (G.deleteIncidenceSet_le v₂) RH
  by_cases hR : small RH = none
  · refine ⟨R, edgeEmbeddingOfLE_mem_retained _ RH, ?_, ?_⟩
    · simpa [R] using hR
    · simp [R, RH]
  · obtain ⟨fH, hfH, y, hyR, hyf⟩ := hsat RH hR
    let f : G.edgeSet := edgeEmbeddingOfLE (G.deleteIncidenceSet_le v₂) fH
    have hfD : f ∈ RetainedEdges H G :=
      edgeEmbeddingOfLE_mem_retained _ fH
    have hbasef :
        transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small f = none := by
      simpa [f] using hfH
    have hycases : y = v₃ ∨ y = z := by simpa [RH] using hyR
    rcases hycases with hyv₃ | hyz
    · have hv₃f : v₃ ∈ (f : Sym2 V) := by
        change v₃ ∈ (fH : Sym2 V)
        simpa [hyv₃] using hyf
      have hfEqR : f = (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) := by
        exact retained_edge_eq_external_of_incident_two G h.third_two
          h.right_adj.symm h.last_adj h.middle_ne_end f hfD hv₃f
      have hREmbed : R = (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) := by
        apply Subtype.ext
        rfl
      have hfHRH : fH = RH := by
        apply (edgeEmbeddingOfLE (G.deleteIncidenceSet_le v₂)).injective
        exact hfEqR.trans hREmbed.symm
      exact False.elim (hR (hfHRH ▸ hfH))
    · refine ⟨f, hfD, hbasef, ?_⟩
      change z ∈ (fH : Sym2 V)
      simpa [hyz] using hyf

/-- The symmetric retained matching witness at the first endpoint. -/
theorem exists_retained_matching_incident_threeThread_start
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsat : OneSaturated (deleteThreeThreadMiddle G v₂) small) :
    ∃ f : G.edgeSet,
      f ∈ RetainedEdges (deleteThreeThreadMiddle G v₂) G ∧
      transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small f = none ∧
      u ∈ (f : Sym2 V) := by
  exact exists_retained_matching_incident_threeThread_end G
    (ThreeThreadCore.reverse G h) small hsat

/-- Palette-size-independent right-gap blocker geometry. -/
theorem longPair_inducedBlockerEdgesOn_right_subset {k : ℕ}
    {a x b u w : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hau : G.Adj a u) (hxu : x ≠ u)
    (hbw : G.Adj b w) (hxw : x ≠ w)
    {colour : G.edgeSet → OneTwoColor k} :
    inducedBlockerEdgesOn G
        (insert (⟨s(a, x), hax⟩ : G.edgeSet)
          (RetainedEdges (G.deleteIncidenceSet x) G))
        colour (⟨s(b, x), hxb.symm⟩ : G.edgeSet) ⊆
      insert (⟨s(a, x), hax⟩ : G.edgeSet)
        (insert (⟨s(a, u), hau⟩ : G.edgeSet)
          (incidentEdgeFinset G w)) := by
  have h := inducedBlockerEdgesOn_right_subset G ha hx hb hax hxb hab hau hxu
    hbw hxw (colour := fun _ ↦ (none : OneTwoColor 5))
  simpa only [inducedBlockerEdgesOn] using h

/-- If the left gap edge is matching-coloured and a matching witness is
available at the far endpoint, at most three active blockers remain for
the right gap edge.  Hence one of the four induced colours is available. -/
theorem exists_available_right_gap_after_left_matching
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (colour : G.edgeSet → OneTwoColor 4)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (m : G.edgeSet) (hm : colour m = none) (hzm : z ∈ (m : Sym2 V)) :
    ∃ i : Fin 4,
      ColorAvailableOn G
        (insert (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet)
          (RetainedEdges (G.deleteIncidenceSet v₂) G))
        colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)
        (some i) := by
  classical
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : Finset G.edgeSet :=
    insert P ((incidentEdgeFinset G z).erase m)
  have hblock : activeInducedBlockerEdgesOn G
      (insert A (RetainedEdges (G.deleteIncidenceSet v₂) G)) colour
      (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) ⊆ T := by
    intro f hf
    have hfparts := Finset.mem_filter.mp hf
    have hfgeom := longPair_inducedBlockerEdgesOn_right_subset G
      h.first_two h.middle_two h.third_two h.left_adj h.right_adj
      h.first_ne_third h.first_adj.symm h.middle_ne_start h.last_adj
      h.middle_ne_end hfparts.1
    rcases Finset.mem_insert.mp hfgeom with hfA | hfrest
    · subst f
      exact False.elim (hfparts.2 (by simpa [A] using hA))
    · rcases Finset.mem_insert.mp hfrest with hfP | hfinc
      · exact Finset.mem_insert.mpr (Or.inl (by simpa [P] using hfP))
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_erase.mpr
        refine ⟨?_, hfinc⟩
        intro hfm
        subst f
        exact hfparts.2 hm
  have hmInc : m ∈ incidentEdgeFinset G z :=
    (mem_incidentEdgeFinset (G := G)).mpr hzm
  have herase : ((incidentEdgeFinset G z).erase m).card + 1 = G.degree z := by
    rw [Finset.card_erase_of_mem hmInc, card_incidentEdgeFinset]
    have hzdeg : G.degree z = 3 := h.end_three
    omega
  have hTcard : T.card < 4 := by
    have hle : T.card ≤ ((incidentEdgeFinset G z).erase m).card + 1 :=
      Finset.card_insert_le _ _
    have hzdeg : G.degree z = 3 := h.end_three
    omega
  apply exists_available_induced_of_card_activeBlockers_lt G
  exact lt_of_le_of_lt (Finset.card_le_card hblock) hTcard

/-- If the outer edge at the first endpoint is induced-coloured, the
matching colour is available on the adjacent gap edge. -/
theorem matching_available_left_gap_of_outer_nonmatching
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (colour : G.edgeSet → OneTwoColor 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G (RetainedEdges (G.deleteIncidenceSet v₂) G)
      colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) none := by
  apply (colorAvailableOn_none_iff G _ _ _).mpr
  intro f hfD _ hf y hyA hyf
  have hycases : y = v₁ ∨ y = v₂ := by simpa using hyA
  rcases hycases with hyv₁ | hyv₂
  · have hv₁f : v₁ ∈ (f : Sym2 V) := by simpa [hyv₁] using hyf
    have hfEq : f = (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) :=
      retained_edge_eq_external_of_incident_two G h.first_two h.left_adj
        h.first_adj.symm h.middle_ne_start f hfD hv₁f
    exact hP (by simpa [hfEq] using hf)
  · have hv₂f : v₂ ∈ (f : Sym2 V) := by simpa [hyv₂] using hyf
    exact ((mem_retained_deleteIncidenceSet_iff G v₂ f).mp hfD) hv₂f

/-- A packing-valid gap filling with matching on the left gap and an
induced colour on the right gap automatically satisfies all three
auxiliary Section-4 conditions. -/
theorem goodFour_of_gap_left_matching_right_induced
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (final : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoring G final)
    (hagree : ColoringsAgreeOff G
      ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet)
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small)
      final)
    (hA : final (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : final (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) ≠ none) :
    GoodFour G final := by
  classical
  let D : Set G.edgeSet :=
    RetainedEdges (deleteThreeThreadMiddle G v₂) G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let S : Set G.edgeSet := {A, B}
  have hagree' : ColoringsAgreeOff G S base final := by
    simpa [S, A, B, base] using hagree
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ D := by
    simpa [D, B] using right_chain_edge_not_retained G h.right_adj
  have hretOff (f : G.edgeSet) (hfD : f ∈ D) : f ∉ S := by
    intro hf
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact hAD hfD
    · exact hBD hfD
  obtain ⟨mL, hmLD, hmLbase, humL⟩ :=
    exists_retained_matching_incident_threeThread_start G h small
      hsmall.oneSaturated
  obtain ⟨mR, hmRD, hmRbase, hzmR⟩ :=
    exists_retained_matching_incident_threeThread_end G h small
      hsmall.oneSaturated
  have hmLfinal : final mL = none :=
    (hagree' mL (hretOff mL (by simpa [D] using hmLD))).symm.trans hmLbase
  have hmRfinal : final mR = none :=
    (hagree' mR (hretOff mR (by simpa [D] using hmRD))).symm.trans hmRbase
  apply goodFour_of_threeThread_gap_recolour G hsub h small hsmall final
    hvalid hagree
  · intro e heS he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heS
    rcases heS with heA | heB
    · subst e
      exact False.elim (he hA)
    · subst e
      refine ⟨A, by simpa [A] using hA, v₂, ?_, ?_⟩
      · simp [B]
      · simp [A]
  · intro q hqcase hmatch hall
    rcases hqcase with rfl | rfl | rfl
    · apply longPair_paletteCondition_at_two_visible_matching G hsub
        h.first_two h.left_adj h.middle_two A mL
      · intro hEq
        exact hAD (by simpa [hEq, D] using hmLD)
      · simpa [A] using hA
      · exact hmLfinal
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G humL
          (Or.inr h.first_adj.symm)
      · exact hall
    · exact (longPair_paletteCondition_at_two_two_neighbours G
        h.middle_two h.left_adj.symm h.right_adj h.first_ne_third
        h.first_two h.third_two hmatch) hall
    · apply longPair_paletteCondition_at_two_visible_matching G hsub
        h.third_two h.right_adj.symm h.middle_two A mR
      · intro hEq
        exact hAD (by simpa [hEq, D] using hmRD)
      · simpa [A] using hA
      · exact hmRfinal
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inr h.right_adj.symm)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G hzmR
          (Or.inr h.last_adj)
      · exact hall

/-- Symmetric one-matching gap filling. -/
theorem goodFour_of_gap_left_induced_right_matching
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (final : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoring G final)
    (hagree : ColoringsAgreeOff G
      ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet)
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small)
      final)
    (hA : final (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) ≠ none)
    (hB : final (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none) :
    GoodFour G final := by
  apply goodFour_of_gap_left_matching_right_induced G hsub
    (ThreeThreadCore.reverse G h) small hsmall final hvalid
  · simpa [ThreeThreadCore.reverse, Sym2.eq_swap, Set.pair_comm] using hagree
  · simpa [ThreeThreadCore.reverse, Sym2.eq_swap] using hB
  · simpa [ThreeThreadCore.reverse, Sym2.eq_swap] using hA

/-- If the first outer edge is induced-coloured, fill the adjacent gap
edge with matching and the other gap edge with an available induced colour. -/
theorem hasGoodFour_of_threeThread_left_outer_nonmatching
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G)
    (hP : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠ none) :
    HasGoodFour G := by
  classical
  let D : Set G.edgeSet :=
    RetainedEdges (deleteThreeThreadMiddle G v₂) G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  have hbase : IsOneTwoColoringOn G D base := by
    simpa [D, base] using transport_deleteThreeThreadMiddle_valid G h
      hsmall.valid
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ D := by
    simpa [D, B] using right_chain_edge_not_retained G h.right_adj
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have havailA : ColorAvailableOn G D base A none := by
    exact matching_available_left_gap_of_outer_nonmatching G h base
      (by simpa [base] using hP)
  let afterA := recolor G base A none
  have hafterA : IsOneTwoColoringOn G (insert A D) afterA :=
    hbase.extend_one G hAD havailA
  obtain ⟨mR, hmRD, hmRbase, hzmR⟩ :=
    exists_retained_matching_incident_threeThread_end G h small
      hsmall.oneSaturated
  have hmRA : mR ≠ A := by
    intro hEq
    exact hAD (by simpa [D, hEq] using hmRD)
  have hmRafter : afterA mR = none := by
    rw [show afterA mR = base mR by
      exact recolor_ne G base none hmRA]
    exact hmRbase
  obtain ⟨i, hi⟩ := exists_available_right_gap_after_left_matching G h
    afterA (by simp [afterA, A]) mR hmRafter hzmR
  let final := recolor G afterA B (some i)
  have hBfresh : B ∉ insert A D := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨hAB.symm, hBD⟩
  have hfinalOn : IsOneTwoColoringOn G (insert B (insert A D)) final :=
    hafterA.extend_one G hBfresh hi
  have hvalid : IsOneTwoColoring G final := by
    simpa [IsOneTwoColoring, D, A, B,
      insert_threeThread_gap_retained_eq_univ G h] using hfinalOn
  have hagree : ColoringsAgreeOff G ({A, B} : Set G.edgeSet) base final := by
    intro f hf
    have hne : f ≠ A ∧ f ≠ B := by simpa using hf
    simp [final, afterA, recolor, hne.1, hne.2]
  have hgood : GoodFour G final :=
    goodFour_of_gap_left_matching_right_induced G hsub h small hsmall
      final hvalid (by simpa [A, B, base] using hagree)
        (by simp [final, afterA, A, B, recolor, hAB])
        (by simp [final, B])
  let d : DecidableRel G.Adj := inferInstance
  rw [HasGoodFour]
  exact ⟨final, goodFour_change_decidableRel d (Classical.decRel _) final hgood⟩

/-- Symmetric easy outer-colour case. -/
theorem hasGoodFour_of_threeThread_right_outer_nonmatching
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G)
    (hR : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠ none) :
    HasGoodFour G := by
  apply hasGoodFour_of_threeThread_left_outer_nonmatching G
    (ThreeThreadCore.reverse G h) small hsmall hsub
  simpa [ThreeThreadCore.reverse, Sym2.eq_swap] using hR

/-- Four of the five outer-colour symmetry classes are reducible without
using either of the other two threads at the degree-three centre. -/
theorem hasGoodFour_of_threeThread_unless_outer_pair_matching
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G)
    (heasy :
      transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠ none ∨
      transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
          (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠ none) :
    HasGoodFour G := by
  rcases heasy with hP | hR
  · exact hasGoodFour_of_threeThread_left_outer_nonmatching G h small hsmall
      hsub hP
  · exact hasGoodFour_of_threeThread_right_outer_nonmatching G h small hsmall
      hsub hR

/-! ## The hard matching/matching outer case

The following lemmas isolate the palette-crossing argument and the first
neighbour-arm swap used in the remaining long-thread configurations.
-/

theorem longPair_left_gap_available_of_missing_external
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (colour : G.edgeSet → OneTwoColor 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (i : Fin 4)
    (hi : i ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    ColorAvailableOn G (RetainedEdges (G.deleteIncidenceSet v₂) G)
      colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) (some i) := by
  apply (colorAvailableOn_some_iff G _ _ _ i).mpr
  intro f hfD hfA hfi
  by_contra hnsep
  have hfblock : f ∈ inducedBlockerEdgesOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour
      (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) := by
    exact (mem_inducedBlockerEdgesOn G _ colour _ f).mpr
      ⟨hfD, hfA, hnsep⟩
  have hfgeom := longPair_inducedBlockerEdgesOn_left_subset G
    h.first_two h.middle_two h.third_two h.left_adj h.right_adj
    h.first_ne_third h.first_adj.symm h.middle_ne_start h.last_adj
    h.middle_ne_end hfblock
  rcases Finset.mem_insert.mp hfgeom with hfR | hfu
  · subst f
    simpa [hR] using hfi
  · have huf : u ∈ (f : Sym2 V) :=
      (mem_incidentEdgeFinset (G := G)).mp hfu
    by_cases hfP : f = (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)
    · subst f
      simpa [hP] using hfi
    · exact hi ⟨f, ⟨huf, hfP⟩, hfi⟩

theorem longPair_right_gap_available_of_cross_colour
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (colour : G.edgeSet → OneTwoColor 4)
    (i j : Fin 4) (hij : i ≠ j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = some i)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hj : j ∉ ExternalInducedColors G colour z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet)) :
    ColorAvailableOn G
      (insert (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet)
        (RetainedEdges (G.deleteIncidenceSet v₂) G))
      colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)
      (some j) := by
  apply (colorAvailableOn_some_iff G _ _ _ j).mpr
  intro f hfD hfB hfj
  by_contra hnsep
  have hfblock : f ∈ inducedBlockerEdgesOn G
      (insert (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet)
        (RetainedEdges (G.deleteIncidenceSet v₂) G)) colour
      (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) := by
    exact (mem_inducedBlockerEdgesOn G _ colour _ f).mpr
      ⟨hfD, hfB, hnsep⟩
  have hfgeom := longPair_inducedBlockerEdgesOn_right_subset G
    h.first_two h.middle_two h.third_two h.left_adj h.right_adj
    h.first_ne_third h.first_adj.symm h.middle_ne_start h.last_adj
    h.middle_ne_end hfblock
  rcases Finset.mem_insert.mp hfgeom with hfA | hfrest
  · subst f
    have : i = j := Option.some.inj (hA.symm.trans hfj)
    exact hij this
  · rcases Finset.mem_insert.mp hfrest with hfP | hfz
    · subst f
      simpa [hP] using hfj
    · have hzf : z ∈ (f : Sym2 V) :=
        (mem_incidentEdgeFinset (G := G)).mp hfz
      by_cases hfR : f = (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet)
      · subst f
        simpa [hR] using hfj
      · exact hj ⟨f, ⟨hzf, hfR⟩, hfj⟩

theorem longPair_gap_misses_external_start
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z) :
    ∀ e : G.edgeSet,
      IsExternalAt G u (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) e →
      e ∉ ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet) := by
  intro e he heS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heS
  rcases heS with rfl | rfl
  · have hu : u = v₁ ∨ u = v₂ := by simpa using he.1
    exact hu.elim (isThreeVertex_ne_isTwoVertex G h.start_three h.first_two)
      (isThreeVertex_ne_isTwoVertex G h.start_three h.middle_two)
  · have hu : u = v₃ ∨ u = v₂ := by simpa using he.1
    exact hu.elim (isThreeVertex_ne_isTwoVertex G h.start_three h.third_two)
      (isThreeVertex_ne_isTwoVertex G h.start_three h.middle_two)

theorem longPair_gap_misses_external_end
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z) :
    ∀ e : G.edgeSet,
      IsExternalAt G z (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) e →
      e ∉ ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet) := by
  simpa [ThreeThreadCore.reverse, Sym2.eq_swap, Set.pair_comm] using
    longPair_gap_misses_external_start G (ThreeThreadCore.reverse G h)

theorem longPair_visible_edge_at_threeThread_first_cases
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (e : G.edgeSet)
    (hvis : ∃ y, y ∈ (e : Sym2 V) ∧ (v₁ = y ∨ G.Adj v₁ y)) :
    e = (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) ∨
      e = (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) ∨
      e = (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∨
      IsExternalAt G u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) e := by
  obtain ⟨y, hye, rfl | hnear⟩ := hvis
  · rcases edge_eq_left_or_right_of_incident_two G h.first_two
      h.left_adj h.first_adj.symm h.middle_ne_start e hye with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext he)))
  · have hyN : y ∈ G.neighborFinset v₁ :=
      (G.mem_neighborFinset v₁ y).mpr hnear
    rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two h.left_adj
      h.first_adj.symm h.middle_ne_start] at hyN
    have hy : y = v₂ ∨ y = u := by simpa using hyN
    rcases hy with hyv₂ | hyu
    · have hv₂e : v₂ ∈ (e : Sym2 V) := by simpa [hyv₂] using hye
      rcases edge_eq_left_or_right_of_incident_two G h.middle_two
        h.left_adj.symm h.right_adj h.first_ne_third e hv₂e with he | he
      · exact Or.inl (Subtype.ext (by simpa [Sym2.eq_swap] using he))
      · exact Or.inr (Or.inl (Subtype.ext (by
            simpa [Sym2.eq_swap] using he)))
    · have hue : u ∈ (e : Sym2 V) := by simpa [hyu] using hye
      by_cases heP : e =
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)
      · exact Or.inr (Or.inr (Or.inl heP))
      · exact Or.inr (Or.inr (Or.inr ⟨hue, heP⟩))

theorem longPair_not_vertexSeesInduced_first_of_palette_bound
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (colour : G.edgeSet → OneTwoColor 4)
    (i j k : Fin 4)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = some i)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = some j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hj : j ∈ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hk : k ∉ insert i (ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))) :
    ¬ VertexSeesInduced G colour v₁ k := by
  intro hsee
  obtain ⟨e, he, y, hye, hclose⟩ :=
    (vertexSeesInduced_iff G colour v₁ k).mp hsee
  rcases longPair_visible_edge_at_threeThread_first_cases G h e
      ⟨y, hye, hclose⟩ with heA | heB | heP | heExt
  · subst e
    have hki : k = i := Option.some.inj (he.symm.trans hA)
    exact hk (by simp [hki])
  · subst e
    have hkj : k = j := Option.some.inj (he.symm.trans hB)
    exact hk (by simp [hkj, hj])
  · subst e
    simpa [hP] using he
  · exact hk (by
      apply Set.mem_insert_iff.mpr
      right
      exact ⟨e, heExt, he⟩)

theorem longPair_not_vertexSeesInduced_end_of_palette_bound
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (colour : G.edgeSet → OneTwoColor 4)
    (i j k : Fin 4)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = some i)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = some j)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hi : i ∈ ExternalInducedColors G colour z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hk : k ∉ insert j (ExternalInducedColors G colour z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))) :
    ¬ VertexSeesInduced G colour v₃ k := by
  simpa [ThreeThreadCore.reverse, Sym2.eq_swap] using
    longPair_not_vertexSeesInduced_first_of_palette_bound G
      (ThreeThreadCore.reverse G h) colour j i k
      (by simpa [ThreeThreadCore.reverse, Sym2.eq_swap] using hB)
      (by simpa [ThreeThreadCore.reverse, Sym2.eq_swap] using hA)
      (by simpa [ThreeThreadCore.reverse, Sym2.eq_swap] using hR)
      (by simpa [ThreeThreadCore.reverse, Sym2.eq_swap] using hi)
      (by simpa [ThreeThreadCore.reverse, Sym2.eq_swap] using hk)

theorem longPair_good_both_gap_induced_of_cross_palettes
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (final : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoring G final)
    (hagree : ColoringsAgreeOff G
      ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet)
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small)
      final)
    (i j kL kR : Fin 4)
    (hA : final (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = some i)
    (hB : final (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = some j)
    (hP : final (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : final (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hiR : i ∈ ExternalInducedColors G final z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hjL : j ∈ ExternalInducedColors G final u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hkL : kL ∉ insert i (ExternalInducedColors G final u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)))
    (hkR : kR ∉ insert j (ExternalInducedColors G final z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))) :
    GoodFour G final := by
  apply goodFour_of_threeThread_gap_recolour G hsub h small hsmall final
    hvalid hagree
  · intro e heS _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heS
    rcases heS with rfl | rfl
    · refine ⟨(⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet), hP,
          v₁, ?_, ?_⟩
      · simp
      · simp
    · refine ⟨(⟨s(v₃, z), h.last_adj⟩ : G.edgeSet), hR,
          v₃, ?_, ?_⟩
      · simp
      · simp
  · intro q hqcase hmatch hall
    rcases hqcase with rfl | rfl | rfl
    · exact longPair_not_vertexSeesInduced_first_of_palette_bound G h final
        i j kL hA hB hP hjL hkL (hall kL)
    · exact (longPair_paletteCondition_at_two_two_neighbours G
        h.middle_two h.left_adj.symm h.right_adj h.first_ne_third
        h.first_two h.third_two hmatch) hall
    · exact longPair_not_vertexSeesInduced_end_of_palette_bound G h final
        i j kR hA hB hR hiR hkR (hall kR)

theorem longPair_hasGoodFour_of_outer_matching_cross_palettes
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G)
    (i j kL kR : Fin 4)
    (hP : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hiR : i ∈ ExternalInducedColors G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hiL : i ∉ ExternalInducedColors G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hjL : j ∈ ExternalInducedColors G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hjR : j ∉ ExternalInducedColors G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hkL : kL ∉ insert i (ExternalInducedColors G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)))
    (hkR : kR ∉ insert j (ExternalInducedColors G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))) :
    HasGoodFour G := by
  classical
  let D : Set G.edgeSet :=
    RetainedEdges (deleteThreeThreadMiddle G v₂) G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let S : Set G.edgeSet := {A, B}
  have hbase : IsOneTwoColoringOn G D base := by
    simpa [D, base] using transport_deleteThreeThreadMiddle_valid G h
      hsmall.valid
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ D := by
    simpa [D, B] using right_chain_edge_not_retained G h.right_adj
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hPD : P ∈ D := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hRD : R ∈ D := by
    change R ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [R, h.right_adj.ne, h.middle_ne_end]
  have havailA : ColorAvailableOn G D base A (some i) := by
    exact longPair_left_gap_available_of_missing_external G h base
      (by simpa [base, P] using hP) (by simpa [base, R] using hR) i
      (by simpa [base, P] using hiL)
  let afterA := recolor G base A (some i)
  have hafterA : IsOneTwoColoringOn G (insert A D) afterA :=
    hbase.extend_one G hAD havailA
  have hagreeA : ColoringsAgreeOff G ({A} : Set G.edgeSet) base afterA :=
    coloringsAgreeOff_recolor G base A (some i)
  have hRpalA : ExternalInducedColors G base z R =
      ExternalInducedColors G afterA z R := by
    apply externalInducedColors_eq_of_agreeOff G hagreeA
    intro e heExt heA
    apply longPair_gap_misses_external_end G h e (by simpa [R] using heExt)
    have heEq : e = A := by simpa using heA
    simpa [A, B] using (show e = A ∨ e = B from Or.inl heEq)
  have hPafter : afterA P = none := by
    rw [show afterA P = base P by
      exact recolor_ne G base (some i) (by
        intro hEq
        exact hAD (hEq ▸ hPD))]
    simpa [base, P] using hP
  have hRafter : afterA R = none := by
    rw [show afterA R = base R by
      exact recolor_ne G base (some i) (by
        intro hEq
        exact hAD (hEq ▸ hRD))]
    simpa [base, R] using hR
  have hjRAfter : j ∉ ExternalInducedColors G afterA z R := by
    rw [← hRpalA]
    simpa [base, R] using hjR
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hiL hjL
  have havailB : ColorAvailableOn G (insert A D) afterA B (some j) := by
    exact longPair_right_gap_available_of_cross_colour G h afterA i j hij
      (by simp [afterA, A]) (by simpa [P] using hPafter)
      (by simpa [R] using hRafter) (by simpa [R] using hjRAfter)
  let final := recolor G afterA B (some j)
  have hBfresh : B ∉ insert A D := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨hAB.symm, hBD⟩
  have hfinalOn : IsOneTwoColoringOn G (insert B (insert A D)) final :=
    hafterA.extend_one G hBfresh havailB
  have hvalid : IsOneTwoColoring G final := by
    simpa [IsOneTwoColoring, D, A, B,
      insert_threeThread_gap_retained_eq_univ G h] using hfinalOn
  have hagree : ColoringsAgreeOff G S base final := by
    intro f hf
    have hne : f ≠ A ∧ f ≠ B := by simpa [S] using hf
    simp [final, afterA, recolor, hne.1, hne.2]
  have hLpal : ExternalInducedColors G base u P =
      ExternalInducedColors G final u P := by
    apply externalInducedColors_eq_of_agreeOff G hagree
    intro e heExt
    exact longPair_gap_misses_external_start G h e (by simpa [P] using heExt)
  have hRpal : ExternalInducedColors G base z R =
      ExternalInducedColors G final z R := by
    apply externalInducedColors_eq_of_agreeOff G hagree
    intro e heExt
    exact longPair_gap_misses_external_end G h e (by simpa [R] using heExt)
  have hPfinal : final P = none :=
    (hagree P (by
      intro hPS
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hPS
      rcases hPS with hEq | hEq
      · exact hAD (hEq ▸ hPD)
      · exact hBD (hEq ▸ hPD))).symm.trans (by simpa [base, P] using hP)
  have hRfinal : final R = none :=
    (hagree R (by
      intro hRS
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hRS
      rcases hRS with hEq | hEq
      · exact hAD (hEq ▸ hRD)
      · exact hBD (hEq ▸ hRD))).symm.trans (by simpa [base, R] using hR)
  have hgood : GoodFour G final :=
    longPair_good_both_gap_induced_of_cross_palettes G hsub h small hsmall final
      hvalid (by simpa [S, A, B, base] using hagree) i j kL kR
      (by simp [final, afterA, A, B, recolor, hAB])
      (by simp [final, B])
      (by simpa [P] using hPfinal) (by simpa [R] using hRfinal)
      (by rw [← hRpal]; simpa [base, R] using hiR)
      (by rw [← hLpal]; simpa [base, P] using hjL)
      (by rw [← hLpal]; simpa [base, P] using hkL)
      (by rw [← hRpal]; simpa [base, R] using hkR)
  let d : DecidableRel G.Adj := inferInstance
  rw [HasGoodFour]
  exact ⟨final, goodFour_change_decidableRel d (Classical.decRel _) final hgood⟩

theorem longPair_cross_witnesses_of_two_colour_sets_ne
    (L R : Set (Fin 4)) (hLcard : L.ncard = 2) (hRcard : R.ncard = 2)
    (hne : L ≠ R) :
    ∃ i j kL kR : Fin 4,
      i ∈ R ∧ i ∉ L ∧ j ∈ L ∧ j ∉ R ∧
      kL ∉ insert i L ∧ kR ∉ insert j R := by
  classical
  have hnRL : ¬ R ⊆ L := by
    intro hsub
    have heq : R = L := Set.eq_of_subset_of_ncard_le hsub (by omega)
    exact hne heq.symm
  have hnLR : ¬ L ⊆ R := by
    intro hsub
    have heq : L = R := Set.eq_of_subset_of_ncard_le hsub (by omega)
    exact hne heq
  obtain ⟨i, hiR, hiL⟩ := Set.not_subset.mp hnRL
  obtain ⟨j, hjL, hjR⟩ := Set.not_subset.mp hnLR
  have hexL : ∃ kL : Fin 4, kL ∉ insert i L := by
    by_contra hn
    push_neg at hn
    have huniv : insert i L = Set.univ := Set.eq_univ_of_forall hn
    have hcard := Set.ncard_insert_le i L
    rw [huniv, hLcard] at hcard
    norm_num at hcard
  have hexR : ∃ kR : Fin 4, kR ∉ insert j R := by
    by_contra hn
    push_neg at hn
    have huniv : insert j R = Set.univ := Set.eq_univ_of_forall hn
    have hcard := Set.ncard_insert_le j R
    rw [huniv, hRcard] at hcard
    norm_num at hcard
  obtain ⟨kL, hkL⟩ := hexL
  obtain ⟨kR, hkR⟩ := hexR
  exact ⟨i, j, kL, kR, hiR, hiL, hjL, hjR, hkL, hkR⟩

theorem longPair_externalInducedColors_ncard_eq_two_of_validOn_matching
    (D : Set G.edgeSet)
    {u : V} (hu : G.degree u = 3)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G D colour)
    (hinc : ∀ e : G.edgeSet, u ∈ (e : Sym2 V) → e ∈ D)
    (P : G.edgeSet) (huP : u ∈ (P : Sym2 V))
    (hP : colour P = none) :
    (ExternalInducedColors G colour u P).ncard = 2 := by
  classical
  let E : Finset G.edgeSet := (incidentEdgeFinset G u).erase P
  have hPmem : P ∈ incidentEdgeFinset G u :=
    (mem_incidentEdgeFinset (G := G)).mpr huP
  have hEcard : E.card = 2 := by
    simp only [E]
    rw [Finset.card_erase_of_mem hPmem, card_incidentEdgeFinset, hu]
  have hsome : ∀ e : G.edgeSet, e ∈ E → ∃ i : Fin 4, colour e = some i := by
    intro e he
    have hedata := Finset.mem_erase.mp he
    cases hce : colour e with
    | none =>
        have hue := (mem_incidentEdgeFinset (G := G)).mp hedata.2
        have hp := hvalid P (hinc P huP) e (hinc e hue) hedata.1.symm
        have hdisj : EndpointDisjoint G P e := by
          simpa [hP, hce] using hp
        exact False.elim (hdisj u huP hue)
    | some i => exact ⟨i, rfl⟩
  let c : {e : G.edgeSet // e ∈ E} → Fin 4 := fun e =>
    Classical.choose (hsome e.1 e.2)
  have hc (e : {e : G.edgeSet // e ∈ E}) :
      colour e.1 = some (c e) := by
    exact Classical.choose_spec (hsome e.1 e.2)
  have hcinj : Function.Injective c := by
    intro e f hef
    apply Subtype.ext
    by_contra hne
    have hene := Finset.mem_erase.mp e.2
    have hfne := Finset.mem_erase.mp f.2
    have hue := (mem_incidentEdgeFinset (G := G)).mp hene.2
    have huf := (mem_incidentEdgeFinset (G := G)).mp hfne.2
    have hp := hvalid e.1 (hinc e.1 hue) f.1 (hinc f.1 huf) hne
    have hsep : InducedSeparated G e.1 f.1 := by
      simpa [hc e, hc f, hef] using hp
    exact hsep.1 u hue huf
  have hpalette : ExternalInducedColors G colour u P = Set.range c := by
    ext i
    constructor
    · rintro ⟨e, ⟨hue, heP⟩, hei⟩
      have heE : e ∈ E := Finset.mem_erase.mpr
        ⟨heP, (mem_incidentEdgeFinset (G := G)).mpr hue⟩
      let ee : {e : G.edgeSet // e ∈ E} := ⟨e, heE⟩
      refine ⟨ee, ?_⟩
      exact Option.some.inj ((hc ee).symm.trans hei)
    · rintro ⟨e, rfl⟩
      have hedata := Finset.mem_erase.mp e.2
      exact ⟨e.1,
        ⟨(mem_incidentEdgeFinset (G := G)).mp hedata.2, hedata.1⟩,
        hc e⟩
  rw [hpalette, Set.ncard_range_of_injective hcinj]
  rw [Nat.card_eq_fintype_card]
  simpa only [Fintype.card_coe] using hEcard

theorem longPair_not_adj_endpoints_of_short_path
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (htwo : 2 ≤ p.length) (hshort : p.length + 1 < 16) :
    ¬ G.Adj b a := by
  intro hba
  have hclosing : s(b, a) ∉ p.edges := by
    intro hedge
    have hedge' : s(a, b) ∈ p.edges := by
      simpa only [Sym2.eq_swap] using hedge
    have hone := hp.length_eq_one_of_mem_edges hedge'
    omega
  have hcycle : (Walk.cons hba p).IsCycle :=
    (Walk.cons_isCycle_iff p hba).mpr ⟨hp, hclosing⟩
  have hboundE : (16 : ℕ∞) ≤ ((Walk.cons hba p).length : ℕ∞) :=
    (le_egirth.mp hgirth) b (Walk.cons hba p) hcycle
  have hbound : 16 ≤ (Walk.cons hba p).length := by
    exact_mod_cast hboundE
  simp only [Walk.length_cons] at hbound
  omega

theorem longPair_incident_retained_deleteIncidence_of_not_adj
    {u x : V} (hux : u ≠ x) (hnadj : ¬ G.Adj u x)
    (e : G.edgeSet) (hue : u ∈ (e : Sym2 V)) :
    e ∈ RetainedEdges (G.deleteIncidenceSet x) G := by
  rw [mem_retained_deleteIncidenceSet_iff]
  intro hxe
  have heq : (e : Sym2 V) = s(u, x) :=
    (Sym2.mem_and_mem_iff hux).mp ⟨hue, hxe⟩
  apply hnadj
  rw [← G.mem_edgeSet]
  rw [← heq]
  exact e.2

theorem longPair_hasGoodFour_of_outer_matching_palettes_ne
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G)
    (hP : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hne : ExternalInducedColors G
        (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      ExternalInducedColors G
        (transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small) z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet)) :
    HasGoodFour G := by
  let D : Set G.edgeSet :=
    RetainedEdges (deleteThreeThreadMiddle G v₂) G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  have hbase : IsOneTwoColoringOn G D base := by
    simpa [D, base] using transport_deleteThreeThreadMiddle_valid G h
      hsmall.valid
  let pL : G.Walk u v₂ := Walk.cons h.first_adj h.left_adj.toWalk
  have hpL : pL.IsPath := by
    apply (Walk.IsPath.of_adj h.left_adj).cons
    simp [h.first_adj.ne]
    exact h.middle_ne_start.symm
  have hnotL : ¬ G.Adj v₂ u :=
    longPair_not_adj_endpoints_of_short_path G hgirth hpL
      (by simp [pL]) (by simp [pL])
  let pR : G.Walk v₂ z := Walk.cons h.right_adj h.last_adj.toWalk
  have hpR : pR.IsPath := by
    apply (Walk.IsPath.of_adj h.last_adj).cons
    simp [pR, h.right_adj.ne, h.middle_ne_end]
  have hnotR : ¬ G.Adj z v₂ :=
    longPair_not_adj_endpoints_of_short_path G hgirth hpR
      (by simp [pR]) (by simp [pR])
  have hincL : ∀ e : G.edgeSet, u ∈ (e : Sym2 V) → e ∈ D := by
    intro e hue
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      h.middle_ne_start.symm (fun huv₂ => hnotL huv₂.symm) e hue
  have hincR : ∀ e : G.edgeSet, z ∈ (e : Sym2 V) → e ∈ D := by
    intro e hze
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      h.middle_ne_end.symm hnotR e hze
  have hLcard : (ExternalInducedColors G base u P).ncard = 2 := by
    exact longPair_externalInducedColors_ncard_eq_two_of_validOn_matching G D
      h.start_three base hbase hincL P (by simp [P]) (by simpa [base, P] using hP)
  have hRcard : (ExternalInducedColors G base z R).ncard = 2 := by
    exact longPair_externalInducedColors_ncard_eq_two_of_validOn_matching G D
      h.end_three base hbase hincR R (by simp [R]) (by simpa [base, R] using hR)
  obtain ⟨i, j, kL, kR, hiR, hiL, hjL, hjR, hkL, hkR⟩ :=
    longPair_cross_witnesses_of_two_colour_sets_ne
      (ExternalInducedColors G base u P)
      (ExternalInducedColors G base z R) hLcard hRcard
      (by simpa [base, P, R] using hne)
  exact longPair_hasGoodFour_of_outer_matching_cross_palettes G h small hsmall
    hsub i j kL kR (by simpa [base, P] using hP)
    (by simpa [base, R] using hR)
    (by simpa [base, R] using hiR) (by simpa [base, P] using hiL)
    (by simpa [base, P] using hjL) (by simpa [base, R] using hjR)
    (by simpa [base, P] using hkL) (by simpa [base, R] using hkR)

theorem longPair_threeThread_hard_normal_form_of_no_goodFour
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) :
    let base := transportColoringToSupergraph
      (G.deleteIncidenceSet_le v₂) small
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
    base P = none ∧ base R = none ∧
      ExternalInducedColors G base u P =
        ExternalInducedColors G base z R := by
  dsimp only
  have hP : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none := by
    by_contra hne
    exact hbad (hasGoodFour_of_threeThread_left_outer_nonmatching G h small
      hsmall hsub hne)
  have hR : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none := by
    by_contra hne
    exact hbad (hasGoodFour_of_threeThread_right_outer_nonmatching G h small
      hsmall hsub hne)
  refine ⟨hP, hR, ?_⟩
  by_contra hpal
  exact hbad (longPair_hasGoodFour_of_outer_matching_palettes_ne G hgirth h small
    hsmall hsub hP hR hpal)

/-- A version of the gap assembly theorem based only on an already prepared
ambient colouring.  This is the interface needed after a neighbour-arm
recolouring: the two gap edges are then the only remaining support. -/
theorem longPair_goodFour_of_preparedThreeThreadGap_recolour
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (base final : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h base)
    (hvalid : IsOneTwoColoring G final)
    (hsaturated : OneSaturated G final)
    (hagree : ColoringsAgreeOff G
      ({(⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet) base final)
    (hpalette : ∀ q : V, q = v₁ ∨ q = v₂ ∨ q = v₃ →
      VertexSeesMatching G final q →
      ¬ ∀ i : Fin 4, VertexSeesInduced G final q i) :
    GoodFour G final := by
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let S : Set G.edgeSet := {A, B}
  refine ⟨hvalid, hsaturated, ?_, ?_⟩
  · apply hprepared.2.2.1.of_agreeOff G (S := S)
    · simpa [S, A, B] using hagree
    · intro q hq haffect hmatch hall
      have hqcase : q = v₁ ∨ q = v₂ ∨ q = v₃ := by
        apply twoVertex_paletteAffectedBy_threeThread_gap G h hq
        simpa [S, A, B] using haffect
      exact hpalette q hqcase hmatch hall
  · apply hprepared.2.2.2.of_agreeOff G (S := S)
    · simpa [S, A, B] using hagree
    · intro r s p hp haffect
      exfalso
      apply not_threadConditionAffectedBy_threeThread_gap G h p hp
      simpa [S, A, B] using haffect

/-- Moving an induced colour from another edge at the degree-three start
onto the selected outer edge introduces no new induced blocker among the
retained edges.  The degree-two vertex `v₁` has no retained edge on its
deleted side. -/
theorem longPair_inducedSeparated_selectedOuter_of_fork
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (Q f : G.edgeSet) (huQ : u ∈ (Q : Sym2 V))
    (hfD : f ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hfP : f ≠ (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hsep : InducedSeparated G Q f) :
    InducedSeparated G
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) f := by
  rw [inducedSeparated_iff_forall_endpoints] at hsep ⊢
  intro x hx y hyf
  have hxcase : x = v₁ ∨ x = u := by simpa using hx
  rcases hxcase with hxv₁ | hxu
  · constructor
    · intro hv₁y
      have hyv₁ : y = v₁ := hv₁y.symm.trans hxv₁
      have hv₁f : v₁ ∈ (f : Sym2 V) := by simpa [hyv₁] using hyf
      exact hfP (retained_edge_eq_external_of_incident_two G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start f hfD hv₁f)
    · intro hv₁y
      have hv₁y' : G.Adj v₁ y := by simpa [hxv₁] using hv₁y
      have hyN : y ∈ G.neighborFinset v₁ :=
        (G.mem_neighborFinset v₁ y).mpr hv₁y'
      rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start] at hyN
      have hycase : y = v₂ ∨ y = u := by simpa using hyN
      rcases hycase with hyv₂ | hyu
      · exact ((mem_retained_deleteIncidenceSet_iff G v₂ f).mp hfD)
          (by simpa [hyv₂] using hyf)
      · exact (hsep u huQ u (by simpa [hyu] using hyf)).1 rfl
  · simpa [hxu] using hsep u huQ y hyf

/-- If the edge immediately following another thread arm is induced, the
matching colour can be moved from the selected outer edge onto that arm's
first edge without conflicting with any unchanged retained matching edge. -/
theorem longPair_endpointDisjoint_forkFirst_of_selectedOuter
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ≠ none)
    (f : G.edgeSet)
    (hfD : f ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hfP : f ≠ (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hfQ : f ≠ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hf : colour f = none) :
    EndpointDisjoint G
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) f := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  have hPD : P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hPf := hvalid P hPD f hfD (by simpa [P] using hfP.symm)
  have hPdisj : EndpointDisjoint G P f := by
    simpa [P, hP, hf] using hPf
  intro x hx hxf
  have hxcase : x = w₁ ∨ x = u := by simpa [Q] using hx
  rcases hxcase with hxw₁ | hxu
  · rcases edge_eq_left_or_right_of_incident_two G g.first_two
      g.first_adj.symm g.left_adj g.middle_ne_start.symm f
      (by simpa [hxw₁] using hxf) with
      hfQu | hfCu
    · exact hfQ (Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfQu))
    · apply hC
      have hfEqC : f = C := Subtype.ext (by simpa [C] using hfCu)
      simpa [hfEqC] using hf
  · exact hPdisj u (by simp [P]) (by simpa [hxu] using hxf)

theorem longPair_validOn_swap_selectedOuter_forkFirst
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (a : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ≠ none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G)
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hnewP : new P = some a := by simp [new, hPQ']
  have hnewQ : new Q = none := by simp [new]
  have hnewOff (f : G.edgeSet) (hfP : f ≠ P) (hfQ : f ≠ Q) :
      new f = colour f := by simp [new, hfP, hfQ]
  have hPD : P ∈ D := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hPcross (f : G.edgeSet) (hfD : f ∈ D)
      (hfP : f ≠ P) (hfQ : f ≠ Q) :
      PairCompatible G P f (some a) (colour f) := by
    cases hcf : colour f with
    | none => exact pairCompatible_of_ne G (by simp)
    | some j =>
        by_cases haj : a = j
        · subst j
          have hp := hvalid Q (by simpa [D, Q] using hQD) f hfD hfQ.symm
          have hsepQ : InducedSeparated G Q f := by
            simpa [Q, hQ, hcf] using hp
          have hsepP := longPair_inducedSeparated_selectedOuter_of_fork G h Q f
            (by simp [Q]) (by simpa [D] using hfD) (by simpa [P] using hfP)
            hsepQ
          simpa [P, hcf] using hsepP
        · exact pairCompatible_of_ne G (by simp [hcf, haj])
  have hQcross (f : G.edgeSet) (hfD : f ∈ D)
      (hfP : f ≠ P) (hfQ : f ≠ Q) :
      PairCompatible G Q f none (colour f) := by
    cases hcf : colour f with
    | none =>
        have hdisj := longPair_endpointDisjoint_forkFirst_of_selectedOuter G h g
          colour (by simpa [D] using hvalid) (by simpa [P] using hP)
          hC f (by simpa [D] using hfD) (by simpa [P] using hfP)
          (by simpa [Q] using hfQ) hcf
        simpa [Q, hcf] using hdisj
    | some j => exact pairCompatible_of_ne G (by simp [hcf])
  change IsOneTwoColoringOn G D new
  intro e heD f hfD hef
  by_cases heP : e = P
  · subst e
    by_cases hfQ : f = Q
    · subst f
      rw [hnewP, hnewQ]
      exact pairCompatible_of_ne G (by simp)
    · have hfP : f ≠ P := by simpa using hef.symm
      rw [hnewP, hnewOff f hfP hfQ]
      exact hPcross f hfD hfP hfQ
  · by_cases heQ : e = Q
    · subst e
      by_cases hfP : f = P
      · subst f
        rw [hnewQ, hnewP]
        exact pairCompatible_of_ne G (by simp)
      · have hfQ : f ≠ Q := by simpa using hef.symm
        rw [hnewQ, hnewOff f hfP hfQ]
        exact hQcross f hfD hfP hfQ
    · by_cases hfP : f = P
      · subst f
        have hp := hPcross e heD heP heQ
        have hp' := (pairCompatible_comm G).mpr hp
        rw [hnewOff e heP heQ, hnewP]
        exact hp'
      · by_cases hfQ : f = Q
        · subst f
          have hp := hQcross e heD heP heQ
          have hp' := (pairCompatible_comm G).mpr hp
          rw [hnewOff e heP heQ, hnewQ]
          exact hp'
        · rw [hnewOff e heP heQ, hnewOff f hfP hfQ]
          exact hvalid e heD f hfD hef

theorem longPair_oneSaturated_swap_selectedOuter_forkFirst
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour)
    (a : Fin 4)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    OneSaturated G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hPD : P ∈ D := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hAP : A ≠ P := fun hEq => hAD (hEq ▸ hPD)
  have hAQ : A ≠ Q := fun hEq => hAD (hEq ▸ (by simpa [D, Q] using hQD))
  have hnewP : new P = some a := by simp [new, hPQ']
  have hnewQ : new Q = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAQ, A, hA]
  have hnewOff (e : G.edgeSet) (heP : e ≠ P) (heQ : e ≠ Q) :
      new e = colour e := by simp [new, heP, heQ]
  change OneSaturated G new
  intro e he
  by_cases heP : e = P
  · subst e
    exact ⟨Q, hnewQ, u, by simp [P], by simp [Q]⟩
  · by_cases heQ : e = Q
    · subst e
      exact False.elim (he hnewQ)
    · have heOld : colour e ≠ none := by
        intro heNone
        exact he ((hnewOff e heP heQ).trans heNone)
      obtain ⟨f, hf, y, hye, hyf⟩ := hsat e heOld
      by_cases hfP : f = P
      · subst f
        have hycase : y = v₁ ∨ y = u := by simpa [P] using hyf
        rcases hycase with hyv₁ | hyu
        · exact ⟨A, hnewA, y, hye, by simpa [A, hyv₁]⟩
        · exact ⟨Q, hnewQ, y, hye, by simpa [Q, hyu]⟩
      · have hfQ : f ≠ Q := by
          intro hfQ
          subst f
          have hQsome : colour Q = some a := by simpa [Q] using hQ
          have hQnone : colour Q = none := by simpa [Q] using hf
          have hfalse := hQsome.symm.trans hQnone
          simp at hfalse
        exact ⟨f, (hnewOff f hfP hfQ).trans hf, y, hye, hyf⟩

/-- Saturation forces the third edge of a 3-thread prefix to be matching
when its first two edges are both induced-coloured. -/
theorem longPair_third_edge_matching_of_first_two_induced
    {u w₁ w₂ w₃ t : V}
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ≠ none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ≠ none) :
    colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) = none := by
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  have hQ' : colour Q ≠ none := by simpa [Q] using hQ
  have hC' : colour C ≠ none := by simpa [C] using hC
  obtain ⟨f, hf, y, hyC, hyf⟩ := hsat C hC'
  have hycase : y = w₁ ∨ y = w₂ := by simpa [C] using hyC
  rcases hycase with hyw₁ | hyw₂
  · have hw₁f : w₁ ∈ (f : Sym2 V) := by simpa [hyw₁] using hyf
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.first_adj.symm g.left_adj g.middle_ne_start.symm f hw₁f with
      hfQ | hfC
    · exfalso
      have hfeq : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfQ)
      exact hQ' (by simpa [hfeq] using hf)
    · exfalso
      have hfeq : f = C := Subtype.ext (by simpa [C] using hfC)
      exact hC' (by simpa [hfeq] using hf)
  · have hw₂f : w₂ ∈ (f : Sym2 V) := by simpa [hyw₂] using hyf
    rcases edge_eq_left_or_right_of_incident_two G g.middle_two
        g.left_adj.symm g.right_adj g.first_ne_third f hw₂f with
      hfC | hfD
    · exfalso
      have hfeq : f = C := Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC)
      exact hC' (by simpa [hfeq] using hf)
    · have hfeq : f = D := Subtype.ext (by simpa [D] using hfD)
      simpa [D, hfeq] using hf

/-! ## Preservation under the neighbour-arm swap -/

theorem longPair_twoThread_firstEdge_ne_threeThread_firstEdge
    {u s w₁ w₂ w₃ t : V}
    (p : G.Walk u s) (hp : IsKThread G p 2)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t) :
    threadFirstEdge G p hp ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) := by
  intro heq
  have hval : s(u, p.getVert 1) = s(w₁, u) :=
    congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hval
  rcases hval with hbad | hfirst
  · exact g.first_adj.ne hbad.1
  · have hw₁ : w₁ ∈ p.support := by
      simpa [hfirst.2] using p.getVert_mem_support 1
    exact (twoThread_avoids_threeThread_internal G hp g).1 hw₁

theorem longPair_twoThread_lastEdge_ne_threeThread_firstEdge
    {r u w₁ w₂ w₃ t : V}
    (p : G.Walk r u) (hp : IsKThread G p 2)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t) :
    threadLastEdge G p hp ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) := by
  intro heq
  have hval : s(p.getVert 2, u) = s(w₁, u) :=
    congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hval
  rcases hval with hlast | hbad
  · have hw₁ : w₁ ∈ p.support := by
      simpa [hlast.1] using p.getVert_mem_support 2
    exact (twoThread_avoids_threeThread_internal G hp g).1 hw₁
  · exact g.first_adj.ne hbad.2

theorem longPair_start_eq_three_of_external_selectedOuter
    {r s u v₁ v₂ v₃ z : V}
    (p : G.Walk r s) (hp : IsKThread G p 2)
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (hext : IsExternalAt G r (threadFirstEdge G p hp)
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    r = u := by
  have hcase : r = v₁ ∨ r = u := by simpa using hext.1
  rcases hcase with hrv₁ | hru
  · have hrthree := hp.start_three
    have hv₁two := h.first_two
    unfold IsThreeVertex at hrthree
    unfold IsTwoVertex at hv₁two
    rw [hrv₁] at hrthree
    omega
  · exact hru

theorem longPair_end_eq_three_of_external_selectedOuter
    {r s u v₁ v₂ v₃ z : V}
    (p : G.Walk r s) (hp : IsKThread G p 2)
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (hext : IsExternalAt G s (threadLastEdge G p hp)
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    s = u := by
  have hcase : s = v₁ ∨ s = u := by simpa using hext.1
  rcases hcase with hsv₁ | hsu
  · have hsthree := hp.end_three
    have hv₁two := h.first_two
    unfold IsThreeVertex at hsthree
    unfold IsTwoVertex at hv₁two
    rw [hsv₁] at hsthree
    omega
  · exact hsu

theorem longPair_conditionThree_swap_selectedOuter_forkFirst
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour)
    (a : Fin 4)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    ConditionThree G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hnewQ : new Q = none := by simp [new]
  have hagree : ColoringsAgreeOff G ({P, Q} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ Q := by simpa using he
    simp [new, hne.1, hne.2]
  change ConditionThree G new
  apply hold.of_agreeOff G hagree
  intro r s p hp haffect hleft hright
  rcases haffect with haffect | haffect
  · obtain ⟨e, heS, hext⟩ := haffect
    have hecase : e = P ∨ e = Q := by simpa using heS
    rcases hecase with rfl | rfl
    · have hru : r = u :=
        longPair_start_eq_three_of_external_selectedOuter G p hp h
          (by simpa [P] using hext)
      subst r
      have hTQ : threadFirstEdge G p hp ≠ Q := by
        simpa [Q] using
          longPair_twoThread_firstEdge_ne_threeThread_firstEdge G p hp g
      obtain ⟨i, hi⟩ := hleft Q ⟨by simp [Q], hTQ.symm⟩
      have := hnewQ.symm.trans hi
      simp at this
    · obtain ⟨i, hi⟩ := hleft Q (by simpa [Q] using hext)
      have := hnewQ.symm.trans hi
      simp at this
  · obtain ⟨e, heS, hext⟩ := haffect
    have hecase : e = P ∨ e = Q := by simpa using heS
    rcases hecase with rfl | rfl
    · have hsu : s = u :=
        longPair_end_eq_three_of_external_selectedOuter G p hp h
          (by simpa [P] using hext)
      subst s
      have hTQ : threadLastEdge G p hp ≠ Q := by
        simpa [Q] using
          longPair_twoThread_lastEdge_ne_threeThread_firstEdge G p hp g
      obtain ⟨i, hi⟩ := hright Q ⟨by simp [Q], hTQ.symm⟩
      have := hnewQ.symm.trans hi
      simp at this
    · obtain ⟨i, hi⟩ := hright Q (by simpa [Q] using hext)
      have := hnewQ.symm.trans hi
      simp at this

/-- A degree-two vertex affected by swapping two first edges at the common
degree-three centre is either the second vertex of one of the two arms, or
is adjacent to the centre. -/
theorem longPair_twoVertex_paletteAffectedBy_forkFirst_swap_cases
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t q : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet),
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = v₂ ∨ q = w₂ ∨ G.Adj q u := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, heS, x, hxe, hqx⟩ := haffect
  have hecase : e = (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∨
      e = (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) := by
    simpa using heS
  have hqne : q ≠ u := by
    intro hqu
    have hthree := h.start_three
    have htwo := hq
    unfold IsThreeVertex at hthree
    unfold IsTwoVertex at htwo
    rw [hqu] at htwo
    omega
  rcases hecase with rfl | rfl
  · have hxcase : x = v₁ ∨ x = u := by simpa using hxe
    rcases hxcase with hxv₁ | hxu
    · subst x
      rcases hqx with hqv₁ | hqv₁
      · right; right
        simpa [hqv₁] using h.first_adj.symm
      · have hqN : q ∈ G.neighborFinset v₁ :=
          (G.mem_neighborFinset v₁ q).mpr hqv₁.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
          h.left_adj h.first_adj.symm h.middle_ne_start] at hqN
        have hqcase : q = v₂ ∨ q = u := by simpa using hqN
        exact hqcase.elim Or.inl (fun hqu' => False.elim (hqne hqu'))
    · subst x
      rcases hqx with hqu | hqu
      · exact False.elim (hqne hqu)
      · exact Or.inr (Or.inr hqu)
  · have hxcase : x = w₁ ∨ x = u := by simpa using hxe
    rcases hxcase with hxw₁ | hxu
    · subst x
      rcases hqx with hqw₁ | hqw₁
      · right; right
        simpa [hqw₁] using g.first_adj.symm
      · have hqN : q ∈ G.neighborFinset w₁ :=
          (G.mem_neighborFinset w₁ q).mpr hqw₁.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
          g.left_adj g.first_adj.symm g.middle_ne_start] at hqN
        have hqcase : q = w₂ ∨ q = u := by simpa using hqN
        exact hqcase.elim (fun h => Or.inr (Or.inl h))
          (fun hqu' => False.elim (hqne hqu'))
    · subst x
      rcases hqx with hqu | hqu
      · exact False.elim (hqne hqu)
      · exact Or.inr (Or.inr hqu)

theorem longPair_vertexSeesInduced_old_of_forkFirst_swap
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t q : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4) (a : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hqu : G.Adj q u)
    (hall : ∀ i : Fin 4, VertexSeesInduced G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) q i) :
    ∀ i : Fin 4, VertexSeesInduced G colour q i := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hnewP : new P = some a := by simp [new, hPQ']
  have hnewQ : new Q = none := by simp [new]
  intro i
  by_cases hia : i = a
  · subst i
    apply (vertexSeesInduced_iff G colour q a).mpr
    exact ⟨Q, by simpa [Q] using hQ, u, by simp [Q], Or.inr hqu⟩
  · obtain ⟨e, he, x, hxe, hqx⟩ :=
      (vertexSeesInduced_iff G new q i).mp (by simpa [new] using hall i)
    have heP : e ≠ P := by
      intro heq
      subst e
      have hc : some a = some i := hnewP.symm.trans he
      exact hia (Option.some.inj hc).symm
    have heQ : e ≠ Q := by
      intro heq
      subst e
      have hc : none = some i := hnewQ.symm.trans he
      simp at hc
    apply (vertexSeesInduced_iff G colour q i).mpr
    refine ⟨e, ?_, x, hxe, hqx⟩
    simpa [new, heP, heQ] using he

theorem longPair_twoTwoEdge_ne_edgeEndingAtThree
    {x y c u : V} (hx : IsTwoVertex G x) (hy : IsTwoVertex G y)
    (hu : IsThreeVertex G u) (hxy : G.Adj x y) (hcu : G.Adj c u) :
    (⟨s(x, y), hxy⟩ : G.edgeSet) ≠
      (⟨s(c, u), hcu⟩ : G.edgeSet) := by
  intro heq
  have hval : s(x, y) = s(c, u) := congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hval
  rcases hval with hcase | hcase
  · exact (isThreeVertex_ne_isTwoVertex G hu hy) hcase.2.symm
  · exact (isThreeVertex_ne_isTwoVertex G hu hx) hcase.1.symm

theorem longPair_conditionTwo_swap_selectedOuter_forkFirst
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour)
    (hsat : OneSaturated G colour)
    (a : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hQD' : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq => hAD (heq ▸ hPD)
  have hAQ : A ≠ Q := fun heq => hAD (heq ▸ hQD')
  have hBP : B ≠ P := fun heq => hBD (heq ▸ hPD)
  have hBQ : B ≠ Q := fun heq => hBD (heq ▸ hQD')
  have hDP : D ≠ P := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G g.middle_two g.third_two
      h.start_three g.right_adj h.first_adj.symm
  have hDQ : D ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G g.middle_two g.third_two
      g.start_three g.right_adj g.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hQDne : Q ≠ D := hDQ.symm
  have hD : colour D = none := by
    simpa [D] using longPair_third_edge_matching_of_first_two_induced G g
      colour hsat (by simpa [Q, hQ]) (by simpa [C, hC])
  have hnewQ : new Q = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAQ, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBQ, B, hB]
  have hnewD : new D = none := by simp [new, hDP, hDQ, D, hD]
  have hagree : ColoringsAgreeOff G ({P, Q} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ Q := by simpa using he
    simp [new, hne.1, hne.2]
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  have hcases := longPair_twoVertex_paletteAffectedBy_forkFirst_swap_cases G
    h g hq (by simpa [P, Q] using haffect)
  rcases hcases with hqv₂ | hqw₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G g.middle_two
      g.left_adj.symm g.right_adj g.first_ne_third g.first_two g.third_two
      hmatch) hall
  · by_cases hqv₁ : q = v₁
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub h.first_two
        h.left_adj h.middle_two A B hAB hnewA hnewB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [A])
          (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
          (Or.inr h.left_adj)
      · exact hall
    · by_cases hqw₁ : q = w₁
      · subst q
        apply longPair_paletteCondition_at_two_visible_matching G hsub g.first_two
          g.left_adj g.middle_two Q D hQDne hnewQ hnewD
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [Q])
            (Or.inl rfl)
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [D])
            (Or.inr g.left_adj)
        · exact hall
      · have hqu' : q ≠ u := by
          intro hEq
          have hthree := h.start_three
          have htwo := hq
          unfold IsThreeVertex at hthree
          unfold IsTwoVertex at htwo
          rw [hEq] at htwo
          omega
        have hnotAffected : ¬ MatchingAffectedBy G
            ({P, Q} : Set G.edgeSet) q := by
          rintro ⟨e, heS, hqe⟩
          have hecase : e = P ∨ e = Q := by simpa using heS
          rcases hecase with rfl | rfl
          · have hqcase : q = v₁ ∨ q = u := by simpa [P] using hqe
            exact hqcase.elim hqv₁ hqu'
          · have hqcase : q = w₁ ∨ q = u := by simpa [Q] using hqe
            exact hqcase.elim hqw₁ hqu'
        apply hold q hq
        · exact (vertexSeesMatching_iff_of_not_affected G hagree
            hnotAffected).mpr hmatch
        · exact longPair_vertexSeesInduced_old_of_forkFirst_swap G h g colour a
            hP hQ hPQ hqu (by simpa [new] using hall)

theorem longPair_preparedThreeThreadGap_swap_selectedOuter_forkFirst
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (a : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    PreparedThreeThreadGap G h
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some a))
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) none) := by
  refine ⟨
    longPair_validOn_swap_selectedOuter_forkFirst G h g colour hprepared.1 a
      hP hQ hC hQD hPQ,
    longPair_oneSaturated_swap_selectedOuter_forkFirst G h g colour
      hprepared.2.1 a hQ hA hQD hPQ,
    longPair_conditionTwo_swap_selectedOuter_forkFirst G hsub h g colour
      hprepared.2.2.1 hprepared.2.1 a hP hQ hC hA hB hQD hPQ,
    longPair_conditionThree_swap_selectedOuter_forkFirst G h g colour
      hprepared.2.2.2 a hPQ⟩

/-! ## Forcing the second edge of a neighbouring 3-thread to be matching -/

theorem longPair_hasGoodFour_of_fork_second_induced
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G)
    (a : Fin 4)
    (hP : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some a)
    (hC : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) ≠ none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let swap : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G base P (some a)) Q none
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hRP' : R ≠ P := by simpa [R, P] using hRP
  have hRQ' : R ≠ Q := by simpa [R, Q] using hRQ
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hRD : R ∈ Dset := by
    change R ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [R, h.right_adj.ne, h.middle_ne_end]
  have hQD' : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq => hAD (heq ▸ hPD)
  have hAQ : A ≠ Q := fun heq => hAD (heq ▸ hQD')
  have hAR : A ≠ R := fun heq => hAD (heq ▸ hRD)
  have hBP : B ≠ P := fun heq => hBD (heq ▸ hPD)
  have hBQ : B ≠ Q := fun heq => hBD (heq ▸ hQD')
  have hBR : B ≠ R := fun heq => hBD (heq ▸ hRD)
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hAedge : A.1 ∉ (G.deleteIncidenceSet v₂).edgeSet := by
    simpa [Dset, RetainedEdges] using hAD
  have hBedge : B.1 ∉ (G.deleteIncidenceSet v₂).edgeSet := by
    simpa [Dset, RetainedEdges] using hBD
  have hbaseA : base A = none := by
    simp [base, transportColoringToSupergraph, hAedge]
  have hbaseB : base B = none := by
    simp [base, transportColoringToSupergraph, hBedge]
  have hswapA : swap A = none := by
    simp [swap, hAP, hAQ, hbaseA]
  have hswapB : swap B = none := by
    simp [swap, hBP, hBQ, hbaseB]
  have hswapP : swap P = some a := by simp [swap, hPQ']
  have hswapQ : swap Q = none := by simp [swap]
  have hswapR : swap R = none := by
    simp [swap, hRP', hRQ', R, base, hR]
  have hpreparedBase : PreparedThreeThreadGap G h base :=
    preparedThreeThreadGap_of_goodFour G hsub h small hsmall
  have hpreparedSwap : PreparedThreeThreadGap G h swap := by
    exact longPair_preparedThreeThreadGap_swap_selectedOuter_forkFirst G hsub
      h g base hpreparedBase a (by simpa [base, P] using hP)
      (by simpa [base, Q] using hQ) (by simpa [base] using hC)
      (by simpa [base, A] using hbaseA) (by simpa [base, B] using hbaseB)
      (by simpa [Q] using hQD) (by simpa [P, Q] using hPQ)
  have havailA : ColorAvailableOn G Dset swap A none := by
    exact matching_available_left_gap_of_outer_nonmatching G h swap
      (by simpa [P] using (show swap P ≠ none by simp [hswapP]))
  let afterA : G.edgeSet → OneTwoColor 4 := recolor G swap A none
  have hafterAOn : IsOneTwoColoringOn G (insert A Dset) afterA :=
    hpreparedSwap.1.extend_one G hAD havailA
  have hafterAA : afterA A = none := by simp [afterA]
  have hafterAR : afterA R = none := by
    rw [show afterA R = swap R by
      exact recolor_ne G swap none hAR.symm]
    exact hswapR
  obtain ⟨b, hb⟩ := exists_available_right_gap_after_left_matching G h
    afterA (by simpa [A] using hafterAA) R
      (by simpa [R] using hafterAR) (by simp [R])
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterA B (some b)
  have hBfresh : B ∉ insert A Dset := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨hAB.symm, hBD⟩
  have hfinalOn : IsOneTwoColoringOn G (insert B (insert A Dset)) final :=
    hafterAOn.extend_one G hBfresh hb
  have hvalid : IsOneTwoColoring G final := by
    simpa [IsOneTwoColoring, Dset, A, B,
      insert_threeThread_gap_retained_eq_univ G h] using hfinalOn
  have hagree : ColoringsAgreeOff G ({A, B} : Set G.edgeSet) swap final := by
    intro e he
    have hne : e ≠ A ∧ e ≠ B := by simpa using he
    simp [final, afterA, hne.1, hne.2]
  have hfinalA : final A = none := by simp [final, afterA, hAB]
  have hfinalB : final B = some b := by simp [final]
  have hfinalQ : final Q = none := by
    simp [final, afterA, hAQ.symm, hBQ.symm, hswapQ]
  have hfinalR : final R = none := by
    simp [final, afterA, hAR.symm, hBR.symm, hswapR]
  have hsaturated : OneSaturated G final := by
    intro e he
    by_cases heA : e = A
    · subst e
      exact False.elim (he hfinalA)
    by_cases heB : e = B
    · subst e
      exact ⟨A, hfinalA, v₂, by simp [B], by simp [A]⟩
    have heSwap : swap e ≠ none := by
      intro heNone
      apply he
      exact (hagree e (by simpa [heA, heB])).symm.trans heNone
    obtain ⟨f, hf, y, hye, hyf⟩ := hpreparedSwap.2.1 e heSwap
    by_cases hfB : f = B
    · subst f
      have hycase : y = v₃ ∨ y = v₂ := by simpa [B] using hyf
      rcases hycase with hyv₃ | hyv₂
      · exact ⟨R, hfinalR, y, hye, by simpa [R, hyv₃]⟩
      · exact ⟨A, hfinalA, y, hye, by simpa [A, hyv₂]⟩
    · by_cases hfA : f = A
      · subst f
        exact ⟨A, hfinalA, y, hye, hyf⟩
      · refine ⟨f, ?_, y, hye, hyf⟩
        exact (hagree f (by simpa [hfA, hfB])).symm.trans hf
  have hpalette : ∀ q : V, q = v₁ ∨ q = v₂ ∨ q = v₃ →
      VertexSeesMatching G final q →
      ¬ ∀ i : Fin 4, VertexSeesInduced G final q i := by
    intro q hqcase hmatch hall
    rcases hqcase with rfl | rfl | rfl
    · apply longPair_paletteCondition_at_two_visible_matching G hsub
        h.first_two h.left_adj h.middle_two A Q
      · exact fun heq => hAD (heq ▸ hQD')
      · exact hfinalA
      · exact hfinalQ
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [Q]) (Or.inr h.first_adj.symm)
      · exact hall
    · exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
        h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
        hmatch) hall
    · apply longPair_paletteCondition_at_two_visible_matching G hsub
        h.third_two h.right_adj.symm h.middle_two A R hAR hfinalA hfinalR
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inr h.right_adj.symm)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [R]) (Or.inl rfl)
      · exact hall
  have hgood : GoodFour G final :=
    longPair_goodFour_of_preparedThreeThreadGap_recolour G h swap final
      hpreparedSwap hvalid hsaturated
      (by simpa [A, B] using hagree) hpalette
  let d : DecidableRel G.Adj := inferInstance
  rw [HasGoodFour]
  exact ⟨final, goodFour_change_decidableRel d (Classical.decRel _) final hgood⟩

/-- In a bad graph, the second edge of another certified 3-thread must be
matching-coloured once the selected thread has matching outer edges. -/
theorem longPair_fork_second_matching_of_no_goodFour
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (small : (deleteThreeThreadMiddle G v₂).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G v₂) small)
    (hsub : IsSubcubic G)
    (hP : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet))
    (hbad : ¬ HasGoodFour G) :
    transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
      (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none := by
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le v₂) small
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hQD' : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hvalid : IsOneTwoColoringOn G Dset base := by
    simpa [Dset, base] using transport_deleteThreeThreadMiddle_valid G h
      hsmall.valid
  have hQne : base Q ≠ none := by
    intro hQnone
    have hpq := hvalid P hPD Q hQD' (by simpa [P, Q] using hPQ)
    have hdisj : EndpointDisjoint G P Q := by
      simpa [base, P, Q, hP, hQnone] using hpq
    exact hdisj u (by simp [P]) (by simp [Q])
  by_contra hC
  cases hQval : base Q with
  | none => exact hQne hQval
  | some a =>
      apply hbad
      exact longPair_hasGoodFour_of_fork_second_induced G h g small hsmall hsub a
        (by simpa [base, P] using hP) (by simpa [base] using hR)
        (by simpa [base, Q] using hQval) (by simpa [base] using hC)
        hQD hPQ hRP hRQ

theorem longPair_fork_second_matching_of_distinct_threeThreads
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t : V} {p : G.Walk u z} {q : G.Walk u t}
    (hp : IsKThread G p 3) (hq : IsKThread G q 3)
    (hdist : p.getVert 1 ≠ q.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G)
    (hP : transportColoringToSupergraph
      (G.deleteIncidenceSet_le (p.getVert 2)) small
      (threadFirstEdge G p hp) = none)
    (hR : transportColoringToSupergraph
      (G.deleteIncidenceSet_le (p.getVert 2)) small
      (threadLastEdge G p hp) = none)
    (hbad : ¬ HasGoodFour G) :
    transportColoringToSupergraph
      (G.deleteIncidenceSet_le (p.getVert 2)) small
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 4 := by simpa using hq.length
          omega)⟩ : G.edgeSet) = none := by
  let h := hp.threeThreadCore G
  let g := hq.threeThreadCore G
  have hpLen : p.length = 4 := by simpa using hp.length
  have hpGetNe (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) (hij : i ≠ j) :
      p.getVert i ≠ p.getVert j := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show i ∈ {r : ℕ | r ≤ p.length} by simpa [hpLen] using hi)
      (show j ∈ {r : ℕ | r ≤ p.length} by simpa [hpLen] using hj)
      heq
    exact hij hinj
  have hpEnd : p.getVert 4 = z := by
    rw [← hpLen]
    exact p.getVert_length
  let pL : G.Walk u (p.getVert 2) := p.take 2
  have hpL : pL.IsPath := hp.1.take 2
  have hnotL : ¬ G.Adj (p.getVert 2) u :=
    longPair_not_adj_endpoints_of_short_path G hgirth hpL
      (by simp [pL, hpLen]) (by simp [pL, hpLen])
  have hQD : (threadFirstEdge G q hq) ∈
      RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G := by
    have hu₂ : u ≠ p.getVert 2 := by
      simpa using hpGetNe 0 2 (by omega) (by omega) (by omega)
    have hnotU₂ : ¬ G.Adj u (p.getVert 2) := fun hadj => hnotL hadj.symm
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      hu₂ hnotU₂ (threadFirstEdge G q hq)
      (by simp [threadFirstEdge])
  have hPQ : threadFirstEdge G p hp ≠ threadFirstEdge G q hq := by
    intro heq
    have hval : s(u, p.getVert 1) = s(u, q.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hloop
    · exact hdist hsame.2
    · exact hp.first_step_adj.ne hloop.2.symm
  have hRP : threadLastEdge G p hp ≠ threadFirstEdge G p hp := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hcase | hcase
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hcase.1)
    · exact hpGetNe 3 1 (by omega) (by omega) (by omega) hcase.1
  have hRQ : threadLastEdge G p hp ≠ threadFirstEdge G q hq := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, q.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hcase | hcase
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hcase.1)
    · apply hpGetNe 4 0 (by omega) (by omega) (by omega)
      simpa [hpEnd] using hcase.2
  exact longPair_fork_second_matching_of_no_goodFour G h g small hsmall hsub
    (by simpa [h, threadFirstEdge, Sym2.eq_swap] using hP)
    (by simpa [h, threadLastEdge] using hR)
    (by simpa [g, threadFirstEdge, Sym2.eq_swap] using hQD)
    (by simpa [h, g, threadFirstEdge, Sym2.eq_swap] using hPQ)
    (by simpa [h, threadFirstEdge, threadLastEdge, Sym2.eq_swap] using hRP)
    (by simpa [h, g, threadFirstEdge, threadLastEdge, Sym2.eq_swap] using hRQ)
    hbad

theorem longPair_fork_second_matching_in_bad_graph
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t : V} {p : G.Walk u z} {q : G.Walk u t}
    (hp : IsKThread G p 3) (hq : IsKThread G q 3)
    (hdist : p.getVert 1 ≠ q.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G)
    (hbad : ¬ HasGoodFour G) :
    transportColoringToSupergraph
      (G.deleteIncidenceSet_le (p.getVert 2)) small
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 4 := by simpa using hq.length
          omega)⟩ : G.edgeSet) = none := by
  let h := hp.threeThreadCore G
  obtain ⟨hP, hR, _hpal⟩ :=
    longPair_threeThread_hard_normal_form_of_no_goodFour G hgirth h small
      hsmall hsub hbad
  exact longPair_fork_second_matching_of_distinct_threeThreads G hgirth hp hq
    hdist small hsmall hsub
    (by simpa [h, threadFirstEdge, Sym2.eq_swap] using hP)
    (by simpa [h, threadLastEdge] using hR) hbad

end Finite

end

end LeanCo.PackingEdgeColoring
