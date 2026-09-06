import LeanCo.PackingEdgeColoring.MinimalCounterexample
import LeanCo.PackingEdgeColoring.Availability
import LeanCo.PackingEdgeColoring.GoodExtension
import LeanCo.PackingEdgeColoring.SectionThreeReduction

/-!
# The Section 3 three-chain reduction

This file develops the first genuine deletion-and-extension configuration
from Section 3 of Kim--Liu--Xu.  No girth assumption is made: in particular,
the two external edges of the chain are allowed to coincide (the triangle
case), or merely to share their external endpoint.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-! ## A structural capacity lemma for Condition I -/

/-- Edges having an endpoint in the open neighborhood of `u`.  This is
also the complete set of edges which a vertex can see in an induced colour:
an edge incident with `u` is counted at its other endpoint. -/
def vertexVisibleEdgeFinset (u : V) : Finset (Sym2 V) :=
  (G.neighborFinset u).biUnion fun v => G.incidenceFinset v

theorem mem_vertexVisibleEdgeFinset_of_endpoint_close
    {u v : V} {e : G.edgeSet} (hve : v ∈ (e : Sym2 V))
    (huv : u = v ∨ G.Adj u v) :
    (e : Sym2 V) ∈ vertexVisibleEdgeFinset G u := by
  classical
  rcases huv with rfl | huv
  · obtain ⟨w, hew⟩ := Sym2.mem_iff_exists.mp hve
    have huw : G.Adj u w := by
      have heG := e.2
      rw [hew] at heG
      simpa using heG
    apply Finset.mem_biUnion.mpr
    refine ⟨w, (G.mem_neighborFinset u w).mpr huw, ?_⟩
    rw [G.mem_incidenceFinset]
    exact (G.edge_mem_incidenceSet_iff).mpr (by rw [hew]; simp)
  · apply Finset.mem_biUnion.mpr
    refine ⟨v, (G.mem_neighborFinset u v).mpr huv, ?_⟩
    rw [G.mem_incidenceFinset]
    exact (G.edge_mem_incidenceSet_iff).mpr hve

/-- If `u` has degree two and one of its neighbors also has degree two,
then at most five graph edges are visible from `u`.  The other neighbor has
degree at most three by subcubicity. -/
theorem card_vertexVisibleEdgeFinset_le_five
    (hsub : IsSubcubic G) {u v : V}
    (hu : IsTwoVertex G u) (huv : G.Adj u v)
    (hv : IsTwoVertex G v) :
    (vertexVisibleEdgeFinset G u).card ≤ 5 := by
  classical
  have hcardN : (G.neighborFinset u).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hu
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hcardN
  have hvN : v ∈ ({a, b} : Finset V) := by
    rw [← hN]
    exact (G.mem_neighborFinset u v).mpr huv
  have hsum :
      (∑ w ∈ G.neighborFinset u, (G.incidenceFinset w).card) ≤ 5 := by
    rw [hN]
    simp only [Finset.sum_insert, Finset.mem_singleton, hab, not_false_eq_true,
      Finset.sum_singleton, SimpleGraph.card_incidenceFinset_eq_degree]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvN
    rcases hvN with rfl | rfl
    · rw [hv]
      exact Nat.add_le_add_left (hsub b) 2
    · rw [hv]
      exact Nat.add_le_add_right (hsub a) 2
  exact (Finset.card_biUnion_le.trans hsum)

/-- At such a vertex, the palette condition is automatic for every colour
assignment: one visible edge carries the matching colour, leaving at most
four visible edges to witness five distinct induced colours. -/
theorem paletteCondition_at_of_adjacent_two
    (hsub : IsSubcubic G) {colour : G.edgeSet → OneTwoColor 5}
    {u v : V} (hu : IsTwoVertex G u) (huv : G.Adj u v)
    (hv : IsTwoVertex G v)
    (hmatch : VertexSeesMatching G colour u) :
    ¬ ∀ i : Fin 5, VertexSeesInduced G colour u i := by
  classical
  intro hall
  obtain ⟨m, hm, hum⟩ := (vertexSeesMatching_iff G colour u).mp hmatch
  have hinduced : ∀ i : Fin 5, ∃ e, colour e = some i ∧
      ∃ w, w ∈ (e : Sym2 V) ∧ (u = w ∨ G.Adj u w) := fun i =>
    (vertexSeesInduced_iff G colour u i).mp (hall i)
  choose f hf w hw hclose using hinduced
  let witness : OneTwoColor 5 → G.edgeSet
    | none => m
    | some i => f i
  have hwcolour (c : OneTwoColor 5) : colour (witness c) = c := by
    cases c with
    | none => exact hm
    | some i => exact hf i
  have hwmem (c : OneTwoColor 5) :
      (witness c : Sym2 V) ∈ vertexVisibleEdgeFinset G u := by
    cases c with
    | none =>
        exact mem_vertexVisibleEdgeFinset_of_endpoint_close G hum (Or.inl rfl)
    | some i =>
        exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (hw i) (hclose i)
  let intoVisible : OneTwoColor 5 ↪
      {e : Sym2 V // e ∈ vertexVisibleEdgeFinset G u} :=
    { toFun := fun c => ⟨witness c, hwmem c⟩
      inj' := by
        intro a b hab
        have hval : (witness a : Sym2 V) = (witness b : Sym2 V) :=
          congrArg (fun z : {e : Sym2 V //
            e ∈ vertexVisibleEdgeFinset G u} => (z : Sym2 V)) hab
        have hedge : witness a = witness b := Subtype.ext hval
        exact (hwcolour a).symm.trans ((congrArg colour hedge).trans (hwcolour b)) }
  have hsix : 6 ≤ (vertexVisibleEdgeFinset G u).card := by
    have hcard := Fintype.card_le_of_injective intoVisible intoVisible.injective
    simpa using hcard
  have hfive := card_vertexVisibleEdgeFinset_le_five G hsub hu huv hv
  omega

/-! ## Finite incident-edge neighborhoods -/

/-- Ambient graph edges incident with `u`, but retaining the useful
`G.edgeSet` subtype rather than coercing to `Sym2 V`. -/
def incidentEdgeFinset (u : V) : Finset G.edgeSet :=
  Finset.univ.filter fun e => u ∈ (e : Sym2 V)

@[simp] theorem mem_incidentEdgeFinset {u : V} {e : G.edgeSet} :
    e ∈ incidentEdgeFinset G u ↔ u ∈ (e : Sym2 V) := by
  simp [incidentEdgeFinset]

theorem card_incidentEdgeFinset (u : V) :
    (incidentEdgeFinset G u).card = G.degree u := by
  classical
  let E : (incidentEdgeFinset G u : Set G.edgeSet) ≃ G.incidenceSet u :=
    { toFun := fun e =>
        ⟨e.1.1, (G.edge_mem_incidenceSet_iff).mpr
          ((mem_incidentEdgeFinset (G := G)).mp e.2)⟩
      invFun := fun e =>
        ⟨⟨e.1, G.incidenceSet_subset u e.2⟩,
          (mem_incidentEdgeFinset (G := G)).mpr
            ((G.edge_mem_incidenceSet_iff).mp e.2)⟩
      left_inv := fun e => by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun e => Subtype.ext rfl }
  calc
    (incidentEdgeFinset G u).card =
        Fintype.card (incidentEdgeFinset G u : Set G.edgeSet) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (G.incidenceSet u) := Fintype.card_congr E
    _ = G.degree u := G.card_incidenceSet_eq_degree u

theorem neighborFinset_eq_pair_of_isTwoVertex
    {a x u : V} (ha : IsTwoVertex G a)
    (hax : G.Adj a x) (hau : G.Adj a u) (hxu : x ≠ u) :
    G.neighborFinset a = {x, u} := by
  have hcard : (G.neighborFinset a).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact ha
  have hx : x ∈ G.neighborFinset a :=
    (G.mem_neighborFinset a x).mpr hax
  have hu : u ∈ G.neighborFinset a :=
    (G.mem_neighborFinset a u).mpr hau
  have hpair : ({x, u} : Finset V) ⊆ G.neighborFinset a := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hu
  have hcardle : (G.neighborFinset a).card ≤ ({x, u} : Finset V).card := by
    simpa [hxu] using hcard.le
  exact (Finset.eq_of_subset_of_card_le hpair hcardle).symm

/-- A graph edge at a degree-two vertex is one of its two prescribed
incident edges. -/
theorem edge_eq_left_or_right_of_incident_two
    {a x u : V} (ha : IsTwoVertex G a)
    (hax : G.Adj a x) (hau : G.Adj a u) (hxu : x ≠ u)
    (f : G.edgeSet) (haf : a ∈ (f : Sym2 V)) :
    (f : Sym2 V) = s(a, x) ∨ (f : Sym2 V) = s(a, u) := by
  obtain ⟨z, hfz⟩ := Sym2.mem_iff_exists.mp haf
  have haz : G.Adj a z := by
    have hfG := f.2
    rw [hfz] at hfG
    simpa using hfG
  have hz : z = x ∨ z = u := by
    have hzN : z ∈ G.neighborFinset a :=
      (G.mem_neighborFinset a z).mpr haz
    rw [neighborFinset_eq_pair_of_isTwoVertex G ha hax hau hxu] at hzN
    simpa using hzN
  rcases hz with rfl | rfl
  · exact Or.inl hfz
  · exact Or.inr hfz

@[simp] theorem mem_retained_deleteIncidenceSet_iff
    (x : V) (e : G.edgeSet) :
    e ∈ RetainedEdges (G.deleteIncidenceSet x) G ↔
      x ∉ (e : Sym2 V) := by
  simp [RetainedEdges, edgeSet_deleteIncidenceSet,
    G.edge_mem_incidenceSet_iff]

theorem retained_edge_eq_external_of_incident_two
    {a x u : V} (ha : IsTwoVertex G a)
    (hax : G.Adj a x) (hau : G.Adj a u) (hxu : x ≠ u)
    (f : G.edgeSet) (hfD : f ∈ RetainedEdges (G.deleteIncidenceSet x) G)
    (haf : a ∈ (f : Sym2 V)) :
    f = (⟨s(a, u), hau⟩ : G.edgeSet) := by
  rcases edge_eq_left_or_right_of_incident_two G ha hax hau hxu f haf with
    hf | hf
  · have hxf : x ∈ (f : Sym2 V) := by rw [hf]; simp
    exact False.elim ((mem_retained_deleteIncidenceSet_iff G x f).mp hfD hxf)
  · exact Subtype.ext hf

/-- Every retained blocker of the left chain edge lies either at its
external neighbor or is the right external edge.  This statement remains
valid when the external edges coincide. -/
theorem inducedBlockerEdgesOn_left_subset
    {a x b u w : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hau : G.Adj a u) (hxu : x ≠ u)
    (hbw : G.Adj b w) (hxw : x ≠ w)
    {colour : G.edgeSet → OneTwoColor 5} :
    inducedBlockerEdgesOn G (RetainedEdges (G.deleteIncidenceSet x) G)
        colour (⟨s(a, x), hax⟩ : G.edgeSet) ⊆
      insert (⟨s(b, w), hbw⟩ : G.edgeSet) (incidentEdgeFinset G u) := by
  classical
  intro f hf
  have hf' := (mem_inducedBlockerEdgesOn G
    (RetainedEdges (G.deleteIncidenceSet x) G) colour
    (⟨s(a, x), hax⟩ : G.edgeSet) f).mp hf
  rcases hf' with ⟨hfD, hfne, hfsep⟩
  have hfx : x ∉ (f : Sym2 V) :=
    (mem_retained_deleteIncidenceSet_iff G x f).mp hfD
  by_cases hdisj : EndpointDisjoint G
      (⟨s(a, x), hax⟩ : G.edgeSet) f
  · have hcross : HasCrossEdge G (⟨s(a, x), hax⟩ : G.edgeSet) f := by
      by_contra hn
      exact hfsep ⟨hdisj, hn⟩
    obtain ⟨z, hzax, y, hyf, hzy⟩ := hcross
    have hz : z = a ∨ z = x := by simpa using hzax
    rcases hz with hza | hzx
    · have hay : G.Adj a y := by simpa [hza] using hzy
      have hy : y = x ∨ y = u := by
        have hyN : y ∈ G.neighborFinset a :=
          (G.mem_neighborFinset a y).mpr hay
        rw [neighborFinset_eq_pair_of_isTwoVertex G ha hax hau hxu] at hyN
        simpa using hyN
      rcases hy with hyx | hyu
      · exact False.elim (hfx (hyx ▸ hyf))
      · exact Finset.mem_insert.mpr (Or.inr
          ((mem_incidentEdgeFinset (G := G)).mpr (hyu ▸ hyf)))
    · have hxy : G.Adj x y := by simpa [hzx] using hzy
      have hy : y = a ∨ y = b := by
        have hyN : y ∈ G.neighborFinset x :=
          (G.mem_neighborFinset x y).mpr hxy
        rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxb hab] at hyN
        simpa using hyN
      rcases hy with hya | hyb
      · have hfe := retained_edge_eq_external_of_incident_two G ha hax hau hxu
          f hfD (hya ▸ hyf)
        exact Finset.mem_insert.mpr (Or.inr (by
          apply (mem_incidentEdgeFinset (G := G)).mpr
          rw [hfe]
          simp))
      · have hfe := retained_edge_eq_external_of_incident_two G hb hxb.symm hbw
          hxw f hfD (hyb ▸ hyf)
        exact Finset.mem_insert.mpr (Or.inl hfe)
  · have hshared : ∃ z, z ∈ (s(a, x) : Sym2 V) ∧ z ∈ (f : Sym2 V) := by
      by_contra hnone
      apply hdisj
      intro z hzax hzf
      exact hnone ⟨z, hzax, hzf⟩
    obtain ⟨z, hzax, hzf⟩ := hshared
    have hz : z = a ∨ z = x := by simpa using hzax
    rcases hz with hza | hzx
    · have hfe := retained_edge_eq_external_of_incident_two G ha hax hau hxu
        f hfD (hza ▸ hzf)
      exact Finset.mem_insert.mpr (Or.inr (by
        apply (mem_incidentEdgeFinset (G := G)).mpr
        rw [hfe]
        simp))
    · exact False.elim (hfx (hzx ▸ hzf))

/-! Matching-coloured edges are geometrically close but do not block an
induced colour.  The general `Availability` bound intentionally overcounts
them; the sharper filtered form below is needed in the `1,1` outer-colour
case of Lemma 3.4. -/

noncomputable def activeInducedBlockerEdgesOn {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet) : Finset G.edgeSet :=
  (inducedBlockerEdgesOn G D colour e).filter fun f => colour f ≠ none

@[simp] theorem mem_activeInducedBlockerEdgesOn {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e f : G.edgeSet) :
    f ∈ activeInducedBlockerEdgesOn G D colour e ↔
      f ∈ D ∧ f ≠ e ∧ ¬ InducedSeparated G e f ∧ colour f ≠ none := by
  classical
  simp [activeInducedBlockerEdgesOn, and_assoc]

theorem card_blockedInducedColorsOn_le_card_activeBlockers {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet) :
    (blockedInducedColorsOn G D colour e).card ≤
      (activeInducedBlockerEdgesOn G D colour e).card := by
  classical
  let A := {i : Fin k // i ∈ blockedInducedColorsOn G D colour e}
  let B := {f : G.edgeSet // f ∈ activeInducedBlockerEdgesOn G D colour e}
  let R : A → B → Prop := fun i f => colour f.1 = some i.1
  letI : DecidableRel R := fun _ _ => Classical.propDecidable _
  have hleft : ∀ i : A,
      1 ≤ (Finset.univ.filter fun f : B => R i f).card := by
    intro i
    obtain ⟨f, hf, hcolour⟩ :=
      exists_blocker_of_mem_blockedInducedColorsOn G D colour e i.2
    have hfactive : f ∈ activeInducedBlockerEdgesOn G D colour e := by
      apply Finset.mem_filter.mpr
      exact ⟨hf, by simp [hcolour]⟩
    apply Finset.card_pos.mpr
    exact ⟨⟨f, hfactive⟩, by simp [R, hcolour]⟩
  have hright : ∀ f : B,
      (Finset.univ.filter fun i : A => R i f).card ≤ 1 := by
    intro f
    apply Finset.card_le_one_iff.mpr
    intro i j hi hj
    apply Subtype.ext
    have hi' : colour f.1 = some i.1 := by simpa [R] using hi
    have hj' : colour f.1 = some j.1 := by simpa [R] using hj
    exact Option.some.inj (hi'.symm.trans hj')
  have hcount := mul_card_le_mul_card_of_relation R 1 1 hleft hright
  have hA : Fintype.card A =
      (blockedInducedColorsOn G D colour e).card := by
    simpa only [A] using
      (Fintype.card_coe (blockedInducedColorsOn G D colour e))
  have hB : Fintype.card B =
      (activeInducedBlockerEdgesOn G D colour e).card := by
    simpa only [B] using
      (Fintype.card_coe (activeInducedBlockerEdgesOn G D colour e))
  rw [hA, hB] at hcount
  simpa only [Nat.one_mul] using hcount

theorem exists_available_induced_of_card_activeBlockers_lt {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet)
    (hcard : (activeInducedBlockerEdgesOn G D colour e).card < k) :
    ∃ i : Fin k, ColorAvailableOn G D colour e (some i) := by
  apply exists_available_induced_of_card_blocked_lt G D colour e
  exact lt_of_le_of_lt
    (card_blockedInducedColorsOn_le_card_activeBlockers G D colour e) hcard

/-! ## The two availability counts in Lemma 3.4 -/

theorem exists_available_left_chain_colour
    (hsub : IsSubcubic G)
    {a x b u w : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hau : G.Adj a u) (hxu : x ≠ u)
    (hbw : G.Adj b w) (hxw : x ≠ w)
    (colour : G.edgeSet → OneTwoColor 5) :
    ∃ i : Fin 5,
      ColorAvailableOn G (RetainedEdges (G.deleteIncidenceSet x) G)
        colour (⟨s(a, x), hax⟩ : G.edgeSet) (some i) := by
  let S : Finset G.edgeSet :=
    insert (⟨s(b, w), hbw⟩ : G.edgeSet) (incidentEdgeFinset G u)
  have hsubBlock : activeInducedBlockerEdgesOn G
      (RetainedEdges (G.deleteIncidenceSet x) G) colour
        (⟨s(a, x), hax⟩ : G.edgeSet) ⊆ S := by
    intro f hf
    apply inducedBlockerEdgesOn_left_subset G ha hx hb hax hxb hab hau hxu
      hbw hxw
    exact (Finset.mem_filter.mp hf).1
  have hScard : S.card < 5 := by
    have hins : S.card ≤ (incidentEdgeFinset G u).card + 1 :=
      Finset.card_insert_le _ _
    rw [card_incidentEdgeFinset G u] at hins
    have hdu := hsub u
    omega
  apply exists_available_induced_of_card_activeBlockers_lt G
  exact lt_of_le_of_lt (Finset.card_le_card hsubBlock) hScard

/-- After the left chain edge has been inserted, every blocker of the right
chain edge is either that new edge, the left external edge, or incident with
the right external neighbor. -/
theorem inducedBlockerEdgesOn_right_subset
    {a x b u w : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hau : G.Adj a u) (hxu : x ≠ u)
    (hbw : G.Adj b w) (hxw : x ≠ w)
    {colour : G.edgeSet → OneTwoColor 5} :
    inducedBlockerEdgesOn G
        (insert (⟨s(a, x), hax⟩ : G.edgeSet)
          (RetainedEdges (G.deleteIncidenceSet x) G))
        colour (⟨s(b, x), hxb.symm⟩ : G.edgeSet) ⊆
      insert (⟨s(a, x), hax⟩ : G.edgeSet)
        (insert (⟨s(a, u), hau⟩ : G.edgeSet)
          (incidentEdgeFinset G w)) := by
  classical
  intro f hf
  have hf' := (mem_inducedBlockerEdgesOn G
    (insert (⟨s(a, x), hax⟩ : G.edgeSet)
      (RetainedEdges (G.deleteIncidenceSet x) G)) colour
    (⟨s(b, x), hxb.symm⟩ : G.edgeSet) f).mp hf
  rcases hf' with ⟨hfD, hfne, hfsep⟩
  rcases hfD with hfe | hfD
  · exact Finset.mem_insert.mpr (Or.inl hfe)
  · apply Finset.mem_insert.mpr
    right
    have hgeom := inducedBlockerEdgesOn_left_subset G hb hx ha hxb.symm
      hax.symm hab.symm hbw hxw hau hxu
      (colour := colour)
    apply hgeom
    apply (mem_inducedBlockerEdgesOn G
      (RetainedEdges (G.deleteIncidenceSet x) G) colour
      (⟨s(b, x), hxb.symm⟩ : G.edgeSet) f).mpr
    exact ⟨hfD, hfne, hfsep⟩

/-- If the right external edge has the matching colour, the right chain
edge has an available induced colour after the left edge is inserted. -/
theorem exists_available_right_chain_colour_of_external_matching
    (hsub : IsSubcubic G)
    {a x b u w : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hau : G.Adj a u) (hxu : x ≠ u)
    (hbw : G.Adj b w) (hxw : x ≠ w)
    (colour : G.edgeSet → OneTwoColor 5)
    (hright : colour (⟨s(b, w), hbw⟩ : G.edgeSet) = none) :
    ∃ i : Fin 5,
      ColorAvailableOn G
        (insert (⟨s(a, x), hax⟩ : G.edgeSet)
          (RetainedEdges (G.deleteIncidenceSet x) G))
        colour (⟨s(b, x), hxb.symm⟩ : G.edgeSet) (some i) := by
  classical
  let eLeft : G.edgeSet := ⟨s(a, x), hax⟩
  let eOuterLeft : G.edgeSet := ⟨s(a, u), hau⟩
  let eOuterRight : G.edgeSet := ⟨s(b, w), hbw⟩
  let S : Finset G.edgeSet :=
    insert eLeft (insert eOuterLeft ((incidentEdgeFinset G w).erase eOuterRight))
  have hsubBlock : activeInducedBlockerEdgesOn G
      (insert eLeft (RetainedEdges (G.deleteIncidenceSet x) G)) colour
        (⟨s(b, x), hxb.symm⟩ : G.edgeSet) ⊆ S := by
    intro f hf
    have hgeom := inducedBlockerEdgesOn_right_subset G ha hx hb hax hxb hab
      hau hxu hbw hxw (colour := colour)
    have hfgeom := hgeom (Finset.mem_filter.mp hf).1
    rcases Finset.mem_insert.mp hfgeom with hfl | hfrest
    · exact Finset.mem_insert.mpr (Or.inl hfl)
    · rcases Finset.mem_insert.mp hfrest with hfol | hfw
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hfol)))
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_erase.mpr
        refine ⟨?_, hfw⟩
        intro hEq
        subst f
        exact (Finset.mem_filter.mp hf).2 hright
  have hOuterMem : eOuterRight ∈ incidentEdgeFinset G w := by
    apply (mem_incidentEdgeFinset (G := G)).mpr
    simp [eOuterRight]
  have herase : ((incidentEdgeFinset G w).erase eOuterRight).card + 1 =
      G.degree w := by
    rw [Finset.card_erase_of_mem hOuterMem, card_incidentEdgeFinset]
    have hdpos : 0 < G.degree w := hbw.degree_pos_right
    omega
  have hScard : S.card < 5 := by
    have hcard : S.card ≤
        ((incidentEdgeFinset G w).erase eOuterRight).card + 2 := by
      exact (Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
    have hd := hsub w
    omega
  apply exists_available_induced_of_card_activeBlockers_lt G
  exact lt_of_le_of_lt (Finset.card_le_card hsubBlock) hScard

/-! ## Completing the partial colouring -/

theorem left_chain_edge_not_retained
    {a x : V} (hax : G.Adj a x) :
    (⟨s(a, x), hax⟩ : G.edgeSet) ∉
      RetainedEdges (G.deleteIncidenceSet x) G := by
  rw [mem_retained_deleteIncidenceSet_iff]
  simp

theorem right_chain_edge_not_retained
    {x b : V} (hxb : G.Adj x b) :
    (⟨s(b, x), hxb.symm⟩ : G.edgeSet) ∉
      RetainedEdges (G.deleteIncidenceSet x) G := by
  rw [mem_retained_deleteIncidenceSet_iff]
  simp

theorem chain_edges_ne {a x b : V}
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b) :
    (⟨s(a, x), hax⟩ : G.edgeSet) ≠
      (⟨s(b, x), hxb.symm⟩ : G.edgeSet) := by
  intro heq
  have hval : s(a, x) = s(b, x) := congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hval
  rcases hval with h | h
  · exact hab h.1
  · exact hax.ne h.1

theorem insert_chain_edges_retained_eq_univ
    {a x b : V} (hx : IsTwoVertex G x)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b) :
    insert (⟨s(b, x), hxb.symm⟩ : G.edgeSet)
        (insert (⟨s(a, x), hax⟩ : G.edgeSet)
          (RetainedEdges (G.deleteIncidenceSet x) G)) = Set.univ := by
  ext f
  simp only [Set.mem_insert_iff, Set.mem_univ, iff_true]
  by_cases hxf : x ∈ (f : Sym2 V)
  · rcases edge_eq_left_or_right_of_incident_two G hx hax.symm hxb hab
        f hxf with hf | hf
    · right
      left
      apply Subtype.ext
      simpa only [Sym2.eq_swap] using hf
    · left
      apply Subtype.ext
      simpa only [Sym2.eq_swap] using hf
  · exact Or.inr (Or.inr
      ((mem_retained_deleteIncidenceSet_iff G x f).mpr hxf))

/-- When the right external edge is not matching-coloured, the matching
colour is available on the right chain edge after assigning an induced
colour to the left chain edge. -/
theorem matching_available_on_right_of_external_nonmatching
    {a x b u w : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hau : G.Adj a u) (hxu : x ≠ u)
    (hbw : G.Adj b w) (hxw : x ≠ w)
    (base : G.edgeSet → OneTwoColor 5) (i : Fin 5)
    (hright : base (⟨s(b, w), hbw⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G
      (insert (⟨s(a, x), hax⟩ : G.edgeSet)
        (RetainedEdges (G.deleteIncidenceSet x) G))
      (recolor G base (⟨s(a, x), hax⟩ : G.edgeSet) (some i))
      (⟨s(b, x), hxb.symm⟩ : G.edgeSet) none := by
  classical
  apply (colorAvailableOn_none_iff G _ _ _).mpr
  intro f hfD hfe hfcolour
  intro z hzright hzf
  have hz : z = b ∨ z = x := by simpa using hzright
  rcases hz with hzb | hzx
  · have hbf : b ∈ (f : Sym2 V) := hzb ▸ hzf
    rcases hfD with hfl | hfD
    · subst f
      have : b ∈ (s(a, x) : Sym2 V) := hbf
      have hbax : b = a ∨ b = x := by simpa using this
      rcases hbax with hba | hbx
      · exact hab hba.symm
      · exact hxb.ne (hbx.symm)
    · have hfeq := retained_edge_eq_external_of_incident_two G hb hxb.symm
        hbw hxw f hfD hbf
      have hOuterLeftNe :
          (⟨s(b, w), hbw⟩ : G.edgeSet) ≠
            (⟨s(a, x), hax⟩ : G.edgeSet) := by
        intro heq
        have hxmem : x ∈ (s(a, x) : Sym2 V) := by simp
        have heqval : s(b, w) = s(a, x) := congrArg Subtype.val heq
        have hxmem' : x ∈ (s(b, w) : Sym2 V) := by
          rw [heqval]
          exact hxmem
        have hxcase : x = b ∨ x = w := by simpa using hxmem'
        rcases hxcase with h | h
        · exact hxb.ne h
        · exact hxw h
      have hbaseOuter : base (⟨s(b, w), hbw⟩ : G.edgeSet) = none := by
        have hrecOuter :
            recolor G base (⟨s(a, x), hax⟩ : G.edgeSet) (some i)
              (⟨s(b, w), hbw⟩ : G.edgeSet) = none := by
          simpa [hfeq] using hfcolour
        rw [recolor_ne G base (some i) hOuterLeftNe] at hrecOuter
        exact hrecOuter
      exact hright hbaseOuter
  · have hxf : x ∈ (f : Sym2 V) := hzx ▸ hzf
    rcases hfD with hfl | hfD
    · subst f
      simp at hfcolour
    · exact ((mem_retained_deleteIncidenceSet_iff G x f).mp hfD) hxf

theorem external_right_ne_left_chain
    {a x b w : V} (hax : G.Adj a x) (hxb : G.Adj x b)
    (hbw : G.Adj b w) (hxw : x ≠ w) :
    (⟨s(b, w), hbw⟩ : G.edgeSet) ≠
      (⟨s(a, x), hax⟩ : G.edgeSet) := by
  intro heq
  have heqval : s(b, w) = s(a, x) := congrArg Subtype.val heq
  have hxmem : x ∈ (s(a, x) : Sym2 V) := by simp
  have hxmem' : x ∈ (s(b, w) : Sym2 V) := by
    rw [heqval]
    exact hxmem
  have hxcase : x = b ∨ x = w := by simpa using hxmem'
  rcases hxcase with h | h
  · exact hxb.ne h
  · exact hxw h

/-- Packing-validity part of the three-chain extension.  The proof has two
honest branches.  If the right external edge is nonmatching, the right
chain edge receives the matching colour.  If it is matching, both chain
edges receive available induced colours.  This subsumes the paper's four
pair-symmetry classes. -/
theorem exists_valid_extension_of_three_chain
    (hsub : IsSubcubic G)
    {a x b u w : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hau : G.Adj a u) (hxu : x ≠ u)
    (hbw : G.Adj b w) (hxw : x ≠ w)
    (small : (G.deleteIncidenceSet x).edgeSet → OneTwoColor 5)
    (hsmall : IsOneTwoColoring (G.deleteIncidenceSet x) small) :
    let base := transportColoringToSupergraph (G.deleteIncidenceSet_le x) small
    let eLeft : G.edgeSet := ⟨s(a, x), hax⟩
    let eRight : G.edgeSet := ⟨s(b, x), hxb.symm⟩
    ∃ colour : G.edgeSet → OneTwoColor 5,
      IsOneTwoColoring G colour ∧
        ColoringsAgreeOff G ({eLeft, eRight} : Set G.edgeSet) base colour := by
  classical
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet x) G
  let eLeft : G.edgeSet := ⟨s(a, x), hax⟩
  let eRight : G.edgeSet := ⟨s(b, x), hxb.symm⟩
  let eOuterRight : G.edgeSet := ⟨s(b, w), hbw⟩
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le x) small
  have hbase : IsOneTwoColoringOn G D base := by
    simpa [D, base] using
      (transport_deleteIncidenceSet_valid (G := G) x hsmall)
  obtain ⟨i, hi⟩ := exists_available_left_chain_colour G hsub ha hx hb hax
    hxb hab hau hxu hbw hxw base
  let afterLeft := recolor G base eLeft (some i)
  have heLeft : eLeft ∉ D := by
    exact left_chain_edge_not_retained G hax
  have hafterLeft : IsOneTwoColoringOn G (insert eLeft D) afterLeft := by
    exact hbase.extend_one G heLeft hi
  by_cases hright : base eOuterRight = none
  · have heOuterRightLeft : eOuterRight ≠ eLeft := by
      exact external_right_ne_left_chain G hax hxb hbw hxw
    have hrightAfter : afterLeft eOuterRight = none := by
      dsimp [afterLeft]
      rw [recolor_ne G base (some i) heOuterRightLeft]
      exact hright
    obtain ⟨j, hj⟩ :=
      exists_available_right_chain_colour_of_external_matching G hsub ha hx hb
        hax hxb hab hau hxu hbw hxw afterLeft hrightAfter
    let final := recolor G afterLeft eRight (some j)
    have heRight : eRight ∉ insert eLeft D := by
      simp only [Set.mem_insert_iff, not_or]
      exact ⟨(chain_edges_ne G hax hxb hab).symm,
        right_chain_edge_not_retained G hxb⟩
    have hfinal : IsOneTwoColoringOn G (insert eRight (insert eLeft D)) final :=
      hafterLeft.extend_one G heRight hj
    refine ⟨final, ?_, ?_⟩
    · simpa [IsOneTwoColoring, D, eLeft, eRight,
        insert_chain_edges_retained_eq_univ G hx hax hxb hab] using hfinal
    · intro f hf
      have hne : f ≠ eLeft ∧ f ≠ eRight := by simpa using hf
      change base f = final f
      simp [final, afterLeft, recolor, hne.1, hne.2]
  · have hmatching : ColorAvailableOn G (insert eLeft D) afterLeft eRight none := by
      exact matching_available_on_right_of_external_nonmatching G ha hx hb hax
        hxb hab hau hxu hbw hxw base i hright
    let final := recolor G afterLeft eRight none
    have heRight : eRight ∉ insert eLeft D := by
      simp only [Set.mem_insert_iff, not_or]
      exact ⟨(chain_edges_ne G hax hxb hab).symm,
        right_chain_edge_not_retained G hxb⟩
    have hfinal : IsOneTwoColoringOn G (insert eRight (insert eLeft D)) final :=
      hafterLeft.extend_one G heRight hmatching
    refine ⟨final, ?_, ?_⟩
    · simpa [IsOneTwoColoring, D, eLeft, eRight,
        insert_chain_edges_retained_eq_univ G hx hax hxb hab] using hfinal
    · intro f hf
      have hne : f ≠ eLeft ∧ f ≠ eRight := by simpa using hf
      change base f = final f
      simp [final, afterLeft, recolor, hne.1, hne.2]

/-! ## Moving Condition I across the incidence deletion -/

theorem degree_deleteIncidenceSet_eq_of_not_adj
    {x z : V} (hzx : z ≠ x) (hnadj : ¬ G.Adj z x) :
    (G.deleteIncidenceSet x).degree z = G.degree z := by
  have hadj (v : V) :
      (G.deleteIncidenceSet x).Adj z v ↔ G.Adj z v := by
    rw [deleteIncidenceSet_adj]
    constructor
    · exact fun h => h.1
    · intro hzv
      refine ⟨hzv, hzx, ?_⟩
      intro hvx
      subst v
      exact hnadj hzv
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext v
  rw [G.mem_neighborFinset, (G.deleteIncidenceSet x).mem_neighborFinset,
    hadj]

theorem vertexSeesMatching_transport_deleteIncidenceSet_iff_of_not_adj
    {k : ℕ} {x z : V} (hzx : z ≠ x) (hnadj : ¬ G.Adj z x)
    (small : (G.deleteIncidenceSet x).edgeSet → OneTwoColor k) :
    VertexSeesMatching G
        (transportColoringToSupergraph (G.deleteIncidenceSet_le x) small) z ↔
      VertexSeesMatching (G.deleteIncidenceSet x) small z := by
  rw [vertexSeesMatching_iff, vertexSeesMatching_iff]
  constructor
  · rintro ⟨e, hecolour, hze⟩
    have heRet : e.1 ∈ (G.deleteIncidenceSet x).edgeSet := by
      by_contra heNot
      have hxe : x ∈ (e : Sym2 V) := by
        by_contra hxe
        exact heNot ((mem_retained_deleteIncidenceSet_iff G x e).mpr hxe)
      have hzxAdj : G.Adj z x :=
        G.adj_of_mem_incidenceSet hzx
          ((G.edge_mem_incidenceSet_iff).mpr hze)
          ((G.edge_mem_incidenceSet_iff).mpr hxe)
      exact hnadj hzxAdj
    let eH : (G.deleteIncidenceSet x).edgeSet := ⟨e.1, heRet⟩
    refine ⟨eH, ?_, hze⟩
    rw [transportColoringToSupergraph_of_mem
      (G.deleteIncidenceSet_le x) small heRet] at hecolour
    exact hecolour
  · rintro ⟨e, hecolour, hze⟩
    let eG := edgeEmbeddingOfLE (G.deleteIncidenceSet_le x) e
    refine ⟨eG, ?_, hze⟩
    simpa [eG] using hecolour

theorem vertexSeesInduced_transport_deleteIncidenceSet_iff_of_not_adj
    {k : ℕ} {x z : V} (hzx : z ≠ x) (hnadj : ¬ G.Adj z x)
    (small : (G.deleteIncidenceSet x).edgeSet → OneTwoColor k) (i : Fin k) :
    VertexSeesInduced G
        (transportColoringToSupergraph (G.deleteIncidenceSet_le x) small) z i ↔
      VertexSeesInduced (G.deleteIncidenceSet x) small z i := by
  rw [vertexSeesInduced_iff, vertexSeesInduced_iff]
  constructor
  · rintro ⟨e, hecolour, v, hve, hzv⟩
    have heRet : e.1 ∈ (G.deleteIncidenceSet x).edgeSet := by
      by_contra heNot
      have hnone :
          transportColoringToSupergraph (G.deleteIncidenceSet_le x) small e =
            none := by
        simp [transportColoringToSupergraph, heNot]
      rw [hnone] at hecolour
      simp at hecolour
    let eH : (G.deleteIncidenceSet x).edgeSet := ⟨e.1, heRet⟩
    refine ⟨eH, ?_, v, hve, ?_⟩
    · rw [transportColoringToSupergraph_of_mem
        (G.deleteIncidenceSet_le x) small heRet] at hecolour
      exact hecolour
    · rcases hzv with rfl | hzv
      · exact Or.inl rfl
      · right
        apply deleteIncidenceSet_adj.mpr
        refine ⟨hzv, hzx, ?_⟩
        intro hvx
        subst v
        exact hnadj hzv
  · rintro ⟨e, hecolour, v, hve, hzv⟩
    let eG := edgeEmbeddingOfLE (G.deleteIncidenceSet_le x) e
    refine ⟨eG, ?_, v, hve, ?_⟩
    · simpa [eG] using hecolour
    · rcases hzv with rfl | hzv
      · exact Or.inl rfl
      · exact Or.inr ((G.deleteIncidenceSet_le x) hzv)

theorem not_adj_chain_center_of_ne_ends
    {a x b z : V} (hx : IsTwoVertex G x)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hza : z ≠ a) (hzb : z ≠ b) : ¬ G.Adj z x := by
  intro hzx
  have hzN : z ∈ G.neighborFinset x :=
    (G.mem_neighborFinset x z).mpr hzx.symm
  rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxb hab] at hzN
  have hz : z = a ∨ z = b := by simpa using hzN
  exact hz.elim hza hzb

/-- The transported smaller colouring already satisfies Condition I in the
ambient graph.  At the three changed-degree vertices the structural
five-edge capacity lemma applies; everywhere else degrees and visibility
are identical to the incidence-deleted graph. -/
theorem conditionI_transport_deleteIncidenceSet_of_three_chain
    (hsub : IsSubcubic G)
    {a x b : V} (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (small : (G.deleteIncidenceSet x).edgeSet → OneTwoColor 5)
    (hsmall : ConditionI (G.deleteIncidenceSet x) small) :
    ConditionI G
      (transportColoringToSupergraph (G.deleteIncidenceSet_le x) small) := by
  intro z hz hmatch hall
  by_cases hza : z = a
  · subst z
    exact (paletteCondition_at_of_adjacent_two G hsub ha hax hx hmatch) hall
  by_cases hzx : z = x
  · subst z
    exact (paletteCondition_at_of_adjacent_two G hsub hx hax.symm ha hmatch) hall
  by_cases hzb : z = b
  · subst z
    exact (paletteCondition_at_of_adjacent_two G hsub hb hxb.symm hx hmatch) hall
  have hnadj : ¬ G.Adj z x :=
    not_adj_chain_center_of_ne_ends G hx hax hxb hab hza hzb
  have hzSmall : IsTwoVertex (G.deleteIncidenceSet x) z := by
    unfold IsTwoVertex at hz ⊢
    rw [degree_deleteIncidenceSet_eq_of_not_adj G hzx hnadj]
    exact hz
  apply hsmall z hzSmall
  · exact (vertexSeesMatching_transport_deleteIncidenceSet_iff_of_not_adj G
      hzx hnadj small).mp hmatch
  · intro i
    exact (vertexSeesInduced_transport_deleteIncidenceSet_iff_of_not_adj G
      hzx hnadj small i).mp (hall i)

/-- Every vertex in the palette influence domain of the two chain edges
has a degree-two neighbor.  No distinctness assumptions on the two external
neighbors occur here. -/
theorem exists_adjacent_two_of_paletteAffected_chain_edges
    {a x b z : V} (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hax : G.Adj a x) (hxb : G.Adj x b)
    (haffect : PaletteAffectedBy G
      ({(⟨s(a, x), hax⟩ : G.edgeSet),
        (⟨s(b, x), hxb.symm⟩ : G.edgeSet)} : Set G.edgeSet) z) :
    ∃ q : V, G.Adj z q ∧ IsTwoVertex G q := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, he, v, hve, hzv⟩ := haffect
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with he | he
  · subst e
    have hv : v = a ∨ v = x := by simpa using hve
    rcases hzv with hzv | hzv
    · rcases hv with hva | hvx
      · refine ⟨x, ?_, hx⟩
        simpa [hzv, hva] using hax
      · refine ⟨a, ?_, ha⟩
        simpa [hzv, hvx] using hax.symm
    · rcases hv with hva | hvx
      · exact ⟨a, by simpa [hva] using hzv, ha⟩
      · exact ⟨x, by simpa [hvx] using hzv, hx⟩
  · subst e
    have hv : v = b ∨ v = x := by simpa using hve
    rcases hzv with hzv | hzv
    · rcases hv with hvb | hvx
      · refine ⟨x, ?_, hx⟩
        simpa [hzv, hvb] using hxb.symm
      · refine ⟨b, ?_, hb⟩
        simpa [hzv, hvx] using hxb
    · rcases hv with hvb | hvx
      · exact ⟨b, by simpa [hvb] using hzv, hb⟩
      · exact ⟨x, by simpa [hvx] using hzv, hx⟩

/-- Exact good-colouring extension across a three-chain. -/
theorem exists_goodFive_extension_of_three_chain
    (hsub : IsSubcubic G)
    {a x b u w : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b)
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (hau : G.Adj a u) (hxu : x ≠ u)
    (hbw : G.Adj b w) (hxw : x ≠ w)
    (small : (G.deleteIncidenceSet x).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (G.deleteIncidenceSet x) small) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  let base := transportColoringToSupergraph (G.deleteIncidenceSet_le x) small
  let eLeft : G.edgeSet := ⟨s(a, x), hax⟩
  let eRight : G.edgeSet := ⟨s(b, x), hxb.symm⟩
  have hbaseCondition : ConditionI G base := by
    exact conditionI_transport_deleteIncidenceSet_of_three_chain G hsub ha hx hb
      hax hxb hab small hsmall.paletteCondition
  obtain ⟨colour, hvalid, hagree⟩ :=
    exists_valid_extension_of_three_chain G hsub ha hx hb hax hxb hab hau hxu
      hbw hxw small hsmall.valid
  have hcondition : ConditionI G colour := by
    apply ConditionI.of_agreeOff G hbaseCondition hagree
    intro z hz haffect hmatch
    obtain ⟨q, hzq, hq⟩ :=
      exists_adjacent_two_of_paletteAffected_chain_edges G ha hx hb hax hxb
        haffect
    exact paletteCondition_at_of_adjacent_two G hsub hz hzq hq hmatch
  exact ⟨colour, hvalid, hcondition⟩

/-! ## From a certified `3`-chain to the local configuration -/

/-- The ordered local data carried by a certified three-chain. -/
structure ThreeChainCore (a x b : V) : Prop where
  left_two : IsTwoVertex G a
  center_two : IsTwoVertex G x
  right_two : IsTwoVertex G b
  left_adj : G.Adj a x
  right_adj : G.Adj x b
  ends_ne : a ≠ b

theorem IsKChain.threeChainCore {a b : V} {p : G.Walk a b}
    (hp : IsKChain G p 3) : ThreeChainCore G a (p.getVert 1) b := by
  have hlen : p.length = 2 := by
    have := hp.length
    omega
  have hleft : G.Adj a (p.getVert 1) := by
    have h := p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
    simpa using h
  have hright : G.Adj (p.getVert 1) b := by
    have h := p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
    have hend : p.getVert 2 = b := by
      rw [← hlen]
      exact p.getVert_length
    simpa [hend] using h
  have hleftTwo : IsTwoVertex G a := by
    have h := hp.2.2 (p.getVert 0) (p.getVert_mem_support 0)
    simpa using h
  have hcenterTwo : IsTwoVertex G (p.getVert 1) :=
    hp.2.2 (p.getVert 1) (p.getVert_mem_support 1)
  have hrightTwo : IsTwoVertex G b := by
    have h := hp.2.2 (p.getVert 2) (p.getVert_mem_support 2)
    have hend : p.getVert 2 = b := by
      rw [← hlen]
      exact p.getVert_length
    simpa [hend] using h
  have hab : a ≠ b := by
    intro hab
    have hzero : p.getVert 0 = a := by simp
    have htwo : p.getVert 2 = b := by
      rw [← hlen]
      exact p.getVert_length
    have heq : p.getVert 0 = p.getVert 2 := by simp [hzero, htwo, hab]
    have hi := hp.1.getVert_injOn
      (show 0 ∈ {i : ℕ | i ≤ p.length} by simp)
      (show 2 ∈ {i : ℕ | i ≤ p.length} by simp [hlen]) heq
    omega
  exact ⟨hleftTwo, hcenterTwo, hrightTwo, hleft, hright, hab⟩

end Finite

/-! ## Decidability-instance transport -/

section DecidableIrrel

variable [Fintype V]

/-- `GoodFive` is independent of the algorithm used to decide adjacency.
The only apparently instance-dependent ingredient is degree; rewriting it as
the `Nat.card` of the neighbor set exposes its semantic invariance. -/
theorem goodFive_change_decidableRel
    (d₁ d₂ : DecidableRel G.Adj)
    (colour : G.edgeSet → OneTwoColor 5)
    (h : @GoodFive V G _ d₁ colour) :
    @GoodFive V G _ d₂ colour := by
  refine ⟨h.1, ?_⟩
  intro u hu hmatching hall
  have huCard : Nat.card (G.neighborSet u) = 2 := by
    letI : DecidableRel G.Adj := d₂
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
    exact hu
  have huOld : @IsTwoVertex V G _ d₁ u := by
    letI : DecidableRel G.Adj := d₁
    rw [IsTwoVertex, ← G.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card]
    exact huCard
  apply h.2 u
  · exact huOld
  · exact hmatching
  · exact hall

end DecidableIrrel

/-! ## Lemma 3.4 for an edge-minimal bad graph -/

section ClassicalMinimal

variable [Fintype V] [DecidableEq V]

/- Paper Lemma 3.4: an edge-minimal Section 3 counterexample contains no
three-chain.  `SectionThreeEligible` and `HasGoodFive` deliberately choose
their decidability instances internally, so the chain predicate is stated
with that same canonical classical instance.  Only subcubicity and MAD
heredity are used; there is no girth or hidden availability hypothesis. -/
set_option maxHeartbeats 800000 in
theorem IsEdgeMinimalBad.no_three_chain_sectionThree
    (hmin : IsEdgeMinimalBad SectionThreeEligible HasGoodFive G)
    {a b : V} (p : G.Walk a b) :
    ¬ @IsKChain V G _ (Classical.decRel G.Adj) a b p 3 := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  intro hp
  let x : V := p.getVert 1
  have hcore : ThreeChainCore G a x b := hp.threeChainCore G
  obtain ⟨u, hux, hau⟩ :=
    exists_other_neighbor_of_isTwoVertex G hcore.left_two hcore.left_adj
  obtain ⟨w, hwx, hbw⟩ :=
    exists_other_neighbor_of_isTwoVertex G hcore.right_two hcore.right_adj.symm
  have hEligibleG : IsSubcubic G ∧ MaximumAverageDegreeLT G 12 5 := by
    simpa [SectionThreeEligible] using hmin.eligible
  letI : DecidableRel (G.deleteIncidenceSet x).Adj :=
    Classical.decRel (G.deleteIncidenceSet x).Adj
  have hEligibleDelete : SectionThreeEligible (G.deleteIncidenceSet x) := by
    rw [SectionThreeEligible]
    constructor
    · intro z
      exact ((G.deleteIncidenceSet x).degree_le_of_le
        (G.deleteIncidenceSet_le x)).trans (hEligibleG.1 z)
    · exact MaximumAverageDegreeLT.mono (G.deleteIncidenceSet_le x) hEligibleG.2
  have hxIncident : ∃ e : G.edgeSet, x ∈ (e : Sym2 V) :=
    ⟨⟨s(a, x), hcore.left_adj⟩, by simp⟩
  have hgoodDelete : HasGoodFive (G.deleteIncidenceSet x) :=
    hmin.good_deleteIncidenceSet hxIncident hEligibleDelete
  rw [HasGoodFive] at hgoodDelete
  obtain ⟨small, hsmall⟩ := hgoodDelete
  have hsmallDerived :
      @GoodFive V (G.deleteIncidenceSet x) _
        (@SimpleGraph.instDecidableRelAdjDeleteIncidenceSet V _ G _ x) small :=
    goodFive_change_decidableRel (G := G.deleteIncidenceSet x)
      (Classical.decRel (G.deleteIncidenceSet x).Adj)
      (@SimpleGraph.instDecidableRelAdjDeleteIncidenceSet V _ G _ x)
      small hsmall
  obtain ⟨colour, hgood⟩ :=
    exists_goodFive_extension_of_three_chain G hEligibleG.1
      hcore.left_two hcore.center_two hcore.right_two
      hcore.left_adj hcore.right_adj hcore.ends_ne hau hux.symm hbw hwx.symm
      small hsmallDerived
  apply hmin.not_good
  rw [HasGoodFive]
  exact ⟨colour, hgood⟩

end ClassicalMinimal

end


end LeanCo.PackingEdgeColoring
