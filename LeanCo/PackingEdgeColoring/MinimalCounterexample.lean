import LeanCo.PackingEdgeColoring.LocalColoring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Edge-minimal counterexamples and colouring transport

This file isolates the bookkeeping shared by deletion-and-extension
arguments.  In particular, it does not pretend that a packing colouring of
an arbitrary spanning subgraph is automatically valid in the supergraph:
a restored edge can create a new distance-two conflict.  The exact
adjacency-reflection hypothesis under which transport is valid is made
explicit below; deleting all edges incident with a vertex satisfies it.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

/-! ## Induction and minimal bad graphs -/

/-- An instance-independent graph edge count.  On finite graphs this is exactly
`G.edgeFinset.card`. -/
def EdgeCount (G : SimpleGraph V) : ℕ :=
  G.edgeSet.ncard

theorem edgeCount_eq_edgeFinset_card [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] : EdgeCount G = G.edgeFinset.card := by
  simpa [EdgeCount, edgeFinset] using Set.ncard_eq_toFinset_card' G.edgeSet

/-- Strong induction over the number of edges, with the vertex type fixed. -/
theorem edgeCount_strong_induction (P : SimpleGraph V → Prop)
    (step : ∀ H : SimpleGraph V,
      (∀ K : SimpleGraph V, EdgeCount K < EdgeCount H → P K) → P H) :
    ∀ H : SimpleGraph V, P H := by
  intro H
  generalize hn : EdgeCount H = n
  induction n using Nat.strong_induction_on generalizing H with
  | h n ih =>
      apply step H
      intro K hKH
      apply ih (EdgeCount K)
      · simpa [hn] using hKH
      · rfl

/-- `G` is an edge-minimal counterexample to `Good` among graphs satisfying
`Eligible`. -/
def IsEdgeMinimalBad (Eligible Good : SimpleGraph V → Prop)
    (G : SimpleGraph V) : Prop :=
  Eligible G ∧ ¬ Good G ∧
    ∀ H : SimpleGraph V, Eligible H → EdgeCount H < EdgeCount G → Good H

theorem IsEdgeMinimalBad.eligible {Eligible Good : SimpleGraph V → Prop}
    {G : SimpleGraph V} (h : IsEdgeMinimalBad Eligible Good G) : Eligible G :=
  h.1

theorem IsEdgeMinimalBad.not_good {Eligible Good : SimpleGraph V → Prop}
    {G : SimpleGraph V} (h : IsEdgeMinimalBad Eligible Good G) : ¬ Good G :=
  h.2.1

theorem IsEdgeMinimalBad.good_of_smaller {Eligible Good : SimpleGraph V → Prop}
    {G H : SimpleGraph V} (h : IsEdgeMinimalBad Eligible Good G)
    (hEligible : Eligible H) (hcard : EdgeCount H < EdgeCount G) : Good H :=
  h.2.2 H hEligible hcard

/-- If a bad eligible graph exists, an edge-minimal one exists. -/
theorem exists_edgeMinimalBad {Eligible Good : SimpleGraph V → Prop}
    (hex : ∃ G : SimpleGraph V, Eligible G ∧ ¬ Good G) :
    ∃ G : SimpleGraph V, IsEdgeMinimalBad Eligible Good G := by
  classical
  let p : ℕ → Prop := fun n =>
    ∃ G : SimpleGraph V, Eligible G ∧ ¬ Good G ∧ EdgeCount G = n
  have hp : ∃ n, p n := by
    obtain ⟨G, hEligible, hbad⟩ := hex
    exact ⟨EdgeCount G, G, hEligible, hbad, rfl⟩
  obtain ⟨G, hEligible, hbad, hcount⟩ := Nat.find_spec hp
  refine ⟨G, hEligible, hbad, ?_⟩
  intro H hHEligible hlt
  by_contra hHbad
  have hpH : p (EdgeCount H) := ⟨H, hHEligible, hHbad, rfl⟩
  have hmin : Nat.find hp ≤ EdgeCount H := Nat.find_min' hp hpH
  have hGH : EdgeCount G ≤ EdgeCount H := by simpa [hcount] using hmin
  exact (not_le_of_gt hlt) hGH

/-- A reusable strong-induction principle restricted to eligible graphs. -/
theorem good_of_smaller_good {Eligible Good : SimpleGraph V → Prop}
    (step : ∀ G : SimpleGraph V, Eligible G →
      (∀ H : SimpleGraph V, Eligible H → EdgeCount H < EdgeCount G → Good H) →
      Good G) :
    ∀ G : SimpleGraph V, Eligible G → Good G := by
  apply edgeCount_strong_induction
  intro G ih hEligible
  exact step G hEligible (fun H hH hlt => ih H hlt hH)

/-! ## Strict decrease under the paper's deletions -/

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Deleting an edge which is actually present strictly lowers the number of
edges. -/
theorem card_edgeFinset_deleteEdge_lt (e : G.edgeSet) :
    (G.deleteEdges ({e.1} : Set (Sym2 V))).edgeFinset.card <
      G.edgeFinset.card := by
  apply Finset.card_lt_card
  rw [edgeFinset_ssubset_edgeFinset]
  apply (G.deleteEdges_le ({e.1} : Set (Sym2 V))).lt_of_ne
  intro hEq
  have heDeleted : e.1 ∈ (G.deleteEdges ({e.1} : Set (Sym2 V))).edgeSet := by
    rw [hEq]
    exact e.2
  rw [edgeSet_deleteEdges] at heDeleted
  exact heDeleted.2 (by simp)

/-- `EdgeCount` version of `card_edgeFinset_deleteEdge_lt`. -/
theorem edgeCount_deleteEdge_lt (e : G.edgeSet) :
    EdgeCount (G.deleteEdges ({e.1} : Set (Sym2 V))) < EdgeCount G := by
  rw [edgeCount_eq_edgeFinset_card, edgeCount_eq_edgeFinset_card]
  exact card_edgeFinset_deleteEdge_lt e

/-- Deleting all edges incident with `x` strictly lowers the edge count as
soon as an incident edge really exists. -/
theorem card_edgeFinset_deleteIncidenceSet_lt {x : V}
    (hx : ∃ e : G.edgeSet, x ∈ (e : Sym2 V)) :
    (G.deleteIncidenceSet x).edgeFinset.card < G.edgeFinset.card := by
  rw [edgeFinset_deleteIncidenceSet_eq_sdiff]
  apply Finset.card_lt_card
  apply Finset.sdiff_ssubset (G.incidenceFinset_subset x)
  obtain ⟨e, hxe⟩ := hx
  refine ⟨e.1, ?_⟩
  rw [mem_incidenceFinset]
  exact ⟨e.2, hxe⟩

/-- `EdgeCount` version of
`card_edgeFinset_deleteIncidenceSet_lt`. -/
theorem edgeCount_deleteIncidenceSet_lt {x : V}
    (hx : ∃ e : G.edgeSet, x ∈ (e : Sym2 V)) :
    EdgeCount (G.deleteIncidenceSet x) < EdgeCount G := by
  rw [edgeCount_eq_edgeFinset_card, edgeCount_eq_edgeFinset_card]
  exact card_edgeFinset_deleteIncidenceSet_lt hx

theorem IsEdgeMinimalBad.good_deleteEdge
    {Eligible Good : SimpleGraph V → Prop}
    (hmin : IsEdgeMinimalBad Eligible Good G) (e : G.edgeSet)
    (hEligible : Eligible (G.deleteEdges ({e.1} : Set (Sym2 V)))) :
    Good (G.deleteEdges ({e.1} : Set (Sym2 V))) :=
  hmin.good_of_smaller hEligible (edgeCount_deleteEdge_lt e)

theorem IsEdgeMinimalBad.good_deleteIncidenceSet
    {Eligible Good : SimpleGraph V → Prop}
    (hmin : IsEdgeMinimalBad Eligible Good G) {x : V}
    (hx : ∃ e : G.edgeSet, x ∈ (e : Sym2 V))
    (hEligible : Eligible (G.deleteIncidenceSet x)) :
    Good (G.deleteIncidenceSet x) :=
  hmin.good_of_smaller hEligible (edgeCount_deleteIncidenceSet_lt hx)

end Finite

/-! ## Edge embeddings and endpoint compatibility -/

variable {H : SimpleGraph V}

/-- The explicit inclusion of edge subtypes induced by `H ≤ G`. -/
def edgeEmbeddingOfLE (h : H ≤ G) : H.edgeSet ↪ G.edgeSet where
  toFun e := ⟨e.1, edgeSet_mono h e.2⟩
  inj' e f hEq := by
    apply Subtype.ext
    exact congrArg (fun x : G.edgeSet => (x : Sym2 V)) hEq

@[simp] theorem edgeEmbeddingOfLE_val (h : H ≤ G) (e : H.edgeSet) :
    (edgeEmbeddingOfLE h e : Sym2 V) = e := rfl

/-- The set of edges of `G` retained in `H`. -/
def RetainedEdges (H G : SimpleGraph V) : Set G.edgeSet :=
  {e | e.1 ∈ H.edgeSet}

@[simp] theorem edgeEmbeddingOfLE_mem_retained (h : H ≤ G) (e : H.edgeSet) :
    edgeEmbeddingOfLE h e ∈ RetainedEdges H G :=
  e.2

theorem range_edgeEmbeddingOfLE (h : H ≤ G) :
    Set.range (edgeEmbeddingOfLE h) = RetainedEdges H G := by
  ext e
  constructor
  · rintro ⟨f, rfl⟩
    exact f.2
  · intro he
    exact ⟨⟨e.1, he⟩, Subtype.ext rfl⟩

theorem endpointDisjoint_edgeEmbedding_iff (h : H ≤ G)
    {e f : H.edgeSet} :
    EndpointDisjoint G (edgeEmbeddingOfLE h e) (edgeEmbeddingOfLE h f) ↔
      EndpointDisjoint H e f := by
  rfl

theorem hasCrossEdge_edgeEmbedding_mono (h : H ≤ G) {e f : H.edgeSet} :
    HasCrossEdge H e f →
      HasCrossEdge G (edgeEmbeddingOfLE h e) (edgeEmbeddingOfLE h f) := by
  rintro ⟨u, hue, v, hvf, huv⟩
  exact ⟨u, hue, v, hvf, h huv⟩

theorem inducedSeparated_edgeEmbedding_of_supergraph (h : H ≤ G)
    {e f : H.edgeSet}
    (hsep : InducedSeparated G (edgeEmbeddingOfLE h e) (edgeEmbeddingOfLE h f)) :
    InducedSeparated H e f := by
  refine ⟨hsep.1, ?_⟩
  exact fun hcross => hsep.2 (hasCrossEdge_edgeEmbedding_mono h hcross)

theorem pairCompatible_edgeEmbedding_of_supergraph (h : H ≤ G) {k : ℕ}
    {e f : H.edgeSet} {a b : OneTwoColor k}
    (hp : PairCompatible G (edgeEmbeddingOfLE h e)
      (edgeEmbeddingOfLE h f) a b) :
    PairCompatible H e f a b := by
  rcases hp with hne | hp
  · exact Or.inl hne
  · right
    cases a with
    | none => exact hp
    | some i => exact inducedSeparated_edgeEmbedding_of_supergraph h hp

/-- The precise structural hypothesis needed to move induced-matching
compatibility from `H` back to `G`: `H` retains every ambient adjacency
between endpoints of retained edges. -/
def ReflectsAdjacencyOnEdgeEndpoints (_h : H ≤ G) : Prop :=
  ∀ (e f : H.edgeSet) (u v : V),
    u ∈ (e : Sym2 V) → v ∈ (f : Sym2 V) → G.Adj u v → H.Adj u v

theorem hasCrossEdge_edgeEmbedding_iff (h : H ≤ G)
    (hreflect : ReflectsAdjacencyOnEdgeEndpoints h) {e f : H.edgeSet} :
    HasCrossEdge G (edgeEmbeddingOfLE h e) (edgeEmbeddingOfLE h f) ↔
      HasCrossEdge H e f := by
  constructor
  · rintro ⟨u, hue, v, hvf, huv⟩
    exact ⟨u, hue, v, hvf, hreflect e f u v hue hvf huv⟩
  · exact hasCrossEdge_edgeEmbedding_mono h

theorem inducedSeparated_edgeEmbedding_iff (h : H ≤ G)
    (hreflect : ReflectsAdjacencyOnEdgeEndpoints h) {e f : H.edgeSet} :
    InducedSeparated G (edgeEmbeddingOfLE h e) (edgeEmbeddingOfLE h f) ↔
      InducedSeparated H e f := by
  rw [InducedSeparated, InducedSeparated, endpointDisjoint_edgeEmbedding_iff,
    hasCrossEdge_edgeEmbedding_iff h hreflect]

theorem pairCompatible_edgeEmbedding_iff (h : H ≤ G)
    (hreflect : ReflectsAdjacencyOnEdgeEndpoints h) {k : ℕ}
    {e f : H.edgeSet} {a b : OneTwoColor k} :
    PairCompatible G (edgeEmbeddingOfLE h e) (edgeEmbeddingOfLE h f) a b ↔
      PairCompatible H e f a b := by
  by_cases hab : a = b
  · subst b
    cases a with
    | none => simp [PairCompatible, endpointDisjoint_edgeEmbedding_iff]
    | some i => simp [PairCompatible, inducedSeparated_edgeEmbedding_iff h hreflect]
  · simp [PairCompatible, hab]

/-! ## Restricting and transporting colourings -/

/-- Restrict an ambient colour assignment to the edge subtype of a
subgraph. -/
def restrictColoringToSubgraph {k : ℕ} (h : H ≤ G)
    (colour : G.edgeSet → OneTwoColor k) : H.edgeSet → OneTwoColor k :=
  fun e => colour (edgeEmbeddingOfLE h e)

theorem restrictColoringToSubgraph_valid {k : ℕ} (h : H ≤ G)
    {colour : G.edgeSet → OneTwoColor k}
    (hc : IsOneTwoColoring G colour) :
    IsOneTwoColoring H (restrictColoringToSubgraph h colour) := by
  intro e _ f _ hef
  apply pairCompatible_edgeEmbedding_of_supergraph h
  exact hc (edgeEmbeddingOfLE h e) (by simp)
    (edgeEmbeddingOfLE h f) (by simp) ((edgeEmbeddingOfLE h).injective.ne hef)

/-- Move a colouring of `H` to `G.edgeSet`; its irrelevant value outside
`RetainedEdges H G` is chosen to be the matching colour. -/
def transportColoringToSupergraph {k : ℕ} [DecidableRel H.Adj]
    (_h : H ≤ G) (colour : H.edgeSet → OneTwoColor k) :
    G.edgeSet → OneTwoColor k :=
  fun e => if he : e.1 ∈ H.edgeSet then colour ⟨e.1, he⟩ else none

@[simp] theorem transportColoringToSupergraph_of_mem {k : ℕ}
    [DecidableRel H.Adj] (h : H ≤ G)
    (colour : H.edgeSet → OneTwoColor k) {e : G.edgeSet}
    (he : e.1 ∈ H.edgeSet) :
    transportColoringToSupergraph h colour e = colour ⟨e.1, he⟩ := by
  simp [transportColoringToSupergraph, he]

@[simp] theorem transportColoringToSupergraph_apply {k : ℕ}
    [DecidableRel H.Adj] (h : H ≤ G)
    (colour : H.edgeSet → OneTwoColor k) (e : H.edgeSet) :
    transportColoringToSupergraph h colour (edgeEmbeddingOfLE h e) = colour e := by
  simp [transportColoringToSupergraph]

/-- Exact ambient-validity criterion for a transported colouring.  This
theorem exposes, rather than hides, all possible conflicts created by
restoring deleted edges. -/
theorem isOneTwoColoringOn_transport_iff {k : ℕ} [DecidableRel H.Adj]
    (h : H ≤ G) (colour : H.edgeSet → OneTwoColor k) :
    IsOneTwoColoringOn G (RetainedEdges H G)
        (transportColoringToSupergraph h colour) ↔
      ∀ e f : H.edgeSet, e ≠ f →
        PairCompatible G (edgeEmbeddingOfLE h e) (edgeEmbeddingOfLE h f)
          (colour e) (colour f) := by
  constructor
  · intro hc e f hef
    simpa using hc (edgeEmbeddingOfLE h e) e.2
      (edgeEmbeddingOfLE h f) f.2 ((edgeEmbeddingOfLE h).injective.ne hef)
  · intro hc e he f hf hef
    let eH : H.edgeSet := ⟨e.1, he⟩
    let fH : H.edgeSet := ⟨f.1, hf⟩
    have heEq : edgeEmbeddingOfLE h eH = e := Subtype.ext rfl
    have hfEq : edgeEmbeddingOfLE h fH = f := Subtype.ext rfl
    have hefH : eH ≠ fH := by
      intro hEq
      exact hef (heEq ▸ hfEq ▸ congrArg (edgeEmbeddingOfLE h) hEq)
    have hp := hc eH fH hefH
    rw [heEq, hfEq] at hp
    rw [transportColoringToSupergraph_of_mem h colour he,
      transportColoringToSupergraph_of_mem h colour hf]
    exact hp

theorem transportColoringToSupergraph_valid {k : ℕ} [DecidableRel H.Adj]
    (h : H ≤ G) (hreflect : ReflectsAdjacencyOnEdgeEndpoints h)
    {colour : H.edgeSet → OneTwoColor k}
    (hc : IsOneTwoColoring H colour) :
    IsOneTwoColoringOn G (RetainedEdges H G)
      (transportColoringToSupergraph h colour) := by
  apply (isOneTwoColoringOn_transport_iff h colour).mpr
  intro e f hef
  apply (pairCompatible_edgeEmbedding_iff h hreflect).mpr
  exact hc e (by simp) f (by simp) hef

/-! ## Incidence deletion has honest transport -/

section DeleteIncidenceTransport

variable [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem deleteIncidenceSet_reflectsAdjacency (x : V) :
    ReflectsAdjacencyOnEdgeEndpoints (G.deleteIncidenceSet_le x) := by
  intro e f u v hue hvf huv
  have he : e.1 ∈ G.edgeSet \ G.incidenceSet x := by
    simpa [edgeSet_deleteIncidenceSet] using e.2
  have hf : f.1 ∈ G.edgeSet \ G.incidenceSet x := by
    simpa [edgeSet_deleteIncidenceSet] using f.2
  have hux : u ≠ x := by
    intro hEq
    subst u
    exact he.2 ⟨he.1, hue⟩
  have hvx : v ≠ x := by
    intro hEq
    subst v
    exact hf.2 ⟨hf.1, hvf⟩
  exact deleteIncidenceSet_adj.mpr ⟨huv, hux, hvx⟩

/-- A colouring of `G.deleteIncidenceSet x` transports without introducing
conflicts among the retained edges of `G`. -/
theorem transport_deleteIncidenceSet_valid {k : ℕ} (x : V)
    {colour : (G.deleteIncidenceSet x).edgeSet → OneTwoColor k}
    (hc : IsOneTwoColoring (G.deleteIncidenceSet x) colour) :
    IsOneTwoColoringOn G (RetainedEdges (G.deleteIncidenceSet x) G)
      (transportColoringToSupergraph (G.deleteIncidenceSet_le x) colour) :=
  transportColoringToSupergraph_valid (G.deleteIncidenceSet_le x)
    (deleteIncidenceSet_reflectsAdjacency (G := G) x) hc

end DeleteIncidenceTransport

end

end LeanCo.PackingEdgeColoring
