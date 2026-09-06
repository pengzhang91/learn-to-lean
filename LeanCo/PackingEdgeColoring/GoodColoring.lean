import LeanCo.PackingEdgeColoring.LocalColoring
import LeanCo.PackingEdgeColoring.Threads

/-!
# The paper's good-colouring invariants

This file formalizes the auxiliary conditions from Sections 3 and 4 of
Kim--Liu--Xu.  The matching colour is `none`; the induced colours are
`some i`.

The paper phrases Section 4 Condition 1 as maximizing the number of
matching-coloured edges.  The recolouring arguments only use the resulting
inclusion-maximality.  We call that exact property `OneSaturated`; it does
**not** assert maximum cardinality.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-! ## Seeing colours -/

/-- A vertex sees the matching colour on `D` when a matching-coloured edge
of `D` is incident with it. -/
def VertexSeesMatchingOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (u : V) : Prop :=
  ∃ e, e ∈ D ∧ colour e = none ∧ u ∈ (e : Sym2 V)

/-- A vertex sees induced colour `i` on `D` when an endpoint of an
`i`-coloured edge is equal or adjacent to it.  This is exactly the paper's
"an endpoint is at distance at most one" definition. -/
def VertexSeesInducedOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (u : V) (i : Fin k) : Prop :=
  ∃ e, e ∈ D ∧ colour e = some i ∧
    ∃ v, v ∈ (e : Sym2 V) ∧ (u = v ∨ G.Adj u v)

/-- An edge sees the matching colour on `D` if a matching-coloured edge of
`D` is at line-graph distance at most one. -/
def EdgeSeesMatchingOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) : Prop :=
  ∃ f, f ∈ D ∧ colour f = none ∧ G.lineGraph.edist e f ≤ 1

/-- An edge sees induced colour `i` on `D` if an `i`-coloured edge of `D`
is at line-graph distance at most two. -/
def EdgeSeesInducedOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) (i : Fin k) : Prop :=
  ∃ f, f ∈ D ∧ colour f = some i ∧ G.lineGraph.edist e f ≤ 2

def VertexSeesMatching {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (u : V) : Prop :=
  VertexSeesMatchingOn G Set.univ colour u

def VertexSeesInduced {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (u : V) (i : Fin k) : Prop :=
  VertexSeesInducedOn G Set.univ colour u i

def EdgeSeesMatching {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) : Prop :=
  EdgeSeesMatchingOn G Set.univ colour e

def EdgeSeesInduced {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) (i : Fin k) : Prop :=
  EdgeSeesInducedOn G Set.univ colour e i

theorem vertexSeesMatching_iff {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (u : V) :
    VertexSeesMatching G colour u ↔
      ∃ e, colour e = none ∧ u ∈ (e : Sym2 V) := by
  simp [VertexSeesMatching, VertexSeesMatchingOn]

theorem vertexSeesInduced_iff {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (u : V) (i : Fin k) :
    VertexSeesInduced G colour u i ↔
      ∃ e, colour e = some i ∧
        ∃ v, v ∈ (e : Sym2 V) ∧ (u = v ∨ G.Adj u v) := by
  simp [VertexSeesInduced, VertexSeesInducedOn]

theorem edgeSeesMatching_iff {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) :
    EdgeSeesMatching G colour e ↔
      ∃ f, colour f = none ∧ G.lineGraph.edist e f ≤ 1 := by
  simp [EdgeSeesMatching, EdgeSeesMatchingOn]

theorem edgeSeesInduced_iff {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) (i : Fin k) :
    EdgeSeesInduced G colour e i ↔
      ∃ f, colour f = some i ∧ G.lineGraph.edist e f ≤ 2 := by
  simp [EdgeSeesInduced, EdgeSeesInducedOn]

/-- Endpoint-local expansion of “an edge sees the matching colour”. -/
theorem edgeSeesMatchingOn_iff_local {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) :
    EdgeSeesMatchingOn G D colour e ↔
      ∃ f, f ∈ D ∧ colour f = none ∧
        (e = f ∨ ¬ EndpointDisjoint G e f) := by
  constructor
  · rintro ⟨f, hfD, hf, hdist⟩
    refine ⟨f, hfD, hf, ?_⟩
    by_cases hef : e = f
    · exact Or.inl hef
    · right
      intro hdisj
      have htwo := (endpointDisjoint_iff_two_le_edist G hef).mp hdisj
      have : (2 : ℕ∞) ≤ 1 := htwo.trans hdist
      norm_num at this
  · rintro ⟨f, hfD, hf, heq | hclose⟩
    · subst f
      exact ⟨e, hfD, hf, by simp⟩
    · refine ⟨f, hfD, hf, ?_⟩
      by_cases hef : e = f
      · subst f
        simp
      · have hadj : G.lineGraph.Adj e f := by
          by_contra hnadj
          exact hclose ((endpointDisjoint_iff_not_lineGraph_adj G hef).mpr hnadj)
        simp [(edist_eq_one_iff_adj.mpr hadj)]

/-- Endpoint-local expansion of “an edge sees induced colour `i`”. -/
theorem edgeSeesInducedOn_iff_local {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) (i : Fin k) :
    EdgeSeesInducedOn G D colour e i ↔
      ∃ f, f ∈ D ∧ colour f = some i ∧
        (e = f ∨ ¬ InducedSeparated G e f) := by
  constructor
  · rintro ⟨f, hfD, hf, hdist⟩
    refine ⟨f, hfD, hf, ?_⟩
    by_cases hef : e = f
    · exact Or.inl hef
    · right
      intro hsep
      have hthree := (inducedSeparated_iff_three_le_edist G hef).mp hsep
      have : (3 : ℕ∞) ≤ 2 := hthree.trans hdist
      norm_num at this
  · rintro ⟨f, hfD, hf, heq | hclose⟩
    · subst f
      exact ⟨e, hfD, hf, by simp⟩
    · refine ⟨f, hfD, hf, ?_⟩
      by_cases hef : e = f
      · subst f
        simp
      · have hnthree : ¬ (3 : ℕ∞) ≤ G.lineGraph.edist e f :=
          fun hthree => hclose ((inducedSeparated_iff_three_le_edist G hef).mpr hthree)
        have hlt : G.lineGraph.edist e f < (3 : ℕ∞) := lt_of_not_ge hnthree
        change G.lineGraph.edist e f < (2 : ℕ∞) + 1 at hlt
        exact (ENat.lt_add_one_iff (by norm_num : (2 : ℕ∞) ≠ ⊤)).mp hlt

theorem IsOneTwoColoring.matching_edge_unique_at_vertex {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k} (h : IsOneTwoColoring G colour)
    {e f : G.edgeSet} (he : colour e = none) (hf : colour f = none)
    {u : V} (hue : u ∈ (e : Sym2 V)) (huf : u ∈ (f : Sym2 V)) :
    e = f := by
  by_contra hef
  have hp := h e (by simp) f (by simp) hef
  have hdisj : EndpointDisjoint G e f := by simpa [he, hf] using hp
  exact hdisj u hue huf

/-- Distinct incident edges in a valid colouring cannot carry the same
induced colour.  In particular, the two external colours at a degree-three
thread endpoint really form a two-element colour pair. -/
theorem IsOneTwoColoring.induced_colors_ne_of_incident {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k} (h : IsOneTwoColoring G colour)
    {e f : G.edgeSet} (hef : e ≠ f) {i j : Fin k}
    (he : colour e = some i) (hf : colour f = some j)
    {u : V} (hue : u ∈ (e : Sym2 V)) (huf : u ∈ (f : Sym2 V)) :
    i ≠ j := by
  intro hij
  subst j
  have hp := h e (by simp) f (by simp) hef
  have hsep : InducedSeparated G e f := by simpa [he, hf] using hp
  exact hsep.1 u hue huf

/-! ## Conditions I, 1, and 2 -/

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The common palette condition from Section 3 Condition I and Section 4
Condition 2. -/
def TwoVertexPaletteCondition {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) : Prop :=
  ∀ u, IsTwoVertex G u → VertexSeesMatching G colour u →
    ¬ ∀ i : Fin k, VertexSeesInduced G colour u i

/-- Section 3 Condition I. -/
def ConditionI (colour : G.edgeSet → OneTwoColor 5) : Prop :=
  TwoVertexPaletteCondition G colour

/-- Section 4 Condition 2. -/
def ConditionTwo (colour : G.edgeSet → OneTwoColor 4) : Prop :=
  TwoVertexPaletteCondition G colour

/-- Section 3's good `(1,2^5)` colouring. -/
def GoodFive (colour : G.edgeSet → OneTwoColor 5) : Prop :=
  IsOneTwoColoring G colour ∧ ConditionI G colour

/-- Inclusion-maximality of the matching-colour class.  Every edge outside
that class is blocked from joining it by an incident matching-coloured edge.
This is deliberately weaker than, and should not be confused with,
maximum-cardinality of the matching class. -/
def OneSaturated {k : ℕ} (colour : G.edgeSet → OneTwoColor k) : Prop :=
  ∀ e, colour e ≠ none →
    ∃ f, colour f = none ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)

theorem OneSaturated.exists_incident_matching {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k} (h : OneSaturated G colour)
    {e : G.edgeSet} (he : colour e ≠ none) :
    ∃ f, colour f = none ∧ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V) :=
  h e he

/-- Operational characterization of inclusion-maximality: no nonmatching
edge can simply be recoloured with the matching colour. -/
theorem oneSaturated_iff_no_matching_available {k : ℕ}
    (colour : G.edgeSet → OneTwoColor k) :
    OneSaturated G colour ↔
      ∀ e, colour e ≠ none →
        ¬ ColorAvailableOn G Set.univ colour e none := by
  constructor
  · intro h e he havail
    obtain ⟨f, hf, v, hve, hvf⟩ := h e he
    have hfe : f ≠ e := by
      intro hEq
      apply he
      simpa [hEq] using hf
    have hdisj := (colorAvailableOn_none_iff G Set.univ colour e).mp
      havail f (by simp) hfe hf
    exact hdisj v hve hvf
  · intro h e he
    by_contra! hnone
    apply h e he
    apply (colorAvailableOn_none_iff G Set.univ colour e).mpr
    intro f _ hfe hf v hve hvf
    exact hnone f hf v hve hvf

/-! ## Condition 3 -/

/-- The first edge of a certified thread. -/
def threadFirstEdge {u₁ u₂ : V} (p : G.Walk u₁ u₂) {k : ℕ}
    (hp : IsKThread G p k) : G.edgeSet :=
  ⟨s(u₁, p.getVert 1), hp.first_step_adj⟩

/-- The last edge of a certified thread. -/
def threadLastEdge {u₁ u₂ : V} (p : G.Walk u₁ u₂) {k : ℕ}
    (hp : IsKThread G p k) : G.edgeSet :=
  ⟨s(p.getVert k, u₂), hp.last_step_adj⟩

/-- An edge incident with `u`, other than the specified thread edge. -/
def IsExternalAt (u : V) (threadEdge e : G.edgeSet) : Prop :=
  u ∈ (e : Sym2 V) ∧ e ≠ threadEdge

/-- All edges external to an endpoint of a thread use induced colours. -/
def ExternalEdgesInduced {k : ℕ} (colour : G.edgeSet → OneTwoColor k)
    (u : V) (threadEdge : G.edgeSet) : Prop :=
  ∀ e, IsExternalAt G u threadEdge e → ∃ i, colour e = some i

/-- The unordered set of induced colours on the external edges at a thread
endpoint.  At a degree-three endpoint it is the paper's external colour
pair. -/
def ExternalInducedColors {k : ℕ} (colour : G.edgeSet → OneTwoColor k)
    (u : V) (threadEdge : G.edgeSet) : Set (Fin k) :=
  {i | ∃ e, IsExternalAt G u threadEdge e ∧ colour e = some i}

/-- Section 4 Condition 3.  `IsKThread G p 2` includes the degree-three
endpoint hypotheses, hence each quantified external edge collection is
exactly the two edges appearing in the paper. -/
def ConditionThree (colour : G.edgeSet → OneTwoColor 4) : Prop :=
  ∀ (u₁ u₂ : V) (p : G.Walk u₁ u₂) (hp : IsKThread G p 2),
    ExternalEdgesInduced G colour u₁ (threadFirstEdge G p hp) →
    ExternalEdgesInduced G colour u₂ (threadLastEdge G p hp) →
    ExternalInducedColors G colour u₁ (threadFirstEdge G p hp) ≠
      ExternalInducedColors G colour u₂ (threadLastEdge G p hp)

/-- Section 4's good `(1,2^4)` colouring, with Condition 1 represented by
the inclusion-maximal property actually used by the recolouring proofs. -/
def GoodFour (colour : G.edgeSet → OneTwoColor 4) : Prop :=
  IsOneTwoColoring G colour ∧
    OneSaturated G colour ∧
    ConditionTwo G colour ∧
    ConditionThree G colour

theorem GoodFive.valid {colour : G.edgeSet → OneTwoColor 5}
    (h : GoodFive G colour) : IsOneTwoColoring G colour := h.1

theorem GoodFive.paletteCondition {colour : G.edgeSet → OneTwoColor 5}
    (h : GoodFive G colour) : ConditionI G colour := h.2

theorem GoodFour.valid {colour : G.edgeSet → OneTwoColor 4}
    (h : GoodFour G colour) : IsOneTwoColoring G colour := h.1

theorem GoodFour.oneSaturated {colour : G.edgeSet → OneTwoColor 4}
    (h : GoodFour G colour) : OneSaturated G colour := h.2.1

theorem GoodFour.paletteCondition {colour : G.edgeSet → OneTwoColor 4}
    (h : GoodFour G colour) : ConditionTwo G colour := h.2.2.1

theorem GoodFour.conditionThree {colour : G.edgeSet → OneTwoColor 4}
    (h : GoodFour G colour) : ConditionThree G colour := h.2.2.2

theorem TwoVertexPaletteCondition.exists_missing {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k}
    (h : TwoVertexPaletteCondition G colour) {u : V}
    (hu : IsTwoVertex G u) (hmatch : VertexSeesMatching G colour u) :
    ∃ i : Fin k, ¬ VertexSeesInduced G colour u i := by
  by_contra! hall
  exact h u hu hmatch hall

/-! ## Permuting induced colours -/

/-- Relabel induced colours while fixing the matching colour. -/
def permuteInducedColor {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    OneTwoColor k ≃ OneTwoColor k :=
  Equiv.optionCongr σ

def permuteInducedColors {k : ℕ} (σ : Equiv.Perm (Fin k))
    (colour : G.edgeSet → OneTwoColor k) : G.edgeSet → OneTwoColor k :=
  fun e => permuteInducedColor σ (colour e)

@[simp] theorem permuteInducedColor_none {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    permuteInducedColor σ none = none := by
  rfl

@[simp] theorem permuteInducedColor_some {k : ℕ} (σ : Equiv.Perm (Fin k))
    (i : Fin k) : permuteInducedColor σ (some i) = some (σ i) := by
  rfl

@[simp] theorem permuteInducedColors_apply {k : ℕ} (σ : Equiv.Perm (Fin k))
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) :
    permuteInducedColors G σ colour e = permuteInducedColor σ (colour e) :=
  rfl

theorem pairCompatible_permute_iff {k : ℕ} (σ : Equiv.Perm (Fin k))
    {e f : G.edgeSet} {a b : OneTwoColor k} :
    PairCompatible G e f (permuteInducedColor σ a) (permuteInducedColor σ b) ↔
      PairCompatible G e f a b := by
  cases a <;> cases b <;> simp [PairCompatible]

theorem isOneTwoColoringOn_permute_iff {k : ℕ} (σ : Equiv.Perm (Fin k))
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k) :
    IsOneTwoColoringOn G D (permuteInducedColors G σ colour) ↔
      IsOneTwoColoringOn G D colour := by
  constructor <;> intro h e he f hf hef
  · exact (pairCompatible_permute_iff G σ).mp (h e he f hf hef)
  · exact (pairCompatible_permute_iff G σ).mpr (h e he f hf hef)

theorem isOneTwoColoring_permute_iff {k : ℕ} (σ : Equiv.Perm (Fin k))
    (colour : G.edgeSet → OneTwoColor k) :
    IsOneTwoColoring G (permuteInducedColors G σ colour) ↔
      IsOneTwoColoring G colour :=
  isOneTwoColoringOn_permute_iff G σ Set.univ colour

theorem vertexSeesMatching_permute_iff {k : ℕ} (σ : Equiv.Perm (Fin k))
    (colour : G.edgeSet → OneTwoColor k) (u : V) :
    VertexSeesMatching G (permuteInducedColors G σ colour) u ↔
      VertexSeesMatching G colour u := by
  simp [VertexSeesMatching, VertexSeesMatchingOn, permuteInducedColors,
    permuteInducedColor]

theorem vertexSeesInduced_permute_iff {k : ℕ} (σ : Equiv.Perm (Fin k))
    (colour : G.edgeSet → OneTwoColor k) (u : V) (i : Fin k) :
    VertexSeesInduced G (permuteInducedColors G σ colour) u (σ i) ↔
      VertexSeesInduced G colour u i := by
  simp [VertexSeesInduced, VertexSeesInducedOn, permuteInducedColors,
    permuteInducedColor]

theorem edgeSeesMatching_permute_iff {k : ℕ} (σ : Equiv.Perm (Fin k))
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) :
    EdgeSeesMatching G (permuteInducedColors G σ colour) e ↔
      EdgeSeesMatching G colour e := by
  simp [EdgeSeesMatching, EdgeSeesMatchingOn, permuteInducedColors,
    permuteInducedColor]

theorem edgeSeesInduced_permute_iff {k : ℕ} (σ : Equiv.Perm (Fin k))
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) (i : Fin k) :
    EdgeSeesInduced G (permuteInducedColors G σ colour) e (σ i) ↔
      EdgeSeesInduced G colour e i := by
  simp [EdgeSeesInduced, EdgeSeesInducedOn, permuteInducedColors,
    permuteInducedColor]

theorem oneSaturated_permute_iff {k : ℕ} (σ : Equiv.Perm (Fin k))
    (colour : G.edgeSet → OneTwoColor k) :
    OneSaturated G (permuteInducedColors G σ colour) ↔
      OneSaturated G colour := by
  have hnone (a : OneTwoColor k) :
      permuteInducedColor σ a = none ↔ a = none := by
    constructor
    · intro h
      apply (permuteInducedColor σ).injective
      simpa using h
    · rintro rfl
      rfl
  constructor
  · intro h e he
    have he' : permuteInducedColors G σ colour e ≠ none :=
      fun hc => he ((hnone (colour e)).mp hc)
    obtain ⟨f, hf, v, hve, hvf⟩ := h e he'
    exact ⟨f, (hnone (colour f)).mp hf, v, hve, hvf⟩
  · intro h e he
    have he' : colour e ≠ none :=
      fun hc => he ((hnone (colour e)).mpr hc)
    obtain ⟨f, hf, v, hve, hvf⟩ := h e he'
    exact ⟨f, (hnone (colour f)).mpr hf, v, hve, hvf⟩

theorem twoVertexPaletteCondition_permute_iff {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (colour : G.edgeSet → OneTwoColor k) :
    TwoVertexPaletteCondition G (permuteInducedColors G σ colour) ↔
      TwoVertexPaletteCondition G colour := by
  constructor
  · intro h u hu hmatch hall
    apply h u hu
    · exact (vertexSeesMatching_permute_iff G σ colour u).mpr hmatch
    · intro j
      have hj := hall (σ.symm j)
      have := (vertexSeesInduced_permute_iff G σ colour u (σ.symm j)).mpr hj
      simpa using this
  · intro h u hu hmatch hall
    apply h u hu
    · exact (vertexSeesMatching_permute_iff G σ colour u).mp hmatch
    · intro i
      exact (vertexSeesInduced_permute_iff G σ colour u i).mp (hall (σ i))

theorem conditionI_permute_iff (σ : Equiv.Perm (Fin 5))
    (colour : G.edgeSet → OneTwoColor 5) :
    ConditionI G (permuteInducedColors G σ colour) ↔ ConditionI G colour :=
  twoVertexPaletteCondition_permute_iff G σ colour

theorem conditionTwo_permute_iff (σ : Equiv.Perm (Fin 4))
    (colour : G.edgeSet → OneTwoColor 4) :
    ConditionTwo G (permuteInducedColors G σ colour) ↔ ConditionTwo G colour :=
  twoVertexPaletteCondition_permute_iff G σ colour

theorem externalEdgesInduced_permute_iff {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (colour : G.edgeSet → OneTwoColor k)
    (u : V) (threadEdge : G.edgeSet) :
    ExternalEdgesInduced G (permuteInducedColors G σ colour) u threadEdge ↔
      ExternalEdgesInduced G colour u threadEdge := by
  constructor
  · intro h e he
    obtain ⟨j, hj⟩ := h e he
    refine ⟨σ.symm j, ?_⟩
    apply (permuteInducedColor σ).injective
    simpa [permuteInducedColors] using hj
  · intro h e he
    obtain ⟨i, hi⟩ := h e he
    exact ⟨σ i, by simp [permuteInducedColors, hi]⟩

theorem externalInducedColors_permute_mem_iff {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (colour : G.edgeSet → OneTwoColor k)
    (u : V) (threadEdge : G.edgeSet) (i : Fin k) :
    σ i ∈ ExternalInducedColors G (permuteInducedColors G σ colour) u threadEdge ↔
      i ∈ ExternalInducedColors G colour u threadEdge := by
  constructor
  · rintro ⟨e, he, hc⟩
    refine ⟨e, he, ?_⟩
    apply (permuteInducedColor σ).injective
    simpa [permuteInducedColors] using hc
  · rintro ⟨e, he, hc⟩
    exact ⟨e, he, by simp [permuteInducedColors, hc]⟩

theorem conditionThree_permute_iff (σ : Equiv.Perm (Fin 4))
    (colour : G.edgeSet → OneTwoColor 4) :
    ConditionThree G (permuteInducedColors G σ colour) ↔
      ConditionThree G colour := by
  constructor
  · intro h u₁ u₂ p hp hleft hright
    have hleft' := (externalEdgesInduced_permute_iff G σ colour u₁
      (threadFirstEdge G p hp)).mpr hleft
    have hright' := (externalEdgesInduced_permute_iff G σ colour u₂
      (threadLastEdge G p hp)).mpr hright
    have hne := h u₁ u₂ p hp hleft' hright'
    intro heq
    apply hne
    ext j
    have hL := externalInducedColors_permute_mem_iff G σ colour u₁
      (threadFirstEdge G p hp) (σ.symm j)
    have hR := externalInducedColors_permute_mem_iff G σ colour u₂
      (threadLastEdge G p hp) (σ.symm j)
    have hmid := Set.ext_iff.mp heq (σ.symm j)
    simpa using hL.trans (hmid.trans hR.symm)
  · intro h u₁ u₂ p hp hleft hright
    have hleft' := (externalEdgesInduced_permute_iff G σ colour u₁
      (threadFirstEdge G p hp)).mp hleft
    have hright' := (externalEdgesInduced_permute_iff G σ colour u₂
      (threadLastEdge G p hp)).mp hright
    have hne := h u₁ u₂ p hp hleft' hright'
    intro heq
    apply hne
    ext i
    have hL := externalInducedColors_permute_mem_iff G σ colour u₁
      (threadFirstEdge G p hp) i
    have hR := externalInducedColors_permute_mem_iff G σ colour u₂
      (threadLastEdge G p hp) i
    exact hL.symm.trans ((Set.ext_iff.mp heq (σ i)).trans hR)

theorem goodFive_permute_iff (σ : Equiv.Perm (Fin 5))
    (colour : G.edgeSet → OneTwoColor 5) :
    GoodFive G (permuteInducedColors G σ colour) ↔ GoodFive G colour := by
  rw [GoodFive, GoodFive, isOneTwoColoring_permute_iff,
    conditionI_permute_iff]

theorem goodFour_permute_iff (σ : Equiv.Perm (Fin 4))
    (colour : G.edgeSet → OneTwoColor 4) :
    GoodFour G (permuteInducedColors G σ colour) ↔ GoodFour G colour := by
  rw [GoodFour, GoodFour, isOneTwoColoring_permute_iff,
    oneSaturated_permute_iff, conditionTwo_permute_iff,
    conditionThree_permute_iff]

end Finite

end


end LeanCo.PackingEdgeColoring
