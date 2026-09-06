import LeanCo.PackingEdgeColoring.Threads
import LeanCo.PackingEdgeColoring.MaximumAverageDegree
import LeanCo.PackingEdgeColoring.GirthTools

/-!
# Reaching degree-three endpoints through degree-two vertices

This file supplies finite relations for the `12 / 5` double-counting
argument.  A path is *two-internal* when it is nonempty, simple, and every
strictly internal vertex has ambient degree two.  Two interfaces are kept
separate: `TwoThreeReach` deduplicates endpoint vertices, while
`TwoDirectionIncidence` counts the two incident directions at each
degree-two vertex with multiplicity.  The latter is the Section 3 interface
and remains valid when both directions terminate at the same degree-three
vertex.

The no-`3`-chain argument below constructs a terminal for every direction.
The upper bound of three assigned directions per degree-three vertex remains
the graph-theoretic obligation supplied by the paper's reducible
configurations.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

universe u

variable {V : Type u} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-! ## Paths with degree-two interior -/

/-- A nonempty simple path all of whose strict internal vertices have
ambient degree two. -/
def IsTwoInternalPath {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ 0 < p.length ∧
    ∀ i : ℕ, 0 < i → i < p.length → IsTwoVertex G (p.getVert i)

theorem IsTwoInternalPath.isPath {u v : V} {p : G.Walk u v}
    (hp : IsTwoInternalPath G p) : p.IsPath :=
  hp.1

theorem IsTwoInternalPath.pos {u v : V} {p : G.Walk u v}
    (hp : IsTwoInternalPath G p) : 0 < p.length :=
  hp.2.1

theorem IsTwoInternalPath.internal_two {u v : V} {p : G.Walk u v}
    (hp : IsTwoInternalPath G p) {i : ℕ} (hi0 : 0 < i)
    (hil : i < p.length) : IsTwoVertex G (p.getVert i) :=
  hp.2.2 i hi0 hil

/-- Reversing a two-internal path preserves all of its defining data. -/
theorem IsTwoInternalPath.reverse {u v : V} {p : G.Walk u v}
    (hp : IsTwoInternalPath G p) : IsTwoInternalPath G p.reverse := by
  refine ⟨hp.isPath.reverse, by simpa using hp.pos, ?_⟩
  intro i hi0 hil
  rw [Walk.getVert_reverse]
  apply hp.internal_two
  · rw [Walk.length_reverse] at hil
    omega
  · rw [Walk.length_reverse] at hil
    omega

/-- Two vertices are joined through degree-two vertices when a two-internal
path joins them. -/
def ReachesThroughTwo (u v : V) : Prop :=
  ∃ p : G.Walk u v, IsTwoInternalPath G p

/-- Reach through degree-two vertices is symmetric. -/
theorem reachesThroughTwo_comm {u v : V} :
    ReachesThroughTwo G u v ↔ ReachesThroughTwo G v u := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.reverse, hp.reverse⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.reverse, hp.reverse⟩

theorem ReachesThroughTwo.symm {u v : V} (h : ReachesThroughTwo G u v) :
    ReachesThroughTwo G v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, hp.reverse⟩

/-- A two-internal path has distinct endpoints. -/
theorem IsTwoInternalPath.endpoints_ne {u v : V} {p : G.Walk u v}
    (hp : IsTwoInternalPath G p) : u ≠ v := by
  intro huv
  subst v
  have hnil : p.Nil := Walk.isPath_iff_nil.mp hp.isPath
  have hzero := hnil.length_eq_zero
  exact (Nat.ne_of_gt hp.pos) hzero

theorem ReachesThroughTwo.ne {u v : V} (h : ReachesThroughTwo G u v) :
    u ≠ v := by
  obtain ⟨p, hp⟩ := h
  exact hp.endpoints_ne

/-- A single edge is a path through degree-two vertices; its interior is
empty. -/
theorem ReachesThroughTwo.of_adj {u v : V} (h : G.Adj u v) :
    ReachesThroughTwo G u v := by
  refine ⟨h.toWalk, Walk.IsPath.of_adj h, by simp, ?_⟩
  intro i hi0 hil
  simp at hil
  omega

/-- Two adjacent steps through a degree-two middle vertex give a reach
witness, provided the endpoints are distinct. -/
theorem ReachesThroughTwo.of_adj_adj {u x v : V}
    (hux : G.Adj u x) (hxv : G.Adj x v) (huv : u ≠ v)
    (hx : IsTwoVertex G x) : ReachesThroughTwo G u v := by
  let p : G.Walk u v := .cons hux (.cons hxv .nil)
  have htail : (hxv.toWalk).IsPath := Walk.IsPath.of_adj hxv
  have hpath : p.IsPath := by
    apply htail.cons
    simp [hux.ne, huv]
  refine ⟨p, hpath, by simp [p], ?_⟩
  intro i hi0 hil
  have hlen : p.length = 2 := rfl
  rw [hlen] at hil
  have hi : i = 1 := by
    omega
  subst i
  simpa [p] using hx

/-! ## Elementary degree-two continuation -/

/-- A degree-two vertex has a neighbor other than any specified neighbor. -/
theorem exists_other_neighbor_of_isTwoVertex {x a : V}
    (ha : IsTwoVertex G a) (hax : G.Adj a x) :
    ∃ y : V, y ≠ x ∧ G.Adj a y := by
  have hcard : (G.neighborFinset a).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact ha
  obtain ⟨r, s, hrs, hneighbors⟩ := Finset.card_eq_two.mp hcard
  have hxmem : x ∈ G.neighborFinset a :=
    (G.mem_neighborFinset a x).mpr hax
  rw [hneighbors] at hxmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
  rcases hxmem with hxr | hxs
  · subst r
    refine ⟨s, hrs.symm, ?_⟩
    apply (G.mem_neighborFinset a s).mp
    rw [hneighbors]
    simp
  · subst s
    refine ⟨r, hrs, ?_⟩
    apply (G.mem_neighborFinset a r).mp
    rw [hneighbors]
    simp

/-- Three distinct consecutive degree-two vertices form a `3`-chain in the
sense of `Threads.lean`. -/
theorem isKChain_three_of_adj {a x b : V}
    (hax : G.Adj a x) (hxb : G.Adj x b) (hab : a ≠ b)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) :
    IsKChain G (.cons hax (.cons hxb .nil)) 3 := by
  let p : G.Walk a b := .cons hax (.cons hxb .nil)
  have htail : (hxb.toWalk).IsPath := Walk.IsPath.of_adj hxb
  have hpath : p.IsPath := by
    apply htail.cons
    simp [hax.ne, hab]
  refine ⟨hpath, rfl, ?_⟩
  intro z hz
  change z ∈ [a, x, b] at hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact ha
  · exact hx
  · exact hb

/-- Starting from a degree-two vertex along a specified incident edge, a
degree-three endpoint is reached within two steps if every vertex has degree
two or three and `3`-chains are forbidden. -/
theorem exists_three_endpoint_via_neighbor
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    {x a : V} (hx : IsTwoVertex G x) (hxa : G.Adj x a) :
    ∃ y : V, IsThreeVertex G y ∧ ReachesThroughTwo G x y ∧
      (y = a ∨ (IsTwoVertex G a ∧ G.Adj a y)) := by
  rcases hdeg a hxa.degree_pos_right with ha | ha
  · obtain ⟨y, hyx, hay⟩ :=
      exists_other_neighbor_of_isTwoVertex G ha hxa.symm
    have hy : IsThreeVertex G y := by
      rcases hdeg y hay.degree_pos_right with hy | hy
      · exact False.elim <| hno3 (.cons hay.symm (.cons hxa.symm .nil))
          (isKChain_three_of_adj G hay.symm hxa.symm hyx hy ha hx)
      · exact hy
    refine ⟨y, hy, ?_, Or.inr ⟨ha, hay⟩⟩
    exact ReachesThroughTwo.of_adj_adj G hxa hay hyx.symm ha
  · exact ⟨a, ha, ReachesThroughTwo.of_adj G hxa, Or.inl rfl⟩

/-- Under the no-`3`-chain hypothesis, the two neighbors of a degree-two
vertex cannot both have degree two. -/
theorem not_both_two_neighbors_of_no_three_chain
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    {x a b : V} (hx : IsTwoVertex G x) (hxa : G.Adj x a)
    (hxb : G.Adj x b) (hab : a ≠ b) :
    ¬ (IsTwoVertex G a ∧ IsTwoVertex G b) := by
  rintro ⟨ha, hb⟩
  exact hno3 (.cons hxa.symm (.cons hxb .nil))
    (isKChain_three_of_adj G hxa.symm hxb hab ha hx hb)

/-! ## Threads supply two endpoint incidences -/

/-- The endpoints of a certified thread are distinct. -/
theorem IsKThread.endpoints_ne {u v : V} {p : G.Walk u v} {k : ℕ}
    (hp : IsKThread G p k) : u ≠ v := by
  intro huv
  subst v
  have hnil : p.Nil := Walk.isPath_iff_nil.mp hp.1
  have hzero := hnil.length_eq_zero
  rw [hp.length] at hzero
  omega

/-- From an internal vertex of a thread, the suffix reaches the terminal
degree-three endpoint through degree-two vertices. -/
theorem IsKThread.internal_reaches_end {u v : V} {p : G.Walk u v} {k i : ℕ}
    (hp : IsKThread G p k) (hi0 : 0 < i) (hil : i < p.length) :
    ReachesThroughTwo G (p.getVert i) v := by
  refine ⟨p.drop i, hp.1.drop i, ?_, ?_⟩
  · simp only [Walk.drop_length]
    omega
  · intro j hj0 hjl
    simp only [Walk.drop_length] at hjl
    rw [Walk.drop_getVert]
    apply hp.internal_two
    · omega
    · omega

/-- From an internal vertex of a thread, reversing the prefix reaches the
initial degree-three endpoint through degree-two vertices. -/
theorem IsKThread.internal_reaches_start {u v : V} {p : G.Walk u v} {k i : ℕ}
    (hp : IsKThread G p k) (hi0 : 0 < i) (hil : i < p.length) :
    ReachesThroughTwo G (p.getVert i) u := by
  have htake : IsTwoInternalPath G (p.take i) := by
    refine ⟨hp.1.take i, ?_, ?_⟩
    · simp only [Walk.take_length]
      omega
    · intro j hj0 hjl
      simp only [Walk.take_length] at hjl
      rw [Walk.take_getVert, Nat.min_eq_right (by omega)]
      apply IsKThread.internal_two (G := G) hp hj0
      omega
  exact ⟨(p.take i).reverse, htake.reverse⟩

/-! ## The finite degree-two/degree-three relation -/

/-- Degree-two vertices as a finite subtype. -/
abbrev DegreeTwoVertex := {v : V // IsTwoVertex G v}

/-- Degree-three vertices as a finite subtype. -/
abbrev DegreeThreeVertex := {v : V // IsThreeVertex G v}

noncomputable local instance : Fintype (DegreeTwoVertex G) :=
  Fintype.ofFinite _

noncomputable local instance : Fintype (DegreeThreeVertex G) :=
  Fintype.ofFinite _

/-! ### Incidences counted with direction multiplicity -/

/-- One of the two incident directions at a degree-two vertex.  Directions
are neighboring vertices, so two different incident edges remain distinct
even when their continuations eventually reach the same degree-three
vertex. -/
abbrev DegreeTwoDirection (x : DegreeTwoVertex G) :=
  {v : V // G.Adj x.1 v}

/-- All directed incidences based at degree-two vertices. -/
abbrev TwoDirectionIncidence :=
  Σ x : DegreeTwoVertex G, DegreeTwoDirection G x

/-- A direction reaches a terminal degree-three vertex when it has a
two-internal witnessing path whose first vertex after the source is the
chosen neighboring direction. -/
def TwoDirectionReaches (d : TwoDirectionIncidence G)
    (y : DegreeThreeVertex G) : Prop :=
  ∃ p : G.Walk d.1.1 y.1,
    IsTwoInternalPath G p ∧ p.getVert 1 = d.2.1

/-- Every degree-two vertex has exactly two incident directions. -/
theorem card_degreeTwoDirection (x : DegreeTwoVertex G) :
    Fintype.card (DegreeTwoDirection G x) = 2 := by
  rw [Fintype.card_subtype]
  have heq :
      (Finset.univ.filter fun v : V ↦ G.Adj x.1 v) =
        G.neighborFinset x.1 := by
    ext v
    simp
  rw [heq, SimpleGraph.card_neighborFinset_eq_degree]
  exact x.2

/-- Hence the total number of directed degree-two incidences is twice the
number of degree-two vertices. -/
theorem card_twoDirectionIncidence :
    Fintype.card (TwoDirectionIncidence G) =
      2 * Fintype.card (DegreeTwoVertex G) := by
  rw [Fintype.card_sigma]
  simp_rw [card_degreeTwoDirection]
  simp [Nat.mul_comm]

/-- With degrees in `{2,3}` and no `3`-chain, every incident direction has
a degree-three terminal within at most two steps.  No triangle hypothesis is
used: the two directions may legitimately choose the same terminal. -/
theorem exists_degreeThree_terminal_for_direction
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    (d : TwoDirectionIncidence G) :
    ∃ y : DegreeThreeVertex G, TwoDirectionReaches G d y := by
  let x : V := d.1.1
  let a : V := d.2.1
  have hx : IsTwoVertex G x := d.1.2
  have hxa : G.Adj x a := d.2.2
  rcases hdeg a hxa.degree_pos_right with ha | ha
  · obtain ⟨y, hyx, hay⟩ :=
      exists_other_neighbor_of_isTwoVertex G ha hxa.symm
    have hy : IsThreeVertex G y := by
      rcases hdeg y hay.degree_pos_right with hy | hy
      · exact False.elim <| hno3 (.cons hay.symm (.cons hxa.symm .nil))
          (isKChain_three_of_adj G hay.symm hxa.symm hyx hy ha hx)
      · exact hy
    let p : G.Walk x y := .cons hxa (.cons hay .nil)
    have htail : (hay.toWalk).IsPath := Walk.IsPath.of_adj hay
    have hpath : p.IsPath := by
      apply htail.cons
      simp [hxa.ne, hyx.symm]
    have hp : IsTwoInternalPath G p := by
      refine ⟨hpath, by simp [p], ?_⟩
      intro i hi0 hil
      have hlen : p.length = 2 := rfl
      rw [hlen] at hil
      have hi : i = 1 := by omega
      subst i
      simpa [p] using ha
    refine ⟨⟨y, hy⟩, p, hp, ?_⟩
    simp [p, a]
  · let p : G.Walk x a := hxa.toWalk
    have hp : IsTwoInternalPath G p := by
      refine ⟨Walk.IsPath.of_adj hxa, by simp [p], ?_⟩
      intro i hi0 hil
      have hlen : p.length = 1 := rfl
      rw [hlen] at hil
      omega
    refine ⟨⟨a, ha⟩, p, hp, ?_⟩
    simp [p, a]

/-- A normalization chooses one terminal for each direction.  It does not
identify directions that happen to have the same terminal. -/
structure DirectionEndpointAssignment where
  terminal : TwoDirectionIncidence G → DegreeThreeVertex G
  reaches : ∀ d, TwoDirectionReaches G d (terminal d)

/-- The no-`3`-chain hypotheses construct a normalized terminal assignment
without any triangle assumption. -/
noncomputable def directionEndpointAssignment
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3) :
    DirectionEndpointAssignment G where
  terminal d := Classical.choose
    (exists_degreeThree_terminal_for_direction G hdeg hno3 d)
  reaches d := Classical.choose_spec
    (exists_degreeThree_terminal_for_direction G hdeg hno3 d)

/-- Direction incidences assigned to a given degree-three terminal. -/
noncomputable def directionSourceFinset (A : DirectionEndpointAssignment G)
    (y : DegreeThreeVertex G) : Finset (TwoDirectionIncidence G) := by
  classical
  exact Finset.univ.filter fun d ↦ A.terminal d = y

@[simp]
theorem mem_directionSourceFinset {A : DirectionEndpointAssignment G}
    {d : TwoDirectionIncidence G} {y : DegreeThreeVertex G} :
    d ∈ directionSourceFinset G A y ↔ A.terminal d = y := by
  classical
  simp [directionSourceFinset]

/-- The relation used for double counting: a degree-two vertex and a
degree-three vertex are incident when a two-internal path joins them. -/
def TwoThreeReach (x : DegreeTwoVertex G) (y : DegreeThreeVertex G) : Prop :=
  ReachesThroughTwo G x.1 y.1

theorem TwoThreeReach.ne (x : DegreeTwoVertex G) (y : DegreeThreeVertex G)
    (h : TwoThreeReach G x y) : x.1 ≠ y.1 :=
  ReachesThroughTwo.ne (G := G) h

/-- The degree-three endpoints reachable from a fixed degree-two vertex. -/
noncomputable def threadEndpointFinset (x : DegreeTwoVertex G) :
    Finset (DegreeThreeVertex G) := by
  classical
  exact Finset.univ.filter fun y ↦ TwoThreeReach G x y

/-- The degree-two sources reaching a fixed degree-three endpoint. -/
noncomputable def threadSourceFinset (y : DegreeThreeVertex G) :
    Finset (DegreeTwoVertex G) := by
  classical
  exact Finset.univ.filter fun x ↦ TwoThreeReach G x y

@[simp]
theorem mem_threadEndpointFinset {x : DegreeTwoVertex G}
    {y : DegreeThreeVertex G} :
    y ∈ threadEndpointFinset G x ↔ TwoThreeReach G x y := by
  classical
  simp [threadEndpointFinset]

@[simp]
theorem mem_threadSourceFinset {x : DegreeTwoVertex G}
    {y : DegreeThreeVertex G} :
    x ∈ threadSourceFinset G y ↔ TwoThreeReach G x y := by
  classical
  simp [threadSourceFinset]

/-- A pair of distinct reachable endpoints certifies the required lower
fiber bound. -/
theorem two_le_card_threadEndpointFinset_of_pair (x : DegreeTwoVertex G)
    {y₁ y₂ : DegreeThreeVertex G} (hy₁ : TwoThreeReach G x y₁)
    (hy₂ : TwoThreeReach G x y₂) (hne : y₁ ≠ y₂) :
    2 ≤ (threadEndpointFinset G x).card := by
  have hlt : 1 < (threadEndpointFinset G x).card :=
    Finset.one_lt_card.mpr
      ⟨y₁, (mem_threadEndpointFinset (G := G)).mpr hy₁,
        y₂, (mem_threadEndpointFinset (G := G)).mpr hy₂, hne⟩
  omega

/-- A local structural endpoint theorem.  If all degrees are two or three,
`3`-chains and triangles are absent, then every degree-two vertex reaches two
distinct degree-three endpoints.  The triangle hypothesis is genuinely
needed here to exclude a two-vertex path whose two ends return to the same
degree-three vertex. -/
theorem exists_two_distinct_three_endpoints
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    (htriangle : HasNoTriangle G) {x : V} (hx : IsTwoVertex G x) :
    ∃ y₁ y₂ : V, y₁ ≠ y₂ ∧
      IsThreeVertex G y₁ ∧ IsThreeVertex G y₂ ∧
      ReachesThroughTwo G x y₁ ∧ ReachesThroughTwo G x y₂ := by
  have hcard : (G.neighborFinset x).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hx
  obtain ⟨a, b, hab, hneighbors⟩ := Finset.card_eq_two.mp hcard
  have hxa : G.Adj x a := by
    apply (G.mem_neighborFinset x a).mp
    rw [hneighbors]
    simp
  have hxb : G.Adj x b := by
    apply (G.mem_neighborFinset x b).mp
    rw [hneighbors]
    simp
  obtain ⟨y₁, hy₁, hry₁, hform₁⟩ :=
    exists_three_endpoint_via_neighbor G hdeg hno3 hx hxa
  obtain ⟨y₂, hy₂, hry₂, hform₂⟩ :=
    exists_three_endpoint_via_neighbor G hdeg hno3 hx hxb
  have hnotBoth : ¬ (IsTwoVertex G a ∧ IsTwoVertex G b) :=
    not_both_two_neighbors_of_no_three_chain G hno3 hx hxa hxb hab
  have hyne : y₁ ≠ y₂ := by
    intro heq
    rcases hform₁ with hya | ⟨ha, haya⟩
    · rcases hform₂ with hyb | ⟨hb, hbyb⟩
      · exact hab (hya.symm.trans (heq.trans hyb))
      · have hyba : y₂ = a := heq.symm.trans hya
        rw [hyba] at hbyb
        exact htriangle x b a ⟨hxb, hbyb, hxa.symm⟩
    · rcases hform₂ with hyb | ⟨hb, _hbyb⟩
      · have hyab : y₁ = b := heq.trans hyb
        rw [hyab] at haya
        exact htriangle x a b ⟨hxa, haya, hxb.symm⟩
      · exact hnotBoth ⟨ha, hb⟩
  exact ⟨y₁, y₂, hyne, hy₁, hy₂, hry₁, hry₂⟩

/-- Finite-fiber form of `exists_two_distinct_three_endpoints`. -/
theorem two_le_card_threadEndpointFinset_of_no_three_chain_and_no_triangle
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    (htriangle : HasNoTriangle G) (x : DegreeTwoVertex G) :
    2 ≤ (threadEndpointFinset G x).card := by
  obtain ⟨y₁, y₂, hyne, hy₁, hy₂, hry₁, hry₂⟩ :=
    exists_two_distinct_three_endpoints G hdeg hno3 htriangle x.2
  let y₁' : DegreeThreeVertex G := ⟨y₁, hy₁⟩
  let y₂' : DegreeThreeVertex G := ⟨y₂, hy₂⟩
  apply two_le_card_threadEndpointFinset_of_pair G x
    (y₁ := y₁') (y₂ := y₂')
  · exact hry₁
  · exact hry₂
  · intro h
    exact hyne (congr_arg Subtype.val h)

/-- The preceding lower fiber bound from the usual minimum-degree and
subcubic hypotheses. -/
theorem two_le_card_threadEndpointFinset_of_isSubcubic_and_no_triangle
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    (htriangle : HasNoTriangle G) (x : DegreeTwoVertex G) :
    2 ≤ (threadEndpointFinset G x).card := by
  refine two_le_card_threadEndpointFinset_of_no_three_chain_and_no_triangle G
    ?_ hno3 htriangle x
  intro v hv
  have hlo := hmin v hv
  have hhi := hsub v
  simp only [IsTwoVertex, IsThreeVertex]
  omega

/-- Every internal vertex of a certified thread has its two distinct thread
endpoints in its endpoint fiber. -/
theorem IsKThread.two_le_card_endpointFinset_at_internal
    {u v : V} {p : G.Walk u v} {k i : ℕ}
    (hp : IsKThread G p k) (hi0 : 0 < i) (hil : i < p.length) :
    2 ≤ (threadEndpointFinset G
      ⟨p.getVert i, IsKThread.internal_two (G := G) hp hi0 hil⟩).card := by
  let x : DegreeTwoVertex G :=
    ⟨p.getVert i, IsKThread.internal_two (G := G) hp hi0 hil⟩
  let yu : DegreeThreeVertex G := ⟨u, hp.start_three⟩
  let yv : DegreeThreeVertex G := ⟨v, hp.end_three⟩
  apply two_le_card_threadEndpointFinset_of_pair G x
    (y₁ := yu) (y₂ := yv)
  · exact IsKThread.internal_reaches_start (G := G) hp hi0 hil
  · exact IsKThread.internal_reaches_end (G := G) hp hi0 hil
  · intro huv
    apply hp.endpoints_ne
    exact congr_arg Subtype.val huv

/-- The two ways of counting the `TwoThreeReach` relation agree. -/
theorem sum_card_threadEndpointFinset_eq_sum_card_threadSourceFinset :
    (∑ x : DegreeTwoVertex G, (threadEndpointFinset G x).card) =
      ∑ y : DegreeThreeVertex G, (threadSourceFinset G y).card := by
  classical
  simpa [threadEndpointFinset, threadSourceFinset] using
    (sum_card_relation_fiber_comm (TwoThreeReach G))

/-- The finite subtype of degree-two vertices has the same cardinality as
the corresponding degree class from `MaximumAverageDegree.lean`. -/
theorem card_degreeTwoVertex :
    Fintype.card (DegreeTwoVertex G) = (degreeClass G 2).card := by
  classical
  simpa [DegreeTwoVertex, IsTwoVertex, degreeClass] using
    (Fintype.card_subtype (fun v : V ↦ IsTwoVertex G v))

/-- The analogous cardinality bridge for degree-three vertices. -/
theorem card_degreeThreeVertex :
    Fintype.card (DegreeThreeVertex G) = (degreeClass G 3).card := by
  classical
  simpa [DegreeThreeVertex, IsThreeVertex, degreeClass] using
    (Fintype.card_subtype (fun v : V ↦ IsThreeVertex G v))

/-! ### Direction-multiplicity counting

Unlike `TwoThreeReach`, this interface counts the two directions at a
degree-two vertex separately.  Thus it is the appropriate interface when a
thread can return to the same degree-three endpoint (for example around a
triangle). -/

/-- Minimum degree two, subcubicity, and absence of a `3`-chain produce a
normalized endpoint assignment for all degree-two directions.  In
particular, no girth or triangle hypothesis is needed. -/
theorem nonempty_directionEndpointAssignment_of_isSubcubic
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3) :
    Nonempty (DirectionEndpointAssignment G) := by
  refine ⟨directionEndpointAssignment G ?_ hno3⟩
  intro v hv
  have hlo := hmin v hv
  have hhi := hsub v
  simp only [IsTwoVertex, IsThreeVertex]
  omega

/-- A named canonical (classical-choice) assignment under the standard
Section 3 degree and no-`3`-chain assumptions. -/
noncomputable def directionEndpointAssignmentOfIsSubcubic
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3) :
    DirectionEndpointAssignment G :=
  Classical.choice
    (nonempty_directionEndpointAssignment_of_isSubcubic G hmin hsub hno3)

/-- If at most three directed degree-two incidences are assigned to each
degree-three terminal, double counting gives `2 n₂ ≤ 3 n₃`.  Directions
are counted with multiplicity even when two of them have the same terminal. -/
theorem two_mul_degreeTwo_le_three_mul_degreeThree_of_directionAssignment
    (A : DirectionEndpointAssignment G)
    (hupper : ∀ y : DegreeThreeVertex G,
      (directionSourceFinset G A y).card ≤ 3) :
    2 * (degreeClass G 2).card ≤ 3 * (degreeClass G 3).card := by
  classical
  have hcount := mul_card_le_mul_card_of_relation
    (fun d : TwoDirectionIncidence G ↦
      fun y : DegreeThreeVertex G ↦ A.terminal d = y) 1 3
    (by
      intro d
      have hmem : A.terminal d ∈
          Finset.univ.filter
            (fun y : DegreeThreeVertex G ↦ A.terminal d = y) := by
        simp
      have hpos : 0 < (Finset.univ.filter
          (fun y : DegreeThreeVertex G ↦ A.terminal d = y)).card :=
        Finset.card_pos.mpr ⟨A.terminal d, hmem⟩
      omega)
    (by
      intro y
      simpa [directionSourceFinset] using hupper y)
  rw [one_mul, card_twoDirectionIncidence (G := G),
    card_degreeTwoVertex G, card_degreeThreeVertex G] at hcount
  exact hcount

/-- Section 3's arithmetic contradiction using direction multiplicity.  The
only graph-structural input left abstract here is the honest upper-fiber
bound on the normalized assignment; no triangle assumption is present. -/
theorem not_maximumAverageDegreeLT_twelve_five_of_directionAssignment
    (hEdge : G.edgeFinset.Nonempty)
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G)
    (A : DirectionEndpointAssignment G)
    (hupper : ∀ y : DegreeThreeVertex G,
      (directionSourceFinset G A y).card ≤ 3) :
    ¬ MaximumAverageDegreeLT G 12 5 := by
  intro hmad
  have hlt :=
    hmad.three_mul_degreeThree_lt_two_mul_degreeTwo_of_active
      hEdge hmin hsub rfl rfl
  have hle :=
    two_mul_degreeTwo_le_three_mul_degreeThree_of_directionAssignment
      G A hupper
  omega

/-- No-triangle-free closing interface under the standard Section 3 local
hypotheses.  The displayed upper bound is exactly the remaining structural
claim about reducible configurations. -/
theorem not_maximumAverageDegreeLT_twelve_five_of_no_three_chain_and_direction_bound
    (hEdge : G.edgeFinset.Nonempty)
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    (hupper : ∀ y : DegreeThreeVertex G,
      (directionSourceFinset G
        (directionEndpointAssignmentOfIsSubcubic G hmin hsub hno3) y).card ≤ 3) :
    ¬ MaximumAverageDegreeLT G 12 5 := by
  exact not_maximumAverageDegreeLT_twelve_five_of_directionAssignment G
    hEdge hmin hsub
    (directionEndpointAssignmentOfIsSubcubic G hmin hsub hno3) hupper

/-- Specialized interface to `mul_card_le_mul_card_of_relation`. -/
theorem two_mul_degreeTwo_le_three_mul_degreeThree_of_reach_fibers
    (hleft : ∀ x : DegreeTwoVertex G,
      2 ≤ (threadEndpointFinset G x).card)
    (hright : ∀ y : DegreeThreeVertex G,
      (threadSourceFinset G y).card ≤ 3) :
    2 * (degreeClass G 2).card ≤ 3 * (degreeClass G 3).card := by
  classical
  have hcount := mul_card_le_mul_card_of_relation
    (TwoThreeReach G) 2 3
    (by simpa [threadEndpointFinset] using hleft)
    (by simpa [threadSourceFinset] using hright)
  simpa [card_degreeTwoVertex G, card_degreeThreeVertex G] using hcount

/-- Honest closing interface for the Section 3 discharging contradiction.
The two fiber hypotheses are precisely the remaining structural content. -/
theorem not_maximumAverageDegreeLT_twelve_five_of_reach_fibers
    (hEdge : G.edgeFinset.Nonempty)
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G)
    (hleft : ∀ x : DegreeTwoVertex G,
      2 ≤ (threadEndpointFinset G x).card)
    (hright : ∀ y : DegreeThreeVertex G,
      (threadSourceFinset G y).card ≤ 3) :
    ¬ MaximumAverageDegreeLT G 12 5 := by
  intro hmad
  have hlt :=
    hmad.three_mul_degreeThree_lt_two_mul_degreeTwo_of_active
      hEdge hmin hsub rfl rfl
  have hle :=
    two_mul_degreeTwo_le_three_mul_degreeThree_of_reach_fibers G hleft hright
  omega

/-- With the lower fibers discharged by the local no-`3`-chain argument, only
the paper's upper-fiber structural bound remains to contradict
`mad(G) < 12/5`. -/
theorem not_maximumAverageDegreeLT_twelve_five_of_no_three_chain_and_no_triangle
    (hEdge : G.edgeFinset.Nonempty)
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    (htriangle : HasNoTriangle G)
    (hright : ∀ y : DegreeThreeVertex G,
      (threadSourceFinset G y).card ≤ 3) :
    ¬ MaximumAverageDegreeLT G 12 5 := by
  apply not_maximumAverageDegreeLT_twelve_five_of_reach_fibers G
    hEdge hmin hsub _ hright
  intro x
  exact two_le_card_threadEndpointFinset_of_isSubcubic_and_no_triangle G
    hmin hsub hno3 htriangle x

end Finite

end

end LeanCo.PackingEdgeColoring
