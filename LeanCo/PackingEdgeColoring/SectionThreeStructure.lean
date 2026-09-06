import LeanCo.PackingEdgeColoring.ThreadReach

/-!
# The three branches at a degree-three vertex

This file isolates the structural counting step in Section 3 of
Kim--Liu--Xu.  The relevant objects are the *directed* degree-two
incidences from `ThreadReach.lean`; consequently two routes which return to
the same degree-three vertex are still counted with multiplicity.

For a normalized endpoint assignment, every assigned incidence has a
chosen two-internal witnessing path.  Its last neighbor is the branch by
which it enters the terminal.  The resulting branch finsets partition the
terminal fiber.  Under the no-`3`-chain hypothesis every branch contains at
most two incidences.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

universe u

variable {V : Type u} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-! ## A chosen terminal-side branch -/

/-- The witnessing path carried propositionally by an endpoint assignment,
chosen once and for all. -/
noncomputable def assignedWalk (A : DirectionEndpointAssignment G)
    (d : TwoDirectionIncidence G) : G.Walk d.1.1 (A.terminal d).1 :=
  Classical.choose (A.reaches d)

/-- The chosen walk satisfies the two-internal path condition. -/
theorem assignedWalk_isTwoInternalPath (A : DirectionEndpointAssignment G)
    (d : TwoDirectionIncidence G) :
    IsTwoInternalPath G (assignedWalk G A d) :=
  (Classical.choose_spec (A.reaches d)).1

/-- Its first step is the direction recorded by the incidence. -/
theorem assignedWalk_getVert_one (A : DirectionEndpointAssignment G)
    (d : TwoDirectionIncidence G) :
    (assignedWalk G A d).getVert 1 = d.2.1 :=
  (Classical.choose_spec (A.reaches d)).2

/-- A two-internal path starting at a degree-two vertex has length at most
two when `3`-chains are forbidden. -/
theorem IsTwoInternalPath.length_le_two_of_no_three_chain
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    {u v : V} {p : G.Walk u v} (hp : IsTwoInternalPath G p)
    (hu : IsTwoVertex G u) :
    p.length ≤ 2 := by
  by_contra hlen
  have hthree : 3 ≤ p.length := by omega
  have h01 : G.Adj (p.getVert 0) (p.getVert 1) :=
    p.adj_getVert_succ (by omega)
  have h12 : G.Adj (p.getVert 1) (p.getVert 2) :=
    p.adj_getVert_succ (by omega)
  have h02 : p.getVert 0 ≠ p.getVert 2 := by
    intro heq
    have hi := hp.isPath.getVert_injOn
      (show 0 ∈ {i : ℕ | i ≤ p.length} by simp)
      (show 2 ∈ {i : ℕ | i ≤ p.length} by simp; omega) heq
    omega
  have hzero : p.getVert 0 = u := by simp
  have htwo0 : IsTwoVertex G (p.getVert 0) := by simpa [hzero] using hu
  have htwo1 : IsTwoVertex G (p.getVert 1) :=
    IsTwoInternalPath.internal_two (G := G) hp (i := 1) (by omega) (by omega)
  have htwo2 : IsTwoVertex G (p.getVert 2) :=
    IsTwoInternalPath.internal_two (G := G) hp (i := 2) (by omega) (by omega)
  exact hno3 (.cons h01 (.cons h12 .nil))
    (isKChain_three_of_adj G h01 h12 h02 htwo0 htwo1 htwo2)

/-- The vertex immediately preceding the assigned terminal on the chosen
path. -/
noncomputable def terminalBranchVertex (A : DirectionEndpointAssignment G)
    (d : TwoDirectionIncidence G) : V :=
  let p := assignedWalk G A d
  p.getVert (p.length - 1)

/-- The terminal branch vertex really is adjacent to the terminal. -/
theorem terminalBranchVertex_adj_terminal
    (A : DirectionEndpointAssignment G) (d : TwoDirectionIncidence G) :
    G.Adj (terminalBranchVertex G A d) (A.terminal d).1 := by
  let p := assignedWalk G A d
  have hp := assignedWalk_isTwoInternalPath G A d
  have hpos : 0 < p.length := hp.pos
  have hi : p.length - 1 < p.length := by omega
  have hadj := p.adj_getVert_succ hi
  have hs : p.length - 1 + 1 = p.length := by omega
  rw [hs, p.getVert_length] at hadj
  exact hadj

/-- Assigned incidences entering `y` through the neighboring vertex `n`.
The definition uses a genuine terminal-side branch, not merely a numerical
cardinality condition. -/
noncomputable def directionBranchFinset
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G) (n : V) :
    Finset (TwoDirectionIncidence G) := by
  classical
  exact (directionSourceFinset G A y).filter fun d ↦
    terminalBranchVertex G A d = n

@[simp]
theorem mem_directionBranchFinset
    {A : DirectionEndpointAssignment G} {y : DegreeThreeVertex G} {n : V}
    {d : TwoDirectionIncidence G} :
    d ∈ directionBranchFinset G A y n ↔
      A.terminal d = y ∧ terminalBranchVertex G A d = n := by
  classical
  simp [directionBranchFinset]

/-- The branch finsets give an exact partition of the assigned terminal
fiber over the three ambient neighbors of `y`. -/
theorem card_directionSourceFinset_eq_sum_directionBranchFinset
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G) :
    (directionSourceFinset G A y).card =
      ∑ n ∈ G.neighborFinset y.1, (directionBranchFinset G A y n).card := by
  classical
  let f : TwoDirectionIncidence G → V := terminalBranchVertex G A
  have hmap :
      ((directionSourceFinset G A y : Finset (TwoDirectionIncidence G)) :
          Set (TwoDirectionIncidence G)).MapsTo f (G.neighborFinset y.1) := by
    intro d hd
    have hterminal : A.terminal d = y :=
      (mem_directionSourceFinset (G := G)).mp hd
    apply (G.mem_neighborFinset y.1 (f d)).mpr
    have hadj := terminalBranchVertex_adj_terminal G A d
    simpa [f, hterminal] using hadj.symm
  simpa [directionBranchFinset, f] using
    (Finset.card_eq_sum_card_fiberwise hmap)

/-! ## The local size of one branch -/

/-- Equality of directed incidences is determined by their source and their
chosen neighboring direction. -/
theorem twoDirectionIncidence_ext {d e : TwoDirectionIncidence G}
    (hsource : d.1.1 = e.1.1) (hdirection : d.2.1 = e.2.1) : d = e := by
  rcases d with ⟨x, a⟩
  rcases e with ⟨z, b⟩
  have hxz : x = z := Subtype.ext hsource
  subst z
  have hab : a = b := Subtype.ext hdirection
  subst b
  rfl

/-- In a degree-two vertex, the neighbor different from a specified
neighbor is unique. -/
theorem eq_of_adj_of_ne_of_isTwoVertex
    {n y x z : V} (hn : IsTwoVertex G n)
    (hny : G.Adj n y) (hnx : G.Adj n x) (hnz : G.Adj n z)
    (hxy : x ≠ y) (hzy : z ≠ y) : x = z := by
  by_contra hxz
  have hsubset : ({y, x, z} : Finset V) ⊆ G.neighborFinset n := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw
    · subst w
      exact (G.mem_neighborFinset n y).mpr hny
    · subst w
      exact (G.mem_neighborFinset n x).mpr hnx
    · subst w
      exact (G.mem_neighborFinset n z).mpr hnz
  have hcard := Finset.card_le_card hsubset
  have hneighborCard : (G.neighborFinset n).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hn
  have hthree : ({y, x, z} : Finset V).card = 3 := by
    simp [hxy, hxy.symm, hzy, hzy.symm, hxz]
  omega

/-- A branch incidence has one of the two expected local forms.  A
length-one witness is based at the branch vertex and points directly to the
terminal.  A length-two witness points from its source into the branch
vertex.  In either case the branch vertex has degree two. -/
theorem mem_directionBranchFinset_shapes
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    {A : DirectionEndpointAssignment G} {y : DegreeThreeVertex G} {n : V}
    {d : TwoDirectionIncidence G}
    (hd : d ∈ directionBranchFinset G A y n) :
    IsTwoVertex G n ∧
      ((d.1.1 = n ∧ d.2.1 = y.1) ∨ d.2.1 = n) := by
  have hmem := (mem_directionBranchFinset (G := G)).mp hd
  let p := assignedWalk G A d
  have hp : IsTwoInternalPath G p := assignedWalk_isTwoInternalPath G A d
  have hle : p.length ≤ 2 :=
    IsTwoInternalPath.length_le_two_of_no_three_chain G hno3 hp d.1.2
  have hpos : 0 < p.length := hp.pos
  have hlen : p.length = 1 ∨ p.length = 2 := by omega
  have hfirst : p.getVert 1 = d.2.1 := assignedWalk_getVert_one G A d
  have hbranch : p.getVert (p.length - 1) = n := by
    exact hmem.2
  rcases hlen with hlen | hlen
  · have hsource : d.1.1 = n := by
      have hb := hbranch
      rw [hlen] at hb
      simpa using hb
    have hend : p.getVert 1 = y.1 := by
      calc
        p.getVert 1 = p.getVert p.length := by rw [hlen]
        _ = (A.terminal d).1 := p.getVert_length
        _ = y.1 := congrArg Subtype.val hmem.1
    refine ⟨?_, Or.inl ⟨hsource, ?_⟩⟩
    · simpa [← hsource] using d.1.2
    · exact hfirst.symm.trans hend
  · have hdirection : d.2.1 = n := by
      have hb := hbranch
      rw [hlen] at hb
      have hone : p.getVert 1 = n := by simpa using hb
      exact hfirst.symm.trans hone
    refine ⟨?_, Or.inr hdirection⟩
    have hone : p.getVert 1 = n := hfirst.trans hdirection
    simpa [← hone] using
      (IsTwoInternalPath.internal_two (G := G) hp (i := 1)
        (by omega) (by omega))

/-- If the recorded first direction is already a degree-three vertex, its
assigned witness consists of that one edge. -/
theorem assignedWalk_length_eq_one_of_direction_three
    (A : DirectionEndpointAssignment G) (d : TwoDirectionIncidence G)
    (hthree : IsThreeVertex G d.2.1) :
    (assignedWalk G A d).length = 1 := by
  let p := assignedWalk G A d
  have hp : IsTwoInternalPath G p := assignedWalk_isTwoInternalPath G A d
  have hpos : 0 < p.length := hp.pos
  have hle : p.length ≤ 1 := by
    by_contra hlen
    have hone : 1 < p.length := by omega
    have htwo : IsTwoVertex G (p.getVert 1) :=
      IsTwoInternalPath.internal_two (G := G) hp (i := 1) (by omega) hone
    have hfirst : p.getVert 1 = d.2.1 := assignedWalk_getVert_one G A d
    rw [hfirst] at htwo
    unfold IsTwoVertex at htwo
    unfold IsThreeVertex at hthree
    omega
  change p.length = 1
  omega

/-- Consequently the assigned terminal is the degree-three direction. -/
theorem terminal_eq_direction_of_direction_three
    (A : DirectionEndpointAssignment G) (d : TwoDirectionIncidence G)
    (hthree : IsThreeVertex G d.2.1) :
    (A.terminal d).1 = d.2.1 := by
  let p := assignedWalk G A d
  have hlen : p.length = 1 :=
    assignedWalk_length_eq_one_of_direction_three G A d hthree
  calc
    (A.terminal d).1 = p.getVert p.length := p.getVert_length.symm
    _ = p.getVert 1 := by rw [hlen]
    _ = d.2.1 := assignedWalk_getVert_one G A d

/-- For such a one-edge assignment, its terminal-side branch is its source
vertex. -/
theorem terminalBranchVertex_eq_source_of_direction_three
    (A : DirectionEndpointAssignment G) (d : TwoDirectionIncidence G)
    (hthree : IsThreeVertex G d.2.1) :
    terminalBranchVertex G A d = d.1.1 := by
  let p := assignedWalk G A d
  have hlen : p.length = 1 :=
    assignedWalk_length_eq_one_of_direction_three G A d hthree
  change p.getVert (p.length - 1) = d.1.1
  rw [hlen]
  simp

/-- The canonical direct incidence from a degree-two neighbor into a
degree-three vertex. -/
def directDirectionIncidence (y : DegreeThreeVertex G) (n : V)
    (hn : IsTwoVertex G n) (hyn : G.Adj y.1 n) :
    TwoDirectionIncidence G :=
  ⟨⟨n, hn⟩, ⟨y.1, hyn.symm⟩⟩

/-- Every degree-two neighbor contributes its direct incidence to its
degree-three neighbor's branch, for every endpoint assignment. -/
theorem directDirectionIncidence_mem_branch
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G) (n : V)
    (hn : IsTwoVertex G n) (hyn : G.Adj y.1 n) :
    directDirectionIncidence G y n hn hyn ∈
      directionBranchFinset G A y n := by
  let d := directDirectionIncidence G y n hn hyn
  apply (mem_directionBranchFinset (G := G)).mpr
  constructor
  · apply Subtype.ext
    simpa [d, directDirectionIncidence] using
      (terminal_eq_direction_of_direction_three G A d y.2)
  · simpa [d, directDirectionIncidence] using
      (terminalBranchVertex_eq_source_of_direction_three G A d y.2)

/-- Every terminal branch has at most two assigned directed incidences.
This remains true when two distinct branches return to the same terminal. -/
theorem card_directionBranchFinset_le_two
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G) (n : V) :
    (directionBranchFinset G A y n).card ≤ 2 := by
  classical
  by_cases hempty : directionBranchFinset G A y n = ∅
  · simp [hempty]
  · obtain ⟨d₀, hd₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hn : IsTwoVertex G n :=
      (mem_directionBranchFinset_shapes G hno3 hd₀).1
    have hyn : G.Adj y.1 n := by
      have hterminal := terminalBranchVertex_adj_terminal G A d₀
      have hm := (mem_directionBranchFinset (G := G)).mp hd₀
      rw [hm.2, congrArg Subtype.val hm.1] at hterminal
      exact hterminal.symm
    obtain ⟨z, hzy, hnz⟩ :=
      exists_other_neighbor_of_isTwoVertex G hn hyn.symm
    let nd : DegreeTwoVertex G := ⟨n, hn⟩
    let direct : TwoDirectionIncidence G :=
      ⟨nd, ⟨y.1, hyn.symm⟩⟩
    by_cases hz : IsTwoVertex G z
    · let zd : DegreeTwoVertex G := ⟨z, hz⟩
      let incoming : TwoDirectionIncidence G :=
        ⟨zd, ⟨n, hnz.symm⟩⟩
      have hsubset : directionBranchFinset G A y n ⊆ {direct, incoming} := by
        intro d hd
        have hshape := mem_directionBranchFinset_shapes G hno3 hd
        rcases hshape.2 with hdirect | hincoming
        · have hdeq : d = direct := by
            apply twoDirectionIncidence_ext G
            · exact hdirect.1
            · exact hdirect.2
          simp [hdeq]
        · have hdn : G.Adj n d.1.1 := by
            have := d.2.2
            rw [hincoming] at this
            exact this.symm
          have hdy : d.1.1 ≠ y.1 := by
            intro h
            have hdeg := d.1.2
            rw [h] at hdeg
            have hydeg := y.2
            exact by
              unfold IsTwoVertex at hdeg
              unfold IsThreeVertex at hydeg
              omega
          have hdz : d.1.1 = z :=
            eq_of_adj_of_ne_of_isTwoVertex G hn hyn.symm hdn hnz hdy hzy
          have hdeq : d = incoming := by
            apply twoDirectionIncidence_ext G
            · exact hdz
            · exact hincoming
          simp [hdeq]
      exact (Finset.card_le_card hsubset).trans Finset.card_le_two
    · have hsubset : directionBranchFinset G A y n ⊆ {direct} := by
        intro d hd
        have hshape := mem_directionBranchFinset_shapes G hno3 hd
        rcases hshape.2 with hdirect | hincoming
        · have hdeq : d = direct := by
            apply twoDirectionIncidence_ext G
            · exact hdirect.1
            · exact hdirect.2
          simp [hdeq]
        · have hdn : G.Adj n d.1.1 := by
            have := d.2.2
            rw [hincoming] at this
            exact this.symm
          have hdy : d.1.1 ≠ y.1 := by
            intro h
            have hdeg := d.1.2
            rw [h] at hdeg
            have hydeg := y.2
            exact by
              unfold IsTwoVertex at hdeg
              unfold IsThreeVertex at hydeg
              omega
          have hdz : d.1.1 = z :=
            eq_of_adj_of_ne_of_isTwoVertex G hn hyn.symm hdn hnz hdy hzy
          exact False.elim (hz (hdz ▸ d.1.2))
      have hcard := Finset.card_le_card hsubset
      simp at hcard
      omega

/-! ## Honest local configurations -/

/-- A positive branch at `u`: the neighboring branch vertex has degree two.
It may continue for one or two degree-two vertices. -/
def IsPositiveTwoBranchAt (u n : V) : Prop :=
  G.Adj u n ∧ IsTwoVertex G n

/-- A two-thread branch written purely in local graph language.  The two
consecutive degree-two vertices are `n,x`; `z` is the far degree-three
terminal.  We allow `z = u`, so a branch returning around a triangle is not
silently discarded. -/
def IsTwoThreadBranchAt (u n : V) : Prop :=
  G.Adj u n ∧ IsTwoVertex G n ∧
    ∃ x z : V, G.Adj n x ∧ x ≠ u ∧ IsTwoVertex G x ∧
      G.Adj x z ∧ z ≠ n ∧ IsThreeVertex G z

/-- A zero branch: the neighbor itself has degree three. -/
def IsZeroBranchAt (u n : V) : Prop :=
  G.Adj u n ∧ IsThreeVertex G n

/-- The paper's `(2,1,1)` configuration.  One incident branch is a genuine
two-thread and each of the other two starts with a degree-two vertex.  The
latter branches are allowed to have length two, matching the paper's use of
`1`-chains rather than *exactly* `1`-threads. -/
def HasTwoOneOneConfigurationAt (u : V) : Prop :=
  IsThreeVertex G u ∧
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsTwoThreadBranchAt G u a ∧
      IsPositiveTwoBranchAt G u b ∧ IsPositiveTwoBranchAt G u c

/-- The paper's `(2,2,0)` configuration: two genuine two-thread branches
and a third degree-three neighbor. -/
def HasTwoTwoZeroConfigurationAt (u : V) : Prop :=
  IsThreeVertex G u ∧
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsTwoThreadBranchAt G u a ∧ IsTwoThreadBranchAt G u b ∧
      IsZeroBranchAt G u c

/-- Existence of a `(2,1,1)` configuration somewhere in the graph. -/
def HasTwoOneOneConfiguration : Prop :=
  ∃ u : V, HasTwoOneOneConfigurationAt G u

/-- Existence of a `(2,2,0)` configuration somewhere in the graph. -/
def HasTwoTwoZeroConfiguration : Prop :=
  ∃ u : V, HasTwoTwoZeroConfigurationAt G u

/-- A nonempty assigned branch is a positive degree-two branch. -/
theorem isPositiveTwoBranchAt_of_directionBranchFinset_card_pos
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G) (n : V)
    (hpos : 0 < (directionBranchFinset G A y n).card) :
    IsPositiveTwoBranchAt G y.1 n := by
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
  have hn : IsTwoVertex G n :=
    (mem_directionBranchFinset_shapes G hno3 hd).1
  have hmem := (mem_directionBranchFinset (G := G)).mp hd
  have hadj := terminalBranchVertex_adj_terminal G A d
  rw [hmem.2, congrArg Subtype.val hmem.1] at hadj
  exact ⟨hadj.symm, hn⟩

/-- Under the `{2,3}` degree dichotomy, a zero-cardinality branch is a
degree-three neighbor. -/
theorem isZeroBranchAt_of_directionBranchFinset_card_eq_zero
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G) (n : V)
    (hyn : G.Adj y.1 n)
    (hzero : (directionBranchFinset G A y n).card = 0) :
    IsZeroBranchAt G y.1 n := by
  refine ⟨hyn, ?_⟩
  rcases hdeg n hyn.degree_pos_right with hn | hn
  · have hmem := directDirectionIncidence_mem_branch G A y n hn hyn
    have hpos : 0 < (directionBranchFinset G A y n).card :=
      Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  · exact hn

/-- A branch of cardinality two contains a genuine two-thread branch.
The far terminal may equal `y`; this is the loop-back case that endpoint
deduplication would miss. -/
theorem isTwoThreadBranchAt_of_directionBranchFinset_card_eq_two
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 3)
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G) (n : V)
    (htwo : (directionBranchFinset G A y n).card = 2) :
    IsTwoThreadBranchAt G y.1 n := by
  have hpos : 0 < (directionBranchFinset G A y n).card := by omega
  have hpositive :=
    isPositiveTwoBranchAt_of_directionBranchFinset_card_pos G hno3 A y n hpos
  have hyn : G.Adj y.1 n := hpositive.1
  have hn : IsTwoVertex G n := hpositive.2
  let direct := directDirectionIncidence G y n hn hyn
  have hdirect : direct ∈ directionBranchFinset G A y n :=
    directDirectionIncidence_mem_branch G A y n hn hyn
  have herase :
      ((directionBranchFinset G A y n).erase direct).card = 1 := by
    rw [Finset.card_erase_of_mem hdirect, htwo]
  have herasePos :
      0 < ((directionBranchFinset G A y n).erase direct).card := by omega
  obtain ⟨d, hdErase⟩ := Finset.card_pos.mp herasePos
  have hne : d ≠ direct := (Finset.mem_erase.mp hdErase).1
  have hd : d ∈ directionBranchFinset G A y n :=
    (Finset.mem_erase.mp hdErase).2
  have hshape := mem_directionBranchFinset_shapes G hno3 hd
  have hincoming : d.2.1 = n := by
    rcases hshape.2 with hdirect | hincoming
    · exfalso
      apply hne
      apply twoDirectionIncidence_ext G
      · exact hdirect.1
      · exact hdirect.2
    · exact hincoming
  let x : V := d.1.1
  have hx : IsTwoVertex G x := d.1.2
  have hxn : G.Adj x n := by
    have := d.2.2
    simpa [x, hincoming] using this
  have hxy : x ≠ y.1 := by
    intro h
    have hxdeg := hx
    rw [h] at hxdeg
    have hydeg := y.2
    unfold IsTwoVertex at hxdeg
    unfold IsThreeVertex at hydeg
    omega
  obtain ⟨z, hzn, hxz⟩ :=
    exists_other_neighbor_of_isTwoVertex G hx hxn
  have hz : IsThreeVertex G z := by
    rcases hdeg z hxz.degree_pos_right with hz | hz
    · exact False.elim <| hno3 (.cons hxn.symm (.cons hxz .nil))
        (isKChain_three_of_adj G hxn.symm hxz hzn.symm hn hx hz)
    · exact hz
  exact ⟨hyn, hn, x, z, hxn.symm, hxy, hx, hxz, hzn, hz⟩

/-! ## From three branch loads to the two forbidden signatures -/

/-- Pure numerical content of the signature argument.  Three numbers in
`{0,1,2}` whose sum is at least four either have a `2` together with two
positive entries, or have signature `(2,2,0)`, up to permutation. -/
theorem three_branch_signature_of_four_le_sum
    {a b c : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2)
    (hsum : 4 ≤ a + b + c) :
    ((a = 2 ∧ 1 ≤ b ∧ 1 ≤ c) ∨
      (b = 2 ∧ 1 ≤ a ∧ 1 ≤ c) ∨
      (c = 2 ∧ 1 ≤ a ∧ 1 ≤ b)) ∨
    ((a = 2 ∧ b = 2 ∧ c = 0) ∨
      (a = 2 ∧ c = 2 ∧ b = 0) ∨
      (b = 2 ∧ c = 2 ∧ a = 0)) := by
  omega

/-- Branch-cardinality bridge to the honest `(2,1,1)` graph
configuration. -/
theorem hasTwoOneOneConfigurationAt_of_branch_cards
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 3)
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : (directionBranchFinset G A y a).card = 2)
    (hb : 1 ≤ (directionBranchFinset G A y b).card)
    (hc : 1 ≤ (directionBranchFinset G A y c).card) :
    HasTwoOneOneConfigurationAt G y.1 := by
  refine ⟨y.2, a, b, c, hab, hac, hbc, ?_, ?_, ?_⟩
  · exact isTwoThreadBranchAt_of_directionBranchFinset_card_eq_two
      G hdeg hno3 A y a ha
  · exact isPositiveTwoBranchAt_of_directionBranchFinset_card_pos
      G hno3 A y b (by omega)
  · exact isPositiveTwoBranchAt_of_directionBranchFinset_card_pos
      G hno3 A y c (by omega)

/-- Branch-cardinality bridge to the honest `(2,2,0)` graph
configuration. -/
theorem hasTwoTwoZeroConfigurationAt_of_branch_cards
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 3)
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcAdj : G.Adj y.1 c)
    (ha : (directionBranchFinset G A y a).card = 2)
    (hb : (directionBranchFinset G A y b).card = 2)
    (hc : (directionBranchFinset G A y c).card = 0) :
    HasTwoTwoZeroConfigurationAt G y.1 := by
  refine ⟨y.2, a, b, c, hab, hac, hbc, ?_, ?_, ?_⟩
  · exact isTwoThreadBranchAt_of_directionBranchFinset_card_eq_two
      G hdeg hno3 A y a ha
  · exact isTwoThreadBranchAt_of_directionBranchFinset_card_eq_two
      G hdeg hno3 A y b hb
  · exact isZeroBranchAt_of_directionBranchFinset_card_eq_zero
      G hdeg A y c hcAdj hc

/-! ## The Section 3 upper fiber bound -/

/-- Excluding the two paper configurations at a fixed degree-three vertex
forces its direction-multiplicity fiber to have cardinality at most three. -/
theorem card_directionSourceFinset_le_three_of_forbidden_configurations_at
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 3)
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G)
    (hno211 : ¬ HasTwoOneOneConfigurationAt G y.1)
    (hno220 : ¬ HasTwoTwoZeroConfigurationAt G y.1) :
    (directionSourceFinset G A y).card ≤ 3 := by
  classical
  by_contra hcard
  have hfour : 4 ≤ (directionSourceFinset G A y).card := by omega
  have hneighborCard : (G.neighborFinset y.1).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact y.2
  obtain ⟨a, b, c, hab, hac, hbc, hneighbors⟩ :=
    Finset.card_eq_three.mp hneighborCard
  let la := (directionBranchFinset G A y a).card
  let lb := (directionBranchFinset G A y b).card
  let lc := (directionBranchFinset G A y c).card
  have hsum : (directionSourceFinset G A y).card = la + lb + lc := by
    have hpartition :=
      card_directionSourceFinset_eq_sum_directionBranchFinset G A y
    rw [hneighbors] at hpartition
    have hpartition' :
        (directionSourceFinset G A y).card = la + (lb + lc) := by
      simpa [la, lb, lc, hab, hac, hbc] using hpartition
    omega
  have hla : la ≤ 2 := by
    exact card_directionBranchFinset_le_two G hno3 A y a
  have hlb : lb ≤ 2 := by
    exact card_directionBranchFinset_le_two G hno3 A y b
  have hlc : lc ≤ 2 := by
    exact card_directionBranchFinset_le_two G hno3 A y c
  have hload : 4 ≤ la + lb + lc := by omega
  have hsignature :=
    three_branch_signature_of_four_le_sum hla hlb hlc hload
  have hya : G.Adj y.1 a := by
    apply (G.mem_neighborFinset y.1 a).mp
    rw [hneighbors]
    simp
  have hyb : G.Adj y.1 b := by
    apply (G.mem_neighborFinset y.1 b).mp
    rw [hneighbors]
    simp
  have hyc : G.Adj y.1 c := by
    apply (G.mem_neighborFinset y.1 c).mp
    rw [hneighbors]
    simp
  rcases hsignature with h211 | h220
  · rcases h211 with h211 | h211 | h211
    · exact hno211 <|
        hasTwoOneOneConfigurationAt_of_branch_cards G hdeg hno3 A y
          hab hac hbc h211.1 h211.2.1 h211.2.2
    · exact hno211 <|
        hasTwoOneOneConfigurationAt_of_branch_cards G hdeg hno3 A y
          hab.symm hbc hac h211.1 h211.2.1 h211.2.2
    · exact hno211 <|
        hasTwoOneOneConfigurationAt_of_branch_cards G hdeg hno3 A y
          hac.symm hbc.symm hab h211.1 h211.2.1 h211.2.2
  · rcases h220 with h220 | h220 | h220
    · exact hno220 <|
        hasTwoTwoZeroConfigurationAt_of_branch_cards G hdeg hno3 A y
          hab hac hbc hyc h220.1 h220.2.1 h220.2.2
    · exact hno220 <|
        hasTwoTwoZeroConfigurationAt_of_branch_cards G hdeg hno3 A y
          hac hab hbc.symm hyb h220.1 h220.2.1 h220.2.2
    · exact hno220 <|
        hasTwoTwoZeroConfigurationAt_of_branch_cards G hdeg hno3 A y
          hbc hab.symm hac.symm hya h220.1 h220.2.1 h220.2.2

/-- Global forbidden-configuration form of the same upper-fiber bound. -/
theorem card_directionSourceFinset_le_three_of_forbidden_configurations
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno3 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 3)
    (hno211 : ¬ HasTwoOneOneConfiguration G)
    (hno220 : ¬ HasTwoTwoZeroConfiguration G)
    (A : DirectionEndpointAssignment G) (y : DegreeThreeVertex G) :
    (directionSourceFinset G A y).card ≤ 3 := by
  apply card_directionSourceFinset_le_three_of_forbidden_configurations_at
    G hdeg hno3 A y
  · intro h
    exact hno211 ⟨y.1, h⟩
  · intro h
    exact hno220 ⟨y.1, h⟩

/-- End-to-end Section 3 counting contradiction, conditional exactly on the
three reducible-configuration conclusions proved earlier in the paper:
there is no `3`-chain, no `(2,1,1)` configuration, and no `(2,2,0)`
configuration.  No triangle or girth assumption is used. -/
theorem not_maximumAverageDegreeLT_twelve_five_of_forbidden_sectionThree_configurations
    (hEdge : G.edgeFinset.Nonempty)
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G)
    (hno3 : ∀ {u v : V} (p : G.Walk u v), ¬ IsKChain G p 3)
    (hno211 : ¬ HasTwoOneOneConfiguration G)
    (hno220 : ¬ HasTwoTwoZeroConfiguration G) :
    ¬ MaximumAverageDegreeLT G 12 5 := by
  apply
    not_maximumAverageDegreeLT_twelve_five_of_no_three_chain_and_direction_bound
      G hEdge hmin hsub hno3
  intro y
  apply card_directionSourceFinset_le_three_of_forbidden_configurations G
    (A := directionEndpointAssignmentOfIsSubcubic G hmin hsub hno3)
    (y := y) _ hno3 hno211 hno220
  intro v hv
  have hlo := hmin v hv
  have hhi := hsub v
  simp only [IsTwoVertex, IsThreeVertex]
  omega

end Finite

end

end LeanCo.PackingEdgeColoring
