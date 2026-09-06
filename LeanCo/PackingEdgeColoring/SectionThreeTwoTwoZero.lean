import LeanCo.PackingEdgeColoring.SectionThreeEasyOuter

/-!
# The Section 3 `(2,2,0)` reduction

This file formalizes Lemma 3.6 of Kim--Liu--Xu.  The local configuration
is the honest graph-theoretic one from `SectionThreeStructure`: in
particular, no girth assumption or tacit distinctness of remote thread
endpoints is used.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-! ## A sharp form of the five-blocker argument -/

/-- The induced colour carried by an active blocker. -/
noncomputable def activeBlockerColour {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet)
    (f : {f : G.edgeSet // f ∈ activeInducedBlockerEdgesOn G D colour e}) :
    Fin k :=
  Classical.choose (Option.ne_none_iff_exists'.mp
    ((mem_activeInducedBlockerEdgesOn G D colour e f.1).mp f.2).2.2.2)

@[simp] theorem colour_activeBlockerColour {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet)
    (f : {f : G.edgeSet // f ∈ activeInducedBlockerEdgesOn G D colour e}) :
    colour f.1 = some (activeBlockerColour G D colour e f) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.mp
    ((mem_activeInducedBlockerEdgesOn G D colour e f.1).mp f.2).2.2.2)

/-- If every induced colour is blocked and there are at most `k` active
blocker edges, the active blockers carry pairwise distinct induced colours.
This is the equality case of the blocker pigeonhole argument used in the
last case of Lemma 3.6. -/
theorem activeBlockerColour_injective_of_no_available {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet)
    (hnone : ∀ i : Fin k, ¬ ColorAvailableOn G D colour e (some i))
    (hcard : (activeInducedBlockerEdgesOn G D colour e).card ≤ k) :
    Function.Injective (activeBlockerColour G D colour e) := by
  let A := {f : G.edgeSet // f ∈ activeInducedBlockerEdgesOn G D colour e}
  let pick : A → Fin k := activeBlockerColour G D colour e
  have hsurj : Function.Surjective pick := by
    intro i
    have hi : i ∈ blockedInducedColorsOn G D colour e :=
      (mem_blockedInducedColorsOn G D colour e i).mpr (hnone i)
    obtain ⟨f, hf, hfc⟩ :=
      exists_blocker_of_mem_blockedInducedColorsOn G D colour e hi
    have hfactive : f ∈ activeInducedBlockerEdgesOn G D colour e := by
      apply (mem_activeInducedBlockerEdgesOn G D colour e f).mpr
      have hf' := (mem_inducedBlockerEdgesOn G D colour e f).mp hf
      exact ⟨hf'.1, hf'.2.1, hf'.2.2, by simp [hfc]⟩
    refine ⟨⟨f, hfactive⟩, ?_⟩
    apply Option.some.inj
    exact (colour_activeBlockerColour G D colour e ⟨f, hfactive⟩).symm.trans hfc
  have hAcard : Fintype.card A =
      (activeInducedBlockerEdgesOn G D colour e).card := by
    simpa [A] using
      (Fintype.card_coe (activeInducedBlockerEdgesOn G D colour e))
  have hEq : Fintype.card A = Fintype.card (Fin k) := by
    apply le_antisymm
    · simpa [hAcard] using hcard
    · exact Fintype.card_le_of_surjective pick hsurj
  exact ((Fintype.bijective_iff_surjective_and_card pick).mpr
    ⟨hsurj, hEq⟩).1

/-- Concrete edge-facing consequence of the preceding equality case. -/
theorem active_blockers_have_distinct_colours_of_no_available {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e f g : G.edgeSet)
    (hnone : ∀ i : Fin k, ¬ ColorAvailableOn G D colour e (some i))
    (hcard : (activeInducedBlockerEdgesOn G D colour e).card ≤ k)
    (hf : f ∈ activeInducedBlockerEdgesOn G D colour e)
    (hg : g ∈ activeInducedBlockerEdgesOn G D colour e)
    (hfg : f ≠ g) : colour f ≠ colour g := by
  intro heq
  have hsome : some (activeBlockerColour G D colour e ⟨f, hf⟩) =
      some (activeBlockerColour G D colour e ⟨g, hg⟩) := by
    rw [← colour_activeBlockerColour G D colour e ⟨f, hf⟩,
      ← colour_activeBlockerColour G D colour e ⟨g, hg⟩]
    exact heq
  have hcol := Option.some.inj hsome
  have hsub := activeBlockerColour_injective_of_no_available G D colour e
    hnone hcard hcol
  exact hfg (congrArg Subtype.val hsub)

/-! ## Exact local structure -/

/-- Three displayed, pairwise distinct neighbors exhaust the neighborhood
of a degree-three vertex. -/
theorem neighborFinset_eq_triple_of_isThreeVertex
    {u a b c : V} (hu : IsThreeVertex G u)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.neighborFinset u = {a, b, c} := by
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hu
  have hsubset : ({a, b, c} : Finset V) ⊆ G.neighborFinset u := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hza | hzb | hzc
    · subst z
      exact (G.mem_neighborFinset u a).mpr hua
    · subst z
      exact (G.mem_neighborFinset u b).mpr hub
    · subst z
      exact (G.mem_neighborFinset u c).mpr huc
  have htriple : ({a, b, c} : Finset V).card = 3 := by
    simp [hab, hac, hbc]
  exact (Finset.eq_of_subset_of_card_le hsubset (by omega)).symm

/-- A neighbor of the center of a displayed `(2,2,0)` configuration is
one of its three displayed branch vertices. -/
theorem eq_left_or_right_or_zero_of_adj_center
    {u a b c z : V} (hu : IsThreeVertex G u)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (huz : G.Adj u z) : z = a ∨ z = b ∨ z = c := by
  have hz : z ∈ G.neighborFinset u :=
    (G.mem_neighborFinset u z).mpr huz
  rw [neighborFinset_eq_triple_of_isThreeVertex G hu hua hub huc hab hac hbc]
    at hz
  simpa using hz

/-- An edge incident with the degree-three center is one of its three
displayed incident edges. -/
theorem edge_eq_one_of_three_of_incident_three
    {u a b c : V} (hu : IsThreeVertex G u)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : G.edgeSet) (huf : u ∈ (f : Sym2 V)) :
    (f : Sym2 V) = s(u, a) ∨ (f : Sym2 V) = s(u, b) ∨
      (f : Sym2 V) = s(u, c) := by
  obtain ⟨z, hfz⟩ := Sym2.mem_iff_exists.mp huf
  have huz : G.Adj u z := by
    have hfG := f.2
    rw [hfz] at hfG
    simpa using hfG
  rcases eq_left_or_right_or_zero_of_adj_center G hu hua hub huc hab hac hbc huz
      with hza | hzb | hzc
  · subst z
    exact Or.inl hfz
  · subst z
    exact Or.inr (Or.inl hfz)
  · subst z
    exact Or.inr (Or.inr hfz)

/-- The two outer edges of a genuine two-thread are distinct. -/
theorem twoThread_outer_edges_ne
    {u a x z : V} (hua : G.Adj u a) (hax : G.Adj a x)
    (hxz : G.Adj x z)
    (hxu : x ≠ u) (hza : z ≠ a) :
    (⟨s(u, a), hua⟩ : G.edgeSet) ≠
      (⟨s(x, z), hxz⟩ : G.edgeSet) := by
  intro hEq
  have hval : s(u, a) = s(x, z) := congrArg Subtype.val hEq
  simp only [Sym2.eq_iff] at hval
  rcases hval with h | h
  · exact hxu h.1.symm
  · exact hax.ne h.2

/-- Local geometric neighborhood of the first outer edge in a displayed
`(2,2,0)` configuration after the middle edge has been deleted.  Every
remaining edge at induced distance at most two is the far outer edge, an
edge at the second degree-two branch vertex, or an edge at the zero-branch
vertex. -/
theorem activeBlockers_leftOuter_subset_twoTwoZero
    {u a x z b c : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hxu : x ≠ u) (hza : z ≠ a)
    (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor 5}
    (hD : ∀ f ∈ D, f ≠ (⟨s(a, x), hax⟩ : G.edgeSet)) :
    activeInducedBlockerEdgesOn G D colour
        (⟨s(u, a), hua⟩ : G.edgeSet) ⊆
      insert (⟨s(x, z), hxz⟩ : G.edgeSet)
        (incidentEdgeFinset G b ∪ incidentEdgeFinset G c) := by
  classical
  intro f hf
  have hf' := (mem_activeInducedBlockerEdgesOn G D colour
    (⟨s(u, a), hua⟩ : G.edgeSet) f).mp hf
  have hfe : f ≠ (⟨s(a, x), hax⟩ : G.edgeSet) := hD f hf'.1
  have hfleft : f ≠ (⟨s(u, a), hua⟩ : G.edgeSet) := hf'.2.1
  have putAtCenter (huf : u ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G b ∪ incidentEdgeFinset G c := by
    rcases edge_eq_one_of_three_of_incident_three G hu hua hub huc hab hac hbc
        f huf with hfa | hfb | hfc
    · exfalso
      apply hfleft
      exact Subtype.ext hfa
    · apply Finset.mem_union_left
      apply (mem_incidentEdgeFinset (G := G)).mpr
      rw [hfb]
      simp
    · apply Finset.mem_union_right
      apply (mem_incidentEdgeFinset (G := G)).mpr
      rw [hfc]
      simp
  have putAtA (haf : a ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G ha hua.symm hax
        hxu.symm f haf with hfl | hfm
    · exact hfleft (Subtype.ext (by simpa [Sym2.eq_swap] using hfl))
    · exact hfe (Subtype.ext hfm)
  by_cases hdisj : EndpointDisjoint G
      (⟨s(u, a), hua⟩ : G.edgeSet) f
  · have hcross : HasCrossEdge G (⟨s(u, a), hua⟩ : G.edgeSet) f := by
      by_contra hn
      exact hf'.2.2.1 ⟨hdisj, hn⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := hcross
    have hp' : p = u ∨ p = a := by simpa using hp
    rcases hp' with hpu | hpa
    · have huq : G.Adj u q := by simpa [hpu] using hpq
      rcases eq_left_or_right_or_zero_of_adj_center G hu hua hub huc
          hab hac hbc huq with hqa | hqb | hqc
      · exact False.elim (putAtA (hqa ▸ hq))
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        left
        exact (mem_incidentEdgeFinset (G := G)).mpr (hqb ▸ hq)
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_union.mpr
        right
        exact (mem_incidentEdgeFinset (G := G)).mpr (hqc ▸ hq)
    · have haq : G.Adj a q := by simpa [hpa] using hpq
      have hqN : q ∈ G.neighborFinset a :=
        (G.mem_neighborFinset a q).mpr haq
      rw [neighborFinset_eq_pair_of_isTwoVertex G ha hua.symm hax hxu.symm] at hqN
      have hq' : q = u ∨ q = x := by simpa using hqN
      rcases hq' with hqu | hqx
      · exact Finset.mem_insert.mpr (Or.inr (putAtCenter (hqu ▸ hq)))
      · rcases edge_eq_left_or_right_of_incident_two G hx hax.symm hxz
            hza.symm f (hqx ▸ hq) with hfm | hfr
        · exact False.elim (hfe (Subtype.ext (by
              simpa [Sym2.eq_swap] using hfm)))
        · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hfr))
  · have hshared : ∃ p, p ∈ (s(u, a) : Sym2 V) ∧ p ∈ (f : Sym2 V) := by
      by_contra hn
      apply hdisj
      intro p hp hpf
      exact hn ⟨p, hp, hpf⟩
    obtain ⟨p, hp, hpf⟩ := hshared
    have hp' : p = u ∨ p = a := by simpa using hp
    rcases hp' with hpu | hpa
    · exact Finset.mem_insert.mpr (Or.inr (putAtCenter (hpu ▸ hpf)))
    · exact False.elim (putAtA (hpa ▸ hpf))

/-- If the first edge of the second two-thread is matching-coloured, the
left outer edge has at most five active induced blockers. -/
theorem card_activeBlockers_leftOuter_le_five_of_second_matching
    {u a x z b c : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hc : IsThreeVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hxu : x ≠ u) (hza : z ≠ a)
    (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor 5}
    (hD : ∀ f ∈ D, f ≠ (⟨s(a, x), hax⟩ : G.edgeSet))
    (hBnone : colour (⟨s(u, b), hub⟩ : G.edgeSet) = none) :
    (activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet)).card ≤ 5 := by
  classical
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  let S : Finset G.edgeSet :=
    insert R (incidentEdgeFinset G b ∪ incidentEdgeFinset G c)
  have hsub : activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet) ⊆ S := by
    simpa [S, R] using activeBlockers_leftOuter_subset_twoTwoZero G hu ha hx
      hua hax hxz hxu hza hub huc hab hac hbc hD
  have hsubErase : activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet) ⊆ S.erase B := by
    intro f hf
    apply Finset.mem_erase.mpr
    refine ⟨?_, hsub hf⟩
    intro hfb
    subst f
    exact ((mem_activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet) B).mp hf).2.2.2 hBnone
  have hBmem : B ∈ S := by
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_union.mpr
    left
    apply (mem_incidentEdgeFinset (G := G)).mpr
    simp [B]
  have hScard : S.card ≤ 6 := by
    have hins : S.card ≤
        (incidentEdgeFinset G b ∪ incidentEdgeFinset G c).card + 1 :=
      Finset.card_insert_le _ _
    have hunion : (incidentEdgeFinset G b ∪ incidentEdgeFinset G c).card ≤
        (incidentEdgeFinset G b).card + (incidentEdgeFinset G c).card :=
      Finset.card_union_le _ _
    rw [card_incidentEdgeFinset G b, card_incidentEdgeFinset G c,
      hb, hc] at hunion
    omega
  have herase : (S.erase B).card + 1 = S.card := by
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨B, hBmem⟩
    rw [Finset.card_erase_of_mem hBmem]
    omega
  exact (Finset.card_le_card hsubErase).trans (by omega)

/-! ## Comparing the three local radius-two neighborhoods -/

/-- Apart from the far outer edge `x-z`, every retained edge close to
`u-a` is also close to `u-b`.  This is the precise geometric reason that
the colour of `u-b` may be moved to `u-a`. -/
theorem leftOuter_close_imp_rightOuter_or_secondFirst_close
    {u a x z b : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z) (hub : G.Adj u b)
    {D : Set G.edgeSet}
    (hD : ∀ f ∈ D, f ≠ (⟨s(a, x), hax⟩ : G.edgeSet))
    {f : G.edgeSet} (hfD : f ∈ D)
    (hfL : f ≠ (⟨s(u, a), hua⟩ : G.edgeSet))
    (hclose : ¬ InducedSeparated G (⟨s(u, a), hua⟩ : G.edgeSet) f) :
    f = (⟨s(x, z), hxz⟩ : G.edgeSet) ∨
      ¬ InducedSeparated G (⟨s(u, b), hub⟩ : G.edgeSet) f := by
  have hfe : f ≠ (⟨s(a, x), hax⟩ : G.edgeSet) := hD f hfD
  have closeSecondOfCenter (huf : u ∈ (f : Sym2 V)) :
      ¬ InducedSeparated G (⟨s(u, b), hub⟩ : G.edgeSet) f := by
    intro hsep
    exact hsep.1 u (by simp) huf
  have impossibleAtA (haf : a ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G ha hua.symm hax hux
        f haf with hfl | hfm
    · exact hfL (Subtype.ext (by simpa only [Sym2.eq_swap] using hfl))
    · exact hfe (Subtype.ext hfm)
  by_cases hdisj : EndpointDisjoint G
      (⟨s(u, a), hua⟩ : G.edgeSet) f
  · have hcross : HasCrossEdge G (⟨s(u, a), hua⟩ : G.edgeSet) f := by
      by_contra hn
      exact hclose ⟨hdisj, hn⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := hcross
    have hp' : p = u ∨ p = a := by simpa using hp
    rcases hp' with hpu | hpa
    · right
      intro hsep
      apply hsep.2
      exact ⟨u, by simp, q, hq, by simpa [hpu] using hpq⟩
    · have haq : G.Adj a q := by simpa [hpa] using hpq
      have hqN : q ∈ G.neighborFinset a :=
        (G.mem_neighborFinset a q).mpr haq
      rw [neighborFinset_eq_pair_of_isTwoVertex G ha hua.symm hax hux] at hqN
      have hq' : q = u ∨ q = x := by simpa using hqN
      rcases hq' with hqu | hqx
      · exact Or.inr (closeSecondOfCenter (hqu ▸ hq))
      · rcases edge_eq_left_or_right_of_incident_two G hx hax.symm hxz
            haz f (hqx ▸ hq) with hfm | hfr
        · exact False.elim (hfe (Subtype.ext (by
              simpa only [Sym2.eq_swap] using hfm)))
        · exact Or.inl (Subtype.ext hfr)
  · have hshared : ∃ p, p ∈ (s(u, a) : Sym2 V) ∧ p ∈ (f : Sym2 V) := by
      by_contra hn
      apply hdisj
      intro p hp hpf
      exact hn ⟨p, hp, hpf⟩
    obtain ⟨p, hp, hpf⟩ := hshared
    have hp' : p = u ∨ p = a := by simpa using hp
    rcases hp' with hpu | hpa
    · exact Or.inr (closeSecondOfCenter (hpu ▸ hpf))
    · exact False.elim (impossibleAtA (hpa ▸ hpf))

/-- Symmetrically, apart from `y-w`, every retained edge close to `u-b`
is close to `u-a`. -/
theorem secondFirst_close_imp_secondOuter_or_leftOuter_close
    {u a b y w : V}
    (hb : IsTwoVertex G b) (hy : IsTwoVertex G y)
    (hua : G.Adj u a) (hub : G.Adj u b) (hby : G.Adj b y)
    (hyw : G.Adj y w) (huy : u ≠ y) (hbw : b ≠ w)
    {D : Set G.edgeSet}
    (hD : ∀ f ∈ D, f ≠ (⟨s(b, y), hby⟩ : G.edgeSet))
    {f : G.edgeSet} (hfD : f ∈ D)
    (hfB : f ≠ (⟨s(u, b), hub⟩ : G.edgeSet))
    (hclose : ¬ InducedSeparated G (⟨s(u, b), hub⟩ : G.edgeSet) f) :
    f = (⟨s(y, w), hyw⟩ : G.edgeSet) ∨
      ¬ InducedSeparated G (⟨s(u, a), hua⟩ : G.edgeSet) f := by
  -- This is the preceding statement with the two branches renamed.
  simpa only [Sym2.eq_swap] using
    (leftOuter_close_imp_rightOuter_or_secondFirst_close G hb hy hub hby hyw
      huy hbw hua hD hfD hfB hclose)

/-- Apart from the old left outer edge and edges at the zero-branch
neighbor `c`, every retained edge close to `u-b` is also close to the
middle edge `b-y`.  This controls the paper's matching-colour shift along
the second two-thread. -/
theorem secondFirst_close_imp_left_or_zeroIncident_or_secondMiddle_close
    {u a x b y c : V}
    (hu : IsThreeVertex G u) (ha : IsTwoVertex G a)
    (hb : IsTwoVertex G b)
    (hua : G.Adj u a) (hax : G.Adj a x)
    (hub : G.Adj u b) (hby : G.Adj b y)
    (huc : G.Adj u c)
    (hux : u ≠ x) (huy : u ≠ y)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {D : Set G.edgeSet}
    (hDelete : ∀ f ∈ D, f ≠ (⟨s(a, x), hax⟩ : G.edgeSet))
    {f : G.edgeSet}
    (hfmem : f ∈ D)
    (hfB : f ≠ (⟨s(u, b), hub⟩ : G.edgeSet))
    (hfD : f ≠ (⟨s(b, y), hby⟩ : G.edgeSet))
    (hclose : ¬ InducedSeparated G (⟨s(u, b), hub⟩ : G.edgeSet) f) :
    f = (⟨s(u, a), hua⟩ : G.edgeSet) ∨
      f ∈ incidentEdgeFinset G c ∨
      ¬ InducedSeparated G (⟨s(b, y), hby⟩ : G.edgeSet) f := by
  have closeMiddleOfAtU (huf : u ∈ (f : Sym2 V)) :
      ¬ InducedSeparated G (⟨s(b, y), hby⟩ : G.edgeSet) f := by
    intro hsep
    apply hsep.2
    exact ⟨b, by simp, u, huf, hub.symm⟩
  have closeMiddleOfAtB (hbf : b ∈ (f : Sym2 V)) :
      ¬ InducedSeparated G (⟨s(b, y), hby⟩ : G.edgeSet) f := by
    intro hsep
    exact hsep.1 b (by simp) hbf
  by_cases hdisj : EndpointDisjoint G
      (⟨s(u, b), hub⟩ : G.edgeSet) f
  · have hcross : HasCrossEdge G (⟨s(u, b), hub⟩ : G.edgeSet) f := by
      by_contra hn
      exact hclose ⟨hdisj, hn⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := hcross
    have hp' : p = u ∨ p = b := by simpa using hp
    rcases hp' with hpu | hpb
    · have huq : G.Adj u q := by simpa [hpu] using hpq
      rcases eq_left_or_right_or_zero_of_adj_center G hu hua hub huc
          hab hac hbc huq with hqa | hqb | hqc
      · left
        rcases edge_eq_left_or_right_of_incident_two G ha hua.symm hax hux
            f (hqa ▸ hq) with hfl | hfm
        · exact Subtype.ext (by simpa only [Sym2.eq_swap] using hfl)
        · exact False.elim ((hDelete f hfmem) (Subtype.ext hfm))
      · exact Or.inr (Or.inr (closeMiddleOfAtB (hqb ▸ hq)))
      · exact Or.inr (Or.inl
          ((mem_incidentEdgeFinset (G := G)).mpr (hqc ▸ hq)))
    · have hbq : G.Adj b q := by simpa [hpb] using hpq
      have hqN : q ∈ G.neighborFinset b :=
        (G.mem_neighborFinset b q).mpr hbq
      rw [neighborFinset_eq_pair_of_isTwoVertex G hb hub.symm hby
        huy] at hqN
      have hq' : q = u ∨ q = y := by simpa using hqN
      rcases hq' with hqu | hqy
      · exact Or.inr (Or.inr (closeMiddleOfAtU (hqu ▸ hq)))
      · right
        right
        intro hsep
        exact hsep.1 y (by simp) (hqy ▸ hq)
  · have hshared : ∃ p, p ∈ (s(u, b) : Sym2 V) ∧ p ∈ (f : Sym2 V) := by
      by_contra hn
      apply hdisj
      intro p hp hpf
      exact hn ⟨p, hp, hpf⟩
    obtain ⟨p, hp, hpf⟩ := hshared
    have hp' : p = u ∨ p = b := by simpa using hp
    rcases hp' with hpu | hpb
    · exact Or.inr (Or.inr (closeMiddleOfAtU (hpu ▸ hpf)))
    · exact Or.inr (Or.inr (closeMiddleOfAtB (hpb ▸ hpf)))

/-! ## The Condition-I influence domain -/

/-- If changes are confined to the first two edges of each of the two
displayed two-threads, every affected degree-two vertex has a degree-two
neighbor.  This is the only special Condition-I fact needed by all
recolouring cases of Lemma 3.6.

The proof deliberately treats a vertex adjacent to the degree-three center
separately: exact degree three forces it to be one of `a,b,c`; the zero
branch `c` is then eliminated by its degree. -/
theorem exists_adjacent_two_of_paletteAffected_twoTwoZero_support
    {u a x b y c z : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hy : IsTwoVertex G y)
    (hc : IsThreeVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x)
    (hub : G.Adj u b) (hby : G.Adj b y)
    (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hz : IsTwoVertex G z)
    (haffect : PaletteAffectedBy G
      ({(⟨s(u, a), hua⟩ : G.edgeSet),
        (⟨s(a, x), hax⟩ : G.edgeSet),
        (⟨s(u, b), hub⟩ : G.edgeSet),
        (⟨s(b, y), hby⟩ : G.edgeSet)} : Set G.edgeSet) z) :
    ∃ q : V, G.Adj z q ∧ IsTwoVertex G q := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, he, v, hve, hzv⟩ := haffect
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with he | he | he | he
  · subst e
    have hv : v = u ∨ v = a := by simpa using hve
    rcases hzv with hzv | hzv
    · subst z
      rcases hv with hv | hv
      · subst v
        exact ⟨a, hua, ha⟩
      · subst v
        exact ⟨x, hax, hx⟩
    · rcases hv with hv | hv
      · subst v
        rcases eq_left_or_right_or_zero_of_adj_center G hu hua hub huc
            hab hac hbc hzv.symm with hza | hzb | hzc
        · subst z
          exact ⟨x, hax, hx⟩
        · subst z
          exact ⟨y, hby, hy⟩
        · have hzTwo : G.degree c = 2 := by
            have hzTwo0 : G.degree z = 2 := hz
            rw [hzc] at hzTwo0
            exact hzTwo0
          have hcThree : G.degree c = 3 := by exact hc
          omega
      · subst v
        exact ⟨a, hzv, ha⟩
  · subst e
    have hv : v = a ∨ v = x := by simpa using hve
    rcases hzv with hzv | hzv
    · subst z
      rcases hv with hv | hv
      · subst v
        exact ⟨x, hax, hx⟩
      · subst v
        exact ⟨a, hax.symm, ha⟩
    · rcases hv with hv | hv
      · subst v
        exact ⟨a, hzv, ha⟩
      · subst v
        exact ⟨x, hzv, hx⟩
  · subst e
    have hv : v = u ∨ v = b := by simpa using hve
    rcases hzv with hzv | hzv
    · subst z
      rcases hv with hv | hv
      · subst v
        exact ⟨b, hub, hb⟩
      · subst v
        exact ⟨y, hby, hy⟩
    · rcases hv with hv | hv
      · subst v
        rcases eq_left_or_right_or_zero_of_adj_center G hu hua hub huc
            hab hac hbc hzv.symm with hza | hzb | hzc
        · subst z
          exact ⟨x, hax, hx⟩
        · subst z
          exact ⟨y, hby, hy⟩
        · have hzTwo : G.degree c = 2 := by
            have hzTwo0 : G.degree z = 2 := hz
            rw [hzc] at hzTwo0
            exact hzTwo0
          have hcThree : G.degree c = 3 := by exact hc
          omega
      · subst v
        exact ⟨b, hzv, hb⟩
  · subst e
    have hv : v = b ∨ v = y := by simpa using hve
    rcases hzv with hzv | hzv
    · subst z
      rcases hv with hv | hv
      · subst v
        exact ⟨y, hby, hy⟩
      · subst v
        exact ⟨b, hby.symm, hb⟩
    · rcases hv with hv | hv
      · subst v
        exact ⟨b, hzv, hb⟩
      · subst v
        exact ⟨y, hzv, hy⟩

/-- Consequently any recolouring supported on those four thread edges
preserves Condition I once the old ambient colouring already has it. -/
theorem conditionI_of_agreeOff_twoTwoZero_support
    (hsub : IsSubcubic G)
    {u a x b y c : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hy : IsTwoVertex G y)
    (hc : IsThreeVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x)
    (hub : G.Adj u b) (hby : G.Adj b y)
    (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {old new : G.edgeSet → OneTwoColor 5}
    (hold : ConditionI G old)
    (hagree : ColoringsAgreeOff G
      ({(⟨s(u, a), hua⟩ : G.edgeSet),
        (⟨s(a, x), hax⟩ : G.edgeSet),
        (⟨s(u, b), hub⟩ : G.edgeSet),
        (⟨s(b, y), hby⟩ : G.edgeSet)} : Set G.edgeSet) old new) :
    ConditionI G new := by
  apply ConditionI.of_agreeOff G hold hagree
  intro z hz haffect hmatch
  obtain ⟨q, hzq, hq⟩ :=
    exists_adjacent_two_of_paletteAffected_twoTwoZero_support G hu ha hx hb hy hc
      hua hax hub hby huc hab hac hbc hz haffect
  exact paletteCondition_at_of_adjacent_two G hsub hz hzq hq hmatch

/-! ## Separation across the two displayed branches -/

/-- If the two outer edges of the deleted first two-thread were
induced-separated before the middle edge was restored, then the first edge
of the second two-thread is induced-separated from the far outer edge of the
first thread in the ambient graph.

This is the separation needed when the common outer colour is moved from
`u-a` to `u-b`.  The proof uses only the exact degree-two neighborhoods and
the fact that the remote endpoints have degree three.  In particular there
is no girth assumption. -/
theorem secondFirst_inducedSeparated_rightOuter_of_deleted_outer_separated
    {u a x z b y : V}
    (hx : IsTwoVertex G x) (hb : IsTwoVertex G b)
    (hy : IsTwoVertex G y) (hz : IsThreeVertex G z)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (hby : G.Adj b y)
    (hux : u ≠ x) (haz : a ≠ z)
    (hab : a ≠ b) (huy : u ≠ y)
    (hsep : InducedSeparated (deleteMiddleEdge G hax)
      (⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩ :
        (deleteMiddleEdge G hax).edgeSet)
      (⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩ :
        (deleteMiddleEdge G hax).edgeSet)) :
    InducedSeparated G
      (⟨s(u, b), hub⟩ : G.edgeSet)
      (⟨s(x, z), hxz⟩ : G.edgeSet) := by
  have hsepUZ : u ≠ z ∧ ¬ (deleteMiddleEdge G hax).Adj u z :=
    (inducedSeparated_iff_forall_endpoints (deleteMiddleEdge G hax)).mp hsep
      u (by simp) z (by simp)
  have hnuz : ¬ G.Adj u z := by
    intro huz
    rcases deleted_middle_endpoint_pair G hax huz hsepUZ.2 with h | h
    · exact hua.ne h.1
    · exact hux h.1
  have hnux : ¬ G.Adj u x := by
    intro huxAdj
    have huN : u ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x u).mpr huxAdj.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz haz] at huN
    have hu : u = a ∨ u = z := by simpa using huN
    exact hu.elim hua.ne hsepUZ.1
  have hbx : b ≠ x := by
    intro hEq
    subst b
    exact hnux hub
  have hbz : b ≠ z := by
    intro hEq
    subst b
    have htwo : G.degree z = 2 := hb
    have hthree : G.degree z = 3 := hz
    omega
  have hnbx : ¬ G.Adj b x := by
    intro hbxAdj
    have hbN : b ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x b).mpr hbxAdj.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz haz] at hbN
    have hb' : b = a ∨ b = z := by simpa using hbN
    exact hb'.elim hab.symm hbz
  have hnbz : ¬ G.Adj b z := by
    intro hbzAdj
    have hzN : z ∈ G.neighborFinset b :=
      (G.mem_neighborFinset b z).mpr hbzAdj
    rw [neighborFinset_eq_pair_of_isTwoVertex G hb hub.symm hby huy] at hzN
    have hz' : z = u ∨ z = y := by simpa using hzN
    rcases hz' with hzu | hzy
    · exact hsepUZ.1 hzu.symm
    · subst z
      have htwo : G.degree y = 2 := hy
      have hthree : G.degree y = 3 := hz
      omega
  apply (inducedSeparated_iff_forall_endpoints G).mpr
  intro p hp q hq
  have hp' : p = u ∨ p = b := by simpa using hp
  have hq' : q = x ∨ q = z := by simpa using hq
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
  · exact ⟨hux, hnux⟩
  · exact ⟨hsepUZ.1, hnuz⟩
  · exact ⟨hbx, hnbx⟩
  · exact ⟨hbz, hnbz⟩

/-! ## Making an outer edge matching-coloured -/

/-- If no other edge at the left terminal carries the matching colour,
then the left outer edge can be recoloured matching.  At the degree-two
vertex `a` there is no other retained edge. -/
theorem matching_available_leftOuter_of_no_terminal_matching
    {u a x : V} (ha : IsTwoVertex G a)
    (hua : G.Adj u a) (hax : G.Adj a x) (hux : u ≠ x)
    (colour : G.edgeSet → OneTwoColor 5)
    (hterminal : ∀ f : G.edgeSet,
      f ∈ RetainedEdges (deleteMiddleEdge G hax) G →
      f ∈ incidentEdgeFinset G u →
      f ≠ (⟨s(u, a), hua⟩ : G.edgeSet) → colour f ≠ none) :
    ColorAvailableOn G (RetainedEdges (deleteMiddleEdge G hax) G) colour
      (⟨s(u, a), hua⟩ : G.edgeSet) none := by
  apply (colorAvailableOn_none_iff G _ colour _).mpr
  intro f hfD hfL hfnone
  intro v hvL hvf
  have hv : v = u ∨ v = a := by simpa using hvL
  rcases hv with hv | hv
  · have hfu : f ∈ incidentEdgeFinset G u :=
      (mem_incidentEdgeFinset (G := G)).mpr (by simpa [hv] using hvf)
    exact (hterminal f hfD hfu hfL) hfnone
  · have hfEq := retained_edge_eq_leftOuter_of_incident G ha hua hax hux
      f hfD (by simpa [hv] using hvf)
    exact hfL hfEq

/-- Right-handed version of
`matching_available_leftOuter_of_no_terminal_matching`. -/
theorem matching_available_rightOuter_of_no_terminal_matching
    {a x z : V} (hx : IsTwoVertex G x)
    (hax : G.Adj a x) (hxz : G.Adj x z) (haz : a ≠ z)
    (colour : G.edgeSet → OneTwoColor 5)
    (hterminal : ∀ f : G.edgeSet,
      f ∈ RetainedEdges (deleteMiddleEdge G hax) G →
      f ∈ incidentEdgeFinset G z →
      f ≠ (⟨s(x, z), hxz⟩ : G.edgeSet) → colour f ≠ none) :
    ColorAvailableOn G (RetainedEdges (deleteMiddleEdge G hax) G) colour
      (⟨s(x, z), hxz⟩ : G.edgeSet) none := by
  apply (colorAvailableOn_none_iff G _ colour _).mpr
  intro f hfD hfR hfnone
  intro v hvR hvf
  have hv : v = x ∨ v = z := by simpa using hvR
  rcases hv with hv | hv
  · have hfEq := retained_edge_eq_rightOuter_of_incident G hx hax hxz haz
      f hfD (by simpa [hv] using hvf)
    exact hfR hfEq
  · have hfz : f ∈ incidentEdgeFinset G z :=
      (mem_incidentEdgeFinset (G := G)).mpr (by simpa [hv] using hvf)
    exact (hterminal f hfD hfz hfR) hfnone

/-- The same five-blocker bound when the zero-branch edge, rather than the
second-thread edge, carries the matching colour. -/
theorem card_activeBlockers_leftOuter_le_five_of_zero_matching
    {u a x z b c : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hc : IsThreeVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hxu : x ≠ u) (hza : z ≠ a)
    (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor 5}
    (hD : ∀ f ∈ D, f ≠ (⟨s(a, x), hax⟩ : G.edgeSet))
    (hCnone : colour (⟨s(u, c), huc⟩ : G.edgeSet) = none) :
    (activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet)).card ≤ 5 := by
  classical
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let C : G.edgeSet := ⟨s(u, c), huc⟩
  let S : Finset G.edgeSet :=
    insert R (incidentEdgeFinset G b ∪ incidentEdgeFinset G c)
  have hsub : activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet) ⊆ S := by
    simpa [S, R] using activeBlockers_leftOuter_subset_twoTwoZero G hu ha hx
      hua hax hxz hxu hza hub huc hab hac hbc hD
  have hsubErase : activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet) ⊆ S.erase C := by
    intro f hf
    apply Finset.mem_erase.mpr
    refine ⟨?_, hsub hf⟩
    intro hfc
    subst f
    exact ((mem_activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet) C).mp hf).2.2.2 hCnone
  have hCmem : C ∈ S := by
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_union.mpr
    right
    exact (mem_incidentEdgeFinset (G := G)).mpr (by simp [C])
  have hScard : S.card ≤ 6 := by
    have hins : S.card ≤
        (incidentEdgeFinset G b ∪ incidentEdgeFinset G c).card + 1 :=
      Finset.card_insert_le _ _
    have hunion : (incidentEdgeFinset G b ∪ incidentEdgeFinset G c).card ≤
        (incidentEdgeFinset G b).card + (incidentEdgeFinset G c).card :=
      Finset.card_union_le _ _
    rw [card_incidentEdgeFinset G b, card_incidentEdgeFinset G c,
      hb, hc] at hunion
    omega
  have herase : (S.erase C).card + 1 = S.card := by
    rw [Finset.card_erase_of_mem hCmem]
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨C, hCmem⟩
    omega
  exact (Finset.card_le_card hsubErase).trans (by omega)

/-- If both the zero-branch edge and the middle edge of the second
two-thread are matching-coloured, only four possible active blockers of the
left outer edge remain. -/
theorem card_activeBlockers_leftOuter_le_four_of_zero_and_secondMiddle_matching
    {u a x z b y c : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hc : IsThreeVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hxu : x ≠ u) (hza : z ≠ a)
    (hub : G.Adj u b) (hby : G.Adj b y) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor 5}
    (hD : ∀ f ∈ D, f ≠ (⟨s(a, x), hax⟩ : G.edgeSet))
    (hCnone : colour (⟨s(u, c), huc⟩ : G.edgeSet) = none)
    (hMnone : colour (⟨s(b, y), hby⟩ : G.edgeSet) = none) :
    (activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet)).card ≤ 4 := by
  classical
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let C : G.edgeSet := ⟨s(u, c), huc⟩
  let M : G.edgeSet := ⟨s(b, y), hby⟩
  let S : Finset G.edgeSet :=
    insert R (incidentEdgeFinset G b ∪ incidentEdgeFinset G c)
  have hsub : activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet) ⊆ S := by
    simpa [S, R] using activeBlockers_leftOuter_subset_twoTwoZero G hu ha hx
      hua hax hxz hxu hza hub huc hab hac hbc hD
  have hsubErase : activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet) ⊆ (S.erase C).erase M := by
    intro f hf
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hsub hf⟩⟩
    · intro hfM
      subst f
      exact ((mem_activeInducedBlockerEdgesOn G D colour
        (⟨s(u, a), hua⟩ : G.edgeSet) M).mp hf).2.2.2 hMnone
    · intro hfC
      subst f
      exact ((mem_activeInducedBlockerEdgesOn G D colour
        (⟨s(u, a), hua⟩ : G.edgeSet) C).mp hf).2.2.2 hCnone
  have hCmem : C ∈ S := by
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_union.mpr
    right
    exact (mem_incidentEdgeFinset (G := G)).mpr (by simp [C])
  have hMmem : M ∈ S := by
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_union.mpr
    left
    exact (mem_incidentEdgeFinset (G := G)).mpr (by simp [M])
  have hMC : M ≠ C := by
    intro heq
    have hs : s(b, y) = s(u, c) := congrArg Subtype.val heq
    have hbumem : b ∈ (s(u, c) : Sym2 V) := by rw [← hs]; simp
    have hbu : b = u ∨ b = c := by simpa using hbumem
    exact hbu.elim hub.ne.symm hbc
  have hMmemErase : M ∈ S.erase C := Finset.mem_erase.mpr ⟨hMC, hMmem⟩
  have hScard : S.card ≤ 6 := by
    have hins : S.card ≤
        (incidentEdgeFinset G b ∪ incidentEdgeFinset G c).card + 1 :=
      Finset.card_insert_le _ _
    have hunion : (incidentEdgeFinset G b ∪ incidentEdgeFinset G c).card ≤
        (incidentEdgeFinset G b).card + (incidentEdgeFinset G c).card :=
      Finset.card_union_le _ _
    rw [card_incidentEdgeFinset G b, card_incidentEdgeFinset G c,
      hb, hc] at hunion
    omega
  have hcardErase : ((S.erase C).erase M).card + 2 = S.card := by
    have hErasePos : 0 < (S.erase C).card :=
      Finset.card_pos.mpr ⟨M, hMmemErase⟩
    have hEraseLt : (S.erase C).card < S.card :=
      Finset.card_erase_lt_of_mem hCmem
    rw [Finset.card_erase_of_mem hMmemErase,
      Finset.card_erase_of_mem hCmem]
    omega
  exact (Finset.card_le_card hsubErase).trans (by omega)

/-- An edge between two displayed degree-two vertices can receive the
matching colour once its two other incident edges are nonmatching. -/
theorem matching_available_secondMiddle_of_outer_nonmatching
    {u b y w : V}
    (hb : IsTwoVertex G b) (hy : IsTwoVertex G y)
    (hub : G.Adj u b) (hby : G.Adj b y) (hyw : G.Adj y w)
    (huy : u ≠ y) (hbw : b ≠ w)
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor 5)
    (hB : colour (⟨s(u, b), hub⟩ : G.edgeSet) ≠ none)
    (hT : colour (⟨s(y, w), hyw⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G D colour
      (⟨s(b, y), hby⟩ : G.edgeSet) none := by
  apply (colorAvailableOn_none_iff G D colour _).mpr
  intro f hfD hfM hfnone
  intro v hvM hvf
  have hv : v = b ∨ v = y := by simpa using hvM
  rcases hv with hv | hv
  · rcases edge_eq_left_or_right_of_incident_two G hb hub.symm hby huy
        f (by simpa [hv] using hvf) with hfB | hfM'
    · have hfEq : f = (⟨s(u, b), hub⟩ : G.edgeSet) := by
        apply Subtype.ext
        simpa only [Sym2.eq_swap] using hfB
      exact hB (hfEq ▸ hfnone)
    · exact hfM (Subtype.ext hfM')
  · rcases edge_eq_left_or_right_of_incident_two G hy hby.symm hyw hbw
        f (by simpa [hv] using hvf) with hfM' | hfT
    · have hfEq : f = (⟨s(b, y), hby⟩ : G.edgeSet) := by
        apply Subtype.ext
        simpa only [Sym2.eq_swap] using hfM'
      exact hfM hfEq
    · have hfEq : f = (⟨s(y, w), hyw⟩ : G.edgeSet) :=
        Subtype.ext hfT
      exact hT (hfEq ▸ hfnone)

/-- Every displayed edge of the second thread and the zero branch survives
deletion of the first middle edge.  The only potentially delicate overlap
is ruled out by the already valid outer pair in the deleted graph; degree
two/three incompatibility handles the remaining coincidences. -/
theorem other_displayed_edges_mem_deleteMiddleEdge
    {u a x z b y w c : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hy : IsTwoVertex G y)
    (hz : IsThreeVertex G z)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (hby : G.Adj b y) (hyw : G.Adj y w)
    (huc : G.Adj u c)
    (hab : a ≠ b) (hux : u ≠ x) (haz : a ≠ z)
    (huy : u ≠ y) (hbw : b ≠ w)
    (hsep : InducedSeparated (deleteMiddleEdge G hax)
      (⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩ :
        (deleteMiddleEdge G hax).edgeSet)
      (⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩ :
        (deleteMiddleEdge G hax).edgeSet)) :
    (⟨s(u, b), hub⟩ : G.edgeSet) ∈
        RetainedEdges (deleteMiddleEdge G hax) G ∧
      (⟨s(u, c), huc⟩ : G.edgeSet) ∈
        RetainedEdges (deleteMiddleEdge G hax) G ∧
      (⟨s(b, y), hby⟩ : G.edgeSet) ∈
        RetainedEdges (deleteMiddleEdge G hax) G ∧
      (⟨s(y, w), hyw⟩ : G.edgeSet) ∈
        RetainedEdges (deleteMiddleEdge G hax) G := by
  have huz : u ≠ z :=
    ((inducedSeparated_iff_forall_endpoints (deleteMiddleEdge G hax)).mp hsep
      u (by simp) z (by simp)).1
  have hbx : b ≠ x := by
    intro hEq
    subst b
    have huN : u ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x u).mpr hub.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz haz] at huN
    have hu : u = a ∨ u = z := by simpa using huN
    exact hu.elim hua.ne huz
  have hya : y ≠ a := by
    intro hEq
    subst y
    have hbN : b ∈ G.neighborFinset a :=
      (G.mem_neighborFinset a b).mpr hby.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G ha hua.symm hax hux] at hbN
    have hb' : b = u ∨ b = x := by simpa using hbN
    exact hb'.elim hub.ne.symm hbx
  have hyx : y ≠ x := by
    intro hEq
    subst y
    have hbN : b ∈ G.neighborFinset x :=
      (G.mem_neighborFinset x b).mpr hby.symm
    rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz haz] at hbN
    have hb' : b = a ∨ b = z := by simpa using hbN
    rcases hb' with hba | hbz
    · exact hab hba.symm
    · subst b
      have htwo : G.degree z = 2 := hb
      have hthree : G.degree z = 3 := hz
      omega
  have hBne : (⟨s(u, b), hub⟩ : G.edgeSet) ≠
      (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro heq
    have hs : s(u, b) = s(a, x) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hua.ne h.1
    · exact hux h.1
  have hCne : (⟨s(u, c), huc⟩ : G.edgeSet) ≠
      (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro heq
    have hs : s(u, c) = s(a, x) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hua.ne h.1
    · exact hux h.1
  have hDne : (⟨s(b, y), hby⟩ : G.edgeSet) ≠
      (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro heq
    have hs : s(b, y) = s(a, x) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hab h.1.symm
    · exact hbx h.1
  have hTne : (⟨s(y, w), hyw⟩ : G.edgeSet) ≠
      (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro heq
    have hs : s(y, w) = s(a, x) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hya h.1
    · exact hyx h.1
  exact ⟨(mem_retained_deleteMiddleEdge_iff G hax _).mpr hBne,
    (mem_retained_deleteMiddleEdge_iff G hax _).mpr hCne,
    (mem_retained_deleteMiddleEdge_iff G hax _).mpr hDne,
    (mem_retained_deleteMiddleEdge_iff G hax _).mpr hTne⟩

/-- Ambient validity on the retained edges itself rules out a common
induced colour on the two outer edges: the restored middle edge is a cross
edge between them. -/
theorem not_same_induced_outer_of_valid_retained
    {u a x z : V}
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    (colour : G.edgeSet → OneTwoColor 5)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G) colour) :
    ¬ ∃ i : Fin 5,
      colour (⟨s(u, a), hua⟩ : G.edgeSet) = some i ∧
      colour (⟨s(x, z), hxz⟩ : G.edgeSet) = some i := by
  rintro ⟨i, hL, hR⟩
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  have hLD : L ∈ RetainedEdges (deleteMiddleEdge G hax) G := by
    apply (mem_retained_deleteMiddleEdge_iff G hax L).mpr
    exact (middleEdge_ne_leftOuter G hua hax hux).symm
  have hRD : R ∈ RetainedEdges (deleteMiddleEdge G hax) G := by
    apply (mem_retained_deleteMiddleEdge_iff G hax R).mpr
    exact (middleEdge_ne_rightOuter G hax hxz haz).symm
  have hLR : L ≠ R := leftOuter_ne_rightOuter G hua hax hxz hux
  have hp := hvalid L hLD R hRD hLR
  have hsep : InducedSeparated G L R := by
    simpa [L, R, hL, hR, PairCompatible] using hp
  exact hsep.2 ⟨a, by simp [L], x, by simp [R], hax⟩

/-! ## The two colour moves used in the saturated case -/

/-- The common outer induced colour may be moved from `u-a` to `u-b`
provided the far edge `y-w` does not carry that colour. -/
theorem induced_available_secondFirst_of_far_ne_leftColour
    {u a x z b y w : V}
    (hx : IsTwoVertex G x) (hb : IsTwoVertex G b)
    (hy : IsTwoVertex G y) (hz : IsThreeVertex G z)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (hby : G.Adj b y) (hyw : G.Adj y w)
    (hux : u ≠ x) (haz : a ≠ z) (hab : a ≠ b)
    (huy : u ≠ y) (hbw : b ≠ w)
    (base : G.edgeSet → OneTwoColor 5) (alpha : Fin 5)
    (hL : base (⟨s(u, a), hua⟩ : G.edgeSet) = some alpha)
    (hT : base (⟨s(y, w), hyw⟩ : G.edgeSet) ≠ some alpha)
    (hvalidNoR : IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(x, z), hxz⟩ : G.edgeSet)}) base)
    (hsepDeleted : InducedSeparated (deleteMiddleEdge G hax)
      (⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩ :
        (deleteMiddleEdge G hax).edgeSet)
      (⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩ :
        (deleteMiddleEdge G hax).edgeSet)) :
    ColorAvailableOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(u, a), hua⟩ : G.edgeSet)}) base
      (⟨s(u, b), hub⟩ : G.edgeSet) (some alpha) := by
  let D : Set G.edgeSet := RetainedEdges (deleteMiddleEdge G hax) G
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  let T : G.edgeSet := ⟨s(y, w), hyw⟩
  have hLD : L ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax L).mpr
    exact (middleEdge_ne_leftOuter G hua hax hux).symm
  have hsepBR : InducedSeparated G B R := by
    simpa [B, R] using
      secondFirst_inducedSeparated_rightOuter_of_deleted_outer_separated G
        hx hb hy hz hua hax hxz hub hby hux haz hab huy hsepDeleted
  apply (colorAvailableOn_some_iff G _ base B alpha).mpr
  intro f hf fneB hfcolour
  by_cases hfR : f = R
  · subst f
    exact hsepBR
  have hLf : L ≠ f := by
    intro hEq
    exact hf.2 (by simpa [L] using hEq.symm)
  have hp := hvalidNoR L (by simpa [D, R] using ⟨hLD, by
      exact leftOuter_ne_rightOuter G hua hax hxz hux⟩)
    f (by simpa [D, R] using ⟨hf.1, hfR⟩) hLf
  have hsepLf : InducedSeparated G L f := by
    simpa [L, hL, hfcolour, PairCompatible] using hp
  by_contra hsepBf
  let M : G.edgeSet := ⟨s(b, y), hby⟩
  by_cases hfM : f = M
  · subst f
    exact hsepLf.2 ⟨u, by simp [L], b, by simp [M], hub⟩
  have hdelete : ∀ q ∈ D \ {M}, q ≠ M := by
    intro q hq
    exact hq.2
  rcases secondFirst_close_imp_secondOuter_or_leftOuter_close G hb hy hua hub
      hby hyw huy hbw hdelete ⟨hf.1, hfM⟩ fneB hsepBf with hfT | hcloseL
  · apply hT
    simpa [T, hfT] using hfcolour
  · exact hcloseL hsepLf

/-- In the saturated `u-b`-matching case, the colour of `b-y` may be
moved onto `u-b` when the far edge `y-w` has the old common outer colour.
Injectivity of the five active blocker colours is the exact equality-case
argument behind this move. -/
theorem induced_available_secondFirst_of_saturated_blockers
    {u a x z b y w c : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hy : IsTwoVertex G y)
    (hc : IsThreeVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (hby : G.Adj b y) (hyw : G.Adj y w)
    (huc : G.Adj u c)
    (hxu : x ≠ u) (hza : z ≠ a) (huz : u ≠ z)
    (huy : u ≠ y) (hbw : b ≠ w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (base : G.edgeSet → OneTwoColor 5) (alpha gamma : Fin 5)
    (hL : base (⟨s(u, a), hua⟩ : G.edgeSet) = some alpha)
    (hB : base (⟨s(u, b), hub⟩ : G.edgeSet) = none)
    (hM : base (⟨s(b, y), hby⟩ : G.edgeSet) = some gamma)
    (hT : base (⟨s(y, w), hyw⟩ : G.edgeSet) = some alpha)
    (hga : gamma ≠ alpha)
    (hnone : ∀ i : Fin 5, ¬ ColorAvailableOn G
      (RetainedEdges (deleteMiddleEdge G hax) G) base
      (⟨s(u, a), hua⟩ : G.edgeSet) (some i)) :
    ColorAvailableOn G
      ((RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(u, a), hua⟩ : G.edgeSet)}) \
        {(⟨s(b, y), hby⟩ : G.edgeSet)})
      base (⟨s(u, b), hub⟩ : G.edgeSet) (some gamma) := by
  let D : Set G.edgeSet := RetainedEdges (deleteMiddleEdge G hax) G
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  let M : G.edgeSet := ⟨s(b, y), hby⟩
  let T : G.edgeSet := ⟨s(y, w), hyw⟩
  have hdelete : ∀ q ∈ D, q ≠ (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro q hq
    exact (mem_retained_deleteMiddleEdge_iff G hax q).mp hq
  have hcard : (activeInducedBlockerEdgesOn G D base L).card ≤ 5 := by
    simpa [D, L] using
      card_activeBlockers_leftOuter_le_five_of_second_matching G hu ha hx hb hc
        hua hax hxz hxu hza hub huc hab hac hbc hdelete hB
  have hMD : M ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax M).mpr
    intro hEq
    have hval : s(b, y) = s(a, x) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hval
    rcases hval with h | h
    · exact hab h.1.symm
    · have huxAdj : G.Adj u x := by simpa [h.1] using hub
      have huN : u ∈ G.neighborFinset x :=
        (G.mem_neighborFinset x u).mpr huxAdj.symm
      rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz hza.symm] at huN
      have hucases : u = a ∨ u = z := by simpa using huN
      rcases hucases with hua' | huzEq
      · exact hua.ne hua'
      · exact huz huzEq
  have hML : M ≠ L := by
    intro hEq
    have hcEq := congrArg base hEq
    rw [hM, hL] at hcEq
    exact hga (Option.some.inj hcEq)
  have hMactive : M ∈ activeInducedBlockerEdgesOn G D base L := by
    apply (mem_activeInducedBlockerEdgesOn G D base L M).mpr
    refine ⟨hMD, hML, ?_, ?_⟩
    intro hsep
    exact hsep.2 ⟨u, by simp [L], b, by simp [M], hub⟩
    simpa [M] using (show base (⟨s(b, y), hby⟩ : G.edgeSet) ≠ none by
      simp [hM])
  apply (colorAvailableOn_some_iff G _ base B gamma).mpr
  intro f hf fneB hfcolour
  by_contra hsepBf
  have hfD : f ∈ D := hf.1.1
  have hfL : f ≠ L := by simpa [L] using hf.1.2
  have hfM : f ≠ M := by simpa [M] using hf.2
  have hdeleteM : ∀ q ∈ D \ {M}, q ≠ M := by
    intro q hq
    exact hq.2
  rcases secondFirst_close_imp_secondOuter_or_leftOuter_close G hb hy hua hub
      hby hyw huy hbw hdeleteM ⟨hfD, hfM⟩ fneB hsepBf with hfT | hcloseL
  · have hEq : some gamma = some alpha := by
      rw [← hfcolour, hfT, hT]
    exact hga (Option.some.inj hEq)
  · have hfactive : f ∈ activeInducedBlockerEdgesOn G D base L := by
      apply (mem_activeInducedBlockerEdgesOn G D base L f).mpr
      exact ⟨hfD, hfL, hcloseL, by simp [hfcolour]⟩
    have hdistinct := active_blockers_have_distinct_colours_of_no_available G
      D base L f M hnone hcard hfactive hMactive hfM
    exact hdistinct (hfcolour.trans hM.symm)

/-- The colour on `u-b` can be moved to `u-a` after temporarily removing
both edges.  The only exceptional edge in the radius-two comparison is the
far outer edge `x-z`, whose colour is assumed different. -/
theorem induced_available_leftOuter_from_secondFirst
    {u a x z b : V}
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (hux : u ≠ x) (haz : a ≠ z)
    (base : G.edgeSet → OneTwoColor 5) (alpha beta : Fin 5)
    (hL : base (⟨s(u, a), hua⟩ : G.edgeSet) = some alpha)
    (hB : base (⟨s(u, b), hub⟩ : G.edgeSet) = some beta)
    (hR : base (⟨s(x, z), hxz⟩ : G.edgeSet) = some alpha)
    (hba : beta ≠ alpha)
    (hvalidNoL : IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(u, a), hua⟩ : G.edgeSet)}) base) :
    ColorAvailableOn G
      ((RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(u, a), hua⟩ : G.edgeSet)}) \
        {(⟨s(u, b), hub⟩ : G.edgeSet)})
      base (⟨s(u, a), hua⟩ : G.edgeSet) (some beta) := by
  let D : Set G.edgeSet := RetainedEdges (deleteMiddleEdge G hax) G
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  have hdelete : ∀ q ∈ D,
      q ≠ (⟨s(a, x), hax⟩ : G.edgeSet) := by
    intro q hq
    exact (mem_retained_deleteMiddleEdge_iff G hax q).mp hq
  have hBD : B ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax B).mpr
    intro hEq
    have hs : s(u, b) = s(a, x) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hua.ne h.1
    · exact hux h.1
  have hBL : B ≠ L := by
    intro hEq
    have hcEq := congrArg base hEq
    rw [hB, hL] at hcEq
    exact hba (Option.some.inj hcEq)
  apply (colorAvailableOn_some_iff G _ base L beta).mpr
  intro f hf hfL hfcolour
  by_contra hsepLf
  rcases leftOuter_close_imp_rightOuter_or_secondFirst_close G ha hx hua hax
      hxz hux haz hub hdelete hf.1.1 hfL hsepLf with hfR | hcloseB
  · have hEq : some beta = some alpha := by
      rw [← hfcolour, hfR, hR]
    exact hba (Option.some.inj hEq)
  · have hBf : B ≠ f := by
      intro hEq
      exact hf.2 (by simpa [B] using hEq.symm)
    have hp := hvalidNoL B (by simpa [D, L] using ⟨hBD, hBL⟩)
      f (by simpa [D, L] using ⟨hf.1.1, hf.1.2⟩) hBf
    have hsepBf : InducedSeparated G B f := by
      simpa [B, hB, hfcolour, PairCompatible] using hp
    exact hcloseB hsepBf

/-! ## Repair when the matching edge at the center is `u-b` -/

set_option maxHeartbeats 1200000 in
theorem exists_goodFive_repair_of_secondFirst_matching
    (hsub : IsSubcubic G)
    {u a x z b y w c : V}
    (hu : IsThreeVertex G u) (hz : IsThreeVertex G z)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hy : IsTwoVertex G y)
    (hc : IsThreeVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (hby : G.Adj b y) (hyw : G.Adj y w)
    (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hux : u ≠ x) (haz : a ≠ z) (huy : u ≠ y) (hbw : b ≠ w)
    (base : G.edgeSet → OneTwoColor 5) (alpha : Fin 5)
    (hcondition : ConditionI G base)
    (hmiddle : base (⟨s(a, x), hax⟩ : G.edgeSet) = none)
    (hL : base (⟨s(u, a), hua⟩ : G.edgeSet) = some alpha)
    (hR : base (⟨s(x, z), hxz⟩ : G.edgeSet) = some alpha)
    (hB : base (⟨s(u, b), hub⟩ : G.edgeSet) = none)
    (hvalidNoL : IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(u, a), hua⟩ : G.edgeSet)}) base)
    (hvalidNoR : IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(x, z), hxz⟩ : G.edgeSet)}) base)
    (hnone : ∀ i : Fin 5, ¬ ColorAvailableOn G
      (RetainedEdges (deleteMiddleEdge G hax) G) base
      (⟨s(u, a), hua⟩ : G.edgeSet) (some i))
    (hsepDeleted : InducedSeparated (deleteMiddleEdge G hax)
      (⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩ :
        (deleteMiddleEdge G hax).edgeSet)
      (⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩ :
        (deleteMiddleEdge G hax).edgeSet)) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  classical
  let D : Set G.edgeSet := RetainedEdges (deleteMiddleEdge G hax) G
  let E : G.edgeSet := ⟨s(a, x), hax⟩
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  let M : G.edgeSet := ⟨s(b, y), hby⟩
  let T : G.edgeSet := ⟨s(y, w), hyw⟩
  let C : G.edgeSet := ⟨s(u, c), huc⟩
  have hNoL : IsOneTwoColoringOn G (D \ {L}) base := by
    simpa [D, L] using hvalidNoL
  have hNoR : IsOneTwoColoringOn G (D \ {R}) base := by
    simpa [D, R] using hvalidNoR
  have hLD : L ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax L).mpr
    exact (middleEdge_ne_leftOuter G hua hax hux).symm
  have hRD : R ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax R).mpr
    exact (middleEdge_ne_rightOuter G hax hxz haz).symm
  obtain ⟨hBD, hCD, hMD, hTD⟩ :=
    other_displayed_edges_mem_deleteMiddleEdge G ha hx hb hy hz hua hax hxz
      hub hby hyw huc hab hux haz huy hbw hsepDeleted
  have hBL : B ≠ L := by
    intro hEq
    have hcEq := congrArg base hEq
    rw [hB, hL] at hcEq
    simp at hcEq
  have hCL : C ≠ L := by
    intro hEq
    have hs : s(u, c) = s(u, a) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hac h.2.symm
    · exact hua.ne h.1
  have hBC : B ≠ C := by
    intro hEq
    have hs : s(u, b) = s(u, c) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hbc h.2
    · exact huc.ne h.1
  have hBM : B ≠ M := by
    simpa [B, M, Sym2.eq_swap] using chain_edges_ne G hub hby huy
  have hMT : M ≠ T := by
    simpa [M, T, Sym2.eq_swap] using chain_edges_ne G hby hyw hbw
  have hML : M ≠ L := by
    intro hEq
    have hs : s(b, y) = s(u, a) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hub.ne h.1.symm
    · exact hab h.1.symm
  have hCnon : base C ≠ none := by
    intro hCnone
    have hp := hNoL B (by simpa [D, L] using ⟨hBD, hBL⟩)
      C (by simpa [D, L] using ⟨hCD, hCL⟩) hBC
    have hdisj : EndpointDisjoint G B C := by
      simpa [B, C, hB, hCnone, PairCompatible] using hp
    exact hdisj u (by simp [B]) (by simp [C])
  have hMnon : base M ≠ none := by
    intro hMnone
    have hp := hNoL B (by simpa [D, L] using ⟨hBD, hBL⟩)
      M (by simpa [D, L] using ⟨hMD, hML⟩) hBM
    have hdisj : EndpointDisjoint G B M := by
      simpa [B, M, hB, hMnone, PairCompatible] using hp
    exact hdisj b (by simp [B]) (by simp [M])
  have huz : u ≠ z :=
    ((inducedSeparated_iff_forall_endpoints (deleteMiddleEdge G hax)).mp
      hsepDeleted u (by simp) z (by simp)).1
  have finish (new : G.edgeSet → OneTwoColor 5)
      (hvalid : IsOneTwoColoringOn G D new)
      (hagree : ColoringsAgreeOff G ({L, E, B, M} : Set G.edgeSet) base new)
      (hnewE : new E = none) :
      ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
    have hcond : ConditionI G new := by
      apply conditionI_of_agreeOff_twoTwoZero_support G hsub hu ha hx hb hy hc
        hua hax hub hby huc hab hac hbc hcondition
      simpa [L, E, B, M] using hagree
    apply exists_goodFive_extension_middle_of_outer_not_same_induced G hsub hu
      hz ha hx hua hax hxz hux haz new (by simpa [D] using hvalid) hcond
      (by simpa [E] using hnewE)
    exact not_same_induced_outer_of_valid_retained G hua hax hxz hux haz new
      (by simpa [D] using hvalid)
  by_cases hTalpha : base T = some alpha
  · obtain ⟨gamma, hMgamma⟩ := Option.ne_none_iff_exists'.mp hMnon
    have hga : gamma ≠ alpha := by
      intro hEq
      subst gamma
      have hTL : T ≠ L := by
        intro hEq'
        have hs : s(y, w) = s(u, a) := congrArg Subtype.val hEq'
        simp only [Sym2.eq_iff] at hs
        rcases hs with h | h
        · exact huy h.1.symm
        · have hya : y = a := h.1
          have hbN : b ∈ G.neighborFinset a :=
            (G.mem_neighborFinset a b).mpr (by simpa [hya] using hby.symm)
          rw [neighborFinset_eq_pair_of_isTwoVertex G ha hua.symm hax hux] at hbN
          have hb' : b = u ∨ b = x := by simpa using hbN
          rcases hb' with hbu | hbx
          · exact hub.ne hbu.symm
          · have huN : u ∈ G.neighborFinset x :=
              (G.mem_neighborFinset x u).mpr (by simpa [hbx] using hub.symm)
            rw [neighborFinset_eq_pair_of_isTwoVertex G hx hax.symm hxz haz] at huN
            have hu' : u = a ∨ u = z := by simpa using huN
            exact hu'.elim hua.ne huz
      have hp := hNoL M (by simpa [D, L] using ⟨hMD, hML⟩)
        T (by simpa [D, L] using ⟨hTD, hTL⟩) hMT
      have hsep : InducedSeparated G M T := by
        simpa [M, T, hMgamma, hTalpha, PairCompatible] using hp
      exact hsep.1 y (by simp [M]) (by simp [T])
    have havailB : ColorAvailableOn G ((D \ {L}) \ {M}) base B
        (some gamma) := by
      simpa [D, L, B, M, T, C] using
        induced_available_secondFirst_of_saturated_blockers G hu ha hx hb hy hc
          hua hax hxz hub hby hyw huc hux.symm haz.symm huz huy hbw hab hac hbc
          base alpha gamma hL hB hMgamma hTalpha hga hnone
    let afterB := recolor G base B (some gamma)
    have hBdom : B ∈ (D \ {L}) \ {M} := by
      refine ⟨⟨hBD, by simpa [L] using hBL⟩, ?_⟩
      simpa [M] using hBM
    have hafterB : IsOneTwoColoringOn G ((D \ {L}) \ {M}) afterB := by
      apply (isOneTwoColoringOn_recolor_iff G hBdom).mpr
      refine ⟨IsOneTwoColoringOn.mono (G := G) hNoL ?_, havailB⟩
      intro f hf
      exact hf.1.1
    have hTB : T ≠ B := by
      intro hEq
      have hcEq := congrArg base hEq
      rw [hTalpha, hB] at hcEq
      simp at hcEq
    have havailM : ColorAvailableOn G (D \ {L}) afterB M none := by
      apply matching_available_secondMiddle_of_outer_nonmatching G hb hy hub hby
        hyw huy hbw (D \ {L}) afterB
      · simp [afterB, B]
      · simp [afterB, T, hTB, hTalpha]
    let afterM := recolor G afterB M none
    have hMdom : M ∈ D \ {L} := by
      exact ⟨hMD, by simpa [L] using hML⟩
    have hafterM : IsOneTwoColoringOn G (D \ {L}) afterM := by
      apply (isOneTwoColoringOn_recolor_iff G hMdom).mpr
      refine ⟨?_, havailM⟩
      exact hafterB
    have havailL : ColorAvailableOn G D afterM L none := by
      apply matching_available_leftOuter_of_no_terminal_matching G ha hua hax hux
        afterM
      intro f hfD hfu hfL hfnone
      rcases edge_eq_one_of_three_of_incident_three G hu hua hub huc hab hac hbc
          f ((mem_incidentEdgeFinset (G := G)).mp hfu) with hf | hf | hf
      · exact hfL (Subtype.ext hf)
      · have hfEq : f = B := Subtype.ext hf
        subst f
        simp [afterM, afterB, B, hBM, hBM.symm] at hfnone
      · have hfEq : f = C := Subtype.ext hf
        subst f
        have hCM : C ≠ M := by
          intro hEq
          have hs : s(u, c) = s(b, y) := congrArg Subtype.val hEq
          simp only [Sym2.eq_iff] at hs
          rcases hs with h | h
          · exact hub.ne h.1
          · exact huy h.1
        have hCB : C ≠ B := hBC.symm
        apply hCnon
        simpa [afterM, afterB, C, hCM, hCB] using hfnone
    let final := recolor G afterM L none
    have hfinal : IsOneTwoColoringOn G D final :=
      (isOneTwoColoringOn_recolor_iff G hLD).mpr ⟨hafterM, havailL⟩
    apply finish final hfinal
    · intro f hf
      have hne : f ≠ L ∧ f ≠ E ∧ f ≠ B ∧ f ≠ M := by
        simpa [L, E, B, M] using hf
      simp [final, afterM, afterB, hne.1, hne.2.2.1, hne.2.2.2]
    · have hEL : E ≠ L := middleEdge_ne_leftOuter G hua hax hux
      have hEB : E ≠ B :=
        ((mem_retained_deleteMiddleEdge_iff G hax B).mp hBD).symm
      have hEM : E ≠ M :=
        ((mem_retained_deleteMiddleEdge_iff G hax M).mp hMD).symm
      simp [final, afterM, afterB, E, hEL, hEB, hEM, hmiddle]
  · have havailB : ColorAvailableOn G (D \ {L}) base B (some alpha) := by
      simpa [D, L, B, T] using
        induced_available_secondFirst_of_far_ne_leftColour G hx hb hy hz hua hax
          hxz hub hby hyw hux haz hab huy hbw base alpha hL hTalpha hvalidNoR
          hsepDeleted
    let afterB := recolor G base B (some alpha)
    have hBdom : B ∈ D \ {L} := ⟨hBD, by simpa [L] using hBL⟩
    have hafterB : IsOneTwoColoringOn G (D \ {L}) afterB := by
      apply (isOneTwoColoringOn_recolor_iff G hBdom).mpr
      refine ⟨IsOneTwoColoringOn.mono (G := G) hNoL ?_, havailB⟩
      intro f hf
      exact hf.1
    have havailL : ColorAvailableOn G D afterB L none := by
      apply matching_available_leftOuter_of_no_terminal_matching G ha hua hax hux
        afterB
      intro f hfD hfu hfL hfnone
      rcases edge_eq_one_of_three_of_incident_three G hu hua hub huc hab hac hbc
          f ((mem_incidentEdgeFinset (G := G)).mp hfu) with hf | hf | hf
      · exact hfL (Subtype.ext hf)
      · have hfEq : f = B := Subtype.ext hf
        subst f
        simp [afterB, B] at hfnone
      · have hfEq : f = C := Subtype.ext hf
        subst f
        have hCB : C ≠ B := hBC.symm
        apply hCnon
        simpa [afterB, C, hCB] using hfnone
    let final := recolor G afterB L none
    have hfinal : IsOneTwoColoringOn G D final :=
      (isOneTwoColoringOn_recolor_iff G hLD).mpr ⟨hafterB, havailL⟩
    apply finish final hfinal
    · intro f hf
      have hne : f ≠ L ∧ f ≠ E ∧ f ≠ B ∧ f ≠ M := by
        simpa [L, E, B, M] using hf
      simp [final, afterB, hne.1, hne.2.2.1]
    · have hEL : E ≠ L := middleEdge_ne_leftOuter G hua hax hux
      have hEB : E ≠ B :=
        ((mem_retained_deleteMiddleEdge_iff G hax B).mp hBD).symm
      simp [final, afterB, E, hEL, hEB, hmiddle]

/-! ## Repair when the matching edge at the center is `u-c` -/

set_option maxHeartbeats 1200000 in
theorem exists_goodFive_repair_of_zero_matching
    (hsub : IsSubcubic G)
    {u a x z b y w c : V}
    (hu : IsThreeVertex G u) (hz : IsThreeVertex G z)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hy : IsTwoVertex G y)
    (hc : IsThreeVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (hby : G.Adj b y) (hyw : G.Adj y w)
    (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hux : u ≠ x) (haz : a ≠ z) (huy : u ≠ y) (hbw : b ≠ w)
    (base : G.edgeSet → OneTwoColor 5) (alpha : Fin 5)
    (hcondition : ConditionI G base)
    (hmiddle : base (⟨s(a, x), hax⟩ : G.edgeSet) = none)
    (hL : base (⟨s(u, a), hua⟩ : G.edgeSet) = some alpha)
    (hR : base (⟨s(x, z), hxz⟩ : G.edgeSet) = some alpha)
    (hC : base (⟨s(u, c), huc⟩ : G.edgeSet) = none)
    (hvalidNoL : IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(u, a), hua⟩ : G.edgeSet)}) base)
    (hvalidNoR : IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(x, z), hxz⟩ : G.edgeSet)}) base)
    (hsepDeleted : InducedSeparated (deleteMiddleEdge G hax)
      (⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩ :
        (deleteMiddleEdge G hax).edgeSet)
      (⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩ :
        (deleteMiddleEdge G hax).edgeSet)) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  classical
  let D : Set G.edgeSet := RetainedEdges (deleteMiddleEdge G hax) G
  let E : G.edgeSet := ⟨s(a, x), hax⟩
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  let M : G.edgeSet := ⟨s(b, y), hby⟩
  let T : G.edgeSet := ⟨s(y, w), hyw⟩
  let C : G.edgeSet := ⟨s(u, c), huc⟩
  have hNoL : IsOneTwoColoringOn G (D \ {L}) base := by
    simpa [D, L] using hvalidNoL
  have hNoR : IsOneTwoColoringOn G (D \ {R}) base := by
    simpa [D, R] using hvalidNoR
  have hLD : L ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax L).mpr
    exact (middleEdge_ne_leftOuter G hua hax hux).symm
  have hRD : R ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax R).mpr
    exact (middleEdge_ne_rightOuter G hax hxz haz).symm
  obtain ⟨hBD, hCD, hMD, hTD⟩ :=
    other_displayed_edges_mem_deleteMiddleEdge G ha hx hb hy hz hua hax hxz
      hub hby hyw huc hab hux haz huy hbw hsepDeleted
  have hBL : B ≠ L := by
    intro hEq
    have hs : s(u, b) = s(u, a) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hab h.2.symm
    · exact hua.ne h.1
  have hCL : C ≠ L := by
    intro hEq
    have hcEq := congrArg base hEq
    rw [hC, hL] at hcEq
    simp at hcEq
  have hBC : B ≠ C := by
    intro hEq
    have hs : s(u, b) = s(u, c) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hbc h.2
    · exact huc.ne h.1
  have hBM : B ≠ M := by
    simpa [B, M, Sym2.eq_swap] using chain_edges_ne G hub hby huy
  have hMT : M ≠ T := by
    simpa [M, T, Sym2.eq_swap] using chain_edges_ne G hby hyw hbw
  have hML : M ≠ L := by
    intro hEq
    have hs : s(b, y) = s(u, a) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hub.ne h.1.symm
    · exact hab h.1.symm
  have hCM : C ≠ M := by
    intro hEq
    have hs : s(u, c) = s(b, y) := congrArg Subtype.val hEq
    simp only [Sym2.eq_iff] at hs
    rcases hs with h | h
    · exact hub.ne h.1
    · exact huy h.1
  have hBnon : base B ≠ none := by
    intro hBnone
    have hp := hNoL B (by simpa [D, L] using ⟨hBD, hBL⟩)
      C (by simpa [D, L] using ⟨hCD, hCL⟩) hBC
    have hdisj : EndpointDisjoint G B C := by
      simpa [B, C, hBnone, hC, PairCompatible] using hp
    exact hdisj u (by simp [B]) (by simp [C])
  obtain ⟨beta, hBbeta⟩ := Option.ne_none_iff_exists'.mp hBnon
  have hsepBR : InducedSeparated G B R := by
    simpa [B, R] using
      secondFirst_inducedSeparated_rightOuter_of_deleted_outer_separated G
        hx hb hy hz hua hax hxz hub hby hux haz hab huy hsepDeleted
  have hBR : B ≠ R := by
    intro hEq
    exact hsepBR.1 x (by rw [hEq]; simp [R]) (by simp [R])
  have hba : beta ≠ alpha := by
    intro hEq
    subst beta
    have hLR : L ≠ B := hBL.symm
    have hp := hNoR L (by simpa [D, R] using
        ⟨hLD, leftOuter_ne_rightOuter G hua hax hxz hux⟩)
      B (by simpa [D, R] using ⟨hBD, hBR⟩) hLR
    have hsep : InducedSeparated G L B := by
      simpa [L, B, hL, hBbeta, PairCompatible] using hp
    exact hsep.1 u (by simp [L]) (by simp [B])
  have finish (new : G.edgeSet → OneTwoColor 5)
      (hvalid : IsOneTwoColoringOn G D new)
      (hagree : ColoringsAgreeOff G ({L, E, B, M} : Set G.edgeSet) base new)
      (hnewE : new E = none) :
      ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
    have hcond : ConditionI G new := by
      apply conditionI_of_agreeOff_twoTwoZero_support G hsub hu ha hx hb hy hc
        hua hax hub hby huc hab hac hbc hcondition
      simpa [L, E, B, M] using hagree
    apply exists_goodFive_extension_middle_of_outer_not_same_induced G hsub hu
      hz ha hx hua hax hxz hux haz new (by simpa [D] using hvalid) hcond
      (by simpa [E] using hnewE)
    exact not_same_induced_outer_of_valid_retained G hua hax hxz hux haz new
      (by simpa [D] using hvalid)
  by_cases hTnone : base T = none
  · have havailL : ColorAvailableOn G ((D \ {L}) \ {B}) base L
        (some beta) := by
      simpa [D, L, R, B] using
        induced_available_leftOuter_from_secondFirst G ha hx hua hax hxz hub hux
          haz base alpha beta hL hBbeta hR hba hvalidNoL
    let afterL := recolor G base L (some beta)
    have hLdom : L ∈ D \ {B} := ⟨hLD, by simpa [B] using hBL.symm⟩
    have havailL' : ColorAvailableOn G (D \ {B}) base L (some beta) := by
      intro f hf hfL
      exact havailL f ⟨⟨hf.1, by simpa [L] using hfL⟩, hf.2⟩ hfL
    have hafterL : IsOneTwoColoringOn G (D \ {B}) afterL := by
      apply (isOneTwoColoringOn_recolor_iff G hLdom).mpr
      refine ⟨?_, havailL'⟩
      apply IsOneTwoColoringOn.mono (G := G) hNoL
      intro f hf
      exact ⟨hf.1.1, hf.2⟩
    have havailBbase : ColorAvailableOn G (D \ {L}) base B (some alpha) := by
      apply induced_available_secondFirst_of_far_ne_leftColour G hx hb hy hz hua
        hax hxz hub hby hyw hux haz hab huy hbw base alpha hL
        (by simpa [T, hTnone]) hvalidNoR hsepDeleted
    have havailB : ColorAvailableOn G D afterL B (some alpha) := by
      apply (colorAvailableOn_some_iff G D afterL B alpha).mpr
      intro f hfD hfB hfcolour
      by_cases hfL : f = L
      · subst f
        simp [afterL, L, hba] at hfcolour
      · have hbasef : base f = some alpha := by
          simpa [afterL, hfL] using hfcolour
        exact (colorAvailableOn_some_iff G (D \ {L}) base B alpha).mp
          havailBbase f ⟨hfD, by simpa [L] using hfL⟩ hfB hbasef
    let final := recolor G afterL B (some alpha)
    have hfinal : IsOneTwoColoringOn G D final :=
      (isOneTwoColoringOn_recolor_iff G hBD).mpr ⟨hafterL, havailB⟩
    apply finish final hfinal
    · intro f hf
      have hne : f ≠ L ∧ f ≠ E ∧ f ≠ B ∧ f ≠ M := by
        simpa [L, E, B, M] using hf
      simp [final, afterL, hne.1, hne.2.2.1]
    · have hEL : E ≠ L := middleEdge_ne_leftOuter G hua hax hux
      have hEB : E ≠ B :=
        ((mem_retained_deleteMiddleEdge_iff G hax B).mp hBD).symm
      simp [final, afterL, E, hEL, hEB, hmiddle]
  · have havailM : ColorAvailableOn G (D \ {L}) base M none := by
      apply matching_available_secondMiddle_of_outer_nonmatching G hb hy hub hby
        hyw huy hbw (D \ {L}) base
      · simpa [B] using hBnon
      · simpa [T] using hTnone
    let afterM := recolor G base M none
    have hMdom : M ∈ D \ {L} := ⟨hMD, by simpa [L] using hML⟩
    have hafterM : IsOneTwoColoringOn G (D \ {L}) afterM := by
      apply (isOneTwoColoringOn_recolor_iff G hMdom).mpr
      refine ⟨IsOneTwoColoringOn.mono (G := G) hNoL ?_, havailM⟩
      intro f hf
      exact hf.1
    have hdelete : ∀ f ∈ D, f ≠ E := by
      intro f hf
      simpa [E] using (mem_retained_deleteMiddleEdge_iff G hax f).mp hf
    have hafterC : afterM C = none := by
      simp [afterM, C, hCM, hC]
    have hafterMnone : afterM M = none := by simp [afterM]
    have hcard : (activeInducedBlockerEdgesOn G D afterM L).card ≤ 4 := by
      simpa [D, L, C, M] using
        card_activeBlockers_leftOuter_le_four_of_zero_and_secondMiddle_matching G
          hu ha hx hb hc hua hax hxz hux.symm haz.symm hub hby huc hab hac hbc
          hdelete hafterC hafterMnone
    obtain ⟨i, hi⟩ := exists_available_induced_of_card_activeBlockers_lt G
      D afterM L (lt_of_le_of_lt hcard (by omega))
    let final := recolor G afterM L (some i)
    have hfinal : IsOneTwoColoringOn G D final :=
      (isOneTwoColoringOn_recolor_iff G hLD).mpr ⟨hafterM, hi⟩
    apply finish final hfinal
    · intro f hf
      have hne : f ≠ L ∧ f ≠ E ∧ f ≠ B ∧ f ≠ M := by
        simpa [L, E, B, M] using hf
      simp [final, afterM, hne.1, hne.2.2.2]
    · have hEL : E ≠ L := middleEdge_ne_leftOuter G hua hax hux
      have hEM : E ≠ M :=
        ((mem_retained_deleteMiddleEdge_iff G hax M).mp hMD).symm
      simp [final, afterM, E, hEL, hEM, hmiddle]

/-! ## Complete extension from the middle-edge deletion -/

set_option maxHeartbeats 1600000 in
theorem exists_goodFive_extension_of_twoTwoZero
    (hsub : IsSubcubic G)
    {u a x z b y w c : V}
    (hu : IsThreeVertex G u) (hz : IsThreeVertex G z)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hy : IsTwoVertex G y)
    (hc : IsThreeVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hub : G.Adj u b) (hby : G.Adj b y) (hyw : G.Adj y w)
    (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hux : u ≠ x) (haz : a ≠ z) (huy : u ≠ y) (hbw : b ≠ w)
    (small : (deleteMiddleEdge G hax).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteMiddleEdge G hax) small) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  classical
  let H := deleteMiddleEdge G hax
  let D : Set G.edgeSet := RetainedEdges H G
  let E : G.edgeSet := ⟨s(a, x), hax⟩
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  let M : G.edgeSet := ⟨s(b, y), hby⟩
  let C : G.edgeSet := ⟨s(u, c), huc⟩
  let LH : H.edgeSet :=
    ⟨s(u, a), leftOuter_mem_deleteMiddleEdge G hua hax hux⟩
  let RH : H.edgeSet :=
    ⟨s(x, z), rightOuter_mem_deleteMiddleEdge G hax hxz haz⟩
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small
  have hLD : L ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax L).mpr
    exact (middleEdge_ne_leftOuter G hua hax hux).symm
  have hRD : R ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax R).mpr
    exact (middleEdge_ne_rightOuter G hax hxz haz).symm
  have hmiddle : base E = none := by
    simp [base, E, transportColoringToSupergraph, H, deleteMiddleEdge]
  have hcondition : ConditionI G base := by
    simpa [base, H] using conditionI_transport_deleteMiddleEdge G hsub ha hx hax
      small hsmall.2
  have hNoL : IsOneTwoColoringOn G (D \ {L}) base := by
    simpa [D, H, L, base] using
      transport_deleteMiddleEdge_valid_without_left G ha hx hua hax hxz hux haz
        small hsmall.1
  have hNoR : IsOneTwoColoringOn G (D \ {R}) base := by
    simpa [D, H, R, base] using
      transport_deleteMiddleEdge_valid_without_right G ha hx hua hax hxz hux haz
        small hsmall.1
  have hbaseLH : base L = small LH := by
    dsimp [base]
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small
      (leftOuter_mem_deleteMiddleEdge G hua hax hux)]
  have hbaseRH : base R = small RH := by
    dsimp [base]
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(a, x)} : Set (Sym2 V))) small
      (rightOuter_mem_deleteMiddleEdge G hax hxz haz)]
  have finish (new : G.edgeSet → OneTwoColor 5)
      (hvalid : IsOneTwoColoringOn G D new)
      (hcond : ConditionI G new) (hE : new E = none) :
      ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
    apply exists_goodFive_extension_middle_of_outer_not_same_induced G hsub hu
      hz ha hx hua hax hxz hux haz new (by simpa [D, H] using hvalid) hcond
      (by simpa [E] using hE)
    exact not_same_induced_outer_of_valid_retained G hua hax hxz hux haz new
      (by simpa [D, H] using hvalid)
  by_cases hsame : ∃ alpha : Fin 5, base L = some alpha ∧ base R = some alpha
  · obtain ⟨alpha, hL, hR⟩ := hsame
    have hLsmall : small LH = some alpha := hbaseLH.symm.trans hL
    have hRsmall : small RH = some alpha := hbaseRH.symm.trans hR
    have hLRH : LH ≠ RH := by
      intro hEq
      apply leftOuter_ne_rightOuter G hua hax hxz hux
      apply Subtype.ext
      exact congrArg (fun e : H.edgeSet => (e : Sym2 V)) hEq
    have hsepDeleted : InducedSeparated H LH RH := by
      have hp := hsmall.1 LH (by simp) RH (by simp) hLRH
      simpa [hLsmall, hRsmall, PairCompatible] using hp
    by_cases hU : ∃ m : G.edgeSet,
        m ∈ D ∧ m ∈ incidentEdgeFinset G u ∧ m ≠ L ∧ base m = none
    · obtain ⟨mU, hmUD, hmUinc, hmUL, hmU⟩ := hU
      by_cases hZ : ∃ m : G.edgeSet,
          m ∈ D ∧ m ∈ incidentEdgeFinset G z ∧ m ≠ R ∧
            base m = none
      · by_cases havail : ∃ i : Fin 5, ColorAvailableOn G D base L (some i)
        · obtain ⟨i, hi⟩ := havail
          let after := recolor G base L (some i)
          have hvalid : IsOneTwoColoringOn G D after := by
            apply (isOneTwoColoringOn_recolor_iff G hLD).mpr
            exact ⟨hNoL, hi⟩
          have hagree : ColoringsAgreeOff G ({L, E, B, M} : Set G.edgeSet)
              base after := by
            intro f hf
            have hfL : f ≠ L := by
              intro hEq
              apply hf
              simp [hEq]
            simp [after, hfL]
          have hcond : ConditionI G after := by
            apply conditionI_of_agreeOff_twoTwoZero_support G hsub hu ha hx hb
              hy hc hua hax hub hby huc hab hac hbc hcondition
            simpa [L, E, B, M] using hagree
          have hEL : E ≠ L := middleEdge_ne_leftOuter G hua hax hux
          apply finish after hvalid hcond
          simp [after, E, hEL, hmiddle]
        · have hnone : ∀ i : Fin 5, ¬ ColorAvailableOn G D base L
              (some i) := by
            intro i hi
            exact havail ⟨i, hi⟩
          have hmu : u ∈ (mU : Sym2 V) :=
            (mem_incidentEdgeFinset (G := G)).mp hmUinc
          rcases edge_eq_one_of_three_of_incident_three G hu hua hub huc hab hac
              hbc mU hmu with hmL | hmB | hmC
          · exact False.elim (hmUL (Subtype.ext hmL))
          · have hBnone : base B = none := by
              have hmEq : mU = B := by
                apply Subtype.ext
                exact hmB
              simpa [hmEq] using hmU
            apply exists_goodFive_repair_of_secondFirst_matching G hsub hu hz ha
              hx hb hy hc hua hax hxz hub hby hyw huc hab hac hbc hux haz huy
              hbw base alpha hcondition hmiddle hL hR hBnone
              (by simpa [D, H, L] using hNoL)
              (by simpa [D, H, R] using hNoR)
              (by simpa [D, H, L] using hnone)
              (by simpa [H, LH, RH] using hsepDeleted)
          · have hCnone : base C = none := by
              have hmEq : mU = C := by
                apply Subtype.ext
                exact hmC
              simpa [hmEq] using hmU
            apply exists_goodFive_repair_of_zero_matching G hsub hu hz ha hx hb
              hy hc hua hax hxz hub hby hyw huc hab hac hbc hux haz huy hbw
              base alpha hcondition hmiddle hL hR hCnone
              (by simpa [D, H, L] using hNoL)
              (by simpa [D, H, R] using hNoR)
              (by simpa [H, LH, RH] using hsepDeleted)
      · have hterminal : ∀ f : G.edgeSet, f ∈ D →
            f ∈ incidentEdgeFinset G z → f ≠ R → base f ≠ none := by
          intro f hfD hfz hfR hfnone
          exact hZ ⟨f, hfD, hfz, hfR, hfnone⟩
        have havailR : ColorAvailableOn G D base R none := by
          simpa [D, H, R] using
            matching_available_rightOuter_of_no_terminal_matching G hx hax hxz
              haz base (by simpa [D, H, R] using hterminal)
        let after := recolor G base R none
        have hvalid : IsOneTwoColoringOn G D after :=
          (isOneTwoColoringOn_recolor_iff G hRD).mpr ⟨hNoR, havailR⟩
        have hcond : ConditionI G after := by
          apply ConditionI.of_middle_new_support G hsub hu hz ha hx hua hax hxz
            hux haz hcondition
          · intro f hf
            by_cases hfR : f = R
            · exact Or.inr (Or.inr hfR)
            · exact Or.inl (by simpa [after, hfR] using hf)
          · intro f i hf
            by_cases hfR : f = R
            · subst f
              simp [after] at hf
            · exact Or.inl (by simpa [after, hfR] using hf)
        have hER : E ≠ R := middleEdge_ne_rightOuter G hax hxz haz
        apply finish after hvalid hcond
        simp [after, E, R, hER, hmiddle]
    · have hterminal : ∀ f : G.edgeSet, f ∈ D →
          f ∈ incidentEdgeFinset G u → f ≠ L → base f ≠ none := by
        intro f hfD hfu hfL hfnone
        exact hU ⟨f, hfD, hfu, hfL, hfnone⟩
      have havailL : ColorAvailableOn G D base L none := by
        simpa [D, H, L] using
          matching_available_leftOuter_of_no_terminal_matching G ha hua hax hux
            base (by simpa [D, H, L] using hterminal)
      let after := recolor G base L none
      have hvalid : IsOneTwoColoringOn G D after :=
        (isOneTwoColoringOn_recolor_iff G hLD).mpr ⟨hNoL, havailL⟩
      have hcond : ConditionI G after := by
        apply ConditionI.of_middle_new_support G hsub hu hz ha hx hua hax hxz
          hux haz hcondition
        · intro f hf
          by_cases hfL : f = L
          · exact Or.inr (Or.inl hfL)
          · exact Or.inl (by simpa [after, hfL] using hf)
        · intro f i hf
          by_cases hfL : f = L
          · subst f
            simp [after] at hf
          · exact Or.inl (by simpa [after, hfL] using hf)
      have hEL : E ≠ L := middleEdge_ne_leftOuter G hua hax hux
      apply finish after hvalid hcond
      simp [after, E, L, hEL, hmiddle]
  · have hvalid : IsOneTwoColoringOn G D base := by
      simpa [D, H, base] using
        transport_deleteMiddleEdge_valid G ha hx hua hax hxz hux haz small
          hsmall.1 (by
            intro i hiL hiR
            exact False.elim (hsame ⟨i, hbaseLH.trans hiL,
              hbaseRH.trans hiR⟩))
    apply finish base hvalid hcondition hmiddle

end Finite

/-! ## Lemma 3.6 for an edge-minimal bad graph -/

section ClassicalMinimal

variable [Fintype V] [DecidableEq V]

/- Paper Lemma 3.6: an edge-minimal Section 3 counterexample contains no
`(2,2,0)` configuration.  The configuration is the honest local predicate
from `SectionThreeStructure`; in particular, neither remote terminal is
assumed distinct from vertices on the other branch. -/
set_option maxHeartbeats 1200000 in
theorem IsEdgeMinimalBad.no_twoTwoZero_sectionThree
    (hmin : IsEdgeMinimalBad SectionThreeEligible HasGoodFive G) :
    ¬ @HasTwoTwoZeroConfiguration V G _ (Classical.decRel G.Adj) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  rintro ⟨u, hu, a, b, c, hab, hac, hbc, hA, hB, hC⟩
  rcases hA with ⟨hua, ha, x, z, hax, hxu, hx, hxz, hza, hz⟩
  rcases hB with ⟨hub, hb, y, w, hby, hyu, hy, hyw, hwb, _hw⟩
  rcases hC with ⟨huc, hc⟩
  have hEligibleG : IsSubcubic G ∧ MaximumAverageDegreeLT G 12 5 := by
    simpa [SectionThreeEligible] using hmin.eligible
  let E : G.edgeSet := ⟨s(a, x), hax⟩
  letI : DecidableRel (G.deleteEdges ({E.1} : Set (Sym2 V))).Adj :=
    Classical.decRel (G.deleteEdges ({E.1} : Set (Sym2 V))).Adj
  have hEligibleDelete :
      SectionThreeEligible (G.deleteEdges ({E.1} : Set (Sym2 V))) := by
    rw [SectionThreeEligible]
    constructor
    · intro q
      exact ((G.deleteEdges ({E.1} : Set (Sym2 V))).degree_le_of_le
        (G.deleteEdges_le ({E.1} : Set (Sym2 V)))).trans (hEligibleG.1 q)
    · exact MaximumAverageDegreeLT.mono
        (G.deleteEdges_le ({E.1} : Set (Sym2 V))) hEligibleG.2
  have hgoodDelete :
      HasGoodFive (G.deleteEdges ({E.1} : Set (Sym2 V))) :=
    hmin.good_deleteEdge E hEligibleDelete
  rw [HasGoodFive] at hgoodDelete
  obtain ⟨small, hsmallClassical⟩ := hgoodDelete
  have hsmall :
      @GoodFive V (deleteMiddleEdge G hax) _
        (@SimpleGraph.instDecidableRelAdjDeleteEdgesOfDecidablePredSym2MemSetOfDecidableEq
          V G ({s(a, x)} : Set (Sym2 V)) _ _ _) small := by
    apply goodFive_change_decidableRel
      (G := deleteMiddleEdge G hax)
      (Classical.decRel (deleteMiddleEdge G hax).Adj)
      (@SimpleGraph.instDecidableRelAdjDeleteEdgesOfDecidablePredSym2MemSetOfDecidableEq
        V G ({s(a, x)} : Set (Sym2 V)) _ _ _) small
    simpa [E, deleteMiddleEdge] using hsmallClassical
  obtain ⟨colour, hgood⟩ :=
    exists_goodFive_extension_of_twoTwoZero G hEligibleG.1 hu hz ha hx hb hy hc
      hua hax hxz hub hby hyw huc hab hac hbc hxu.symm hza.symm hyu.symm
      hwb.symm small hsmall
  apply hmin.not_good
  rw [HasGoodFive]
  exact ⟨colour, hgood⟩

end ClassicalMinimal

end

end LeanCo.PackingEdgeColoring
