import LeanCo.PackingEdgeColoring.SectionFourReduction
import LeanCo.PackingEdgeColoring.GoodExtension
import LeanCo.PackingEdgeColoring.AvailabilityMultiplicity
import LeanCo.PackingEdgeColoring.ColorSymmetry
import LeanCo.PackingEdgeColoring.SectionThreeNoThreeChain
import LeanCo.PackingEdgeColoring.SectionFourLongThreadPair
import LeanCo.PackingEdgeColoring.PlanarHeredity

/-!
# The Section 4 no-four-chain reduction

This module formalizes Lemma 4.3.  The middle two vertices of a certified
four-chain are isolated, the resulting good four-colouring is transported
back to the ambient edge type, and the three missing path edges are restored.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-! ## The two-vertex deletion -/

/-- The spanning subgraph obtained by deleting every edge incident with
either of the two middle vertices. -/
abbrev deleteFourChainCenters (v₂ v₃ : V) : SimpleGraph V :=
  (G.deleteIncidenceSet v₂).deleteIncidenceSet v₃

/-- The canonical inclusion of the twice-deleted graph. -/
def deleteFourChainCentersLE (v₂ v₃ : V) :
    deleteFourChainCenters G v₂ v₃ ≤ G :=
  ((G.deleteIncidenceSet v₂).deleteIncidenceSet_le v₃).trans
    (G.deleteIncidenceSet_le v₂)

theorem deleteFourChainCenters_adj_iff {v₂ v₃ r s : V} :
    (deleteFourChainCenters G v₂ v₃).Adj r s ↔
      G.Adj r s ∧ r ≠ v₂ ∧ s ≠ v₂ ∧ r ≠ v₃ ∧ s ≠ v₃ := by
  simp only [deleteFourChainCenters, SimpleGraph.deleteIncidenceSet_adj]
  aesop

/-- An ambient edge survives precisely when neither deleted vertex is one
of its endpoints. -/
theorem mem_retained_deleteFourChainCenters_iff {v₂ v₃ : V}
    (e : G.edgeSet) :
    e ∈ RetainedEdges (deleteFourChainCenters G v₂ v₃) G ↔
      v₂ ∉ (e : Sym2 V) ∧ v₃ ∉ (e : Sym2 V) := by
  constructor
  · intro he
    have he' : e.1 ∈
        (G.deleteIncidenceSet v₂).edgeSet \
          (G.deleteIncidenceSet v₂).incidenceSet v₃ := by
      simpa [RetainedEdges, deleteFourChainCenters,
        edgeSet_deleteIncidenceSet] using he
    constructor
    · intro hv₂
      have hbase : e.1 ∈ G.edgeSet \ G.incidenceSet v₂ := by
        simpa [edgeSet_deleteIncidenceSet] using he'.1
      exact hbase.2 ⟨e.2, hv₂⟩
    · intro hv₃
      exact he'.2 ⟨he'.1, hv₃⟩
  · rintro ⟨hv₂, hv₃⟩
    change e.1 ∈ (deleteFourChainCenters G v₂ v₃).edgeSet
    simp only [deleteFourChainCenters, edgeSet_deleteIncidenceSet]
    refine ⟨⟨e.2, ?_⟩, ?_⟩
    · rintro ⟨_, hmem⟩
      exact hv₂ hmem
    · rintro ⟨_, hmem⟩
      exact hv₃ hmem

/-- Deleting two incidence sets still reflects every ambient adjacency
between endpoints of retained edges. -/
theorem deleteFourChainCenters_reflectsAdjacency (v₂ v₃ : V) :
    ReflectsAdjacencyOnEdgeEndpoints
      (deleteFourChainCentersLE G v₂ v₃) := by
  intro e f r s hre hsf hrs
  have he : (edgeEmbeddingOfLE (deleteFourChainCentersLE G v₂ v₃) e) ∈
      RetainedEdges (deleteFourChainCenters G v₂ v₃) G :=
    edgeEmbeddingOfLE_mem_retained _ e
  have hf : (edgeEmbeddingOfLE (deleteFourChainCentersLE G v₂ v₃) f) ∈
      RetainedEdges (deleteFourChainCenters G v₂ v₃) G :=
    edgeEmbeddingOfLE_mem_retained _ f
  have heAvoid :=
    (mem_retained_deleteFourChainCenters_iff G _).mp he
  have hfAvoid :=
    (mem_retained_deleteFourChainCenters_iff G _).mp hf
  apply (deleteFourChainCenters_adj_iff G).mpr
  exact ⟨hrs, fun h => heAvoid.1 (h ▸ hre),
    fun h => hfAvoid.1 (h ▸ hsf),
    fun h => heAvoid.2 (h ▸ hre),
    fun h => hfAvoid.2 (h ▸ hsf)⟩

/-- A valid colouring of the twice-deleted graph transports honestly to all
retained ambient edges. -/
theorem transport_deleteFourChainCenters_valid {k : ℕ} (v₂ v₃ : V)
    {small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor k}
    (hsmall : IsOneTwoColoring (deleteFourChainCenters G v₂ v₃) small) :
    IsOneTwoColoringOn G
      (RetainedEdges (deleteFourChainCenters G v₂ v₃) G)
      (transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small) :=
  transportColoringToSupergraph_valid
    (deleteFourChainCentersLE G v₂ v₃)
    (deleteFourChainCenters_reflectsAdjacency G v₂ v₃) hsmall

/-! ## Ordered data extracted from a four-chain -/

structure FourChainCore (v₁ v₂ v₃ v₄ : V) : Prop where
  first_two : IsTwoVertex G v₁
  second_two : IsTwoVertex G v₂
  third_two : IsTwoVertex G v₃
  fourth_two : IsTwoVertex G v₄
  first_adj : G.Adj v₁ v₂
  middle_adj : G.Adj v₂ v₃
  last_adj : G.Adj v₃ v₄
  ne₁₃ : v₁ ≠ v₃
  ne₁₄ : v₁ ≠ v₄
  ne₂₄ : v₂ ≠ v₄

theorem IsKChain.fourChainCore {v₁ v₄ : V} {p : G.Walk v₁ v₄}
    (hp : IsKChain G p 4) :
    FourChainCore G v₁ (p.getVert 1) (p.getVert 2) v₄ := by
  have hlen : p.length = 3 := by
    have := hp.length
    omega
  have hadj₁₂ : G.Adj v₁ (p.getVert 1) := by
    simpa using p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
  have hadj₂₃ : G.Adj (p.getVert 1) (p.getVert 2) :=
    p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
  have hadj₃₄ : G.Adj (p.getVert 2) v₄ := by
    have h := p.adj_getVert_succ (i := 2) (by omega : 2 < p.length)
    have hend : p.getVert 3 = v₄ := by
      rw [← hlen]
      exact p.getVert_length
    simpa [hend] using h
  have htwo (i : ℕ) (hi : i ≤ 3) : IsTwoVertex G (p.getVert i) :=
    hp.2.2 (p.getVert i) (p.getVert_mem_support i)
  have hfirst : IsTwoVertex G v₁ := by simpa using htwo 0 (by omega)
  have hfourth : IsTwoVertex G v₄ := by
    have hend : p.getVert 3 = v₄ := by
      rw [← hlen]
      exact p.getVert_length
    simpa [hend] using htwo 3 (by omega)
  have getVert_ne (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 3) (hij : i ≠ j) :
      p.getVert i ≠ p.getVert j := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show i ∈ {r : ℕ | r ≤ p.length} by simpa [hlen] using hi)
      (show j ∈ {r : ℕ | r ≤ p.length} by simpa [hlen] using hj)
      heq
    exact hij hinj
  have hend : p.getVert 3 = v₄ := by
    rw [← hlen]
    exact p.getVert_length
  refine ⟨hfirst, htwo 1 (by omega), htwo 2 (by omega), hfourth,
    hadj₁₂, hadj₂₃, hadj₃₄, ?_, ?_, ?_⟩
  · simpa using getVert_ne 0 2 (by omega) (by omega) (by omega)
  · simpa [hend] using getVert_ne 0 3 (by omega) (by omega) (by omega)
  · simpa [hend] using getVert_ne 1 3 (by omega) (by omega) (by omega)

/-! ## Availability at the two outer missing edges -/

/-- If the two vertices beyond `v₁-v₂` carry no retained edges, every
active induced-colour blocker of `v₁-v₂` is an edge at the external
terminal `u`.  The already matching-coloured edge `u-v₁` can then be
removed from that incidence set. -/
theorem activeBlockers_chainOuter_subset_terminal_erase
    {u v₁ v₂ v₃ : V}
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4)
    (hP : colour (⟨s(u, v₁), hu₁⟩ : G.edgeSet) = none) :
    activeInducedBlockerEdgesOn G D colour
        (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) ⊆
      (incidentEdgeFinset G u).erase
        (⟨s(u, v₁), hu₁⟩ : G.edgeSet) := by
  classical
  let A : G.edgeSet := ⟨s(v₁, v₂), h₁₂⟩
  let P : G.edgeSet := ⟨s(u, v₁), hu₁⟩
  intro f hf
  have hf' := (mem_activeInducedBlockerEdgesOn G D colour A f).mp hf
  have hfAvoid := hDavoid f hf'.1
  have putU (huf : u ∈ (f : Sym2 V)) : f ∈ incidentEdgeFinset G u :=
    (mem_incidentEdgeFinset (G := G)).mpr huf
  have fromV₁ (h₁f : v₁ ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G u := by
    rcases edge_eq_left_or_right_of_incident_two G hv₁ hu₁.symm h₁₂
        hu₂ f h₁f with hfP | hfA
    · apply putU
      rw [hfP]
      simp
    · have hv₂f : v₂ ∈ (f : Sym2 V) := by rw [hfA]; simp
      exact False.elim (hfAvoid.1 hv₂f)
  have hinc : f ∈ incidentEdgeFinset G u := by
    by_cases hdisj : EndpointDisjoint G A f
    · have hcross : HasCrossEdge G A f := by
        by_contra hn
        exact hf'.2.2.1 ⟨hdisj, hn⟩
      obtain ⟨p, hp, q, hqf, hpq⟩ := hcross
      have hp' : p = v₁ ∨ p = v₂ := by simpa [A] using hp
      rcases hp' with hp₁ | hp₂
      · have h₁q : G.Adj v₁ q := by simpa [hp₁] using hpq
        have hqN : q ∈ G.neighborFinset v₁ :=
          (G.mem_neighborFinset v₁ q).mpr h₁q
        rw [neighborFinset_eq_pair_of_isTwoVertex G hv₁ hu₁.symm h₁₂
          hu₂] at hqN
        have hq : q = u ∨ q = v₂ := by simpa using hqN
        rcases hq with hqu | hq₂
        · exact putU (hqu ▸ hqf)
        · exact False.elim (hfAvoid.1 (hq₂ ▸ hqf))
      · have h₂q : G.Adj v₂ q := by simpa [hp₂] using hpq
        have hqN : q ∈ G.neighborFinset v₂ :=
          (G.mem_neighborFinset v₂ q).mpr h₂q
        rw [neighborFinset_eq_pair_of_isTwoVertex G hv₂ h₁₂.symm h₂₃
          h₁₃] at hqN
        have hq : q = v₁ ∨ q = v₃ := by simpa using hqN
        rcases hq with hq₁ | hq₃
        · exact fromV₁ (hq₁ ▸ hqf)
        · exact False.elim (hfAvoid.2 (hq₃ ▸ hqf))
    · have hshared : ∃ p, p ∈ (A : Sym2 V) ∧ p ∈ (f : Sym2 V) := by
        by_contra hn
        apply hdisj
        intro p hpA hpf
        exact hn ⟨p, hpA, hpf⟩
      obtain ⟨p, hpA, hpf⟩ := hshared
      have hp : p = v₁ ∨ p = v₂ := by simpa [A] using hpA
      rcases hp with hp₁ | hp₂
      · exact fromV₁ (hp₁ ▸ hpf)
      · exact False.elim (hfAvoid.1 (hp₂ ▸ hpf))
  apply Finset.mem_erase.mpr
  refine ⟨?_, hinc⟩
  intro hfP
  subst f
  exact hf'.2.2.2 hP

/-- Without assuming a colour on the retained outer edge, every active
induced blocker of the adjacent restored edge is still incident with the
external terminal. -/
theorem activeBlockers_chainOuter_subset_terminal
    {u v₁ v₂ v₃ : V}
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4) :
    activeInducedBlockerEdgesOn G D colour
        (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) ⊆
      incidentEdgeFinset G u := by
  classical
  let A : G.edgeSet := ⟨s(v₁, v₂), h₁₂⟩
  intro f hf
  have hf' := (mem_activeInducedBlockerEdgesOn G D colour A f).mp hf
  have hfAvoid := hDavoid f hf'.1
  have putU (huf : u ∈ (f : Sym2 V)) : f ∈ incidentEdgeFinset G u :=
    (mem_incidentEdgeFinset (G := G)).mpr huf
  have fromV₁ (h₁f : v₁ ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G u := by
    rcases edge_eq_left_or_right_of_incident_two G hv₁ hu₁.symm h₁₂
        hu₂ f h₁f with hfP | hfA
    · apply putU
      rw [hfP]
      simp
    · have hv₂f : v₂ ∈ (f : Sym2 V) := by rw [hfA]; simp
      exact False.elim (hfAvoid.1 hv₂f)
  by_cases hdisj : EndpointDisjoint G A f
  · have hcross : HasCrossEdge G A f := by
      by_contra hn
      exact hf'.2.2.1 ⟨hdisj, hn⟩
    obtain ⟨p, hp, q, hqf, hpq⟩ := hcross
    have hp' : p = v₁ ∨ p = v₂ := by simpa [A] using hp
    rcases hp' with hp₁ | hp₂
    · have h₁q : G.Adj v₁ q := by simpa [hp₁] using hpq
      have hqN : q ∈ G.neighborFinset v₁ :=
        (G.mem_neighborFinset v₁ q).mpr h₁q
      rw [neighborFinset_eq_pair_of_isTwoVertex G hv₁ hu₁.symm h₁₂
        hu₂] at hqN
      have hq : q = u ∨ q = v₂ := by simpa using hqN
      rcases hq with hqu | hq₂
      · exact putU (hqu ▸ hqf)
      · exact False.elim (hfAvoid.1 (hq₂ ▸ hqf))
    · have h₂q : G.Adj v₂ q := by simpa [hp₂] using hpq
      have hqN : q ∈ G.neighborFinset v₂ :=
        (G.mem_neighborFinset v₂ q).mpr h₂q
      rw [neighborFinset_eq_pair_of_isTwoVertex G hv₂ h₁₂.symm h₂₃
        h₁₃] at hqN
      have hq : q = v₁ ∨ q = v₃ := by simpa using hqN
      rcases hq with hq₁ | hq₃
      · exact fromV₁ (hq₁ ▸ hqf)
      · exact False.elim (hfAvoid.2 (hq₃ ▸ hqf))
  · have hshared : ∃ p, p ∈ (A : Sym2 V) ∧ p ∈ (f : Sym2 V) := by
      by_contra hn
      apply hdisj
      intro p hpA hpf
      exact hn ⟨p, hpA, hpf⟩
    obtain ⟨p, hpA, hpf⟩ := hshared
    have hp : p = v₁ ∨ p = v₂ := by simpa [A] using hpA
    rcases hp with hp₁ | hp₂
    · exact fromV₁ (hp₁ ▸ hpf)
    · exact False.elim (hfAvoid.1 (hp₂ ▸ hpf))

/-- With a subcubic terminal there are at most three active blockers for
the adjacent restored edge. -/
theorem card_activeBlockers_chainOuter_le_three
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ : V}
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4) :
    (activeInducedBlockerEdgesOn G D colour
      (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet)).card ≤ 3 := by
  have hcard := Finset.card_le_card
    (activeBlockers_chainOuter_subset_terminal G hv₁ hv₂ hu₁ h₁₂
      h₂₃ hu₂ h₁₃ hDavoid colour)
  rw [card_incidentEdgeFinset] at hcard
  exact hcard.trans (hsub u)

/-- At a degree-two terminal the preceding general bound sharpens to two. -/
theorem card_activeBlockers_chainOuter_le_two_of_terminal_two
    {u v₁ v₂ v₃ : V}
    (hu : IsTwoVertex G u)
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4) :
    (activeInducedBlockerEdgesOn G D colour
      (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet)).card ≤ 2 := by
  have hcard := Finset.card_le_card
    (activeBlockers_chainOuter_subset_terminal G hv₁ hv₂ hu₁ h₁₂
      h₂₃ hu₂ h₁₃ hDavoid colour)
  rw [card_incidentEdgeFinset, hu] at hcard
  exact hcard

/-- A matching-coloured external edge leaves at most two active induced
blockers for the adjacent missing chain edge. -/
theorem card_activeBlockers_chainOuter_le_two
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ : V}
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4)
    (hP : colour (⟨s(u, v₁), hu₁⟩ : G.edgeSet) = none) :
    (activeInducedBlockerEdgesOn G D colour
      (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet)).card ≤ 2 := by
  classical
  let P : G.edgeSet := ⟨s(u, v₁), hu₁⟩
  have hsubset := activeBlockers_chainOuter_subset_terminal_erase G hv₁
    hv₂ hu₁ h₁₂ h₂₃ hu₂ h₁₃ hDavoid colour hP
  have hPmem : P ∈ incidentEdgeFinset G u :=
    (mem_incidentEdgeFinset (G := G)).mpr (by simp [P])
  have hpos : 0 < (incidentEdgeFinset G u).card :=
    Finset.card_pos.mpr ⟨P, hPmem⟩
  have herase : ((incidentEdgeFinset G u).erase P).card + 1 = G.degree u := by
    rw [Finset.card_erase_of_mem hPmem, card_incidentEdgeFinset]
    rw [card_incidentEdgeFinset] at hpos
    omega
  have hcard := Finset.card_le_card hsubset
  change (activeInducedBlockerEdgesOn G D colour
    (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet)).card ≤
      ((incidentEdgeFinset G u).erase P).card at hcard
  have hdeg := hsub u
  omega

/-- Consequently there are two distinct available induced colours; this is
the exact multiplicity needed to preserve Condition 2 at a degree-two
external terminal. -/
theorem exists_two_available_chainOuter
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ : V}
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4)
    (hP : colour (⟨s(u, v₁), hu₁⟩ : G.edgeSet) = none) :
    ∃ i j : Fin 4, i ≠ j ∧
      ColorAvailableOn G D colour
        (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) (some i) ∧
      ColorAvailableOn G D colour
        (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) (some j) := by
  have hactive := card_activeBlockers_chainOuter_le_two G hsub hv₁ hv₂
    hu₁ h₁₂ h₂₃ hu₂ h₁₃ hDavoid colour hP
  apply exists_two_distinct_available_induced_of_card_blocked_add_two_le
  have hblocked := card_blockedInducedColorsOn_le_card_activeBlockers G D colour
    (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet)
  omega

/-! ## Small visible-edge capacity lemmas for the four-colour palette -/

/-- If both neighbours of a degree-two vertex also have degree two, at
most four graph edges are visible from that vertex. -/
theorem card_vertexVisibleEdgeFinset_le_four
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
different visible edges. -/
theorem five_le_card_vertexVisibleEdgeFinset_of_matching_and_full_four
    {colour : G.edgeSet → OneTwoColor 4} {q : V}
    (hmatch : VertexSeesMatching G colour q)
    (hall : ∀ i : Fin 4, VertexSeesInduced G colour q i) :
    5 ≤ (vertexVisibleEdgeFinset G q).card := by
  classical
  obtain ⟨m, hm, hqm⟩ := (vertexSeesMatching_iff G colour q).mp hmatch
  choose f hf v hv hclose using fun i =>
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
automatic as soon as a matching colour is visible. -/
theorem paletteCondition_at_of_two_two_neighbours_four
    {colour : G.edgeSet → OneTwoColor 4}
    {q a b : V} (hq : IsTwoVertex G q)
    (hqa : G.Adj q a) (hqb : G.Adj q b) (hab : a ≠ b)
    (ha : IsTwoVertex G a) (hb : IsTwoVertex G b)
    (hmatch : VertexSeesMatching G colour q) :
    ¬ ∀ i : Fin 4, VertexSeesInduced G colour q i := by
  intro hall
  have hfive :=
    five_le_card_vertexVisibleEdgeFinset_of_matching_and_full_four G hmatch hall
  have hfour := card_vertexVisibleEdgeFinset_le_four G hq hqa hqb hab ha hb
  omega

/-- Two distinct visible matching edges and the full four-colour induced
palette require six distinct visible graph edges. -/
theorem six_le_card_vertexVisibleEdgeFinset_of_two_matching_and_full_four
    {colour : G.edgeSet → OneTwoColor 4} {q : V}
    (m n : G.edgeSet) (hmn : m ≠ n)
    (hm : colour m = none) (hn : colour n = none)
    (hmvis : (m : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hnvis : (n : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hall : ∀ i : Fin 4, VertexSeesInduced G colour q i) :
    6 ≤ (vertexVisibleEdgeFinset G q).card := by
  classical
  choose f hfcolour v hv hclose using fun i =>
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
          have := hm.symm.trans ((congrArg colour hedge).trans (hfcolour j))
          simp at this
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
            have := hn.symm.trans ((congrArg colour hedge).trans (hfcolour j))
            simp at this
      | some i =>
        cases s with
        | none =>
          exfalso
          have hedge : f i = m := by
            apply Subtype.ext
            exact congrArg (fun e : {e : Sym2 V //
              e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs
          have := (hfcolour i).symm.trans ((congrArg colour hedge).trans hm)
          simp at this
        | some s =>
          cases s with
          | none =>
            exfalso
            have hedge : f i = n := by
              apply Subtype.ext
              exact congrArg (fun e : {e : Sym2 V //
                e ∈ vertexVisibleEdgeFinset G q} => (e : Sym2 V)) hrs
            have := (hfcolour i).symm.trans ((congrArg colour hedge).trans hn)
            simp at this
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

/-- At a degree-two vertex adjacent to a degree-two vertex, two visible
matching edges force the four-colour palette condition. -/
theorem paletteCondition_at_of_two_visible_matching_four
    (hsub : IsSubcubic G) {colour : G.edgeSet → OneTwoColor 4}
    {q r : V} (hq : IsTwoVertex G q) (hqr : G.Adj q r)
    (hr : IsTwoVertex G r)
    (m n : G.edgeSet) (hmn : m ≠ n)
    (hm : colour m = none) (hn : colour n = none)
    (hmvis : (m : Sym2 V) ∈ vertexVisibleEdgeFinset G q)
    (hnvis : (n : Sym2 V) ∈ vertexVisibleEdgeFinset G q) :
    ¬ ∀ i : Fin 4, VertexSeesInduced G colour q i := by
  intro hall
  have hsix :=
    six_le_card_vertexVisibleEdgeFinset_of_two_matching_and_full_four G
      m n hmn hm hn hmvis hnvis hall
  have hfive := card_vertexVisibleEdgeFinset_le_five G hsub hq hqr hr
  omega

/-! ## A six-vertex neighbourhood around the chain -/

/-- The explicit local path used by the extension theorem.  Requiring the
six displayed vertices to be different isolates the purely local colouring
argument from the girth argument used by the final minimal-counterexample
wrapper. -/
structure FourChainNeighborhood (u v₁ v₂ v₃ v₄ w : V) : Prop where
  first_two : IsTwoVertex G v₁
  second_two : IsTwoVertex G v₂
  third_two : IsTwoVertex G v₃
  fourth_two : IsTwoVertex G v₄
  left_adj : G.Adj u v₁
  first_adj : G.Adj v₁ v₂
  middle_adj : G.Adj v₂ v₃
  last_adj : G.Adj v₃ v₄
  right_adj : G.Adj v₄ w
  nodup : [u, v₁, v₂, v₃, v₄, w].Nodup

namespace FourChainNeighborhood

variable {u v₁ v₂ v₃ v₄ w : V}

theorem ne_u_v₂ (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) : u ≠ v₂ := by
  have hn := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, not_false_eq_true] at hn
  exact hn.1.2.1

theorem ne_v₁_v₃ (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) : v₁ ≠ v₃ := by
  have hn := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, not_false_eq_true] at hn
  exact hn.2.1.2.1

theorem ne_v₂_v₄ (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) : v₂ ≠ v₄ := by
  have hn := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, not_false_eq_true] at hn
  exact hn.2.2.1.2.1

theorem ne_v₃_w (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) : v₃ ≠ w := by
  have hn := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, not_false_eq_true] at hn
  exact hn.2.2.2.1.2.1

theorem neighbors_first (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    G.neighborFinset v₁ = {u, v₂} :=
  neighborFinset_eq_pair_of_isTwoVertex G h.first_two h.left_adj.symm
    h.first_adj h.ne_u_v₂

theorem neighbors_second (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    G.neighborFinset v₂ = {v₁, v₃} :=
  neighborFinset_eq_pair_of_isTwoVertex G h.second_two h.first_adj.symm
    h.middle_adj h.ne_v₁_v₃

theorem neighbors_third (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    G.neighborFinset v₃ = {v₂, v₄} :=
  neighborFinset_eq_pair_of_isTwoVertex G h.third_two h.middle_adj.symm
    h.last_adj h.ne_v₂_v₄

theorem neighbors_fourth (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    G.neighborFinset v₄ = {v₃, w} :=
  neighborFinset_eq_pair_of_isTwoVertex G h.fourth_two h.last_adj.symm
    h.right_adj h.ne_v₃_w

theorem reverse (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    FourChainNeighborhood G w v₄ v₃ v₂ v₁ u := by
  refine ⟨h.fourth_two, h.third_two, h.second_two, h.first_two,
    h.right_adj.symm, h.last_adj.symm, h.middle_adj.symm, h.first_adj.symm,
    h.left_adj.symm, ?_⟩
  simpa [ne_comm] using h.nodup.reverse

end FourChainNeighborhood

/-- The three deleted path edges, together with the retained edge set,
partition all ambient edges. -/
theorem insert_fourChainEdges_retained_eq_univ
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    let A : G.edgeSet := ⟨s(v₁, v₂), h.first_adj⟩
    let B : G.edgeSet := ⟨s(v₂, v₃), h.middle_adj⟩
    let C : G.edgeSet := ⟨s(v₃, v₄), h.last_adj⟩
    insert C (insert B (insert A
      (RetainedEdges (deleteFourChainCenters G v₂ v₃) G))) = Set.univ := by
  classical
  dsimp
  ext f
  simp only [Set.mem_insert_iff, Set.mem_univ, iff_true]
  by_cases hv₂f : v₂ ∈ (f : Sym2 V)
  · rcases edge_eq_left_or_right_of_incident_two G h.second_two
      h.first_adj.symm h.middle_adj h.ne_v₁_v₃ f hv₂f with hf | hf
    · right; right; left
      apply Subtype.ext
      simpa only [Sym2.eq_swap] using hf
    · right; left
      apply Subtype.ext
      exact hf
  · by_cases hv₃f : v₃ ∈ (f : Sym2 V)
    · rcases edge_eq_left_or_right_of_incident_two G h.third_two
        h.middle_adj.symm h.last_adj h.ne_v₂_v₄ f hv₃f with hf | hf
      · right; left
        apply Subtype.ext
        simpa only [Sym2.eq_swap] using hf
      · left
        apply Subtype.ext
        exact hf
    · exact Or.inr (Or.inr (Or.inr
        ((mem_retained_deleteFourChainCenters_iff G f).mpr ⟨hv₂f, hv₃f⟩)))

/-- The three missing path edges are pairwise distinct and are not
retained by the twice-deleted graph. -/
theorem fourChainEdges_fresh
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    let A : G.edgeSet := ⟨s(v₁, v₂), h.first_adj⟩
    let B : G.edgeSet := ⟨s(v₂, v₃), h.middle_adj⟩
    let C : G.edgeSet := ⟨s(v₃, v₄), h.last_adj⟩
    A ∉ RetainedEdges (deleteFourChainCenters G v₂ v₃) G ∧
      B ∉ RetainedEdges (deleteFourChainCenters G v₂ v₃) G ∧
      C ∉ RetainedEdges (deleteFourChainCenters G v₂ v₃) G ∧
      A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  classical
  dsimp
  constructor
  · rw [mem_retained_deleteFourChainCenters_iff]
    simp
  constructor
  · rw [mem_retained_deleteFourChainCenters_iff]
    simp
  constructor
  · rw [mem_retained_deleteFourChainCenters_iff]
    simp
  have hA_B : (⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet) ≠
      ⟨s(v₂, v₃), h.middle_adj⟩ := by
    intro heq
    have hval : s(v₁, v₂) = s(v₂, v₃) :=
      congrArg (fun e : G.edgeSet => (e : Sym2 V)) heq
    have hv₁ : v₁ ∈ (s(v₂, v₃) : Sym2 V) := by
      rw [← hval]
      simp
    have : v₁ = v₂ ∨ v₁ = v₃ := by simpa using hv₁
    exact this.elim h.first_adj.ne h.ne_v₁_v₃
  have hA_C : (⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet) ≠
      ⟨s(v₃, v₄), h.last_adj⟩ := by
    intro heq
    have hval : s(v₁, v₂) = s(v₃, v₄) :=
      congrArg (fun e : G.edgeSet => (e : Sym2 V)) heq
    have hv₁ : v₁ ∈ (s(v₃, v₄) : Sym2 V) := by
      rw [← hval]
      simp
    have hv₁' : v₁ = v₃ ∨ v₁ = v₄ := by simpa using hv₁
    have hn := h.nodup
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      not_or, not_false_eq_true] at hn
    exact hv₁'.elim h.ne_v₁_v₃ hn.2.1.2.2.1
  have hB_C : (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet) ≠
      ⟨s(v₃, v₄), h.last_adj⟩ := by
    intro heq
    have hval : s(v₂, v₃) = s(v₃, v₄) :=
      congrArg (fun e : G.edgeSet => (e : Sym2 V)) heq
    have hv₂ : v₂ ∈ (s(v₃, v₄) : Sym2 V) := by
      rw [← hval]
      simp
    have : v₂ = v₃ ∨ v₂ = v₄ := by simpa using hv₂
    exact this.elim h.middle_adj.ne h.ne_v₂_v₄
  exact ⟨hA_B, hA_C, hB_C⟩

theorem fourChainOuterEdges_retained
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    (⟨s(u, v₁), h.left_adj⟩ : G.edgeSet) ∈
        RetainedEdges (deleteFourChainCenters G v₂ v₃) G ∧
      (⟨s(v₄, w), h.right_adj⟩ : G.edgeSet) ∈
        RetainedEdges (deleteFourChainCenters G v₂ v₃) G := by
  classical
  have hn := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, not_false_eq_true] at hn
  constructor
  · apply (mem_retained_deleteFourChainCenters_iff G _).mpr
    constructor
    · intro hm
      have hm' : v₂ = u ∨ v₂ = v₁ := by simpa using hm
      exact hm'.elim (fun e => hn.1.2.1 e.symm)
        (fun e => hn.2.1.1 e.symm)
    · intro hm
      have hm' : v₃ = u ∨ v₃ = v₁ := by simpa using hm
      exact hm'.elim (fun e => hn.1.2.2.1 e.symm)
        (fun e => hn.2.1.2.1 e.symm)
  · apply (mem_retained_deleteFourChainCenters_iff G _).mpr
    constructor
    · intro hm
      have hm' : v₂ = v₄ ∨ v₂ = w := by simpa using hm
      exact hm'.elim h.ne_v₂_v₄ (fun e => hn.2.2.1.2.2.1 e)
    · intro hm
      have hm' : v₃ = v₄ ∨ v₃ = w := by simpa using hm
      exact hm'.elim h.last_adj.ne h.ne_v₃_w

/-! ## Saturation and sharpened outer-edge availability -/

/-- Inclusion-maximality of the matching class transports along an
arbitrary spanning-subgraph inclusion: edges outside the subgraph receive
the matching colour by definition. -/
theorem OneSaturated.transportColoringToSupergraph
    {H : SimpleGraph V} [DecidableRel H.Adj] {k : ℕ}
    (hHG : H ≤ G) {small : H.edgeSet → OneTwoColor k}
    (hsmall : OneSaturated H small) :
    OneSaturated G
      (LeanCo.PackingEdgeColoring.transportColoringToSupergraph hHG small) := by
  intro e he
  have heH : e.1 ∈ H.edgeSet := by
    by_contra hnot
    have : LeanCo.PackingEdgeColoring.transportColoringToSupergraph
        hHG small e = none := by
      simp [LeanCo.PackingEdgeColoring.transportColoringToSupergraph, hnot]
    exact he this
  let eH : H.edgeSet := ⟨e.1, heH⟩
  have hecolour : small eH ≠ none := by
    intro hnone
    apply he
    rw [LeanCo.PackingEdgeColoring.transportColoringToSupergraph_of_mem
      hHG small heH]
    exact hnone
  obtain ⟨f, hf, v, hve, hvf⟩ := hsmall eH hecolour
  let fG : G.edgeSet := edgeEmbeddingOfLE hHG f
  refine ⟨fG, ?_, v, hve, hvf⟩
  simpa [fG] using hf

/-- The preceding transport proof can retain the stronger fact that the
matching witness itself lies in the embedded subgraph. -/
theorem OneSaturated.transportColoringToSupergraph_retained_witness
    {H : SimpleGraph V} [DecidableRel H.Adj] {k : ℕ}
    (hHG : H ≤ G) {small : H.edgeSet → OneTwoColor k}
    (hsmall : OneSaturated H small) :
    ∀ e : G.edgeSet,
      LeanCo.PackingEdgeColoring.transportColoringToSupergraph hHG small e ≠
        none →
      ∃ f : G.edgeSet, f ∈ RetainedEdges H G ∧
        LeanCo.PackingEdgeColoring.transportColoringToSupergraph hHG small f =
          none ∧
        ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V) := by
  intro e he
  have heH : e.1 ∈ H.edgeSet := by
    by_contra hnot
    apply he
    simp [LeanCo.PackingEdgeColoring.transportColoringToSupergraph, hnot]
  let eH : H.edgeSet := ⟨e.1, heH⟩
  have hecolour : small eH ≠ none := by
    intro hnone
    apply he
    rw [LeanCo.PackingEdgeColoring.transportColoringToSupergraph_of_mem
      hHG small heH]
    exact hnone
  obtain ⟨f, hf, v, hve, hvf⟩ := hsmall eH hecolour
  let fG : G.edgeSet := edgeEmbeddingOfLE hHG f
  refine ⟨fG, edgeEmbeddingOfLE_mem_retained hHG f, ?_, v, hve, hvf⟩
  simpa [fG] using hf

/-- With only one blocked colour in a four-colour palette, two available
colours can be chosen while avoiding one prescribed colour. -/
theorem exists_two_available_induced_ne_of_card_blocked_le_one
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor 4)
    (e : G.edgeSet) (t : Fin 4)
    (hcard : (blockedInducedColorsOn G D colour e).card ≤ 1) :
    ∃ i j : Fin 4, i ≠ j ∧ i ≠ t ∧ j ≠ t ∧
      ColorAvailableOn G D colour e (some i) ∧
      ColorAvailableOn G D colour e (some j) := by
  classical
  let A := (availableInducedColorsOn G D colour e).erase t
  have havailCard : 3 ≤ (availableInducedColorsOn G D colour e).card := by
    have hpartition := card_available_add_card_blocked G D colour e
    omega
  have hAcard : 2 ≤ A.card := by
    dsimp [A]
    by_cases ht : t ∈ availableInducedColorsOn G D colour e
    · rw [Finset.card_erase_of_mem ht]
      omega
    · rw [Finset.erase_eq_self.mpr ht]
      exact (by omega : 2 ≤ 3).trans havailCard
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hi' := (Finset.mem_erase.mp hi)
  have hj' := (Finset.mem_erase.mp hj)
  exact ⟨i, j, hij, hi'.1, hj'.1,
    (mem_availableInducedColorsOn G D colour e i).mp hi'.2,
    (mem_availableInducedColorsOn G D colour e j).mp hj'.2⟩

/-- If the external terminal itself has degree two, the active blocker
bound for its adjacent missing chain edge improves from two to one. -/
theorem card_activeBlockers_chainOuter_le_one_of_terminal_two
    {u v₁ v₂ v₃ : V}
    (hu : IsTwoVertex G u)
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4)
    (hP : colour (⟨s(u, v₁), hu₁⟩ : G.edgeSet) = none) :
    (activeInducedBlockerEdgesOn G D colour
      (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet)).card ≤ 1 := by
  classical
  let P : G.edgeSet := ⟨s(u, v₁), hu₁⟩
  have hsubset := activeBlockers_chainOuter_subset_terminal_erase G hv₁
    hv₂ hu₁ h₁₂ h₂₃ hu₂ h₁₃ hDavoid colour hP
  have hPmem : P ∈ incidentEdgeFinset G u :=
    (mem_incidentEdgeFinset (G := G)).mpr (by simp [P])
  have herase : ((incidentEdgeFinset G u).erase P).card = 1 := by
    rw [Finset.card_erase_of_mem hPmem, card_incidentEdgeFinset, hu]
  calc
    (activeInducedBlockerEdgesOn G D colour
      (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet)).card ≤
        ((incidentEdgeFinset G u).erase P).card :=
      Finset.card_le_card hsubset
    _ = 1 := herase

/-- At a degree-two external terminal, two available colours may moreover
be chosen not to fill the terminal's unique missing palette slot. -/
theorem exists_two_available_chainOuter_avoiding
    {u v₁ v₂ v₃ : V}
    (hu : IsTwoVertex G u)
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4)
    (hP : colour (⟨s(u, v₁), hu₁⟩ : G.edgeSet) = none)
    (t : Fin 4) :
    ∃ i j : Fin 4, i ≠ j ∧ i ≠ t ∧ j ≠ t ∧
      ColorAvailableOn G D colour
        (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) (some i) ∧
      ColorAvailableOn G D colour
        (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) (some j) := by
  apply exists_two_available_induced_ne_of_card_blocked_le_one G D colour
  have hblocked := card_blockedInducedColorsOn_le_card_activeBlockers G D colour
    (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet)
  exact hblocked.trans (card_activeBlockers_chainOuter_le_one_of_terminal_two G
    hu hv₁ hv₂ hu₁ h₁₂ h₂₃ hu₂ h₁₃ hDavoid colour hP)

/-- If an outer retained edge is induced-coloured, the matching colour is
available on its adjacent missing chain edge. -/
theorem matching_available_chainOuter_of_outer_induced
    {u v₁ v₂ v₃ : V}
    (hv₁ : IsTwoVertex G v₁)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (hu₂ : u ≠ v₂)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4)
    (hP : colour (⟨s(u, v₁), hu₁⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G D colour
      (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) none := by
  classical
  apply (colorAvailableOn_none_iff G D colour
    (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet)).mpr
  intro f hfD _ hfnone z hzA hzf
  have hz : z = v₁ ∨ z = v₂ := by simpa using hzA
  rcases hz with hz₁ | hz₂
  · rcases edge_eq_left_or_right_of_incident_two G hv₁ hu₁.symm h₁₂ hu₂
        f (hz₁ ▸ hzf) with hfP | hfA
    · apply hP
      have heq : f = (⟨s(u, v₁), hu₁⟩ : G.edgeSet) := by
        apply Subtype.ext
        simpa only [Sym2.eq_swap] using hfP
      simpa [heq] using hfnone
    · have hv₂f : v₂ ∈ (f : Sym2 V) := by rw [hfA]; simp
      exact False.elim ((hDavoid f hfD).1 hv₂f)
  · exact False.elim ((hDavoid f hfD).1 (hz₂ ▸ hzf))

/-- Once the left missing edge has been inserted, an induced-coloured
right outer edge still permits the right missing edge to be matching. -/
theorem matching_available_rightOuter_after_left
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4) (a : OneTwoColor 4)
    (hQ : colour (⟨s(v₄, w), h.right_adj⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G
      (insert (⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet) D)
      (recolor G colour (⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet) a)
      (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet) none := by
  classical
  let A : G.edgeSet := ⟨s(v₁, v₂), h.first_adj⟩
  let C : G.edgeSet := ⟨s(v₃, v₄), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(v₄, w), h.right_adj⟩
  apply (colorAvailableOn_none_iff G _ _ C).mpr
  intro f hf _ hfnone z hzC hzf
  rcases hf with rfl | hfD
  · have hz : z = v₃ ∨ z = v₄ := by simpa [C] using hzC
    have hzf' : z = v₁ ∨ z = v₂ := by simpa [A] using hzf
    have hn := h.nodup
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      not_or, not_false_eq_true] at hn
    rcases hz with hz₃ | hz₄ <;> rcases hzf' with hz₁ | hz₂
    · exact hn.2.1.2.1 (hz₁.symm.trans hz₃)
    · exact hn.2.2.1.1 (hz₂.symm.trans hz₃)
    · exact hn.2.1.2.2.1 (hz₁.symm.trans hz₄)
    · exact hn.2.2.1.2.1 (hz₂.symm.trans hz₄)
  · have hz : z = v₃ ∨ z = v₄ := by simpa [C] using hzC
    rcases hz with rfl | rfl
    · exact False.elim ((hDavoid f hfD).2 hzf)
    · rcases edge_eq_left_or_right_of_incident_two G h.fourth_two
          h.last_adj.symm h.right_adj h.ne_v₃_w f hzf with hfC | hfQ
      · have hv₃f : v₃ ∈ (f : Sym2 V) := by rw [hfC]; simp
        exact False.elim ((hDavoid f hfD).2 hv₃f)
      · apply hQ
        have heq : f = Q := by
          apply Subtype.ext
          exact hfQ
        have hQA : Q ≠ A := by
          intro hEq
          have hw : w ∈ (A : Sym2 V) := by rw [← hEq]; simp [Q]
          have hw' : w = v₁ ∨ w = v₂ := by simpa [A] using hw
          have hn := h.nodup
          simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
            not_or, not_false_eq_true] at hn
          exact hw'.elim (fun e => hn.2.1.2.2.2.1 e.symm)
            (fun e => hn.2.2.1.2.2.1 e.symm)
        simpa [heq, Q, A, recolor_ne G colour a hQA] using hfnone

/-- If both outer missing edges have received induced colours, the middle
edge may receive the matching colour. -/
theorem matching_available_middle_after_induced_outers
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4) (i j : Fin 4) :
    let A : G.edgeSet := ⟨s(v₁, v₂), h.first_adj⟩
    let B : G.edgeSet := ⟨s(v₂, v₃), h.middle_adj⟩
    let C : G.edgeSet := ⟨s(v₃, v₄), h.last_adj⟩
    let afterA := recolor G colour A (some i)
    ColorAvailableOn G (insert C (insert A D))
      (recolor G afterA C (some j)) B none := by
  classical
  dsimp
  have hfresh := fourChainEdges_fresh G h
  apply (colorAvailableOn_none_iff G _ _ _).mpr
  intro f hf _ hfnone z hzB hzf
  rcases hf with rfl | rfl | hfD
  · simp [recolor] at hfnone
  · simp [recolor, hfresh.2.2.2.2.1] at hfnone
  · have hz : z = v₂ ∨ z = v₃ := by simpa using hzB
    exact hz.elim (fun e => (hDavoid f hfD).1 (e ▸ hzf))
      (fun e => (hDavoid f hfD).2 (e ▸ hzf))

/-- A retained edge which conflicts at induced distance with the middle
edge is one of the two retained outer edges. -/
theorem retained_middle_blocker_eq_outer
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    {f : G.edgeSet} (hfD : f ∈ D)
    (hfsep : ¬ InducedSeparated G
      (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet) f) :
    f = (⟨s(u, v₁), h.left_adj⟩ : G.edgeSet) ∨
      f = (⟨s(v₄, w), h.right_adj⟩ : G.edgeSet) := by
  classical
  let B : G.edgeSet := ⟨s(v₂, v₃), h.middle_adj⟩
  have hdisj : EndpointDisjoint G B f := by
    intro z hzB hzf
    have hz : z = v₂ ∨ z = v₃ := by simpa [B] using hzB
    exact hz.elim (fun e => (hDavoid f hfD).1 (e ▸ hzf))
      (fun e => (hDavoid f hfD).2 (e ▸ hzf))
  have hcross : HasCrossEdge G B f := by
    by_contra hn
    exact hfsep ⟨hdisj, hn⟩
  obtain ⟨z, hzB, y, hyf, hzy⟩ := hcross
  have hz : z = v₂ ∨ z = v₃ := by simpa [B] using hzB
  rcases hz with hz₂ | hz₃
  · have hyN : y ∈ G.neighborFinset v₂ :=
      (G.mem_neighborFinset v₂ y).mpr (hz₂ ▸ hzy)
    rw [h.neighbors_second] at hyN
    have hy : y = v₁ ∨ y = v₃ := by simpa using hyN
    rcases hy with rfl | rfl
    · rcases edge_eq_left_or_right_of_incident_two G h.first_two
          h.left_adj.symm h.first_adj h.ne_u_v₂ f hyf with hfP | hfA
      · left
        apply Subtype.ext
        simpa only [Sym2.eq_swap] using hfP
      · have hv₂f : v₂ ∈ (f : Sym2 V) := by rw [hfA]; simp
        exact False.elim ((hDavoid f hfD).1 hv₂f)
    · exact False.elim ((hDavoid f hfD).2 hyf)
  · have hyN : y ∈ G.neighborFinset v₃ :=
      (G.mem_neighborFinset v₃ y).mpr (hz₃ ▸ hzy)
    rw [h.neighbors_third] at hyN
    have hy : y = v₂ ∨ y = v₄ := by simpa using hyN
    rcases hy with rfl | rfl
    · exact False.elim ((hDavoid f hfD).1 hyf)
    · rcases edge_eq_left_or_right_of_incident_two G h.fourth_two
          h.last_adj.symm h.right_adj h.ne_v₃_w f hyf with hfC | hfQ
      · have hv₃f : v₃ ∈ (f : Sym2 V) := by rw [hfC]; simp
        exact False.elim ((hDavoid f hfD).2 hv₃f)
      · right
        apply Subtype.ext
        exact hfQ

/-- A colour different from the colours on the four possible local
blockers is available on the middle edge. -/
theorem colorAvailable_middle_of_avoids_local
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4) (k : Fin 4)
    (hA : colour (⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet) ≠ some k)
    (hC : colour (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet) ≠ some k)
    (hP : colour (⟨s(u, v₁), h.left_adj⟩ : G.edgeSet) ≠ some k)
    (hQ : colour (⟨s(v₄, w), h.right_adj⟩ : G.edgeSet) ≠ some k) :
    ColorAvailableOn G
      (insert (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)
        (insert (⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet) D))
      colour (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet) (some k) := by
  classical
  apply (colorAvailableOn_some_iff G _ colour _ k).mpr
  intro f hf _ hfcolour
  rcases hf with rfl | rfl | hfD
  · exact (hC hfcolour).elim
  · exact (hA hfcolour).elim
  · by_contra hnsep
    rcases retained_middle_blocker_eq_outer G h hDavoid hfD hnsep with rfl | rfl
    · exact hP hfcolour
    · exact hQ hfcolour

/-- Four colours always contain one which avoids two prescribed colours. -/
theorem exists_fin4_ne_two (i j : Fin 4) :
    ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
  classical
  have hnsub : ¬ (Finset.univ : Finset (Fin 4)) ⊆ {i, j} := by
    intro hsub
    have hc := Finset.card_le_card hsub
    have hp : ({i, j} : Finset (Fin 4)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    simpa using (hc.trans hp)
  obtain ⟨k, _, hk⟩ := Finset.not_subset.mp hnsub
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk.1, hk.2⟩

/-- Four colours always contain one which avoids three prescribed colours. -/
theorem exists_fin4_ne_three (i j t : Fin 4) :
    ∃ k : Fin 4, k ≠ i ∧ k ≠ j ∧ k ≠ t := by
  classical
  have hnsub : ¬ (Finset.univ : Finset (Fin 4)) ⊆ {i, j, t} := by
    intro hsub
    have hc := Finset.card_le_card hsub
    have hp : ({i, j, t} : Finset (Fin 4)).card ≤ 3 :=
      (Finset.card_insert_le _ _).trans
        ((Nat.add_le_add_right (Finset.card_insert_le j {t}) 1).trans (by simp))
    simpa using (hc.trans hp)
  obtain ⟨k, _, hk⟩ := Finset.not_subset.mp hnsub
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk.1, hk.2.1, hk.2.2⟩

/-! ## Transporting Condition 2 across the double deletion -/

theorem transport_deleteFourChainCenters_eq_iterated {k : ℕ}
    (v₂ v₃ : V)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor k) :
    transportColoringToSupergraph (deleteFourChainCentersLE G v₂ v₃) small =
      transportColoringToSupergraph (G.deleteIncidenceSet_le v₂)
        (transportColoringToSupergraph
          ((G.deleteIncidenceSet v₂).deleteIncidenceSet_le v₃) small) := by
  funext e
  by_cases hH : e.1 ∈ (deleteFourChainCenters G v₂ v₃).edgeSet
  · have hfirst : e.1 ∈ (G.deleteIncidenceSet v₂).edgeSet :=
      SimpleGraph.edgeSet_mono
        ((G.deleteIncidenceSet v₂).deleteIncidenceSet_le v₃) hH
    simp [transportColoringToSupergraph, hH, hfirst]
  · by_cases hfirst : e.1 ∈ (G.deleteIncidenceSet v₂).edgeSet
    · simp [transportColoringToSupergraph, hH, hfirst]
    · simp [transportColoringToSupergraph, hH, hfirst]

theorem degree_deleteFourChainCenters_eq_of_not_adj
    {v₂ v₃ q : V}
    (hq₂ : q ≠ v₂) (hn₂ : ¬ G.Adj q v₂)
    (hq₃ : q ≠ v₃) (hn₃ : ¬ G.Adj q v₃) :
    (deleteFourChainCenters G v₂ v₃).degree q = G.degree q := by
  have hn₃' : ¬ (G.deleteIncidenceSet v₂).Adj q v₃ :=
    fun h => hn₃ ((G.deleteIncidenceSet_le v₂) h)
  rw [degree_deleteIncidenceSet_eq_of_not_adj
      (G.deleteIncidenceSet v₂) hq₃ hn₃',
    degree_deleteIncidenceSet_eq_of_not_adj G hq₂ hn₂]

theorem vertexSeesMatching_transport_deleteFourChainCenters_iff_of_not_adj
    {k : ℕ} {v₂ v₃ q : V}
    (hq₂ : q ≠ v₂) (hn₂ : ¬ G.Adj q v₂)
    (hq₃ : q ≠ v₃) (hn₃ : ¬ G.Adj q v₃)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor k) :
    VertexSeesMatching G
        (transportColoringToSupergraph
          (deleteFourChainCentersLE G v₂ v₃) small) q ↔
      VertexSeesMatching (deleteFourChainCenters G v₂ v₃) small q := by
  rw [transport_deleteFourChainCenters_eq_iterated G v₂ v₃ small]
  rw [vertexSeesMatching_transport_deleteIncidenceSet_iff_of_not_adj G
    hq₂ hn₂]
  apply vertexSeesMatching_transport_deleteIncidenceSet_iff_of_not_adj
  · exact hq₃
  · exact fun h => hn₃ ((G.deleteIncidenceSet_le v₂) h)

theorem vertexSeesInduced_transport_deleteFourChainCenters_iff_of_not_adj
    {k : ℕ} {v₂ v₃ q : V}
    (hq₂ : q ≠ v₂) (hn₂ : ¬ G.Adj q v₂)
    (hq₃ : q ≠ v₃) (hn₃ : ¬ G.Adj q v₃)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor k)
    (i : Fin k) :
    VertexSeesInduced G
        (transportColoringToSupergraph
          (deleteFourChainCentersLE G v₂ v₃) small) q i ↔
      VertexSeesInduced (deleteFourChainCenters G v₂ v₃) small q i := by
  rw [transport_deleteFourChainCenters_eq_iterated G v₂ v₃ small]
  rw [vertexSeesInduced_transport_deleteIncidenceSet_iff_of_not_adj G
    hq₂ hn₂]
  apply vertexSeesInduced_transport_deleteIncidenceSet_iff_of_not_adj
  · exact hq₃
  · exact fun h => hn₃ ((G.deleteIncidenceSet_le v₂) h)

/-- The default matching colours on the three deleted path edges make
Condition 2 valid even at the four changed-degree vertices; elsewhere it
is transported exactly from the twice-deleted graph. -/
theorem conditionTwo_transport_deleteFourChainCenters
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    (hsmall : ConditionTwo (deleteFourChainCenters G v₂ v₃) small) :
    ConditionTwo G
      (transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small) := by
  classical
  let base := transportColoringToSupergraph
    (deleteFourChainCentersLE G v₂ v₃) small
  let A : G.edgeSet := ⟨s(v₁, v₂), h.first_adj⟩
  let B : G.edgeSet := ⟨s(v₂, v₃), h.middle_adj⟩
  let C : G.edgeSet := ⟨s(v₃, v₄), h.last_adj⟩
  have hfresh := fourChainEdges_fresh G h
  have hAnot : A.1 ∉ (deleteFourChainCenters G v₂ v₃).edgeSet := by
    exact hfresh.1
  have hBnot : B.1 ∉ (deleteFourChainCenters G v₂ v₃).edgeSet := by
    exact hfresh.2.1
  have hCnot : C.1 ∉ (deleteFourChainCenters G v₂ v₃).edgeSet := by
    exact hfresh.2.2.1
  have hA : base A = none := by
    simp [base, transportColoringToSupergraph, hAnot]
  have hB : base B = none := by
    simp [base, transportColoringToSupergraph, hBnot]
  have hC : base C = none := by
    simp [base, transportColoringToSupergraph, hCnot]
  intro q hq hmatch hall
  by_cases hq₁ : q = v₁
  · subst q
    apply paletteCondition_at_of_two_visible_matching_four G hsub h.first_two
      h.first_adj h.second_two A B hfresh.2.2.2.1 hA hB
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [A])
        (Or.inl rfl)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
        (Or.inr h.first_adj)
    · exact hall
  by_cases hq₂ : q = v₂
  · subst q
    exact (paletteCondition_at_of_two_two_neighbours_four G h.second_two
      h.first_adj.symm h.middle_adj h.ne_v₁_v₃ h.first_two h.third_two
      hmatch) hall
  by_cases hq₃ : q = v₃
  · subst q
    exact (paletteCondition_at_of_two_two_neighbours_four G h.third_two
      h.middle_adj.symm h.last_adj h.ne_v₂_v₄ h.second_two h.fourth_two
      hmatch) hall
  by_cases hq₄ : q = v₄
  · subst q
    apply paletteCondition_at_of_two_visible_matching_four G hsub h.fourth_two
      h.last_adj.symm h.third_two B C hfresh.2.2.2.2.2 hB hC
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
        (Or.inr h.last_adj.symm)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [C])
        (Or.inl rfl)
    · exact hall
  have hn₂ : ¬ G.Adj q v₂ := by
    intro hadj
    have hmem : q ∈ G.neighborFinset v₂ :=
      (G.mem_neighborFinset v₂ q).mpr hadj.symm
    rw [h.neighbors_second] at hmem
    have : q = v₁ ∨ q = v₃ := by simpa using hmem
    exact this.elim hq₁ hq₃
  have hn₃ : ¬ G.Adj q v₃ := by
    intro hadj
    have hmem : q ∈ G.neighborFinset v₃ :=
      (G.mem_neighborFinset v₃ q).mpr hadj.symm
    rw [h.neighbors_third] at hmem
    have : q = v₂ ∨ q = v₄ := by simpa using hmem
    exact this.elim hq₂ hq₄
  have hqSmall : IsTwoVertex (deleteFourChainCenters G v₂ v₃) q := by
    unfold IsTwoVertex at hq ⊢
    rw [degree_deleteFourChainCenters_eq_of_not_adj G hq₂ hn₂ hq₃ hn₃]
    exact hq
  apply hsmall q hqSmall
  · exact (vertexSeesMatching_transport_deleteFourChainCenters_iff_of_not_adj
      G hq₂ hn₂ hq₃ hn₃ small).mp hmatch
  · intro i
    exact (vertexSeesInduced_transport_deleteFourChainCenters_iff_of_not_adj
      G hq₂ hn₂ hq₃ hn₃ small i).mp (hall i)

/-! ## Choosing and inserting the outer restored edges -/

/-- Two available outer-edge colours can be chosen so that, whenever the
external terminal has degree two, neither fills one fixed missing palette
slot there. -/
theorem exists_safe_outer_colour_pair
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ : V}
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4)
    (hcondition : ConditionTwo G colour)
    (hP : colour (⟨s(u, v₁), hu₁⟩ : G.edgeSet) = none) :
    ∃ i j : Fin 4, i ≠ j ∧
      ColorAvailableOn G D colour
        (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) (some i) ∧
      ColorAvailableOn G D colour
        (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) (some j) ∧
      ∀ hu : IsTwoVertex G u,
        ∃ t : Fin 4, ¬ VertexSeesInduced G colour u t ∧ i ≠ t ∧ j ≠ t := by
  classical
  by_cases hu : IsTwoVertex G u
  · have hmatch : VertexSeesMatching G colour u := by
      apply (vertexSeesMatching_iff G colour u).mpr
      exact ⟨⟨s(u, v₁), hu₁⟩, hP, by simp⟩
    obtain ⟨t, ht⟩ :=
      TwoVertexPaletteCondition.exists_missing G hcondition hu hmatch
    obtain ⟨i, j, hij, hit, hjt, hi, hj⟩ :=
      exists_two_available_chainOuter_avoiding G hu hv₁ hv₂ hu₁ h₁₂ h₂₃
        hu₂ h₁₃ hDavoid colour hP t
    exact ⟨i, j, hij, hi, hj, fun _ => ⟨t, ht, hit, hjt⟩⟩
  · obtain ⟨i, j, hij, hi, hj⟩ :=
      exists_two_available_chainOuter G hsub hv₁ hv₂ hu₁ h₁₂ h₂₃
        hu₂ h₁₃ hDavoid colour hP
    exact ⟨i, j, hij, hi, hj, fun hu' => False.elim (hu hu')⟩

/-- Recolouring a fresh edge with a different induced colour preserves an
available colour on a second edge. -/
theorem colorAvailableOn_insert_recolor_of_ne
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor 4}
    {A C : G.edgeSet} {i j : Fin 4}
    (hAD : A ∉ D) (hAC : A ≠ C) (hij : i ≠ j)
    (hC : ColorAvailableOn G D colour C (some j)) :
    ColorAvailableOn G (insert A D) (recolor G colour A (some i)) C
      (some j) := by
  classical
  apply (colorAvailableOn_some_iff G _ _ C j).mpr
  intro f hf hfC hfcolour
  rcases hf with rfl | hfD
  · simp [recolor, hij] at hfcolour
  · have hfA : f ≠ A := fun h => hAD (h ▸ hfD)
    have hfcolourOld : colour f = some j := by
      simpa [recolor_ne G colour (some i) hfA] using hfcolour
    exact (colorAvailableOn_some_iff G D colour C j).mp hC f hfD hfC
      hfcolourOld

def OuterChoiceSafe (colour : G.edgeSet → OneTwoColor 4)
    (u : V) (i : Fin 4) : Prop :=
  ∀ hu : IsTwoVertex G u,
    ∃ t : Fin 4, ¬ VertexSeesInduced G colour u t ∧ i ≠ t

/-- The exact safety needed at a terminal: if Condition 2 is active there,
the new induced colour leaves one old palette slot missing. -/
def OuterPaletteSafe (colour : G.edgeSet → OneTwoColor 4)
    (u : V) (i : Fin 4) : Prop :=
  ∀ (_hu : IsTwoVertex G u), VertexSeesMatching G colour u →
    ∃ t : Fin 4, ¬ VertexSeesInduced G colour u t ∧ i ≠ t

/-- Even when the retained outer edge is induced, the adjacent restored
edge has a palette-safe available induced colour. -/
theorem exists_paletteSafe_available_chainOuter
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ : V}
    (hv₁ : IsTwoVertex G v₁) (hv₂ : IsTwoVertex G v₂)
    (hu₁ : G.Adj u v₁) (h₁₂ : G.Adj v₁ v₂)
    (h₂₃ : G.Adj v₂ v₃)
    (hu₂ : u ≠ v₂) (h₁₃ : v₁ ≠ v₃)
    {D : Set G.edgeSet} (hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V))
    (colour : G.edgeSet → OneTwoColor 4)
    (hcondition : ConditionTwo G colour) :
    ∃ i : Fin 4,
      ColorAvailableOn G D colour
        (⟨s(v₁, v₂), h₁₂⟩ : G.edgeSet) (some i) ∧
      OuterPaletteSafe G colour u i := by
  classical
  let A : G.edgeSet := ⟨s(v₁, v₂), h₁₂⟩
  by_cases hu : IsTwoVertex G u
  · by_cases hmatch : VertexSeesMatching G colour u
    · obtain ⟨t, ht⟩ :=
        TwoVertexPaletteCondition.exists_missing G hcondition hu hmatch
      have hactive := card_activeBlockers_chainOuter_le_two_of_terminal_two G
        hu hv₁ hv₂ hu₁ h₁₂ h₂₃ hu₂ h₁₃ hDavoid colour
      have hactiveA :
          (activeInducedBlockerEdgesOn G D colour A).card ≤ 2 := by
        simpa [A] using hactive
      have hblocked := card_blockedInducedColorsOn_le_card_activeBlockers G D
        colour A
      obtain ⟨i, hi, hit⟩ :=
        exists_available_induced_not_mem_of_card_blocked_add_card_lt G D
          colour A ({t} : Finset (Fin 4)) (by
            simp only [Finset.card_singleton]
            omega)
      exact ⟨i, hi, fun _ _ => ⟨t, ht, by simpa using hit⟩⟩
    · have hactive := card_activeBlockers_chainOuter_le_three G hsub hv₁
        hv₂ hu₁ h₁₂ h₂₃ hu₂ h₁₃ hDavoid colour
      have hactiveA :
          (activeInducedBlockerEdgesOn G D colour A).card ≤ 3 := by
        simpa [A] using hactive
      have hblocked := card_blockedInducedColorsOn_le_card_activeBlockers G D
        colour A
      obtain ⟨i, hi⟩ := exists_available_induced_of_card_blocked_lt G D
        colour A (by omega)
      exact ⟨i, hi, fun _ hm => False.elim (hmatch hm)⟩
  · have hactive := card_activeBlockers_chainOuter_le_three G hsub hv₁
      hv₂ hu₁ h₁₂ h₂₃ hu₂ h₁₃ hDavoid colour
    have hactiveA :
        (activeInducedBlockerEdgesOn G D colour A).card ≤ 3 := by
      simpa [A] using hactive
    have hblocked := card_blockedInducedColorsOn_le_card_activeBlockers G D
      colour A
    obtain ⟨i, hi⟩ := exists_available_induced_of_card_blocked_lt G D
      colour A (by omega)
    exact ⟨i, hi, fun hu' _ => False.elim (hu hu')⟩

/-- In a mixed outer-colour case two new induced colours are visible from
one terminal.  Both must avoid the same palette slot there. -/
def OuterPairChoiceSafe (colour : G.edgeSet → OneTwoColor 4)
    (u : V) (i k : Fin 4) : Prop :=
  ∀ hu : IsTwoVertex G u,
    ∃ t : Fin 4, ¬ VertexSeesInduced G colour u t ∧ i ≠ t ∧ k ≠ t

/-- The four honest extension patterns.  Mixed outer colours use a
matching restored edge on the induced side; this avoids an implicit
palette gap in the paper's terse argument. -/
def FourChainColourPattern
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (base final : G.edgeSet → OneTwoColor 4) : Prop :=
  let P : G.edgeSet := ⟨s(u, v₁), h.left_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.first_adj⟩
  let B : G.edgeSet := ⟨s(v₂, v₃), h.middle_adj⟩
  let C : G.edgeSet := ⟨s(v₃, v₄), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(v₄, w), h.right_adj⟩
  (base P = none ∧ base Q = none ∧
    ∃ i j : Fin 4, i ≠ j ∧ final A = some i ∧ final B = none ∧
      final C = some j ∧ OuterPaletteSafe G base u i ∧
      OuterPaletteSafe G base w j) ∨
  (base P = none ∧ base Q ≠ none ∧
    ∃ i j : Fin 4, i ≠ j ∧ final A = some i ∧ final B = none ∧
      final C = some j ∧ OuterPaletteSafe G base u i ∧
      OuterPaletteSafe G base w j) ∨
  (base P ≠ none ∧ base Q = none ∧
    ∃ i j : Fin 4, i ≠ j ∧ final A = some i ∧ final B = none ∧
      final C = some j ∧ OuterPaletteSafe G base u i ∧
      OuterPaletteSafe G base w j) ∨
  (base P ≠ none ∧ base Q ≠ none ∧
    ∃ k : Fin 4, final A = none ∧ final B = some k ∧ final C = none)

/-- Packing-valid extension across the three deleted chain edges, together
with the exact local colour pattern used by the invariant proofs. -/
theorem exists_valid_fourChain_extension
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteFourChainCenters G v₂ v₃) small) :
    let base := transportColoringToSupergraph
      (deleteFourChainCentersLE G v₂ v₃) small
    ∃ final : G.edgeSet → OneTwoColor 4,
      IsOneTwoColoring G final ∧
      ColoringsAgreeOff G
        ({(⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet),
          (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet),
          (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)} : Set G.edgeSet)
        base final ∧
      FourChainColourPattern G h base final := by
  classical
  let H := deleteFourChainCenters G v₂ v₃
  let D : Set G.edgeSet := RetainedEdges H G
  let P : G.edgeSet := ⟨s(u, v₁), h.left_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.first_adj⟩
  let B : G.edgeSet := ⟨s(v₂, v₃), h.middle_adj⟩
  let C : G.edgeSet := ⟨s(v₃, v₄), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(v₄, w), h.right_adj⟩
  let base := transportColoringToSupergraph
    (deleteFourChainCentersLE G v₂ v₃) small
  have hDavoid : ∀ f ∈ D,
      v₂ ∉ (f : Sym2 V) ∧ v₃ ∉ (f : Sym2 V) := by
    intro f hf
    exact (mem_retained_deleteFourChainCenters_iff G f).mp hf
  have hbaseValid : IsOneTwoColoringOn G D base := by
    simpa [H, D, base] using
      transport_deleteFourChainCenters_valid G v₂ v₃ hsmall.valid
  have hbaseCondition : ConditionTwo G base :=
    conditionTwo_transport_deleteFourChainCenters G hsub h small
      hsmall.paletteCondition
  have hfresh := fourChainEdges_fresh G h
  have hAD : A ∉ D := by simpa [H, D, A] using hfresh.1
  have hBD : B ∉ D := by simpa [H, D, B] using hfresh.2.1
  have hCD : C ∉ D := by simpa [H, D, C] using hfresh.2.2.1
  have hAB : A ≠ B := by simpa [A, B] using hfresh.2.2.2.1
  have hAC : A ≠ C := by simpa [A, C] using hfresh.2.2.2.2.1
  have hBC : B ≠ C := by simpa [B, C] using hfresh.2.2.2.2.2
  have hBA : B ≠ A := hAB.symm
  have hCA : C ≠ A := hAC.symm
  have hCB : C ≠ B := hBC.symm
  have hPD : P ∈ D := by
    apply (mem_retained_deleteFourChainCenters_iff G P).mpr
    constructor
    · intro hm
      have hm' : v₂ = u ∨ v₂ = v₁ := by simpa [P] using hm
      have hn := h.nodup
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
        not_or, not_false_eq_true] at hn
      exact hm'.elim (fun e => hn.1.2.1 e.symm)
        (fun e => hn.2.1.1 e.symm)
    · intro hm
      have hm' : v₃ = u ∨ v₃ = v₁ := by simpa [P] using hm
      have hn := h.nodup
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
        not_or, not_false_eq_true] at hn
      exact hm'.elim (fun e => hn.1.2.2.1 e.symm)
        (fun e => hn.2.1.2.1 e.symm)
  have hQD : Q ∈ D := by
    apply (mem_retained_deleteFourChainCenters_iff G Q).mpr
    constructor
    · intro hm
      have hm' : v₂ = v₄ ∨ v₂ = w := by simpa [Q] using hm
      have hn := h.nodup
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
        not_or, not_false_eq_true] at hn
      exact hm'.elim h.ne_v₂_v₄ (fun e => hn.2.2.1.2.2.1 e)
    · intro hm
      have hm' : v₃ = v₄ ∨ v₃ = w := by simpa [Q] using hm
      exact hm'.elim h.last_adj.ne h.ne_v₃_w
  have hPA : P ≠ A := fun heq => hAD (heq ▸ hPD)
  have hPB : P ≠ B := fun heq => hBD (heq ▸ hPD)
  have hPC : P ≠ C := fun heq => hCD (heq ▸ hPD)
  have hQA : Q ≠ A := fun heq => hAD (heq ▸ hQD)
  have hQB : Q ≠ B := fun heq => hBD (heq ▸ hQD)
  have hQC : Q ≠ C := fun heq => hCD (heq ▸ hQD)
  have hcover : insert B (insert C (insert A D)) = Set.univ := by
    rw [Set.insert_comm B C]
    simpa [H, D, A, B, C] using insert_fourChainEdges_retained_eq_univ G h
  by_cases hPnone : base P = none
  · obtain ⟨i₁, i₂, hi₁i₂, hi₁, hi₂, hsafeI⟩ :=
      exists_safe_outer_colour_pair G hsub h.first_two h.second_two
        h.left_adj h.first_adj h.middle_adj h.ne_u_v₂ h.ne_v₁_v₃
        hDavoid base hbaseCondition (by simpa [P] using hPnone)
    by_cases hQnone : base Q = none
    · obtain ⟨j₁, j₂, hj₁j₂, hj₁, hj₂, hsafeJ⟩ :=
        exists_safe_outer_colour_pair G hsub h.fourth_two h.third_two
          h.right_adj.symm h.last_adj.symm h.middle_adj.symm
          h.ne_v₃_w.symm h.ne_v₂_v₄.symm
          (fun f hf => ⟨(hDavoid f hf).2, (hDavoid f hf).1⟩)
          base hbaseCondition
          (by simpa [Q, Sym2.eq_swap] using hQnone)
      let i := i₁
      let j := if i ≠ j₁ then j₁ else j₂
      have hij : i ≠ j := by
        dsimp [j]
        split
        · assumption
        · rename_i heq
          intro hij₂
          apply hj₁j₂
          exact (not_ne_iff.mp heq).symm.trans hij₂
      have hj : ColorAvailableOn G D base C (some j) := by
        dsimp [j]
        split
        · simpa [C, Sym2.eq_swap] using hj₁
        · simpa [C, Sym2.eq_swap] using hj₂
      have hsafeJj : OuterPaletteSafe G base w j := by
        intro hw _
        obtain ⟨t, ht, hj₁t, hj₂t⟩ := hsafeJ hw
        refine ⟨t, ht, ?_⟩
        dsimp [j]
        split <;> assumption
      let afterA := recolor G base A (some i)
      have hafterA : IsOneTwoColoringOn G (insert A D) afterA :=
        hbaseValid.extend_one G hAD (by simpa [A, i] using hi₁)
      have hjAfter : ColorAvailableOn G (insert A D) afterA C (some j) :=
        colorAvailableOn_insert_recolor_of_ne G hAD hAC hij hj
      let afterC := recolor G afterA C (some j)
      have hafterC : IsOneTwoColoringOn G (insert C (insert A D)) afterC :=
        hafterA.extend_one G (by simp [hCD, hCA]) hjAfter
      have hBmatch : ColorAvailableOn G (insert C (insert A D)) afterC B none := by
        simpa [A, B, C, afterA, afterC] using
          matching_available_middle_after_induced_outers G h hDavoid base i j
      let final := recolor G afterC B none
      have hfinalOn : IsOneTwoColoringOn G
          (insert B (insert C (insert A D))) final :=
        hafterC.extend_one G (by simp [hBD, hBA, hBC]) hBmatch
      refine ⟨final, ?_, ?_, ?_⟩
      · simpa [IsOneTwoColoring, hcover] using hfinalOn
      · intro f hf
        have hne : f ≠ A ∧ f ≠ B ∧ f ≠ C := by simpa [A, B, C] using hf
        change base f = final f
        simp [final, afterC, afterA, recolor, hne.1, hne.2.1, hne.2.2]
      · left
        refine ⟨by simpa [P] using hPnone, by simpa [Q] using hQnone,
          i, j, hij, ?_, ?_, ?_, ?_, hsafeJj⟩
        · simp [final, afterC, afterA, A, B, C, hAB, hBA, hAC, hCA,
            hBC, hCB]
        · simp [final, B]
        · simp [final, afterC, afterA, A, B, C, hAB, hBA, hAC, hCA,
            hBC, hCB]
        · intro hu _
          obtain ⟨t, ht, hi₁t, _⟩ := hsafeI hu
          exact ⟨t, ht, hi₁t⟩
    · obtain ⟨j, hj, hsafeJ⟩ :=
        exists_paletteSafe_available_chainOuter G hsub h.fourth_two
          h.third_two h.right_adj.symm h.last_adj.symm h.middle_adj.symm
          h.ne_v₃_w.symm h.ne_v₂_v₄.symm
          (fun f hf => ⟨(hDavoid f hf).2, (hDavoid f hf).1⟩)
          base hbaseCondition
      have hjC : ColorAvailableOn G D base C (some j) := by
        simpa [C, Sym2.eq_swap] using hj
      let i := if i₁ ≠ j then i₁ else i₂
      have hij : i ≠ j := by
        dsimp [i]
        split
        · assumption
        · rename_i heq
          intro hi₂j
          apply hi₁i₂
          exact (not_ne_iff.mp heq).trans hi₂j.symm
      have hi : ColorAvailableOn G D base A (some i) := by
        dsimp [i]
        split
        · simpa [A] using hi₁
        · simpa [A] using hi₂
      have hsafeIi : OuterPaletteSafe G base u i := by
        intro hu _
        obtain ⟨t, ht, hi₁t, hi₂t⟩ := hsafeI hu
        refine ⟨t, ht, ?_⟩
        dsimp [i]
        split <;> assumption
      let afterA := recolor G base A (some i)
      have hafterA : IsOneTwoColoringOn G (insert A D) afterA :=
        hbaseValid.extend_one G hAD hi
      have hjAfter : ColorAvailableOn G (insert A D) afterA C (some j) :=
        colorAvailableOn_insert_recolor_of_ne G hAD hAC hij hjC
      let afterC := recolor G afterA C (some j)
      have hafterC : IsOneTwoColoringOn G (insert C (insert A D)) afterC :=
        hafterA.extend_one G (by simp [hCD, hCA]) hjAfter
      have hBmatch : ColorAvailableOn G (insert C (insert A D)) afterC B none := by
        simpa [A, B, C, afterA, afterC] using
          matching_available_middle_after_induced_outers G h hDavoid base i j
      let final := recolor G afterC B none
      have hfinalOn : IsOneTwoColoringOn G
          (insert B (insert C (insert A D))) final :=
        hafterC.extend_one G (by simp [hBD, hBA, hBC]) hBmatch
      refine ⟨final, ?_, ?_, ?_⟩
      · simpa [IsOneTwoColoring, hcover] using hfinalOn
      · intro f hf
        have hne : f ≠ A ∧ f ≠ B ∧ f ≠ C := by simpa [A, B, C] using hf
        change base f = final f
        simp [final, afterC, afterA, recolor, hne.1, hne.2.1, hne.2.2]
      · right; left
        refine ⟨by simpa [P] using hPnone, by simpa [Q] using hQnone,
          i, j, hij, ?_, ?_, ?_, hsafeIi, hsafeJ⟩
        · simp [final, afterC, afterA, A, B, C, hAB, hBA, hAC, hCA,
            hBC, hCB]
        · simp [final, B]
        · simp [final, afterC, afterA, A, B, C, hAB, hBA, hAC, hCA,
            hBC, hCB]
  ·
    by_cases hQnone : base Q = none
    · obtain ⟨j₁, j₂, hj₁j₂, hj₁, hj₂, hsafeJ⟩ :=
        exists_safe_outer_colour_pair G hsub h.fourth_two h.third_two
          h.right_adj.symm h.last_adj.symm h.middle_adj.symm
          h.ne_v₃_w.symm h.ne_v₂_v₄.symm
          (fun f hf => ⟨(hDavoid f hf).2, (hDavoid f hf).1⟩)
          base hbaseCondition
          (by simpa [Q, Sym2.eq_swap] using hQnone)
      obtain ⟨i, hi, hsafeI⟩ :=
        exists_paletteSafe_available_chainOuter G hsub h.first_two h.second_two
          h.left_adj h.first_adj h.middle_adj h.ne_u_v₂ h.ne_v₁_v₃ hDavoid
          base hbaseCondition
      let j := if i ≠ j₁ then j₁ else j₂
      have hij : i ≠ j := by
        dsimp [j]
        split
        · assumption
        · rename_i heq
          intro hij₂
          apply hj₁j₂
          exact (not_ne_iff.mp heq).symm.trans hij₂
      have hj : ColorAvailableOn G D base C (some j) := by
        dsimp [j]
        split
        · simpa [C, Sym2.eq_swap] using hj₁
        · simpa [C, Sym2.eq_swap] using hj₂
      have hsafeJj : OuterPaletteSafe G base w j := by
        intro hw _
        obtain ⟨t, ht, hj₁t, hj₂t⟩ := hsafeJ hw
        refine ⟨t, ht, ?_⟩
        dsimp [j]
        split <;> assumption
      let afterA := recolor G base A (some i)
      have hafterA : IsOneTwoColoringOn G (insert A D) afterA :=
        hbaseValid.extend_one G hAD (by simpa [A] using hi)
      have hjAfter : ColorAvailableOn G (insert A D) afterA C (some j) :=
        colorAvailableOn_insert_recolor_of_ne G hAD hAC hij hj
      let afterC := recolor G afterA C (some j)
      have hafterC : IsOneTwoColoringOn G (insert C (insert A D)) afterC :=
        hafterA.extend_one G (by simp [hCD, hCA]) hjAfter
      have hBmatch : ColorAvailableOn G (insert C (insert A D)) afterC B none := by
        simpa [A, B, C, afterA, afterC] using
          matching_available_middle_after_induced_outers G h hDavoid base i j
      let final := recolor G afterC B none
      have hfinalOn : IsOneTwoColoringOn G
          (insert B (insert C (insert A D))) final :=
        hafterC.extend_one G (by simp [hBD, hBA, hBC]) hBmatch
      refine ⟨final, ?_, ?_, ?_⟩
      · simpa [IsOneTwoColoring, hcover] using hfinalOn
      · intro f hf
        have hne : f ≠ A ∧ f ≠ B ∧ f ≠ C := by simpa [A, B, C] using hf
        change base f = final f
        simp [final, afterC, afterA, recolor, hne.1, hne.2.1, hne.2.2]
      · right; right; left
        refine ⟨by simpa [P] using hPnone, by simpa [Q] using hQnone,
          i, j, hij, ?_, ?_, ?_, hsafeI, hsafeJj⟩
        · simp [final, afterC, afterA, A, B, C, hAB, hBA, hAC, hCA,
            hBC, hCB]
        · simp [final, B]
        · simp [final, afterC, afterA, A, B, C, hAB, hBA, hAC, hCA,
            hBC, hCB]
    · obtain ⟨q, hQq'⟩ := Option.ne_none_iff_exists.mp hQnone
      have hQq : base Q = some q := hQq'.symm
      obtain ⟨p, hPp'⟩ := Option.ne_none_iff_exists.mp hPnone
      have hPp : base P = some p := hPp'.symm
      have hAmatch : ColorAvailableOn G D base A none :=
        matching_available_chainOuter_of_outer_induced G h.first_two
          h.left_adj h.first_adj h.ne_u_v₂ hDavoid base
          (by simpa [P, hPp])
      let afterA := recolor G base A none
      have hafterA : IsOneTwoColoringOn G (insert A D) afterA :=
        hbaseValid.extend_one G hAD hAmatch
      have hCmatch : ColorAvailableOn G (insert A D) afterA C none := by
        simpa [A, C, Q, afterA] using
          matching_available_rightOuter_after_left G h hDavoid base none
            (by simpa [Q, hQq])
      let afterC := recolor G afterA C none
      have hafterC : IsOneTwoColoringOn G (insert C (insert A D)) afterC :=
        hafterA.extend_one G (by simp [hCD, hCA]) hCmatch
      obtain ⟨k, hkp, hkq⟩ := exists_fin4_ne_two p q
      have hBavail : ColorAvailableOn G (insert C (insert A D)) afterC B
          (some k) := by
        apply colorAvailable_middle_of_avoids_local G h hDavoid afterC k
        · simp [afterC, afterA, A, C, hAC]
        · simp [afterC, C]
        · simp [afterC, afterA, A, C, P, hAC, hCA, hPA, hPC, hPp,
            hkp, hkp.symm]
        · simp [afterC, afterA, A, C, Q, hQA, hQC, hQq, hkq, hkq.symm]
      let final := recolor G afterC B (some k)
      have hfinalOn : IsOneTwoColoringOn G
          (insert B (insert C (insert A D))) final :=
        hafterC.extend_one G (by simp [hBD, hBA, hBC]) hBavail
      refine ⟨final, ?_, ?_, ?_⟩
      · simpa [IsOneTwoColoring, hcover] using hfinalOn
      · intro f hf
        have hne : f ≠ A ∧ f ≠ B ∧ f ≠ C := by simpa [A, B, C] using hf
        change base f = final f
        simp [final, afterC, afterA, recolor, hne.1, hne.2.1, hne.2.2]
      · right; right; right
        refine ⟨by simpa [P] using hPnone, by simpa [Q] using hQnone,
          k, ?_, ?_, ?_⟩
        · simp [final, afterC, afterA, A, B, C, hAB, hBA, hAC, hCA,
            hBC, hCB]
        · simp [final, B]
        · simp [final, afterC, C, hBC, hCB]

/-! ## The two local goodness invariants -/

/-- Every one of the four extension patterns preserves inclusion-maximality
of the matching class.  Retained induced edges use retained witnesses from
the smaller saturated colouring; each new induced edge has the explicitly
displayed local matching witness. -/
theorem oneSaturated_of_fourChain_pattern
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    (hsmall : OneSaturated (deleteFourChainCenters G v₂ v₃) small)
    (final : G.edgeSet → OneTwoColor 4)
    (hagree : ColoringsAgreeOff G
      ({(⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet),
        (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)} : Set G.edgeSet)
      (transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small) final)
    (hpattern : FourChainColourPattern G h
      (transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small) final) :
    OneSaturated G final := by
  classical
  let H := deleteFourChainCenters G v₂ v₃
  let D : Set G.edgeSet := RetainedEdges H G
  let base := transportColoringToSupergraph
    (deleteFourChainCentersLE G v₂ v₃) small
  let P : G.edgeSet := ⟨s(u, v₁), h.left_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.first_adj⟩
  let B : G.edgeSet := ⟨s(v₂, v₃), h.middle_adj⟩
  let C : G.edgeSet := ⟨s(v₃, v₄), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(v₄, w), h.right_adj⟩
  have hfresh := fourChainEdges_fresh G h
  have hAD : A ∉ D := by simpa [H, D, A] using hfresh.1
  have hBD : B ∉ D := by simpa [H, D, B] using hfresh.2.1
  have hCD : C ∉ D := by simpa [H, D, C] using hfresh.2.2.1
  have houter := fourChainOuterEdges_retained G h
  have hPD : P ∈ D := by simpa [H, D, P] using houter.1
  have hQD : Q ∈ D := by simpa [H, D, Q] using houter.2
  have hagreeD : ∀ f ∈ D, base f = final f := by
    intro f hf
    apply hagree
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro e
      change f = A at e
      exact hAD (e ▸ hf)
    · intro e
      change f = B at e
      exact hBD (e ▸ hf)
    · intro e
      change f = C at e
      exact hCD (e ▸ hf)
  have hretainedWitness : ∀ e : G.edgeSet, base e ≠ none →
      ∃ f : G.edgeSet, f ∈ D ∧ base f = none ∧
        ∃ z, z ∈ (e : Sym2 V) ∧ z ∈ (f : Sym2 V) := by
    simpa [H, D, base] using
      OneSaturated.transportColoringToSupergraph_retained_witness G
        (deleteFourChainCentersLE G v₂ v₃) hsmall
  dsimp [FourChainColourPattern, P, A, B, C, Q, base] at hpattern
  intro e he
  by_cases heA : e = A
  · subst e
    rcases hpattern with hcase | hcase | hcase | hcase
    · rcases hcase with ⟨_, _, i, j, _, hAi, hB, _, _, _⟩
      exact ⟨B, hB, v₂, by simp [A], by simp [B]⟩
    · rcases hcase with ⟨_, _, i, j, _, hAi, hB, _, _, _⟩
      exact ⟨B, hB, v₂, by simp [A], by simp [B]⟩
    · rcases hcase with ⟨_, _, i, j, _, hAi, hB, _, _, _⟩
      exact ⟨B, hB, v₂, by simp [A], by simp [B]⟩
    · rcases hcase with ⟨_, _, k, hA, _, _⟩
      exact False.elim (he hA)
  by_cases heB : e = B
  · subst e
    rcases hpattern with hcase | hcase | hcase | hcase
    · rcases hcase with ⟨_, _, i, j, _, _, hB, _, _, _⟩
      exact False.elim (he hB)
    · rcases hcase with ⟨_, _, i, j, _, _, hB, _, _, _⟩
      exact False.elim (he hB)
    · rcases hcase with ⟨_, _, i, j, _, _, hB, _, _, _⟩
      exact False.elim (he hB)
    · rcases hcase with ⟨_, _, k, hA, _, _⟩
      exact ⟨A, hA, v₂, by simp [B], by simp [A]⟩
  by_cases heC : e = C
  · subst e
    rcases hpattern with hcase | hcase | hcase | hcase
    · rcases hcase with ⟨_, _, i, j, _, _, hB, _, _, _⟩
      exact ⟨B, hB, v₃, by simp [C], by simp [B]⟩
    · rcases hcase with ⟨_, _, i, j, _, _, hB, _, _, _⟩
      exact ⟨B, hB, v₃, by simp [C], by simp [B]⟩
    · rcases hcase with ⟨_, _, i, j, _, _, hB, _, _, _⟩
      exact ⟨B, hB, v₃, by simp [C], by simp [B]⟩
    · rcases hcase with ⟨_, _, k, _, _, hC⟩
      exact False.elim (he hC)
  have heOff : e ∉ ({A, B, C} : Set G.edgeSet) := by
    simp [heA, heB, heC]
  have hbaseE : base e ≠ none := by
    have heq := hagree e (by simpa [A, B, C] using heOff)
    exact fun hb => he (heq.symm.trans hb)
  obtain ⟨f, hfD, hfnone, z, hze, hzf⟩ := hretainedWitness e hbaseE
  exact ⟨f, (hagreeD f hfD).symm.trans hfnone, z, hze, hzf⟩

/-- A missing induced colour stays missing after a local change if every
support edge carrying that colour is outside the vertex's visibility ball. -/
theorem not_vertexSeesInduced_of_agreeOff_of_support
    {S : Set G.edgeSet} {old new : G.edgeSet → OneTwoColor 4}
    {q : V} {t : Fin 4}
    (hagree : ColoringsAgreeOff G S old new)
    (hold : ¬ VertexSeesInduced G old q t)
    (hsupport : ∀ e ∈ S, new e = some t →
      ¬ ∃ z, z ∈ (e : Sym2 V) ∧ (q = z ∨ G.Adj q z)) :
    ¬ VertexSeesInduced G new q t := by
  intro hnew
  obtain ⟨e, he, z, hze, hqz⟩ :=
    (vertexSeesInduced_iff G new q t).mp hnew
  by_cases heS : e ∈ S
  · exact hsupport e heS he ⟨z, hze, hqz⟩
  · apply hold
    apply (vertexSeesInduced_iff G old q t).mpr
    exact ⟨e, (hagree e heS).trans he, z, hze, hqz⟩

/-- Three-edge specialization convenient for the chain reduction. -/
theorem not_vertexSeesInduced_of_three_edge_change
    {old new : G.edgeSet → OneTwoColor 4} {q : V} {t : Fin 4}
    (A B C : G.edgeSet)
    (hagree : ColoringsAgreeOff G ({A, B, C} : Set G.edgeSet) old new)
    (hold : ¬ VertexSeesInduced G old q t)
    (hA : new A ≠ some t ∨
      ¬ ∃ z, z ∈ (A : Sym2 V) ∧ (q = z ∨ G.Adj q z))
    (hB : new B ≠ some t ∨
      ¬ ∃ z, z ∈ (B : Sym2 V) ∧ (q = z ∨ G.Adj q z))
    (hC : new C ≠ some t ∨
      ¬ ∃ z, z ∈ (C : Sym2 V) ∧ (q = z ∨ G.Adj q z)) :
    ¬ ∀ i : Fin 4, VertexSeesInduced G new q i := by
  intro hall
  refine (not_vertexSeesInduced_of_agreeOff_of_support G hagree hold ?_) (hall t)
  intro e heS he
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heS
  rcases heS with rfl | rfl | rfl
  · exact hA.elim (fun hn => False.elim (hn he)) id
  · exact hB.elim (fun hn => False.elim (hn he)) id
  · exact hC.elim (fun hn => False.elim (hn he)) id

/-- Only the six displayed vertices can have their palette affected by the
three restored chain edges. -/
theorem paletteAffectedBy_fourChainEdges_cases
    {u v₁ v₂ v₃ v₄ w q : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (haffect : PaletteAffectedBy G
      ({(⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet),
        (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = u ∨ q = v₁ ∨ q = v₂ ∨ q = v₃ ∨ q = v₄ ∨ q = w := by
  classical
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  rcases haffect with ⟨e, he, z, hze, hqz⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  have closeFirst (hz : z = v₁) : q = u ∨ q = v₁ ∨ q = v₂ := by
    subst z
    rcases hqz with rfl | hadj
    · exact Or.inr (Or.inl rfl)
    · have hmem : q ∈ G.neighborFinset v₁ :=
        (G.mem_neighborFinset v₁ q).mpr hadj.symm
      rw [h.neighbors_first] at hmem
      have hcases : q = u ∨ q = v₂ := by simpa using hmem
      exact hcases.elim Or.inl (fun hq ↦ Or.inr (Or.inr hq))
  have closeSecond (hz : z = v₂) : q = v₁ ∨ q = v₂ ∨ q = v₃ := by
    subst z
    rcases hqz with rfl | hadj
    · exact Or.inr (Or.inl rfl)
    · have hmem : q ∈ G.neighborFinset v₂ :=
        (G.mem_neighborFinset v₂ q).mpr hadj.symm
      rw [h.neighbors_second] at hmem
      have hcases : q = v₁ ∨ q = v₃ := by simpa using hmem
      exact hcases.elim Or.inl (fun hq ↦ Or.inr (Or.inr hq))
  have closeThird (hz : z = v₃) : q = v₂ ∨ q = v₃ ∨ q = v₄ := by
    subst z
    rcases hqz with rfl | hadj
    · exact Or.inr (Or.inl rfl)
    · have hmem : q ∈ G.neighborFinset v₃ :=
        (G.mem_neighborFinset v₃ q).mpr hadj.symm
      rw [h.neighbors_third] at hmem
      have hcases : q = v₂ ∨ q = v₄ := by simpa using hmem
      exact hcases.elim Or.inl (fun hq ↦ Or.inr (Or.inr hq))
  have closeFourth (hz : z = v₄) : q = v₃ ∨ q = v₄ ∨ q = w := by
    subst z
    rcases hqz with rfl | hadj
    · exact Or.inr (Or.inl rfl)
    · have hmem : q ∈ G.neighborFinset v₄ :=
        (G.mem_neighborFinset v₄ q).mpr hadj.symm
      rw [h.neighbors_fourth] at hmem
      have hcases : q = v₃ ∨ q = w := by simpa using hmem
      exact hcases.elim Or.inl (fun hq ↦ Or.inr (Or.inr hq))
  rcases he with rfl | rfl | rfl
  · have hz : z = v₁ ∨ z = v₂ := by simpa using hze
    rcases hz with hz | hz
    · rcases closeFirst hz with hq | hq | hq
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (Or.inl hq))
    · rcases closeSecond hz with hq | hq | hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
  · have hz : z = v₂ ∨ z = v₃ := by simpa using hze
    rcases hz with hz | hz
    · rcases closeSecond hz with hq | hq | hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
    · rcases closeThird hz with hq | hq | hq
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))
  · have hz : z = v₃ ∨ z = v₄ := by simpa using hze
    rcases hz with hz | hz
    · rcases closeThird hz with hq | hq | hq
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))
    · rcases closeFourth hz with hq | hq | hq
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq))))

/-- The right restored edge is outside the induced-colour visibility ball
of the left external terminal. -/
theorem rightChainEdge_not_visible_from_leftTerminal
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    ¬ ∃ z, z ∈ (s(v₃, v₄) : Sym2 V) ∧ (u = z ∨ G.Adj u z) := by
  classical
  have hn := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, not_false_eq_true] at hn
  rintro ⟨z, hz, huz⟩
  have hz' : z = v₃ ∨ z = v₄ := by simpa using hz
  rcases hz' with hz₃ | hz₄
  · subst z
    rcases huz with huv₃ | huv₃
    · exact hn.1.2.2.1 huv₃
    · have hmem : u ∈ G.neighborFinset v₃ :=
        (G.mem_neighborFinset v₃ u).mpr huv₃.symm
      rw [h.neighbors_third] at hmem
      have hc : u = v₂ ∨ u = v₄ := by simpa using hmem
      exact hc.elim h.ne_u_v₂ hn.1.2.2.2.1
  · subst z
    rcases huz with huv₄ | huv₄
    · exact hn.1.2.2.2.1 huv₄
    · have hmem : u ∈ G.neighborFinset v₄ :=
        (G.mem_neighborFinset v₄ u).mpr huv₄.symm
      rw [h.neighbors_fourth] at hmem
      have hc : u = v₃ ∨ u = w := by simpa using hmem
      exact hc.elim hn.1.2.2.1 hn.1.2.2.2.2.1

/-- Symmetric visibility separation for the left restored edge and the
right external terminal. -/
theorem leftChainEdge_not_visible_from_rightTerminal
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    ¬ ∃ z, z ∈ (s(v₁, v₂) : Sym2 V) ∧ (w = z ∨ G.Adj w z) := by
  simpa [Sym2.eq_swap] using
    rightChainEdge_not_visible_from_leftTerminal G h.reverse

/-- The central restored edge is invisible from either external terminal. -/
theorem middleChainEdge_not_visible_from_leftTerminal
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    ¬ ∃ z, z ∈ (s(v₂, v₃) : Sym2 V) ∧ (u = z ∨ G.Adj u z) := by
  classical
  have hn := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, not_false_eq_true] at hn
  rintro ⟨z, hz, huz⟩
  have hz' : z = v₂ ∨ z = v₃ := by simpa using hz
  rcases hz' with hz₂ | hz₃
  · subst z
    rcases huz with huv₂ | huv₂
    · exact FourChainNeighborhood.ne_u_v₂ G h huv₂
    · have hmem : u ∈ G.neighborFinset v₂ :=
        (G.mem_neighborFinset v₂ u).mpr huv₂.symm
      rw [h.neighbors_second] at hmem
      have hc : u = v₁ ∨ u = v₃ := by simpa using hmem
      exact hc.elim hn.1.1 hn.1.2.2.1
  · subst z
    rcases huz with huv₃ | huv₃
    · exact hn.1.2.2.1 huv₃
    · have hmem : u ∈ G.neighborFinset v₃ :=
        (G.mem_neighborFinset v₃ u).mpr huv₃.symm
      rw [h.neighbors_third] at hmem
      have hc : u = v₂ ∨ u = v₄ := by simpa using hmem
      exact hc.elim (FourChainNeighborhood.ne_u_v₂ G h) hn.1.2.2.2.1

theorem middleChainEdge_not_visible_from_rightTerminal
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    ¬ ∃ z, z ∈ (s(v₂, v₃) : Sym2 V) ∧ (w = z ∨ G.Adj w z) := by
  simpa [Sym2.eq_swap] using
    middleChainEdge_not_visible_from_leftTerminal G h.reverse

/-- Recolouring the three restored edges cannot change whether either
external terminal is incident with a matching edge. -/
theorem matchingAffectedBy_fourChainEdges_not_terminals
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    ¬ MatchingAffectedBy G
        ({(⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet),
          (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet),
          (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)} : Set G.edgeSet) u ∧
      ¬ MatchingAffectedBy G
        ({(⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet),
          (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet),
          (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)} : Set G.edgeSet) w := by
  classical
  have hn := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    not_or, not_false_eq_true] at hn
  constructor
  · rintro ⟨e, he, hue⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · have hc : u = v₁ ∨ u = v₂ := by simpa using hue
      exact hc.elim hn.1.1 hn.1.2.1
    · have hc : u = v₂ ∨ u = v₃ := by simpa using hue
      exact hc.elim hn.1.2.1 hn.1.2.2.1
    · have hc : u = v₃ ∨ u = v₄ := by simpa using hue
      exact hc.elim hn.1.2.2.1 hn.1.2.2.2.1
  · rintro ⟨e, he, hwe⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · have hc : w = v₁ ∨ w = v₂ := by simpa using hwe
      exact hc.elim (fun e => hn.2.1.2.2.2.1 e.symm)
        (fun e => hn.2.2.1.2.2.1 e.symm)
    · have hc : w = v₂ ∨ w = v₃ := by simpa using hwe
      exact hc.elim (fun e => hn.2.2.1.2.2.1 e.symm) h.ne_v₃_w.symm
    · have hc : w = v₃ ∨ w = v₄ := by simpa using hwe
      exact hc.elim h.ne_v₃_w.symm (fun e => hn.2.2.2.2.1.1 e.symm)

/-- Saturation in the smaller graph supplies a retained matching edge
visible at the left chain end whenever the retained outer edge is induced. -/
theorem exists_retained_matching_visible_at_leftEnd
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    (hsat : OneSaturated (deleteFourChainCenters G v₂ v₃) small)
    (hP : transportColoringToSupergraph
      (deleteFourChainCentersLE G v₂ v₃) small
        (⟨s(u, v₁), h.left_adj⟩ : G.edgeSet) ≠ none) :
    ∃ f : G.edgeSet,
      f ∈ RetainedEdges (deleteFourChainCenters G v₂ v₃) G ∧
      transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small f = none ∧
      (f : Sym2 V) ∈ vertexVisibleEdgeFinset G v₁ := by
  obtain ⟨f, hfD, hf, z, hzP, hzf⟩ :=
    OneSaturated.transportColoringToSupergraph_retained_witness G
      (deleteFourChainCentersLE G v₂ v₃) hsat
      (⟨s(u, v₁), h.left_adj⟩ : G.edgeSet) hP
  refine ⟨f, hfD, hf,
    mem_vertexVisibleEdgeFinset_of_endpoint_close G hzf ?_⟩
  have hz : z = u ∨ z = v₁ := by simpa using hzP
  exact hz.elim (fun e => Or.inr (e ▸ h.left_adj.symm))
    (fun e => Or.inl e.symm)

/-- Symmetric retained witness at the right chain end. -/
theorem exists_retained_matching_visible_at_rightEnd
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    (hsat : OneSaturated (deleteFourChainCenters G v₂ v₃) small)
    (hQ : transportColoringToSupergraph
      (deleteFourChainCentersLE G v₂ v₃) small
        (⟨s(v₄, w), h.right_adj⟩ : G.edgeSet) ≠ none) :
    ∃ f : G.edgeSet,
      f ∈ RetainedEdges (deleteFourChainCenters G v₂ v₃) G ∧
      transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small f = none ∧
      (f : Sym2 V) ∈ vertexVisibleEdgeFinset G v₄ := by
  obtain ⟨f, hfD, hf, z, hzQ, hzf⟩ :=
    OneSaturated.transportColoringToSupergraph_retained_witness G
      (deleteFourChainCentersLE G v₂ v₃) hsat
      (⟨s(v₄, w), h.right_adj⟩ : G.edgeSet) hQ
  refine ⟨f, hfD, hf,
    mem_vertexVisibleEdgeFinset_of_endpoint_close G hzf ?_⟩
  have hz : z = v₄ ∨ z = w := by simpa using hzQ
  exact hz.elim (fun e => Or.inl e.symm)
    (fun e => Or.inr (e ▸ h.right_adj))

/-- Every honest extension pattern preserves the four-colour palette
condition.  The proof checks precisely the six affected vertices. -/
theorem conditionTwo_of_fourChain_pattern
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteFourChainCenters G v₂ v₃) small)
    (final : G.edgeSet → OneTwoColor 4)
    (hagree : ColoringsAgreeOff G
      ({(⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet),
        (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)} : Set G.edgeSet)
      (transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small) final)
    (hpattern : FourChainColourPattern G h
      (transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small) final) :
    ConditionTwo G final := by
  classical
  let H := deleteFourChainCenters G v₂ v₃
  let D : Set G.edgeSet := RetainedEdges H G
  let S : Set G.edgeSet :=
    {(⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet),
      (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet),
      (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)}
  let base := transportColoringToSupergraph
    (deleteFourChainCentersLE G v₂ v₃) small
  let P : G.edgeSet := ⟨s(u, v₁), h.left_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.first_adj⟩
  let B : G.edgeSet := ⟨s(v₂, v₃), h.middle_adj⟩
  let C : G.edgeSet := ⟨s(v₃, v₄), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(v₄, w), h.right_adj⟩
  have hbaseCondition : ConditionTwo G base := by
    simpa [base] using conditionTwo_transport_deleteFourChainCenters G hsub h
      small hsmall.paletteCondition
  have hfresh := fourChainEdges_fresh G h
  have hAD : A ∉ D := by simpa [H, D, A] using hfresh.1
  have hBD : B ∉ D := by simpa [H, D, B] using hfresh.2.1
  have hCD : C ∉ D := by simpa [H, D, C] using hfresh.2.2.1
  have houter := fourChainOuterEdges_retained G h
  have hPD : P ∈ D := by simpa [H, D, P] using houter.1
  have hQD : Q ∈ D := by simpa [H, D, Q] using houter.2
  have hPB : P ≠ B := fun heq => hBD (heq ▸ hPD)
  have hQB : Q ≠ B := fun heq => hBD (heq ▸ hQD)
  have hagreeD : ∀ f ∈ D, base f = final f := by
    intro f hf
    apply hagree
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro e
      change f = A at e
      exact hAD (e ▸ hf)
    · intro e
      change f = B at e
      exact hBD (e ▸ hf)
    · intro e
      change f = C at e
      exact hCD (e ▸ hf)
  have hleftWitness (hP : base P ≠ none) :
      ∃ f : G.edgeSet, f ∈ D ∧ final f = none ∧
        (f : Sym2 V) ∈ vertexVisibleEdgeFinset G v₁ := by
    obtain ⟨f, hfD, hf, hfvis⟩ :=
      exists_retained_matching_visible_at_leftEnd G h small hsmall.oneSaturated
        (by simpa [base, P] using hP)
    exact ⟨f, by simpa [H, D] using hfD,
      (hagreeD f (by simpa [H, D] using hfD)).symm.trans hf, hfvis⟩
  have hrightWitness (hQ : base Q ≠ none) :
      ∃ f : G.edgeSet, f ∈ D ∧ final f = none ∧
        (f : Sym2 V) ∈ vertexVisibleEdgeFinset G v₄ := by
    obtain ⟨f, hfD, hf, hfvis⟩ :=
      exists_retained_matching_visible_at_rightEnd G h small hsmall.oneSaturated
        (by simpa [base, Q] using hQ)
    exact ⟨f, by simpa [H, D] using hfD,
      (hagreeD f (by simpa [H, D] using hfD)).symm.trans hf, hfvis⟩
  have hnotTerm := matchingAffectedBy_fourChainEdges_not_terminals G h
  have hpattern' := hpattern
  dsimp [FourChainColourPattern, P, A, B, C, Q, base] at hpattern'
  apply ConditionTwo.of_agreeOff G hbaseCondition hagree
  intro q hq haffect hmatch
  have hcases := paletteAffectedBy_fourChainEdges_cases G h haffect
  rcases hcases with hq' | hq' | hq' | hq' | hq' | hq'
  · subst q
    have hmatchBase : VertexSeesMatching G base u :=
      (vertexSeesMatching_iff_of_not_affected G hagree hnotTerm.1).mpr hmatch
    rcases hpattern' with hp | hp | hp | hp
    · rcases hp with ⟨_, _, i, j, _, hA, hB, hC, hsafe, _⟩
      change final A = some i at hA
      change final B = none at hB
      change final C = some j at hC
      obtain ⟨t, ht, hit⟩ := hsafe hq hmatchBase
      apply not_vertexSeesInduced_of_three_edge_change G A B C hagree ht
      · left; simpa [hA] using hit
      · left; simp [hB]
      · right; simpa [C] using rightChainEdge_not_visible_from_leftTerminal G h
    · rcases hp with ⟨_, _, i, j, _, hA, hB, hC, hsafe, _⟩
      change final A = some i at hA
      change final B = none at hB
      change final C = some j at hC
      obtain ⟨t, ht, hit⟩ := hsafe hq hmatchBase
      apply not_vertexSeesInduced_of_three_edge_change G A B C hagree ht
      · left; simpa [hA] using hit
      · left; simp [hB]
      · right; simpa [C] using rightChainEdge_not_visible_from_leftTerminal G h
    · rcases hp with ⟨_, _, i, j, _, hA, hB, hC, hsafe, _⟩
      change final A = some i at hA
      change final B = none at hB
      change final C = some j at hC
      obtain ⟨t, ht, hit⟩ := hsafe hq hmatchBase
      apply not_vertexSeesInduced_of_three_edge_change G A B C hagree ht
      · left; simpa [hA] using hit
      · left; simp [hB]
      · right; simpa [C] using rightChainEdge_not_visible_from_leftTerminal G h
    · rcases hp with ⟨_, _, k, hA, hB, hC⟩
      change final A = none at hA
      change final B = some k at hB
      change final C = none at hC
      obtain ⟨t, ht⟩ :=
        TwoVertexPaletteCondition.exists_missing G hbaseCondition hq hmatchBase
      apply not_vertexSeesInduced_of_three_edge_change G A B C hagree ht
      · left; simp [hA]
      · right; simpa [B] using middleChainEdge_not_visible_from_leftTerminal G h
      · left; simp [hC]

  · subst q
    rcases hpattern' with hp | hp | hp | hp
    · rcases hp with ⟨hP, _, i, j, _, hA, hB, hC, _, _⟩
      apply paletteCondition_at_of_two_visible_matching_four G hsub h.first_two
        h.first_adj h.second_two P B hPB
      · exact (hagreeD P hPD).symm.trans hP
      · exact hB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [P])
          (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
          (Or.inr h.first_adj)
    · rcases hp with ⟨hP, _, i, j, _, hA, hB, hC, _, _⟩
      apply paletteCondition_at_of_two_visible_matching_four G hsub h.first_two
        h.first_adj h.second_two P B hPB
      · exact (hagreeD P hPD).symm.trans hP
      · exact hB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [P])
          (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
          (Or.inr h.first_adj)
    · rcases hp with ⟨hP, _, i, j, _, hA, hB, hC, _, _⟩
      obtain ⟨f, hfD, hf, hfvis⟩ := hleftWitness hP
      have hBf : B ≠ f := by intro e; apply hBD; rw [e]; exact hfD
      apply paletteCondition_at_of_two_visible_matching_four G hsub h.first_two
        h.first_adj h.second_two B f hBf hB hf
        (mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
          (Or.inr h.first_adj)) hfvis
    · rcases hp with ⟨hP, _, k, hA, hB, hC⟩
      obtain ⟨f, hfD, hf, hfvis⟩ := hleftWitness hP
      have hAf : A ≠ f := by intro e; apply hAD; rw [e]; exact hfD
      apply paletteCondition_at_of_two_visible_matching_four G hsub h.first_two
        h.first_adj h.second_two A f hAf hA hf
        (mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [A])
          (Or.inl rfl)) hfvis
  · subst q
    exact paletteCondition_at_of_two_two_neighbours_four G h.second_two
      h.first_adj.symm h.middle_adj h.ne_v₁_v₃ h.first_two h.third_two hmatch
  · subst q
    exact paletteCondition_at_of_two_two_neighbours_four G h.third_two
      h.middle_adj.symm h.last_adj h.ne_v₂_v₄ h.second_two h.fourth_two hmatch
  · subst q
    rcases hpattern' with hp | hp | hp | hp
    · rcases hp with ⟨_, hQ, i, j, _, hA, hB, hC, _, _⟩
      apply paletteCondition_at_of_two_visible_matching_four G hsub h.fourth_two
        h.last_adj.symm h.third_two Q B hQB
      · exact (hagreeD Q hQD).symm.trans hQ
      · exact hB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [Q])
          (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
          (Or.inr h.last_adj.symm)
    · rcases hp with ⟨_, hQ, i, j, _, hA, hB, hC, _, _⟩
      obtain ⟨f, hfD, hf, hfvis⟩ := hrightWitness hQ
      have hBf : B ≠ f := by intro e; apply hBD; rw [e]; exact hfD
      apply paletteCondition_at_of_two_visible_matching_four G hsub h.fourth_two
        h.last_adj.symm h.third_two B f hBf hB hf
        (mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
          (Or.inr h.last_adj.symm)) hfvis
    · rcases hp with ⟨_, hQ, i, j, _, hA, hB, hC, _, _⟩
      apply paletteCondition_at_of_two_visible_matching_four G hsub h.fourth_two
        h.last_adj.symm h.third_two Q B hQB
      · exact (hagreeD Q hQD).symm.trans hQ
      · exact hB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [Q])
          (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [B])
          (Or.inr h.last_adj.symm)
    · rcases hp with ⟨_, hQ, k, hA, hB, hC⟩
      obtain ⟨f, hfD, hf, hfvis⟩ := hrightWitness hQ
      have hCf : C ≠ f := by intro e; apply hCD; rw [e]; exact hfD
      apply paletteCondition_at_of_two_visible_matching_four G hsub h.fourth_two
        h.last_adj.symm h.third_two C f hCf hC hf
        (mem_vertexVisibleEdgeFinset_of_endpoint_close G (by simp [C])
          (Or.inl rfl)) hfvis
  · subst q
    have hmatchBase : VertexSeesMatching G base w :=
      (vertexSeesMatching_iff_of_not_affected G hagree hnotTerm.2).mpr hmatch
    rcases hpattern' with hp | hp | hp | hp
    · rcases hp with ⟨_, _, i, j, _, hA, hB, hC, _, hsafe⟩
      change final A = some i at hA
      change final B = none at hB
      change final C = some j at hC
      obtain ⟨t, ht, hjt⟩ := hsafe hq hmatchBase
      apply not_vertexSeesInduced_of_three_edge_change G A B C hagree ht
      · right; simpa [A] using leftChainEdge_not_visible_from_rightTerminal G h
      · left; simp [hB]
      · left; simpa [hC] using hjt
    · rcases hp with ⟨_, _, i, j, _, hA, hB, hC, _, hsafe⟩
      change final A = some i at hA
      change final B = none at hB
      change final C = some j at hC
      obtain ⟨t, ht, hjt⟩ := hsafe hq hmatchBase
      apply not_vertexSeesInduced_of_three_edge_change G A B C hagree ht
      · right; simpa [A] using leftChainEdge_not_visible_from_rightTerminal G h
      · left; simp [hB]
      · left; simpa [hC] using hjt
    · rcases hp with ⟨_, _, i, j, _, hA, hB, hC, _, hsafe⟩
      change final A = some i at hA
      change final B = none at hB
      change final C = some j at hC
      obtain ⟨t, ht, hjt⟩ := hsafe hq hmatchBase
      apply not_vertexSeesInduced_of_three_edge_change G A B C hagree ht
      · right; simpa [A] using leftChainEdge_not_visible_from_rightTerminal G h
      · left; simp [hB]
      · left; simpa [hC] using hjt
    · rcases hp with ⟨_, _, k, hA, hB, hC⟩
      change final A = none at hA
      change final B = some k at hB
      change final C = none at hC
      obtain ⟨t, ht⟩ :=
        TwoVertexPaletteCondition.exists_missing G hbaseCondition hq hmatchBase
      apply not_vertexSeesInduced_of_three_edge_change G A B C hagree ht
      · left; simp [hA]
      · right; simpa [B] using middleChainEdge_not_visible_from_rightTerminal G h
      · left; simp [hC]

/-! ## Transporting Condition 3 -/

/-- A certified 2-thread cannot use any of the four consecutive degree-two
vertices in the displayed chain. -/
theorem twoThread_avoids_fourChain
    {r s : V} {p : G.Walk r s} (hp : IsKThread G p 2)
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    v₁ ∉ p.support ∧ v₂ ∉ p.support ∧
      v₃ ∉ p.support ∧ v₄ ∉ p.support := by
  have hv₂ : v₂ ∉ p.support :=
    twoThread_avoids_twoVertex_between_twoTwo G hp h.second_two
      h.first_adj h.middle_adj h.ne_v₁_v₃ h.first_two h.third_two
  have hv₃ : v₃ ∉ p.support :=
    twoThread_avoids_twoVertex_between_twoTwo G hp h.third_two
      h.middle_adj h.last_adj h.ne_v₂_v₄ h.second_two h.fourth_two
  have hv₁ : v₁ ∉ p.support :=
    twoThread_avoids_twoVertex_of_neighbor_avoided G hp h.first_two
      h.left_adj.symm h.first_adj h.ne_u_v₂ hv₂
  have hv₄ : v₄ ∉ p.support :=
    twoThread_avoids_twoVertex_of_neighbor_avoided G hp h.fourth_two
      h.right_adj h.last_adj.symm h.ne_v₃_w.symm hv₃
  exact ⟨hv₁, hv₂, hv₃, hv₄⟩

/-- Every vertex occurrence of an ambient 2-thread is different from and
nonadjacent to both deleted chain centres. -/
theorem twoThread_vertex_far_from_fourChainCenters
    {r s : V} {p : G.Walk r s} (hp : IsKThread G p 2)
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    {y : V} (hy : y ∈ p.support) :
    y ≠ v₂ ∧ ¬ G.Adj y v₂ ∧ y ≠ v₃ ∧ ¬ G.Adj y v₃ := by
  have hav := twoThread_avoids_fourChain G hp h
  have hy₂ : y ≠ v₂ := fun e => hav.2.1 (e ▸ hy)
  have hy₃ : y ≠ v₃ := fun e => hav.2.2.1 (e ▸ hy)
  refine ⟨hy₂, ?_, hy₃, ?_⟩
  · intro hadj
    have hmem : y ∈ G.neighborFinset v₂ :=
      (G.mem_neighborFinset v₂ y).mpr hadj.symm
    rw [h.neighbors_second] at hmem
    have hc : y = v₁ ∨ y = v₃ := by simpa using hmem
    exact hc.elim (fun e => hav.1 (e ▸ hy))
      (fun e => hav.2.2.1 (e ▸ hy))
  · intro hadj
    have hmem : y ∈ G.neighborFinset v₃ :=
      (G.mem_neighborFinset v₃ y).mpr hadj.symm
    rw [h.neighbors_third] at hmem
    have hc : y = v₂ ∨ y = v₄ := by simpa using hmem
    exact hc.elim (fun e => hav.2.1 (e ▸ hy))
      (fun e => hav.2.2.2 (e ▸ hy))

/-- An ambient 2-thread transfers unchanged to the graph obtained by
deleting both chain centres. -/
theorem exists_twoThread_deleteFourChainCenters
    {r s : V} {p : G.Walk r s} (hp : IsKThread G p 2)
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w) :
    ∃ pH : (deleteFourChainCenters G v₂ v₃).Walk r s,
      IsKThread (deleteFourChainCenters G v₂ v₃) pH 2 ∧
        ∀ i, pH.getVert i = p.getVert i := by
  let H := deleteFourChainCenters G v₂ v₃
  have hav := twoThread_avoids_fourChain G hp h
  let htransfer : ∀ e, e ∈ p.edges → e ∈ H.edgeSet := by
    intro e he
    let eG : G.edgeSet := ⟨e, p.edges_subset_edgeSet he⟩
    have hv₂e : v₂ ∉ e := by
      intro hv
      exact hav.2.1 (SimpleGraph.Walk.mem_support_of_mem_edges he hv)
    have hv₃e : v₃ ∉ e := by
      intro hv
      exact hav.2.2.1 (SimpleGraph.Walk.mem_support_of_mem_edges he hv)
    change eG ∈ RetainedEdges H G
    exact (mem_retained_deleteFourChainCenters_iff G eG).mpr ⟨hv₂e, hv₃e⟩
  let pH : H.Walk r s := p.transfer H htransfer
  have hget (i : ℕ) : pH.getVert i = p.getVert i := by
    change (p.transfer H htransfer).getVert i = p.getVert i
    rw [SimpleGraph.Walk.getVert_eq_getD_support,
      SimpleGraph.Walk.getVert_eq_getD_support,
      SimpleGraph.Walk.support_transfer]
  have hlength : pH.length = p.length := by
    change (p.transfer H htransfer).length = p.length
    exact SimpleGraph.Walk.length_transfer p htransfer
  have hstartFar := twoThread_vertex_far_from_fourChainCenters G hp h
    p.start_mem_support
  have hendFar := twoThread_vertex_far_from_fourChainCenters G hp h
    p.end_mem_support
  refine ⟨pH, ?_, hget⟩
  refine ⟨hp.1.transfer htransfer, by simpa [hlength] using hp.length,
    ?_, ?_, ?_⟩
  · have hthree := hp.start_three
    unfold IsThreeVertex at hthree ⊢
    rw [degree_deleteFourChainCenters_eq_of_not_adj G hstartFar.1 hstartFar.2.1
      hstartFar.2.2.1 hstartFar.2.2.2]
    exact hthree
  · have hthree := hp.end_three
    unfold IsThreeVertex at hthree ⊢
    rw [degree_deleteFourChainCenters_eq_of_not_adj G hendFar.1 hendFar.2.1
      hendFar.2.2.1 hendFar.2.2.2]
    exact hthree
  · intro i hi0 hil
    have hilG : i < p.length := by simpa [hlength] using hil
    have hfar := twoThread_vertex_far_from_fourChainCenters G hp h
      (p.getVert_mem_support i)
    unfold IsTwoVertex
    rw [hget i, degree_deleteFourChainCenters_eq_of_not_adj G hfar.1 hfar.2.1
      hfar.2.2.1 hfar.2.2.2]
    exact IsKThread.internal_two G hp hi0 hilG

/-- Every ambient edge incident with a vertex far from both deleted centres
survives the double incidence deletion. -/
theorem edge_mem_deleteFourChainCenters_of_incident_far
    {v₂ v₃ q : V}
    (hq₂ : q ≠ v₂) (hn₂ : ¬ G.Adj q v₂)
    (hq₃ : q ≠ v₃) (hn₃ : ¬ G.Adj q v₃)
    (e : G.edgeSet) (hqe : q ∈ (e : Sym2 V)) :
    e.1 ∈ (deleteFourChainCenters G v₂ v₃).edgeSet := by
  have hv₂ : v₂ ∉ (e : Sym2 V) := by
    intro hv₂e
    apply hn₂
    exact G.adj_of_mem_incidenceSet hq₂
      ((G.edge_mem_incidenceSet_iff (e := e)).mpr hqe)
      ((G.edge_mem_incidenceSet_iff (e := e)).mpr hv₂e)
  have hv₃ : v₃ ∉ (e : Sym2 V) := by
    intro hv₃e
    apply hn₃
    exact G.adj_of_mem_incidenceSet hq₃
      ((G.edge_mem_incidenceSet_iff (e := e)).mpr hqe)
      ((G.edge_mem_incidenceSet_iff (e := e)).mpr hv₃e)
  exact (mem_retained_deleteFourChainCenters_iff G e).mpr ⟨hv₂, hv₃⟩

/-- External inducedness descends to the twice-deleted graph when the
designated thread edges correspond under the canonical inclusion. -/
theorem externalEdgesInduced_small_deleteFourChainCenters
    {v₂ v₃ q : V}
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    {threadH : (deleteFourChainCenters G v₂ v₃).edgeSet}
    {threadG : G.edgeSet}
    (hthread : edgeEmbeddingOfLE (deleteFourChainCentersLE G v₂ v₃)
      threadH = threadG)
    (hamb : ExternalEdgesInduced G
      (transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small) q threadG) :
    ExternalEdgesInduced (deleteFourChainCenters G v₂ v₃) small q
      threadH := by
  intro e he
  let eG : G.edgeSet :=
    edgeEmbeddingOfLE (deleteFourChainCentersLE G v₂ v₃) e
  have heG : IsExternalAt G q threadG eG := by
    refine ⟨he.1, ?_⟩
    intro heq
    apply he.2
    apply (edgeEmbeddingOfLE
      (deleteFourChainCentersLE G v₂ v₃)).injective
    exact heq.trans hthread.symm
  obtain ⟨i, hi⟩ := hamb eG heG
  exact ⟨i, by simpa [eG] using hi⟩

/-- At a vertex far from both deleted centres, external induced-colour
sets are exactly preserved by transport. -/
theorem externalInducedColors_deleteFourChainCenters_eq_transport
    {v₂ v₃ q : V}
    (hq₂ : q ≠ v₂) (hn₂ : ¬ G.Adj q v₂)
    (hq₃ : q ≠ v₃) (hn₃ : ¬ G.Adj q v₃)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    {threadH : (deleteFourChainCenters G v₂ v₃).edgeSet}
    {threadG : G.edgeSet}
    (hthread : edgeEmbeddingOfLE (deleteFourChainCentersLE G v₂ v₃)
      threadH = threadG) :
    ExternalInducedColors (deleteFourChainCenters G v₂ v₃) small q
        threadH =
      ExternalInducedColors G
        (transportColoringToSupergraph
          (deleteFourChainCentersLE G v₂ v₃) small) q threadG := by
  ext i
  constructor
  · rintro ⟨e, he, hi⟩
    let eG : G.edgeSet :=
      edgeEmbeddingOfLE (deleteFourChainCentersLE G v₂ v₃) e
    refine ⟨eG, ⟨he.1, ?_⟩, ?_⟩
    · intro heq
      apply he.2
      apply (edgeEmbeddingOfLE
        (deleteFourChainCentersLE G v₂ v₃)).injective
      exact heq.trans hthread.symm
    · simpa [eG] using hi
  · rintro ⟨e, he, hi⟩
    have heH : e.1 ∈ (deleteFourChainCenters G v₂ v₃).edgeSet :=
      edge_mem_deleteFourChainCenters_of_incident_far G hq₂ hn₂ hq₃ hn₃
        e he.1
    let eH : (deleteFourChainCenters G v₂ v₃).edgeSet := ⟨e.1, heH⟩
    have heEmbed : edgeEmbeddingOfLE
        (deleteFourChainCentersLE G v₂ v₃) eH = e := by
      apply Subtype.ext
      rfl
    refine ⟨eH, ⟨he.1, ?_⟩, ?_⟩
    · intro heq
      apply he.2
      have heqG : edgeEmbeddingOfLE
          (deleteFourChainCentersLE G v₂ v₃) eH =
          edgeEmbeddingOfLE (deleteFourChainCentersLE G v₂ v₃) threadH :=
        congrArg (edgeEmbeddingOfLE
          (deleteFourChainCentersLE G v₂ v₃)) heq
      exact heEmbed.symm.trans (heqG.trans hthread)
    · rw [← heEmbed] at hi
      simpa [eH] using hi

/-- Condition 3 transports honestly across deletion of the two middle
vertices of a four-chain. -/
theorem conditionThree_transport_deleteFourChainCenters
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    (hsmall : ConditionThree (deleteFourChainCenters G v₂ v₃) small) :
    ConditionThree G (transportColoringToSupergraph
      (deleteFourChainCentersLE G v₂ v₃) small) := by
  intro r s p hp hleft hright
  obtain ⟨pH, hpH, hget⟩ :=
    exists_twoThread_deleteFourChainCenters G hp h
  let firstH : (deleteFourChainCenters G v₂ v₃).edgeSet :=
    threadFirstEdge (deleteFourChainCenters G v₂ v₃) pH hpH
  let firstG : G.edgeSet := threadFirstEdge G p hp
  let lastH : (deleteFourChainCenters G v₂ v₃).edgeSet :=
    threadLastEdge (deleteFourChainCenters G v₂ v₃) pH hpH
  let lastG : G.edgeSet := threadLastEdge G p hp
  have hfirst : edgeEmbeddingOfLE (deleteFourChainCentersLE G v₂ v₃)
      firstH = firstG := by
    apply Subtype.ext
    simp [firstH, firstG, threadFirstEdge, hget]
  have hlast : edgeEmbeddingOfLE (deleteFourChainCentersLE G v₂ v₃)
      lastH = lastG := by
    apply Subtype.ext
    simp [lastH, lastG, threadLastEdge, hget]
  have hleftH : ExternalEdgesInduced (deleteFourChainCenters G v₂ v₃)
      small r firstH := by
    apply externalEdgesInduced_small_deleteFourChainCenters G small hfirst
    simpa [firstG] using hleft
  have hrightH : ExternalEdgesInduced (deleteFourChainCenters G v₂ v₃)
      small s lastH := by
    apply externalEdgesInduced_small_deleteFourChainCenters G small hlast
    simpa [lastG] using hright
  have hneH := hsmall r s pH hpH hleftH hrightH
  have hrFar := twoThread_vertex_far_from_fourChainCenters G hp h
    p.start_mem_support
  have hsFar := twoThread_vertex_far_from_fourChainCenters G hp h
    p.end_mem_support
  have hleftEq := externalInducedColors_deleteFourChainCenters_eq_transport G
    hrFar.1 hrFar.2.1 hrFar.2.2.1 hrFar.2.2.2 small hfirst
  have hrightEq := externalInducedColors_deleteFourChainCenters_eq_transport G
    hsFar.1 hsFar.2.1 hsFar.2.2.1 hsFar.2.2.2 small hlast
  simpa [firstH, firstG, lastH, lastG, hleftEq, hrightEq] using hneH

/-- None of the three recoloured chain edges can be external at an endpoint
of a certified 2-thread: every endpoint of such a chain edge has degree two,
whereas a certified thread endpoint has degree three. -/
theorem not_threadConditionAffectedBy_fourChainEdges
    {u v₁ v₂ v₃ v₄ w r s : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (p : G.Walk r s) (hp : IsKThread G p 2) :
    ¬ ThreadConditionAffectedBy G
      ({(⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet),
        (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)} : Set G.edgeSet)
      p hp := by
  intro haffect
  rcases haffect with ⟨e, he, her⟩ | ⟨e, he, hes⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · have hr : r = v₁ ∨ r = v₂ := by simpa using her.1
      exact hr.elim
        (isThreeVertex_ne_isTwoVertex G hp.start_three h.first_two)
        (isThreeVertex_ne_isTwoVertex G hp.start_three h.second_two)
    · have hr : r = v₂ ∨ r = v₃ := by simpa using her.1
      exact hr.elim
        (isThreeVertex_ne_isTwoVertex G hp.start_three h.second_two)
        (isThreeVertex_ne_isTwoVertex G hp.start_three h.third_two)
    · have hr : r = v₃ ∨ r = v₄ := by simpa using her.1
      exact hr.elim
        (isThreeVertex_ne_isTwoVertex G hp.start_three h.third_two)
        (isThreeVertex_ne_isTwoVertex G hp.start_three h.fourth_two)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · have hs : s = v₁ ∨ s = v₂ := by simpa using hes.1
      exact hs.elim
        (isThreeVertex_ne_isTwoVertex G hp.end_three h.first_two)
        (isThreeVertex_ne_isTwoVertex G hp.end_three h.second_two)
    · have hs : s = v₂ ∨ s = v₃ := by simpa using hes.1
      exact hs.elim
        (isThreeVertex_ne_isTwoVertex G hp.end_three h.second_two)
        (isThreeVertex_ne_isTwoVertex G hp.end_three h.third_two)
    · have hs : s = v₃ ∨ s = v₄ := by simpa using hes.1
      exact hs.elim
        (isThreeVertex_ne_isTwoVertex G hp.end_three h.third_two)
        (isThreeVertex_ne_isTwoVertex G hp.end_three h.fourth_two)

/-- A local four-chain extension preserves Condition 3. -/
theorem conditionThree_of_fourChain_extension
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteFourChainCenters G v₂ v₃) small)
    (final : G.edgeSet → OneTwoColor 4)
    (hagree : ColoringsAgreeOff G
      ({(⟨s(v₁, v₂), h.first_adj⟩ : G.edgeSet),
        (⟨s(v₂, v₃), h.middle_adj⟩ : G.edgeSet),
        (⟨s(v₃, v₄), h.last_adj⟩ : G.edgeSet)} : Set G.edgeSet)
      (transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small) final) :
    ConditionThree G final := by
  have hbase : ConditionThree G
      (transportColoringToSupergraph
        (deleteFourChainCentersLE G v₂ v₃) small) :=
    conditionThree_transport_deleteFourChainCenters G h small
      hsmall.conditionThree
  apply ConditionThree.of_agreeOff G hbase hagree
  intro r s p hp haffect
  exact False.elim
    ((not_threadConditionAffectedBy_fourChainEdges G h p hp) haffect)

/-! ## Complete local reduction -/

/-- Every good colouring of the graph obtained by deleting the two middle
vertices of a four-chain extends to a good four-colouring of the ambient
graph. -/
theorem exists_goodFour_of_deleteFourChainCenters
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ v₄ w : V}
    (h : FourChainNeighborhood G u v₁ v₂ v₃ v₄ w)
    (small : (deleteFourChainCenters G v₂ v₃).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteFourChainCenters G v₂ v₃) small) :
    ∃ final : G.edgeSet → OneTwoColor 4, GoodFour G final := by
  obtain ⟨final, hvalid, hagree, hpattern⟩ :=
    exists_valid_fourChain_extension G hsub h small hsmall
  refine ⟨final, hvalid, ?_, ?_, ?_⟩
  · exact oneSaturated_of_fourChain_pattern G h small hsmall.oneSaturated
      final hagree hpattern
  · exact conditionTwo_of_fourChain_pattern G hsub h small hsmall final
      hagree hpattern
  · exact conditionThree_of_fourChain_extension G h small hsmall final hagree

/-! ## From a certified four-chain to the six-vertex neighbourhood -/

/-- In girth at least sixteen, the endpoints of a path of length between
two and fourteen cannot be adjacent. -/
theorem not_adj_endpoints_of_short_path
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

/-- Girth supplies the two genuinely external neighbours and proves that
the resulting six displayed vertices are all different. -/
theorem IsKChain.exists_fourChainNeighborhood
    {v₁ v₄ : V} {p : G.Walk v₁ v₄}
    (hp : IsKChain G p 4) (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    ∃ u w : V,
      FourChainNeighborhood G u v₁ (p.getVert 1) (p.getVert 2) v₄ w := by
  let v₂ : V := p.getVert 1
  let v₃ : V := p.getVert 2
  have hcore : FourChainCore G v₁ v₂ v₃ v₄ := by
    simpa [v₂, v₃] using hp.fourChainCore G
  have hlen : p.length = 3 := by
    have := hp.length
    omega
  obtain ⟨u, hu₂, hv₁u⟩ :=
    exists_other_neighbor_of_isTwoVertex G hcore.first_two hcore.first_adj
  obtain ⟨w, hw₃, hv₄w⟩ :=
    exists_other_neighbor_of_isTwoVertex G hcore.fourth_two
      hcore.last_adj.symm
  have hu₁ : u ≠ v₁ := hv₁u.ne.symm
  have hu₃ : u ≠ v₃ := by
    intro huv₃
    let q : G.Walk v₁ v₃ :=
      Walk.cons hcore.first_adj hcore.middle_adj.toWalk
    have hqPath : q.IsPath := by
      apply (Walk.IsPath.of_adj hcore.middle_adj).cons
      simp [hcore.first_adj.ne, hcore.ne₁₃]
    have hclose : G.Adj v₃ v₁ := by
      simpa [huv₃] using hv₁u.symm
    exact not_adj_endpoints_of_short_path G hgirth hqPath
      (by simp [q]) (by simp [q]) hclose
  have hu₄ : u ≠ v₄ := by
    intro huv₄
    have hclose : G.Adj v₄ v₁ := by
      simpa [huv₄] using hv₁u.symm
    exact not_adj_endpoints_of_short_path G hgirth hp.1
      (by omega) (by omega) hclose
  have hv₂w : v₂ ≠ w := by
    intro hv₂w
    let q : G.Walk v₂ v₄ :=
      Walk.cons hcore.middle_adj hcore.last_adj.toWalk
    have hqPath : q.IsPath := by
      apply (Walk.IsPath.of_adj hcore.last_adj).cons
      simp [hcore.middle_adj.ne, hcore.ne₂₄]
    have hclose : G.Adj v₄ v₂ := by
      simpa [hv₂w] using hv₄w
    exact not_adj_endpoints_of_short_path G hgirth hqPath
      (by simp [q]) (by simp [q]) hclose
  have hv₁w : v₁ ≠ w := by
    intro hv₁w
    have hclose : G.Adj v₄ v₁ := by
      simpa [hv₁w] using hv₄w
    exact not_adj_endpoints_of_short_path G hgirth hp.1
      (by omega) (by omega) hclose
  have hv₃w : v₃ ≠ w := hw₃.symm
  have huw : u ≠ w := by
    intro huw
    have huSupport : u ∉ p.support := by
      intro hup
      obtain ⟨i, hi, hil⟩ :=
        Walk.mem_support_iff_exists_getVert.mp hup
      have hicases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
        omega
      rcases hicases with rfl | rfl | rfl | rfl
      · apply hu₁
        simpa using hi.symm
      · apply hu₂
        simpa [v₂] using hi.symm
      · apply hu₃
        simpa [v₃] using hi.symm
      · apply hu₄
        have hend : p.getVert 3 = v₄ := by
          rw [← hlen]
          exact p.getVert_length
        exact hi.symm.trans hend
    let q : G.Walk u v₄ := Walk.cons hv₁u.symm p
    have hqPath : q.IsPath := hp.1.cons huSupport
    have hclose : G.Adj v₄ u := by
      simpa [huw] using hv₄w
    exact not_adj_endpoints_of_short_path G hgirth hqPath
      (by simp [q, hlen]) (by simp [q, hlen]) hclose
  refine ⟨u, w, hcore.first_two, hcore.second_two, hcore.third_two,
    hcore.fourth_two, hv₁u.symm, hcore.first_adj, hcore.middle_adj,
    hcore.last_adj, hv₄w, ?_⟩
  simp [v₂, v₃, hu₁, hu₂, hu₃, hu₄, huw,
    hcore.first_adj.ne, hcore.ne₁₃, hcore.ne₁₄, hv₁w,
    hcore.middle_adj.ne, hcore.ne₂₄, hv₂w,
    hcore.last_adj.ne, hv₃w, hv₄w.ne]

/-! ## Hereditary structural inputs and strict decrease -/

theorem isSubcubic_deleteFourChainCenters {v₂ v₃ : V}
    (hsub : IsSubcubic G) :
    IsSubcubic (deleteFourChainCenters G v₂ v₃) := by
  intro q
  exact ((deleteFourChainCenters G v₂ v₃).degree_le_of_le
    (deleteFourChainCentersLE G v₂ v₃)).trans (hsub q)

theorem egirth_deleteFourChainCenters {v₂ v₃ : V}
    (hgirth : (16 : ℕ∞) ≤ G.egirth) :
    (16 : ℕ∞) ≤ (deleteFourChainCenters G v₂ v₃).egirth :=
  hgirth.trans (egirth_anti (deleteFourChainCentersLE G v₂ v₃))

theorem edgeCount_deleteFourChainCenters_lt
    {v₂ v₃ : V} (hincident : ∃ e : G.edgeSet, v₂ ∈ (e : Sym2 V)) :
    EdgeCount (deleteFourChainCenters G v₂ v₃) < EdgeCount G := by
  have hle : EdgeCount (deleteFourChainCenters G v₂ v₃) ≤
      EdgeCount (G.deleteIncidenceSet v₂) := by
    rw [edgeCount_eq_edgeFinset_card, edgeCount_eq_edgeFinset_card]
    exact Finset.card_le_card
      (edgeFinset_mono ((G.deleteIncidenceSet v₂).deleteIncidenceSet_le v₃))
  exact hle.trans_lt (edgeCount_deleteIncidenceSet_lt (G := G) hincident)

end Finite

section DecidableIrrel

variable [Fintype V]

/-- Subcubicity is semantic and hence independent of the procedure used to
decide adjacency. -/
theorem isSubcubic_change_decidableRel_fourChain
    (d₁ d₂ : DecidableRel G.Adj)
    (h : @IsSubcubic V G _ d₁) : @IsSubcubic V G _ d₂ := by
  intro q
  have hqCard : Nat.card (G.neighborSet q) ≤ 3 := by
    letI : DecidableRel G.Adj := d₁
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
    exact h q
  letI : DecidableRel G.Adj := d₂
  rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  exact hqCard

end DecidableIrrel

/-! ## Minimal-counterexample wrapper

The sole global structural input separated in the first theorem below is
planarity heredity for the twice-deleted spanning subgraph.  Keeping it as a
parameter lets the complete colouring reduction remain independent of the
rotation-system implementation used to establish that heredity. -/

section ClassicalMinimal

variable [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1600000 in
theorem IsEdgeMinimalBad.no_four_chain_sectionFour_of_delete_planar
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G)
    (hdeletePlanar : ∀ v₂ v₃ : V,
      IsCombinatoriallyPlanar (deleteFourChainCenters G v₂ v₃))
    {v₁ v₄ : V} (p : G.Walk v₁ v₄) :
    ¬ @IsKChain V G _ (Classical.decRel G.Adj) v₁ v₄ p 4 := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  intro hp
  have hEligibleG : IsSubcubic G ∧ IsCombinatoriallyPlanar G ∧
      (16 : ℕ∞) ≤ G.egirth := by
    simpa [SectionFourEligible] using hmin.eligible
  obtain ⟨u, w, hneighborhood⟩ :=
    hp.exists_fourChainNeighborhood G hEligibleG.2.2
  let v₂ : V := p.getVert 1
  let v₃ : V := p.getVert 2
  let H : SimpleGraph V := deleteFourChainCenters G v₂ v₃
  have hsubH : IsSubcubic H := by
    simpa [H] using isSubcubic_deleteFourChainCenters G
      (v₂ := v₂) (v₃ := v₃) hEligibleG.1
  have hsubHClassical :
      @IsSubcubic V H _ (Classical.decRel H.Adj) :=
    isSubcubic_change_decidableRel_fourChain H inferInstance
      (Classical.decRel H.Adj) hsubH
  have hEligibleH : SectionFourEligible H := by
    rw [SectionFourEligible]
    refine ⟨hsubHClassical, ?_, ?_⟩
    · simpa [H] using hdeletePlanar v₂ v₃
    · simpa [H] using (egirth_deleteFourChainCenters G
        (v₂ := v₂) (v₃ := v₃) hEligibleG.2.2)
  have hincident : ∃ e : G.edgeSet, v₂ ∈ (e : Sym2 V) :=
    ⟨⟨s(v₁, v₂), hneighborhood.first_adj⟩, by simp⟩
  have hsmaller : EdgeCount H < EdgeCount G := by
    simpa [H] using edgeCount_deleteFourChainCenters_lt G
      (v₂ := v₂) (v₃ := v₃) hincident
  have hgoodH : HasGoodFour H :=
    hmin.good_of_smaller hEligibleH hsmaller
  rw [HasGoodFour] at hgoodH
  obtain ⟨small, hsmallClassical⟩ := hgoodH
  have hsmall : GoodFour H small := by
    apply goodFour_change_decidableRel
      (G := H) (Classical.decRel H.Adj) inferInstance small
    exact hsmallClassical
  have hneighborhood' :
      FourChainNeighborhood G u v₁ v₂ v₃ v₄ w := by
    simpa [v₂, v₃] using hneighborhood
  obtain ⟨final, hfinal⟩ :=
    exists_goodFour_of_deleteFourChainCenters G hEligibleG.1
      hneighborhood' small (by simpa [H] using hsmall)
  apply hmin.not_good
  rw [HasGoodFour]
  exact ⟨final, hfinal⟩

/-- Lemma 4.3 with the planarity side condition discharged by the hereditary
theorem for combinatorial planarity. -/
theorem IsEdgeMinimalBad.no_four_chain_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G)
    {v₁ v₄ : V} (p : G.Walk v₁ v₄) :
    ¬ @IsKChain V G _ (Classical.decRel G.Adj) v₁ v₄ p 4 := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hEligibleG : IsSubcubic G ∧ IsCombinatoriallyPlanar G ∧
      (16 : ℕ∞) ≤ G.egirth := by
    simpa [SectionFourEligible] using hmin.eligible
  apply hmin.no_four_chain_sectionFour_of_delete_planar
  intro v₂ v₃
  exact hEligibleG.2.1.mono (deleteFourChainCentersLE G v₂ v₃)

end ClassicalMinimal

end


end LeanCo.PackingEdgeColoring
