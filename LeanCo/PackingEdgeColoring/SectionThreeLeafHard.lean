import LeanCo.PackingEdgeColoring.SectionThreeMinDegree
import LeanCo.PackingEdgeColoring.SectionThreeTwoOneOne

/-!
# The degree-three hard branch of the Section 3 leaf reduction

This file completes Lemma 3.3.  The deleted leaf edge is restored from an
arbitrary good colouring of the smaller graph.  All palette checks are made
in the ambient graph; no unstated girth or endpoint-distinctness hypothesis
is used.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-! ## The deleted neighbour is a two-vertex -/

theorem deleteLeafEdge_adj_neighbor_iff {u v z : V}
    (huv : G.Adj u v) :
    (deleteLeafEdge G huv).Adj v z ↔ G.Adj v z ∧ z ≠ u := by
  rw [deleteLeafEdge, SimpleGraph.deleteEdges_adj]
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hvz, hnot⟩
    refine ⟨hvz, ?_⟩
    intro hzu
    subst z
    exact hnot (by simp [Sym2.eq_swap])
  · rintro ⟨hvz, hzu⟩
    refine ⟨hvz, ?_⟩
    intro heq
    have humem : u ∈ (s(v, z) : Sym2 V) := by rw [heq]; simp
    have hu : u = v ∨ u = z := by simpa using humem
    exact hu.elim huv.ne (fun huz ↦ hzu huz.symm)

theorem neighborFinset_deleteLeafEdge_at_neighbor {u v : V}
    (huv : G.Adj u v) :
    (deleteLeafEdge G huv).neighborFinset v =
      (G.neighborFinset v).erase u := by
  ext z
  simp only [Finset.mem_erase]
  rw [(deleteLeafEdge G huv).mem_neighborFinset,
    G.mem_neighborFinset, deleteLeafEdge_adj_neighbor_iff G huv]
  tauto

theorem isTwoVertex_deleteLeafEdge_at_three_neighbor {u v : V}
    (huv : G.Adj u v) (hv : IsThreeVertex G v) :
    IsTwoVertex (deleteLeafEdge G huv) v := by
  have huN : u ∈ G.neighborFinset v :=
    (G.mem_neighborFinset v u).mpr huv.symm
  unfold IsTwoVertex
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_deleteLeafEdge_at_neighbor G huv,
    Finset.card_erase_of_mem huN,
    SimpleGraph.card_neighborFinset_eq_degree, hv]

/-! ## Visibility at the degree-three endpoint -/

theorem vertexSeesInduced_transport_deleteLeafEdge_at_neighbor_iff
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (i : Fin 5) :
    VertexSeesInduced G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small) v i ↔
      VertexSeesInduced (deleteLeafEdge G huv) small v i := by
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
  rw [vertexSeesInduced_iff, vertexSeesInduced_iff]
  constructor
  · rintro ⟨e, hecolour, z, hze, hvz⟩
    have heD : e ∈ RetainedEdges (deleteLeafEdge G huv) G := by
      by_contra heNot
      have heq : e = (⟨s(u, v), huv⟩ : G.edgeSet) := by
        by_contra hne
        exact heNot ((mem_retained_deleteLeafEdge_iff G huv e).mpr hne)
      subst e
      simp [base, transportColoringToSupergraph] at hecolour
    let eH : (deleteLeafEdge G huv).edgeSet := ⟨e.1, heD⟩
    refine ⟨eH, ?_, z, hze, ?_⟩
    · rw [transportColoringToSupergraph_of_mem
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small heD] at hecolour
      exact hecolour
    · rcases hvz with rfl | hvz
      · exact Or.inl rfl
      · right
        apply (deleteLeafEdge_adj_neighbor_iff G huv).mpr
        refine ⟨hvz, ?_⟩
        intro hzu
        subst z
        let eSmall : (deleteLeafEdge G huv).edgeSet := ⟨e.1, heD⟩
        exact no_retained_edge_incident_leaf G hu huv eSmall hze
  · rintro ⟨e, hecolour, z, hze, hvz⟩
    let eG := edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) e
    refine ⟨eG, by simpa [eG, base] using hecolour, z, hze, ?_⟩
    exact hvz.imp_right (fun h ↦
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) h)

/-- Condition I at the newly degree-two vertex in the deleted graph supplies
an induced colour available on the missing leaf edge. -/
theorem exists_available_leafEdge_at_three_neighbor
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteLeafEdge G huv) small)
    (hmatch : VertexSeesMatching (deleteLeafEdge G huv) small v) :
    ∃ i : Fin 5, ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i) := by
  have hvTwo := isTwoVertex_deleteLeafEdge_at_three_neighbor G huv hv
  have hmissing := hsmall.2 v hvTwo hmatch
  push_neg at hmissing
  obtain ⟨i, hi⟩ := hmissing
  refine ⟨i, induced_available_leafEdge_of_not_seen_at_neighbor G hu huv _
    (fun _ h ↦ h) _ i ?_⟩
  intro hseen
  apply hi
  exact (vertexSeesInduced_transport_deleteLeafEdge_at_neighbor_iff
    G hu huv small i).mp hseen

/-! ## A colour can endanger a fixed two-vertex only once -/

theorem vertexSeesMatching_of_recolor_leafEdge_induced
    {u v q : V} (huv : G.Adj u v)
    (base : G.edgeSet → OneTwoColor 5)
    (hE : base (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (i : Fin 5)
    (hmatch : VertexSeesMatching G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q) :
    VertexSeesMatching G base q := by
  rw [vertexSeesMatching_iff] at hmatch ⊢
  obtain ⟨f, hf, hqf⟩ := hmatch
  by_cases hfE : f = (⟨s(u, v), huv⟩ : G.edgeSet)
  · subst f
    simp at hf
  · exact ⟨f, by simpa [recolor, hfE] using hf, hqf⟩

theorem vertexSeesInduced_of_recolor_leafEdge_other
    {u v q : V} (huv : G.Adj u v)
    (base : G.edgeSet → OneTwoColor 5)
    {i j : Fin 5} (hji : j ≠ i)
    (hseen : VertexSeesInduced G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q j) :
    VertexSeesInduced G base q j := by
  rw [vertexSeesInduced_iff] at hseen ⊢
  obtain ⟨f, hf, z, hzf, hqz⟩ := hseen
  by_cases hfE : f = (⟨s(u, v), huv⟩ : G.edgeSet)
  · subst f
    have : some i = some j := by simpa using hf
    exact False.elim (hji (Option.some.inj this).symm)
  · exact ⟨f, by simpa [recolor, hfE] using hf, z, hzf, hqz⟩

theorem not_full_palette_base_of_full_after_leaf_colour
    {u v q : V} (huv : G.Adj u v)
    (base : G.edgeSet → OneTwoColor 5)
    (hcondition : ConditionI G base) (hq : IsTwoVertex G q)
    (hE : base (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    (i : Fin 5)
    (hmatch : VertexSeesMatching G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q)
    (hall : ∀ j : Fin 5, VertexSeesInduced G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q j) :
    ¬ VertexSeesInduced G base q i := by
  have hmatchBase := vertexSeesMatching_of_recolor_leafEdge_induced G huv base
    hE i hmatch
  intro hi
  apply hcondition q hq hmatchBase
  intro j
  by_cases hji : j = i
  · simpa [hji] using hi
  · exact vertexSeesInduced_of_recolor_leafEdge_other G huv base hji
      (hall j)

theorem full_palette_leaf_colour_unique_at_two
    {u v q : V} (huv : G.Adj u v)
    (base : G.edgeSet → OneTwoColor 5)
    (hcondition : ConditionI G base) (hq : IsTwoVertex G q)
    (hE : base (⟨s(u, v), huv⟩ : G.edgeSet) = none)
    {i j : Fin 5} (hij : i ≠ j)
    (hmatchI : VertexSeesMatching G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q)
    (hallI : ∀ t : Fin 5, VertexSeesInduced G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q t)
    (hmatchJ : VertexSeesMatching G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) q)
    (hallJ : ∀ t : Fin 5, VertexSeesInduced G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) q t) :
    False := by
  have hiMissing := not_full_palette_base_of_full_after_leaf_colour G huv base
    hcondition hq hE i hmatchI hallI
  apply hiMissing
  exact vertexSeesInduced_of_recolor_leafEdge_other G huv base hij
    (hallJ i)

/-! ## The local blocking neighbourhood -/

/-- Every active induced blocker of the missing leaf edge is incident with
one of the two nonleaf neighbours of its degree-three endpoint. -/
theorem activeBlockers_leafEdge_subset_other_incidence
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hN : G.neighborFinset v = {u, a, b})
    {colour : G.edgeSet → OneTwoColor 5} :
    activeInducedBlockerEdgesOn G
        (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet) ⊆
      incidentEdgeFinset G a ∪ incidentEdgeFinset G b := by
  classical
  intro f hf
  have hf' := (mem_activeInducedBlockerEdgesOn G
    (RetainedEdges (deleteLeafEdge G huv) G) colour
    (⟨s(u, v), huv⟩ : G.edgeSet) f).mp hf
  have noU (huf : u ∈ (f : Sym2 V)) : False := by
    let fH : (deleteLeafEdge G huv).edgeSet := ⟨f.1, hf'.1⟩
    exact no_retained_edge_incident_leaf G hu huv fH huf
  have putA (haf : a ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G a ∪ incidentEdgeFinset G b :=
    Finset.mem_union_left _ ((mem_incidentEdgeFinset (G := G)).mpr haf)
  have putB (hbf : b ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G a ∪ incidentEdgeFinset G b :=
    Finset.mem_union_right _ ((mem_incidentEdgeFinset (G := G)).mpr hbf)
  have putV (hvf : v ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G a ∪ incidentEdgeFinset G b := by
    rcases retained_edge_incident_three_eq_first_or_second G huv hva hvb hN
        f hf'.1 hvf with rfl | rfl
    · exact putA (by simp)
    · exact putB (by simp)
  have putNeighborOfV {q : V} (hvq : G.Adj v q)
      (hqf : q ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G a ∪ incidentEdgeFinset G b := by
    have hqN : q ∈ ({u, a, b} : Finset V) := by
      rw [← hN]
      exact (G.mem_neighborFinset v q).mpr hvq
    have hq : q = u ∨ q = a ∨ q = b := by simpa using hqN
    rcases hq with rfl | rfl | rfl
    · exact False.elim (noU hqf)
    · exact putA hqf
    · exact putB hqf
  by_cases hdisj : EndpointDisjoint G
      (⟨s(u, v), huv⟩ : G.edgeSet) f
  · have hcross : HasCrossEdge G (⟨s(u, v), huv⟩ : G.edgeSet) f := by
      by_contra hn
      exact hf'.2.2.1 ⟨hdisj, hn⟩
    obtain ⟨p, hp, q, hqf, hpq⟩ := hcross
    have hp' : p = u ∨ p = v := by simpa using hp
    rcases hp' with hpu | hpv
    · have huq : G.Adj u q := by simpa [hpu] using hpq
      have hqv : q = v := eq_neighbor_of_degree_eq_one G hu huv huq
      exact putV (hqv ▸ hqf)
    · exact putNeighborOfV (by simpa [hpv] using hpq) hqf
  · have hshared : ∃ p, p ∈ (s(u, v) : Sym2 V) ∧ p ∈ (f : Sym2 V) := by
      by_contra hn
      apply hdisj
      intro p hp hpf
      exact hn ⟨p, hp, hpf⟩
    obtain ⟨p, hp, hpf⟩ := hshared
    have hp' : p = u ∨ p = v := by simpa using hp
    exact hp'.elim (fun h ↦ False.elim (noU (h ▸ hpf)))
      (fun h ↦ putV (h ▸ hpf))

/-- Removing one known matching edge from the two incidence sets gives the
sharp active-blocker count used below. -/
theorem card_activeBlockers_leafEdge_add_one_le
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hN : G.neighborFinset v = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 5)
    (hAnone : colour (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    (activeInducedBlockerEdgesOn G
        (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet)).card + 1 ≤
      G.degree a + G.degree b := by
  classical
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let S : Finset G.edgeSet :=
    incidentEdgeFinset G a ∪ incidentEdgeFinset G b
  have hsub : activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) ⊆ S := by
    simpa [S] using activeBlockers_leafEdge_subset_other_incidence G hu huv
      hva hvb hN (colour := colour)
  have hsubErase : activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) ⊆ S.erase A := by
    intro f hf
    apply Finset.mem_erase.mpr
    refine ⟨?_, hsub hf⟩
    intro hfA
    subst f
    exact ((mem_activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) A).mp hf).2.2.2 hAnone
  have hAmem : A ∈ S := by
    apply Finset.mem_union_left
    apply (mem_incidentEdgeFinset (G := G)).mpr
    simp [A]
  have hScard : S.card ≤ G.degree a + G.degree b := by
    calc
      S.card ≤ (incidentEdgeFinset G a).card +
          (incidentEdgeFinset G b).card := by
        simpa [S] using Finset.card_union_le
          (incidentEdgeFinset G a) (incidentEdgeFinset G b)
      _ = G.degree a + G.degree b := by
        rw [card_incidentEdgeFinset, card_incidentEdgeFinset]
  have herase : (S.erase A).card + 1 = S.card := by
    rw [Finset.card_erase_of_mem hAmem]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨A, hAmem⟩
    omega
  calc
    (activeInducedBlockerEdgesOn G
        (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet)).card + 1 ≤
        (S.erase A).card + 1 :=
      Nat.add_le_add_right (Finset.card_le_card hsubErase) 1
    _ = S.card := herase
    _ ≤ G.degree a + G.degree b := hScard

/-! ## Preserving Condition I after the ordinary extension -/

theorem conditionI_recolor_leafEdge_at_three_neighbor
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v) (hv : IsThreeVertex G v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hN : G.neighborFinset v = {u, a, b})
    (base : G.edgeSet → OneTwoColor 5) (hcondition : ConditionI G base)
    (i : Fin 5)
    (hsafeA : IsTwoVertex G a → VertexSeesMatching G
        (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a →
      ¬ ∀ j : Fin 5, VertexSeesInduced G
        (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j)
    (hsafeB : IsTwoVertex G b → VertexSeesMatching G
        (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b →
      ¬ ∀ j : Fin 5, VertexSeesInduced G
        (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j) :
    ConditionI G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  apply hcondition.recolor_of_local G
  intro q hq haffect hmatch
  have haffect' : q ∈ (E : Sym2 V) ∨
      ∃ p, p ∈ (E : Sym2 V) ∧ (q = p ∨ G.Adj q p) := by
    simpa [E] using haffect
  have hnear : q = u ∨ q = v ∨ G.Adj q u ∨ G.Adj q v := by
    rcases haffect' with hqE | ⟨p, hpE, hqp⟩
    · have hq : q = u ∨ q = v := by simpa [E] using hqE
      exact hq.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
    · have hp : p = u ∨ p = v := by simpa [E] using hpE
      rcases hp with rfl | rfl
      · exact hqp.elim Or.inl (fun h ↦ Or.inr (Or.inr (Or.inl h)))
      · exact hqp.elim (fun h ↦ Or.inr (Or.inl h))
          (fun h ↦ Or.inr (Or.inr (Or.inr h)))
  rcases hnear with hqu | hqv | hqu | hqv
  · subst q
    unfold IsTwoVertex at hq
    omega
  · subst q
    unfold IsTwoVertex at hq
    unfold IsThreeVertex at hv
    omega
  · have hqv' : q = v :=
      eq_neighbor_of_degree_eq_one G hu huv hqu.symm
    subst q
    unfold IsTwoVertex at hq
    unfold IsThreeVertex at hv
    omega
  · have hqN : q ∈ ({u, a, b} : Finset V) := by
      rw [← hN]
      exact (G.mem_neighborFinset v q).mpr hqv.symm
    have hq' : q = u ∨ q = a ∨ q = b := by simpa using hqN
    rcases hq' with rfl | rfl | rfl
    · unfold IsTwoVertex at hq
      omega
    · exact hsafeA hq hmatch
    · exact hsafeB hq hmatch

/-- The nonmatching branch is automatically safe: if its degree-two first
vertex sees a matching edge, that edge and the matching edge at `v` are two
distinct visible matching witnesses. -/
theorem palette_safe_other_neighbor_of_first_matching
    (hsub : IsSubcubic G)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b)
    (base : G.edgeSet → OneTwoColor 5)
    (hAnone : base (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    {u : V} (huv : G.Adj u v) (hau : a ≠ u) (i : Fin 5)
    (hb : IsTwoVertex G b)
    (hmatch : VertexSeesMatching G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b) :
    ¬ ∀ j : Fin 5, VertexSeesInduced G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j := by
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let after := recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)
  obtain ⟨m, hm, hbm⟩ := (vertexSeesMatching_iff G after b).mp hmatch
  have hAafter : after A = none := by
    have hAE : A ≠ (⟨s(u, v), huv⟩ : G.edgeSet) := by
      intro heq
      have humem : u ∈ (A : Sym2 V) := by
        rw [heq]
        simp
      have huva : u = v ∨ u = a := by simpa [A] using humem
      exact huva.elim huv.ne (fun h ↦ hau h.symm)
    simpa [after, A, hAE] using hAnone
  have hAm : A ≠ m := by
    intro hEq
    have hba : b = v ∨ b = a := by
      have : b ∈ (A : Sym2 V) := hEq ▸ hbm
      simpa [A] using this
    exact hba.elim (fun h ↦ hvb.ne h.symm) (fun h ↦ hab h.symm)
  apply paletteCondition_at_of_two_visible_matching G hsub hb A m hAm
    hAafter hm
  · apply mem_vertexVisibleEdgeFinset_of_endpoint_close G
      (show v ∈ (A : Sym2 V) by simp [A])
    exact Or.inr hvb.symm
  · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G hbm (Or.inl rfl)

/-- Package validity and a separately checked Condition I after assigning an
available induced colour to the missing leaf edge. -/
theorem goodFive_recolor_leafEdge_of_available
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteLeafEdge G huv) small)
    (i : Fin 5)
    (havail : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hcondition : ConditionI G
      (recolor G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i))) :
    GoodFive G
      (recolor G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
  have hvalidD : IsOneTwoColoringOn G D base :=
    transport_deleteLeafEdge_valid G hu huv small hsmall.1
  have htotal := hvalidD.extend_one G (leafEdge_not_mem_retained G huv)
    (by simpa [D, base, E] using havail)
  rw [insert_leafEdge_retained_eq_univ G huv] at htotal
  exact ⟨by simpa [IsOneTwoColoring, base, E] using htotal, hcondition⟩

/-- Ordinary leaf extension once the matching-side degree-two vertex (if
there is one) has been checked.  The other branch is automatically safe by
the two-visible-matching argument. -/
theorem exists_goodFive_recolor_leaf_of_safe_first
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v) (hv : IsThreeVertex G v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteLeafEdge G huv) small)
    (i : Fin 5)
    (havail : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hAnone : transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
        (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hsafeA : IsTwoVertex G a → VertexSeesMatching G
        (recolor G
          (transportColoringToSupergraph
            (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a →
      ¬ ∀ j : Fin 5, VertexSeesInduced G
        (recolor G
          (transportColoringToSupergraph
            (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
  let after := recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)
  have hbaseCondition : ConditionI G base :=
    conditionI_transport_deleteLeafEdge G hsub hu huv small hsmall.2
  have hsafeB : IsTwoVertex G b → VertexSeesMatching G after b →
      ¬ ∀ j : Fin 5, VertexSeesInduced G after b j := by
    intro hb hmatch
    exact palette_safe_other_neighbor_of_first_matching G hsub hva hvb hab
      base (by simpa [base] using hAnone) huv hau i hb
      (by simpa [after, base] using hmatch)
  have hcondition : ConditionI G after := by
    apply conditionI_recolor_leafEdge_at_three_neighbor G hu huv hv hva hvb hN
      base hbaseCondition i
    · simpa [after, base] using hsafeA
    · exact hsafeB
  refine ⟨after, ?_⟩
  exact goodFive_recolor_leafEdge_of_available G hu huv small hsmall i havail
    (by simpa [after, base] using hcondition)

/-- All ordinary degree cases reduce either immediately or to the sole
paper-hard situation: the matching edge points to a two-vertex, the other
branch points to a three-vertex, and the unique available colour saturates
the matching-side two-vertex. -/
theorem leaf_three_first_matching_reduction
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v) (hv : IsThreeVertex G v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteLeafEdge G huv) small)
    (hmatchDeleted : VertexSeesMatching (deleteLeafEdge G huv) small v)
    (hAnone : transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
        (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    (∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour) ∨
      (IsTwoVertex G a ∧ IsThreeVertex G b ∧
        ∃ i : Fin 5,
          ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G)
            (transportColoringToSupergraph
              (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
            (⟨s(u, v), huv⟩ : G.edgeSet) (some i) ∧
          VertexSeesMatching G
            (recolor G
              (transportColoringToSupergraph
                (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
              (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a ∧
          (∀ j : Fin 5, VertexSeesInduced G
            (recolor G
              (transportColoringToSupergraph
                (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
              (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j) ∧
          ∀ j : Fin 5,
            ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G)
              (transportColoringToSupergraph
                (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
              (⟨s(u, v), huv⟩ : G.edgeSet) (some j) → j = i) := by
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
  obtain ⟨i, hi⟩ := exists_available_leafEdge_at_three_neighbor G hu huv hv
    small hsmall hmatchDeleted
  have hE : base (⟨s(u, v), huv⟩ : G.edgeSet) = none := by
    simp [base, transportColoringToSupergraph]
  have hbaseCondition : ConditionI G base :=
    conditionI_transport_deleteLeafEdge G hsub hu huv small hsmall.2
  by_cases haTwo : IsTwoVertex G a
  · by_cases hbThree : IsThreeVertex G b
    · let afterI := recolor G base
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)
      by_cases hbadI : VertexSeesMatching G afterI a ∧
          ∀ t : Fin 5, VertexSeesInduced G afterI a t
      · by_cases hsecond : ∃ j : Fin 5,
            ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G)
              base (⟨s(u, v), huv⟩ : G.edgeSet) (some j) ∧ j ≠ i
        · obtain ⟨j, hj, hji⟩ := hsecond
          left
          apply exists_goodFive_recolor_leaf_of_safe_first G hsub hu huv hv
            hva hvb hab hau hN small hsmall j hj hAnone
          intro _ hmatchJ hallJ
          exact full_palette_leaf_colour_unique_at_two G huv base hbaseCondition
            haTwo hE hji.symm hbadI.1 hbadI.2 hmatchJ hallJ
        · right
          refine ⟨haTwo, hbThree, i, hi, hbadI.1, hbadI.2, ?_⟩
          intro j hj
          by_contra hji
          exact hsecond ⟨j, by simpa [base] using hj, hji⟩
      · left
        apply exists_goodFive_recolor_leaf_of_safe_first G hsub hu huv hv
          hva hvb hab hau hN small hsmall i hi hAnone
        intro _ hmatchI hallI
        exact hbadI ⟨by simpa [afterI, base] using hmatchI,
          by simpa [afterI, base] using hallI⟩
    · have hbpos : 0 < G.degree b := by
          rw [G.degree_pos_iff_exists_adj b]
          exact ⟨v, hvb.symm⟩
      have hble : G.degree b ≤ 2 := by
        have hbsub := hsub b
        unfold IsThreeVertex at hbThree
        omega
      have hactive : (activeInducedBlockerEdgesOn G
          (RetainedEdges (deleteLeafEdge G huv) G) base
          (⟨s(u, v), huv⟩ : G.edgeSet)).card ≤ 3 := by
        have hcount := card_activeBlockers_leafEdge_add_one_le G hu huv hva hvb
          hN base (by simpa [base] using hAnone)
        unfold IsTwoVertex at haTwo
        omega
      have hblocked : (blockedInducedColorsOn G
          (RetainedEdges (deleteLeafEdge G huv) G) base
          (⟨s(u, v), huv⟩ : G.edgeSet)).card ≤ 3 :=
        (card_blockedInducedColorsOn_le_card_activeBlockers G _ base _).trans
          hactive
      obtain ⟨i, j, hij, hi, hj⟩ :=
        exists_two_distinct_available_induced_of_card_blocked_add_two_le G
          (RetainedEdges (deleteLeafEdge G huv) G) base
          (⟨s(u, v), huv⟩ : G.edgeSet) (by omega)
      let afterI := recolor G base
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)
      by_cases hbadI : VertexSeesMatching G afterI a ∧
          ∀ t : Fin 5, VertexSeesInduced G afterI a t
      · left
        apply exists_goodFive_recolor_leaf_of_safe_first G hsub hu huv hv
          hva hvb hab hau hN small hsmall j hj hAnone
        intro _ hmatchJ hallJ
        exact full_palette_leaf_colour_unique_at_two G huv base hbaseCondition
          haTwo hE hij hbadI.1 hbadI.2 hmatchJ hallJ
      · left
        apply exists_goodFive_recolor_leaf_of_safe_first G hsub hu huv hv
          hva hvb hab hau hN small hsmall i hi hAnone
        intro _ hmatchI hallI
        exact hbadI ⟨by simpa [afterI, base] using hmatchI,
          by simpa [afterI, base] using hallI⟩
  · left
    apply exists_goodFive_recolor_leaf_of_safe_first G hsub hu huv hv
      hva hvb hab hau hN small hsmall i hi hAnone
    intro ha
    exact False.elim (haTwo ha)

/-! ## The unique-availability matching/induced swap -/

/- The final hard state is repaired by moving the induced colour of the
outer edge `a-r` onto `v-a`, moving the matching colour from `v-a` to
`a-r`, and leaving the deleted leaf edge matching-coloured.  The hypotheses
that make the swap sound (the far endpoint is degree three and has no other
matching edge) are derived below from palette saturation, rather than being
assumed as in the informal proof. -/
set_option maxHeartbeats 1200000 in
theorem exists_goodFive_leaf_swap_of_unique_saturation
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v) (hv : IsThreeVertex G v)
    (ha : IsTwoVertex G a) (hb : IsThreeVertex G b)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteLeafEdge G huv) small)
    (i : Fin 5)
    (hi : ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G)
      (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hAnone : transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
        (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hbadMatch : VertexSeesMatching G
      (recolor G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a)
    (hbadFull : ∀ j : Fin 5, VertexSeesInduced G
      (recolor G
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j)
    (hunique : ∀ j : Fin 5,
      ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G)
        (transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some j) → j = i) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let base : G.edgeSet → OneTwoColor 5 :=
    transportColoringToSupergraph
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  obtain ⟨r, hrv, har⟩ := exists_other_neighbor_of_isTwoVertex G ha hva.symm
  let C : G.edgeSet := ⟨s(a, r), har⟩
  have hvaNe : v ≠ a := hva.ne
  have harNe : a ≠ r := har.ne
  have hru : r ≠ u := by
    intro hru
    subst r
    have hav : a = v := eq_neighbor_of_degree_eq_one G hu huv har.symm
    exact hvaNe hav.symm
  have hAE : A ≠ E := by
    intro heq
    have humem : u ∈ (A : Sym2 V) := by rw [heq]; simp [E]
    have hu : u = v ∨ u = a := by simpa [A] using humem
    exact hu.elim huv.ne (fun h ↦ hau h.symm)
  have hCE : C ≠ E := by
    intro heq
    have hamem : a ∈ (E : Sym2 V) := by rw [← heq]; simp [C]
    have ha' : a = u ∨ a = v := by simpa [E] using hamem
    exact ha'.elim hau (fun h ↦ hvaNe h.symm)
  have hAC : A ≠ C := by
    intro heq
    have hrmem : r ∈ (A : Sym2 V) := by rw [heq]; simp [C]
    have hr' : r = v ∨ r = a := by simpa [A] using hrmem
    exact hr'.elim hrv (fun h ↦ harNe h.symm)
  have hAD : A ∈ D := by
    simpa [D, E] using (mem_retained_deleteLeafEdge_iff G huv A).mpr hAE
  have hCD : C ∈ D := by
    simpa [D, E] using (mem_retained_deleteLeafEdge_iff G huv C).mpr hCE
  have hvalidD : IsOneTwoColoringOn G D base :=
    transport_deleteLeafEdge_valid G hu huv small hsmall.1
  have hCnonmatching : base C ≠ none := by
    intro hCnone
    have hp := hvalidD A hAD C hCD hAC
    have hdisj : EndpointDisjoint G A C := by
      simpa [base, A, C, hAnone, hCnone] using hp
    exact hdisj a (by simp [A]) (by simp [C])
  obtain ⟨gamma, hCgamma⟩ := Option.ne_none_iff_exists'.mp hCnonmatching
  have hECnotSeparated : ¬ InducedSeparated G E C := by
    intro hsep
    apply hsep.2
    exact ⟨v, by simp [E], a, by simp [C], hva⟩
  have hgammai : gamma ≠ i := by
    intro hgi
    subst gamma
    have hsep := (colorAvailableOn_some_iff G D base E i).mp
      (by simpa [D, base, E] using hi) C hCD hCE
      (by simpa [base] using hCgamma)
    exact hECnotSeparated hsep
  let afterI := recolor G base E (some i)
  have hEbase : base E = none := by
    simp [base, E, transportColoringToSupergraph]
  have hbaseCondition : ConditionI G base :=
    conditionI_transport_deleteLeafEdge G hsub hu huv small hsmall.2
  have hiMissing : ¬ VertexSeesInduced G base a i :=
    not_full_palette_base_of_full_after_leaf_colour G huv base hbaseCondition
      ha (by simpa [E] using hEbase) i
      (by simpa [afterI, E] using hbadMatch)
      (by simpa [afterI, E] using hbadFull)
  have hrThree : IsThreeVertex G r := by
    have hrpos : 0 < G.degree r := by
      rw [G.degree_pos_iff_exists_adj r]
      exact ⟨a, har.symm⟩
    have hrle := hsub r
    unfold IsThreeVertex
    by_contra hrne
    have hrCases : G.degree r = 1 ∨ G.degree r = 2 := by omega
    rcases hrCases with hrOne | hrTwo
    · exact (paletteCondition_at_of_adjacent_leaf G hsub ha har hrOne
        (by simpa [afterI, base, E] using hbadMatch))
        (by simpa [afterI, base, E] using hbadFull)
    · exact (paletteCondition_at_of_adjacent_two G hsub ha har hrTwo
        (by simpa [afterI, base, E] using hbadMatch))
        (by simpa [afterI, base, E] using hbadFull)
  have hAnoMatch : afterI A = none := by
    simpa [afterI, A, E, hAE] using hAnone
  have hnoMatchingAtR : ∀ f : G.edgeSet,
      base f = none → r ∈ (f : Sym2 V) → False := by
    intro f hfnone hrf
    have hfE : f ≠ E := by
      intro hEq
      have hrmem : r ∈ (E : Sym2 V) := hEq ▸ hrf
      have hr' : r = u ∨ r = v := by simpa [E] using hrmem
      exact hr'.elim hru hrv
    have hfAfter : afterI f = none := by
      simpa [afterI, hfE] using hfnone
    have hAf : A ≠ f := by
      intro hEq
      have hrmem : r ∈ (A : Sym2 V) := hEq ▸ hrf
      have hr' : r = v ∨ r = a := by simpa [A] using hrmem
      exact hr'.elim hrv (fun h ↦ harNe h.symm)
    exact (paletteCondition_at_of_two_visible_matching G hsub ha A f hAf
      hAnoMatch hfAfter
      (mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (show a ∈ (A : Sym2 V) by simp [A]) (Or.inl rfl))
      (mem_vertexVisibleEdgeFinset_of_endpoint_close G hrf (Or.inr har)))
      (by simpa [afterI, base, E] using hbadFull)
  have hactiveCard : (activeInducedBlockerEdgesOn G D base E).card ≤ 4 := by
    have hcount := card_activeBlockers_leafEdge_add_one_le G hu huv hva hvb hN
      base (by simpa [base, A] using hAnone)
    unfold IsTwoVertex at ha
    unfold IsThreeVertex at hb
    change (activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) base
      (⟨s(u, v), huv⟩ : G.edgeSet)).card ≤ 4
    omega
  have hCactive : C ∈ activeInducedBlockerEdgesOn G D base E := by
    apply (mem_activeInducedBlockerEdgesOn G D base E C).mpr
    exact ⟨hCD, hCE, hECnotSeparated, by simp [hCgamma]⟩
  have hdistinct := active_blockers_have_distinct_colours_of_unique_available
    G D base E i (by simpa [D, base, E] using hi)
      (by intro j hj; exact hunique j (by simpa [D, base, E] using hj))
      hactiveCard
  let D0 : Set G.edgeSet := D \ ({A, C} : Set G.edgeSet)
  have havailC : ColorAvailableOn G D0 base C none := by
    apply (colorAvailableOn_none_iff G D0 base C).mpr
    intro f hfD0 hfC hfnone
    apply (show EndpointDisjoint G C f from ?_)
    intro p hpC hpf
    have hp : p = a ∨ p = r := by simpa [C] using hpC
    rcases hp with hpa | hpr
    · have hfA : f ≠ A := by
        intro hEq
        apply hfD0.2
        simp [hEq]
      have hpAF := hvalidD A hAD f hfD0.1 hfA.symm
      have hdisj : EndpointDisjoint G A f := by
        simpa [base, A, hAnone, hfnone] using hpAF
      exact hdisj a (by simp [A]) (hpa ▸ hpf)
    · exact hnoMatchingAtR f hfnone (hpr ▸ hpf)
  let afterC := recolor G base C none
  let D1 : Set G.edgeSet := insert C D0
  have havailA : ColorAvailableOn G D1 afterC A (some gamma) := by
    apply (colorAvailableOn_some_iff G D1 afterC A gamma).mpr
    intro f hfD1 hfA hfgamma
    have hfCases : f = C ∨ f ∈ D0 := by simpa [D1] using hfD1
    rcases hfCases with rfl | hfD0
    · simp [afterC] at hfgamma
    · have hfC : f ≠ C := by
        intro hEq
        apply hfD0.2
        simp [hEq]
      have hfBase : base f = some gamma := by
        simpa [afterC, hfC] using hfgamma
      have hsepCf : InducedSeparated G C f := by
        have hp := hvalidD C hCD f hfD0.1 hfC.symm
        simpa [base, C, hCgamma, hfBase] using hp
      have hsepEf : InducedSeparated G E f := by
        by_contra hnot
        have hfE : f ≠ E := by
          exact ((mem_retained_deleteLeafEdge_iff G huv f).mp
            (by simpa [D] using hfD0.1))
        have hfactive : f ∈ activeInducedBlockerEdgesOn G D base E := by
          apply (mem_activeInducedBlockerEdgesOn G D base E f).mpr
          exact ⟨hfD0.1, hfE, hnot, by simp [hfBase]⟩
        exact (hdistinct C f hCactive hfactive hfC.symm)
          (hCgamma.trans hfBase.symm)
      apply (inducedSeparated_iff_forall_endpoints G).mpr
      intro p hpA q hqf
      have hp : p = v ∨ p = a := by simpa [A] using hpA
      rcases hp with hpv | hpa
      · simpa [hpv] using
          ((inducedSeparated_iff_forall_endpoints G).mp hsepEf v
            (by simp [E]) q hqf)
      · simpa [hpa] using
          ((inducedSeparated_iff_forall_endpoints G).mp hsepCf a
            (by simp [C]) q hqf)
  have hvalid0 : IsOneTwoColoringOn G D0 base :=
    hvalidD.mono G (fun (_ : G.edgeSet) (hf : _ ∈ D0) ↦ hf.1)
  have hCnotD0 : C ∉ D0 := by simp [D0]
  have hvalid1 : IsOneTwoColoringOn G D1 afterC := by
    simpa [D1, afterC] using hvalid0.extend_one G hCnotD0 havailC
  have hAnotD1 : A ∉ D1 := by simp [D1, D0, hAC]
  let final := recolor G afterC A (some gamma)
  let D2 : Set G.edgeSet := insert A D1
  have hvalid2 : IsOneTwoColoringOn G D2 final := by
    simpa [D2, final] using hvalid1.extend_one G hAnotD1 havailA
  have hECdisjoint : EndpointDisjoint G E C := by
    intro p hpE hpC
    have hp' : p = u ∨ p = v := by simpa [E] using hpE
    have hp'' : p = a ∨ p = r := by simpa [C] using hpC
    rcases hp' with rfl | rfl <;> rcases hp'' with h | h
    · exact hau h.symm
    · exact hru h.symm
    · exact hvaNe h
    · exact hrv h.symm
  have havailE : ColorAvailableOn G D2 final E none := by
    apply (colorAvailableOn_none_iff G D2 final E).mpr
    intro f hfD2 hfE hfnone
    have hfCases : f = A ∨ f = C ∨ f ∈ D0 := by
      simpa [D2, D1] using hfD2
    rcases hfCases with rfl | rfl | hfD0
    · simp [final] at hfnone
    · exact hECdisjoint
    · have hfA : f ≠ A := by
        intro hEq
        apply hfD0.2
        simp [hEq]
      have hfC : f ≠ C := by
        intro hEq
        apply hfD0.2
        simp [hEq]
      have hfBase : base f = none := by
        simpa [final, afterC, hfA, hfC] using hfnone
      have hdisjAf : EndpointDisjoint G A f := by
        have hp := hvalidD A hAD f hfD0.1 hfA.symm
        simpa [base, A, hAnone, hfBase] using hp
      intro p hpE hpf
      have hp : p = u ∨ p = v := by simpa [E] using hpE
      rcases hp with hpu | hpv
      · let fH : (deleteLeafEdge G huv).edgeSet := ⟨f.1, hfD0.1⟩
        exact no_retained_edge_incident_leaf G hu huv fH (hpu ▸ hpf)
      · exact hdisjAf v (by simp [A]) (hpv ▸ hpf)
  have hEnotD2 : E ∉ D2 := by
    intro hmem
    have hcases : E = A ∨ E = C ∨ E ∈ D0 := by
      simpa [D2, D1] using hmem
    rcases hcases with h | h | h
    · exact hAE h.symm
    · exact hCE h.symm
    · exact ((mem_retained_deleteLeafEdge_iff G huv E).mp
        (by simpa [D] using h.1)) rfl
  have hvalid3 := hvalid2.extend_one G hEnotD2 havailE
  have hdomain : insert E D2 = Set.univ := by
    ext f
    simp only [Set.mem_insert_iff, Set.mem_univ, iff_true]
    by_cases hfE : f = E
    · exact Or.inl hfE
    right
    by_cases hfA : f = A
    · exact Or.inl hfA
    right
    by_cases hfC : f = C
    · exact Or.inl hfC
    right
    refine ⟨?_, ?_⟩
    · simpa [D] using (mem_retained_deleteLeafEdge_iff G huv f).mpr
        (by simpa [E] using hfE)
    · simp [hfA, hfC]
  have hfinalE : final E = none := by
    simp [final, afterC, hAE.symm, hCE.symm, hEbase]
  have hrecolorE : recolor G final E none = final := by
    funext f
    by_cases hfE : f = E
    · subst f
      simp [hfinalE]
    · simp [hfE]
  rw [hdomain, hrecolorE] at hvalid3
  have hbaseFinalAgree :
      ColoringsAgreeOff G ({A, C} : Set G.edgeSet) base final := by
    intro f hf
    have hfA : f ≠ A := by
      intro hEq
      apply hf
      simp [hEq]
    have hfC : f ≠ C := by
      intro hEq
      apply hf
      simp [hEq]
    simp [final, afterC, hfA, hfC]
  have hseeIBack : ∀ {q : V}, VertexSeesInduced G final q i →
      VertexSeesInduced G base q i := by
    intro q hseen
    rw [vertexSeesInduced_iff] at hseen ⊢
    obtain ⟨f, hf, z, hzf, hqz⟩ := hseen
    by_cases hfA : f = A
    · subst f
      have : some gamma = some i := by simpa [final] using hf
      exact False.elim (hgammai (Option.some.inj this))
    by_cases hfC : f = C
    · subst f
      have hfinalC : final C = none := by
        simp [final, afterC, hAC.symm]
      rw [hfinalC] at hf
      simp at hf
    exact ⟨f, by simpa [final, afterC, hfA, hfC] using hf,
      z, hzf, hqz⟩
  have hconditionFinal : ConditionI G final := by
    apply hbaseCondition.of_agreeOff G (S := ({A, C} : Set G.edgeSet))
      hbaseFinalAgree
    intro q hq _ hmatchFinal hallFinal
    by_cases hqa : q = a
    · subst q
      exact hiMissing (hseeIBack (hallFinal i))
    have hmatchBase : VertexSeesMatching G base q := by
      rw [vertexSeesMatching_iff] at hmatchFinal ⊢
      obtain ⟨f, hf, hqf⟩ := hmatchFinal
      by_cases hfA : f = A
      · subst f
        simp [final] at hf
      by_cases hfC : f = C
      · subst f
        have hq' : q = a ∨ q = r := by simpa [C] using hqf
        rcases hq' with h | h
        · exact False.elim (hqa h)
        · subst q
          unfold IsTwoVertex at hq
          unfold IsThreeVertex at hrThree
          omega
      exact ⟨f, by simpa [final, afterC, hfA, hfC] using hf, hqf⟩
    apply hbaseCondition q hq hmatchBase
    intro j
    have hseenFinal := hallFinal j
    rw [vertexSeesInduced_iff] at hseenFinal
    rw [vertexSeesInduced_iff]
    obtain ⟨f, hf, z, hzf, hqz⟩ := hseenFinal
    by_cases hfA : f = A
    · subst f
      have hjg : j = gamma := by
        have : some gamma = some j := by simpa [final] using hf
        exact (Option.some.inj this).symm
      subst j
      have hz : z = v ∨ z = a := by simpa [A] using hzf
      rcases hz with hzv | hza
      · have hqz' : q = v ∨ G.Adj q v := by simpa [hzv] using hqz
        rcases hqz' with hqv | hqv
        · subst q
          unfold IsTwoVertex at hq
          unfold IsThreeVertex at hv
          omega
        · have hqN : q ∈ ({u, a, b} : Finset V) := by
            rw [← hN]
            exact (G.mem_neighborFinset v q).mpr hqv.symm
          have hq' : q = u ∨ q = a ∨ q = b := by simpa using hqN
          rcases hq' with h | h | h
          · subst q
            unfold IsTwoVertex at hq
            omega
          · exact False.elim (hqa h)
          · subst q
            unfold IsTwoVertex at hq
            unfold IsThreeVertex at hb
            omega
      · have hqz' : q = a ∨ G.Adj q a := by simpa [hza] using hqz
        exact ⟨C, by simpa [base] using hCgamma, a, by simp [C], hqz'⟩
    · by_cases hfC : f = C
      · subst f
        have hfinalC : final C = none := by
          simp [final, afterC, hAC.symm]
        rw [hfinalC] at hf
        simp at hf
      · exact ⟨f, by simpa [final, afterC, hfA, hfC] using hf,
          z, hzf, hqz⟩
  exact ⟨final, ⟨by simpa [IsOneTwoColoring] using hvalid3,
    hconditionFinal⟩⟩

/-! ## Complete degree-three leaf extension -/

theorem exists_goodFive_extension_leaf_three_of_first_matching
    (hsub : IsSubcubic G)
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v) (hv : IsThreeVertex G v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : a ≠ b) (hau : a ≠ u)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteLeafEdge G huv) small)
    (hmatchDeleted : VertexSeesMatching (deleteLeafEdge G huv) small v)
    (hAnone : transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
        (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  rcases leaf_three_first_matching_reduction G hsub hu huv hv hva hvb hab hau
      hN small hsmall hmatchDeleted hAnone with hgood | hhard
  · exact hgood
  · obtain ⟨ha, hb, i, hi, hbadMatch, hbadFull, hunique⟩ := hhard
    exact exists_goodFive_leaf_swap_of_unique_saturation G hsub hu huv hv ha hb
      hva hvb hab hau hN small hsmall i hi hAnone hbadMatch hbadFull hunique

/-- A good colouring of the leaf-deleted graph always extends when the
nonleaf endpoint has degree three and already has a retained matching edge.
The matching edge itself selects the orientation of the two remaining
branches. -/
theorem exists_goodFive_extension_leaf_three_neighbor
    (hsub : IsSubcubic G)
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 5)
    (hsmall : GoodFive (deleteLeafEdge G huv) small)
    (hmatching : ∃ f : G.edgeSet,
      f ∈ RetainedEdges (deleteLeafEdge G huv) G ∧
      transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small f = none ∧
      v ∈ (f : Sym2 V)) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  obtain ⟨a, b, hab, hau, hbu, hva, hvb, hN⟩ :=
    exists_two_other_neighbors_of_isThreeVertex G hv huv
  obtain ⟨f, hfD, hfnone, hvf⟩ := hmatching
  let fH : (deleteLeafEdge G huv).edgeSet := ⟨f.1, hfD⟩
  have hfSmall : small fH = none := by
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small hfD] at hfnone
    exact hfnone
  have hmatchDeleted :
      VertexSeesMatching (deleteLeafEdge G huv) small v := by
    rw [vertexSeesMatching_iff]
    exact ⟨fH, hfSmall, hvf⟩
  rcases retained_edge_incident_three_eq_first_or_second G huv hva hvb hN
      f hfD hvf with hfA | hfB
  · have hAnone : transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
        (⟨s(v, a), hva⟩ : G.edgeSet) = none := by
      simpa [hfA] using hfnone
    exact exists_goodFive_extension_leaf_three_of_first_matching G hsub hu huv
      hv hva hvb hab hau hN small hsmall hmatchDeleted hAnone
  · have hBnone : transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small
        (⟨s(v, b), hvb⟩ : G.edgeSet) = none := by
      simpa [hfB] using hfnone
    have hNswap : G.neighborFinset v = {u, b, a} := by
      simpa [Finset.pair_comm] using hN
    exact exists_goodFive_extension_leaf_three_of_first_matching G hsub hu huv
      hv hvb hva hab.symm hbu hNswap small hsmall hmatchDeleted hBnone

end Finite

section Minimal

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every active vertex of an edge-minimal bad Section 3 graph has degree at
least two.  The only remaining case after positivity is a leaf; its neighbour
is forced to have degree three, and the complete hard-branch extension above
then contradicts minimal badness. -/
theorem IsEdgeMinimalBad.active_min_degree_sectionThree
    (hmin : IsEdgeMinimalBad SectionThreeEligible HasGoodFive G) :
    ∀ u, 0 < G.degree u → 2 ≤ G.degree u := by
  intro u huPos
  by_contra huNot
  have huOne : G.degree u = 1 := by omega
  rw [G.degree_pos_iff_exists_adj u] at huPos
  obtain ⟨v, huv⟩ := huPos
  have hvThree : IsThreeVertex G v :=
    hmin.leaf_neighbor_isThreeVertex_sectionThree G huOne huv
  obtain ⟨small, hsmall, f, hfD, hfnone, hvf⟩ :=
    hmin.exists_deleteLeaf_goodFive_and_matching_at_neighbor G huOne huv
  have hsub : IsSubcubic G :=
    isSubcubic_change_decidableRel G
      (Classical.decRel G.Adj) inferInstance hmin.eligible.1
  obtain ⟨colour, hgood⟩ :=
    exists_goodFive_extension_leaf_three_neighbor G hsub huOne huv hvThree
      small hsmall ⟨f, hfD, hfnone, hvf⟩
  apply hmin.not_good
  rw [HasGoodFive]
  refine ⟨colour, ?_⟩
  apply goodFive_change_decidableRel
    (G := G) inferInstance (Classical.decRel G.Adj) colour
  exact hgood

end Minimal

end

end LeanCo.PackingEdgeColoring
