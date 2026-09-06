import LeanCo.PackingEdgeColoring.SectionFourNoFourChain
import LeanCo.PackingEdgeColoring.LeafDeletion
import LeanCo.PackingEdgeColoring.PlanarHeredity
import LeanCo.PackingEdgeColoring.SectionFourLeafC3

/-!
# The Section 4 leaf reduction

This module isolates the reusable deletion, extension, and locality layer of
Lemma 4.2.  The paper's large finite palette analysis can then supply only
the two genuinely local predicates, Conditions 2 and 3.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The transported colouring used throughout the leaf reduction. -/
abbrev leafBaseFour {u v : V} (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4) :
    G.edgeSet → OneTwoColor 4 :=
  transportColoringToSupergraph
    (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small

/-- Recolouring only the deleted leaf edge is supported on that singleton. -/
theorem leaf_recolor_agreesOff
    {u v : V} (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (c : OneTwoColor 4) :
    ColoringsAgreeOff G
      ({(⟨s(u, v), huv⟩ : G.edgeSet)} : Set G.edgeSet)
      (leafBaseFour G huv small)
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) c) :=
  coloringsAgreeOff_recolor G _ _ _

/-- Saturation of a smaller good colouring transports across the leaf
deletion.  The default colour on the absent leaf edge is matching. -/
theorem oneSaturated_leafBaseFour
    {u v : V} (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsat : OneSaturated (deleteLeafEdge G huv) small) :
    OneSaturated G (leafBaseFour G huv small) :=
  OneSaturated.transportColoringToSupergraph G
    (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) hsat

/-- If a retained matching edge is incident with the nonleaf endpoint, then
an induced-colour extension of the leaf edge remains saturated. -/
theorem oneSaturated_recolor_leafEdge_of_retained_matching
    {u v : V} (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsat : OneSaturated (deleteLeafEdge G huv) small)
    (m : G.edgeSet)
    (hmD : m ∈ RetainedEdges (deleteLeafEdge G huv) G)
    (hm : leafBaseFour G huv small m = none)
    (hvm : v ∈ (m : Sym2 V)) (i : Fin 4) :
    OneSaturated G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  let base := leafBaseFour G huv small
  let final := recolor G base e (some i)
  intro f hf
  by_cases hfe : f = e
  · subst f
    refine ⟨m, ?_, v, by simp [e], hvm⟩
    have hme : m ≠ e := by
      intro h
      apply leafEdge_not_mem_retained G huv
      simpa [e, h] using hmD
    change recolor G base e (some i) m = none
    rw [recolor_ne G base (some i) hme]
    exact hm
  · have hfBase : base f ≠ none := by
      change recolor G base e (some i) f ≠ none at hf
      rw [recolor_ne G base (some i) hfe] at hf
      exact hf
    obtain ⟨m', hm'D, hm', z, hzf, hzm'⟩ :=
      OneSaturated.transportColoringToSupergraph_retained_witness G
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) hsat f hfBase
    have hm'e : m' ≠ e := by
      intro h
      apply leafEdge_not_mem_retained G huv
      simpa [e, h] using hm'D
    refine ⟨m', ?_, z, hzf, hzm'⟩
    change recolor G base e (some i) m' = none
    rw [recolor_ne G base (some i) hm'e]
    exact hm'

/-! ## Transport and locality for Condition 2 -/

theorem vertexSeesMatching_leafBase_iff_of_ne
    {k : ℕ} {u v q : V} (huv : G.Adj u v)
    (hqu : q ≠ u) (hqv : q ≠ v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor k) :
    VertexSeesMatching G (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small) q ↔
      VertexSeesMatching (deleteLeafEdge G huv) small q := by
  rw [vertexSeesMatching_iff, vertexSeesMatching_iff]
  constructor
  · rintro ⟨e, hecolour, hqe⟩
    have heD : e ∈ RetainedEdges (deleteLeafEdge G huv) G := by
      by_contra heNot
      have heeq : e = (⟨s(u, v), huv⟩ : G.edgeSet) := by
        by_contra hne
        exact heNot ((mem_retained_deleteLeafEdge_iff G huv e).mpr hne)
      have heval : (e : Sym2 V) = s(u, v) := congrArg Subtype.val heeq
      have hqmem : q ∈ (s(u, v) : Sym2 V) := by
        rw [← heval]
        exact hqe
      rcases (Sym2.mem_iff.mp hqmem) with h | h
      · exact hqu h
      · exact hqv h
    let eH : (deleteLeafEdge G huv).edgeSet := ⟨e.1, heD⟩
    refine ⟨eH, ?_, hqe⟩
    rw [transportColoringToSupergraph_of_mem
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small heD] at hecolour
    exact hecolour
  · rintro ⟨e, hecolour, hqe⟩
    let eG := edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) e
    exact ⟨eG, by simpa [eG] using hecolour, hqe⟩

theorem vertexSeesInduced_leafBase_iff_of_ne
    {k : ℕ} {u v q : V} (huv : G.Adj u v)
    (hqu : q ≠ u) (hqv : q ≠ v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor k)
    (i : Fin k) :
    VertexSeesInduced G (transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small) q i ↔
      VertexSeesInduced (deleteLeafEdge G huv) small q i := by
  rw [vertexSeesInduced_iff, vertexSeesInduced_iff]
  constructor
  · rintro ⟨e, hecolour, z, hze, hqz⟩
    have heD : e ∈ RetainedEdges (deleteLeafEdge G huv) G := by
      by_contra heNot
      have heeq : e = (⟨s(u, v), huv⟩ : G.edgeSet) := by
        by_contra hne
        exact heNot ((mem_retained_deleteLeafEdge_iff G huv e).mpr hne)
      have heval : (e : Sym2 V) = s(u, v) := congrArg Subtype.val heeq
      have hnone : transportColoringToSupergraph
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small e = none := by
        simp [transportColoringToSupergraph, heval]
      rw [hnone] at hecolour
      contradiction
    let eH : (deleteLeafEdge G huv).edgeSet := ⟨e.1, heD⟩
    refine ⟨eH, ?_, z, hze, ?_⟩
    · rw [transportColoringToSupergraph_of_mem
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small heD] at hecolour
      exact hecolour
    · rcases hqz with rfl | hqz
      · exact Or.inl rfl
      · right
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hqz, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro hs
        have hqmem : q ∈ (s(u, v) : Sym2 V) := by rw [← hs]; simp
        rcases (Sym2.mem_iff.mp hqmem) with h | h
        · exact hqu h
        · exact hqv h
  · rintro ⟨e, hecolour, z, hze, hqz⟩
    let eG := edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) e
    refine ⟨eG, by simpa [eG] using hecolour, z, hze, ?_⟩
    exact hqz.imp_right (fun h =>
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) h)

theorem conditionTwo_at_adjacent_leaf
    (hsub : IsSubcubic G) {colour : G.edgeSet → OneTwoColor 4}
    {q u : V} (hq : IsTwoVertex G q) (hqu : G.Adj q u)
    (hu : G.degree u = 1)
    (hmatch : VertexSeesMatching G colour q) :
    ¬ ∀ i : Fin 4, VertexSeesInduced G colour q i := by
  intro hall
  have hfive := longPair_five_le_card_visible_of_full_palette G hmatch hall
  have hfour := card_vertexVisibleEdgeFinset_le_four_of_adjacent_leaf
    G hsub hq hqu hu
  omega

theorem conditionTwo_leafBaseFour
    (hsub : IsSubcubic G) {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : ConditionTwo (deleteLeafEdge G huv) small) :
    ConditionTwo G (leafBaseFour G huv small) := by
  intro q hq hmatch hall
  by_cases hqu : q = u
  · subst q
    unfold IsTwoVertex at hq
    omega
  by_cases hqv : q = v
  · subst q
    exact conditionTwo_at_adjacent_leaf G hsub hq huv.symm hu hmatch hall
  have hqSmall : IsTwoVertex (deleteLeafEdge G huv) q := by
    unfold IsTwoVertex at hq ⊢
    rw [degree_deleteLeafEdge_eq_of_ne G huv hqu hqv]
    exact hq
  exact hsmall q hqSmall
    ((vertexSeesMatching_leafBase_iff_of_ne G huv hqu hqv small).mp hmatch)
    (fun i =>
      (vertexSeesInduced_leafBase_iff_of_ne G huv hqu hqv small i).mp
        (hall i))

/-- Only the leaf, its neighbour, or a vertex adjacent to one of them can
have its Condition-2 palette changed by recolouring the leaf edge. -/
theorem paletteAffectedBy_leafEdge_cases
    {u v q : V} (huv : G.Adj u v)
    (haffect : PaletteAffectedBy G
      ({(⟨s(u, v), huv⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = u ∨ q = v ∨ G.Adj q u ∨ G.Adj q v := by
  rcases haffect with ⟨e, he, hqe⟩ | ⟨e, he, z, hze, hqz⟩
  · simp only [Set.mem_singleton_iff] at he
    subst e
    have hq : q = u ∨ q = v := by simpa using hqe
    exact hq.elim Or.inl (fun h => Or.inr (Or.inl h))
  · simp only [Set.mem_singleton_iff] at he
    subst e
    have hz : z = u ∨ z = v := by simpa using hze
    rcases hz with rfl | rfl
    · exact hqz.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))
    · exact hqz.elim (fun h => Or.inr (Or.inl h))
        (fun h => Or.inr (Or.inr (Or.inr h)))

/-- A Condition-2 proof after leaf recolouring reduces to the nonleaf
endpoint and the two-vertices adjacent to it. -/
theorem ConditionTwo.recolor_leafEdge_of_local
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hold : ConditionTwo G old)
    (hatV : IsTwoVertex G v →
      VertexSeesMatching G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) v →
      ¬ ∀ j : Fin 4, VertexSeesInduced G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) v j)
    (hatNeighbor : ∀ q, IsTwoVertex G q → G.Adj q v →
      VertexSeesMatching G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q →
      ¬ ∀ j : Fin 4, VertexSeesInduced G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q j) :
    ConditionTwo G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  apply ConditionTwo.of_agreeOff G hold
    (coloringsAgreeOff_recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
  intro q hq haffect hmatch
  rcases paletteAffectedBy_leafEdge_cases G huv haffect with
    rfl | rfl | hqu | hqv
  · unfold IsTwoVertex at hq
    omega
  · exact hatV hq hmatch
  · have hqv' : q = v := eq_neighbor_of_degree_eq_one G hu huv hqu.symm
    subst q
    exact hatV hq hmatch
  · exact hatNeighbor q hq hqv hmatch

/-! ## Locality for Condition 3 -/

/-- If recolouring the leaf edge affects Condition 3 for a certified
2-thread, the nonleaf endpoint is one of the thread endpoints. -/
theorem threadConditionAffectedBy_leafEdge_endpoint
    {u v r s : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (p : G.Walk r s) (hp : IsKThread G p 2)
    (haffect : ThreadConditionAffectedBy G
      ({(⟨s(u, v), huv⟩ : G.edgeSet)} : Set G.edgeSet) p hp) :
    r = v ∨ s = v := by
  rcases haffect with ⟨e, he, her⟩ | ⟨e, he, hes⟩
  · simp only [Set.mem_singleton_iff] at he
    subst e
    have hr : r = u ∨ r = v := by simpa using her.1
    rcases hr with hru | hrv
    · have hrThree := hp.start_three
      unfold IsThreeVertex at hrThree
      rw [hru, hu] at hrThree
      omega
    · exact Or.inl hrv
  · simp only [Set.mem_singleton_iff] at he
    subst e
    have hs : s = u ∨ s = v := by simpa using hes.1
    rcases hs with hsu | hsv
    · have hsThree := hp.end_three
      unfold IsThreeVertex at hsThree
      rw [hsu, hu] at hsThree
      omega
    · exact Or.inr hsv

/-- At a 2-thread starting at the nonleaf endpoint, the deleted leaf edge
is genuinely external to its first thread edge. -/
theorem leafEdge_externalAt_thread_start
    {u v s : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (p : G.Walk v s) (hp : IsKThread G p 2) :
    IsExternalAt G v (threadFirstEdge G p hp)
      (⟨s(u, v), huv⟩ : G.edgeSet) := by
  refine ⟨by simp, ?_⟩
  intro heq
  have huFirst : u ∈ (threadFirstEdge G p hp : Sym2 V) := by
    rw [← heq]
    simp
  have hcases : u = v ∨ u = p.getVert 1 := by
    simpa [threadFirstEdge] using huFirst
  rcases hcases with huv' | huOne
  · exact huv.ne huv'
  · have hlen : p.length = 3 := by simpa using hp.length
    have htwo := IsKThread.internal_two G hp (i := 1) (by omega) (by omega)
    unfold IsTwoVertex at htwo
    rw [← huOne, hu] at htwo
    omega

/-- Symmetric externality at a 2-thread ending at the nonleaf endpoint. -/
theorem leafEdge_externalAt_thread_end
    {u v r : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (p : G.Walk r v) (hp : IsKThread G p 2) :
    IsExternalAt G v (threadLastEdge G p hp)
      (⟨s(u, v), huv⟩ : G.edgeSet) := by
  refine ⟨by simp, ?_⟩
  intro heq
  have huLast : u ∈ (threadLastEdge G p hp : Sym2 V) := by
    rw [← heq]
    simp
  have hcases : u = p.getVert 2 ∨ u = v := by
    simpa [threadLastEdge] using huLast
  rcases hcases with huTwo | huv'
  · have hlen : p.length = 3 := by simpa using hp.length
    have htwo := IsKThread.internal_two G hp (i := 2) (by omega) (by omega)
    unfold IsTwoVertex at htwo
    rw [← huTwo, hu] at htwo
    omega
  · exact huv.ne huv'

/-- Condition 3 after a leaf recolouring reduces exactly to affected
2-threads having the nonleaf vertex as one endpoint. -/
theorem ConditionThree.recolor_leafEdge_of_local
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hold : ConditionThree G old)
    (hstart : ∀ (r s : V) (p : G.Walk r s)
        (hp : IsKThread G p 2), r = v →
      ExternalEdgesInduced G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
        (threadFirstEdge G p hp) →
      ExternalEdgesInduced G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) s
        (threadLastEdge G p hp) →
      ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
          (threadFirstEdge G p hp) ≠
        ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) s
          (threadLastEdge G p hp))
    (hend : ∀ (r s : V) (p : G.Walk r s)
        (hp : IsKThread G p 2), s = v →
      ExternalEdgesInduced G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
        (threadFirstEdge G p hp) →
      ExternalEdgesInduced G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) s
        (threadLastEdge G p hp) →
      ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
          (threadFirstEdge G p hp) ≠
        ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) s
          (threadLastEdge G p hp)) :
    ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  apply ConditionThree.of_agreeOff G hold
    (coloringsAgreeOff_recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
  intro r s p hp haffect hleft hright
  rcases threadConditionAffectedBy_leafEdge_endpoint G hu huv p hp haffect with
    hr | hs
  · exact hstart r s p hp hr hleft hright
  · exact hend r s p hp hs hleft hright

/-! ## Transporting Condition 3 across leaf deletion -/

/-- A certified 2-thread cannot contain a degree-one vertex. -/
theorem twoThread_avoids_leaf
    {u v r s : V} (hu : G.degree u = 1) (_huv : G.Adj u v)
    {p : G.Walk r s} (hp : IsKThread G p 2) :
    u ∉ p.support := by
  intro hup
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hup
  have hlen : p.length = 3 := by simpa using hp.length
  have hicases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hicases with rfl | rfl | rfl | rfl
  · have hthree := hp.start_three
    unfold IsThreeVertex at hthree
    have hru : r = u := by simpa using hi
    rw [hru, hu] at hthree
    omega
  · have htwo := IsKThread.internal_two G hp (i := 1) (by omega) (by omega)
    unfold IsTwoVertex at htwo
    rw [hi, hu] at htwo
    omega
  · have htwo := IsKThread.internal_two G hp (i := 2) (by omega) (by omega)
    unfold IsTwoVertex at htwo
    rw [hi, hu] at htwo
    omega
  · have hthree := hp.end_three
    unfold IsThreeVertex at hthree
    have hend : p.getVert 3 = s := by
      rw [← hlen]
      exact p.getVert_length
    have hsu : s = u := hend.symm.trans hi
    rw [hsu, hu] at hthree
    omega

/-- Unless it is an endpoint, the neighbour of a leaf cannot occur in a
certified 2-thread: an internal occurrence already uses its two path
neighbours, leaving no room for the leaf. -/
theorem twoThread_avoids_leafNeighbor_of_end_ne
    {u v r s : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    {p : G.Walk r s} (hp : IsKThread G p 2)
    (hrv : r ≠ v) (hsv : s ≠ v) :
    v ∉ p.support := by
  intro hvp
  have huAvoid := twoThread_avoids_leaf G hu huv hp
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hvp
  have hlen : p.length = 3 := by simpa using hp.length
  have hget_ne (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (hab : a ≠ b) :
      p.getVert a ≠ p.getVert b := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show a ∈ {j : ℕ | j ≤ p.length} by simpa [hlen] using ha)
      (show b ∈ {j : ℕ | j ≤ p.length} by simpa [hlen] using hb)
      heq
    exact hab hinj
  have hicases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hicases with rfl | rfl | rfl | rfl
  · apply hrv
    simpa using hi
  · have hvTwo' := IsKThread.internal_two G hp (i := 1)
      (by omega) (by omega)
    have hvTwo : IsTwoVertex G v := by
      rw [← hi]
      exact hvTwo'
    have hprev : G.Adj v r := by
      have hadj := p.adj_getVert_succ (i := 0) (by omega : 0 < p.length)
      simpa [hi] using hadj.symm
    have hnext : G.Adj v (p.getVert 2) := by
      have hadj := p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
      simpa [hi] using hadj
    have hne : r ≠ p.getVert 2 := by
      simpa using hget_ne 0 2 (by omega) (by omega) (by omega)
    have huN : u ∈ ({r, p.getVert 2} : Finset V) := by
      rw [← neighborFinset_eq_pair_of_isTwoVertex G hvTwo hprev hnext hne]
      exact (G.mem_neighborFinset v u).mpr huv.symm
    have huCases : u = r ∨ u = p.getVert 2 := by simpa using huN
    rcases huCases with hur | huTwo
    · exact huAvoid (hur ▸ p.start_mem_support)
    · exact huAvoid (huTwo ▸ p.getVert_mem_support 2)
  · have hvTwo' := IsKThread.internal_two G hp (i := 2)
      (by omega) (by omega)
    have hvTwo : IsTwoVertex G v := by
      rw [← hi]
      exact hvTwo'
    have hprev : G.Adj v (p.getVert 1) := by
      have hadj := p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
      simpa [hi] using hadj.symm
    have hnext : G.Adj v s := by
      have hadj := p.adj_getVert_succ (i := 2) (by omega : 2 < p.length)
      have hend : p.getVert 3 = s := by
        rw [← hlen]
        exact p.getVert_length
      simpa [hi, hend] using hadj
    have hne : p.getVert 1 ≠ s := by
      have h13 := hget_ne 1 3 (by omega) (by omega) (by omega)
      have hend : p.getVert 3 = s := by
        rw [← hlen]
        exact p.getVert_length
      simpa [hend] using h13
    have huN : u ∈ ({p.getVert 1, s} : Finset V) := by
      rw [← neighborFinset_eq_pair_of_isTwoVertex G hvTwo hprev hnext hne]
      exact (G.mem_neighborFinset v u).mpr huv.symm
    have huCases : u = p.getVert 1 ∨ u = s := by simpa using huN
    rcases huCases with huOne | hus
    · exact huAvoid (huOne ▸ p.getVert_mem_support 1)
    · exact huAvoid (hus ▸ p.end_mem_support)
  · apply hsv
    have hend : p.getVert 3 = s := by
      rw [← hlen]
      exact p.getVert_length
    exact hend.symm.trans hi

/-- A certified 2-thread whose endpoints avoid the nonleaf vertex transfers
unchanged to the leaf-deleted graph. -/
theorem exists_twoThread_deleteLeafEdge_of_end_ne
    {u v r s : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    {p : G.Walk r s} (hp : IsKThread G p 2)
    (hrv : r ≠ v) (hsv : s ≠ v) :
    ∃ pH : (deleteLeafEdge G huv).Walk r s,
      IsKThread (deleteLeafEdge G huv) pH 2 ∧
        ∀ i, pH.getVert i = p.getVert i := by
  let H := deleteLeafEdge G huv
  have huAvoid := twoThread_avoids_leaf G hu huv hp
  have hvAvoid := twoThread_avoids_leafNeighbor_of_end_ne G hu huv hp hrv hsv
  let htransfer : ∀ e, e ∈ p.edges → e ∈ H.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨p.edges_subset_edgeSet he, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hedge
    have hue : u ∈ e := by rw [hedge]; simp
    exact huAvoid (Walk.mem_support_of_mem_edges he hue)
  let pH : H.Walk r s := p.transfer H htransfer
  have hget (i : ℕ) : pH.getVert i = p.getVert i := by
    change (p.transfer H htransfer).getVert i = p.getVert i
    rw [Walk.getVert_eq_getD_support, Walk.getVert_eq_getD_support,
      Walk.support_transfer]
  have hlength : pH.length = p.length := by
    change (p.transfer H htransfer).length = p.length
    exact Walk.length_transfer p htransfer
  have hfar (q : V) (hq : q ∈ p.support) : q ≠ u ∧ q ≠ v := by
    exact ⟨fun h => huAvoid (h ▸ hq), fun h => hvAvoid (h ▸ hq)⟩
  have hrFar := hfar r p.start_mem_support
  have hsFar := hfar s p.end_mem_support
  refine ⟨pH, ?_, hget⟩
  refine ⟨hp.1.transfer htransfer, by simpa [hlength] using hp.length,
    ?_, ?_, ?_⟩
  · have hthree := hp.start_three
    unfold IsThreeVertex at hthree ⊢
    rw [degree_deleteLeafEdge_eq_of_ne G huv hrFar.1 hrFar.2]
    exact hthree
  · have hthree := hp.end_three
    unfold IsThreeVertex at hthree ⊢
    rw [degree_deleteLeafEdge_eq_of_ne G huv hsFar.1 hsFar.2]
    exact hthree
  · intro i hi0 hil
    have hilG : i < p.length := by simpa [hlength] using hil
    have hqFar := hfar (p.getVert i) (p.getVert_mem_support i)
    unfold IsTwoVertex
    rw [hget i, degree_deleteLeafEdge_eq_of_ne G huv hqFar.1 hqFar.2]
    exact IsKThread.internal_two G hp hi0 hilG

/-- Every ambient edge incident with a vertex different from and
nonadjacent to both endpoints of the deleted leaf edge survives. -/
theorem edge_mem_deleteLeafEdge_of_incident_far
    {u v q : V} (huv : G.Adj u v)
    (hqu : q ≠ u) (hqv : q ≠ v)
    (e : G.edgeSet) (hqe : q ∈ (e : Sym2 V)) :
    e.1 ∈ (deleteLeafEdge G huv).edgeSet := by
  rw [SimpleGraph.edgeSet_deleteEdges]
  refine ⟨e.2, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro heq
  have huMem : u ∈ (e : Sym2 V) := by rw [heq]; simp
  have hcases : q = u ∨ q = v := by
    rw [heq] at hqe
    simpa using hqe
  exact hcases.elim hqu hqv

/-- External-inducedness descends through leaf-edge deletion when the
designated thread edges correspond under the canonical inclusion. -/
theorem externalEdgesInduced_small_deleteLeafEdge
    {u v q : V} (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    {threadH : (deleteLeafEdge G huv).edgeSet}
    {threadG : G.edgeSet}
    (hthread : edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) threadH = threadG)
    (hamb : ExternalEdgesInduced G (leafBaseFour G huv small) q threadG) :
    ExternalEdgesInduced (deleteLeafEdge G huv) small q threadH := by
  intro e he
  let eG : G.edgeSet := edgeEmbeddingOfLE
    (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) e
  have heG : IsExternalAt G q threadG eG := by
    refine ⟨he.1, ?_⟩
    intro heq
    apply he.2
    apply (edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V)))).injective
    exact heq.trans hthread.symm
  obtain ⟨i, hi⟩ := hamb eG heG
  exact ⟨i, by simpa [leafBaseFour, eG] using hi⟩

/-- At a vertex far from the deleted leaf edge, external induced-colour
sets are exactly preserved by transport. -/
theorem externalInducedColors_deleteLeafEdge_eq_transport
    {u v q : V} (huv : G.Adj u v)
    (hqu : q ≠ u) (hqv : q ≠ v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    {threadH : (deleteLeafEdge G huv).edgeSet}
    {threadG : G.edgeSet}
    (hthread : edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) threadH = threadG) :
    ExternalInducedColors (deleteLeafEdge G huv) small q threadH =
      ExternalInducedColors G (leafBaseFour G huv small) q threadG := by
  ext i
  constructor
  · rintro ⟨e, he, hi⟩
    let eG : G.edgeSet := edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) e
    refine ⟨eG, ⟨he.1, ?_⟩, ?_⟩
    · intro heq
      apply he.2
      apply (edgeEmbeddingOfLE
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V)))).injective
      exact heq.trans hthread.symm
    · simpa [leafBaseFour, eG] using hi
  · rintro ⟨e, he, hi⟩
    have heH : e.1 ∈ (deleteLeafEdge G huv).edgeSet :=
      edge_mem_deleteLeafEdge_of_incident_far G huv hqu hqv e he.1
    let eH : (deleteLeafEdge G huv).edgeSet := ⟨e.1, heH⟩
    have heEmbed : edgeEmbeddingOfLE
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) eH = e := by
      apply Subtype.ext
      rfl
    refine ⟨eH, ⟨he.1, ?_⟩, ?_⟩
    · intro heq
      apply he.2
      have heqG : edgeEmbeddingOfLE
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) eH =
          edgeEmbeddingOfLE
            (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) threadH :=
        congrArg (edgeEmbeddingOfLE
          (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V)))) heq
      exact heEmbed.symm.trans (heqG.trans hthread)
    · rw [← heEmbed] at hi
      simpa [leafBaseFour, eH] using hi

/-- Condition 3 transports honestly across deletion of a leaf edge. -/
theorem conditionThree_leafBaseFour
    (hsub : IsSubcubic G) {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : ConditionThree (deleteLeafEdge G huv) small) :
    ConditionThree G (leafBaseFour G huv small) := by
  intro r s p hp hleft hright
  by_cases hrv : r = v
  · subst r
    obtain ⟨i, hi⟩ := hleft
      (⟨s(u, v), huv⟩ : G.edgeSet)
      (leafEdge_externalAt_thread_start G hu huv p hp)
    have hnone : leafBaseFour G huv small
        (⟨s(u, v), huv⟩ : G.edgeSet) = none := by
      simp [leafBaseFour, transportColoringToSupergraph]
    rw [hnone] at hi
    contradiction
  by_cases hsv : s = v
  · subst s
    obtain ⟨i, hi⟩ := hright
      (⟨s(u, v), huv⟩ : G.edgeSet)
      (leafEdge_externalAt_thread_end G hu huv p hp)
    have hnone : leafBaseFour G huv small
        (⟨s(u, v), huv⟩ : G.edgeSet) = none := by
      simp [leafBaseFour, transportColoringToSupergraph]
    rw [hnone] at hi
    contradiction
  obtain ⟨pH, hpH, hget⟩ :=
    exists_twoThread_deleteLeafEdge_of_end_ne G hu huv hp hrv hsv
  let firstH : (deleteLeafEdge G huv).edgeSet :=
    threadFirstEdge (deleteLeafEdge G huv) pH hpH
  let firstG : G.edgeSet := threadFirstEdge G p hp
  let lastH : (deleteLeafEdge G huv).edgeSet :=
    threadLastEdge (deleteLeafEdge G huv) pH hpH
  let lastG : G.edgeSet := threadLastEdge G p hp
  have hfirst : edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) firstH = firstG := by
    apply Subtype.ext
    simp [firstH, firstG, threadFirstEdge, hget]
  have hlast : edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) lastH = lastG := by
    apply Subtype.ext
    simp [lastH, lastG, threadLastEdge, hget]
  have hleftH : ExternalEdgesInduced (deleteLeafEdge G huv) small r firstH := by
    apply externalEdgesInduced_small_deleteLeafEdge G huv small hfirst
    simpa [firstG] using hleft
  have hrightH : ExternalEdgesInduced (deleteLeafEdge G huv) small s lastH := by
    apply externalEdgesInduced_small_deleteLeafEdge G huv small hlast
    simpa [lastG] using hright
  have hneH := hsmall r s pH hpH hleftH hrightH
  have huAvoid := twoThread_avoids_leaf G hu huv hp
  have hvAvoid := twoThread_avoids_leafNeighbor_of_end_ne G hu huv hp hrv hsv
  have endpointFar (q : V) (hq : q ∈ p.support) : q ≠ u ∧ q ≠ v := by
    have hqu : q ≠ u := fun h => huAvoid (h ▸ hq)
    have hqv : q ≠ v := fun h => hvAvoid (h ▸ hq)
    exact ⟨hqu, hqv⟩
  have hrFar := endpointFar r p.start_mem_support
  have hsFar := endpointFar s p.end_mem_support
  have hleftEq := externalInducedColors_deleteLeafEdge_eq_transport G huv
    hrFar.1 hrFar.2 small hfirst
  have hrightEq := externalInducedColors_deleteLeafEdge_eq_transport G huv
    hsFar.1 hsFar.2 small hlast
  simpa [firstH, firstG, lastH, lastG, hleftEq, hrightEq] using hneH

/-! ## Immediate matching-colour extension -/

/-- The matching-colour availability argument for a deleted leaf is
palette-independent. -/
theorem matching_available_leafEdge_four_of_no_matching_at_neighbor
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hnoMatch : ∀ f : G.edgeSet,
      f ∈ RetainedEdges (deleteLeafEdge G huv) G →
      v ∈ (f : Sym2 V) → leafBaseFour G huv small f ≠ none) :
    ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) none := by
  rw [colorAvailableOn_none_iff]
  intro f hfD _ hcf x hxe hxf
  have hx : x = u ∨ x = v := by simpa using hxe
  rcases hx with rfl | rfl
  · let fH : (deleteLeafEdge G huv).edgeSet := ⟨f.1, hfD⟩
    exact no_retained_edge_incident_leaf G hu huv fH hxf
  · exact hnoMatch f hfD hxf hcf

/-- If the deleted leaf's neighbour has degree one too, the transported
matching colour is automatically available. -/
theorem matching_available_leafEdge_four_of_neighbor_one
    {u v : V} (hu : G.degree u = 1) (hv : G.degree v = 1)
    (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4) :
    ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) none := by
  apply matching_available_leafEdge_four_of_no_matching_at_neighbor G hu huv
  intro f hfD hvf
  have hfneq : f ≠ (⟨s(u, v), huv⟩ : G.edgeSet) :=
    (mem_retained_deleteLeafEdge_iff G huv f).mp hfD
  intro _
  exact hfneq (by
    have hfv := edge_eq_of_incident_degree_eq_one G hv huv.symm f hvf
    apply Subtype.ext
    simpa only [Sym2.eq_swap] using congrArg Subtype.val hfv)

/-! ## The degree-two neighbour branch -/

/-- With a degree-two nonleaf endpoint, every active induced blocker of
the deleted leaf edge is incident with its other neighbour. -/
theorem activeBlockers_leafEdge_subset_other_incidence_two
    {u v a : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsTwoVertex G v) (hva : G.Adj v a) (hua : u ≠ a)
    {colour : G.edgeSet → OneTwoColor 4} :
    activeInducedBlockerEdgesOn G
        (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet) ⊆
      incidentEdgeFinset G a := by
  intro f hf
  have hf' := (mem_activeInducedBlockerEdgesOn G
    (RetainedEdges (deleteLeafEdge G huv) G) colour
    (⟨s(u, v), huv⟩ : G.edgeSet) f).mp hf
  have hN : G.neighborFinset v = {u, a} :=
    neighborFinset_eq_pair_of_isTwoVertex G hv huv.symm hva hua
  have noU (huf : u ∈ (f : Sym2 V)) : False := by
    let fH : (deleteLeafEdge G huv).edgeSet := ⟨f.1, hf'.1⟩
    exact no_retained_edge_incident_leaf G hu huv fH huf
  have putA (haf : a ∈ (f : Sym2 V)) : f ∈ incidentEdgeFinset G a :=
    (mem_incidentEdgeFinset (G := G)).mpr haf
  have putV (hvf : v ∈ (f : Sym2 V)) :
      f ∈ incidentEdgeFinset G a := by
    rcases edge_eq_left_or_right_of_incident_two G hv huv.symm hva hua f hvf with
      he | he
    · have hfe : f = (⟨s(u, v), huv⟩ : G.edgeSet) := by
        apply Subtype.ext
        simpa only [Sym2.eq_swap] using he
      exact False.elim (((mem_retained_deleteLeafEdge_iff G huv f).mp hf'.1) hfe)
    · exact putA (by rw [he]; simp)
  have putNeighbor {q : V} (hvq : G.Adj v q)
      (hqf : q ∈ (f : Sym2 V)) : f ∈ incidentEdgeFinset G a := by
    have hqN : q ∈ ({u, a} : Finset V) := by
      rw [← hN]
      exact (G.mem_neighborFinset v q).mpr hvq
    have hq : q = u ∨ q = a := by simpa using hqN
    exact hq.elim (fun h => False.elim (noU (h ▸ hqf)))
      (fun h => putA (h ▸ hqf))
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
    · exact putNeighbor (by simpa [hpv] using hpq) hqf
  · have hshared : ∃ p, p ∈ (s(u, v) : Sym2 V) ∧ p ∈ (f : Sym2 V) := by
      by_contra hn
      apply hdisj
      intro p hp hpf
      exact hn ⟨p, hp, hpf⟩
    obtain ⟨p, hp, hpf⟩ := hshared
    have hp' : p = u ∨ p = v := by simpa using hp
    exact hp'.elim (fun h => False.elim (noU (h ▸ hpf)))
      (fun h => putV (h ▸ hpf))

/-- A retained matching edge at the degree-two endpoint removes one edge
from the only possible blocker incidence set, leaving at most two active
blockers in a subcubic graph. -/
theorem card_activeBlockers_leafEdge_le_two_of_two_neighbor_matching
    (hsub : IsSubcubic G) {u v a : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsTwoVertex G v) (hva : G.Adj v a) (hua : u ≠ a)
    (colour : G.edgeSet → OneTwoColor 4)
    (hAnone : colour (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    (activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet)).card ≤ 2 := by
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let S : Finset G.edgeSet := incidentEdgeFinset G a
  have hsubS : activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) ⊆ S := by
    simpa [S] using activeBlockers_leafEdge_subset_other_incidence_two G
      hu huv hv hva hua (colour := colour)
  have hsubErase : activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) ⊆ S.erase A := by
    intro f hf
    refine Finset.mem_erase.mpr ⟨?_, hsubS hf⟩
    intro hfA
    subst f
    exact ((mem_activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) A).mp hf).2.2.2 hAnone
  have hAmem : A ∈ S := by
    exact (mem_incidentEdgeFinset (G := G)).mpr (by simp [A])
  have herase : (S.erase A).card + 1 = S.card := by
    rw [Finset.card_erase_of_mem hAmem]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨A, hAmem⟩
    omega
  have hcardS : S.card = G.degree a := by
    simp [S, card_incidentEdgeFinset]
  have hdeg : G.degree a ≤ 3 := hsub a
  have hc := Finset.card_le_card hsubErase
  omega

/-- Two distinct induced colours are available on the leaf edge whenever
its degree-two endpoint has a retained matching edge. -/
theorem exists_two_available_leafEdge_of_two_neighbor_matching
    (hsub : IsSubcubic G) {u v a : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsTwoVertex G v) (hva : G.Adj v a) (hua : u ≠ a)
    (colour : G.edgeSet → OneTwoColor 4)
    (hAnone : colour (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    ∃ i j : Fin 4, i ≠ j ∧
      ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i) ∧
      ColorAvailableOn G (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet) (some j) := by
  apply exists_two_distinct_available_induced_of_card_blocked_add_two_le
  have hblocked := card_blockedInducedColorsOn_le_card_activeBlockers G
    (RetainedEdges (deleteLeafEdge G huv) G) colour
    (⟨s(u, v), huv⟩ : G.edgeSet)
  have hactive := card_activeBlockers_leafEdge_le_two_of_two_neighbor_matching
    G hsub hu huv hv hva hua colour hAnone
  omega

/-- Recolouring a formerly matching leaf edge by an induced colour cannot
create a new visible matching witness. -/
theorem vertexSeesMatching_of_recolor_leafEdge_induced_four
    {u v q : V} (huv : G.Adj u v)
    (base : G.edgeSet → OneTwoColor 4)
    (i : Fin 4)
    (hmatch : VertexSeesMatching G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q) :
    VertexSeesMatching G base q := by
  rw [vertexSeesMatching_iff] at hmatch ⊢
  obtain ⟨f, hf, hqf⟩ := hmatch
  by_cases hfE : f = (⟨s(u, v), huv⟩ : G.edgeSet)
  · subst f
    simp at hf
  · exact ⟨f, by simpa [recolor, hfE] using hf, hqf⟩

/-- A recolouring by `i` does not create visibility of a different induced
colour `j`. -/
theorem vertexSeesInduced_of_recolor_leafEdge_other_four
    {u v q : V} (huv : G.Adj u v)
    (base : G.edgeSet → OneTwoColor 4)
    {i j : Fin 4} (hji : j ≠ i)
    (hseen : VertexSeesInduced G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q j) :
    VertexSeesInduced G base q j := by
  rw [vertexSeesInduced_iff] at hseen ⊢
  obtain ⟨f, hf, z, hzf, hqz⟩ := hseen
  by_cases hfE : f = (⟨s(u, v), huv⟩ : G.edgeSet)
  · subst f
    have hsome : some i = some j := by simpa using hf
    exact False.elim (hji (Option.some.inj hsome).symm)
  · exact ⟨f, by simpa [recolor, hfE] using hf, z, hzf, hqz⟩

/-- If assigning `i` completes the four-colour palette at a two-vertex,
then `i` was absent from that vertex in the base colouring. -/
theorem not_seen_base_of_full_after_leaf_colour_four
    {u v q : V} (huv : G.Adj u v)
    (base : G.edgeSet → OneTwoColor 4)
    (hcondition : ConditionTwo G base) (hq : IsTwoVertex G q)
    (i : Fin 4)
    (hmatch : VertexSeesMatching G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q)
    (hall : ∀ j : Fin 4, VertexSeesInduced G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q j) :
    ¬ VertexSeesInduced G base q i := by
  have hmatchBase := vertexSeesMatching_of_recolor_leafEdge_induced_four
    G huv base i hmatch
  intro hi
  apply hcondition q hq hmatchBase
  intro j
  by_cases hji : j = i
  · simpa [hji] using hi
  · exact vertexSeesInduced_of_recolor_leafEdge_other_four G huv base hji
      (hall j)

/-- At one fixed two-vertex, at most one leaf-edge colour can be the unique
new colour that completes a forbidden full palette. -/
theorem full_palette_leaf_colour_unique_at_two_four
    {u v q : V} (huv : G.Adj u v)
    (base : G.edgeSet → OneTwoColor 4)
    (hcondition : ConditionTwo G base) (hq : IsTwoVertex G q)
    {i j : Fin 4} (hij : i ≠ j)
    (hmatchI : VertexSeesMatching G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q)
    (hallI : ∀ t : Fin 4, VertexSeesInduced G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) q t)
    (hmatchJ : VertexSeesMatching G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) q)
    (hallJ : ∀ t : Fin 4, VertexSeesInduced G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) q t) :
    False := by
  have hiMissing := not_seen_base_of_full_after_leaf_colour_four G huv base
    hcondition hq i hmatchI hallI
  apply hiMissing
  exact vertexSeesInduced_of_recolor_leafEdge_other_four G huv base hij
    (hallJ i)

/-- Recolouring the leaf edge cannot affect Condition 3 when its nonleaf
endpoint has degree two, because a certified 2-thread has degree-three
endpoints. -/
theorem conditionThree_recolor_leafEdge_of_two_neighbor
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsTwoVertex G v)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hold : ConditionThree G old) :
    ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  apply ConditionThree.recolor_leafEdge_of_local G hu huv old i hold
  · intro r s p hp hrv
    subst r
    have hthree := hp.start_three
    unfold IsThreeVertex at hthree
    unfold IsTwoVertex at hv
    omega
  · intro r s p hp hsv
    subst s
    have hthree := hp.end_three
    unfold IsThreeVertex at hthree
    unfold IsTwoVertex at hv
    omega

/-! ## Local assembly at a degree-three leaf neighbour -/

/-- A colour missing from the induced visibility palette of the nonleaf
endpoint is available on the deleted leaf edge. -/
theorem induced_available_leafEdge_four_of_not_seen_at_neighbor
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (D : Set G.edgeSet) (hD : D ⊆ RetainedEdges (deleteLeafEdge G huv) G)
    (colour : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hmiss : ¬ VertexSeesInduced G colour v i) :
    ColorAvailableOn G D colour
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i) := by
  rw [colorAvailableOn_some_iff]
  intro f hfD hfe hfi
  rw [inducedSeparated_iff_forall_endpoints]
  intro p hpe q hqf
  have hp : p = u ∨ p = v := by simpa using hpe
  constructor
  · intro hpq
    rcases hp with hpu | hpv
    · have huf : u ∈ (f : Sym2 V) := by rw [← hpu, hpq]; exact hqf
      let hfSmall : (deleteLeafEdge G huv).edgeSet := ⟨f.1, hD hfD⟩
      exact no_retained_edge_incident_leaf G hu huv hfSmall huf
    · apply hmiss
      rw [vertexSeesInduced_iff]
      have hqv : q = v := hpq.symm.trans hpv
      exact ⟨f, hfi, v, hqv ▸ hqf, Or.inl rfl⟩
  · intro hpq
    rcases hp with hpu | hpv
    · have huq : G.Adj u q := by simpa [hpu] using hpq
      have hqv : q = v := eq_neighbor_of_degree_eq_one G hu huv huq
      subst q
      apply hmiss
      rw [vertexSeesInduced_iff]
      exact ⟨f, hfi, v, hqf, Or.inl rfl⟩
    · apply hmiss
      rw [vertexSeesInduced_iff]
      exact ⟨f, hfi, q, hqf, Or.inr (by simpa [hpv] using hpq)⟩

/-- Adjacency at the nonleaf endpoint after deleting the leaf edge. -/
theorem deleteLeafEdge_adj_neighbor_iff_four
    {u v z : V} (huv : G.Adj u v) :
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
    have hu' : u = v ∨ u = z := by simpa using humem
    exact hu'.elim huv.ne (fun huz => hzu huz.symm)

theorem neighborFinset_deleteLeafEdge_at_neighbor_four
    {u v : V} (huv : G.Adj u v) :
    (deleteLeafEdge G huv).neighborFinset v =
      (G.neighborFinset v).erase u := by
  ext z
  simp only [Finset.mem_erase]
  rw [(deleteLeafEdge G huv).mem_neighborFinset, G.mem_neighborFinset,
    deleteLeafEdge_adj_neighbor_iff_four G huv]
  tauto

/-- A degree-three nonleaf endpoint becomes a two-vertex after deletion of
its leaf edge. -/
theorem isTwoVertex_deleteLeafEdge_at_three_neighbor_four
    {u v : V} (huv : G.Adj u v) (hv : IsThreeVertex G v) :
    IsTwoVertex (deleteLeafEdge G huv) v := by
  have huN : u ∈ G.neighborFinset v :=
    (G.mem_neighborFinset v u).mpr huv.symm
  unfold IsTwoVertex
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_deleteLeafEdge_at_neighbor_four G huv,
    Finset.card_erase_of_mem huN,
    SimpleGraph.card_neighborFinset_eq_degree, hv]

/-- Induced visibility at the nonleaf endpoint is unchanged by transport
from the leaf-deleted graph; the absent edge has default matching colour. -/
theorem vertexSeesInduced_leafBase_at_neighbor_iff
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (i : Fin 4) :
    VertexSeesInduced G (leafBaseFour G huv small) v i ↔
      VertexSeesInduced (deleteLeafEdge G huv) small v i := by
  rw [vertexSeesInduced_iff, vertexSeesInduced_iff]
  constructor
  · rintro ⟨e, hecolour, z, hze, hvz⟩
    have heD : e ∈ RetainedEdges (deleteLeafEdge G huv) G := by
      by_contra heNot
      have heq : e = (⟨s(u, v), huv⟩ : G.edgeSet) := by
        by_contra hne
        exact heNot ((mem_retained_deleteLeafEdge_iff G huv e).mpr hne)
      subst e
      simp [leafBaseFour, transportColoringToSupergraph] at hecolour
    let eH : (deleteLeafEdge G huv).edgeSet := ⟨e.1, heD⟩
    refine ⟨eH, ?_, z, hze, ?_⟩
    · change transportColoringToSupergraph
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small e = some i at hecolour
      rw [transportColoringToSupergraph_of_mem
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) small heD] at hecolour
      exact hecolour
    · rcases hvz with rfl | hvz
      · exact Or.inl rfl
      · right
        apply (deleteLeafEdge_adj_neighbor_iff_four G huv).mpr
        refine ⟨hvz, ?_⟩
        intro hzu
        subst z
        exact no_retained_edge_incident_leaf G hu huv eH hze
  · rintro ⟨e, hecolour, z, hze, hvz⟩
    let eG := edgeEmbeddingOfLE
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) e
    refine ⟨eG, by simpa [eG, leafBaseFour] using hecolour,
      z, hze, ?_⟩
    exact hvz.imp_right (fun h =>
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))) h)

/-- Condition 2 at the newly degree-two endpoint supplies an available
induced colour for the missing leaf edge. -/
theorem exists_available_leafEdge_at_three_neighbor_four
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (hmatch : VertexSeesMatching (deleteLeafEdge G huv) small v) :
    ∃ i : Fin 4, ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i) := by
  have hvTwo := isTwoVertex_deleteLeafEdge_at_three_neighbor_four G huv hv
  have hcondition : ConditionTwo (deleteLeafEdge G huv) small :=
    hsmall.paletteCondition
  have hmissing := hcondition v hvTwo hmatch
  push_neg at hmissing
  obtain ⟨i, hi⟩ := hmissing
  refine ⟨i, induced_available_leafEdge_four_of_not_seen_at_neighbor G
    hu huv _ (fun _ h => h) _ i ?_⟩
  intro hseen
  apply hi
  exact (vertexSeesInduced_leafBase_at_neighbor_iff G hu huv small i).mp hseen

/-- Every active blocker of the missing leaf edge is incident with one of
the two nonleaf neighbours of its degree-three endpoint. -/
theorem activeBlockers_leafEdge_subset_other_incidence_three_four
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hN : G.neighborFinset v = {u, a, b})
    {colour : G.edgeSet → OneTwoColor 4} :
    activeInducedBlockerEdgesOn G
        (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet) ⊆
      incidentEdgeFinset G a ∪ incidentEdgeFinset G b := by
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
  have putNeighbor {q : V} (hvq : G.Adj v q)
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
    · exact putNeighbor (by simpa [hpv] using hpq) hqf
  · have hshared : ∃ p, p ∈ (s(u, v) : Sym2 V) ∧ p ∈ (f : Sym2 V) := by
      by_contra hn
      apply hdisj
      intro p hp hpf
      exact hn ⟨p, hp, hpf⟩
    obtain ⟨p, hp, hpf⟩ := hshared
    have hp' : p = u ∨ p = v := by simpa using hp
    exact hp'.elim (fun h => False.elim (noU (h ▸ hpf)))
      (fun h => putV (h ▸ hpf))

/-- Removing a known matching edge from the two possible blocker incidence
sets gives the sharp degree sum bound. -/
theorem card_activeBlockers_leafEdge_add_one_le_three_four
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hN : G.neighborFinset v = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hAnone : colour (⟨s(v, a), hva⟩ : G.edgeSet) = none) :
    (activeInducedBlockerEdgesOn G
        (RetainedEdges (deleteLeafEdge G huv) G) colour
        (⟨s(u, v), huv⟩ : G.edgeSet)).card + 1 ≤
      G.degree a + G.degree b := by
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let S : Finset G.edgeSet :=
    incidentEdgeFinset G a ∪ incidentEdgeFinset G b
  have hsub : activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) ⊆ S := by
    simpa [S] using
      activeBlockers_leafEdge_subset_other_incidence_three_four G hu huv
        hva hvb hN (colour := colour)
  have hsubErase : activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) ⊆ S.erase A := by
    intro f hf
    refine Finset.mem_erase.mpr ⟨?_, hsub hf⟩
    intro hfA
    subst f
    exact ((mem_activeInducedBlockerEdgesOn G
      (RetainedEdges (deleteLeafEdge G huv) G) colour
      (⟨s(u, v), huv⟩ : G.edgeSet) A).mp hf).2.2.2 hAnone
  have hAmem : A ∈ S := by
    apply Finset.mem_union_left
    exact (mem_incidentEdgeFinset (G := G)).mpr (by simp [A])
  have hScard : S.card ≤ G.degree a + G.degree b := by
    calc
      S.card ≤ (incidentEdgeFinset G a).card +
          (incidentEdgeFinset G b).card := Finset.card_union_le _ _
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
        (S.erase A).card + 1 := Nat.add_le_add_right
          (Finset.card_le_card hsubErase) 1
    _ = S.card := herase
    _ ≤ G.degree a + G.degree b := hScard

/-- Normal form around a degree-three neighbour of a leaf: orient the two
remaining branches so the first edge is the retained matching edge; the
other edge then has an induced colour by validity. -/
theorem exists_leaf_three_matching_normal_form
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsThreeVertex G v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (m : G.edgeSet)
    (hmD : m ∈ RetainedEdges (deleteLeafEdge G huv) G)
    (hm : leafBaseFour G huv small m = none)
    (hvm : v ∈ (m : Sym2 V)) :
    ∃ (a b : V) (hva : G.Adj v a) (hvb : G.Adj v b)
        (beta : Fin 4),
      a ≠ b ∧ a ≠ u ∧ b ≠ u ∧
      G.neighborFinset v = {u, a, b} ∧
      leafBaseFour G huv small (⟨s(v, a), hva⟩ : G.edgeSet) = none ∧
      leafBaseFour G huv small (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta := by
  obtain ⟨a₀, b₀, hab, hau, hbu, hva, hvb, hN⟩ :=
    exists_two_other_neighbors_of_isThreeVertex G hv huv
  rcases retained_edge_incident_three_eq_first_or_second G huv hva hvb hN
      m hmD hvm with hmA | hmB
  · have hAnone : leafBaseFour G huv small
        (⟨s(v, a₀), hva⟩ : G.edgeSet) = none := by
      simpa [hmA] using hm
    have hBne : leafBaseFour G huv small
        (⟨s(v, b₀), hvb⟩ : G.edgeSet) ≠ none := by
      intro hBnone
      let A : G.edgeSet := ⟨s(v, a₀), hva⟩
      let B : G.edgeSet := ⟨s(v, b₀), hvb⟩
      have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G := by
        exact (mem_retained_deleteLeafEdge_iff G huv A).mpr (by
          intro hAE
          have huA : u ∈ (A : Sym2 V) := by rw [hAE]; simp
          have hcases : u = v ∨ u = a₀ := by simpa [A] using huA
          exact hcases.elim huv.ne hau.symm)
      have hBD : B ∈ RetainedEdges (deleteLeafEdge G huv) G := by
        exact (mem_retained_deleteLeafEdge_iff G huv B).mpr (by
          intro hBE
          have huB : u ∈ (B : Sym2 V) := by rw [hBE]; simp
          have hcases : u = v ∨ u = b₀ := by simpa [B] using huB
          exact hcases.elim huv.ne hbu.symm)
      have hAB : A ≠ B := by
        intro heq
        have hbA : b₀ ∈ (A : Sym2 V) := by rw [heq]; simp [B]
        have hc : b₀ = v ∨ b₀ = a₀ := by simpa [A] using hbA
        exact hc.elim hvb.ne.symm (fun h => hab h.symm)
      have hvalidD : IsOneTwoColoringOn G
          (RetainedEdges (deleteLeafEdge G huv) G)
          (leafBaseFour G huv small) :=
        transport_deleteLeafEdge_valid G hu huv small hsmall.valid
      have hp := hvalidD A hAD B hBD hAB
      have hdisj : EndpointDisjoint G A B := by
        simpa [A, B, hAnone, hBnone] using hp
      exact hdisj v (by simp [A]) (by simp [B])
    obtain ⟨beta, hbeta⟩ := Option.ne_none_iff_exists'.mp hBne
    exact ⟨a₀, b₀, hva, hvb, beta, hab, hau, hbu, hN,
      hAnone, hbeta⟩
  · have hBnone : leafBaseFour G huv small
        (⟨s(v, b₀), hvb⟩ : G.edgeSet) = none := by
      simpa [hmB] using hm
    have hNswap : G.neighborFinset v = {u, b₀, a₀} := by
      simpa [Finset.pair_comm] using hN
    have hAne : leafBaseFour G huv small
        (⟨s(v, a₀), hva⟩ : G.edgeSet) ≠ none := by
      intro hAnone
      let A : G.edgeSet := ⟨s(v, a₀), hva⟩
      let B : G.edgeSet := ⟨s(v, b₀), hvb⟩
      have hAD : A ∈ RetainedEdges (deleteLeafEdge G huv) G := by
        exact (mem_retained_deleteLeafEdge_iff G huv A).mpr (by
          intro hAE
          have huA : u ∈ (A : Sym2 V) := by rw [hAE]; simp
          have hc : u = v ∨ u = a₀ := by simpa [A] using huA
          exact hc.elim huv.ne hau.symm)
      have hBD : B ∈ RetainedEdges (deleteLeafEdge G huv) G := by
        exact (mem_retained_deleteLeafEdge_iff G huv B).mpr (by
          intro hBE
          have huB : u ∈ (B : Sym2 V) := by rw [hBE]; simp
          have hc : u = v ∨ u = b₀ := by simpa [B] using huB
          exact hc.elim huv.ne hbu.symm)
      have hAB : A ≠ B := by
        intro heq
        have hbA : b₀ ∈ (A : Sym2 V) := by rw [heq]; simp [B]
        have hc : b₀ = v ∨ b₀ = a₀ := by simpa [A] using hbA
        exact hc.elim hvb.ne.symm (fun h => hab h.symm)
      have hvalidD := transport_deleteLeafEdge_valid G hu huv small hsmall.valid
      have hp := hvalidD A hAD B hBD hAB
      have hdisj : EndpointDisjoint G A B := by
        simpa [A, B, hAnone, hBnone] using hp
      exact hdisj v (by simp [A]) (by simp [B])
    obtain ⟨beta, hbeta⟩ := Option.ne_none_iff_exists'.mp hAne
    exact ⟨b₀, a₀, hvb, hva, beta, hab.symm, hbu, hau, hNswap,
      hBnone, hbeta⟩

/-- For a degree-three nonleaf endpoint, Condition 2 after recolouring the
leaf edge reduces exactly to its two other neighbours. -/
theorem conditionTwo_recolor_leafEdge_at_three_neighbor_four
    {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v) (hv : IsThreeVertex G v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hN : G.neighborFinset v = {u, a, b})
    (base : G.edgeSet → OneTwoColor 4) (hcondition : ConditionTwo G base)
    (i : Fin 4)
    (hsafeA : IsTwoVertex G a → VertexSeesMatching G
        (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a →
      ¬ ∀ j : Fin 4, VertexSeesInduced G
        (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j)
    (hsafeB : IsTwoVertex G b → VertexSeesMatching G
        (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b →
      ¬ ∀ j : Fin 4, VertexSeesInduced G
        (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j) :
    ConditionTwo G
      (recolor G base (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  apply ConditionTwo.recolor_leafEdge_of_local G hu huv base i hcondition
  · intro hvTwo
    unfold IsTwoVertex at hvTwo
    unfold IsThreeVertex at hv
    omega
  · intro q hq hqv hmatch
    have hqN : q ∈ ({u, a, b} : Finset V) := by
      rw [← hN]
      exact (G.mem_neighborFinset v q).mpr hqv.symm
    have hq' : q = u ∨ q = a ∨ q = b := by simpa using hqN
    rcases hq' with rfl | rfl | rfl
    · unfold IsTwoVertex at hq
      omega
    · exact hsafeA hq hmatch
    · exact hsafeB hq hmatch

/-- Package an available ordinary leaf-edge colour once the two local
Condition-2 checks and the two endpoint orientations of Condition 3 have
been discharged. -/
theorem goodFour_recolor_leafEdge_of_local
    (hsub : IsSubcubic G) {u v a b : V}
    (hu : G.degree u = 1) (huv : G.Adj u v) (hv : IsThreeVertex G v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hN : G.neighborFinset v = {u, a, b})
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (m : G.edgeSet)
    (hmD : m ∈ RetainedEdges (deleteLeafEdge G huv) G)
    (hm : leafBaseFour G huv small m = none)
    (hvm : v ∈ (m : Sym2 V))
    (i : Fin 4)
    (havail : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hsafeA : IsTwoVertex G a → VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a →
      ¬ ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) a j)
    (hsafeB : IsTwoVertex G b → VertexSeesMatching G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b →
      ¬ ∀ j : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) b j)
    (hstart : ∀ (r s : V) (p : G.Walk r s) (hp : IsKThread G p 2),
      r = v →
      ExternalEdgesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
        (threadFirstEdge G p hp) →
      ExternalEdgesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) s
        (threadLastEdge G p hp) →
      ExternalInducedColors G
          (recolor G (leafBaseFour G huv small)
            (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
          (threadFirstEdge G p hp) ≠
        ExternalInducedColors G
          (recolor G (leafBaseFour G huv small)
            (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) s
          (threadLastEdge G p hp))
    (hend : ∀ (r s : V) (p : G.Walk r s) (hp : IsKThread G p 2),
      s = v →
      ExternalEdgesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
        (threadFirstEdge G p hp) →
      ExternalEdgesInduced G
        (recolor G (leafBaseFour G huv small)
          (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) s
        (threadLastEdge G p hp) →
      ExternalInducedColors G
          (recolor G (leafBaseFour G huv small)
            (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) r
          (threadFirstEdge G p hp) ≠
        ExternalInducedColors G
          (recolor G (leafBaseFour G huv small)
            (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) s
          (threadLastEdge G p hp)) :
    GoodFour G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  have hbaseTwo : ConditionTwo G (leafBaseFour G huv small) :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have htwo := conditionTwo_recolor_leafEdge_at_three_neighbor_four G hu huv hv
    hva hvb hN (leafBaseFour G huv small) hbaseTwo i hsafeA hsafeB
  have hthreeBase := conditionThree_leafBaseFour G hsub
    hu huv small hsmall.conditionThree
  have hthree := ConditionThree.recolor_leafEdge_of_local G hu huv
    (leafBaseFour G huv small) i hthreeBase hstart hend
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let base := leafBaseFour G huv small
  let final := recolor G base e (some i)
  have hvalidD : IsOneTwoColoringOn G D base :=
    transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hvalid := hvalidD.extend_one G (leafEdge_not_mem_retained G huv)
    (by simpa [D, base, e] using havail)
  rw [insert_leafEdge_retained_eq_univ G huv] at hvalid
  refine ⟨by simpa only [IsOneTwoColoring, final, base, e] using hvalid,
    ?_, htwo, hthree⟩
  exact oneSaturated_recolor_leafEdge_of_retained_matching G huv small
    hsmall.oneSaturated m hmD hm hvm i

/-- Assembly for the easy matching-colour branch.  Conditions 2 and 3 are
explicit inputs so later palette analysis stays cleanly separated. -/
theorem goodFour_leafBase_of_matching_available
    {u v : V} (hsub : IsSubcubic G)
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (havail : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) none)
    (hconditionTwo : ConditionTwo G (leafBaseFour G huv small))
    (hconditionThree : ConditionThree G (leafBaseFour G huv small)) :
    GoodFour G (leafBaseFour G huv small) := by
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let base := leafBaseFour G huv small
  have hvalidD : IsOneTwoColoringOn G D base :=
    transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hnot : e ∉ D := leafEdge_not_mem_retained G huv
  have he : base e = none := by
    simp [base, leafBaseFour, e, transportColoringToSupergraph]
  have hrecolor : recolor G base e none = base := by
    funext f
    by_cases hfe : f = e
    · subst f
      simp [recolor, he]
    · simp [recolor, hfe]
  have htotal := hvalidD.extend_one G hnot (by simpa [D, base, e] using havail)
  rw [insert_leafEdge_retained_eq_univ G huv, hrecolor] at htotal
  exact ⟨htotal, oneSaturated_leafBaseFour G huv small hsmall.oneSaturated,
    hconditionTwo, hconditionThree⟩

/-- Assembly for an induced-colour leaf extension. -/
theorem goodFour_recolor_leafEdge_of_available
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (m : G.edgeSet)
    (hmD : m ∈ RetainedEdges (deleteLeafEdge G huv) G)
    (hm : leafBaseFour G huv small m = none)
    (hvm : v ∈ (m : Sym2 V))
    (i : Fin 4)
    (havail : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G)
      (leafBaseFour G huv small)
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (hconditionTwo : ConditionTwo G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)))
    (hconditionThree : ConditionThree G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i))) :
    GoodFour G
      (recolor G (leafBaseFour G huv small)
        (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) := by
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  let D : Set G.edgeSet := RetainedEdges (deleteLeafEdge G huv) G
  let base := leafBaseFour G huv small
  let final := recolor G base e (some i)
  have hvalidD : IsOneTwoColoringOn G D base :=
    transport_deleteLeafEdge_valid G hu huv small hsmall.valid
  have hvalid := hvalidD.extend_one G (leafEdge_not_mem_retained G huv)
    (by simpa [D, base, e] using havail)
  rw [insert_leafEdge_retained_eq_univ G huv] at hvalid
  refine ⟨by simpa only [IsOneTwoColoring, final, base, e] using hvalid, ?_, hconditionTwo,
    hconditionThree⟩
  exact oneSaturated_recolor_leafEdge_of_retained_matching G huv small
    hsmall.oneSaturated m hmD hm hvm i

/-- Complete easy branch: if no retained matching edge meets the nonleaf
endpoint, the transported colouring itself is good. -/
theorem goodFour_leafBase_of_no_matching_at_neighbor
    (hsub : IsSubcubic G) {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (hnoMatch : ∀ f : G.edgeSet,
      f ∈ RetainedEdges (deleteLeafEdge G huv) G →
      v ∈ (f : Sym2 V) → leafBaseFour G huv small f ≠ none) :
    GoodFour G (leafBaseFour G huv small) := by
  apply goodFour_leafBase_of_matching_available G hsub hu huv small hsmall
    (matching_available_leafEdge_four_of_no_matching_at_neighbor G hu huv
      small hnoMatch)
    (conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition)
    (conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree)

/-- A good colouring of the leaf-deleted graph extends whenever the
nonleaf endpoint has degree two and has a retained matching edge.  There
are two available induced colours; at most one can complete the palette at
the unique other neighbour. -/
theorem exists_goodFour_extension_leaf_of_two_neighbor
    (hsub : IsSubcubic G) {u v : V}
    (hu : G.degree u = 1) (huv : G.Adj u v)
    (hv : IsTwoVertex G v)
    (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4)
    (hsmall : GoodFour (deleteLeafEdge G huv) small)
    (m : G.edgeSet)
    (hmD : m ∈ RetainedEdges (deleteLeafEdge G huv) G)
    (hm : leafBaseFour G huv small m = none)
    (hvm : v ∈ (m : Sym2 V)) :
    ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour := by
  obtain ⟨a, hau, hva⟩ := exists_other_neighbor_of_isTwoVertex G hv huv.symm
  have hua : u ≠ a := hau.symm
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  have hEA : E ≠ A := by
    intro heq
    have hua' : u = v ∨ u = a := by
      have : u ∈ (A : Sym2 V) := by rw [← heq]; simp [E]
      simpa [A] using this
    exact hua'.elim huv.ne hua
  have hmA : m = A := by
    rcases edge_eq_left_or_right_of_incident_two G hv huv.symm hva hua m hvm with
      he | he
    · have hmE : m = E := by
        apply Subtype.ext
        simpa [E, Sym2.eq_swap] using he
      exact False.elim (((mem_retained_deleteLeafEdge_iff G huv m).mp hmD)
        (by simpa [E] using hmE))
    · apply Subtype.ext
      simpa [A] using he
  have hAnone : leafBaseFour G huv small A = none := by
    simpa [hmA] using hm
  obtain ⟨i, j, hij, hi, hj⟩ :=
    exists_two_available_leafEdge_of_two_neighbor_matching G hsub hu huv hv
      hva hua (leafBaseFour G huv small) hAnone
  have hbaseTwo : ConditionTwo G (leafBaseFour G huv small) :=
    conditionTwo_leafBaseFour G hsub hu huv small hsmall.paletteCondition
  have hbaseThree : ConditionThree G (leafBaseFour G huv small) :=
    conditionThree_leafBaseFour G hsub hu huv small hsmall.conditionThree
  let Bad (c : Fin 4) : Prop :=
    IsTwoVertex G a ∧
      VertexSeesMatching G
        (recolor G (leafBaseFour G huv small) E (some c)) a ∧
      ∀ t : Fin 4, VertexSeesInduced G
        (recolor G (leafBaseFour G huv small) E (some c)) a t
  have makeGood (c : Fin 4)
      (hc : ColorAvailableOn G
        (RetainedEdges (deleteLeafEdge G huv) G)
        (leafBaseFour G huv small) E (some c))
      (hsafe : ¬ Bad c) :
      GoodFour G
        (recolor G (leafBaseFour G huv small) E (some c)) := by
    have htwoFinal : ConditionTwo G
        (recolor G (leafBaseFour G huv small) E (some c)) := by
      apply ConditionTwo.recolor_leafEdge_of_local G hu huv
        (leafBaseFour G huv small) c hbaseTwo
      · intro _ hmatch
        exact conditionTwo_at_adjacent_leaf G hsub hv huv.symm hu hmatch
      · intro q hq hqv hmatch
        have hN : G.neighborFinset v = {u, a} :=
    neighborFinset_eq_pair_of_isTwoVertex G hv huv.symm hva hua
        have hqN : q ∈ ({u, a} : Finset V) := by
          rw [← hN]
          exact (G.mem_neighborFinset v q).mpr hqv.symm
        have hqa : q = u ∨ q = a := by simpa using hqN
        rcases hqa with rfl | rfl
        · unfold IsTwoVertex at hq
          omega
        · intro hall
          apply hsafe
          exact ⟨hq, by simpa [E] using hmatch,
            by simpa [E] using hall⟩
    have hthreeFinal : ConditionThree G
        (recolor G (leafBaseFour G huv small) E (some c)) := by
      simpa [E] using conditionThree_recolor_leafEdge_of_two_neighbor G
        hu huv hv (leafBaseFour G huv small) c hbaseThree
    apply goodFour_recolor_leafEdge_of_available G hu huv small hsmall
      m hmD hm hvm c
    · simpa [E] using hc
    · simpa [E] using htwoFinal
    · simpa [E] using hthreeFinal
  by_cases hbadI : Bad i
  · refine ⟨recolor G (leafBaseFour G huv small) E (some j),
      makeGood j (by simpa [E] using hj) ?_⟩
    intro hbadJ
    rcases hbadI with ⟨haTwo, hmatchI, hallI⟩
    rcases hbadJ with ⟨_, hmatchJ, hallJ⟩
    exact full_palette_leaf_colour_unique_at_two_four G huv
      (leafBaseFour G huv small) hbaseTwo haTwo hij
      (by simpa [E] using hmatchI) (by simpa [E] using hallI)
      (by simpa [E] using hmatchJ) (by simpa [E] using hallJ)
  · exact ⟨recolor G (leafBaseFour G huv small) E (some i),
      makeGood i (by simpa [E] using hi) hbadI⟩

end Finite

/-! ## Minimal-counterexample interface -/

section Minimal

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Deleting the edge incident with a leaf preserves all Section 4
eligibility hypotheses. -/
theorem sectionFourEligible_deleteLeafEdge
    (hEligible : SectionFourEligible G)
    {u v : V} (huv : G.Adj u v) :
    SectionFourEligible (deleteLeafEdge G huv) := by
  let H := deleteLeafEdge G huv
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hEligibleG :
      @IsSubcubic V G _ (Classical.decRel G.Adj) ∧
        IsCombinatoriallyPlanar G ∧ (16 : ℕ∞) ≤ G.egirth := by
    simpa [SectionFourEligible] using hEligible
  have hsubCurrent : IsSubcubic G :=
    isSubcubic_change_decidableRel_fourChain G
      (Classical.decRel G.Adj) inferInstance hEligibleG.1
  rw [SectionFourEligible]
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact (H.degree_le_of_le
      (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V)))).trans
      (hsubCurrent q)
  · have hplan := hEligibleG.2.1.deleteEdgesFinset
        ({s(u, v)} : Finset (Sym2 V))
    simpa [H, deleteLeafEdge] using hplan
  · exact hEligibleG.2.2.trans
      (SimpleGraph.egirth_anti
        (G.deleteEdges_le ({s(u, v)} : Set (Sym2 V))))

/-- Minimality supplies a good colouring after deleting a leaf edge.  In
every such colouring a retained matching edge must meet the nonleaf
endpoint, since otherwise the easy matching extension contradicts
minimal badness. -/
theorem IsEdgeMinimalBad.exists_deleteLeaf_goodFour_and_matching_at_neighbor
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G)
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v) :
    ∃ small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4,
      GoodFour (deleteLeafEdge G huv) small ∧
      ∃ f : G.edgeSet,
        f ∈ RetainedEdges (deleteLeafEdge G huv) G ∧
        leafBaseFour G huv small f = none ∧
        v ∈ (f : Sym2 V) := by
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  have hEligibleDelete :
      SectionFourEligible (G.deleteEdges ({e.1} : Set (Sym2 V))) := by
    simpa [e, deleteLeafEdge] using
      sectionFourEligible_deleteLeafEdge G hmin.eligible huv
  have hgoodDelete :
      HasGoodFour (G.deleteEdges ({e.1} : Set (Sym2 V))) :=
    hmin.good_deleteEdge e hEligibleDelete
  rw [HasGoodFour] at hgoodDelete
  obtain ⟨small, hsmallClassical⟩ := hgoodDelete
  have hsmall : GoodFour (deleteLeafEdge G huv) small := by
    apply goodFour_change_decidableRel
      (G := deleteLeafEdge G huv)
      (Classical.decRel (deleteLeafEdge G huv).Adj) inferInstance small
    exact hsmallClassical
  refine ⟨small, hsmall, ?_⟩
  by_contra hnone
  push_neg at hnone
  have hnoMatch : ∀ f : G.edgeSet,
      f ∈ RetainedEdges (deleteLeafEdge G huv) G →
      v ∈ (f : Sym2 V) → leafBaseFour G huv small f ≠ none := by
    intro f hfD hvf hcolour
    exact hnone f hfD hcolour hvf
  have hsub : IsSubcubic G :=
    isSubcubic_change_decidableRel_fourChain G
      (Classical.decRel G.Adj) inferInstance hmin.eligible.1
  have hgoodG := goodFour_leafBase_of_no_matching_at_neighbor G hsub hu huv
    small hsmall hnoMatch
  apply hmin.not_good
  rw [HasGoodFour]
  refine ⟨leafBaseFour G huv small, ?_⟩
  apply goodFour_change_decidableRel
    (G := G) inferInstance (Classical.decRel G.Adj)
      (leafBaseFour G huv small)
  exact hgoodG

/-- In a minimal bad Section 4 graph, the neighbour of every leaf is a
three-vertex.  The degree-one case contradicts retention, while the
degree-two case is the fully verified two-colour-choice extension above. -/
theorem IsEdgeMinimalBad.leaf_neighbor_isThreeVertex_sectionFour
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G)
    {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v) :
    IsThreeVertex G v := by
  obtain ⟨small, hsmall, f, hfD, hfnone, hvf⟩ :=
    hmin.exists_deleteLeaf_goodFour_and_matching_at_neighbor G hu huv
  have hsub : IsSubcubic G :=
    isSubcubic_change_decidableRel_fourChain G
      (Classical.decRel G.Adj) inferInstance hmin.eligible.1
  have hvpos : 0 < G.degree v := by
    rw [G.degree_pos_iff_exists_adj v]
    exact ⟨u, huv.symm⟩
  have hvle : G.degree v ≤ 3 := hsub v
  unfold IsThreeVertex
  by_contra hvne
  have hvCases : G.degree v = 1 ∨ G.degree v = 2 := by omega
  rcases hvCases with hvOne | hvTwo
  · have hfe : f = (⟨s(u, v), huv⟩ : G.edgeSet) := by
      have hfv := edge_eq_of_incident_degree_eq_one G hvOne huv.symm f hvf
      apply Subtype.ext
      simpa only [Sym2.eq_swap] using congrArg Subtype.val hfv
    exact ((mem_retained_deleteLeafEdge_iff G huv f).mp hfD) hfe
  · obtain ⟨colour, hgoodG⟩ :=
      exists_goodFour_extension_leaf_of_two_neighbor G hsub hu huv hvTwo
        small hsmall f hfD hfnone hvf
    apply hmin.not_good
    rw [HasGoodFour]
    refine ⟨colour, ?_⟩
    apply goodFour_change_decidableRel
      (G := G) inferInstance (Classical.decRel G.Adj) colour
    exact hgoodG

/-- Exact global wrapper once the remaining local degree-three extension
is supplied.  This theorem isolates the only genuine finite palette case
left in Lemma 4.2. -/
theorem IsEdgeMinimalBad.active_min_degree_sectionFour_of_three_extension
    (hmin : IsEdgeMinimalBad SectionFourEligible HasGoodFour G)
    (hthree : ∀ {u v : V} (hu : G.degree u = 1) (huv : G.Adj u v)
      (hv : IsThreeVertex G v)
      (small : (deleteLeafEdge G huv).edgeSet → OneTwoColor 4),
      GoodFour (deleteLeafEdge G huv) small →
      ∀ (f : G.edgeSet),
        f ∈ RetainedEdges (deleteLeafEdge G huv) G →
        leafBaseFour G huv small f = none →
        v ∈ (f : Sym2 V) →
        ∃ colour : G.edgeSet → OneTwoColor 4, GoodFour G colour) :
    ∀ u, 0 < G.degree u → 2 ≤ G.degree u := by
  intro u huPos
  by_contra huNot
  have huOne : G.degree u = 1 := by omega
  rw [G.degree_pos_iff_exists_adj u] at huPos
  obtain ⟨v, huv⟩ := huPos
  have hvThree := hmin.leaf_neighbor_isThreeVertex_sectionFour G huOne huv
  obtain ⟨small, hsmall, f, hfD, hfnone, hvf⟩ :=
    hmin.exists_deleteLeaf_goodFour_and_matching_at_neighbor G huOne huv
  obtain ⟨colour, hgood⟩ :=
    hthree huOne huv hvThree small hsmall f hfD hfnone hvf
  apply hmin.not_good
  rw [HasGoodFour]
  refine ⟨colour, ?_⟩
  apply goodFour_change_decidableRel
    (G := G) inferInstance (Classical.decRel G.Adj) colour
  exact hgood

end Minimal

end

end LeanCo.PackingEdgeColoring
