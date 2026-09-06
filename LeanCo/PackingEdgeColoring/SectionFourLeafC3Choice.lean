import LeanCo.PackingEdgeColoring.SectionFourLeafEasyThree

/-!
# Two-colour choice for the Condition-3 leaf obstruction

This module develops the finite part of the hard degree-three leaf branch.
The first layer computes the external induced-colour set at the leaf
neighbour after recolouring the leaf edge.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every edge at a vertex with the displayed three-neighbour normal form
is one of the three displayed edges. -/
theorem edge_eq_leaf_or_first_or_second_of_incident_three
    {u v a b : V} (huv : G.Adj u v) (hva : G.Adj v a)
    (hvb : G.Adj v b) (hN : G.neighborFinset v = {u, a, b})
    (e : G.edgeSet) (hve : v ∈ (e : Sym2 V)) :
    e = (⟨s(u, v), huv⟩ : G.edgeSet) ∨
      e = (⟨s(v, a), hva⟩ : G.edgeSet) ∨
      e = (⟨s(v, b), hvb⟩ : G.edgeSet) := by
  obtain ⟨z, hez⟩ := Sym2.mem_iff_exists.mp hve
  have hvz : G.Adj v z := by
    have heG := e.2
    rw [hez] at heG
    simpa using heG
  have hzN : z ∈ ({u, a, b} : Finset V) := by
    rw [← hN]
    exact (G.mem_neighborFinset v z).mpr hvz
  have hz : z = u ∨ z = a ∨ z = b := by simpa using hzN
  rcases hz with hzu | hza | hzb
  · apply Or.inl
    apply Subtype.ext
    simpa only [hzu, Sym2.eq_swap] using hez
  · apply Or.inr
    apply Or.inl
    apply Subtype.ext
    simpa only [hza] using hez
  · apply Or.inr
    apply Or.inr
    apply Subtype.ext
    simpa only [hzb] using hez

/-- In the normal form `E = u-v`, `A = v-a`, `B = v-b`, if `B` has
induced colour `beta`, then after assigning `i` to `E` the external colour
set at `v` relative to the guard edge `A` is exactly `{i, beta}`. -/
theorem externalInducedColors_recolor_leaf_at_matching_guard
    {u v a b : V} (huv : G.Adj u v) (hva : G.Adj v a)
    (hvb : G.Adj v b) (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
    (old : G.edgeSet → OneTwoColor 4) (beta i : Fin 4)
    (hB : old (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta) :
    ExternalInducedColors G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) v
        (⟨s(v, a), hva⟩ : G.edgeSet) =
      ({i, beta} : Set (Fin 4)) := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let A : G.edgeSet := ⟨s(v, a), hva⟩
  let B : G.edgeSet := ⟨s(v, b), hvb⟩
  have hEA : E ≠ A := by
    intro hEq
    have huA : u ∈ (A : Sym2 V) := by rw [← hEq]; simp [E]
    have hc : u = v ∨ u = a := by simpa [A] using huA
    exact hc.elim huv.ne hau.symm
  have hBA : B ≠ A := by
    intro hEq
    have hbA : b ∈ (A : Sym2 V) := by rw [← hEq]; simp [B]
    have hc : b = v ∨ b = a := by simpa [A] using hbA
    exact hc.elim hvb.ne.symm (fun h ↦ hab h.symm)
  have hBE : B ≠ E := by
    intro hEq
    have hbE : b ∈ (E : Sym2 V) := by rw [← hEq]; simp [B]
    have hc : b = u ∨ b = v := by simpa [E] using hbE
    exact hc.elim hbu hvb.ne.symm
  have hBfinal : recolor G old E (some i) B = some beta := by
    rw [recolor_ne G old (some i) hBE]
    exact hB
  ext c
  constructor
  · rintro ⟨e, hext, hcolour⟩
    rcases edge_eq_leaf_or_first_or_second_of_incident_three G huv hva hvb hN
        e hext.1 with rfl | rfl | rfl
    · have hci : c = i := by
        simpa [E] using hcolour.symm
      simp [hci]
    · exact False.elim (hext.2 rfl)
    · have hcb : c = beta := by
        rw [show recolor G old E (some i) B = some beta from hBfinal] at hcolour
        exact Option.some.inj hcolour.symm
      simp [hcb]
  · intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · refine ⟨E, ⟨by simp [E], hEA⟩, ?_⟩
      simp [E]
    · refine ⟨B, ⟨by simp [B], hBA⟩, hBfinal⟩

/-- An available colour for the leaf edge differs from the colour on the
other induced branch edge, since the two edges share `v`. -/
theorem available_leaf_colour_ne_other_branch_colour
    {u v b : V} (huv : G.Adj u v) (hvb : G.Adj v b) (hbu : b ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (beta i : Fin 4)
    (hB : old (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (havail : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) :
    i ≠ beta := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  let B : G.edgeSet := ⟨s(v, b), hvb⟩
  have hBE : B ≠ E := by
    intro hEq
    have hbE : b ∈ (E : Sym2 V) := by rw [← hEq]; simp [B]
    have hc : b = u ∨ b = v := by simpa [E] using hbE
    exact hc.elim hbu hvb.ne.symm
  have hBD : B ∈ RetainedEdges (deleteLeafEdge G huv) G :=
    (mem_retained_deleteLeafEdge_iff G huv B).mpr hBE
  intro hibeta
  have hsep := (colorAvailableOn_some_iff G
    (RetainedEdges (deleteLeafEdge G huv) G) old E i).mp havail
      B hBD hBE (by simpa [B, hibeta] using hB)
  exact hsep.1 v (by simp [E]) (by simp [B])

/-! ## Uniqueness of the critical directed 2-thread -/

/-- Equality of the first edge with `v-a` identifies the first internal
vertex of the thread. -/
theorem getVert_one_eq_of_threadFirstEdge_eq
    {v a t : V} (hva : G.Adj v a) (p : G.Walk v t)
    (hp : IsKThread G p 2)
    (hfirst : threadFirstEdge G p hp =
      (⟨s(v, a), hva⟩ : G.edgeSet)) :
    p.getVert 1 = a := by
  have hedge : s(v, p.getVert 1) = s(v, a) :=
    congrArg Subtype.val hfirst
  rcases Sym2.eq_iff.mp hedge with h | h
  · exact h.2
  · exact False.elim (hva.ne h.1)

/-- Reversing a certified 2-thread exchanges its first and last designated
edges. -/
theorem threadFirstEdge_reverse_two
    {r t : V} (p : G.Walk r t) (hp : IsKThread G p 2) :
    threadFirstEdge G p.reverse hp.reverse = threadLastEdge G p hp := by
  apply Subtype.ext
  simp [threadFirstEdge, threadLastEdge, Walk.getVert_reverse, hp.length,
    Sym2.eq_swap]

/-- The companion orientation identity for the last designated edge. -/
theorem threadLastEdge_reverse_two
    {r t : V} (p : G.Walk r t) (hp : IsKThread G p 2) :
    threadLastEdge G p.reverse hp.reverse = threadFirstEdge G p hp := by
  apply Subtype.ext
  simp [threadFirstEdge, threadLastEdge, Walk.getVert_reverse, hp.length,
    Sym2.eq_swap]

/-- Two certified 2-threads with the same start and same first internal
vertex have the same second internal vertex and endpoint.  This is the
degree-two uniqueness needed to compare two critical Condition-3 failures. -/
theorem twoThread_tail_eq_of_getVert_one_eq
    {v r t : V} (p : G.Walk v r) (q : G.Walk v t)
    (hp : IsKThread G p 2) (hq : IsKThread G q 2)
    (hone : p.getVert 1 = q.getVert 1) :
    p.getVert 2 = q.getVert 2 ∧ r = t := by
  have hplen : p.length = 3 := by simpa using hp.length
  have hqlen : q.length = 3 := by simpa using hq.length
  have hpne (x y : ℕ) (hx : x ≤ 3) (hy : y ≤ 3) (hxy : x ≠ y) :
      p.getVert x ≠ p.getVert y := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show x ∈ {z : ℕ | z ≤ p.length} by simpa [hplen] using hx)
      (show y ∈ {z : ℕ | z ≤ p.length} by simpa [hplen] using hy)
      heq
    exact hxy hinj
  have hqne (x y : ℕ) (hx : x ≤ 3) (hy : y ≤ 3) (hxy : x ≠ y) :
      q.getVert x ≠ q.getVert y := by
    intro heq
    have hinj := hq.1.getVert_injOn
      (show x ∈ {z : ℕ | z ≤ q.length} by simpa [hqlen] using hx)
      (show y ∈ {z : ℕ | z ≤ q.length} by simpa [hqlen] using hy)
      heq
    exact hxy hinj
  have hp01 : G.Adj v (p.getVert 1) := hp.first_step_adj
  have hp12 : G.Adj (p.getVert 1) (p.getVert 2) := by
    exact p.adj_getVert_succ (by omega)
  have hp02 : v ≠ p.getVert 2 := by
    simpa using hpne 0 2 (by omega) (by omega) (by omega)
  have hpOneTwo : IsTwoVertex G (p.getVert 1) :=
    IsKThread.internal_two G hp (i := 1) (by omega) (by omega)
  have hNOne : G.neighborFinset (p.getVert 1) = {v, p.getVert 2} :=
    neighborFinset_eq_pair_of_isTwoVertex G hpOneTwo hp01.symm hp12 hp02
  have hq12 : G.Adj (q.getVert 1) (q.getVert 2) := by
    exact q.adj_getVert_succ (by omega)
  have hqTwoMem : q.getVert 2 ∈ ({v, p.getVert 2} : Finset V) := by
    rw [← hNOne, hone]
    exact (G.mem_neighborFinset _ _).mpr hq12
  have hqTwoCases : q.getVert 2 = v ∨ q.getVert 2 = p.getVert 2 := by
    simpa using hqTwoMem
  have hq20 : q.getVert 2 ≠ v := by
    simpa using hqne 2 0 (by omega) (by omega) (by omega)
  have htwo : p.getVert 2 = q.getVert 2 := by
    rcases hqTwoCases with hqv | hqp
    · exact False.elim (hq20 hqv)
    · exact hqp.symm
  have hp23 : G.Adj (p.getVert 2) r := by
    have hadj := p.adj_getVert_succ (i := 2) (by omega)
    have hend : p.getVert 3 = r := by
      rw [← hplen]
      exact p.getVert_length
    simpa [hend] using hadj
  have hp13 : p.getVert 1 ≠ r := by
    have hne := hpne 1 3 (by omega) (by omega) (by omega)
    have hend : p.getVert 3 = r := by
      rw [← hplen]
      exact p.getVert_length
    simpa [hend] using hne
  have hpTwoTwo : IsTwoVertex G (p.getVert 2) :=
    IsKThread.internal_two G hp (i := 2) (by omega) (by omega)
  have hNTwo : G.neighborFinset (p.getVert 2) = {p.getVert 1, r} :=
    neighborFinset_eq_pair_of_isTwoVertex G hpTwoTwo hp12.symm hp23 hp13
  have hq23 : G.Adj (q.getVert 2) t := by
    have hadj := q.adj_getVert_succ (i := 2) (by omega)
    have hend : q.getVert 3 = t := by
      rw [← hqlen]
      exact q.getVert_length
    simpa [hend] using hadj
  have htMem : t ∈ ({p.getVert 1, r} : Finset V) := by
    rw [← hNTwo, htwo]
    exact (G.mem_neighborFinset _ _).mpr hq23
  have htCases : t = p.getVert 1 ∨ t = r := by simpa using htMem
  have htNeOne : t ≠ p.getVert 1 := by
    have hne := hqne 3 1 (by omega) (by omega) (by omega)
    have hstartOne : q.getVert 1 = p.getVert 1 := hone.symm
    have hend : q.getVert 3 = t := by
      rw [← hqlen]
      exact q.getVert_length
    simpa [hend, hstartOne] using hne
  refine ⟨htwo, ?_⟩
  exact (htCases.resolve_left htNeOne).symm

/-- Consequently the far designated edges of two such directed threads
are equal. -/
theorem twoThread_lastEdge_eq_of_getVert_one_eq
    {v r t : V} (p : G.Walk v r) (q : G.Walk v t)
    (hp : IsKThread G p 2) (hq : IsKThread G q 2)
    (hone : p.getVert 1 = q.getVert 1) :
    threadLastEdge G p hp = threadLastEdge G q hq := by
  obtain ⟨htwo, hrt⟩ := twoThread_tail_eq_of_getVert_one_eq G p q hp hq hone
  apply Subtype.ext
  simp only [threadLastEdge]
  rw [htwo, hrt]

/-! ## Normalized critical failures -/

/-- A failure of Condition 3 normalized so that the leaf neighbour `v` is
the start of the 2-thread and the matching guard `v-a` is its first edge. -/
def LeafC3CriticalFailure
    {u v a : V} (huv : G.Adj u v) (hva : G.Adj v a)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4) : Prop :=
  ∃ (t : V) (p : G.Walk v t) (hp : IsKThread G p 2),
    threadFirstEdge G p hp = (⟨s(v, a), hva⟩ : G.edgeSet) ∧
    ExternalEdgesInduced G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) v
      (threadFirstEdge G p hp) ∧
    ExternalEdgesInduced G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) t
      (threadLastEdge G p hp) ∧
    ExternalInducedColors G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) v
        (threadFirstEdge G p hp) =
      ExternalInducedColors G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) t
        (threadLastEdge G p hp)

/-- Any failure after recolouring a leaf edge has a normalized critical
witness.  The reverse-orientation case is normalized using the exact
first/last-edge identities above. -/
theorem leafC3CriticalFailure_of_not_conditionThree
    {u v a : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hau : a ≠ u)
    (old : G.edgeSet → OneTwoColor 4) (i : Fin 4)
    (hAold : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hold : ConditionThree G old)
    (hfail : ¬ ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i))) :
    LeafC3CriticalFailure G huv hva old i := by
  by_contra hnone
  apply hfail
  apply ConditionThree.recolor_leafEdge_of_matching_otherNeighbor G
    hu huv hva hau old i hAold hold
  intro r t p hp hcritical hleft hright
  intro heq
  apply hnone
  rcases hcritical with ⟨hr, hfirst⟩ | ⟨ht, hlast⟩
  · subst r
    exact ⟨t, p, hp, hfirst, hleft, hright, heq⟩
  · subst t
    refine ⟨r, p.reverse, hp.reverse, ?_, ?_, ?_, ?_⟩
    · exact (threadFirstEdge_reverse_two G p hp).trans hlast
    · rw [threadFirstEdge_reverse_two G p hp]
      exact hright
    · rw [threadLastEdge_reverse_two G p hp]
      exact hleft
    · rw [threadFirstEdge_reverse_two G p hp,
        threadLastEdge_reverse_two G p hp]
      exact heq.symm

/-- Recolouring the leaf edge by two different colours does not change an
external colour set at a vertex different from both endpoints of that leaf
edge. -/
theorem externalInducedColors_recolor_leaf_eq_of_endpoint_ne
    {u v t : V} (huv : G.Adj u v) (htu : t ≠ u) (htv : t ≠ v)
    (old : G.edgeSet → OneTwoColor 4) (i j : Fin 4)
    (threadEdge : G.edgeSet) :
    ExternalInducedColors G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) t threadEdge =
      ExternalInducedColors G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) t threadEdge := by
  let E : G.edgeSet := ⟨s(u, v), huv⟩
  have hagree : ColoringsAgreeOff G ({E} : Set G.edgeSet)
      (recolor G old E (some i)) (recolor G old E (some j)) := by
    intro e he
    have heE : e ≠ E := by simpa using he
    rw [recolor_ne G old (some i) heE, recolor_ne G old (some j) heE]
  apply externalInducedColors_eq_of_agreeOff G hagree
  intro e hext heS
  have heE : e = E := by simpa using heS
  subst e
  have htmem : t ∈ (E : Sym2 V) := hext.1
  have htCases : t = u ∨ t = v := by simpa [E] using htmem
  exact htCases.elim htu htv

/-- The far endpoint of a certified 2-thread from a leaf neighbour is
different from both endpoints of the leaf edge. -/
theorem twoThread_far_endpoint_ne_leaf_ends
    {u v t : V} (hu : G.degree u = 1) (p : G.Walk v t)
    (hp : IsKThread G p 2) : t ≠ u ∧ t ≠ v := by
  constructor
  · intro htu
    have htThree := hp.end_three
    unfold IsThreeVertex at htThree
    rw [htu, hu] at htThree
    omega
  · intro htv
    have hlen : p.length = 3 := by simpa using hp.length
    have hinj := hp.1.getVert_injOn
      (show 0 ∈ {z : ℕ | z ≤ p.length} by simp)
      (show 3 ∈ {z : ℕ | z ≤ p.length} by simp [hlen])
      (show p.getVert 0 = p.getVert 3 by
        have hend : p.getVert 3 = t := by
          rw [← hlen]
          exact p.getVert_length
        simp [hend, htv])
    omega

/-! ## The two-colour Condition-3 choice -/

/-- Two distinct available colours for the leaf edge cannot both violate
Condition 3 in the degree-three normal form.  A critical failure is forced
onto the unique directed 2-thread beginning with the matching guard `v-a`.
Its far external palette is independent of the colour put on the leaf edge,
whereas its palette at `v` is `{leafColour, beta}`. -/
theorem conditionThree_for_one_of_two_available_leaf_colours
    {u v a b : V} (hu : G.degree u = 1) (huv : G.Adj u v)
    (hva : G.Adj v a) (hvb : G.Adj v b)
    (hau : a ≠ u) (hbu : b ≠ u) (hab : a ≠ b)
    (hN : G.neighborFinset v = {u, a, b})
    (old : G.edgeSet → OneTwoColor 4) (beta : Fin 4)
    (hA : old (⟨s(v, a), hva⟩ : G.edgeSet) = none)
    (hB : old (⟨s(v, b), hvb⟩ : G.edgeSet) = some beta)
    (hold : ConditionThree G old)
    {i j : Fin 4} (hij : i ≠ j)
    (hi : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old
      (⟨s(u, v), huv⟩ : G.edgeSet) (some i))
    (_hj : ColorAvailableOn G
      (RetainedEdges (deleteLeafEdge G huv) G) old
      (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) :
    ConditionThree G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) ∨
      ConditionThree G
        (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) := by
  have hiBeta : i ≠ beta :=
    available_leaf_colour_ne_other_branch_colour G huv hvb hbu old beta i hB hi
  by_contra hboth
  have hfailI : ¬ ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) :=
    fun h ↦ hboth (Or.inl h)
  have hfailJ : ¬ ConditionThree G
      (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) :=
    fun h ↦ hboth (Or.inr h)
  obtain ⟨ti, pi, hpi, hfirstI, hleftI, hrightI, heqI⟩ :=
    leafC3CriticalFailure_of_not_conditionThree G hu huv hva hau old i
      hA hold hfailI
  obtain ⟨tj, pj, hpj, hfirstJ, hleftJ, hrightJ, heqJ⟩ :=
    leafC3CriticalFailure_of_not_conditionThree G hu huv hva hau old j
      hA hold hfailJ
  have hpiOne : pi.getVert 1 = a :=
    getVert_one_eq_of_threadFirstEdge_eq G hva pi hpi hfirstI
  have hpjOne : pj.getVert 1 = a :=
    getVert_one_eq_of_threadFirstEdge_eq G hva pj hpj hfirstJ
  have hone : pi.getVert 1 = pj.getVert 1 := hpiOne.trans hpjOne.symm
  obtain ⟨_htwo, htij⟩ :=
    twoThread_tail_eq_of_getVert_one_eq G pi pj hpi hpj hone
  have hlast : threadLastEdge G pi hpi = threadLastEdge G pj hpj :=
    twoThread_lastEdge_eq_of_getVert_one_eq G pi pj hpi hpj hone
  have htiFar := twoThread_far_endpoint_ne_leaf_ends G hu pi hpi
  have hfarEq :
      ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) ti
          (threadLastEdge G pi hpi) =
        ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) tj
          (threadLastEdge G pj hpj) := by
    calc
      ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) ti
          (threadLastEdge G pi hpi) =
        ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) ti
          (threadLastEdge G pi hpi) :=
        externalInducedColors_recolor_leaf_eq_of_endpoint_ne G huv
          htiFar.1 htiFar.2 old i j (threadLastEdge G pi hpi)
      _ = ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) tj
          (threadLastEdge G pj hpj) :=
        congrArg₂
          (fun x e ↦ ExternalInducedColors G
            (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) x e)
          htij hlast
  have heqI' :
      ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) v
          (⟨s(v, a), hva⟩ : G.edgeSet) =
        ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) ti
          (threadLastEdge G pi hpi) := by
    rw [← hfirstI]
    exact heqI
  have heqJ' :
      ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) v
          (⟨s(v, a), hva⟩ : G.edgeSet) =
        ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) tj
          (threadLastEdge G pj hpj) := by
    rw [← hfirstJ]
    exact heqJ
  have hvEq :
      ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some i)) v
          (⟨s(v, a), hva⟩ : G.edgeSet) =
        ExternalInducedColors G
          (recolor G old (⟨s(u, v), huv⟩ : G.edgeSet) (some j)) v
          (⟨s(v, a), hva⟩ : G.edgeSet) :=
    heqI'.trans (hfarEq.trans heqJ'.symm)
  have hpaletteI := externalInducedColors_recolor_leaf_at_matching_guard G
    huv hva hvb hau hbu hab hN old beta i hB
  have hpaletteJ := externalInducedColors_recolor_leaf_at_matching_guard G
    huv hva hvb hau hbu hab hN old beta j hB
  have hpair : ({i, beta} : Set (Fin 4)) = {j, beta} :=
    hpaletteI.symm.trans (hvEq.trans hpaletteJ)
  have himem : i ∈ ({j, beta} : Set (Fin 4)) := by
    rw [← hpair]
    simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at himem
  exact himem.elim hij hiBeta

end Finite

end

end LeanCo.PackingEdgeColoring
