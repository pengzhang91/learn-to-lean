import LeanCo.PackingEdgeColoring.SectionFourLongThreeForkLocal

/-!
# Excluding three 3-threads at one centre in Section 4

This module completes the fresh-colour recolouring and gap restoration for
the paper's `no333` configuration.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Three displayed, pairwise distinct neighbors exhaust the neighborhood
of a degree-three vertex.  This local copy keeps the long-thread reduction
independent of the Section 3 configuration modules. -/
theorem longPair_neighborFinset_eq_three
    {u a b c : V} (hu : IsThreeVertex G u)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.neighborFinset u = {a, b, c} := by
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hu
  have hsubset : ({a, b, c} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxa | hxb | hxc
    · subst x
      exact (G.mem_neighborFinset u _).mpr hua
    · subst x
      exact (G.mem_neighborFinset u _).mpr hub
    · subst x
      exact (G.mem_neighborFinset u _).mpr huc
  have hthree : ({a, b, c} : Finset V).card = 3 := by
    simp [hab, hac, hbc]
  exact (Finset.eq_of_subset_of_card_le hsubset (by omega)).symm

theorem longPair_eq_one_of_three_of_adj
    {u a b c x : V} (hu : IsThreeVertex G u)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hux : G.Adj u x) : x = a ∨ x = b ∨ x = c := by
  have hx : x ∈ G.neighborFinset u :=
    (G.mem_neighborFinset u x).mpr hux
  rw [longPair_neighborFinset_eq_three G hu hua hub huc hab hac hbc] at hx
  simpa using hx

theorem longPair_firstEdges_ne_of_firstVertices_ne
    {u a b : V} (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b) :
    (⟨s(a, u), hua.symm⟩ : G.edgeSet) ≠
      (⟨s(b, u), hub.symm⟩ : G.edgeSet) := by
  intro heq
  have hv : s(a, u) = s(b, u) := congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hv
  rcases hv with hv | hv
  · exact hab hv.1
  · exact hua.ne hv.1.symm

/-- With three displayed arms at a degree-three centre, the external
palette of one arm is exactly the colours on the other two first edges. -/
theorem longPair_externalPalette_eq_pair_threeForks
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ x₃ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ThreeThreadCore G u x₁ x₂ x₃ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j) :
    ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = {i, j} := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  have hPQ : P ≠ Q := by
    simpa [P, Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  ext a
  constructor
  · rintro ⟨f, ⟨huf, hfP⟩, hfa⟩
    obtain ⟨q, hfq⟩ := Sym2.mem_iff_exists.mp huf
    have huq : G.Adj u q := by
      have := f.2
      rw [hfq] at this
      simpa using this
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx huq with rfl | rfl | rfl
    · have hfEq : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfq)
      exact False.elim (hfP hfEq)
    · have hfEq : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfq)
      have hfa' : colour Q = some a := by simpa [hfEq] using hfa
      have hai : a = i := Option.some.inj (hfa'.symm.trans hQ)
      simp [hai]
    · have hfEq : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfq)
      have hfa' : colour T = some a := by simpa [hfEq] using hfa
      have haj : a = j := Option.some.inj (hfa'.symm.trans hT)
      simp [haj]
  · intro ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact ⟨Q, ⟨by simp [Q], hPQ.symm⟩, by simpa [Q] using hQ⟩
    · exact ⟨T, ⟨by simp [T], hPT.symm⟩, by simpa [T] using hT⟩

/-- Among four induced colours, a two-element palette and one edge colour
cannot forbid every choice. -/
theorem longPair_exists_fresh_outside_two_palette
    (L : Set (Fin 4)) (hL : L.ncard = 2) (c : OneTwoColor 4) :
    ∃ k : Fin 4, k ∉ L ∧ c ≠ some k := by
  classical
  cases hc : c with
  | none =>
      have hex : ∃ k : Fin 4, k ∉ L := by
        by_contra hn
        push_neg at hn
        have huniv : L = Set.univ := Set.eq_univ_of_forall hn
        rw [huniv] at hL
        norm_num at hL
      obtain ⟨k, hk⟩ := hex
      exact ⟨k, hk, by simp [hc]⟩
  | some d =>
      have hex : ∃ k : Fin 4, k ∉ insert d L := by
        by_contra hn
        push_neg at hn
        have huniv : insert d L = Set.univ := Set.eq_univ_of_forall hn
        have hcard := Set.ncard_insert_le d L
        rw [huniv, hL] at hcard
        norm_num at hcard
      obtain ⟨k, hk⟩ := hex
      have hkdata : k ≠ d ∧ k ∉ L := by
        simpa only [Set.mem_insert_iff, not_or] using hk
      have hkd : k ≠ d := hkdata.1
      have hkL : k ∉ L := hkdata.2
      exact ⟨k, hkL, by simpa [hc] using hkd.symm⟩

/-- In a three-long-arm fork, a colour absent from the external palette at
the centre and from the next edge of the chosen arm is available on that
arm's first edge.  Matching second edges on both unselected arms shield all
remaining distance-two conflicts. -/
theorem longPair_forkFirst_fresh_available_threeForks
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ x₃ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ThreeThreadCore G u x₁ x₂ x₃ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (Dset : Set G.edgeSet)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.left_adj⟩ : G.edgeSet) = none)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDk : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ≠ some k)
    (hretained : ∀ f : G.edgeSet, f ∈ Dset → v₂ ∉ (f : Sym2 V)) :
    ColorAvailableOn G Dset colour
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.left_adj⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hC' : colour C = none := by simpa [C] using hC
  have hS' : colour S = none := by simpa [S] using hS
  have hDk' : colour D ≠ some k := by simpa [D] using hDk
  have hPT : P ≠ T := by
    intro heq
    have hv : s(v₁, u) = s(x₁, u) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hv
    rcases hv with hv | hv
    · exact hvx hv.1
    · exact h.first_adj.ne hv.1.symm
  have noAtU (f : G.edgeSet) (hfQ : f ≠ Q)
      (huf : u ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have := f.2
      rw [hfa] at this
      simpa using this
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      have hfalse : none = some k := hP'.symm.trans (by simpa [hfP] using hcf)
      simp at hfalse
    · have hfQ' : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      exact hfQ hfQ'
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      apply hk
      exact ⟨T, ⟨by simp [T], hPT.symm⟩, by simpa [hfT] using hcf⟩
  have noAtV₁ (f : G.edgeSet) (hfD : f ∈ Dset)
      (hvf : v₁ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start f hvf with hfA | hfP
    · have hfA' : f = A := Subtype.ext (by simpa [A] using hfA)
      exact hretained f hfD (by simpa [hfA', A])
    · have hfP' : f = P := Subtype.ext (by simpa [P] using hfP)
      have hfalse : none = some k := hP'.symm.trans (by simpa [hfP'] using hcf)
      simp at hfalse
  have noAtW₁ (f : G.edgeSet) (hfQ : f ≠ Q)
      (hwf : w₁ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.left_adj g.first_adj.symm g.middle_ne_start f hwf with hfC | hfQ'
    · have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
      have hfalse : none = some k := hC'.symm.trans (by simpa [hfC'] using hcf)
      simp at hfalse
    · exact hfQ (Subtype.ext (by simpa [Q] using hfQ'))
  have noAtX₁ (f : G.edgeSet)
      (hxf : x₁ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.left_adj r.first_adj.symm r.middle_ne_start f hxf with hfS | hfT
    · have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
      have hfalse : none = some k := hS'.symm.trans (by simpa [hfS'] using hcf)
      simp at hfalse
    · have hfT' : f = T := Subtype.ext (by simpa [T] using hfT)
      apply hk
      exact ⟨T, ⟨by simp [T], hPT.symm⟩, by simpa [hfT'] using hcf⟩
  have noAtW₂ (f : G.edgeSet)
      (hwf : w₂ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.middle_two
        g.left_adj.symm g.right_adj g.first_ne_third f hwf with hfC | hfD
    · have hfC' : f = C := Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC)
      have hfalse : none = some k := hC'.symm.trans (by simpa [hfC'] using hcf)
      simp at hfalse
    · have hfD' : f = D := Subtype.ext (by simpa [D] using hfD)
      exact hDk' (by simpa [hfD'] using hcf)
  apply (colorAvailableOn_some_iff G Dset colour Q k).mpr
  intro f hfD hfQ hcf
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = w₁ ∨ a = u := by simpa [Q] using ha
  rcases hacase with haw | hau
  · constructor
    · intro hwb
      have hwb' : w₁ = b := haw.symm.trans hwb
      exact noAtW₁ f hfQ (by rw [hwb']; exact hbf) hcf
    · intro hwb
      have hwb' : G.Adj w₁ b := by simpa [haw] using hwb
      have hbN : b ∈ G.neighborFinset w₁ :=
        (G.mem_neighborFinset w₁ b).mpr hwb'
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.left_adj g.first_adj.symm g.middle_ne_start] at hbN
      have hbcase : b = w₂ ∨ b = u := by simpa using hbN
      exact hbcase.elim
        (fun hb ↦ noAtW₂ f (by simpa [hb] using hbf) hcf)
        (fun hb ↦ noAtU f hfQ (by simpa [hb] using hbf) hcf)
  · constructor
    · intro hub
      have hub' : u = b := hau.symm.trans hub
      exact noAtU f hfQ (by rw [hub']; exact hbf) hcf
    · intro hub
      have hub' : G.Adj u b := by simpa [hau] using hub
      rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
          g.first_adj r.first_adj hvw hvx hwx hub' with rfl | rfl | rfl
      · exact noAtV₁ f hfD hbf hcf
      · exact noAtW₁ f hfQ hbf hcf
      · exact noAtX₁ f hbf hcf

/-- Replacing one induced colour on the first edge of a 3-thread by another
induced colour preserves matching saturation when the following edge is
matching-coloured. -/
theorem longPair_oneSaturated_recolor_forkFirst_induced
    {u w₁ w₂ w₃ t : V}
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : OneSaturated G colour)
    (i k : Fin 4)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none) :
    OneSaturated G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  classical
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hCQ : C ≠ Q := by
    intro heq
    have hv : s(w₁, w₂) = s(w₁, u) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hv
    rcases hv with hv | hv
    · exact g.middle_ne_start hv.2
    · exact g.first_adj.ne hv.1.symm
  have hnewQ : new Q = some k := by simp [new]
  have hnewC : new C = none := by
    rw [show new C = colour C by exact recolor_ne G colour (some k) hCQ]
    simpa [C] using hC
  change OneSaturated G new
  intro e he
  by_cases heQ : e = Q
  · subst e
    exact ⟨C, hnewC, w₁, by simp [Q], by simp [C]⟩
  · have heOld : colour e ≠ none := by
      intro heNone
      apply he
      rw [show new e = colour e by exact recolor_ne G colour (some k) heQ]
      exact heNone
    obtain ⟨f, hf, y, hye, hyf⟩ := hold e heOld
    have hfQ : f ≠ Q := by
      intro hfEq
      subst f
      have hQnone : colour Q = none := hf
      have hQsome : colour Q = some i := by simpa [Q] using hQ
      have hfalse : none = some i := hQnone.symm.trans hQsome
      simp at hfalse
    refine ⟨f, ?_, y, hye, hyf⟩
    rw [show new f = colour f by exact recolor_ne G colour (some k) hfQ]
    exact hf

/-- The complete prepared-gap preservation package for the fresh induced
recolouring used in the hard `(3,3,3)` case. -/
theorem longPair_prepared_recolor_forkFirst_fresh_threeForks
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ x₃ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ThreeThreadCore G u x₁ x₂ x₃ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.left_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDk : colour (⟨s(w₂, w₃), g.right_adj⟩ : G.edgeSet) ≠ some k)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    PreparedThreeThreadGap G h
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have havail : ColorAvailableOn G Dset colour Q (some k) := by
    exact longPair_forkFirst_fresh_available_threeForks G h g r hvw hvx hwx
      colour Dset k hP hC hS hk hDk (fun f hf ↦
        (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalid : IsOneTwoColoringOn G Dset new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := Q) (a := some k) (by simpa [Dset, Q] using hQD)).mpr
    refine ⟨?_, havail⟩
    exact IsOneTwoColoringOn.mono (G := G) (by simpa [Dset] using hprepared.1)
      Set.diff_subset
  have hsat : OneSaturated G new := by
    exact longPair_oneSaturated_recolor_forkFirst_induced G g colour
      hprepared.2.1 i k hQ hC
  have htwo : ConditionTwo G new := by
    exact longThreeFork_conditionTwo_recolor_forkFirst_induced G hsub h g r
      hvw hvx hwx colour hprepared.2.2.1 k hP hC hS hA hB
  have hthree : ConditionThree G new := by
    exact longThreeFork_conditionThree_recolor_forkFirst_induced G h g colour
      hprepared.2.2.2 k hP (by simpa [P, Q] using hPQ)
  exact ⟨hvalid, hsat, htwo, hthree⟩

/-- Fill the two missing edges after a local neighbour-arm recolouring.
The left gap receives `i`, the right gap receives `k`; the displayed
cross-palette hypotheses are exactly the remaining availability and
Condition-2 obligations. -/
theorem longPair_hasGoodFour_of_prepared_cross_fill
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (base : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h base)
    (i k l : Fin 4)
    (hA : base (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : base (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hP : base (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : base (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hiL : i ∉ ExternalInducedColors G base u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hkR : k ∉ ExternalInducedColors G base z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hiR : i ∈ ExternalInducedColors G base z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hkL : k ∈ ExternalInducedColors G base u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hlL : l ∉ insert i (ExternalInducedColors G base u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)))
    (hlR : l ∉ insert k (ExternalInducedColors G base z
      (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let S : Set G.edgeSet := {A, B}
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hRD : R ∈ Dset := by
    change R ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [R, h.right_adj.ne, h.middle_ne_end]
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
  have hAR : A ≠ R := fun heq ↦ hAD (heq ▸ hRD)
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD)
  have hBR : B ≠ R := fun heq ↦ hBD (heq ▸ hRD)
  have havailA : ColorAvailableOn G Dset base A (some i) := by
    exact longPair_left_gap_available_of_missing_external G h base
      (by simpa [P] using hP) (by simpa [R] using hR) i
      (by simpa [P] using hiL)
  let afterA : G.edgeSet → OneTwoColor 4 := recolor G base A (some i)
  have hbaseOn : IsOneTwoColoringOn G Dset base := by
    simpa [Dset] using hprepared.1
  have hafterAOn : IsOneTwoColoringOn G (insert A Dset) afterA :=
    hbaseOn.extend_one G hAD havailA
  have hafterAA : afterA A = some i := by simp [afterA]
  have hafterAP : afterA P = none := by
    rw [show afterA P = base P by exact recolor_ne G base (some i) hAP.symm]
    simpa [P] using hP
  have hafterAR : afterA R = none := by
    rw [show afterA R = base R by exact recolor_ne G base (some i) hAR.symm]
    simpa [R] using hR
  have hRpalA : ExternalInducedColors G base z R =
      ExternalInducedColors G afterA z R := by
    apply externalInducedColors_eq_of_agreeOff G
      (coloringsAgreeOff_recolor G base A (some i))
    intro e hext heA
    apply longPair_gap_misses_external_end G h e (by simpa [R] using hext)
    have heq : e = A := by simpa using heA
    simpa [A, B] using (show e = A ∨ e = B from Or.inl heq)
  have hkRA : k ∉ ExternalInducedColors G afterA z R := by
    rw [← hRpalA]
    simpa [R] using hkR
  have hik : i ≠ k := by
    intro hik
    subst k
    exact hiL hkL
  have havailB : ColorAvailableOn G (insert A Dset) afterA B (some k) := by
    exact longPair_right_gap_available_of_cross_colour G h afterA i k hik
      (by simpa [A] using hafterAA) (by simpa [P] using hafterAP)
      (by simpa [R] using hafterAR) (by simpa [R] using hkRA)
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterA B (some k)
  have hBfresh : B ∉ insert A Dset := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨hAB.symm, hBD⟩
  have hfinalOn : IsOneTwoColoringOn G (insert B (insert A Dset)) final :=
    hafterAOn.extend_one G hBfresh havailB
  have hvalid : IsOneTwoColoring G final := by
    simpa [IsOneTwoColoring, Dset, A, B,
      insert_threeThread_gap_retained_eq_univ G h] using hfinalOn
  have hagree : ColoringsAgreeOff G S base final := by
    intro e he
    have hne : e ≠ A ∧ e ≠ B := by simpa [S] using he
    simp [final, afterA, hne.1, hne.2]
  have hfinalA : final A = some i := by simp [final, afterA, hAB]
  have hfinalB : final B = some k := by simp [final]
  have hfinalP : final P = none := by
    simp [final, afterA, hAP.symm, hBP.symm, P, hP]
  have hfinalR : final R = none := by
    simp [final, afterA, hAR.symm, hBR.symm, R, hR]
  have hLpal : ExternalInducedColors G base u P =
      ExternalInducedColors G final u P := by
    apply externalInducedColors_eq_of_agreeOff G hagree
    intro e hext
    exact longPair_gap_misses_external_start G h e (by simpa [P] using hext)
  have hRpal : ExternalInducedColors G base z R =
      ExternalInducedColors G final z R := by
    apply externalInducedColors_eq_of_agreeOff G hagree
    intro e hext
    exact longPair_gap_misses_external_end G h e (by simpa [R] using hext)
  have hsaturated : OneSaturated G final := by
    intro e he
    by_cases heA : e = A
    · subst e
      exact ⟨P, hfinalP, v₁, by simp [A], by simp [P]⟩
    by_cases heB : e = B
    · subst e
      exact ⟨R, hfinalR, v₃, by simp [B], by simp [R]⟩
    have heOld : base e ≠ none := by
      intro heNone
      apply he
      exact (hagree e (by simpa [S, heA, heB])).symm.trans heNone
    obtain ⟨f, hf, q, hqe, hqf⟩ := hprepared.2.1 e heOld
    by_cases hfA : f = A
    · subst f
      have hqcase : q = v₁ ∨ q = v₂ := by simpa [A] using hqf
      rcases hqcase with hqv₁ | hqv₂
      · exact ⟨P, hfinalP, q, hqe, by simpa [P, hqv₁]⟩
      · have hqmem : v₂ ∈ (e : Sym2 V) := by simpa [hqv₂] using hqe
        rcases edge_eq_left_or_right_of_incident_two G h.middle_two
            h.left_adj.symm h.right_adj h.first_ne_third e hqmem with heA' | heB'
        · exact False.elim (heA (Subtype.ext (by simpa [A, Sym2.eq_swap] using heA')))
        · exact False.elim (heB (Subtype.ext (by simpa [B, Sym2.eq_swap] using heB')))
    · by_cases hfB : f = B
      · subst f
        have hqcase : q = v₃ ∨ q = v₂ := by simpa [B] using hqf
        rcases hqcase with hqv₃ | hqv₂
        · exact ⟨R, hfinalR, q, hqe, by simpa [R, hqv₃]⟩
        · have hqmem : v₂ ∈ (e : Sym2 V) := by simpa [hqv₂] using hqe
          rcases edge_eq_left_or_right_of_incident_two G h.middle_two
              h.left_adj.symm h.right_adj h.first_ne_third e hqmem with heA' | heB'
          · exact False.elim (heA (Subtype.ext (by simpa [A, Sym2.eq_swap] using heA')))
          · exact False.elim (heB (Subtype.ext (by simpa [B, Sym2.eq_swap] using heB')))
      · refine ⟨f, ?_, q, hqe, hqf⟩
        exact (hagree f (by simpa [S, hfA, hfB])).symm.trans hf
  have hpalette : ∀ q : V, q = v₁ ∨ q = v₂ ∨ q = v₃ →
      VertexSeesMatching G final q →
      ¬ ∀ a : Fin 4, VertexSeesInduced G final q a := by
    intro q hq hmatch hall
    rcases hq with rfl | rfl | rfl
    · apply longPair_not_vertexSeesInduced_first_of_palette_bound G h final
        i k l hfinalA hfinalB hfinalP
      · rw [← hLpal]
        simpa [P] using hkL
      · rw [← hLpal]
        simpa [P] using hlL
      · exact hall l
    · exact (longPair_paletteCondition_at_two_two_neighbours G
        h.middle_two h.left_adj.symm h.right_adj h.first_ne_third
        h.first_two h.third_two hmatch) hall
    · apply longPair_not_vertexSeesInduced_end_of_palette_bound G h final
        i k l hfinalA hfinalB hfinalR
      · rw [← hRpal]
        simpa [R] using hiR
      · rw [← hRpal]
        simpa [R] using hlR
      · exact hall l
  have hgood : GoodFour G final :=
    longPair_goodFour_of_preparedThreeThreadGap_recolour G h base final
      hprepared hvalid hsaturated (by simpa [S, A, B] using hagree) hpalette
  let d : DecidableRel G.Adj := inferInstance
  rw [HasGoodFour]
  exact ⟨final, goodFour_change_decidableRel d (Classical.decRel _) final hgood⟩

/-- The complete hard-colour case for three distinct 3-thread arms.  The
matching second-edge hypotheses are precisely Claim 1; all colour choices
and both missing-edge extensions are constructed internally. -/
theorem longPair_hasGoodFour_of_threeFork_hard
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ x₃ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : ThreeThreadCore G u x₁ x₂ x₃ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.left_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzQ : z ∉ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet).1) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let D : G.edgeSet := ⟨s(w₂, w₃), g.right_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.left_adj⟩
  have hPQ : P ≠ Q := by
    simpa [P, Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  have hQT : Q ≠ T := by
    simpa [Q, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G g.first_adj r.first_adj hwx
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet v₂) G
    rw [mem_retained_deleteIncidenceSet_iff]
    simp [P, h.left_adj.ne.symm, h.middle_ne_start]
  have hQD' : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hTD' : T ∈ Dset := by simpa [Dset, T] using hTD
  have hvalid : IsOneTwoColoringOn G Dset colour := by
    simpa [Dset] using hprepared.1
  have hQne : colour Q ≠ none := by
    intro hQnone
    have hp := hvalid P hPD Q hQD' hPQ
    have hdisj : EndpointDisjoint G P Q := by
      simpa [P, Q, hP, hQnone] using hp
    exact hdisj u (by simp [P]) (by simp [Q])
  have hTne : colour T ≠ none := by
    intro hTnone
    have hp := hvalid P hPD T hTD' hPT
    have hdisj : EndpointDisjoint G P T := by
      simpa [P, T, hP, hTnone] using hp
    exact hdisj u (by simp [P]) (by simp [T])
  cases hQval : colour Q with
  | none => exact False.elim (hQne hQval)
  | some i =>
    cases hTval : colour T with
    | none => exact False.elim (hTne hTval)
    | some j =>
      have hij : i ≠ j := by
        intro hij
        subst j
        have hp := hvalid Q hQD' T hTD' hQT
        have hsep : InducedSeparated G Q T := by
          simpa [hQval, hTval] using hp
        exact hsep.1 u (by simp [Q]) (by simp [T])
      have hLold : ExternalInducedColors G colour u P = {i, j} := by
        simpa [P, Q, T] using
          longPair_externalPalette_eq_pair_threeForks G h g r hvw hvx hwx
            colour i j hP (by simpa [Q] using hQval)
              (by simpa [T] using hTval)
      have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by
        simp [hij]
      obtain ⟨k, hkPair, hDk⟩ :=
        longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
          hpairCard (colour D)
      have hkData : k ≠ i ∧ k ≠ j := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hkPair
      have hkOld : k ∉ ExternalInducedColors G colour u P := by
        rw [hLold]
        exact hkPair
      let fresh : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
      have hpreparedFresh : PreparedThreeThreadGap G h fresh := by
        exact longPair_prepared_recolor_forkFirst_fresh_threeForks G hsub h g r
          hvw hvx hwx colour hprepared i k hP
          (by simpa [Q] using hQval) hC hS hA hB
          (by simpa [P] using hkOld) (by simpa [D] using hDk) hQD
      have hfreshP : fresh P = none := by
        rw [show fresh P = colour P by exact recolor_ne G colour (some k) hPQ]
        simpa [P] using hP
      have hfreshR : fresh R = none := by
        have hRQ : R ≠ Q := by
          intro heq
          apply hzQ
          have hzR : z ∈ (R : Sym2 V) := by simp [R]
          rw [heq] at hzR
          exact hzR
        rw [show fresh R = colour R by exact recolor_ne G colour (some k) hRQ]
        simpa [R] using hR
      have hfreshA : fresh A = none := by
        have hAQ : A ≠ Q := by
          intro heq
          have hAD : A ∉ Dset := by
            simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
          exact hAD (heq ▸ hQD')
        rw [show fresh A = colour A by exact recolor_ne G colour (some k) hAQ]
        simpa [A] using hA
      have hfreshB : fresh B = none := by
        have hBQ : B ≠ Q := by
          intro heq
          have hBD : B ∉ Dset := by
            simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
          exact hBD (heq ▸ hQD')
        rw [show fresh B = colour B by exact recolor_ne G colour (some k) hBQ]
        simpa [B] using hB
      have hfreshQ : fresh Q = some k := by simp [fresh]
      have hfreshT : fresh T = some j := by
        rw [show fresh T = colour T by
          exact recolor_ne G colour (some k) hQT.symm]
        simpa [T] using hTval
      have hLfresh : ExternalInducedColors G fresh u P = {k, j} := by
        simpa [P, Q, T] using
          longPair_externalPalette_eq_pair_threeForks G h g r hvw hvx hwx
            fresh k j (by simpa [P] using hfreshP)
              (by simpa [Q] using hfreshQ) (by simpa [T] using hfreshT)
      have hagreeFresh : ColoringsAgreeOff G ({Q} : Set G.edgeSet)
          colour fresh := by
        simpa [fresh] using coloringsAgreeOff_recolor G colour Q (some k)
      have hRunchanged : ExternalInducedColors G colour z R =
          ExternalInducedColors G fresh z R := by
        apply externalInducedColors_eq_of_agreeOff G hagreeFresh
        intro e hext heQ
        have heq : e = Q := by simpa using heQ
        subst e
        exact hzQ hext.1
      have hRfresh : ExternalInducedColors G fresh z R = {i, j} := by
        calc
          ExternalInducedColors G fresh z R =
              ExternalInducedColors G colour z R := hRunchanged.symm
          _ = ExternalInducedColors G colour u P := hpal.symm
          _ = {i, j} := hLold
      obtain ⟨l, hlPair, hklOpt⟩ :=
        longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
          hpairCard (some k)
      have hlData : l ≠ i ∧ l ≠ j := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hlPair
      have hkl : k ≠ l := by
        intro hEq
        apply hklOpt
        simp [hEq]
      apply longPair_hasGoodFour_of_prepared_cross_fill G hsub h fresh
        hpreparedFresh i k l hfreshA hfreshB hfreshP hfreshR
      · rw [hLfresh]
        simp [hkData.1.symm, hij]
      · rw [hRfresh]
        exact hkPair
      · rw [hRfresh]
        simp
      · rw [hLfresh]
        simp
      · rw [hLfresh]
        simp [hlData.1, hlData.2, hkl.symm]
      · rw [hRfresh]
        simp [hlData.1, hlData.2, hkl.symm]

/-- Kernel-level reduction of the paper's `no333` configuration.  A good
colouring after deleting the middle vertex of one arm contradicts badness
whenever three certified 3-threads leave the same centre through distinct
first neighbours. -/
theorem longPair_no_threeThreeThree_of_smaller_good
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u y}
    (hp : IsKThread G p 3) (hq : IsKThread G q 3) (hr : IsKThread G r 3)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) : False := by
  classical
  let h := hp.threeThreadCore G
  let g := hq.threeThreadCore G
  let sCore := hr.threeThreadCore G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le (p.getVert 2)) small
  let P : G.edgeSet := threadFirstEdge G p hp
  let R : G.edgeSet := threadLastEdge G p hp
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := threadFirstEdge G r hr
  let A : G.edgeSet :=
    ⟨s(p.getVert 1, p.getVert 2),
      p.adj_getVert_succ (i := 1) (by
        have hlen : p.length = 4 := by simpa using hp.length
        omega)⟩
  let B : G.edgeSet :=
    ⟨s(p.getVert 3, p.getVert 2),
      (p.adj_getVert_succ (i := 2) (by
        have hlen : p.length = 4 := by simpa using hp.length
        omega)).symm⟩
  have hpLen : p.length = 4 := by simpa using hp.length
  have hpGetNe (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) (hab : a ≠ b) :
      p.getVert a ≠ p.getVert b := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using ha)
      (show b ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using hb)
      heq
    exact hab hinj
  have hpEnd : p.getVert 4 = z := by
    rw [← hpLen]
    exact p.getVert_length
  let pL : G.Walk u (p.getVert 2) := p.take 2
  have hpL : pL.IsPath := hp.1.take 2
  have hnotU₂ : ¬ G.Adj u (p.getVert 2) := by
    intro hadj
    exact longPair_not_adj_endpoints_of_short_path G hgirth hpL
      (by simp [pL, hpLen]) (by simp [pL, hpLen]) hadj.symm
  have hu₂ : u ≠ p.getVert 2 := by
    simpa using hpGetNe 0 2 (by omega) (by omega) (by omega)
  have hQD : Q ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G hu₂ hnotU₂
      Q (by simp [Q, threadFirstEdge])
  have hTD : T ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G hu₂ hnotU₂
      T (by simp [T, threadFirstEdge])
  obtain ⟨hP, hR, hpal⟩ :=
    longPair_threeThread_hard_normal_form_of_no_goodFour G hgirth h small
      hsmall hsub hbad
  have hC := longPair_fork_second_matching_in_bad_graph G hgirth hp hq hpq
    small hsmall hsub hbad
  have hS := longPair_fork_second_matching_in_bad_graph G hgirth hp hr hpr
    small hsmall hsub hbad
  have hprepared : PreparedThreeThreadGap G h base := by
    exact preparedThreeThreadGap_of_goodFour G hsub h small hsmall
  have hAD : A ∉ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G := by
    simpa [h, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G := by
    simpa [h, B, Sym2.eq_swap] using right_chain_edge_not_retained G h.right_adj
  have hA : base A = none := by
    have hAe : A.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [RetainedEdges] using hAD
    simp [base, transportColoringToSupergraph, hAe]
  have hB : base B = none := by
    have hBe : B.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [RetainedEdges] using hBD
    simp [base, transportColoringToSupergraph, hBe]
  have hzQ : z ∉ (Q : Sym2 V) := by
    intro hz
    have hzcase : z = u ∨ z = q.getVert 1 := by
      simpa [Q, threadFirstEdge] using hz
    rcases hzcase with hzu | hzq
    · apply hpGetNe 4 0 (by omega) (by omega) (by omega)
      simpa [hpEnd] using hzu
    · have hzThree : IsThreeVertex G z := hp.end_three
      have hqTwo : IsTwoVertex G (q.getVert 1) :=
        IsKThread.internal_two G hq (by omega) (by
          have hlen : q.length = 4 := by simpa using hq.length
          omega)
      exact (isThreeVertex_ne_isTwoVertex G hzThree hqTwo) hzq
  apply hbad
  exact longPair_hasGoodFour_of_threeFork_hard G hsub h g sCore hpq hpr hqr
    base hprepared
    (by simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP)
    (by simpa [h, base, R, threadLastEdge] using hR)
    (by simpa [h, A] using hA) (by simpa [h, B] using hB)
    (by simpa [g, base] using hC) (by simpa [sCore, base] using hS)
    (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQD)
    (by simpa [sCore, T, threadFirstEdge, Sym2.eq_swap] using hTD)
    (by simpa [h, base, P, R, threadFirstEdge, threadLastEdge,
      Sym2.eq_swap] using hpal)
    (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hzQ)

end Finite

end

end LeanCo.PackingEdgeColoring
