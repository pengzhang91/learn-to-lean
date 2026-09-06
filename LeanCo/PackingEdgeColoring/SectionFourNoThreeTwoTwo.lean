import LeanCo.PackingEdgeColoring.SectionFourLongTwoThreadSecondMatching

/-!
# Excluding a `(3,2,2)` fork in Section 4

This module carries out the local recolourings around a three-vertex incident
with one 3-thread and two 2-threads.  The selected 3-thread is opened at its
middle vertex, exactly as in the preceding long-thread reductions.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The two-step prefix underlying a certified 2-thread. -/
theorem TwoThreadCoreData.twoStepArmCore
    {u w₁ w₂ t : V} (g : TwoThreadCoreData G u w₁ w₂ t) :
    TwoStepArmCore G u w₁ w₂ :=
  ⟨g.first_two, g.second_two, g.first_adj, g.middle_adj, g.second_ne_start⟩

/-- At the common end of the three displayed arms, the external palette of
the selected arm is exactly the colours on the two 2-thread first edges. -/
theorem longPair_externalPalette_eq_pair_twoTwoArms
    {u v₁ v₂ v₃ z w₁ w₂ t x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ t)
    (r : TwoThreadCoreData G u x₁ x₂ y)
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
      have hf := f.2
      rw [hfq] at hf
      simpa using hf
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

/-- External data at the common centre after the first edge of a displayed
2-thread has become matching.  Only the first-edge data of the other arm is
used, so this is the `(3,2,2)` analogue of the long-fork helper. -/
theorem longPair_twoThreadFirst_external_data_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4) (d i : Fin 4)
    (hT : colour (threadFirstEdge G q hq) = none)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = some d)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i) :
    ExternalEdgesInduced G colour u (threadFirstEdge G q hq) ∧
      ExternalInducedColors G colour u (threadFirstEdge G q hq) = {d, i} := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G g.first_adj
        hq.first_step_adj hwq
  have classify (f : G.edgeSet) (huf : u ∈ (f : Sym2 V)) :
      f = P ∨ f = Q ∨ f = T := by
    obtain ⟨x, hfx⟩ := Sym2.mem_iff_exists.mp huf
    have hux : G.Adj u x := by
      have hf := f.2
      rw [hfx] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj hq.first_step_adj hvw hvq hwq hux with rfl | rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa [P, Sym2.eq_swap] using hfx))
    · exact Or.inr (Or.inl
        (Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfx)))
    · exact Or.inr (Or.inr
        (Subtype.ext (by simpa [T, threadFirstEdge] using hfx)))
  constructor
  · intro f hfext
    rcases classify f hfext.1 with rfl | rfl | rfl
    · exact ⟨d, by simpa [P] using hP⟩
    · exact ⟨i, by simpa [Q] using hQ⟩
    · exact False.elim (hfext.2 rfl)
  · ext a
    constructor
    · rintro ⟨f, hfext, hfa⟩
      rcases classify f hfext.1 with rfl | rfl | rfl
      · have hfaP : colour P = some a := by simpa [P] using hfa
        have had : a = d := Option.some.inj
          (hfaP.symm.trans (by simpa [P] using hP))
        simp [had]
      · have hfaQ : colour Q = some a := by simpa [Q] using hfa
        have hai : a = i := Option.some.inj
          (hfaQ.symm.trans (by simpa [Q] using hQ))
        simp [hai]
      · exact False.elim (hfext.2 rfl)
    · intro ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact ⟨P, ⟨by simp [P], hPT⟩, by simpa [P] using hP⟩
      · exact ⟨Q, ⟨by simp [Q], hQT⟩, by simpa [Q] using hQ⟩

/-- A colour absent from both other first edges and from both following
2-thread edges is available on the selected first edge. -/
theorem longPair_selectedFirst_fresh_available_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hCd : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ some d)
    (hSd : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) ≠ some d)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hretained : ∀ f : G.edgeSet, f ∈ Dset → v₂ ∉ (f : Sym2 V)) :
    ColorAvailableOn G Dset colour
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hQ' : colour Q = some i := by simpa [Q] using hQ
  have hT' : colour T = some j := by simpa [T] using hT
  have hCd' : colour C ≠ some d := by simpa [C] using hCd
  have hSd' : colour S ≠ some d := by simpa [S] using hSd
  have noAtU (f : G.edgeSet) (hfP : f ≠ P)
      (huf : u ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hf := f.2
      rw [hfa] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · exact hfP (Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa))
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hdEq : i = d := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ] using hcf))
      exact hdi hdEq.symm
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      have hdEq : j = d := Option.some.inj
        (hT'.symm.trans (by simpa [hfT] using hcf))
      exact hdj hdEq.symm
  have noAtV₁ (f : G.edgeSet) (hfD : f ∈ Dset) (hfP : f ≠ P)
      (hvf : v₁ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start f hvf with hfA | hfP'
    · have hfA' : f = A := Subtype.ext (by simpa [A] using hfA)
      exact hretained f hfD (by simpa [hfA', A])
    · exact hfP (Subtype.ext (by simpa [P] using hfP'))
  have noAtW₁ (f : G.edgeSet)
      (hwf : w₁ ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start f hwf with hfC | hfQ
    · exact hCd' (by
        have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
        simpa [hfC'] using hcf)
    · have hfQ' : f = Q := Subtype.ext (by simpa [Q] using hfQ)
      have hdEq : i = d := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ'] using hcf))
      exact hdi hdEq.symm
  have noAtX₁ (f : G.edgeSet)
      (hxf : x₁ ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT
    · exact hSd' (by
        have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
        simpa [hfS'] using hcf)
    · have hfT' : f = T := Subtype.ext (by simpa [T] using hfT)
      have hdEq : j = d := Option.some.inj
        (hT'.symm.trans (by simpa [hfT'] using hcf))
      exact hdj hdEq.symm
  apply (colorAvailableOn_some_iff G Dset colour P d).mpr
  intro f hfD hfP hcf
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = v₁ ∨ a = u := by simpa [P] using ha
  rcases hacase with hav | hau
  · constructor
    · intro hvb
      have hvb' : v₁ = b := hav.symm.trans hvb
      exact noAtV₁ f hfD hfP (by rw [hvb']; exact hbf)
    · intro hvb
      have hvb' : G.Adj v₁ b := by simpa [hav] using hvb
      have hbN : b ∈ G.neighborFinset v₁ :=
        (G.mem_neighborFinset v₁ b).mpr hvb'
      rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start] at hbN
      have hbcase : b = v₂ ∨ b = u := by simpa using hbN
      rcases hbcase with hbv₂ | hbu
      · exact hretained f hfD (by simpa [hbv₂] using hbf)
      · exact noAtU f hfP (by simpa [hbu] using hbf) hcf
  · constructor
    · intro hub
      have hub' : u = b := hau.symm.trans hub
      exact noAtU f hfP (by rw [hub']; exact hbf) hcf
    · intro hub
      have hub' : G.Adj u b := by simpa [hau] using hub
      rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
          g.first_adj r.first_adj hvw hvx hwx hub' with rfl | rfl | rfl
      · exact noAtV₁ f hfD hfP hbf
      · exact noAtW₁ f hbf hcf
      · exact noAtX₁ f hbf hcf

/-- After the selected edge receives an induced colour, the target
2-thread first edge may be made matching. -/
theorem longPair_twoThreadFirst_matching_available_after_selectedFresh_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (d i j : Fin 4)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G Dset
      (recolor G colour
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
      (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some d)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  have hPS : P ≠ S := by
    exact (longPair_twoTwoEdge_ne_edgeEndingAtThree G r.first_two r.second_two
      h.start_three r.middle_adj h.first_adj.symm).symm
  have hafterP : afterP P = some d := by simp [afterP]
  have hafterQ : afterP Q = some i := by
    rw [show afterP Q = colour Q by
      exact recolor_ne G colour (some d) hPQ.symm]
    simpa [Q] using hQ
  have hafterS : afterP S ≠ none := by
    rw [show afterP S = colour S by
      exact recolor_ne G colour (some d) hPS.symm]
    simpa [S] using hS
  have noAtU (f : G.edgeSet) (hfT : f ≠ T)
      (huf : u ∈ (f : Sym2 V)) (hcf : afterP f = none) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hf := f.2
      rw [hfa] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      have hfalse : some d = none :=
        hafterP.symm.trans (by simpa [hfP] using hcf)
      simp at hfalse
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hfalse : some i = none :=
        hafterQ.symm.trans (by simpa [hfQ] using hcf)
      simp at hfalse
    · exact hfT (Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa))
  have noAtX₁ (f : G.edgeSet) (hfT : f ≠ T)
      (hxf : x₁ ∈ (f : Sym2 V)) (hcf : afterP f = none) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT'
    · have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
      exact hafterS (by simpa [hfS'] using hcf)
    · exact hfT (Subtype.ext (by simpa [T] using hfT'))
  apply (colorAvailableOn_none_iff G Dset afterP T).mpr
  intro f _hfD hfT hcf a ha haf
  have hacase : a = x₁ ∨ a = u := by simpa [T] using ha
  exact hacase.elim
    (fun hax ↦ noAtX₁ f hfT (by simpa [hax] using haf) hcf)
    (fun hau ↦ noAtU f hfT (by simpa [hau] using haf) hcf)

/-- Condition 2 for the alternate selected-outer/2-thread-first swap.  On
the untouched 2-thread, either its middle edge itself is matching or its
last edge is matching; together with the newly matching first edge of the
target arm this supplies the two matching guards needed at the only new
centre-side obstruction. -/
theorem longPair_conditionTwo_selectedFresh_twoThreadFirstMatching_twoTwo
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (hsat : OneSaturated G colour)
    (d j : Fin 4)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hguard : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none ∨
      colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = none)
    (hUP : (⟨s(x₂, y), r.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDP : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDT : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet)) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  let U : G.edgeSet := ⟨s(x₂, y), r.last_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) T none
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  have hUT : U ≠ T := by
    simpa [U, T] using (twoThreadCore_firstEdge_ne_lastEdge G r).symm
  have hUP' : U ≠ P := by simpa [U, P] using hUP
  have hDP' : D ≠ P := by simpa [D, P] using hDP
  have hDT' : D ≠ T := by simpa [D, T] using hDT
  have hAP : A ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      h.start_three h.left_adj h.first_adj.symm
  have hAT : A ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      h.start_three h.left_adj r.first_adj.symm
  have hBP : B ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      h.start_three h.right_adj.symm h.first_adj.symm
  have hBT : B ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      h.start_three h.right_adj.symm r.first_adj.symm
  have hCP : C ≠ P := by
    intro heq
    apply longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj h.first_adj.symm
    apply Subtype.ext
    have hval := congrArg Subtype.val heq
    simpa [C, P, threadFirstEdge, Sym2.eq_swap] using hval
  have hCT : C ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj r.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hTne : colour T ≠ none := by simpa [T, hT]
  have hU : colour U = none := by
    exact longPair_twoThread_last_matching_of_first_two_induced G r colour hsat
      hTne (by simpa [S] using hS)
  have hnewT : new T = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBT, B, hB]
  have hnewU : new U = none := by simp [new, hUP', hUT, U, hU]
  have hnewC_of (hC : colour C = none) : new C = none := by
    simp [new, hCP, hCT, hC]
  have hnewD_of (hD : colour D = none) : new D = none := by
    simp [new, hDP', hDT', hD]
  have hagree : ColoringsAgreeOff G ({P, T} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ T := by simpa using he
    simp [new, hne.1, hne.2]
  have hNu : G.neighborFinset u = {v₁, w₁, x₁} :=
    neighborFinset_eq_triple_of_isThreeVertex G h.start_three
      h.first_adj g.first_adj r.first_adj hvw hvx hwx
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases longPair_twoVertex_paletteAffectedBy_twoThreadFirst_swap_cases
      G h r hq (by simpa [P, T] using haffect) with hqv₂ | hqx₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub r.second_two
      r.middle_adj.symm r.first_two T U hUT.symm hnewT hnewU
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [T]) (Or.inr r.middle_adj.symm)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [U]) (Or.inl rfl)
    · exact hall
  · have hqmem : q ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u q).mpr hqu.symm
    rw [hNu] at hqmem
    have hqcases : q = v₁ ∨ q = w₁ ∨ q = x₁ := by simpa using hqmem
    rcases hqcases with hqv₁ | hqw₁ | hqx₁
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub h.first_two
        h.left_adj h.middle_two A B hAB hnewA hnewB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [B]) (Or.inr h.left_adj)
      · exact hall

    · subst q
      rcases hguard with hC | hD
      · apply longPair_paletteCondition_at_two_visible_matching G hsub
          g.first_two g.middle_adj g.second_two C T hCT
            (hnewC_of (by simpa [C] using hC)) hnewT
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
            (by simp [C]) (Or.inl rfl)
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
            (by simp [T]) (Or.inr g.first_adj.symm)
        · exact hall
      · apply longPair_paletteCondition_at_two_visible_matching G hsub
          g.first_two g.middle_adj g.second_two D T hDT'
            (hnewD_of (by simpa [D] using hD)) hnewT
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
            (by simp [D]) (Or.inr g.middle_adj)
        · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
            (by simp [T]) (Or.inr g.first_adj.symm)
        · exact hall
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub r.first_two
        r.middle_adj r.second_two T U hUT.symm hnewT hnewU
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [T]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [U]) (Or.inr r.middle_adj)
      · exact hall

/-- The critical swap with the old target-arm colour fixes the far palette.
Changing the selected outer edge instead to a colour outside the two centre
colours therefore repairs the unique Condition-3 obligation. -/
theorem longPair_conditionThreeAtTwoThread_alt_of_critical_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (base : G.edgeSet → OneTwoColor 4) (i j d : Fin 4)
    (hP : base (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : base (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : base (threadFirstEdge G q hq) = some j)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G base P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let T : G.edgeSet := threadFirstEdge G q hq
    let alt := recolor G (recolor G base P (some d)) T none
    ConditionThreeAtTwoThread G q hq alt := by
  dsimp only
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let U : G.edgeSet := threadLastEdge G q hq
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G base P (some j)) T none
  let alt : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G base P (some d)) T none
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne
      G h.first_adj g.first_adj hvw
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G g.first_adj
        hq.first_step_adj hwq
  have hcriticalP : critical P = some j := by simp [critical, hPT]
  have hcriticalQ : critical Q = some i := by
    simp [critical, hPQ.symm, hQT, Q, hQ]
  have hcriticalT : critical T = none := by simp [critical]
  have haltP : alt P = some d := by simp [alt, hPT]
  have haltQ : alt Q = some i := by simp [alt, hPQ.symm, hQT, Q, hQ]
  have haltT : alt T = none := by simp [alt]
  have hcriticalStart := longPair_twoThreadFirst_external_data_twoTwo
    G h g q hq hvw hvq hwq critical j i hcriticalT hcriticalP hcriticalQ
  have haltStart := longPair_twoThreadFirst_external_data_twoTwo
    G h g q hq hvw hvq hwq alt d i haltT haltP haltQ
  have htP : t ∉ (P : Sym2 V) := by
    intro hmem
    have hcase : t = v₁ ∨ t = u := by simpa [P] using hmem
    rcases hcase with htv₁ | htu
    · exact (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two) htv₁
    · exact (IsKThread.endpoints_ne G hq) htu.symm
  have hagree : ColoringsAgreeOff G ({P} : Set G.edgeSet) critical alt := by
    intro e he
    have heP : e ≠ P := by simpa using he
    by_cases heT : e = T
    · subst e
      simp [critical, alt]
    · simp [critical, alt, heP, heT]
  have hmiss : ∀ e, IsExternalAt G t U e → e ∉ ({P} : Set G.edgeSet) := by
    intro e hext heS
    have heq : e = P := by simpa using heS
    subst e
    exact htP hext.1
  have hfarEq : ExternalInducedColors G critical t U =
      ExternalInducedColors G alt t U :=
    externalInducedColors_eq_of_agreeOff G hagree hmiss
  have hfarAlt : ExternalInducedColors G alt t U = {j, i} := by
    rw [← hfarEq, ← hcritical.2.2]
    exact hcriticalStart.2
  change ConditionThreeAtTwoThread G q hq alt
  intro _hleft _hright
  rw [haltStart.2, hfarAlt]
  intro heq
  have hdmem : d ∈ ({j, i} : Set (Fin 4)) := by
    rw [← heq]
    simp
  simpa [hdj, hdi] using hdmem

/-- The complete prepared-gap package for the alternate swap in a
`(3,2,2)` fork. -/
theorem longPair_prepared_selectedFresh_twoThreadFirstMatching_twoTwo
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hCd : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ some d)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ none)
    (hSd : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ some d)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hguard : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none ∨
      colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDP : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDT : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
    let T : G.edgeSet := threadFirstEdge G q hq
    PreparedThreeThreadGap G h
      (recolor G (recolor G colour P (some d)) T none) := by
  dsimp only
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some d)
  let alt : G.edgeSet → OneTwoColor 4 := recolor G afterP T none
  let r := hq.twoThreadCoreData G
  let r₂ := hq.twoStepArmCore G
  have hPD' : P ∈ Dset := by simpa [P, Dset] using hPD
  have hTD' : T ∈ Dset := by simpa [T, Dset] using hTD
  have havailP : ColorAvailableOn G Dset colour P (some d) := by
    exact longPair_selectedFirst_fresh_available_twoTwo G h g r
      hvw hvq hwq colour Dset d i j hP hQ
      (by simpa [r, T, threadFirstEdge, Sym2.eq_swap] using hT)
      hCd (by simpa [r] using hSd) hdi hdj
      (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalidAfterP : IsOneTwoColoringOn G Dset afterP := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := P) (a := some d) hPD').mpr
    refine ⟨?_, havailP⟩
    exact IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.diff_subset
  have havailT : ColorAvailableOn G Dset afterP T none := by
    simpa [afterP, P, Q, T, r, threadFirstEdge, Sym2.eq_swap] using
      longPair_twoThreadFirst_matching_available_after_selectedFresh_twoTwo
        G h g r hvw hvq hwq colour Dset d i j hQ
        (by simpa [r, threadFirstEdge, Sym2.eq_swap] using hT)
        (by simpa [r] using hS)
  have hvalidAlt : IsOneTwoColoringOn G Dset alt := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := afterP) (e := T) (a := none) hTD').mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G) hvalidAfterP Set.diff_subset,
      havailT⟩
  have hsatAlt : OneSaturated G alt := by
    simpa [alt, afterP, P, T, r₂, threadFirstEdge, Sym2.eq_swap] using
      longPair_oneSaturated_selectedFresh_twoStepFirstMatching
        G h r₂ hvq colour hprepared.2.1 d j
        (by simpa [r₂, threadFirstEdge, Sym2.eq_swap] using hT) hA
  have htwoAlt : ConditionTwo G alt := by
    simpa [alt, afterP, P, T, r, threadFirstEdge, Sym2.eq_swap] using
      longPair_conditionTwo_selectedFresh_twoThreadFirstMatching_twoTwo
        G hsub h g r hvw hvq hwq colour hprepared.2.2.1 hprepared.2.1 d j
        (by simpa [r, threadFirstEdge, Sym2.eq_swap] using hT)
        (by simpa [r] using hS) hA hB hguard
        (by simpa [r, threadLastEdge, Sym2.eq_swap] using hUP)
        hDP (by simpa [r, threadFirstEdge, Sym2.eq_swap] using hDT)
  have hcriticalAlt : ConditionThreeAtTwoThread G q hq alt := by
    exact longPair_conditionThreeAtTwoThread_alt_of_critical_twoTwo
      G h g q hq hvw hvq hwq colour i j d hP hQ hT hdi hdj
        (by simpa [P, T, alt, afterP] using hcritical)
  have hthreeAlt : ConditionThree G alt := by
    exact (longPair_conditionThree_swap_selectedOuter_twoThreadFirst_iff
      G h q hq colour hprepared.2.2.2 d).2
        (by simpa [P, T, alt, afterP] using hcriticalAlt)
  exact ⟨by simpa [Dset, alt, afterP] using hvalidAlt,
    by simpa [alt, afterP] using hsatAlt,
    by simpa [alt, afterP] using htwoAlt,
    by simpa [alt, afterP] using hthreeAlt⟩

/-- Once the alternate swap is prepared, its newly matching target first
edge guards the left end while the generic prepared-gap theorem restores
the two deleted edges. -/
theorem longPair_hasGoodFour_of_twoThread_middle_induced_alt_twoTwo
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hCd : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ≠ some d)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ none)
    (hSd : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ≠ some d)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hguard : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none ∨
      colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDP : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDT : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRT : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    HasGoodFour G := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let alt : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some d)) T none
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hpreparedAlt : PreparedThreeThreadGap G h alt := by
    exact longPair_prepared_selectedFresh_twoThreadFirstMatching_twoTwo
      G hsub h g q hq hvw hvq hwq colour hprepared d i j hP hQ hT
        hCd hS hSd hA hB hguard hPD hTD hUP hDP hDT hdi hdj
        (by simpa [P, T] using hcritical)
  have hAltP : alt P ≠ none := by simp [alt, hPT]
  have hAltR : alt R = none := by
    simp [alt, R, P, T, hRP, hRT, hR]
  have hAD : A ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ RetainedEdges (G.deleteIncidenceSet v₂) G := by
    simpa [B] using right_chain_edge_not_retained G h.right_adj
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD)
  have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ hTD)
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD)
  have hAltA : alt A = none := by simp [alt, A, hAP, hAT, hA]
  have hAltB : alt B = none := by simp [alt, B, hBP, hBT, hB]
  have hAltT : alt T = none := by simp [alt]
  apply longPair_hasGoodFour_of_prepared_left_outer_induced
    G hsub h alt hpreparedAlt
      (by simpa [P] using hAltP) (by simpa [R] using hAltR)
      (by simpa [A] using hAltA) (by simpa [B] using hAltB)
      T hAltT
  · simp [T, threadFirstEdge]
  · exact hAT.symm
  · exact hBT.symm

/-- If the target 2-thread middle edge is induced while the other middle
edge is matching or carries the same induced colour, a fourth colour gives
the alternate swap immediately. -/
theorem longPair_hasGoodFour_of_twoThread_middle_induced_same_or_matching
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j c : Fin 4) (hij : i ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) = some c)
    (hCcase : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none ∨
      colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDP : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDT : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRT : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    HasGoodFour G := by
  classical
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let S : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2),
      q.adj_getVert_succ (i := 1) (by
        have hlen : q.length = 3 := by simpa using hq.length
        omega)⟩
  have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by simp [hij]
  obtain ⟨d, hdPair, hcd⟩ :=
    longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
      hpairCard (some c)
  have hdData : d ≠ i ∧ d ≠ j := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hdPair
  have hSnon : colour S ≠ none := by simp [S, hS]
  have hSd : colour S ≠ some d := by simpa [S, hS] using hcd
  have hCd : colour C ≠ some d := by
    rcases hCcase with hC | hC
    · simp [C, hC]
    · simpa [C, hC] using hcd
  have hguard : colour C = none ∨ colour D = none := by
    rcases hCcase with hC | hC
    · exact Or.inl (by simpa [C] using hC)
    · right
      exact longPair_twoThread_last_matching_of_first_two_induced G g colour
        hprepared.2.1 (by simpa [hQ])
          (by simpa [C, hC])
  exact longPair_hasGoodFour_of_twoThread_middle_induced_alt_twoTwo
    G hsub h g q hq hvw hvq hwq colour hprepared d i j hP hR hQ hT
      (by simpa [C] using hCd) (by simpa [S] using hSnon)
      (by simpa [S] using hSd) hA hB
      (by simpa [C, D] using hguard) hPD hTD hUP hDP hDT hRP hRT
      hdData.1 hdData.2 hcritical

/-! ## The distinct-middle-colour preliminary recolouring -/

/-- Changing an induced edge to another induced colour preserves matching
saturation: no old matching witness can be the changed edge. -/
theorem oneSaturated_recolor_induced_to_induced
    {colour : G.edgeSet → OneTwoColor 4} (hold : OneSaturated G colour)
    (S : G.edgeSet) (c e : Fin 4) (hS : colour S = some c) :
    OneSaturated G (recolor G colour S (some e)) := by
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour S (some e)
  intro f hf
  have hfOld : colour f ≠ none := by
    by_cases hfS : f = S
    · subst f
      simp [hS]
    · intro hfNone
      apply hf
      simpa [new, hfS, hfNone]
  obtain ⟨m, hm, x, hxf, hxm⟩ := hold f hfOld
  have hmS : m ≠ S := by
    intro hEq
    subst m
    have hfalse : some c = none := hS.symm.trans hm
    simp at hfalse
  exact ⟨m, by simpa [new, hmS] using hm, x, hxf, hxm⟩

/-- An edge with two degree-two endpoints is never external at an endpoint
of a certified 2-thread, whose endpoints have degree three.  Recolouring
such an internal edge therefore leaves Condition 3 unchanged. -/
theorem conditionThree_recolor_edge_between_two_vertices
    {x₁ x₂ : V} (hx₁ : IsTwoVertex G x₁) (hx₂ : IsTwoVertex G x₂)
    (hxx : G.Adj x₁ x₂) (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (e : Fin 4) :
    ConditionThree G
      (recolor G colour (⟨s(x₁, x₂), hxx⟩ : G.edgeSet) (some e)) := by
  let S : G.edgeSet := ⟨s(x₁, x₂), hxx⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour S (some e)
  have hagree : ColoringsAgreeOff G ({S} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour S (some e)
  change ConditionThree G new
  apply hold.of_agreeOff G hagree
  intro a b p hp haffect _hleft _hright
  rcases haffect with ⟨f, hfS, hext⟩ | ⟨f, hfS, hext⟩
  · have hf : f = S := by simpa using hfS
    subst f
    have hacase : a = x₁ ∨ a = x₂ := by simpa [S] using hext.1
    rcases hacase with hax₁ | hax₂
    · exact False.elim
        ((isThreeVertex_ne_isTwoVertex G hp.start_three hx₁) hax₁)
    · exact False.elim
        ((isThreeVertex_ne_isTwoVertex G hp.start_three hx₂) hax₂)
  · have hf : f = S := by simpa using hfS
    subst f
    have hbcase : b = x₁ ∨ b = x₂ := by simpa [S] using hext.1
    rcases hbcase with hbx₁ | hbx₂
    · exact False.elim
        ((isThreeVertex_ne_isTwoVertex G hp.end_three hx₁) hbx₁)
    · exact False.elim
        ((isThreeVertex_ne_isTwoVertex G hp.end_three hx₂) hbx₂)

/-- In the distinct-complement case, the colour on the other 2-thread
middle edge is available on the target middle edge.  The critical normal
form supplies the far external palette `{i,j}`. -/
theorem longPair_twoThreadMiddle_otherColour_available
    {u v₁ v₂ v₃ z w₁ w₂ s x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (i j c e : Fin 4) (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) = some c)
    (hU : colour (⟨s(x₂, y), r.last_adj⟩ : G.edgeSet) = none)
    (hfar : ExternalInducedColors G colour y
      (⟨s(x₂, y), r.last_adj⟩ : G.edgeSet) = {i, j}) :
    ColorAvailableOn G Dset colour
      (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) (some e) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  let U : G.edgeSet := ⟨s(x₂, y), r.last_adj⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hQ' : colour Q = some i := by simpa [Q] using hQ
  have hT' : colour T = some j := by simpa [T] using hT
  have hS' : colour S = some c := by simpa [S] using hS
  have hU' : colour U = none := by simpa [U] using hU
  have noAtU (f : G.edgeSet) (huf : u ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hf := f.2
      rw [hfa] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      have hfalse : none = some e := hP'.symm.trans (by simpa [hfP] using hcf)
      simp at hfalse
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hie : i = e := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ] using hcf))
      exact hei hie.symm
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      have hje : j = e := Option.some.inj
        (hT'.symm.trans (by simpa [hfT] using hcf))
      exact hej hje.symm
  have noAtX₁ (f : G.edgeSet) (hxf : x₁ ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT
    · have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
      have hce : c = e := Option.some.inj
        (hS'.symm.trans (by simpa [hfS'] using hcf))
      exact hec hce.symm
    · have hfT' : f = T := Subtype.ext (by simpa [T] using hfT)
      have hje : j = e := Option.some.inj
        (hT'.symm.trans (by simpa [hfT'] using hcf))
      exact hej hje.symm
  have noAtX₂ (f : G.edgeSet) (hxf : x₂ ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.second_two
        r.middle_adj.symm r.last_adj r.first_ne_end f hxf with hfS | hfU
    · have hfS' : f = S :=
        Subtype.ext (by simpa [S, Sym2.eq_swap] using hfS)
      have hce : c = e := Option.some.inj
        (hS'.symm.trans (by simpa [hfS'] using hcf))
      exact hec hce.symm
    · have hfU' : f = U := Subtype.ext (by simpa [U] using hfU)
      have hfalse : none = some e := hU'.symm.trans (by simpa [hfU'] using hcf)
      simp at hfalse
  have noAtY (f : G.edgeSet) (hyf : y ∈ (f : Sym2 V))
      (hcf : colour f = some e) : False := by
    by_cases hfU : f = U
    · subst f
      have hfalse : none = some e := hU'.symm.trans hcf
      simp at hfalse
    · have hemem : e ∈ ExternalInducedColors G colour y U :=
        ⟨f, ⟨hyf, hfU⟩, hcf⟩
      rw [hfar] at hemem
      simpa [hei, hej] using hemem
  apply (colorAvailableOn_some_iff G Dset colour S e).mpr
  intro f _hfD hfS hcf
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = x₁ ∨ a = x₂ := by simpa [S] using ha
  rcases hacase with hax₁ | hax₂
  · constructor
    · intro hab
      have hxb : x₁ = b := hax₁.symm.trans hab
      exact noAtX₁ f (by rw [hxb]; exact hbf) hcf
    · intro hab
      have hxb : G.Adj x₁ b := by simpa [hax₁] using hab
      have hbN : b ∈ G.neighborFinset x₁ :=
        (G.mem_neighborFinset x₁ b).mpr hxb
      rw [neighborFinset_eq_pair_of_isTwoVertex G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start] at hbN
      have hbcase : b = x₂ ∨ b = u := by simpa using hbN
      exact hbcase.elim
        (fun hbx ↦ noAtX₂ f (by simpa [hbx] using hbf) hcf)
        (fun hbu ↦ noAtU f (by simpa [hbu] using hbf) hcf)
  · constructor
    · intro hab
      have hxb : x₂ = b := hax₂.symm.trans hab
      exact noAtX₂ f (by rw [hxb]; exact hbf) hcf
    · intro hab
      have hxb : G.Adj x₂ b := by simpa [hax₂] using hab
      have hbN : b ∈ G.neighborFinset x₂ :=
        (G.mem_neighborFinset x₂ b).mpr hxb
      rw [neighborFinset_eq_pair_of_isTwoVertex G r.second_two
        r.middle_adj.symm r.last_adj r.first_ne_end] at hbN
      have hbcase : b = x₁ ∨ b = y := by simpa using hbN
      exact hbcase.elim
        (fun hbx ↦ noAtX₁ f (by simpa [hbx] using hbf) hcf)
        (fun hby ↦ noAtY f (by simpa [hby] using hbf) hcf)

/-- After recolouring the middle edge of a 2-thread, its old induced colour
disappears from the second internal vertex. -/
theorem not_vertexSeesInduced_oldMiddleColor_after_middle_recolor
    {u v₁ v₂ v₃ z x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (c e : Fin 4) (hec : e ≠ c)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hSD : (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    ¬ VertexSeesInduced G
      (recolor G colour
        (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) (some e))
      x₂ c := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour S (some e)
  have hSD' : S ∈ Dset := by simpa [S, Dset] using hSD
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAS : A ≠ S := fun heq ↦ hAD (heq ▸ hSD')
  have hBS : B ≠ S := fun heq ↦ hBD (heq ▸ hSD')
  have hnewS : new S = some e := by simp [new]
  have hnewA : new A = none := by simp [new, hAS, A, hA]
  have hnewB : new B = none := by simp [new, hBS, B, hB]
  intro hsee
  obtain ⟨f, hf, a, haf, hclose⟩ :=
    (vertexSeesInduced_iff G new x₂ c).mp hsee
  have hfS : f ≠ S := by
    intro heq
    subst f
    have heq' : some e = some c := hnewS.symm.trans hf
    exact hec (Option.some.inj heq')
  have hfA : f ≠ A := by
    intro heq
    subst f
    have hfalse : none = some c := hnewA.symm.trans hf
    simp at hfalse
  have hfB : f ≠ B := by
    intro heq
    subst f
    have hfalse : none = some c := hnewB.symm.trans hf
    simp at hfalse
  have hfOld : colour f = some c := by simpa [new, hfS] using hf
  have hcover : insert B (insert A Dset) = Set.univ := by
    simpa [Dset, A, B] using insert_threeThread_gap_retained_eq_univ G h
  have hfD : f ∈ Dset := by
    have hfCover : f ∈ insert B (insert A Dset) := by rw [hcover]; simp
    simpa [hfA, hfB] using hfCover
  have hcompat := hvalid S hSD' f hfD hfS.symm
  have hsep : InducedSeparated G S f := by
    simpa [S, hS, hfOld] using hcompat
  rw [inducedSeparated_iff_forall_endpoints] at hsep
  have hlocal := hsep x₂ (by simp [S]) a haf
  exact hclose.elim hlocal.1 hlocal.2

theorem twoVertex_paletteAffectedBy_twoThreadMiddle_cases
    {u x₁ x₂ y q : V} (r : TwoThreadCoreData G u x₁ x₂ y)
    (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = x₁ ∨ q = x₂ := by
  rw [paletteAffectedBy_iff_inducedAffectedBy,
    inducedAffectedBy_singleton] at haffect
  obtain ⟨a, ha, hqa⟩ := haffect
  have hacase : a = x₁ ∨ a = x₂ := by simpa using ha
  rcases hacase with hax₁ | hax₂
  · subst a
    rcases hqa with hqx₁ | hqx₁
    · exact Or.inl hqx₁
    · have hqN : q ∈ G.neighborFinset x₁ :=
        (G.mem_neighborFinset x₁ q).mpr hqx₁.symm
      rw [neighborFinset_eq_pair_of_isTwoVertex G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start] at hqN
      have hqcase : q = x₂ ∨ q = u := by simpa using hqN
      rcases hqcase with hqx₂ | hqu
      · exact Or.inr hqx₂
      · exact False.elim
          ((isThreeVertex_ne_isTwoVertex G r.start_three hq) hqu.symm)
  · subst a
    rcases hqa with hqx₂ | hqx₂
    · exact Or.inr hqx₂
    · have hqN : q ∈ G.neighborFinset x₂ :=
        (G.mem_neighborFinset x₂ q).mpr hqx₂.symm
      rw [neighborFinset_eq_pair_of_isTwoVertex G r.second_two
        r.middle_adj.symm r.last_adj r.first_ne_end] at hqN
      have hqcase : q = x₁ ∨ q = y := by simpa using hqN
      rcases hqcase with hqx₁ | hqy
      · exact Or.inl hqx₁
      · exact False.elim
          ((isThreeVertex_ne_isTwoVertex G r.end_three hq) hqy.symm)

theorem conditionTwo_recolor_twoThreadMiddle_to_induced
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z x₁ x₂ y : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : TwoThreadCoreData G u x₁ x₂ y)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (c e : Fin 4) (hec : e ≠ c)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) = some c)
    (hU : colour (⟨s(x₂, y), r.last_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hSD : (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : (⟨s(x₂, y), r.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    ConditionTwo G
      (recolor G colour
        (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) (some e)) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  let U : G.edgeSet := ⟨s(x₂, y), r.last_adj⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour S (some e)
  have hPS : P ≠ S := by
    intro hEq
    have hc : none = some c := hP.symm.trans (by simpa [P, S, hEq] using hS)
    simp at hc
  have hUS : U ≠ S := by
    intro hEq
    have hc : none = some c := hU.symm.trans (by simpa [U, S, hEq] using hS)
    simp at hc
  have hPU : P ≠ U := by simpa [P, U] using hUP.symm
  have hnewP : new P = none := by simp [new, hPS, P, hP]
  have hnewU : new U = none := by simp [new, hUS, U, hU]
  have hagree : ColoringsAgreeOff G ({S} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour S (some e)
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases twoVertex_paletteAffectedBy_twoThreadMiddle_cases G r hq
      (by simpa [S] using haffect) with hqx₁ | hqx₂
  · subst q
    apply longPair_paletteCondition_at_two_visible_matching G hsub r.first_two
      r.middle_adj r.second_two P U hPU hnewP hnewU
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [P]) (Or.inr r.first_adj.symm)
    · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
        (by simp [U]) (Or.inr r.middle_adj)
    · exact hall
  · subst q
    exact (not_vertexSeesInduced_oldMiddleColor_after_middle_recolor
      G h r colour hvalid c e hec hS hA hB hSD) (hall c)

/-- Prepared-gap preservation for the preliminary middle-edge recolouring
in the distinct-complement case. -/
theorem longPair_prepared_recolor_twoThreadMiddle_to_otherColour
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j c e : Fin 4) (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hSD : (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    let S : G.edgeSet :=
      ⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩
    PreparedThreeThreadGap G h (recolor G colour S (some e)) := by
  dsimp only
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let S : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2),
      q.adj_getVert_succ (i := 1) (by
        have hlen : q.length = 3 := by simpa using hq.length
        omega)⟩
  let U : G.edgeSet := threadLastEdge G q hq
  let r := hq.twoThreadCoreData G
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some j)) T none
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour S (some e)
  have hSD' : S ∈ Dset := by simpa [S, Dset] using hSD
  have hTcore : colour (⟨s(q.getVert 1, u), r.first_adj.symm⟩ : G.edgeSet) =
      some j := by simpa [r, T, threadFirstEdge, Sym2.eq_swap] using hT
  have hScore : colour (⟨s(q.getVert 1, q.getVert 2), r.middle_adj⟩ :
      G.edgeSet) = some c := by simpa [r, S] using hS
  have hU : colour U = none := by
    exact longPair_twoThread_last_matching_of_first_two_induced G r colour
      hprepared.2.1
        (by
          have : colour T ≠ none := by rw [hT]; simp
          simpa [T, r, threadFirstEdge, Sym2.eq_swap] using this)
        (by
          have : colour S ≠ none := by rw [hS]; simp
          simpa [S, r] using this)
  have hcriticalP : critical P = some j := by
    have hPT : P ≠ T := by
      simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
        longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
          hq.first_step_adj hvq
    simp [critical, hPT]
  have hcriticalQ : critical Q = some i := by
    have hPQ : P ≠ Q := by
      simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne
        G h.first_adj g.first_adj hvw
    have hQT : Q ≠ T := by
      simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
        longPair_firstEdges_ne_of_firstVertices_ne G g.first_adj
          hq.first_step_adj hwq
    simp [critical, hPQ.symm, hQT, Q, hQ]
  have hcriticalT : critical T = none := by simp [critical]
  have hcriticalStart := longPair_twoThreadFirst_external_data_twoTwo
    G h g q hq hvw hvq hwq critical j i hcriticalT hcriticalP hcriticalQ
  have htP : t ∉ (P : Sym2 V) := by
    intro hmem
    have hcase : t = v₁ ∨ t = u := by simpa [P] using hmem
    rcases hcase with htv₁ | htu
    · exact (isThreeVertex_ne_isTwoVertex G hq.end_three h.first_two) htv₁
    · exact (IsKThread.endpoints_ne G hq) htu.symm
  have htT : t ∉ (T : Sym2 V) := by
    intro hmem
    have hcase : t = u ∨ t = q.getVert 1 := by
      simpa [T, threadFirstEdge] using hmem
    rcases hcase with htu | htx₁
    · exact (IsKThread.endpoints_ne G hq) htu.symm
    · have hx₁two : IsTwoVertex G (q.getVert 1) :=
        IsKThread.internal_two G hq (by omega) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)
      exact (isThreeVertex_ne_isTwoVertex G hq.end_three hx₁two) htx₁
  have hagreeCritical : ColoringsAgreeOff G ({P, T} : Set G.edgeSet)
      colour critical := by
    intro f hf
    have hne : f ≠ P ∧ f ≠ T := by simpa using hf
    simp [critical, hne.1, hne.2]
  have hmissFar : ∀ f, IsExternalAt G t U f →
      f ∉ ({P, T} : Set G.edgeSet) := by
    intro f hfext hfset
    have hfcase : f = P ∨ f = T := by simpa using hfset
    exact hfcase.elim
      (fun hf ↦ htP (by simpa [hf] using hfext.1))
      (fun hf ↦ htT (by simpa [hf] using hfext.1))
  have hfarEq : ExternalInducedColors G colour t U =
      ExternalInducedColors G critical t U :=
    externalInducedColors_eq_of_agreeOff G hagreeCritical hmissFar
  have hfar : ExternalInducedColors G colour t U = {i, j} := by
    rw [hfarEq, ← hcritical.2.2]
    simpa [Set.pair_comm] using hcriticalStart.2
  have havail : ColorAvailableOn G Dset colour S (some e) := by
    simpa [S, U, r, threadFirstEdge, threadLastEdge, Sym2.eq_swap] using
      longPair_twoThreadMiddle_otherColour_available G h g r hvw hvq hwq
        colour Dset i j c e hei hej hec hP hQ hTcore hScore
          (by simpa [U, r, threadLastEdge, Sym2.eq_swap] using hU)
          (by simpa [U, r, threadLastEdge, Sym2.eq_swap] using hfar)
  have hvalid : IsOneTwoColoringOn G Dset new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := S) (a := some e) hSD').mpr
    refine ⟨?_, havail⟩
    exact IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.diff_subset
  have hsat : OneSaturated G new := by
    simpa [new] using oneSaturated_recolor_induced_to_induced
      G hprepared.2.1 S c e (by simpa [S] using hS)
  have htwo : ConditionTwo G new := by
    simpa [new, S, U, r, threadFirstEdge, threadLastEdge, Sym2.eq_swap] using
      conditionTwo_recolor_twoThreadMiddle_to_induced G hsub h r colour
        hprepared.2.2.1 (by simpa [Dset] using hprepared.1) c e hec hP
        hScore (by simpa [U, r, threadLastEdge, Sym2.eq_swap] using hU)
        hA hB (by simpa [S, Dset, r] using hSD')
        (by simpa [P, U, r, threadLastEdge, Sym2.eq_swap] using hUP)
  have hthree : ConditionThree G new := by
    simpa [new, S, r] using
      conditionThree_recolor_edge_between_two_vertices G r.first_two
        r.second_two r.middle_adj colour hprepared.2.2.2 e
  exact ⟨by simpa [Dset, new] using hvalid,
    by simpa [new] using hsat, by simpa [new] using htwo,
    by simpa [new] using hthree⟩

/-- The remaining Claim-1 subcase: the two middle edges carry the two
different colours outside the centre pair.  First move the target middle
edge to the other middle colour, then use its old colour on the selected
outer edge. -/
theorem longPair_hasGoodFour_of_twoThread_middle_induced_distinct
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (hvw : v₁ ≠ w₁) (hvq : v₁ ≠ q.getVert 1)
    (hwq : w₁ ≠ q.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j c e : Fin 4)
    (hei : e ≠ i) (hej : e ≠ j) (hec : e ≠ c)
    (hci : c ≠ i) (hcj : c ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (threadFirstEdge G q hq) = some j)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = some e)
    (hS : colour
      (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) = some c)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hSD : (⟨s(q.getVert 1, q.getVert 2),
        q.adj_getVert_succ (i := 1) (by
          have hlen : q.length = 3 := by simpa using hq.length
          omega)⟩ : G.edgeSet) ∈ RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDP : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDT : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRT : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hcritical :
      let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
      let T : G.edgeSet := threadFirstEdge G q hq
      let critical := recolor G (recolor G colour P (some j)) T none
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t (threadLastEdge G q hq) ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t (threadLastEdge G q hq)) :
    HasGoodFour G := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let T : G.edgeSet := threadFirstEdge G q hq
  let S : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2),
      q.adj_getVert_succ (i := 1) (by
        have hlen : q.length = 3 := by simpa using hq.length
        omega)⟩
  let U : G.edgeSet := threadLastEdge G q hq
  let changed : G.edgeSet → OneTwoColor 4 := recolor G colour S (some e)
  let critical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some j)) T none
  let changedCritical : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G changed P (some j)) T none
  let r := hq.twoThreadCoreData G
  have hcriticalBase :
      ExternalEdgesInduced G critical u T ∧
        ExternalEdgesInduced G critical t U ∧
        ExternalInducedColors G critical u T =
          ExternalInducedColors G critical t U := by
    simpa [critical, P, T, U] using hcritical
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hvq
  have hPS : P ≠ S := by
    intro hEq
    have hf : none = some c := hP.symm.trans (by simpa [P, S, hEq] using hS)
    simp at hf
  have hRS : R ≠ S := by
    intro hEq
    have hf : none = some c := hR.symm.trans (by simpa [R, S, hEq] using hS)
    simp at hf
  have hQS : Q ≠ S := by
    intro hEq
    have hf : some i = some c := hQ.symm.trans (by simpa [Q, S, hEq] using hS)
    exact hci (Option.some.inj hf).symm
  have hTS : T ≠ S := by
    intro hEq
    have hf : some j = some c := hT.symm.trans (by simpa [T, S, hEq] using hS)
    exact hcj (Option.some.inj hf).symm
  have hCS : C ≠ S := by
    intro hEq
    have hf : some e = some c := hC.symm.trans (by simpa [C, S, hEq] using hS)
    exact hec (Option.some.inj hf)
  have hD : colour D = none := by
    exact longPair_twoThread_last_matching_of_first_two_induced G g colour
      hprepared.2.1 (by rw [hQ]; simp) (by rw [hC]; simp)
  have hDS : D ≠ S := by
    intro hEq
    have hf : none = some c := hD.symm.trans (by simpa [D, S, hEq] using hS)
    simp at hf
  have hpreparedChanged : PreparedThreeThreadGap G h changed := by
    exact longPair_prepared_recolor_twoThreadMiddle_to_otherColour
      G hsub h g q hq hvw hvq hwq colour hprepared i j c e hei hej hec
        hP hQ hT hS hA hB hSD hUP
        (by simpa [P, T, U, critical] using hcriticalBase)
  have hchangedP : changed P = none := by simp [changed, hPS, P, hP]
  have hchangedR : changed R = none := by simp [changed, hRS, R, hR]
  have hchangedQ : changed Q = some i := by simp [changed, hQS, Q, hQ]
  have hchangedC : changed C = some e := by simp [changed, hCS, C, hC]
  have hchangedD : changed D = none := by simp [changed, hDS, D, hD]
  have hchangedT : changed T = some j := by simp [changed, hTS, T, hT]
  have hchangedS : changed S = some e := by simp [changed]
  have hcritEq : changedCritical = recolor G critical S (some e) := by
    funext f
    by_cases hfP : f = P
    · subst f
      simp [changedCritical, changed, critical, hPS, hPS.symm,
        hPT, hPT.symm]
    · by_cases hfT : f = T
      · subst f
        simp [changedCritical, changed, critical, hPT, hPT.symm,
          hTS, hTS.symm]
      · by_cases hfS : f = S
        · subst f
          simp [changedCritical, changed, critical, hPS, hPS.symm,
            hTS, hTS.symm]
        · simp [changedCritical, changed, critical, hfP, hfT, hfS]
  have huS : u ∉ (S : Sym2 V) := by
    intro hmem
    have hcase : u = q.getVert 1 ∨ u = q.getVert 2 := by simpa [S] using hmem
    rcases hcase with hux₁ | hux₂
    · exact hq.first_step_adj.ne hux₁
    · exact r.second_ne_start hux₂.symm
  have htS : t ∉ (S : Sym2 V) := by
    intro hmem
    have hcase : t = q.getVert 1 ∨ t = q.getVert 2 := by simpa [S] using hmem
    rcases hcase with htx₁ | htx₂
    · exact r.first_ne_end htx₁.symm
    · exact r.last_adj.ne htx₂.symm
  have hagreeCrit : ColoringsAgreeOff G ({S} : Set G.edgeSet)
      critical changedCritical := by
    rw [hcritEq]
    simpa using coloringsAgreeOff_recolor G critical S (some e)
  have hmissStart : ∀ f, IsExternalAt G u T f →
      f ∉ ({S} : Set G.edgeSet) := by
    intro f hfext hfset
    have hf : f = S := by simpa using hfset
    subst f
    exact huS hfext.1
  have hmissFar : ∀ f, IsExternalAt G t U f →
      f ∉ ({S} : Set G.edgeSet) := by
    intro f hfext hfset
    have hf : f = S := by simpa using hfset
    subst f
    exact htS hfext.1
  have hcriticalChanged :
      ExternalEdgesInduced G changedCritical u T ∧
        ExternalEdgesInduced G changedCritical t U ∧
        ExternalInducedColors G changedCritical u T =
          ExternalInducedColors G changedCritical t U := by
    have hstart := externalEdgesInduced_of_agreeOff G hagreeCrit
      hmissStart hcriticalBase.1
    have hfar := externalEdgesInduced_of_agreeOff G hagreeCrit
      hmissFar hcriticalBase.2.1
    have hstartEq := externalInducedColors_eq_of_agreeOff G hagreeCrit hmissStart
    have hfarEq := externalInducedColors_eq_of_agreeOff G hagreeCrit hmissFar
    refine ⟨hstart, hfar, ?_⟩
    calc
      ExternalInducedColors G changedCritical u T =
          ExternalInducedColors G critical u T := hstartEq.symm
      _ = ExternalInducedColors G critical t U := hcriticalBase.2.2
      _ = ExternalInducedColors G changedCritical t U := hfarEq
  have hAS : (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) ≠ S := by
    intro hEq
    have hf : none = some c := hA.symm.trans (by simpa [S, hEq] using hS)
    simp at hf
  have hBS : (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) ≠ S := by
    intro hEq
    have hf : none = some c := hB.symm.trans (by simpa [S, hEq] using hS)
    simp at hf
  apply longPair_hasGoodFour_of_twoThread_middle_induced_alt_twoTwo
    G hsub h g q hq hvw hvq hwq changed hpreparedChanged c i j
  · exact hchangedP
  · exact hchangedR
  · exact hchangedQ
  · exact hchangedT
  · rw [hchangedC]
    simpa using hec
  · rw [hchangedS]
    simp
  · rw [hchangedS]
    simpa using hec
  · simp [changed, hAS, hA]
  · simp [changed, hBS, hB]
  · exact Or.inr hchangedD
  · exact hPD
  · exact hTD
  · exact hUP
  · exact hDP
  · exact hDT
  · exact hRP
  · exact hRT
  · exact hci
  · exact hcj
  · simpa [P, T, changedCritical] using hcriticalChanged

/-! ## The two-thread middle-edge conclusion -/

/-- In a bad graph, the middle edge of either displayed 2-thread is
matching-coloured.  The other 2-thread is used only to classify the unique
four-colour obstruction: its middle edge is matching, has the same induced
colour, or has the other complementary induced colour. -/
theorem longPair_twoThread_middle_matching_in_bad_graph_twoTwo
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z s t : V} {p : G.Walk u z} {q : G.Walk u s} {r : G.Walk u t}
    (hp : IsKThread G p 3) (hq : IsKThread G q 2)
    (hr : IsKThread G r 2)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) :
    (transportColoringToSupergraph
        (G.deleteIncidenceSet_le (p.getVert 2)) small)
      (⟨s(r.getVert 1, r.getVert 2),
        (hr.twoThreadCoreData G).middle_adj⟩ : G.edgeSet) = none := by
  classical
  let h := hp.threeThreadCore G
  let g := hq.twoThreadCoreData G
  let rr := hr.twoThreadCoreData G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le (p.getVert 2)) small
  let Dset : Set G.edgeSet :=
    RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
  let P : G.edgeSet := threadFirstEdge G p hp
  let R : G.edgeSet := threadLastEdge G p hp
  let Q : G.edgeSet := threadFirstEdge G q hq
  let C : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2), g.middle_adj⟩
  let D : G.edgeSet := threadLastEdge G q hq
  let T : G.edgeSet := threadFirstEdge G r hr
  let S : G.edgeSet :=
    ⟨s(r.getVert 1, r.getVert 2), rr.middle_adj⟩
  let U : G.edgeSet := threadLastEdge G r hr
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
  have hqLen : q.length = 3 := by simpa using hq.length
  have hrLen : r.length = 3 := by simpa using hr.length
  have hpGetNe (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) (hab : a ≠ b) :
      p.getVert a ≠ p.getVert b := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using ha)
      (show b ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using hb)
      heq
    exact hab hinj
  have hqGetNe (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (hab : a ≠ b) :
      q.getVert a ≠ q.getVert b := by
    intro heq
    have hinj := hq.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ q.length} by simpa [hqLen] using ha)
      (show b ∈ {n : ℕ | n ≤ q.length} by simpa [hqLen] using hb)
      heq
    exact hab hinj
  have hrGetNe (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (hab : a ≠ b) :
      r.getVert a ≠ r.getVert b := by
    intro heq
    have hinj := hr.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ r.length} by simpa [hrLen] using ha)
      (show b ∈ {n : ℕ | n ≤ r.length} by simpa [hrLen] using hb)
      heq
    exact hab hinj
  have hpEnd : p.getVert 4 = z := by
    rw [← hpLen]
    exact p.getVert_length
  have hqEnd : q.getVert 3 = s := by
    rw [← hqLen]
    exact q.getVert_length
  have hrEnd : r.getVert 3 = t := by
    rw [← hrLen]
    exact r.getVert_length
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = u ∨ p.getVert 2 = p.getVert 1 := by
      simpa [P, threadFirstEdge] using hmem
    exact hcase.elim
      (fun he ↦ hpGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using he))
      (hpGetNe 2 1 (by omega) (by omega) (by omega))
  have huFarQ := twoThread_vertex_far_from_threeThread_middle G hq h
    q.start_mem_support
  have huFarR := twoThread_vertex_far_from_threeThread_middle G hr h
    r.start_mem_support
  have hQD : Q ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      huFarQ.1 huFarQ.2 Q (by simp [Q, threadFirstEdge])
  have hTD : T ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      huFarR.1 huFarR.2 T (by simp [T, threadFirstEdge])
  have hCD : C ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = q.getVert 1 ∨
        p.getVert 2 = q.getVert 2 := by simpa [C] using hmem
    rcases hcase with hcase | hcase
    · exact (twoThread_vertex_far_from_threeThread_middle G hq h
        (q.getVert_mem_support 1)).1 hcase.symm
    · exact (twoThread_vertex_far_from_threeThread_middle G hq h
        (q.getVert_mem_support 2)).1 hcase.symm
  have hSD : S ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = r.getVert 1 ∨
        p.getVert 2 = r.getVert 2 := by simpa [S] using hmem
    rcases hcase with hcase | hcase
    · exact (twoThread_vertex_far_from_threeThread_middle G hr h
        (r.getVert_mem_support 1)).1 hcase.symm
    · exact (twoThread_vertex_far_from_threeThread_middle G hr h
        (r.getVert_mem_support 2)).1 hcase.symm
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hpq
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hr.first_step_adj hpr
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj
        hr.first_step_adj hqr
  have hQC : Q ≠ C := by
    intro heq
    have hval : s(u, q.getVert 1) = s(q.getVert 1, q.getVert 2) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hq.first_step_adj.ne hval.1
    · exact hqGetNe 0 2 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
  have hTS : T ≠ S := by
    intro heq
    have hval : s(u, r.getVert 1) = s(r.getVert 1, r.getVert 2) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hr.first_step_adj.ne hval.1
    · exact hrGetNe 0 2 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
  have hCT : C ≠ T := by
    intro heq
    have hval : s(q.getVert 1, q.getVert 2) =
        s(u, r.getVert 1) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hq.first_step_adj.ne hval.1.symm
    · exact hqGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hval.2)
  have hQS : Q ≠ S := by
    intro heq
    have hval : s(u, q.getVert 1) =
        s(r.getVert 1, r.getVert 2) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hr.first_step_adj.ne hval.1
    · exact hrGetNe 0 2 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
  have hUP : U ≠ P := by
    intro heq
    have hval : s(r.getVert 2, t) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hrGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hrGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa [hrEnd] using hval.2)
  have hDP : D ≠ P := by
    intro heq
    have hval : s(q.getVert 2, s) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hqGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hqGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa [hqEnd] using hval.2)
  have hDT : D ≠ T := by
    intro heq
    have hval : s(q.getVert 2, s) = s(u, r.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hqGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact (IsKThread.endpoints_ne G hq) (by simpa [hqEnd] using hval.2.symm)
  have hRP : R ≠ P := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hpGetNe 3 1 (by omega) (by omega) (by omega) hval.1
  have hRT : R ≠ T := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, r.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hpGetNe 4 0 (by omega) (by omega) (by omega)
        (by simpa [hpEnd] using hval.2)
  obtain ⟨hP, hR, _hpal⟩ :=
    longPair_threeThread_hard_normal_form_of_no_goodFour G hgirth h small
      hsmall hsub hbad
  have hprepared : PreparedThreeThreadGap G h base :=
    preparedThreeThreadGap_of_goodFour G hsub h small hsmall
  have hAD : A ∉ Dset := by
    simpa [h, A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [h, B, Dset, Sym2.eq_swap] using
      right_chain_edge_not_retained G h.right_adj
  have hA : base A = none := by
    have hAe : A.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [Dset, RetainedEdges] using hAD
    simp [base, transportColoringToSupergraph, hAe]
  have hB : base B = none := by
    have hBe : B.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [Dset, RetainedEdges] using hBD
    simp [base, transportColoringToSupergraph, hBe]
  by_contra hSne
  have hSnon : base S ≠ none := by simpa [S, rr, base] using hSne
  obtain ⟨j, hTval, hcritical⟩ :=
    longPair_twoThread_second_induced_critical_normal_form
      G hp hr hpr small hsmall hsub
        (by simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP)
        (by simpa [h, base, R, threadLastEdge] using hR)
        (by simpa [S, rr, base] using hSnon) hbad
  have hPval : base P = none := by
    simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP
  have hRval : base R = none := by
    simpa [h, base, R, threadLastEdge] using hR
  have hTval' : base T = some j := by simpa [base, T] using hTval
  have hvalid : IsOneTwoColoringOn G Dset base := by
    simpa [Dset] using hprepared.1
  have hQne : base Q ≠ none := by
    intro hQnone
    have hcompat := hvalid P hPD Q hQD hPQ
    have hdisj : EndpointDisjoint G P Q := by
      simpa [hPval, hQnone] using hcompat
    exact hdisj u (by simp [P, threadFirstEdge])
      (by simp [Q, threadFirstEdge])
  cases hQval : base Q with
  | none => exact False.elim (hQne hQval)
  | some i =>
      have hij : i ≠ j := by
        intro hij
        subst j
        have hcompat := hvalid Q hQD T hTD hQT
        have hsep : InducedSeparated G Q T := by
          simpa [hQval, hTval'] using hcompat
        exact hsep.1 u (by simp [Q, threadFirstEdge])
          (by simp [T, threadFirstEdge])
      cases hSval : base S with
      | none => exact False.elim (hSnon hSval)
      | some c =>
          cases hCval : base C with
          | none =>
              apply hbad
              exact longPair_hasGoodFour_of_twoThread_middle_induced_same_or_matching
                G hsub h g r hr hpq hpr hqr base hprepared i j c hij
                  (by simpa [P, threadFirstEdge, Sym2.eq_swap] using hPval) hRval
                  (by simpa [base, Q, g, threadFirstEdge, Sym2.eq_swap] using hQval)
                  (by simpa [base, T] using hTval')
                  (by simpa [base, S, rr] using hSval)
                  (Or.inl (by simpa [base, C, g] using hCval))
                  (by simpa [h, base, A] using hA)
                  (by simpa [h, base, B] using hB)
                  (by simpa [h, P, Dset, threadFirstEdge, Sym2.eq_swap] using hPD)
                  (by simpa [T, Dset] using hTD)
                  (by simpa [h, P, U, threadFirstEdge, threadLastEdge,
                    Sym2.eq_swap] using hUP)
                  (by simpa [h, P, D, g, threadFirstEdge, threadLastEdge,
                    Sym2.eq_swap] using hDP)
                  (by simpa [D, T, g, threadFirstEdge, threadLastEdge,
                    Sym2.eq_swap] using hDT)
                  (by simpa [h, P, R, threadFirstEdge, threadLastEdge,
                    Sym2.eq_swap] using hRP)
                  (by simpa [h, R, T, threadFirstEdge, threadLastEdge,
                    Sym2.eq_swap] using hRT)
                  (by simpa [base, P, T, threadFirstEdge, Sym2.eq_swap] using hcritical)
          | some e =>
              by_cases hec : e = c
              · subst e
                apply hbad
                exact longPair_hasGoodFour_of_twoThread_middle_induced_same_or_matching
                  G hsub h g r hr hpq hpr hqr base hprepared i j c hij
                    (by simpa [P, threadFirstEdge, Sym2.eq_swap] using hPval) hRval
                    (by simpa [base, Q, g, threadFirstEdge, Sym2.eq_swap] using hQval)
                    (by simpa [base, T] using hTval')
                    (by simpa [base, S, rr] using hSval)
                    (Or.inr (by simpa [base, C, g] using hCval))
                    (by simpa [h, base, A] using hA)
                    (by simpa [h, base, B] using hB)
                    (by simpa [h, P, Dset, threadFirstEdge, Sym2.eq_swap] using hPD)
                    (by simpa [T, Dset] using hTD)
                    (by simpa [h, P, U, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hUP)
                    (by simpa [h, P, D, g, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hDP)
                    (by simpa [D, T, g, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hDT)
                    (by simpa [h, P, R, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hRP)
                    (by simpa [h, R, T, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hRT)
                    (by simpa [base, P, T, threadFirstEdge, Sym2.eq_swap] using hcritical)
              · have hei : e ≠ i := by
                  intro hei
                  subst e
                  have hcompat := hvalid Q hQD C hCD hQC
                  have hsep : InducedSeparated G Q C := by
                    simpa [hQval, hCval] using hcompat
                  exact hsep.1 (q.getVert 1)
                    (by simp [Q, threadFirstEdge]) (by simp [C])
                have hej : e ≠ j := by
                  intro hej
                  subst e
                  have hcompat := hvalid C hCD T hTD hCT
                  have hsep : InducedSeparated G C T := by
                    simpa [hCval, hTval'] using hcompat
                  exact hsep.2 ⟨q.getVert 1, by simp [C], u,
                    by simp [T, threadFirstEdge], hq.first_step_adj.symm⟩
                have hci : c ≠ i := by
                  intro hci
                  subst c
                  have hcompat := hvalid Q hQD S hSD hQS
                  have hsep : InducedSeparated G Q S := by
                    simpa [hQval, hSval] using hcompat
                  exact hsep.2 ⟨u, by simp [Q, threadFirstEdge], r.getVert 1,
                    by simp [S], hr.first_step_adj⟩
                have hcj : c ≠ j := by
                  intro hcj
                  subst c
                  have hcompat := hvalid T hTD S hSD hTS
                  have hsep : InducedSeparated G T S := by
                    simpa [hTval', hSval] using hcompat
                  exact hsep.1 (r.getVert 1)
                    (by simp [T, threadFirstEdge]) (by simp [S])
                apply hbad
                exact longPair_hasGoodFour_of_twoThread_middle_induced_distinct
                  G hsub h g r hr hpq hpr hqr base hprepared i j c e
                    hei hej hec hci hcj
                    (by simpa [P, threadFirstEdge, Sym2.eq_swap] using hPval) hRval
                    (by simpa [base, Q, g, threadFirstEdge, Sym2.eq_swap] using hQval)
                    (by simpa [base, T] using hTval')
                    (by simpa [base, C, g] using hCval)
                    (by simpa [base, S, rr] using hSval)
                    (by simpa [h, base, A] using hA)
                    (by simpa [h, base, B] using hB)
                    (by simpa [h, P, Dset, threadFirstEdge, Sym2.eq_swap] using hPD)
                    (by simpa [T, Dset] using hTD)
                    (by simpa [S, rr, Dset] using hSD)
                    (by simpa [h, P, U, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hUP)
                    (by simpa [h, P, D, g, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hDP)
                    (by simpa [D, T, g, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hDT)
                    (by simpa [h, P, R, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hRP)
                    (by simpa [h, R, T, threadFirstEdge, threadLastEdge,
                      Sym2.eq_swap] using hRT)
                    (by simpa [base, P, T, threadFirstEdge, Sym2.eq_swap] using hcritical)

/-! ## Fresh first-edge recolouring with one explicit palette obstruction -/

/-- A degree-two vertex affected by recolouring the first edge of a
2-thread is either its second internal vertex or is adjacent to the common
degree-three endpoint. -/
theorem twoVertex_paletteAffectedBy_twoThreadFirst_cases_twoTwo
    {u w₁ w₂ s q : V} (g : TwoThreadCoreData G u w₁ w₂ s)
    (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = w₂ ∨ G.Adj q u := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, heS, x, hxe, hqx⟩ := haffect
  have heQ : e = (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) := by
    simpa using heS
  subst e
  have hqne : q ≠ u := by
    intro hqu
    have hthree := g.start_three
    have htwo := hq
    unfold IsThreeVertex at hthree
    unfold IsTwoVertex at htwo
    rw [hqu] at htwo
    omega
  have hxcase : x = w₁ ∨ x = u := by simpa using hxe
  rcases hxcase with hxw₁ | hxu
  · subst x
    rcases hqx with hqw₁ | hqw₁
    · exact Or.inr (by simpa [hqw₁] using g.first_adj.symm)
    · have hqN : q ∈ G.neighborFinset w₁ :=
        (G.mem_neighborFinset w₁ q).mpr hqw₁.symm
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start] at hqN
      have hqcase : q = w₂ ∨ q = u := by simpa using hqN
      exact hqcase.elim Or.inl (fun hqu' ↦ False.elim (hqne hqu'))
  · subst x
    rcases hqx with hqu | hqu
    · exact False.elim (hqne hqu)
    · exact Or.inr hqu

/-- Recolouring the first edge of a 2-thread from one induced colour to
another preserves Condition 3 when a different first edge at the common
centre remains matching. -/
theorem conditionThree_recolor_twoThreadFirst_induced_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)) :
    ConditionThree G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ' : P ≠ Q := by simpa [P, Q] using hPQ
  have hnewP : new P = none := by simp [new, hPQ', P, hP]
  have hagree : ColoringsAgreeOff G ({Q} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour Q (some k)
  change ConditionThree G new
  apply hold.of_agreeOff G hagree
  intro a b p hp haffect hleft hright
  rcases haffect with ⟨e, heS, hext⟩ | ⟨e, heS, hext⟩
  · have heQ : e = Q := by simpa using heS
    subst e
    have hau : a = u := by
      have hcase : a = w₁ ∨ a = u := by simpa [Q] using hext.1
      rcases hcase with haw | hau
      · exact False.elim
          ((isThreeVertex_ne_isTwoVertex G hp.start_three g.first_two) haw)
      · exact hau
    subst a
    have hTP : threadFirstEdge G p hp ≠ P := by
      simpa [P] using
        longPair_twoThread_firstEdge_ne_threeThread_firstEdge G p hp h
    obtain ⟨i, hi⟩ := hleft P ⟨by simp [P], fun he ↦ hTP he.symm⟩
    rw [hnewP] at hi
    simp at hi
  · have heQ : e = Q := by simpa using heS
    subst e
    have hbu : b = u := by
      have hcase : b = w₁ ∨ b = u := by simpa [Q] using hext.1
      rcases hcase with hbw | hbu
      · exact False.elim
          ((isThreeVertex_ne_isTwoVertex G hp.end_three g.first_two) hbw)
      · exact hbu
    subst b
    have hTP : threadLastEdge G p hp ≠ P := by
      simpa [P] using
        longPair_twoThread_lastEdge_ne_threeThread_firstEdge G p hp h
    obtain ⟨i, hi⟩ := hright P ⟨by simp [P], fun he ↦ hTP he.symm⟩
    rw [hnewP] at hi
    simp at hi

/-- Availability of a fresh induced colour on the first edge of one
2-thread when both displayed middle edges are matching. -/
theorem longPair_forkFirst_fresh_available_twoTwoArms
    {u v₁ v₂ v₃ z w₁ w₂ s x₁ x₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (r : TwoThreadCoreData G u x₁ x₂ t)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) = none)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDk : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠ some k)
    (hretained : ∀ f : G.edgeSet, f ∈ Dset → v₂ ∉ (f : Sym2 V)) :
    ColorAvailableOn G Dset colour
      (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hC' : colour C = none := by simpa [C] using hC
  have hS' : colour S = none := by simpa [S] using hS
  have hDk' : colour D ≠ some k := by simpa [D] using hDk
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  have noAtU (f : G.edgeSet) (hfQ : f ≠ Q)
      (huf : u ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hf := f.2
      rw [hfa] at hf
      simpa using hf
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      have hfalse : none = some k := hP'.symm.trans (by simpa [hfP] using hcf)
      simp at hfalse
    · exact hfQ (Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa))
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      exact hk ⟨T, ⟨by simp [T], hPT.symm⟩, by simpa [hfT] using hcf⟩
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
        g.middle_adj g.first_adj.symm g.second_ne_start f hwf with hfC | hfQ'
    · have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
      have hfalse : none = some k := hC'.symm.trans (by simpa [hfC'] using hcf)
      simp at hfalse
    · exact hfQ (Subtype.ext (by simpa [Q] using hfQ'))
  have noAtX₁ (f : G.edgeSet)
      (hxf : x₁ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.middle_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT
    · have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
      have hfalse : none = some k := hS'.symm.trans (by simpa [hfS'] using hcf)
      simp at hfalse
    · have hfT' : f = T := Subtype.ext (by simpa [T] using hfT)
      exact hk ⟨T, ⟨by simp [T], hPT.symm⟩, by simpa [hfT'] using hcf⟩
  have noAtW₂ (f : G.edgeSet)
      (hwf : w₂ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.second_two
        g.middle_adj.symm g.last_adj g.first_ne_end f hwf with hfC | hfD
    · have hfC' : f = C := Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC)
      have hfalse : none = some k := hC'.symm.trans (by simpa [hfC'] using hcf)
      simp at hfalse
    · exact hDk' (by
        have hfD' : f = D := Subtype.ext (by simpa [D] using hfD)
        simpa [hfD'] using hcf)
  apply (colorAvailableOn_some_iff G Dset colour Q k).mpr
  intro f hfD hfQ hcf
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = w₁ ∨ a = u := by simpa [Q] using ha
  rcases hacase with haw | hau
  · constructor
    · intro hwb
      exact noAtW₁ f hfQ (by simpa [haw.symm.trans hwb] using hbf) hcf
    · intro hwb
      have hbN : b ∈ G.neighborFinset w₁ :=
        (G.mem_neighborFinset w₁ b).mpr (by simpa [haw] using hwb)
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start] at hbN
      have hbcase : b = w₂ ∨ b = u := by simpa using hbN
      exact hbcase.elim
        (fun hb ↦ noAtW₂ f (by simpa [hb] using hbf) hcf)
        (fun hb ↦ noAtU f hfQ (by simpa [hb] using hbf) hcf)
  · constructor
    · intro hub
      exact noAtU f hfQ (by simpa [hau.symm.trans hub] using hbf) hcf
    · intro hub
      have hub' : G.Adj u b := by simpa [hau] using hub
      rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
          g.first_adj r.first_adj hvw hvx hwx hub' with rfl | rfl | rfl
      · exact noAtV₁ f hfD hbf hcf
      · exact noAtW₁ f hfQ hbf hcf
      · exact noAtX₁ f hbf hcf

/-- Condition 2 after the fresh first-edge recolouring, assuming precisely
that the second internal vertex of that arm does not see all four induced
colours. -/
theorem conditionTwo_recolor_twoThreadFirst_fresh_of_not_full_twoTwo
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s x₁ x₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (r : TwoThreadCoreData G u x₁ x₂ t)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (hold : ConditionTwo G colour)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hnotfull : ¬ ∀ i : Fin 4, VertexSeesInduced G
      (recolor G colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)
        (some k)) w₂ i) :
    ConditionTwo G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.middle_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have hCQ : C ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      g.start_three g.middle_adj g.first_adj.symm
  have hSQ : S ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G r.first_two r.second_two
      g.start_three r.middle_adj g.first_adj.symm
  have hAQ : A ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      g.start_three h.left_adj g.first_adj.symm
  have hBQ : B ≠ Q :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      g.start_three h.right_adj.symm g.first_adj.symm
  have hCP : C ≠ P := by
    intro heq
    apply longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj h.first_adj.symm
    apply Subtype.ext
    have hval := congrArg Subtype.val heq
    simpa [C, P, threadFirstEdge, Sym2.eq_swap] using hval
  have hSP : S ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G r.first_two r.second_two
      h.start_three r.middle_adj h.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hnewP : new P = none := by simp [new, hPQ, P, hP]
  have hnewC : new C = none := by simp [new, hCQ, C, hC]
  have hnewS : new S = none := by simp [new, hSQ, S, hS]
  have hnewA : new A = none := by simp [new, hAQ, A, hA]
  have hnewB : new B = none := by simp [new, hBQ, B, hB]
  have hagree : ColoringsAgreeOff G ({Q} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour Q (some k)
  have hNu : G.neighborFinset u = {v₁, w₁, x₁} :=
    neighborFinset_eq_triple_of_isThreeVertex G h.start_three
      h.first_adj g.first_adj r.first_adj hvw hvx hwx
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect _hmatch hall
  rcases twoVertex_paletteAffectedBy_twoThreadFirst_cases_twoTwo G g hq
      (by simpa [Q] using haffect) with hqw₂ | hqu
  · subst q
    exact hnotfull (by simpa [new, Q] using hall)
  · have hqN : q ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u q).mpr hqu.symm
    rw [hNu] at hqN
    have hqcase : q = v₁ ∨ q = w₁ ∨ q = x₁ := by simpa using hqN
    rcases hqcase with hqv₁ | hqw₁ | hqx₁
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub h.first_two
        h.left_adj h.middle_two A B hAB hnewA hnewB
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [A]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [B]) (Or.inr h.left_adj)
      · exact hall
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub g.first_two
        g.middle_adj g.second_two C P hCP hnewC hnewP
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [P]) (Or.inr g.first_adj.symm)
      · exact hall
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub r.first_two
        r.middle_adj r.second_two S P hSP hnewS hnewP
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [S]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [P]) (Or.inr r.first_adj.symm)
      · exact hall

/-- Complete prepared-gap preservation for a fresh first-edge recolouring,
with the sole possible full-palette obstruction excluded explicitly. -/
theorem longPair_prepared_recolor_forkFirst_fresh_twoTwo_of_not_full
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s x₁ x₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (r : TwoThreadCoreData G u x₁ x₂ t)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hDk : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠ some k)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hnotfull : ¬ ∀ a : Fin 4, VertexSeesInduced G
      (recolor G colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)
        (some k)) w₂ a) :
    PreparedThreeThreadGap G h
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have havail : ColorAvailableOn G Dset colour Q (some k) := by
    exact longPair_forkFirst_fresh_available_twoTwoArms G h g r hvw hvx hwx
      colour Dset k hP hC hS hk hDk
        (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalid : IsOneTwoColoringOn G Dset new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := Q) (a := some k)
      (by simpa [Dset, Q] using hQD)).mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.sdiff_subset, havail⟩
  have hsat : OneSaturated G new := by
    simpa [new, Q] using oneSaturated_recolor_induced_to_induced
      G hprepared.2.1 Q i k (by simpa [Q] using hQ)
  have htwo : ConditionTwo G new := by
    simpa [new, Q] using
      conditionTwo_recolor_twoThreadFirst_fresh_of_not_full_twoTwo
        G hsub h g r hvw hvx hwx colour hprepared.2.2.1 k
          hP hC hS hA hB hnotfull
  have hPQ : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ≠ Q := by
    simpa [Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have hthree : ConditionThree G new := by
    simpa [new, Q] using
      conditionThree_recolor_twoThreadFirst_induced_twoTwo G h g colour
        hprepared.2.2.2 k hP hPQ
  exact ⟨by simpa [Dset, new] using hvalid,
    by simpa [new] using hsat, by simpa [new] using htwo,
    by simpa [new] using hthree⟩

/-- Four pairwise distinct elements exhaust `Fin 4`. -/
theorem finFour_eq_one_of_pairwise_distinct
    (i j k l a : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    a = i ∨ a = j ∨ a = k ∨ a = l := by
  classical
  have hcard : ({i, j, k, l} : Finset (Fin 4)).card = 4 := by
    simp [hij, hik, hil, hjk, hjl, hkl]
  have huniv : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hcard)
  have ha : a ∈ ({i, j, k, l} : Finset (Fin 4)) := by
    rw [huniv]
    simp
  simpa only [Finset.mem_insert, Finset.mem_singleton] using ha

/-- If recolouring the first edge of a 2-thread with the second
complementary colour makes its second internal vertex see all four induced
colours, then the far external edges are all induced and use exactly the
two centre colours. -/
theorem full_second_palette_after_fresh_far_normal_form_twoTwo
    (hsub : IsSubcubic G)
    {u w₁ w₂ s : V} (g : TwoThreadCoreData G u w₁ w₂ s)
    (Dset : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G Dset colour)
    (hold : ConditionTwo G colour)
    (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = some k)
    (hDD : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ∈ Dset)
    (hret : ∀ f, IsExternalAt G s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) f → f ∈ Dset)
    (hall : ∀ a : Fin 4, VertexSeesInduced G
      (recolor G colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet)
        (some l)) w₂ a) :
    ExternalEdgesInduced G colour s
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ∧
      ExternalInducedColors G colour s
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = {i, j} := by
  classical
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some l)
  have hCQ : C ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      g.start_three g.middle_adj g.first_adj.symm
  have hCD : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hDQ : D ≠ Q := by
    simpa [D, Q] using (twoThreadCore_firstEdge_ne_lastEdge G g).symm
  have hnewC : new C = none := by simp [new, hCQ, C, hC]
  have hnewD : new D = some k := by simp [new, hDQ, D, hD]
  have hmatch : VertexSeesMatching G new w₂ :=
    (vertexSeesMatching_iff G new w₂).mpr ⟨C, hnewC, by simp [C]⟩
  have hnotL : ¬ VertexSeesInduced G colour w₂ l := by
    simpa [Q, new] using
      not_seen_base_of_full_after_leaf_colour_four G g.first_adj.symm colour
        hold g.second_two l hmatch (by simpa [Q, new] using hall)
  have hexternal : ExternalEdgesInduced G colour s D := by
    intro f hfext
    by_contra hfnone
    have hcfnone : colour f = none := by
      cases hcf : colour f with
      | none => rfl
      | some a => exact False.elim (hfnone ⟨a, hcf⟩)
    have hfQ : f ≠ Q := by
      intro hEq
      subst f
      have hQi : colour Q = some i := by simpa [Q] using hQ
      have hfalse : some i = none := hQi.symm.trans hcfnone
      simp at hfalse
    have hfC : f ≠ C := by
      intro hEq
      subst f
      have hscase : s = w₁ ∨ s = w₂ := by simpa [C] using hfext.1
      rcases hscase with hsw₁ | hsw₂
      · exact (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two) hsw₁
      · exact (isThreeVertex_ne_isTwoVertex G g.end_three g.second_two) hsw₂
    have hnewf : new f = none := by simp [new, hfQ, hcfnone]
    have hfvis : (f : Sym2 V) ∈ vertexVisibleEdgeFinset G w₂ :=
      mem_vertexVisibleEdgeFinset_of_endpoint_close G hfext.1
        (Or.inr g.last_adj)
    exact longPair_paletteCondition_at_two_visible_matching G hsub
      g.second_two g.middle_adj.symm g.first_two C f hfC.symm
        hnewC hnewf
        (mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)) hfvis hall
  have hfromFull (a : Fin 4) (hak : a ≠ k) (hal : a ≠ l) :
      a ∈ ExternalInducedColors G colour s D := by
    obtain ⟨f, hfnew, x, hxf, hclose⟩ :=
      (vertexSeesInduced_iff G new w₂ a).mp (hall a)
    have hfQ : f ≠ Q := by
      intro hEq
      subst f
      have heq : some l = some a := by simpa [new] using hfnew
      exact hal (Option.some.inj heq).symm
    have hfC : f ≠ C := by
      intro hEq
      subst f
      have hfalse : none = some a := hnewC.symm.trans hfnew
      simp at hfalse
    have hfD : f ≠ D := by
      intro hEq
      subst f
      have heq : some k = some a := hnewD.symm.trans hfnew
      exact hak (Option.some.inj heq).symm
    have hfold : colour f = some a := by simpa [new, hfQ] using hfnew
    have hsx : x = s := by
      rcases hclose with hwx | hwx
      · subst x
        rcases edge_eq_left_or_right_of_incident_two G g.second_two
            g.middle_adj.symm g.last_adj g.first_ne_end f hxf with hfC' | hfD'
        · exact False.elim (hfC
            (Subtype.ext (by simpa [C, Sym2.eq_swap] using hfC')))
        · exact False.elim (hfD
            (Subtype.ext (by simpa [D] using hfD')))
      · have hxN : x ∈ G.neighborFinset w₂ :=
          (G.mem_neighborFinset w₂ x).mpr hwx
        rw [neighborFinset_eq_pair_of_isTwoVertex G g.second_two
          g.middle_adj.symm g.last_adj g.first_ne_end] at hxN
        have hxcase : x = w₁ ∨ x = s := by simpa using hxN
        rcases hxcase with hxw₁ | hxs
        · subst x
          rcases edge_eq_left_or_right_of_incident_two G g.first_two
              g.middle_adj g.first_adj.symm g.second_ne_start f hxf with
            hfC' | hfQ'
          · exact False.elim (hfC
              (Subtype.ext (by simpa [C] using hfC')))
          · exact False.elim (hfQ
              (Subtype.ext (by simpa [Q] using hfQ')))
        · exact hxs
    exact ⟨f, ⟨by simpa [hsx] using hxf, hfD⟩, hfold⟩
  refine ⟨hexternal, ?_⟩
  ext a
  constructor
  · rintro ⟨f, hfext, hfa⟩
    have hal : a ≠ l := by
      intro hal
      subst a
      apply hnotL
      apply (vertexSeesInduced_iff G colour w₂ l).mpr
      exact ⟨f, hfa, s, hfext.1, Or.inr g.last_adj⟩
    have hak : a ≠ k := by
      intro hak
      subst a
      have hcompat := hvalid D hDD f (hret f hfext) hfext.2.symm
      have hsep : InducedSeparated G D f := by
        simpa [D, hD, hfa] using hcompat
      exact hsep.1 s (by simp [D]) hfext.1
    rcases finFour_eq_one_of_pairwise_distinct i j k l a hij hik hil
        hjk hjl hkl with hai | haj | hak' | hal'
    · simp [hai]
    · simp [haj]
    · exact False.elim (hak hak')
    · exact False.elim (hal hal')
  · intro ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with hai | haj
    · simpa [hai] using hfromFull i hik hil
    · simpa [haj] using hfromFull j hjk hjl

/-! ## Moving the terminal induced colour one step inward -/

/-- A degree-two vertex whose palette can be changed by the middle and
last edges of a 2-thread is one of its two internal vertices, or is
adjacent to the far endpoint. -/
theorem twoVertex_paletteAffectedBy_twoThreadTail_cases
    {u w₁ w₂ s q : V} (g : TwoThreadCoreData G u w₁ w₂ s)
    (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet),
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)} : Set G.edgeSet) q) :
    q = w₁ ∨ q = w₂ ∨ G.Adj q s := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, heS, x, hxe, hqx⟩ := haffect
  have hecase : e = (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ∨
      e = (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) := by
    simpa using heS
  have hqneS : q ≠ s := by
    intro hqs
    exact (isThreeVertex_ne_isTwoVertex G g.end_three hq) hqs.symm
  rcases hecase with rfl | rfl
  · have hxcase : x = w₁ ∨ x = w₂ := by simpa using hxe
    rcases hxcase with hxw₁ | hxw₂
    · subst x
      rcases hqx with hqw₁ | hqw₁
      · exact Or.inl hqw₁
      · have hqN : q ∈ G.neighborFinset w₁ :=
          (G.mem_neighborFinset w₁ q).mpr hqw₁.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
          g.middle_adj g.first_adj.symm g.second_ne_start] at hqN
        have hqcase : q = w₂ ∨ q = u := by simpa using hqN
        rcases hqcase with hqw₂ | hqu
        · exact Or.inr (Or.inl hqw₂)
        · exact False.elim
            ((isThreeVertex_ne_isTwoVertex G g.start_three hq) hqu.symm)
    · subst x
      rcases hqx with hqw₂ | hqw₂
      · exact Or.inr (Or.inl hqw₂)
      · have hqN : q ∈ G.neighborFinset w₂ :=
          (G.mem_neighborFinset w₂ q).mpr hqw₂.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G g.second_two
          g.middle_adj.symm g.last_adj g.first_ne_end] at hqN
        have hqcase : q = w₁ ∨ q = s := by simpa using hqN
        rcases hqcase with hqw₁ | hqs
        · exact Or.inl hqw₁
        · exact False.elim (hqneS hqs)
  · have hxcase : x = w₂ ∨ x = s := by simpa using hxe
    rcases hxcase with hxw₂ | hxs
    · subst x
      rcases hqx with hqw₂ | hqw₂
      · exact Or.inr (Or.inl hqw₂)
      · have hqN : q ∈ G.neighborFinset w₂ :=
          (G.mem_neighborFinset w₂ q).mpr hqw₂.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G g.second_two
          g.middle_adj.symm g.last_adj g.first_ne_end] at hqN
        have hqcase : q = w₁ ∨ q = s := by simpa using hqN
        rcases hqcase with hqw₁ | hqs
        · exact Or.inl hqw₁
        · exact False.elim (hqneS hqs)
    · subst x
      rcases hqx with hqs | hqs
      · exact False.elim (hqneS hqs)
      · exact Or.inr (Or.inr hqs)

/-- With the terminal edge temporarily omitted, its induced colour is
available on the middle edge.  The old terminal edge controls the far
side, while absence from the selected external palette controls the
centre side. -/
theorem longPair_twoThreadMiddle_shift_induced_available_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = some k)
    (hDD : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet)) :
    ColorAvailableOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G \
        {(⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet),
          (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)})
      colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let D₀ : Set G.edgeSet := Dset \ {C, D}
  have hDD' : D ∈ Dset := by simpa [Dset, D] using hDD
  have hD' : colour D = some k := by simpa [D] using hD
  have hP' : colour P = none := by simpa [P] using hP
  change ColorAvailableOn G D₀ colour C (some k)
  apply (colorAvailableOn_some_iff G D₀ colour C k).mpr
  intro f hf₀ hfC hfk
  have hfDset : f ∈ Dset := hf₀.1
  have hfne : f ≠ C ∧ f ≠ D := by simpa [D₀] using hf₀.2
  have hsepD : InducedSeparated G D f := by
    have hp := hvalid D hDD' f hfDset (Ne.symm hfne.2)
    simpa [hD', hfk] using hp
  have noAtU (huf : u ∈ (f : Sym2 V)) : False := by
    by_cases hfP : f = P
    · subst f
      have hfalse : none = some k := hP'.symm.trans hfk
      simp at hfalse
    · exact hk ⟨f, ⟨huf, hfP⟩, hfk⟩
  have noAtW₁ (hw₁f : w₁ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.first_adj.symm g.middle_adj g.second_ne_start.symm f hw₁f with
      hfQ | hfC'
    · have hEqQ : f = Q :=
        Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfQ)
      exact noAtU (by simpa [hEqQ, Q])
    · exact hfne.1 (Subtype.ext (by simpa [C] using hfC'))
  rw [inducedSeparated_iff_forall_endpoints] at hsepD ⊢
  intro a ha b hbf
  have hacase : a = w₁ ∨ a = w₂ := by simpa [C] using ha
  rcases hacase with haw₁ | haw₂
  · constructor
    · intro hab
      apply noAtW₁
      rw [← haw₁, hab]
      exact hbf
    · intro hab
      have hbN : b ∈ G.neighborFinset w₁ :=
        (G.mem_neighborFinset w₁ b).mpr (by simpa [haw₁] using hab)
      rw [neighborFinset_eq_pair_of_isTwoVertex G g.first_two
        g.middle_adj g.first_adj.symm g.second_ne_start] at hbN
      have hbcase : b = w₂ ∨ b = u := by simpa using hbN
      rcases hbcase with hbw₂ | hbu
      · exact (hsepD w₂ (by simp [D]) w₂
          (by simpa [hbw₂] using hbf)).1 rfl
      · exact noAtU (by simpa [hbu] using hbf)
  · simpa [haw₂] using hsepD w₂ (by simp [D]) b hbf

/-- After the induced colour has moved to the middle edge, the terminal
edge can receive the matching colour: the old middle matching edge
controls `w₂`, and all other edges at the far endpoint are induced. -/
theorem longPair_twoThreadLast_shift_matching_available_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (k : Fin 4)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hCD : (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hfar : ExternalEdgesInduced G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)) :
    ColorAvailableOn G
      (insert (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet)
        (RetainedEdges (G.deleteIncidenceSet v₂) G \
          {(⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet),
            (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)}))
      (recolor G colour
        (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let D₀ : Set G.edgeSet := Dset \ {C, D}
  let afterC : G.edgeSet → OneTwoColor 4 := recolor G colour C (some k)
  have hCD' : C ∈ Dset := by simpa [C, Dset] using hCD
  have hC' : colour C = none := by simpa [C] using hC
  change ColorAvailableOn G (insert C D₀) afterC D none
  apply (colorAvailableOn_none_iff G (insert C D₀) afterC D).mpr
  intro f hfIns hfD hfnew
  rcases hfIns with hEq | hf₀
  · subst f
    have hfalse : some k = none := by simpa [afterC] using hfnew
    simp at hfalse
  · have hfDset : f ∈ Dset := hf₀.1
    have hfne : f ≠ C ∧ f ≠ D := by simpa [D₀] using hf₀.2
    have hfold : colour f = none := by
      simpa [afterC, hfne.1] using hfnew
    have hCdisj : EndpointDisjoint G C f := by
      have hp := hvalid C hCD' f hfDset (Ne.symm hfne.1)
      simpa [hC', hfold] using hp
    intro y hyD hyf
    have hycase : y = w₂ ∨ y = s := by simpa [D] using hyD
    rcases hycase with hyw₂ | hys
    · exact hCdisj w₂ (by simp [C]) (by simpa [hyw₂] using hyf)
    · obtain ⟨a, ha⟩ := hfar f
          ⟨by simpa [hys] using hyf, hfne.2⟩
      have hfalse : none = some a := hfold.symm.trans ha
      simp at hfalse

/-- Packing validity of the terminal shift `C : matching, D : k` to
`C : k, D : matching`. -/
theorem longPair_validOn_shift_twoThreadTail_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = some k)
    (hCD : (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hfar : ExternalEdgesInduced G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)) :
    IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G)
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let D₀ : Set G.edgeSet := Dset \ {C, D}
  let afterC : G.edgeSet → OneTwoColor 4 := recolor G colour C (some k)
  let final : G.edgeSet → OneTwoColor 4 := recolor G afterC D none
  have hCD' : C ∈ Dset := by simpa [C, Dset] using hCD
  have hDD' : D ∈ Dset := by simpa [D, Dset] using hDD
  have hCDne : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hvalid₀ : IsOneTwoColoringOn G D₀ colour :=
    hvalid.mono G Set.sdiff_subset
  have hCfresh : C ∉ D₀ := by simp [D₀]
  have havailC : ColorAvailableOn G D₀ colour C (some k) := by
    simpa [Dset, D₀, C, D] using
      longPair_twoThreadMiddle_shift_induced_available_twoTwo G h g colour
        hvalid k hP hC hD hDD hk
  have hvalidC : IsOneTwoColoringOn G (insert C D₀) afterC := by
    simpa [afterC] using hvalid₀.extend_one G hCfresh havailC
  have hDfresh : D ∉ insert C D₀ := by simp [D₀, hCDne.symm]
  have havailD : ColorAvailableOn G (insert C D₀) afterC D none := by
    simpa [Dset, D₀, C, D, afterC] using
      longPair_twoThreadLast_shift_matching_available_twoTwo G
        (v₁ := v₁) (v₃ := v₃) (z := z) g colour hvalid k hC hCD hfar
  have hvalidFinal : IsOneTwoColoringOn G (insert D (insert C D₀)) final := by
    simpa [final] using hvalidC.extend_one G hDfresh havailD
  have hcover : insert D (insert C D₀) = Dset := by
    ext f
    simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl | ⟨hf, _⟩)
      · exact hDD'
      · exact hCD'
      · exact hf
    · intro hf
      by_cases hfD : f = D
      · exact Or.inl hfD
      by_cases hfC : f = C
      · exact Or.inr (Or.inl hfC)
      · exact Or.inr (Or.inr ⟨hf, by simp [hfC, hfD]⟩)
  rw [hcover] at hvalidFinal
  simpa [Dset, final, afterC] using hvalidFinal

/-- Matching saturation is preserved by the terminal shift.  The new
middle induced edge is witnessed by the now-matching terminal edge; an
old witness on the middle edge is rerouted either to the selected matching
edge at the centre or to the terminal edge. -/
theorem longPair_oneSaturated_shift_twoThreadTail_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = some k) :
    OneSaturated G
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some k)) D none
  have hCD : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.start_three g.middle_adj h.first_adj.symm
  have hDP : D ≠ P := by
    intro hEq
    have hD' : colour D = some k := by simpa [D] using hD
    have hP' : colour P = none := by simpa [P] using hP
    have hfalse : some k = none := hD'.symm.trans (by simpa [hEq] using hP')
    simp at hfalse
  have hfinalC : final C = some k := by simp [final, hCD]
  have hfinalD : final D = none := by simp [final]
  have hfinalP : final P = none := by
    simp [final, hCP.symm, hDP.symm, P, hP]
  have hfinalOff (e : G.edgeSet) (heC : e ≠ C) (heD : e ≠ D) :
      final e = colour e := by simp [final, heC, heD]
  change OneSaturated G final
  intro e he
  by_cases heC : e = C
  · subst e
    exact ⟨D, hfinalD, w₂, by simp [C], by simp [D]⟩
  by_cases heD : e = D
  · subst e
    exact False.elim (he hfinalD)
  have heOld : colour e ≠ none := by
    intro heNone
    exact he ((hfinalOff e heC heD).trans heNone)
  obtain ⟨f, hf, y, hye, hyf⟩ := hsat e heOld
  by_cases hfC : f = C
  · subst f
    have hycase : y = w₁ ∨ y = w₂ := by simpa [C] using hyf
    rcases hycase with hyw₁ | hyw₂
    · have hw₁e : w₁ ∈ (e : Sym2 V) := by simpa [hyw₁] using hye
      rcases edge_eq_left_or_right_of_incident_two G g.first_two
          g.first_adj.symm g.middle_adj g.second_ne_start.symm e hw₁e with
        heQ | heC'
      · have hEqQ : e = Q :=
          Subtype.ext (by simpa [Q, Sym2.eq_swap] using heQ)
        exact ⟨P, hfinalP, u, by simpa [hEqQ, Q], by simp [P]⟩
      · exact False.elim
          (heC (Subtype.ext (by simpa [C] using heC')))
    · exact ⟨D, hfinalD, y, hye, by simpa [D, hyw₂]⟩
  · have hfD : f ≠ D := by
      intro hEq
      subst f
      have hDsome : colour D = some k := by simpa [D] using hD
      have hDnone : colour D = none := by simpa [D] using hf
      have hfalse : some k = none := hDsome.symm.trans hDnone
      simp at hfalse
    exact ⟨f, (hfinalOff f hfC hfD).trans hf, y, hye, hyf⟩

/-- Condition 2 survives the terminal shift.  A full new palette transports
back to a full old palette by replacing the moved colour on `C` with its
old occurrence on `D`.  At the two internal vertices the old matching edge
is `C`; at a degree-two vertex adjacent to the far endpoint, saturation of
its incident external induced edge supplies an old matching edge there. -/
theorem longPair_conditionTwo_shift_twoThreadTail_twoTwo
    {u w₁ w₂ s : V}
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (hsat : OneSaturated G colour)
    (k : Fin 4)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = some k)
    (hfar : ExternalEdgesInduced G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none) := by
  classical
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some k)) D none
  have hCD : C ≠ D := by
    simpa [C, D, Sym2.eq_swap] using
      chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
  have hC' : colour C = none := by simpa [C] using hC
  have hD' : colour D = some k := by simpa [D] using hD
  have hfinalC : final C = some k := by simp [final, hCD]
  have hfinalD : final D = none := by simp [final]
  have hfinalOff (e : G.edgeSet) (heC : e ≠ C) (heD : e ≠ D) :
      final e = colour e := by simp [final, heC, heD]
  have hagree : ColoringsAgreeOff G ({C, D} : Set G.edgeSet) colour final := by
    intro e he
    have hne : e ≠ C ∧ e ≠ D := by simpa using he
    exact (hfinalOff e hne.1 hne.2).symm
  have oldAll (q : V)
      (hcloseD : ∃ x, x ∈ (D : Sym2 V) ∧ (q = x ∨ G.Adj q x))
      (hall : ∀ a : Fin 4, VertexSeesInduced G final q a) :
      ∀ a : Fin 4, VertexSeesInduced G colour q a := by
    intro a
    by_cases hak : a = k
    · subst a
      obtain ⟨x, hxD, hqx⟩ := hcloseD
      exact (vertexSeesInduced_iff G colour q k).mpr
        ⟨D, hD', x, hxD, hqx⟩
    · obtain ⟨e, he, x, hxe, hqx⟩ :=
        (vertexSeesInduced_iff G final q a).mp (hall a)
      have heC : e ≠ C := by
        intro hEq
        subst e
        have hEqColour : some k = some a := hfinalC.symm.trans he
        exact hak (Option.some.inj hEqColour).symm
      have heD : e ≠ D := by
        intro hEq
        subst e
        have hfalse : none = some a := hfinalD.symm.trans he
        simp at hfalse
      exact (vertexSeesInduced_iff G colour q a).mpr
        ⟨e, by simpa [hfinalOff e heC heD] using he, x, hxe, hqx⟩
  change ConditionTwo G final
  apply hold.of_agreeOff G hagree
  intro q hq haffect _hmatch hall
  have hqcase : q = w₁ ∨ q = w₂ ∨ G.Adj q s := by
    exact twoVertex_paletteAffectedBy_twoThreadTail_cases G g hq
      (by simpa [C, D, Sym2.eq_swap] using haffect)
  by_cases hqw₁ : q = w₁
  · subst q
    apply hold w₁ g.first_two
    · exact (vertexSeesMatching_iff G colour w₁).mpr
        ⟨C, hC', by simp [C]⟩
    · apply oldAll w₁
      · exact ⟨w₂, by simp [D], Or.inr g.middle_adj⟩
      · exact hall
  by_cases hqw₂ : q = w₂
  · subst q
    apply hold w₂ g.second_two
    · exact (vertexSeesMatching_iff G colour w₂).mpr
        ⟨C, hC', by simp [C]⟩
    · apply oldAll w₂
      · exact ⟨w₂, by simp [D], Or.inl rfl⟩
      · exact hall
  have hqs : G.Adj q s := hqcase.elim
    (fun hEq ↦ False.elim (hqw₁ hEq))
    (fun hrest ↦ hrest.elim
      (fun hEq ↦ False.elim (hqw₂ hEq)) id)
  let E : G.edgeSet := ⟨s(q, s), hqs⟩
  have hED : E ≠ D := by
    intro hEq
    have hw₂E : w₂ ∈ (E : Sym2 V) := by rw [hEq]; simp [D]
    have hwcase : w₂ = q ∨ w₂ = s := by simpa [E] using hw₂E
    rcases hwcase with hwq | hws
    · exact hqw₂ hwq.symm
    · exact (isThreeVertex_ne_isTwoVertex G g.end_three g.second_two) hws.symm
  obtain ⟨a, hEa⟩ := hfar E ⟨by simp [E], hED⟩
  obtain ⟨M, hM, y, hyE, hyM⟩ := hsat E (by
    intro hnone
    have hfalse : some a = none := hEa.symm.trans hnone
    simp at hfalse)
  have hycase : y = q ∨ y = s := by simpa [E] using hyE
  have hyq : y = q := by
    rcases hycase with hyq | hys
    · exact hyq
    · have hMD : M ≠ D := by
        intro hEq
        subst M
        have hfalse : some k = none := hD'.symm.trans hM
        simp at hfalse
      obtain ⟨b, hMb⟩ := hfar M
        ⟨by simpa [hys] using hyM, hMD⟩
      have hfalse : none = some b := hM.symm.trans hMb
      simp at hfalse
  apply hold q hq
  · exact (vertexSeesMatching_iff G colour q).mpr
      ⟨M, hM, by simpa [hyq] using hyM⟩
  · apply oldAll q
    · exact ⟨s, by simp [D], Or.inr hqs⟩
    · exact hall

/-- Condition 3 survives the terminal shift.  The internal changed edge
cannot be external at a certified 2-thread endpoint.  If the terminal edge
is external there, the new premise that all external edges are induced is
immediately contradicted by its new matching colour. -/
theorem longPair_conditionThree_shift_twoThreadTail_twoTwo
    {u w₁ w₂ s : V}
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (k : Fin 4) :
    ConditionThree G
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none) := by
  let C : G.edgeSet := ⟨s(w₁, w₂), g.middle_adj⟩
  let D : G.edgeSet := ⟨s(w₂, s), g.last_adj⟩
  let final : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour C (some k)) D none
  have hfinalD : final D = none := by simp [final]
  have hagree : ColoringsAgreeOff G ({C, D} : Set G.edgeSet) colour final := by
    intro e he
    have hne : e ≠ C ∧ e ≠ D := by simpa using he
    simp [final, hne.1, hne.2]
  change ConditionThree G final
  apply hold.of_agreeOff G hagree
  intro a b p hp haffect hleft hright
  rcases haffect with ⟨e, heS, hext⟩ | ⟨e, heS, hext⟩
  · have hecase : e = C ∨ e = D := by simpa using heS
    rcases hecase with rfl | rfl
    · have hacase : a = w₁ ∨ a = w₂ := by simpa [C] using hext.1
      exact False.elim (hacase.elim
        (isThreeVertex_ne_isTwoVertex G hp.start_three g.first_two)
        (isThreeVertex_ne_isTwoVertex G hp.start_three g.second_two))
    · obtain ⟨c, hc⟩ := hleft D hext
      rw [hfinalD] at hc
      simp at hc
  · have hecase : e = C ∨ e = D := by simpa using heS
    rcases hecase with rfl | rfl
    · have hbcase : b = w₁ ∨ b = w₂ := by simpa [C] using hext.1
      exact False.elim (hbcase.elim
        (isThreeVertex_ne_isTwoVertex G hp.end_three g.first_two)
        (isThreeVertex_ne_isTwoVertex G hp.end_three g.second_two))
    · obtain ⟨c, hc⟩ := hright D hext
      rw [hfinalD] at hc
      simp at hc

/-- Complete prepared-gap preservation for the terminal shift used in the
last no-`(3,2,2)` branch. -/
theorem longPair_prepared_shift_twoThreadTail_twoTwo
    {u v₁ v₂ v₃ z w₁ w₂ s : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hD : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) = some k)
    (hCD : (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hfar : ExternalEdgesInduced G colour s
      (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet)) :
    PreparedThreeThreadGap G h
      (recolor G
        (recolor G colour
          (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) (some k))
        (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) none) := by
  exact ⟨
    longPair_validOn_shift_twoThreadTail_twoTwo G h g colour hprepared.1 k
      hP hC hD hCD hDD hk hfar,
    longPair_oneSaturated_shift_twoThreadTail_twoTwo G h g colour
      hprepared.2.1 k hP hD,
    longPair_conditionTwo_shift_twoThreadTail_twoTwo G g colour
      hprepared.2.2.1 hprepared.2.1 k hC hD hfar,
    longPair_conditionThree_shift_twoThreadTail_twoTwo G g colour
      hprepared.2.2.2 k⟩

/-! ## Closing the two fresh-colour branches -/

/-- If recolouring the first edge of one 2-thread with a complementary
colour does not complete a full palette at its second internal vertex,
the prepared recolouring and the generic crossed gap fill give a good
four-colouring. -/
theorem longPair_hasGoodFour_of_twoTwo_fresh_not_full
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ s x₁ x₂ t : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : TwoThreadCoreData G u w₁ w₂ s)
    (r : TwoThreadCoreData G u x₁ x₂ t)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j k l : Fin 4)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hli : l ≠ i) (hlj : l ≠ j) (hkl : k ≠ l)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hC : colour (⟨s(w₁, w₂), g.middle_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.middle_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDk : colour (⟨s(w₂, s), g.last_adj⟩ : G.edgeSet) ≠ some k)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzQ : z ∉ (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet).1)
    (hnotfull : ¬ ∀ a : Fin 4, VertexSeesInduced G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) w₂ a) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let fresh : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hvw
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hvx
  have hQT : Q ≠ T := by
    simpa [Q, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      g.first_adj r.first_adj hwx
  have hLold : ExternalInducedColors G colour u P = {i, j} := by
    simpa [P, Q, T] using
      longPair_externalPalette_eq_pair_twoTwoArms G h g r hvw hvx hwx
        colour i j hP hQ hT
  have hkOld : k ∉ ExternalInducedColors G colour u P := by
    rw [hLold]
    simpa [hki, hkj]
  have hpreparedFresh : PreparedThreeThreadGap G h fresh := by
    exact longPair_prepared_recolor_forkFirst_fresh_twoTwo_of_not_full
      G hsub h g r hvw hvx hwx colour hprepared i k hP hQ hC hS hA hB
        (by simpa [P] using hkOld) hDk hQD
        (by simpa [fresh, Q] using hnotfull)
  have hQD' : Q ∈ Dset := by simpa [Dset, Q] using hQD
  have hAD : A ∉ Dset := by
    simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
  have hAQ : A ≠ Q := fun heq ↦ hAD (heq ▸ hQD')
  have hBQ : B ≠ Q := fun heq ↦ hBD (heq ▸ hQD')
  have hRQ : R ≠ Q := by
    intro heq
    apply hzQ
    have hzR : z ∈ (R : Sym2 V) := by simp [R]
    rw [heq] at hzR
    exact hzR
  have hfreshP : fresh P = none := by simp [fresh, hPQ, P, hP]
  have hfreshR : fresh R = none := by simp [fresh, hRQ, R, hR]
  have hfreshA : fresh A = none := by simp [fresh, hAQ, A, hA]
  have hfreshB : fresh B = none := by simp [fresh, hBQ, B, hB]
  have hfreshQ : fresh Q = some k := by simp [fresh]
  have hfreshT : fresh T = some j := by simp [fresh, hQT.symm, T, hT]
  have hLfresh : ExternalInducedColors G fresh u P = {k, j} := by
    simpa [P, Q, T] using
      longPair_externalPalette_eq_pair_twoTwoArms G h g r hvw hvx hwx
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
  apply longPair_hasGoodFour_of_prepared_cross_fill G hsub h fresh
    hpreparedFresh i k l hfreshA hfreshB hfreshP hfreshR
  · rw [hLfresh]
    simp [hki.symm, hij]
  · rw [hRfresh]
    simp [hki, hkj]
  · rw [hRfresh]
    simp
  · rw [hLfresh]
    simp
  · rw [hLfresh]
    simp [hli, hlj, hkl.symm]
  · rw [hRfresh]
    simp [hli, hlj, hkl.symm]

/-- Distinct 2-threads leaving the same vertex have distinct middle edges
under the ambient girth hypothesis.  The swapped-edge alternative would
close the first two steps of one thread with the first step of the other. -/
theorem twoThread_middleEdges_ne_of_distinct_first_girth
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u s t : V} {q : G.Walk u s} {r : G.Walk u t}
    (hq : IsKThread G q 2) (hr : IsKThread G r 2)
    (hqr : q.getVert 1 ≠ r.getVert 1) :
    (⟨s(q.getVert 1, q.getVert 2),
      (hq.twoThreadCoreData G).middle_adj⟩ : G.edgeSet) ≠
      (⟨s(r.getVert 1, r.getVert 2),
        (hr.twoThreadCoreData G).middle_adj⟩ : G.edgeSet) := by
  intro hEq
  have hval : s(q.getVert 1, q.getVert 2) =
      s(r.getVert 1, r.getVert 2) := congrArg Subtype.val hEq
  simp only [Sym2.eq_iff] at hval
  rcases hval with hsame | hswap
  · exact hqr hsame.1
  · let q₂ : G.Walk u (q.getVert 2) := q.take 2
    have hq₂path : q₂.IsPath := hq.1.take 2
    have hqLen : q.length = 3 := by simpa using hq.length
    have hnot : ¬ G.Adj (q.getVert 2) u :=
      longPair_not_adj_endpoints_of_short_path G hgirth hq₂path
        (by simp [q₂, hqLen]) (by simp [q₂, hqLen])
    apply hnot
    simpa [hswap.2] using hr.first_step_adj.symm

/-- The final local hard case for a `(3,2,2)` fork.  Two complementary
colours are tried on the first edge of one 2-thread.  At most one can
complete the forbidden full palette.  If the only colour available there
is already on the terminal edge, its full-palette normal form permits the
terminal shift, after which the alternate selected-edge swap closes the
gap. -/
theorem longPair_hasGoodFour_of_twoThread_middles_matching_twoTwo
    (hgirth : (16 : ℕ∞) ≤ G.egirth) (hsub : IsSubcubic G)
    {u z s t : V} {p : G.Walk u z} {q : G.Walk u s} {r : G.Walk u t}
    (hp : IsKThread G p 3) (hq : IsKThread G q 2)
    (hr : IsKThread G r 2)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G (hp.threeThreadCore G) colour)
    (i j : Fin 4)
    (hP : colour (threadFirstEdge G p hp) = none)
    (hR : colour (threadLastEdge G p hp) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (threadFirstEdge G r hr) = some j)
    (hC : colour
      (⟨s(q.getVert 1, q.getVert 2),
        (hq.twoThreadCoreData G).middle_adj⟩ : G.edgeSet) = none)
    (hS : colour
      (⟨s(r.getVert 1, r.getVert 2),
        (hr.twoThreadCoreData G).middle_adj⟩ : G.edgeSet) = none)
    (hA : colour
      (⟨s(p.getVert 1, p.getVert 2),
        (hp.threeThreadCore G).left_adj⟩ : G.edgeSet) = none)
    (hB : colour
      (⟨s(p.getVert 3, p.getVert 2),
        (hp.threeThreadCore G).right_adj.symm⟩ : G.edgeSet) = none)
    (hpal : ExternalInducedColors G colour u (threadFirstEdge G p hp) =
      ExternalInducedColors G colour z (threadLastEdge G p hp)) :
    HasGoodFour G := by
  classical
  let h := hp.threeThreadCore G
  let g := hq.twoThreadCoreData G
  let rr := hr.twoThreadCoreData G
  let Dset : Set G.edgeSet :=
    RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
  let P : G.edgeSet := threadFirstEdge G p hp
  let R : G.edgeSet := threadLastEdge G p hp
  let Q : G.edgeSet := threadFirstEdge G q hq
  let C : G.edgeSet := ⟨s(q.getVert 1, q.getVert 2), g.middle_adj⟩
  let D : G.edgeSet := threadLastEdge G q hq
  let T : G.edgeSet := threadFirstEdge G r hr
  let S : G.edgeSet := ⟨s(r.getVert 1, r.getVert 2), rr.middle_adj⟩
  let U : G.edgeSet := threadLastEdge G r hr
  let A : G.edgeSet := ⟨s(p.getVert 1, p.getVert 2), h.left_adj⟩
  let B : G.edgeSet := ⟨s(p.getVert 3, p.getVert 2), h.right_adj.symm⟩
  have hpLen : p.length = 4 := by simpa using hp.length
  have hqLen : q.length = 3 := by simpa using hq.length
  have hrLen : r.length = 3 := by simpa using hr.length
  have hpGetNe (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) (hab : a ≠ b) :
      p.getVert a ≠ p.getVert b := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using ha)
      (show b ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using hb) heq
    exact hab hinj
  have hqGetNe (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (hab : a ≠ b) :
      q.getVert a ≠ q.getVert b := by
    intro heq
    have hinj := hq.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ q.length} by simpa [hqLen] using ha)
      (show b ∈ {n : ℕ | n ≤ q.length} by simpa [hqLen] using hb) heq
    exact hab hinj
  have hrGetNe (a b : ℕ) (ha : a ≤ 3) (hb : b ≤ 3) (hab : a ≠ b) :
      r.getVert a ≠ r.getVert b := by
    intro heq
    have hinj := hr.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ r.length} by simpa [hrLen] using ha)
      (show b ∈ {n : ℕ | n ≤ r.length} by simpa [hrLen] using hb) heq
    exact hab hinj
  have hpEnd : p.getVert 4 = z := by
    rw [← hpLen]
    exact p.getVert_length
  have hqEnd : q.getVert 3 = s := by
    rw [← hqLen]
    exact q.getVert_length
  have hrEnd : r.getVert 3 = t := by
    rw [← hrLen]
    exact r.getVert_length
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = u ∨ p.getVert 2 = p.getVert 1 := by
      simpa [P, threadFirstEdge] using hmem
    exact hcase.elim
      (fun he ↦ hpGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using he))
      (hpGetNe 2 1 (by omega) (by omega) (by omega))
  have huFar := twoThread_vertex_far_from_threeThread_middle G hq h
    q.start_mem_support
  have hQD : Q ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      huFar.1 huFar.2 Q (by simp [Q, threadFirstEdge])
  have hTD : T ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      huFar.1 huFar.2 T (by simp [T, threadFirstEdge])
  have hCD : C ∈ Dset := by
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = q.getVert 1 ∨
        p.getVert 2 = q.getVert 2 := by simpa [C] using hmem
    rcases hcase with hcase | hcase
    · exact (twoThread_vertex_far_from_threeThread_middle G hq h
        (q.getVert_mem_support 1)).1 hcase.symm
    · exact (twoThread_vertex_far_from_threeThread_middle G hq h
        (q.getVert_mem_support 2)).1 hcase.symm
  have hDD : D ∈ Dset := by
    have hsFar := twoThread_vertex_far_from_threeThread_middle G hq h
      q.end_mem_support
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      hsFar.1 hsFar.2 D (by simp [D, threadLastEdge])
  have hretFar : ∀ f, IsExternalAt G s D f → f ∈ Dset := by
    intro f hf
    have hsFar := twoThread_vertex_far_from_threeThread_middle G hq h
      q.end_mem_support
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      hsFar.1 hsFar.2 f hf.1
  have hvalid : IsOneTwoColoringOn G Dset colour := by
    simpa [Dset, h] using hprepared.1
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hpq
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hr.first_step_adj hpr
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj
        hr.first_step_adj hqr
  have hij : i ≠ j := by
    intro hij
    subst j
    have hpqt := hvalid Q hQD T hTD hQT
    have hsep : InducedSeparated G Q T := by
      simpa [Q, T, hQ, hT] using hpqt
    exact hsep.1 u (by simp [Q, threadFirstEdge])
      (by simp [T, threadFirstEdge])
  have hCS : C ≠ S := by
    simpa [C, S, g, rr] using
      twoThread_middleEdges_ne_of_distinct_first_girth G hgirth hq hr hqr
  have hCP : C ≠ P := by
    intro heq
    have hdirect :
        (⟨s(q.getVert 1, q.getVert 2), g.middle_adj⟩ : G.edgeSet) =
          (⟨s(p.getVert 1, u), h.first_adj.symm⟩ : G.edgeSet) := by
      apply Subtype.ext
      have hval := congrArg Subtype.val heq
      simpa [C, P, threadFirstEdge, Sym2.eq_swap] using hval
    exact (longPair_twoTwoEdge_ne_edgeEndingAtThree G
      g.first_two g.second_two h.start_three g.middle_adj
      h.first_adj.symm) hdirect
  have hCR : C ≠ R :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.second_two
      h.end_three g.middle_adj h.last_adj
  have hCQ : C ≠ Q := by
    intro heq
    have hC' : colour C = none := by simpa [C] using hC
    have hQ' : colour Q = some i := by simpa [Q] using hQ
    have hfalse : none = some i :=
      hC'.symm.trans ((congrArg colour heq).trans hQ')
    simp at hfalse
  have hCT : C ≠ T := by
    intro heq
    have hC' : colour C = none := by simpa [C] using hC
    have hT' : colour T = some j := by simpa [T] using hT
    have hfalse : none = some j :=
      hC'.symm.trans ((congrArg colour heq).trans hT')
    simp at hfalse
  have hDQ : D ≠ Q := by
    intro heq
    apply twoThreadCore_firstEdge_ne_lastEdge G g
    simpa [D, Q, g, threadFirstEdge, threadLastEdge, Sym2.eq_swap] using heq.symm
  have hDP : D ≠ P := by
    intro heq
    have hval : s(q.getVert 2, s) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hqGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hqGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa [hqEnd] using hval.2)
  have hUP : U ≠ P := by
    intro heq
    have hval : s(r.getVert 2, t) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hrGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hrGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa [hrEnd] using hval.2)
  have hUQ : U ≠ Q := by
    intro heq
    have hval : s(r.getVert 2, t) = s(u, q.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hrGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hrGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa [hrEnd] using hval.2)
  have hRP : R ≠ P := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, p.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hpGetNe 3 1 (by omega) (by omega) (by omega) hval.1
  have hRQ : R ≠ Q := by
    intro heq
    have hval : s(p.getVert 3, z) = s(u, q.getVert 1) :=
      congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact hpGetNe 3 0 (by omega) (by omega) (by omega)
        (by simpa using hval.1)
    · exact hpGetNe 4 0 (by omega) (by omega) (by omega)
        (by simpa [hpEnd] using hval.2)
  have hzQ : z ∉ (Q : Sym2 V) := by
    intro hz
    have hzcase : z = u ∨ z = q.getVert 1 := by
      simpa [Q, threadFirstEdge] using hz
    rcases hzcase with hzu | hzq
    · exact (IsKThread.endpoints_ne G hp) hzu.symm
    · exact (isThreeVertex_ne_isTwoVertex G h.end_three g.first_two) hzq
  have hAD : A ∉ Dset := by
    simpa [Dset, A, h] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [Dset, B, h] using right_chain_edge_not_retained G h.right_adj
  have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by simp [hij]
  obtain ⟨k, hkPair, hDk⟩ :=
    longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
      hpairCard (colour D)
  have hkData : k ≠ i ∧ k ≠ j := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hkPair
  obtain ⟨l, hlPair, hklOpt⟩ :=
    longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
      hpairCard (some k)
  have hlData : l ≠ i ∧ l ≠ j := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hlPair
  have hkl : k ≠ l := by simpa using hklOpt
  let freshK : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  by_cases hfullK : ∀ a : Fin 4, VertexSeesInduced G freshK (q.getVert 2) a
  · by_cases hDl : colour D ≠ some l
    · have hmatchK : VertexSeesMatching G freshK (q.getVert 2) := by
        apply (vertexSeesMatching_iff G freshK (q.getVert 2)).mpr
        exact ⟨C, by simp [freshK, hCQ, C, hC], by simp [C]⟩
      let freshL : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some l)
      have hmatchL : VertexSeesMatching G freshL (q.getVert 2) := by
        apply (vertexSeesMatching_iff G freshL (q.getVert 2)).mpr
        exact ⟨C, by simp [freshL, hCQ, C, hC], by simp [C]⟩
      have hnotfullL : ¬ ∀ a : Fin 4,
          VertexSeesInduced G freshL (q.getVert 2) a := by
        intro hfullL
        let Qrev : G.edgeSet := ⟨s(q.getVert 1, u), hq.first_step_adj.symm⟩
        have hQrev : Qrev = Q := by
          apply Subtype.ext
          simp [Qrev, Q, threadFirstEdge, Sym2.eq_swap]
        exact full_palette_leaf_colour_unique_at_two_four G
          hq.first_step_adj.symm colour hprepared.2.2.1 g.second_two hkl
          (by simpa only [Qrev, hQrev, freshK] using hmatchK)
          (by simpa only [Qrev, hQrev, freshK] using hfullK)
          (by simpa only [Qrev, hQrev, freshL] using hmatchL)
          (by simpa only [Qrev, hQrev, freshL] using hfullL)
      exact longPair_hasGoodFour_of_twoTwo_fresh_not_full G hsub h g rr
        hpq hpr hqr colour hprepared i j l k hij hlData.1 hlData.2
        hkData.1 hkData.2 hkl.symm
        (by simpa [P, h, threadFirstEdge, Sym2.eq_swap] using hP)
        (by simpa [R, h, threadLastEdge] using hR)
        (by simpa [Q, g, threadFirstEdge, Sym2.eq_swap] using hQ)
        (by simpa [T, rr, threadFirstEdge, Sym2.eq_swap] using hT)
        (by simpa [C, g] using hC) (by simpa [S, rr] using hS)
        (by simpa [A, h] using hA) (by simpa [B, h] using hB)
        (by
          let Qrev : G.edgeSet := ⟨s(q.getVert 1, u), g.first_adj.symm⟩
          have hQrev : Qrev = Q := by
            apply Subtype.ext
            simp [Qrev, Q, threadFirstEdge, Sym2.eq_swap]
          simpa only [Qrev, hQrev, Dset] using hQD)
        (by simpa [D, g, threadLastEdge, Sym2.eq_swap] using hDl)
        (by simpa [P, R, h, threadFirstEdge, threadLastEdge,
          Sym2.eq_swap] using hpal)
        (by simpa [Q, g, threadFirstEdge, Sym2.eq_swap] using hzQ)
        (by simpa [freshL, Q, g, threadFirstEdge, Sym2.eq_swap] using hnotfullL)
    · have hD : colour D = some l := by simpa using Classical.not_not.mp hDl
      have hfar := full_second_palette_after_fresh_far_normal_form_twoTwo
        G hsub g Dset colour hvalid hprepared.2.2.1 i j l k hij
          hlData.1.symm hkData.1.symm hlData.2.symm hkData.2.symm hkl.symm
          (by simpa [Q, g, threadFirstEdge, Sym2.eq_swap] using hQ)
          (by simpa [C, g] using hC)
          (by simpa [D, g, threadLastEdge, Sym2.eq_swap] using hD)
          (by simpa [D, Dset, g, threadLastEdge, Sym2.eq_swap] using hDD)
          (by
            intro f hf
            exact hretFar f (by simpa [D, g, threadLastEdge,
              Sym2.eq_swap] using hf))
          (by simpa [freshK, Q, g, threadFirstEdge, Sym2.eq_swap] using hfullK)
      let inner : G.edgeSet → OneTwoColor 4 :=
        recolor G (recolor G colour C (some l)) D none
      have hpreparedInner : PreparedThreeThreadGap G h inner := by
        exact longPair_prepared_shift_twoThreadTail_twoTwo G h g colour
          (by simpa [h] using hprepared) l
          (by simpa [P, h, threadFirstEdge, Sym2.eq_swap] using hP)
          (by simpa [C, g] using hC)
          (by simpa [D, g, threadLastEdge, Sym2.eq_swap] using hD)
          (by simpa [C, Dset, g] using hCD)
          (by simpa [D, Dset, g, threadLastEdge, Sym2.eq_swap] using hDD)
          (by
            have hcenter : ExternalInducedColors G colour u P = {i, j} := by
              simpa [P, Q, T, h, g, rr, threadFirstEdge, Sym2.eq_swap] using
                longPair_externalPalette_eq_pair_twoTwoArms G h g rr hpq hpr hqr
                  colour i j
                  (by simpa [P, h, threadFirstEdge, Sym2.eq_swap] using hP)
                  (by simpa [Q, g, threadFirstEdge, Sym2.eq_swap] using hQ)
                  (by simpa [T, rr, threadFirstEdge, Sym2.eq_swap] using hT)
            have hcenter' : ExternalInducedColors G colour u
                (⟨s(p.getVert 1, u), h.first_adj.symm⟩ : G.edgeSet) =
                {i, j} := by
              simpa [P, h, threadFirstEdge, Sym2.eq_swap] using hcenter
            rw [hcenter']
            exact hlPair)
          (by simpa [D, g, threadLastEdge, Sym2.eq_swap] using hfar.1)
      have hDR : D ≠ R := by
        intro heq
        have hD' : colour D = some l := by simpa [D] using hD
        have hR' : colour R = none := by simpa [R] using hR
        have hfalse : some l = none :=
          hD'.symm.trans ((congrArg colour heq).trans hR')
        simp at hfalse
      have hDT : D ≠ T := by
        intro heq
        have hD' : colour D = some l := by simpa [D] using hD
        have hT' : colour T = some j := by simpa [T] using hT
        have hfalse : some l = some j :=
          hD'.symm.trans ((congrArg colour heq).trans hT')
        exact hlData.2 (Option.some.inj hfalse)
      have hDS : D ≠ S := by
        intro heq
        have hD' : colour D = some l := by simpa [D] using hD
        have hS' : colour S = none := by simpa [S] using hS
        have hfalse : some l = none :=
          hD'.symm.trans ((congrArg colour heq).trans hS')
        simp at hfalse
      have hAC : A ≠ C := fun heq ↦ hAD (heq ▸ hCD)
      have hADedge : A ≠ D := fun heq ↦ hAD (heq ▸ hDD)
      have hBC : B ≠ C := fun heq ↦ hBD (heq ▸ hCD)
      have hBDedge : B ≠ D := fun heq ↦ hBD (heq ▸ hDD)
      have hinnerP : inner P = none := by
        rw [show inner P = colour P by
          simp [inner, hCP.symm, hDP.symm]]
        simpa [P] using hP
      have hinnerR : inner R = none := by
        rw [show inner R = colour R by
          simp [inner, hCR.symm, hDR.symm]]
        simpa [R] using hR
      have hinnerQ : inner Q = some i := by
        rw [show inner Q = colour Q by
          simp [inner, hCQ.symm, hDQ.symm]]
        simpa [Q] using hQ
      have hinnerT : inner T = some j := by
        rw [show inner T = colour T by
          simp [inner, hCT.symm, hDT.symm]]
        simpa [T] using hT
      have hinnerS : inner S = none := by
        rw [show inner S = colour S by
          simp [inner, hCS.symm, hDS.symm]]
        simpa [S] using hS
      have hinnerC : inner C = some l := by
        have hCDne : C ≠ D := by
          simpa [C, D, g, threadLastEdge, Sym2.eq_swap] using
            chain_edges_ne G g.middle_adj g.last_adj g.first_ne_end
        simp [inner, hCDne]
      have hinnerD : inner D = none := by simp [inner]
      have hinnerA : inner A = none := by simp [inner, hAC, hADedge, A, hA]
      have hinnerB : inner B = none := by simp [inner, hBC, hBDedge, B, hB]
      let critical : G.edgeSet → OneTwoColor 4 :=
        recolor G (recolor G inner P (some i)) Q none
      have hcriticalQ : critical Q = none := by simp [critical]
      have hcriticalP : critical P = some i := by simp [critical, hPQ]
      have hcriticalT : critical T = some j := by
        simp [critical, hPT.symm, hQT.symm, hinnerT]
      have hcriticalStart :
          ExternalEdgesInduced G critical u Q ∧
            ExternalInducedColors G critical u Q = {i, j} := by
        simpa [P, Q, T, critical, h, g, rr, threadFirstEdge, Sym2.eq_swap] using
          longPair_twoThreadFirst_external_data_twoTwo G h rr q hq hpr hpq
            hqr.symm critical i j
              (by simpa [Q, g, threadFirstEdge, Sym2.eq_swap] using hcriticalQ)
              (by simpa [P, h, threadFirstEdge, Sym2.eq_swap] using hcriticalP)
              (by simpa [T, rr, threadFirstEdge, Sym2.eq_swap] using hcriticalT)
      have hmissFar : ∀ e, IsExternalAt G s D e →
          e ∉ ({C, D, P, Q} : Set G.edgeSet) := by
        intro e hext heS
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heS
        rcases heS with rfl | rfl | rfl | rfl
        · have hscase : s = q.getVert 1 ∨ s = q.getVert 2 := by
            simpa [C] using hext.1
          exact hscase.elim
            (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two)
            (isThreeVertex_ne_isTwoVertex G g.end_three g.second_two)
        · exact hext.2 rfl
        · have hscase : s = u ∨ s = p.getVert 1 := by
            simpa [P, threadFirstEdge] using hext.1
          rcases hscase with hsu | hsp
          · exact (IsKThread.endpoints_ne G hq) hsu.symm
          · exact (isThreeVertex_ne_isTwoVertex G g.end_three h.first_two) hsp
        · have hscase : s = u ∨ s = q.getVert 1 := by
            simpa [Q, threadFirstEdge] using hext.1
          rcases hscase with hsu | hsw
          · exact (IsKThread.endpoints_ne G hq) hsu.symm
          · exact (isThreeVertex_ne_isTwoVertex G g.end_three g.first_two) hsw
      have hagreeCritical : ColoringsAgreeOff G
          ({C, D, P, Q} : Set G.edgeSet) colour critical := by
        intro e he
        have hne : e ≠ C ∧ e ≠ D ∧ e ≠ P ∧ e ≠ Q := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using he
        simp [critical, inner, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2]
      have hcriticalFarEdges : ExternalEdgesInduced G critical s D :=
        externalEdgesInduced_of_agreeOff G hagreeCritical hmissFar hfar.1
      have hcriticalFarPalette : ExternalInducedColors G critical s D = {i, j} := by
        have heq := externalInducedColors_eq_of_agreeOff G hagreeCritical hmissFar
        rw [← heq]
        exact hfar.2
      have hcriticalData :
          ExternalEdgesInduced G critical u Q ∧
            ExternalEdgesInduced G critical s D ∧
            ExternalInducedColors G critical u Q =
              ExternalInducedColors G critical s D := by
        exact ⟨hcriticalStart.1, hcriticalFarEdges,
          hcriticalStart.2.trans hcriticalFarPalette.symm⟩
      exact longPair_hasGoodFour_of_twoThread_middle_induced_alt_twoTwo
        G hsub h rr q hq hpr hpq hqr.symm inner hpreparedInner k j i
          (by simpa [P, h, threadFirstEdge, Sym2.eq_swap] using hinnerP)
          (by simpa [R, h, threadLastEdge] using hinnerR)
          (by simpa [T, rr, threadFirstEdge, Sym2.eq_swap] using hinnerT)
          (by simpa [Q, g, threadFirstEdge, Sym2.eq_swap] using hinnerQ)
          (by simpa [S, rr] using (show inner S ≠ some k by
            rw [hinnerS]; simp))
          (by simpa [C, g] using (show inner C ≠ none by
            simp [hinnerC]))
          (by simpa [C, g] using (show inner C ≠ some k by
            rw [hinnerC]; simpa using hkl.symm))
          (by simpa [A, h] using hinnerA) (by simpa [B, h] using hinnerB)
          (Or.inl (by simpa [S, rr] using hinnerS))
          (by simpa [P, h, Dset, threadFirstEdge, Sym2.eq_swap] using hPD)
          (by
            let Qrev : G.edgeSet := ⟨s(q.getVert 1, u), g.first_adj.symm⟩
            have hQrev : Qrev = Q := by
              apply Subtype.ext
              simp [Qrev, Q, threadFirstEdge, Sym2.eq_swap]
            simpa only [Qrev, hQrev, Dset] using hQD)
          (by simpa [D, P, g, h, threadFirstEdge, threadLastEdge,
            Sym2.eq_swap] using hDP)
          (by simpa [U, P, rr, h, threadFirstEdge, threadLastEdge,
            Sym2.eq_swap] using hUP)
          (by simpa [U, Q, rr, g, threadFirstEdge, threadLastEdge,
            Sym2.eq_swap] using hUQ)
          (by simpa [R, P, h, threadFirstEdge, threadLastEdge,
            Sym2.eq_swap] using hRP)
          (by simpa [R, Q, h, g, threadFirstEdge, threadLastEdge,
            Sym2.eq_swap] using hRQ)
          hkData.2 hkData.1
          (by simpa [P, Q, D, critical, h, g, threadFirstEdge,
            threadLastEdge, Sym2.eq_swap] using hcriticalData)
  · exact longPair_hasGoodFour_of_twoTwo_fresh_not_full G hsub h g rr
      hpq hpr hqr colour hprepared i j k l hij hkData.1 hkData.2
      hlData.1 hlData.2 hkl
      (by simpa [P, h, threadFirstEdge, Sym2.eq_swap] using hP)
      (by simpa [R, h, threadLastEdge] using hR)
      (by simpa [Q, g, threadFirstEdge, Sym2.eq_swap] using hQ)
      (by simpa [T, rr, threadFirstEdge, Sym2.eq_swap] using hT)
      (by simpa [C, g] using hC) (by simpa [S, rr] using hS)
      (by simpa [A, h] using hA) (by simpa [B, h] using hB)
      (by
        let Qrev : G.edgeSet := ⟨s(q.getVert 1, u), g.first_adj.symm⟩
        have hQrev : Qrev = Q := by
          apply Subtype.ext
          simp [Qrev, Q, threadFirstEdge, Sym2.eq_swap]
        simpa only [Qrev, hQrev, Dset] using hQD)
      (by simpa [D, g, threadLastEdge, Sym2.eq_swap] using hDk)
      (by simpa [P, R, h, threadFirstEdge, threadLastEdge,
        Sym2.eq_swap] using hpal)
      (by simpa [Q, g, threadFirstEdge, Sym2.eq_swap] using hzQ)
      (by simpa [freshK, Q, g, threadFirstEdge, Sym2.eq_swap] using hfullK)

/-! ## The local `(3,2,2)` exclusion -/

/- A good colouring after deleting the middle vertex of the selected
3-thread rules out a `(3,2,2)` fork in a bad graph. -/
set_option maxHeartbeats 3000000 in
theorem longPair_no_threeTwoTwo_of_smaller_good
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z s t : V} {p : G.Walk u z} {q : G.Walk u s} {r : G.Walk u t}
    (hp : IsKThread G p 3) (hq : IsKThread G q 2)
    (hr : IsKThread G r 2)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) : False := by
  classical
  let h := hp.threeThreadCore G
  let base : G.edgeSet → OneTwoColor 4 :=
    transportColoringToSupergraph (G.deleteIncidenceSet_le (p.getVert 2)) small
  let Dset : Set G.edgeSet :=
    RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
  let P : G.edgeSet := threadFirstEdge G p hp
  let R : G.edgeSet := threadLastEdge G p hp
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := threadFirstEdge G r hr
  let C : G.edgeSet :=
    ⟨s(q.getVert 1, q.getVert 2),
      (hq.twoThreadCoreData G).middle_adj⟩
  let S : G.edgeSet :=
    ⟨s(r.getVert 1, r.getVert 2),
      (hr.twoThreadCoreData G).middle_adj⟩
  let A : G.edgeSet :=
    ⟨s(p.getVert 1, p.getVert 2),
      (hp.threeThreadCore G).left_adj⟩
  let B : G.edgeSet :=
    ⟨s(p.getVert 3, p.getVert 2),
      (hp.threeThreadCore G).right_adj.symm⟩
  have hpLen : p.length = 4 := by simpa using hp.length
  have hpGetNe (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) (hab : a ≠ b) :
      p.getVert a ≠ p.getVert b := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show a ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using ha)
      (show b ∈ {n : ℕ | n ≤ p.length} by simpa [hpLen] using hb) heq
    exact hab hinj
  have hPD : P ∈ Dset := by
    change P ∈ RetainedEdges (G.deleteIncidenceSet (p.getVert 2)) G
    rw [mem_retained_deleteIncidenceSet_iff]
    intro hmem
    have hcase : p.getVert 2 = u ∨ p.getVert 2 = p.getVert 1 := by
      simpa [P, threadFirstEdge] using hmem
    exact hcase.elim
      (fun he ↦ hpGetNe 2 0 (by omega) (by omega) (by omega)
        (by simpa using he))
      (hpGetNe 2 1 (by omega) (by omega) (by omega))
  have huFarQ := twoThread_vertex_far_from_threeThread_middle G hq h
    q.start_mem_support
  have huFarR := twoThread_vertex_far_from_threeThread_middle G hr h
    r.start_mem_support
  have hQD : Q ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      huFarQ.1 huFarQ.2 Q (by simp [Q, threadFirstEdge])
  have hTD : T ∈ Dset := by
    exact longPair_incident_retained_deleteIncidence_of_not_adj G
      huFarR.1 huFarR.2 T (by simp [T, threadFirstEdge])
  have hPQ : P ≠ Q := by
    simpa [P, Q, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hq.first_step_adj hpq
  have hPT : P ≠ T := by
    simpa [P, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj
        hr.first_step_adj hpr
  have hQT : Q ≠ T := by
    simpa [Q, T, threadFirstEdge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G hq.first_step_adj
        hr.first_step_adj hqr
  obtain ⟨hP, hR, hpal⟩ :=
    longPair_threeThread_hard_normal_form_of_no_goodFour G hgirth h small
      hsmall hsub hbad
  have hprepared : PreparedThreeThreadGap G h base :=
    preparedThreeThreadGap_of_goodFour G hsub h small hsmall
  have hAD : A ∉ Dset := by
    simpa [h, A, Dset] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ Dset := by
    simpa [h, B, Dset, Sym2.eq_swap] using
      right_chain_edge_not_retained G h.right_adj
  have hA : base A = none := by
    have hAe : A.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [Dset, RetainedEdges] using hAD
    simp [base, transportColoringToSupergraph, hAe]
  have hB : base B = none := by
    have hBe : B.1 ∉ (G.deleteIncidenceSet (p.getVert 2)).edgeSet := by
      simpa [Dset, RetainedEdges] using hBD
    simp [base, transportColoringToSupergraph, hBe]
  have hC := longPair_twoThread_middle_matching_in_bad_graph_twoTwo
    G hgirth hp hr hq hpr hpq hqr.symm small hsmall hsub hbad
  have hS := longPair_twoThread_middle_matching_in_bad_graph_twoTwo
    G hgirth hp hq hr hpq hpr hqr small hsmall hsub hbad
  have hPval : base P = none := by
    simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP
  have hRval : base R = none := by
    simpa [h, base, R, threadLastEdge] using hR
  have hCval : base C = none := by simpa [base, C] using hC
  have hSval : base S = none := by simpa [base, S] using hS
  have hvalid : IsOneTwoColoringOn G Dset base := by
    simpa [Dset] using hprepared.1
  have hQne : base Q ≠ none := by
    intro hQnone
    have hcompat := hvalid P hPD Q hQD hPQ
    have hdisj : EndpointDisjoint G P Q := by
      simpa [hPval, hQnone] using hcompat
    exact hdisj u (by simp [P, threadFirstEdge])
      (by simp [Q, threadFirstEdge])
  have hTne : base T ≠ none := by
    intro hTnone
    have hcompat := hvalid P hPD T hTD hPT
    have hdisj : EndpointDisjoint G P T := by
      simpa [hPval, hTnone] using hcompat
    exact hdisj u (by simp [P, threadFirstEdge])
      (by simp [T, threadFirstEdge])
  cases hQval : base Q with
  | none => exact False.elim (hQne hQval)
  | some i =>
      cases hTval : base T with
      | none => exact False.elim (hTne hTval)
      | some j =>
          have hij : i ≠ j := by
            intro hij
            subst j
            have hcompat := hvalid Q hQD T hTD hQT
            have hsep : InducedSeparated G Q T := by
              simpa [hQval, hTval] using hcompat
            exact hsep.1 u (by simp [Q, threadFirstEdge])
              (by simp [T, threadFirstEdge])
          apply hbad
          exact longPair_hasGoodFour_of_twoThread_middles_matching_twoTwo
            G hgirth hsub hp hq hr hpq hpr hqr base hprepared i j
              (by simpa [P] using hPval)
              (by simpa [R] using hRval)
              (by simpa [Q] using hQval)
              (by simpa [T] using hTval)
              (by simpa [C] using hCval)
              (by simpa [S] using hSval)
              (by simpa [A] using hA)
              (by simpa [B] using hB)
              (by simpa [h, base, P, R, threadFirstEdge, threadLastEdge,
                Sym2.eq_swap] using hpal)

end Finite

end

end LeanCo.PackingEdgeColoring
