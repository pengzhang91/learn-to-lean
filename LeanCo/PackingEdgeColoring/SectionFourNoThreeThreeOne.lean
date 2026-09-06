import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeThree
import LeanCo.PackingEdgeColoring.SectionFourLongPreparedOuter

/-!
# The one-thread third-arm reduction for Section 4

This module treats the local core of the paper's `no331` configuration.
The selected and second arms are 3-threads; the third arm has one internal
degree-two vertex.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The ordered local data of a 1-thread `u-x₁-x₂`. -/
structure OneThreadCore (u x₁ x₂ : V) : Prop where
  start_three : IsThreeVertex G u
  first_two : IsTwoVertex G x₁
  end_three : IsThreeVertex G x₂
  first_adj : G.Adj u x₁
  last_adj : G.Adj x₁ x₂
  end_ne_start : x₂ ≠ u

/-- The two degree-two vertices at the start of an auxiliary arm.  The
`no331` recolouring only uses this prefix of its second 3-thread; exposing
that exact interface lets the same local argument serve the later
`no321` configuration, whose corresponding arm is only a 2-thread. -/
structure ForkTwoStepCore (u w₁ w₂ : V) : Prop where
  first_two : IsTwoVertex G w₁
  middle_two : IsTwoVertex G w₂
  first_adj : G.Adj u w₁
  left_adj : G.Adj w₁ w₂
  middle_ne_start : w₂ ≠ u

/-- Forget the unused tail of a 3-thread and retain its first two steps. -/
theorem ThreeThreadCore.forkTwoStep
    {u w₁ w₂ w₃ t : V} (g : ThreeThreadCore G u w₁ w₂ w₃ t) :
    ForkTwoStepCore G u w₁ w₂ :=
  ⟨g.first_two, g.middle_two, g.first_adj, g.left_adj, g.middle_ne_start⟩

/-- A certified 2-thread supplies exactly the same two-step auxiliary-arm
interface. -/
theorem IsKThread.forkTwoStepCore
    {u y : V} {p : G.Walk u y} (hp : IsKThread G p 2) :
    ForkTwoStepCore G u (p.getVert 1) (p.getVert 2) := by
  have hlen : p.length = 3 := by simpa using hp.length
  have hget : p.getVert 2 ≠ u := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show 2 ∈ {n : ℕ | n ≤ p.length} by simp [hlen])
      (show 0 ∈ {n : ℕ | n ≤ p.length} by simp)
      (by simpa using heq)
    omega
  exact ⟨
    IsKThread.internal_two G hp (by omega) (by omega),
    IsKThread.internal_two G hp (by omega) (by omega),
    hp.first_step_adj,
    p.adj_getVert_succ (i := 1) (by omega), hget⟩

/-- Extract the ordered three-vertex core from a certified 1-thread. -/
theorem IsKThread.oneThreadCore
    {u x₂ : V} {p : G.Walk u x₂} (hp : IsKThread G p 1) :
    OneThreadCore G u (p.getVert 1) x₂ := by
  have hlen : p.length = 2 := by simpa using hp.length
  have hend : p.getVert 2 = x₂ := by
    rw [← hlen]
    exact p.getVert_length
  have hne : x₂ ≠ u := by
    intro heq
    have hinj := hp.1.getVert_injOn
      (show 2 ∈ {n : ℕ | n ≤ p.length} by simp [hlen])
      (show 0 ∈ {n : ℕ | n ≤ p.length} by simp)
      (by simpa [hend] using heq)
    omega
  exact ⟨hp.start_three,
    IsKThread.internal_two G hp (by omega) (by omega),
    hp.end_three, hp.first_step_adj, by simpa [hend] using hp.last_step_adj,
    hne⟩

/-- At the degree-three centre, the external palette of the selected arm
is exactly the colours on the other long arm and the 1-thread arm. -/
theorem longPair_externalPalette_eq_pair_oneThreadThird
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
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
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hv₁w₁
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  ext a
  constructor
  · rintro ⟨f, ⟨huf, hfP⟩, hfa⟩
    obtain ⟨q, hfq⟩ := Sym2.mem_iff_exists.mp huf
    have huq : G.Adj u q := by
      have hadj := f.2
      rw [hfq] at hadj
      simpa using hadj
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hv₁w₁ hv₁x₁ hw₁x₁ huq with
      rfl | rfl | rfl
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

/-! ## Fresh recolouring of the selected outer edge -/

/-- A colour missing from the centre palette and from the sole continuation
of a 1-thread is available on the selected outer edge.  The other long arm
has a matching-coloured second edge, so it creates no further blocker. -/
theorem longPair_selectedFirst_fresh_available_oneThreadThird
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (Dset : Set G.edgeSet) (k m : Fin 4)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) = some m)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hkm : k ≠ m)
    (hretained : ∀ f : G.edgeSet, f ∈ Dset → v₂ ∉ (f : Sym2 V)) :
    ColorAvailableOn G Dset colour
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some k) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.last_adj⟩
  have hC' : colour C = none := by simpa [C] using hC
  have hS' : colour S = some m := by simpa [S] using hS
  have noAtU (f : G.edgeSet) (hfP : f ≠ P)
      (huf : u ∈ (f : Sym2 V)) (hfk : colour f = some k) : False := by
    exact hk ⟨f, ⟨huf, by simpa [P] using hfP⟩, hfk⟩
  have noAtV₁ (f : G.edgeSet) (hfD : f ∈ Dset) (hfP : f ≠ P)
      (hvf : v₁ ∈ (f : Sym2 V)) : False := by
    rcases edge_eq_left_or_right_of_incident_two G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start f hvf with hfA | hfP'
    · exact hretained f hfD (by rw [hfA]; simp)
    · exact hfP (Subtype.ext (by simpa [P] using hfP'))
  have noAtW₁ (f : G.edgeSet) (hfD : f ∈ Dset) (hfP : f ≠ P)
      (hwf : w₁ ∈ (f : Sym2 V)) (hfk : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.first_adj.symm g.left_adj g.middle_ne_start.symm f hwf with
      hfQ | hfC
    · have hfEq : f = Q :=
        Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfQ)
      exact noAtU f hfP (by simpa [hfEq, Q]) hfk
    · have hfEq : f = C := Subtype.ext (by simpa [C] using hfC)
      have hfalse : none = some k := hC'.symm.trans (by simpa [hfEq] using hfk)
      simp at hfalse
  have noAtX₁ (f : G.edgeSet) (hfP : f ≠ P)
      (hxf : x₁ ∈ (f : Sym2 V)) (hfk : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.first_adj.symm r.last_adj r.end_ne_start.symm f hxf with
      hfT | hfS
    · have hfEq : f = T :=
        Subtype.ext (by simpa [T, Sym2.eq_swap] using hfT)
      exact noAtU f hfP (by simpa [hfEq, T]) hfk
    · have hfEq : f = S := Subtype.ext (by simpa [S] using hfS)
      have hmk : m = k :=
        Option.some.inj (hS'.symm.trans (by simpa [hfEq] using hfk))
      exact hkm hmk.symm
  apply (colorAvailableOn_some_iff G Dset colour P k).mpr
  intro f hfD hfP hfk
  rw [inducedSeparated_iff_forall_endpoints]
  intro a ha b hbf
  have hacase : a = v₁ ∨ a = u := by simpa [P] using ha
  rcases hacase with hav₁ | hau
  · constructor
    · intro hab
      apply noAtV₁ f hfD hfP
      have : v₁ = b := hav₁.symm.trans hab
      simpa [this] using hbf
    · intro hab
      have hv₁b : G.Adj v₁ b := by simpa [hav₁] using hab
      have hbN : b ∈ G.neighborFinset v₁ :=
        (G.mem_neighborFinset v₁ b).mpr hv₁b
      rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start] at hbN
      have hbcase : b = v₂ ∨ b = u := by simpa using hbN
      rcases hbcase with hbv₂ | hbu
      · exact hretained f hfD (by simpa [hbv₂] using hbf)
      · exact noAtU f hfP (by simpa [hbu] using hbf) hfk
  · constructor
    · intro hab
      apply noAtU f hfP
      have : u = b := hau.symm.trans hab
      · simpa [this] using hbf
      · exact hfk
    · intro hab
      have hub : G.Adj u b := by simpa [hau] using hab
      rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
          g.first_adj r.first_adj hv₁w₁ hv₁x₁ hw₁x₁ hub with
        rfl | rfl | rfl
      · exact noAtV₁ f hfD hfP hbf
      · exact noAtW₁ f hfD hfP hbf hfk
      · exact noAtX₁ f hfP hbf hfk

/-- After the selected matching edge is recoloured induced, matching is
available on the first edge of the 1-thread: the old selected edge excludes
every other matching edge at the centre, while the 1-thread continuation is
induced. -/
theorem longPair_oneThreadFirst_matching_available_after_selectedFresh
    {u v₁ v₂ v₃ z x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : OneThreadCore G u x₁ x₂)
    (colour : G.edgeSet → OneTwoColor 4)
    (Dset : Set G.edgeSet)
    (hvalid : IsOneTwoColoringOn G Dset colour)
    (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) ≠ none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈ Dset)
    (hv₁x₁ : v₁ ≠ x₁) :
    ColorAvailableOn G Dset
      (recolor G colour
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some k))
      (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.last_adj⟩
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some k)
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  have hafterPP : afterP P = some k := by simp [afterP]
  have hS' : colour S ≠ none := by simpa [S] using hS
  apply (colorAvailableOn_none_iff G Dset afterP T).mpr
  intro f hfD hfT hfnone y hyT hyf
  have hycase : y = x₁ ∨ y = u := by simpa [T] using hyT
  have hfP : f ≠ P := by
    intro hEq
    subst f
    have hfalse : some k = none := hafterPP.symm.trans hfnone
    simp at hfalse
  have hfOld : colour f = none := by
    simpa [afterP, hfP] using hfnone
  rcases hycase with hyx₁ | hyu
  · have hx₁f : x₁ ∈ (f : Sym2 V) := by simpa [hyx₁] using hyf
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.first_adj.symm r.last_adj r.end_ne_start.symm f hx₁f with
      hfT' | hfS
    · exact hfT (Subtype.ext (by simpa [T, Sym2.eq_swap] using hfT'))
    · have hfEq : f = S := Subtype.ext (by simpa [S] using hfS)
      exact hS' (by simpa [hfEq] using hfOld)
  · have hcompat := hvalid P (by simpa [P] using hPD) f hfD hfP.symm
    have hdisj : EndpointDisjoint G P f := by
      simpa [P, hP, hfOld] using hcompat
    exact hdisj u (by simp [P]) (by simpa [hyu] using hyf)

/-- Saturation is preserved when matching moves from the selected outer
edge to the first edge of a distinct 1-thread. -/
theorem longPair_oneSaturated_selectedFresh_oneThreadFirstMatching
    {u v₁ v₂ v₃ z x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : OneThreadCore G u x₁ x₂)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour)
    (k : Fin 4)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ≠ none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hv₁x₁ : v₁ ≠ x₁) :
    OneSaturated G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some k))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some k)) T none
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  have hAP : A ≠ P := by
    intro heq
    have hval : s(v₁, v₂) = s(v₁, u) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hval | hval
    · exact h.middle_ne_start hval.2
    · exact h.first_adj.ne hval.1.symm
  have hAT : A ≠ T := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      r.start_three h.left_adj r.first_adj.symm
  have hnewP : new P = some k := by simp [new, hPT]
  have hnewT : new T = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewOff (e : G.edgeSet) (heP : e ≠ P) (heT : e ≠ T) :
      new e = colour e := by simp [new, heP, heT]
  change OneSaturated G new
  intro e he
  by_cases heP : e = P
  · subst e
    exact ⟨T, hnewT, u, by simp [P], by simp [T]⟩
  by_cases heT : e = T
  · subst e
    exact False.elim (he hnewT)
  have heOld : colour e ≠ none := by
    intro heNone
    exact he ((hnewOff e heP heT).trans heNone)
  obtain ⟨f, hf, y, hye, hyf⟩ := hsat e heOld
  by_cases hfP : f = P
  · subst f
    have hycase : y = v₁ ∨ y = u := by simpa [P] using hyf
    rcases hycase with hyv₁ | hyu
    · exact ⟨A, hnewA, y, hye, by simpa [A, hyv₁]⟩
    · exact ⟨T, hnewT, y, hye, by simpa [T, hyu]⟩
  · have hfT : f ≠ T := by
      intro hfT
      subst f
      exact hT hf
    exact ⟨f, (hnewOff f hfP hfT).trans hf, y, hye, hyf⟩

/-! ## Condition 3 under the same move -/

/-- The first edge of a certified 2-thread cannot be the first edge of a
certified 1-thread from the same endpoint. -/
theorem longPair_twoThread_firstEdge_ne_oneThread_firstEdge
    {u s x₁ x₂ : V} (p : G.Walk u s) (hp : IsKThread G p 2)
    (r : OneThreadCore G u x₁ x₂) :
    threadFirstEdge G p hp ≠
      (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) := by
  intro heq
  have hval : s(u, p.getVert 1) = s(x₁, u) := congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hval
  rcases hval with hbad | hfirst
  · exact r.first_adj.ne hbad.1
  · have hp₁ : p.getVert 1 = x₁ := hfirst.2
    have hpLen : p.length = 3 := by simpa using hp.length
    have hp₁₂ : G.Adj (p.getVert 1) (p.getVert 2) :=
      p.adj_getVert_succ (i := 1) (by omega)
    have hx₁p₂ : G.Adj x₁ (p.getVert 2) := by simpa [hp₁] using hp₁₂
    have hp₂mem : p.getVert 2 ∈ G.neighborFinset x₁ :=
      (G.mem_neighborFinset x₁ (p.getVert 2)).mpr hx₁p₂
    rw [neighborFinset_eq_pair_of_isTwoVertex G r.first_two
      r.first_adj.symm r.last_adj r.end_ne_start.symm] at hp₂mem
    have hp₂case : p.getVert 2 = u ∨ p.getVert 2 = x₂ := by
      simpa using hp₂mem
    rcases hp₂case with hp₂u | hp₂x₂
    · have hinj := hp.1.getVert_injOn
        (show 2 ∈ {n : ℕ | n ≤ p.length} by simp [hpLen])
        (show 0 ∈ {n : ℕ | n ≤ p.length} by simp)
        (by simpa using hp₂u)
      omega
    · have hp₂two : IsTwoVertex G (p.getVert 2) :=
        hp.internal_two G (by omega) (by omega)
      exact (isThreeVertex_ne_isTwoVertex G r.end_three hp₂two)
        hp₂x₂.symm

/-- The corresponding statement for a 2-thread ending at the common
endpoint. -/
theorem longPair_twoThread_lastEdge_ne_oneThread_firstEdge
    {s u x₁ x₂ : V} (p : G.Walk s u) (hp : IsKThread G p 2)
    (r : OneThreadCore G u x₁ x₂) :
    threadLastEdge G p hp ≠
      (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) := by
  intro heq
  have hrev : threadFirstEdge G p.reverse hp.reverse =
      threadLastEdge G p hp := by
    apply Subtype.ext
    simp [threadFirstEdge, threadLastEdge, Walk.getVert_reverse, hp.length,
      Sym2.eq_swap]
  exact (longPair_twoThread_firstEdge_ne_oneThread_firstEdge G p.reverse
    hp.reverse r) (hrev.trans heq)

/-- Condition 3 survives the selected-edge/1-thread matching move.  If an
external palette is affected, the newly matching 1-thread edge itself is
external at that endpoint, so the all-induced antecedent is false. -/
theorem longPair_conditionThree_selectedFresh_oneThreadFirstMatching
    {u v₁ v₂ v₃ z x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : OneThreadCore G u x₁ x₂)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (k : Fin 4)
    (hv₁x₁ : v₁ ≠ x₁) :
    ConditionThree G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some k))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some k)) T none
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  have hnewT : new T = none := by simp [new]
  have hagree : ColoringsAgreeOff G ({P, T} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ T := by simpa using he
    simp [new, hne.1, hne.2]
  change ConditionThree G new
  apply hold.of_agreeOff G hagree
  intro a b p hp haffect hleft hright
  rcases haffect with haffect | haffect
  · obtain ⟨e, heS, hext⟩ := haffect
    have hecase : e = P ∨ e = T := by simpa using heS
    rcases hecase with rfl | rfl
    · have hau : a = u :=
        longPair_start_eq_three_of_external_selectedOuter G p hp h
          (by simpa [P] using hext)
      subst a
      have hfirstT : threadFirstEdge G p hp ≠ T := by
        simpa [T] using
          longPair_twoThread_firstEdge_ne_oneThread_firstEdge G p hp r
      obtain ⟨i, hi⟩ := hleft T ⟨by simp [T], hfirstT.symm⟩
      have hfalse := hnewT.symm.trans hi
      simp at hfalse
    · obtain ⟨i, hi⟩ := hleft T (by simpa [T] using hext)
      have hfalse := hnewT.symm.trans hi
      simp at hfalse
  · obtain ⟨e, heS, hext⟩ := haffect
    have hecase : e = P ∨ e = T := by simpa using heS
    rcases hecase with rfl | rfl
    · have hbu : b = u :=
        longPair_end_eq_three_of_external_selectedOuter G p hp h
          (by simpa [P] using hext)
      subst b
      have hlastT : threadLastEdge G p hp ≠ T := by
        simpa [T] using
          longPair_twoThread_lastEdge_ne_oneThread_firstEdge G p hp r
      obtain ⟨i, hi⟩ := hright T ⟨by simp [T], hlastT.symm⟩
      have hfalse := hnewT.symm.trans hi
      simp at hfalse
    · obtain ⟨i, hi⟩ := hright T (by simpa [T] using hext)
      have hfalse := hnewT.symm.trans hi
      simp at hfalse

/-! ## Condition 2 under the same move -/

/-- If both edges of a 1-thread are induced-coloured, saturation supplies
a matching edge at its degree-three end. -/
theorem exists_matching_incident_oneThread_end_of_both_induced
    {u x₁ x₂ : V} (r : OneThreadCore G u x₁ x₂)
    (colour : G.edgeSet → OneTwoColor 4)
    (hsat : OneSaturated G colour)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ≠ none)
    (hS : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) ≠ none) :
    ∃ m : G.edgeSet, colour m = none ∧ x₂ ∈ (m : Sym2 V) := by
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.last_adj⟩
  obtain ⟨m, hm, y, hyS, hym⟩ := hsat S (by simpa [S] using hS)
  have hycase : y = x₁ ∨ y = x₂ := by simpa [S] using hyS
  rcases hycase with hyx₁ | hyx₂
  · have hx₁m : x₁ ∈ (m : Sym2 V) := by simpa [hyx₁] using hym
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.first_adj.symm r.last_adj r.end_ne_start.symm m hx₁m with
      hmT | hmS
    · have hmEq : m = T :=
        Subtype.ext (by simpa [T, Sym2.eq_swap] using hmT)
      exact False.elim (hT (by simpa [hmEq] using hm))
    · have hmEq : m = S := Subtype.ext (by simpa [S] using hmS)
      exact False.elim (hS (by simpa [hmEq] using hm))
  · exact ⟨m, hm, by simpa [hyx₂] using hym⟩

/-- A degree-two vertex affected by the selected-edge/1-thread move is
either the selected middle vertex or a neighbour of the common centre. -/
theorem longPair_twoVertex_paletteAffectedBy_selected_oneThread_cases
    {u v₁ v₂ v₃ z x₁ x₂ q : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : OneThreadCore G u x₁ x₂)
    (hq : IsTwoVertex G q)
    (haffect : PaletteAffectedBy G
      ({(⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet),
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet)} :
        Set G.edgeSet) q) :
    q = v₂ ∨ G.Adj q u := by
  rw [paletteAffectedBy_iff_inducedAffectedBy] at haffect
  obtain ⟨e, heS, y, hye, hqy⟩ := haffect
  have hecase : e = (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∨
      e = (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) := by
    simpa using heS
  have hqneU : q ≠ u :=
    isThreeVertex_ne_isTwoVertex G h.start_three hq |>.symm
  rcases hecase with rfl | rfl
  · have hycase : y = v₁ ∨ y = u := by simpa using hye
    rcases hycase with hyv₁ | hyu
    · subst y
      rcases hqy with hqv₁ | hqv₁
      · right
        simpa [hqv₁] using h.first_adj.symm
      · have hqN : q ∈ G.neighborFinset v₁ :=
          (G.mem_neighborFinset v₁ q).mpr hqv₁.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G h.first_two
          h.left_adj h.first_adj.symm h.middle_ne_start] at hqN
        have hqcase : q = v₂ ∨ q = u := by simpa using hqN
        exact hqcase.elim Or.inl (fun hqu ↦ False.elim (hqneU hqu))
    · subst y
      rcases hqy with hqu | hqu
      · exact False.elim (hqneU hqu)
      · exact Or.inr hqu
  · have hycase : y = x₁ ∨ y = u := by simpa using hye
    rcases hycase with hyx₁ | hyu
    · subst y
      rcases hqy with hqx₁ | hqx₁
      · right
        simpa [hqx₁] using r.first_adj.symm
      · have hqN : q ∈ G.neighborFinset x₁ :=
          (G.mem_neighborFinset x₁ q).mpr hqx₁.symm
        rw [neighborFinset_eq_pair_of_isTwoVertex G r.first_two
          r.first_adj.symm r.last_adj r.end_ne_start.symm] at hqN
        have hqcase : q = u ∨ q = x₂ := by simpa using hqN
        rcases hqcase with hqu | hqx₂
        · exact False.elim (hqneU hqu)
        · exact False.elim
            ((isThreeVertex_ne_isTwoVertex G r.end_three hq) hqx₂.symm)
    · subst y
      rcases hqy with hqu | hqu
      · exact False.elim (hqneU hqu)
      · exact Or.inr hqu

/-- The old induced colour on the first edge of the 1-thread disappears
from the first internal vertex after that edge becomes matching.  Any other
visible edge of the same colour would already have conflicted with the old
edge in the retained colouring. -/
theorem not_vertexSeesInduced_oneThread_oldFirstColor_after_move
    {u v₁ v₂ v₃ z x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : OneThreadCore G u x₁ x₂)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (k j : Fin 4) (hkj : k ≠ j)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hv₁x₁ : v₁ ≠ x₁) :
    ¬ VertexSeesInduced G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some k))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none)
      x₁ j := by
  classical
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some k)) T none
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ D := by
    simpa [D, B] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ (by simpa [D, P] using hPD))
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ (by simpa [D, T] using hTD))
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ (by simpa [D, P] using hPD))
  have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ (by simpa [D, T] using hTD))
  have hnewP : new P = some k := by simp [new, hPT]
  have hnewT : new T = none := by simp [new]
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBT, B, hB]
  intro hall
  obtain ⟨e, he, y, hye, hclose⟩ :=
    (vertexSeesInduced_iff G new x₁ j).mp hall
  have heP : e ≠ P := by
    intro heq
    subst e
    have hEq : some k = some j := hnewP.symm.trans he
    exact hkj (Option.some.inj hEq)
  have heT : e ≠ T := by
    intro heq
    subst e
    have hfalse : none = some j := hnewT.symm.trans he
    simp at hfalse
  have heA : e ≠ A := by
    intro heq
    subst e
    have hfalse : none = some j := hnewA.symm.trans he
    simp at hfalse
  have heB : e ≠ B := by
    intro heq
    subst e
    have hfalse : none = some j := hnewB.symm.trans he
    simp at hfalse
  have heOld : colour e = some j := by
    simpa [new, heP, heT] using he
  have hcover : insert B (insert A D) = Set.univ := by
    simpa [D, A, B] using insert_threeThread_gap_retained_eq_univ G h
  have heD : e ∈ D := by
    have heCover : e ∈ insert B (insert A D) := by rw [hcover]; simp
    simpa [heA, heB] using heCover
  have hcompat := hvalid T (by simpa [D, T] using hTD) e heD heT.symm
  have hsep : InducedSeparated G T e := by
    simpa [T, hT, heOld] using hcompat
  rw [inducedSeparated_iff_forall_endpoints] at hsep
  have hlocal := hsep x₁ (by simp [T]) y hye
  exact hclose.elim hlocal.1 hlocal.2

/-- Condition 2 survives the fresh selected-edge/1-thread matching move.
At the 1-thread vertex the old first-edge colour disappears completely;
the other affected degree-two vertices have two visible matching edges. -/
theorem longPair_conditionTwo_selectedFresh_oneThreadFirstMatching
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (hold : ConditionTwo G colour)
    (k j : Fin 4) (hkj : k ≠ j)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    ConditionTwo G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some k))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  classical
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let new : G.edgeSet → OneTwoColor 4 :=
    recolor G (recolor G colour P (some k)) T none
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ D := by
    simpa [D, B] using right_chain_edge_not_retained G h.right_adj
  have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ (by simpa [D, P] using hPD))
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ (by simpa [D, T] using hTD))
  have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ (by simpa [D, P] using hPD))
  have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ (by simpa [D, T] using hTD))
  have hCP : C ≠ P :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj h.first_adj.symm
  have hCT : C ≠ T :=
    longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      r.start_three g.left_adj r.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hnewA : new A = none := by simp [new, hAP, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBP, hBT, B, hB]
  have hnewC : new C = none := by simp [new, hCP, hCT, C, hC]
  have hnewT : new T = none := by simp [new]
  have hCTne : C ≠ T := hCT
  have hagree : ColoringsAgreeOff G ({P, T} : Set G.edgeSet) colour new := by
    intro e he
    have hne : e ≠ P ∧ e ≠ T := by simpa using he
    simp [new, hne.1, hne.2]
  have hNu : G.neighborFinset u = {v₁, w₁, x₁} :=
    longPair_neighborFinset_eq_three G h.start_three h.first_adj
      g.first_adj r.first_adj hv₁w₁ hv₁x₁ hw₁x₁
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases longPair_twoVertex_paletteAffectedBy_selected_oneThread_cases G h r
      hq (by simpa [P, T] using haffect) with hqv₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  · have hqmem : q ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u q).mpr hqu.symm
    rw [hNu] at hqmem
    have hqcase : q = v₁ ∨ q = w₁ ∨ q = x₁ := by simpa using hqmem
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
        g.left_adj g.middle_two C T hCTne hnewC hnewT
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [T]) (Or.inr g.first_adj.symm)
      · exact hall
    · subst q
      exact (not_vertexSeesInduced_oneThread_oldFirstColor_after_move G h r
        colour (by simpa [D] using hvalid) k j hkj hT hA hB hPD hTD hv₁x₁)
        (hall j)

/-- The complete prepared-gap preservation package for the induced
continuation case of `no331`. -/
theorem longPair_prepared_selectedFresh_oneThreadFirstMatching
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (k j m : Fin 4) (hkj : k ≠ j) (hkm : k ≠ m)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hk : k ∉ ExternalInducedColors G colour u
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    PreparedThreeThreadGap G h
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some k))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some k)
  let new : G.edgeSet → OneTwoColor 4 := recolor G afterP T none
  have havailP : ColorAvailableOn G D colour P (some k) := by
    exact longPair_selectedFirst_fresh_available_oneThreadThird G h g r
      hv₁w₁ hv₁x₁ hw₁x₁ colour D k m hC hS hk hkm
      (fun f hf ↦ (mem_retained_deleteIncidenceSet_iff G v₂ f).mp hf)
  have hvalidP : IsOneTwoColoringOn G D afterP := by
    apply (isOneTwoColoringOn_recolor_iff G (D := D) (colour := colour)
      (e := P) (a := some k) (by simpa [D, P] using hPD)).mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G)
      (by simpa [D] using hprepared.1) Set.diff_subset, havailP⟩
  have havailT : ColorAvailableOn G D afterP T none := by
    exact longPair_oneThreadFirst_matching_available_after_selectedFresh G h r
      colour D (by simpa [D] using hprepared.1) k hP
      (by simp [hS]) hPD hv₁x₁
  have hvalidNew : IsOneTwoColoringOn G D new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := D) (colour := afterP)
      (e := T) (a := none) (by simpa [D, T] using hTD)).mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G) hvalidP Set.diff_subset, havailT⟩
  refine ⟨by simpa [D, new, afterP, P, T] using hvalidNew, ?_, ?_, ?_⟩
  · exact longPair_oneSaturated_selectedFresh_oneThreadFirstMatching G h r
      colour hprepared.2.1 k (by simp [hT])
      hA hv₁x₁
  · exact longPair_conditionTwo_selectedFresh_oneThreadFirstMatching G hsub
      h g r hv₁w₁ hv₁x₁ hw₁x₁ colour hprepared.1
      hprepared.2.2.1 k j hkj hT hC hA hB hPD hTD
  · exact longPair_conditionThree_selectedFresh_oneThreadFirstMatching G h r
      colour hprepared.2.2.2 k hv₁x₁

/-- In the hard normal form, if the continuation of the 1-thread is
induced-coloured, move matching from the selected outer edge to the first
edge of that 1-thread.  A fourth colour can be chosen outside both colours
at the centre and outside the continuation colour; the generic prepared-gap
completion then closes the reduction. -/
theorem longPair_hasGoodFour_of_oneThreadThird_hard_of_continuation_induced
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (m : Fin 4)
    (hS : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) = some m)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    HasGoodFour G := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let R : G.edgeSet := ⟨s(v₃, z), h.last_adj⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.last_adj⟩
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hv₁w₁
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  have hQT : Q ≠ T := by
    simpa [Q, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      g.first_adj r.first_adj hw₁x₁
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
          longPair_externalPalette_eq_pair_oneThreadThird G h g r
            hv₁w₁ hv₁x₁ hw₁x₁ colour i j hP
            (by simpa [Q] using hQval) (by simpa [T] using hTval)
      have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by
        simp [hij]
      obtain ⟨k, hkPair, hkS⟩ :=
        longPair_exists_fresh_outside_two_palette ({i, j} : Set (Fin 4))
          hpairCard (colour S)
      have hkData : k ≠ i ∧ k ≠ j := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hkPair
      have hkm : k ≠ m := by
        intro hEq
        subst m
        exact hkS (by simpa [S] using hS)
      have hkOld : k ∉ ExternalInducedColors G colour u P := by
        rw [hLold]
        exact hkPair
      let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some k)
      let new : G.edgeSet → OneTwoColor 4 := recolor G afterP T none
      have hpreparedNew : PreparedThreeThreadGap G h new := by
        exact longPair_prepared_selectedFresh_oneThreadFirstMatching G hsub
          h g r hv₁w₁ hv₁x₁ hw₁x₁ colour hprepared k j m hkData.2 hkm
          hP (by simpa [T] using hTval) hC hS hA hB
          (by simpa [P] using hkOld) (by simpa [Dset, P] using hPD)
          (by simpa [Dset, T] using hTD)
      have hAD : A ∉ Dset := by
        simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
      have hBD : B ∉ Dset := by
        simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
      have hAP : A ≠ P := fun heq ↦ hAD (heq ▸ hPD)
      have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD')
      have hBP : B ≠ P := fun heq ↦ hBD (heq ▸ hPD)
      have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ hTD')
      have hRP : R ≠ P := by
        intro heq
        have hval : s(v₃, z) = s(v₁, u) := congrArg Subtype.val heq
        simp only [Sym2.eq_iff] at hval
        rcases hval with hsame | hswap
        · exact h.first_ne_third hsame.1.symm
        · exact (isThreeVertex_ne_isTwoVertex G h.start_three h.third_two)
            hswap.1.symm
      have hRT : R ≠ T := by
        intro heq
        have hcol := congrArg colour heq
        rw [show colour R = none by simpa [R] using hR,
          show colour T = some j by simpa [T] using hTval] at hcol
        simp at hcol
      have hnewP : new P = some k := by simp [new, afterP, hPT]
      have hnewT : new T = none := by simp [new]
      have hnewR : new R = none := by
        simp [new, afterP, hRP, hRT, R, hR]
      have hnewA : new A = none := by
        simp [new, afterP, hAP, hAT, A, hA]
      have hnewB : new B = none := by
        simp [new, afterP, hBP, hBT, B, hB]
      exact longPair_hasGoodFour_of_prepared_left_outer_induced G hsub h new
        hpreparedNew (by change new P ≠ none; simp [hnewP]) hnewR hnewA hnewB T hnewT
        (by simp [T]) hAT.symm hBT.symm

/-- If neither endpoint of an edge sees an induced colour, that colour is
available on the edge over every relevant edge set. -/
theorem colorAvailableOn_some_of_endpoints_not_see
    {a b : V} (hab : G.Adj a b)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet) (k : Fin 4)
    (ha : ¬ VertexSeesInduced G colour a k)
    (hb : ¬ VertexSeesInduced G colour b k) :
    ColorAvailableOn G Dset colour (⟨s(a, b), hab⟩ : G.edgeSet) (some k) := by
  apply (colorAvailableOn_some_iff G Dset colour
    (⟨s(a, b), hab⟩ : G.edgeSet) k).mpr
  intro f _hfD _hfe hfk
  rw [inducedSeparated_iff_forall_endpoints]
  intro x hxe y hyf
  have hx : x = a ∨ x = b := by simpa using hxe
  rcases hx with rfl | rfl
  · constructor
    · intro hay
      apply ha
      apply (vertexSeesInduced_iff G colour _ k).mpr
      exact ⟨f, hfk, y, hyf, Or.inl hay⟩
    · intro hay
      apply ha
      apply (vertexSeesInduced_iff G colour _ k).mpr
      exact ⟨f, hfk, y, hyf, Or.inr hay⟩
  · constructor
    · intro hby
      apply hb
      apply (vertexSeesInduced_iff G colour _ k).mpr
      exact ⟨f, hfk, y, hyf, Or.inl hby⟩
    · intro hby
      apply hb
      apply (vertexSeesInduced_iff G colour _ k).mpr
      exact ⟨f, hfk, y, hyf, Or.inr hby⟩

/-- With matching continuations on all three arms, the centre sees no
induced colour outside the two colours of the non-selected first edges. -/
theorem not_vertexSeesInduced_center_outside_pair_oneThread_matching
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (i j k : Fin 4)
    (hki : k ≠ i) (hkj : k ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) = none) :
    ¬ VertexSeesInduced G colour u k := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.last_adj⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hQ' : colour Q = some i := by simpa [Q] using hQ
  have hT' : colour T = some j := by simpa [T] using hT
  have hA' : colour A = none := by simpa [A] using hA
  have hC' : colour C = none := by simpa [C] using hC
  have hS' : colour S = none := by simpa [S] using hS
  have noAtU (f : G.edgeSet) (huf : u ∈ (f : Sym2 V))
      (hfk : colour f = some k) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have hadj := f.2
      rw [hfa] at hadj
      simpa using hadj
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hv₁w₁ hv₁x₁ hw₁x₁ hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      have hfalse : none = some k := hP'.symm.trans
        (by simpa [hfP] using hfk)
      simp at hfalse
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hik : i = k := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ] using hfk))
      exact hki hik.symm
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      have hjk : j = k := Option.some.inj
        (hT'.symm.trans (by simpa [hfT] using hfk))
      exact hkj hjk.symm
  have noAtV₁ (f : G.edgeSet) (hvf : v₁ ∈ (f : Sym2 V))
      (hfk : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G h.first_two
        h.left_adj h.first_adj.symm h.middle_ne_start f hvf with hfA | hfP
    · have hfA' : f = A := Subtype.ext (by simpa [A] using hfA)
      have hfalse : none = some k := hA'.symm.trans
        (by simpa [hfA'] using hfk)
      simp at hfalse
    · have hfP' : f = P := Subtype.ext (by simpa [P] using hfP)
      have hfalse : none = some k := hP'.symm.trans
        (by simpa [hfP'] using hfk)
      simp at hfalse
  have noAtW₁ (f : G.edgeSet) (hwf : w₁ ∈ (f : Sym2 V))
      (hfk : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G g.first_two
        g.left_adj g.first_adj.symm g.middle_ne_start f hwf with hfC | hfQ
    · have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
      have hfalse : none = some k := hC'.symm.trans
        (by simpa [hfC'] using hfk)
      simp at hfalse
    · have hfQ' : f = Q := Subtype.ext (by simpa [Q] using hfQ)
      have hik : i = k := Option.some.inj
        (hQ'.symm.trans (by simpa [hfQ'] using hfk))
      exact hki hik.symm
  have noAtX₁ (f : G.edgeSet) (hxf : x₁ ∈ (f : Sym2 V))
      (hfk : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.last_adj r.first_adj.symm r.end_ne_start f hxf with hfS | hfT
    · have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
      have hfalse : none = some k := hS'.symm.trans
        (by simpa [hfS'] using hfk)
      simp at hfalse
    · have hfT' : f = T := Subtype.ext (by simpa [T] using hfT)
      have hjk : j = k := Option.some.inj
        (hT'.symm.trans (by simpa [hfT'] using hfk))
      exact hkj hjk.symm
  intro hsee
  obtain ⟨f, hfk, y, hyf, hclose⟩ :=
    (vertexSeesInduced_iff G colour u k).mp hsee
  rcases hclose with huy | huy
  · exact noAtU f (by simpa [huy] using hyf) hfk
  · have hyN : y ∈ G.neighborFinset u := (G.mem_neighborFinset u y).mpr huy
    rw [longPair_neighborFinset_eq_three G h.start_three h.first_adj
      g.first_adj r.first_adj hv₁w₁ hv₁x₁ hw₁x₁] at hyN
    have hycase : y = v₁ ∨ y = w₁ ∨ y = x₁ := by simpa using hyN
    exact hycase.elim
      (fun hyv ↦ noAtV₁ f (by simpa [hyv] using hyf) hfk)
      (fun hywx ↦ hywx.elim
        (fun hyv ↦ noAtW₁ f (by simpa [hyv] using hyf) hfk)
        (fun hyv ↦ noAtX₁ f (by simpa [hyv] using hyf) hfk))

/-- Recolouring the first edge of a 1-thread from `j` to a distinct
induced colour removes `j` from the palette seen at its first internal
vertex. -/
theorem not_vertexSeesInduced_oneThread_oldFirstColor_after_induced_recolor
    {u v₁ v₂ v₃ z x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : OneThreadCore G u x₁ x₂)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (k j : Fin 4) (hkj : k ≠ j)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    ¬ VertexSeesInduced G
      (recolor G colour
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) (some k)) x₁ j := by
  classical
  let D : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour T (some k)
  have hAD : A ∉ D := by
    simpa [D, A] using left_chain_edge_not_retained G h.left_adj
  have hBD : B ∉ D := by
    simpa [D, B] using right_chain_edge_not_retained G h.right_adj
  have hTD' : T ∈ D := by simpa [D, T] using hTD
  have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD')
  have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ hTD')
  have hnewT : new T = some k := by simp [new]
  have hnewA : new A = none := by simp [new, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBT, B, hB]
  intro hall
  obtain ⟨e, he, y, hye, hclose⟩ :=
    (vertexSeesInduced_iff G new x₁ j).mp hall
  have heT : e ≠ T := by
    intro heq
    subst e
    have hEq : some k = some j := hnewT.symm.trans he
    exact hkj (Option.some.inj hEq)
  have heA : e ≠ A := by
    intro heq
    subst e
    have hfalse : none = some j := hnewA.symm.trans he
    simp at hfalse
  have heB : e ≠ B := by
    intro heq
    subst e
    have hfalse : none = some j := hnewB.symm.trans he
    simp at hfalse
  have heOld : colour e = some j := by
    simpa [new, heT] using he
  have hcover : insert B (insert A D) = Set.univ := by
    simpa [D, A, B] using insert_threeThread_gap_retained_eq_univ G h
  have heD : e ∈ D := by
    have heCover : e ∈ insert B (insert A D) := by rw [hcover]; simp
    simpa [heA, heB] using heCover
  have hcompat := hvalid T (by simpa [D, T] using hTD) e heD heT.symm
  have hsep : InducedSeparated G T e := by
    simpa [T, hT, heOld] using hcompat
  rw [inducedSeparated_iff_forall_endpoints] at hsep
  have hlocal := hsep x₁ (by simp [T]) y hye
  exact hclose.elim hlocal.1 hlocal.2

/-- Condition 2 survives recolouring the first edge of the 1-thread to a
fresh induced colour.  At the only delicate affected vertex, the old
colour disappears by induced separation. -/
theorem longPair_conditionTwo_recolor_oneThreadFirst_induced
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hvalid : IsOneTwoColoringOn G
      (RetainedEdges (G.deleteIncidenceSet v₂) G) colour)
    (hold : ConditionTwo G colour) (k j : Fin 4) (hkj : k ≠ j)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    ConditionTwo G
      (recolor G colour
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour T (some k)
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  have hAT : A ≠ T := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      r.start_three h.left_adj r.first_adj.symm
  have hBT : B ≠ T := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      r.start_three h.right_adj.symm r.first_adj.symm
  have hCT : C ≠ T := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      r.start_three g.left_adj r.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hCP : C ≠ P := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj h.first_adj.symm
  have hnewP : new P = none := by simp [new, hPT, P, hP]
  have hnewA : new A = none := by simp [new, hAT, A, hA]
  have hnewB : new B = none := by simp [new, hBT, B, hB]
  have hnewC : new C = none := by simp [new, hCT, C, hC]
  have hagree : ColoringsAgreeOff G ({T} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour T (some k)
  have hNu : G.neighborFinset u = {v₁, w₁, x₁} :=
    longPair_neighborFinset_eq_three G h.start_three h.first_adj
      g.first_adj r.first_adj hv₁w₁ hv₁x₁ hw₁x₁
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  have haffect' : PaletteAffectedBy G ({P, T} : Set G.edgeSet) q := by
    apply paletteAffectedBy_mono G (S := ({T} : Set G.edgeSet))
      (T := ({P, T} : Set G.edgeSet))
    · intro e he
      simpa using Or.inr he
    · exact haffect
  rcases longPair_twoVertex_paletteAffectedBy_selected_oneThread_cases G h r
      hq (by simpa [P, T] using haffect') with hqv₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G h.middle_two
      h.left_adj.symm h.right_adj h.first_ne_third h.first_two h.third_two
      hmatch) hall
  · have hqmem : q ∈ G.neighborFinset u :=
      (G.mem_neighborFinset u q).mpr hqu.symm
    rw [hNu] at hqmem
    have hqcase : q = v₁ ∨ q = w₁ ∨ q = x₁ := by simpa using hqmem
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
        g.left_adj g.middle_two C P hCP hnewC hnewP
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [P]) (Or.inr g.first_adj.symm)
      · exact hall
    · subst q
      exact (not_vertexSeesInduced_oneThread_oldFirstColor_after_induced_recolor
        G h r colour hvalid k j hkj hT hA hB hTD) (hall j)

/-- Recolouring the first edge of a 1-thread to an induced colour preserves
Condition 3 as long as a distinct 3-thread first edge at the common
degree-three centre stays matching-coloured. -/
theorem longPair_conditionThree_recolor_oneThreadFirst_induced
    {u v₁ v₂ v₃ z x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : OneThreadCore G u x₁ x₂)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionThree G colour) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hv₁x₁ : v₁ ≠ x₁) :
    ConditionThree G
      (recolor G colour
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour T (some k)
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  have hnewP : new P = none := by simp [new, hPT, P, hP]
  have hagree : ColoringsAgreeOff G ({T} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour T (some k)
  change ConditionThree G new
  apply hold.of_agreeOff G hagree
  intro a b p hp haffect hleft hright
  rcases haffect with ⟨e, heS, hext⟩ | ⟨e, heS, hext⟩
  · have heT : e = T := by simpa using heS
    subst e
    have hau : a = u := by
      have hacase : a = x₁ ∨ a = u := by simpa [T] using hext.1
      rcases hacase with hax | hau
      · exact False.elim
          ((isThreeVertex_ne_isTwoVertex G hp.start_three r.first_two) hax)
      · exact hau
    subst a
    have hTP : threadFirstEdge G p hp ≠ P := by
      simpa [P] using
        longPair_twoThread_firstEdge_ne_threeThread_firstEdge G p hp h
    have hPext : IsExternalAt G u (threadFirstEdge G p hp) P := by
      exact ⟨by simp [P], fun heq ↦ hTP heq.symm⟩
    obtain ⟨i, hi⟩ := hleft P hPext
    rw [hnewP] at hi
    simp at hi
  · have heT : e = T := by simpa using heS
    subst e
    have hbu : b = u := by
      have hbcase : b = x₁ ∨ b = u := by simpa [T] using hext.1
      rcases hbcase with hbx | hbu
      · exact False.elim
          ((isThreeVertex_ne_isTwoVertex G hp.end_three r.first_two) hbx)
      · exact hbu
    subst b
    have hTP : threadLastEdge G p hp ≠ P := by
      simpa [P] using
        longPair_twoThread_lastEdge_ne_threeThread_firstEdge G p hp h
    have hPext : IsExternalAt G u (threadLastEdge G p hp) P := by
      exact ⟨by simp [P], fun heq ↦ hTP heq.symm⟩
    obtain ⟨i, hi⟩ := hright P hPext
    rw [hnewP] at hi
    simp at hi

/-- The complete prepared-gap package for recolouring a 1-thread first
edge from its old induced colour to a fresh induced colour while its
continuation remains matching. -/
theorem longPair_prepared_recolor_oneThreadFirst_fresh
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j k : Fin 4) (hki : k ≠ i) (hkj : k ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) = none)
    (hmissX : ¬ VertexSeesInduced G colour x₁ k)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G) :
    PreparedThreeThreadGap G h
      (recolor G colour
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  classical
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour T (some k)
  have hnotU : ¬ VertexSeesInduced G colour u k := by
    exact not_vertexSeesInduced_center_outside_pair_oneThread_matching G h g r
      hv₁w₁ hv₁x₁ hw₁x₁ colour i j k hki hkj hP hQ hT hA hC hS
  have havail : ColorAvailableOn G Dset colour T (some k) := by
    exact colorAvailableOn_some_of_endpoints_not_see G r.first_adj.symm
      colour Dset k hmissX hnotU
  have hvalid : IsOneTwoColoringOn G Dset new := by
    apply (isOneTwoColoringOn_recolor_iff G (D := Dset)
      (colour := colour) (e := T) (a := some k)
      (by simpa [Dset, T] using hTD)).mpr
    exact ⟨IsOneTwoColoringOn.mono (G := G)
      (by simpa [Dset] using hprepared.1) Set.diff_subset, havail⟩
  have hsat : OneSaturated G new := by
    intro e he
    by_cases heT : e = T
    · subst e
      obtain ⟨f, hf, y, hyT, hyf⟩ := hprepared.2.1 T (by simp [T, hT])
      have hfT : f ≠ T := by
        intro hEq
        subst f
        exact (by simp [T, hT] at hf)
      exact ⟨f, by simpa [new, hfT] using hf, y, hyT, hyf⟩
    · have heOld : colour e ≠ none := by simpa [new, heT] using he
      obtain ⟨f, hf, y, hye, hyf⟩ := hprepared.2.1 e heOld
      have hfT : f ≠ T := by
        intro hEq
        subst f
        exact (by simp [T, hT] at hf)
      exact ⟨f, by simpa [new, hfT] using hf, y, hye, hyf⟩
  have htwo : ConditionTwo G new := by
    exact longPair_conditionTwo_recolor_oneThreadFirst_induced G hsub h g r
      hv₁w₁ hv₁x₁ hw₁x₁ colour hprepared.1 hprepared.2.2.1
      k j hkj hT hP hC hA hB hTD
  have hthree : ConditionThree G new := by
    exact longPair_conditionThree_recolor_oneThreadFirst_induced G h r colour
      hprepared.2.2.2 k hP hv₁x₁
  exact ⟨hvalid, hsat, htwo, hthree⟩

/-- The hard normal form with a matching-coloured continuation of the
1-thread.  Condition 2 supplies a colour missing at its degree-two internal
vertex; recolouring the first edge with that colour creates the crossed
endpoint palettes needed to fill the selected 3-thread gap. -/
theorem longPair_hasGoodFour_of_oneThreadThird_hard_of_continuation_matching
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzT : z ∉ (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet).1) :
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
  let S : G.edgeSet := ⟨s(x₁, x₂), r.last_adj⟩
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj g.first_adj hv₁w₁
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.first_adj hv₁x₁
  have hQT : Q ≠ T := by
    simpa [Q, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      g.first_adj r.first_adj hw₁x₁
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
          longPair_externalPalette_eq_pair_oneThreadThird G h g r
            hv₁w₁ hv₁x₁ hw₁x₁ colour i j hP
            (by simpa [Q] using hQval) (by simpa [T] using hTval)
      have hmatchX : VertexSeesMatching G colour x₁ := by
        apply (vertexSeesMatching_iff G colour x₁).mpr
        exact ⟨S, by simpa [S] using hS, by simp [S]⟩
      have hnotAll := hprepared.2.2.1 x₁ r.first_two hmatchX
      push_neg at hnotAll
      obtain ⟨k, hmissX⟩ := hnotAll
      have hseeI : VertexSeesInduced G colour x₁ i := by
        apply (vertexSeesInduced_iff G colour x₁ i).mpr
        exact ⟨Q, by simpa [Q] using hQval, u, by simp [Q],
          Or.inr r.first_adj.symm⟩
      have hseeJ : VertexSeesInduced G colour x₁ j := by
        apply (vertexSeesInduced_iff G colour x₁ j).mpr
        exact ⟨T, by simpa [T] using hTval, x₁, by simp [T], Or.inl rfl⟩
      have hki : k ≠ i := by
        intro hEq
        subst k
        exact hmissX hseeI
      have hkj : k ≠ j := by
        intro hEq
        subst k
        exact hmissX hseeJ
      let fresh : G.edgeSet → OneTwoColor 4 := recolor G colour T (some k)
      have hpreparedFresh : PreparedThreeThreadGap G h fresh := by
        exact longPair_prepared_recolor_oneThreadFirst_fresh G hsub h g r
          hv₁w₁ hv₁x₁ hw₁x₁ colour hprepared i j k hki hkj hP
          (by simpa [Q] using hQval) (by simpa [T] using hTval)
          hA hB hC hS hmissX hTD
      have hAD : A ∉ Dset := by
        simpa [Dset, A] using left_chain_edge_not_retained G h.left_adj
      have hBD : B ∉ Dset := by
        simpa [Dset, B] using right_chain_edge_not_retained G h.right_adj
      have hAT : A ≠ T := fun heq ↦ hAD (heq ▸ hTD')
      have hBT : B ≠ T := fun heq ↦ hBD (heq ▸ hTD')
      have hRT : R ≠ T := by
        intro heq
        apply hzT
        have hzR : z ∈ (R : Sym2 V) := by simp [R]
        rw [heq] at hzR
        exact hzR
      have hfreshP : fresh P = none := by simp [fresh, hPT, P, hP]
      have hfreshR : fresh R = none := by simp [fresh, hRT, R, hR]
      have hfreshA : fresh A = none := by simp [fresh, hAT, A, hA]
      have hfreshB : fresh B = none := by simp [fresh, hBT, B, hB]
      have hfreshQ : fresh Q = some i := by
        rw [show fresh Q = colour Q by exact recolor_ne G colour (some k) hQT]
        simpa [Q] using hQval
      have hfreshT : fresh T = some k := by simp [fresh]
      have hLfresh : ExternalInducedColors G fresh u P = {i, k} := by
        simpa [P, Q, T] using
          longPair_externalPalette_eq_pair_oneThreadThird G h g r
            hv₁w₁ hv₁x₁ hw₁x₁ fresh i k
            (by simpa [P] using hfreshP) (by simpa [Q] using hfreshQ)
            (by simpa [T] using hfreshT)
      have hagreeFresh : ColoringsAgreeOff G ({T} : Set G.edgeSet)
          colour fresh := by
        simpa [fresh] using coloringsAgreeOff_recolor G colour T (some k)
      have hRunchanged : ExternalInducedColors G colour z R =
          ExternalInducedColors G fresh z R := by
        apply externalInducedColors_eq_of_agreeOff G hagreeFresh
        intro e hext heT
        have heq : e = T := by simpa using heT
        subst e
        exact hzT hext.1
      have hRfresh : ExternalInducedColors G fresh z R = {i, j} := by
        calc
          ExternalInducedColors G fresh z R =
              ExternalInducedColors G colour z R := hRunchanged.symm
          _ = ExternalInducedColors G colour u P := hpal.symm
          _ = {i, j} := hLold
      have hpairCard : ({i, j} : Set (Fin 4)).ncard = 2 := by simp [hij]
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
        hpreparedFresh j k l hfreshA hfreshB hfreshP hfreshR
      · rw [hLfresh]
        simp [hij.symm, hkj.symm]
      · rw [hRfresh]
        simp [hki, hkj]
      · rw [hRfresh]
        simp
      · rw [hLfresh]
        simp
      · rw [hLfresh]
        simp [hlData.1, hlData.2, hkl.symm]
      · rw [hRfresh]
        simp [hlData.1, hlData.2, hkl.symm]

/-- The complete hard case for a 1-thread third arm, obtained by splitting
on whether its continuation is matching or induced-coloured. -/
theorem longPair_hasGoodFour_of_oneThreadThird_hard
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ForkTwoStepCore G u w₁ w₂)
    (r : OneThreadCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hQD : (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzT : z ∉ (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet).1) :
    HasGoodFour G := by
  cases hSval : colour (⟨s(x₁, x₂), r.last_adj⟩ : G.edgeSet) with
  | none =>
      exact longPair_hasGoodFour_of_oneThreadThird_hard_of_continuation_matching
        G hsub h g r hv₁w₁ hv₁x₁ hw₁x₁ colour hprepared hP hR hA hB hC
        hSval hQD hTD hpal hzT
  | some m =>
      exact longPair_hasGoodFour_of_oneThreadThird_hard_of_continuation_induced
        G hsub h g r hv₁w₁ hv₁x₁ hw₁x₁ colour hprepared hP hR hA hB hC
        m hSval hQD hTD

/-- A smaller good colouring obtained by deleting the middle of the
selected 3-thread rules out the complete `(3,3,1)` configuration. -/
theorem longPair_no_threeThreeOne_of_smaller_good
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u y}
    (hp : IsKThread G p 3) (hq : IsKThread G q 3) (hr : IsKThread G r 1)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G) : False := by
  classical
  let h := hp.threeThreadCore G
  let g := (hq.threeThreadCore G).forkTwoStep G
  let rCore := hr.oneThreadCore G
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
  have hzT : z ∉ (T : Sym2 V) := by
    intro hz
    have hzcase : z = u ∨ z = r.getVert 1 := by
      simpa [T, threadFirstEdge] using hz
    rcases hzcase with hzu | hzr
    · apply hpGetNe 4 0 (by omega) (by omega) (by omega)
      simpa [hpEnd] using hzu
    · have hzThree : IsThreeVertex G z := hp.end_three
      have hrTwo : IsTwoVertex G (r.getVert 1) :=
        IsKThread.internal_two G hr (by omega) (by
          have hlen : r.length = 2 := by simpa using hr.length
          omega)
      exact (isThreeVertex_ne_isTwoVertex G hzThree hrTwo) hzr
  apply hbad
  exact longPair_hasGoodFour_of_oneThreadThird_hard G hsub h g rCore
    hpq hpr hqr base hprepared
    (by simpa [h, base, P, threadFirstEdge, Sym2.eq_swap] using hP)
    (by simpa [h, base, R, threadLastEdge] using hR)
    (by simpa [h, A] using hA) (by simpa [h, B] using hB)
    (by simpa [g, base] using hC)
    (by simpa [g, Q, threadFirstEdge, Sym2.eq_swap] using hQD)
    (by simpa [rCore, T, threadFirstEdge, Sym2.eq_swap] using hTD)
    (by simpa [h, base, P, R, threadFirstEdge, threadLastEdge,
      Sym2.eq_swap] using hpal)
    (by simpa [rCore, T, threadFirstEdge, Sym2.eq_swap] using hzT)

end Finite

end


end LeanCo.PackingEdgeColoring
