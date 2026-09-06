import LeanCo.PackingEdgeColoring.SectionFourNoThreeThreeThree

/-!
# The common two-step third-arm reduction for Section 4

This module generalizes the fresh-colour core of `no333` to a third arm
whose first two vertices are degree two.  It is the shared colour-theoretic
part of the paper's `no332` reduction.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Exactly the prefix of a long third arm used by the no333/no332 fresh
recolouring: `u-x₁-x₂`, with both noncentral vertices degree two. -/
structure TwoStepArmCore (u x₁ x₂ : V) : Prop where
  first_two : IsTwoVertex G x₁
  second_two : IsTwoVertex G x₂
  first_adj : G.Adj u x₁
  second_adj : G.Adj x₁ x₂
  second_ne_start : x₂ ≠ u

theorem ThreeThreadCore.twoStepArm
    {u x₁ x₂ x₃ y : V} (h : ThreeThreadCore G u x₁ x₂ x₃ y) :
    TwoStepArmCore G u x₁ x₂ :=
  ⟨h.first_two, h.middle_two, h.first_adj, h.left_adj, h.middle_ne_start⟩

theorem IsKThread.twoStepArmCore
    {u y : V} {p : G.Walk u y} (hp : IsKThread G p 2) :
    TwoStepArmCore G u (p.getVert 1) (p.getVert 2) := by
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

theorem longPair_externalPalette_eq_pair_twoStepThird
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : TwoStepArmCore G u x₁ x₂)
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

/-- Availability part of the fresh recolouring with only a two-step third
arm. -/
theorem longPair_forkFirst_fresh_available_twoStepThird
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : TwoStepArmCore G u x₁ x₂)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.second_adj⟩ : G.edgeSet) = none)
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
  let S : G.edgeSet := ⟨s(x₁, x₂), r.second_adj⟩
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
      have := f.2
      rw [hfa] at this
      simpa using this
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
        g.left_adj g.first_adj.symm g.middle_ne_start f hwf with hfC | hfQ'
    · have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
      have hfalse : none = some k := hC'.symm.trans (by simpa [hfC'] using hcf)
      simp at hfalse
    · exact hfQ (Subtype.ext (by simpa [Q] using hfQ'))
  have noAtX₁ (f : G.edgeSet)
      (hxf : x₁ ∈ (f : Sym2 V)) (hcf : colour f = some k) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.second_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT
    · have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
      have hfalse : none = some k := hS'.symm.trans (by simpa [hfS'] using hcf)
      simp at hfalse
    · have hfT' : f = T := Subtype.ext (by simpa [T] using hfT)
      exact hk ⟨T, ⟨by simp [T], hPT.symm⟩, by simpa [hfT'] using hcf⟩
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

/-- The Condition-2 part of the fork-first recolouring only needs the
third arm through `x₁` to continue to one further degree-two vertex. -/
theorem longPair_conditionTwo_recolor_forkFirst_twoStepThird
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : TwoStepArmCore G u x₁ x₂)
    (hv₁w₁ : v₁ ≠ w₁) (hv₁x₁ : v₁ ≠ x₁) (hw₁x₁ : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : ConditionTwo G colour) (k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.second_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none) :
    ConditionTwo G
      (recolor G colour
        (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) (some k)) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.second_adj⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let B : G.edgeSet := ⟨s(v₃, v₂), h.right_adj.symm⟩
  let new : G.edgeSet → OneTwoColor 4 := recolor G colour Q (some k)
  have hPQ : P ≠ Q := by
    intro heq
    have hval : s(v₁, u) = s(w₁, u) := congrArg Subtype.val heq
    simp only [Sym2.eq_iff] at hval
    rcases hval with hsame | hswap
    · exact hv₁w₁ hsame.1
    · exact h.first_adj.ne hswap.1.symm
  have hCQ : C ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      g.start_three g.left_adj g.first_adj.symm
  have hSQ : S ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G r.first_two r.second_two
      g.start_three r.second_adj g.first_adj.symm
  have hAQ : A ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      g.start_three h.left_adj g.first_adj.symm
  have hBQ : B ≠ Q := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.third_two h.middle_two
      g.start_three h.right_adj.symm g.first_adj.symm
  have hCP : C ≠ P := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G g.first_two g.middle_two
      h.start_three g.left_adj h.first_adj.symm
  have hSP : S ≠ P := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G r.first_two r.second_two
      h.start_three r.second_adj h.first_adj.symm
  have hAB : A ≠ B := by
    simpa [A, B, Sym2.eq_swap] using
      chain_edges_ne G h.left_adj h.right_adj h.first_ne_third
  have hnewP : new P = none := by
    rw [show new P = colour P by exact recolor_ne G colour (some k) hPQ]
    simpa [P] using hP
  have hnewC : new C = none := by
    rw [show new C = colour C by exact recolor_ne G colour (some k) hCQ]
    simpa [C] using hC
  have hnewS : new S = none := by
    rw [show new S = colour S by exact recolor_ne G colour (some k) hSQ]
    simpa [S] using hS
  have hnewA : new A = none := by
    rw [show new A = colour A by exact recolor_ne G colour (some k) hAQ]
    simpa [A] using hA
  have hnewB : new B = none := by
    rw [show new B = colour B by exact recolor_ne G colour (some k) hBQ]
    simpa [B] using hB
  have hagree : ColoringsAgreeOff G ({Q} : Set G.edgeSet) colour new := by
    simpa [new] using coloringsAgreeOff_recolor G colour Q (some k)
  have hNu : G.neighborFinset u = {v₁, w₁, x₁} :=
    neighborFinset_eq_triple_of_isThreeVertex G h.start_three
      h.first_adj g.first_adj r.first_adj
      hv₁w₁ hv₁x₁ hw₁x₁
  change ConditionTwo G new
  apply hold.of_agreeOff G hagree
  intro q hq haffect hmatch hall
  rcases longThreeFork_twoVertex_paletteAffectedBy_forkFirst_cases G g hq
      (by simpa [Q] using haffect) with hqw₂ | hqu
  · subst q
    exact (longPair_paletteCondition_at_two_two_neighbours G g.middle_two
      g.left_adj.symm g.right_adj g.first_ne_third g.first_two g.third_two
      hmatch) hall
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
      apply longPair_paletteCondition_at_two_visible_matching G hsub g.first_two
        g.left_adj g.middle_two C P hCP hnewC hnewP
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [C]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [P]) (Or.inr g.first_adj.symm)
      · exact hall
    · subst q
      apply longPair_paletteCondition_at_two_visible_matching G hsub r.first_two
        r.second_adj r.second_two S P hSP hnewS hnewP
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [S]) (Or.inl rfl)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (by simp [P]) (Or.inr r.first_adj.symm)
      · exact hall

/-- The complete prepared-gap package for the fresh recolouring when the
third arm is known only through its first two degree-two vertices. -/
theorem longPair_prepared_recolor_forkFirst_fresh_twoStepThird
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : TwoStepArmCore G u x₁ x₂)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i k : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.second_adj⟩ : G.edgeSet) = none)
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
    exact longPair_forkFirst_fresh_available_twoStepThird G h g r hvw hvx hwx
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
    exact longPair_conditionTwo_recolor_forkFirst_twoStepThird G hsub h g r
      hvw hvx hwx colour hprepared.2.2.1 k hP hC hS hA hB
  have hthree : ConditionThree G new := by
    exact longThreeFork_conditionThree_recolor_forkFirst_induced G h g colour
      hprepared.2.2.2 k hP (by simpa [P, Q] using hPQ)
  exact ⟨hvalid, hsat, htwo, hthree⟩

/-- The complete hard-colour case for two distinct 3-thread arms and a
third arm known through two consecutive degree-two vertices. -/
theorem longPair_hasGoodFour_of_twoStepThird_hard
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : TwoStepArmCore G u x₁ x₂)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hS : colour (⟨s(x₁, x₂), r.second_adj⟩ : G.edgeSet) = none)
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
  let S : G.edgeSet := ⟨s(x₁, x₂), r.second_adj⟩
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
          longPair_externalPalette_eq_pair_twoStepThird G h g r hvw hvx hwx
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
        exact longPair_prepared_recolor_forkFirst_fresh_twoStepThird G hsub h g r
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
          longPair_externalPalette_eq_pair_twoStepThird G h g r hvw hvx hwx
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

/-- The no332 reduction with the two-thread Claim-1 conclusion exposed as
one explicit hypothesis.  This is the exact integration boundary for the
independent proof that the second edge of the 2-thread is matching. -/
theorem longPair_no_threeThreeTwo_of_smaller_good_of_second_matching
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    {u z t y : V} {p : G.Walk u z} {q : G.Walk u t} {r : G.Walk u y}
    (hp : IsKThread G p 3) (hq : IsKThread G q 3) (hr : IsKThread G r 2)
    (hpq : p.getVert 1 ≠ q.getVert 1)
    (hpr : p.getVert 1 ≠ r.getVert 1)
    (hqr : q.getVert 1 ≠ r.getVert 1)
    (small : (deleteThreeThreadMiddle G (p.getVert 2)).edgeSet →
      OneTwoColor 4)
    (hsmall : GoodFour (deleteThreeThreadMiddle G (p.getVert 2)) small)
    (hsub : IsSubcubic G) (hbad : ¬ HasGoodFour G)
    (hS : (transportColoringToSupergraph
        (G.deleteIncidenceSet_le (p.getVert 2)) small)
      (⟨s(r.getVert 1, r.getVert 2),
        (hr.twoStepArmCore G).second_adj⟩ : G.edgeSet) = none) : False := by
  classical
  let h := hp.threeThreadCore G
  let g := hq.threeThreadCore G
  let sCore := hr.twoStepArmCore G
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
  exact longPair_hasGoodFour_of_twoStepThird_hard G hsub h g sCore hpq hpr hqr
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

/-! ## Alternate fresh swap for the induced second-edge obstruction -/

/-- A colour avoiding the two other first edges and the second edge of the
two-step arm is available on the selected first edge.  This is the local
availability fact used to break the unique Condition-3 obstruction left by
the ordinary Claim-1 swap. -/
theorem longPair_selectedFirst_fresh_available_twoStepThird
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : TwoStepArmCore G u x₁ x₂)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (d i j : Fin 4)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hC : colour (⟨s(w₁, w₂), g.left_adj⟩ : G.edgeSet) = none)
    (hSd : colour (⟨s(x₁, x₂), r.second_adj⟩ : G.edgeSet) ≠ some d)
    (hdi : d ≠ i) (hdj : d ≠ j)
    (hretained : ∀ f : G.edgeSet, f ∈ Dset → v₂ ∉ (f : Sym2 V)) :
    ColorAvailableOn G Dset colour
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d) := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let C : G.edgeSet := ⟨s(w₁, w₂), g.left_adj⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.second_adj⟩
  have hP' : colour P = none := by simpa [P] using hP
  have hQ' : colour Q = some i := by simpa [Q] using hQ
  have hT' : colour T = some j := by simpa [T] using hT
  have hC' : colour C = none := by simpa [C] using hC
  have hSd' : colour S ≠ some d := by simpa [S] using hSd
  have noAtU (f : G.edgeSet) (hfP : f ≠ P)
      (huf : u ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    obtain ⟨a, hfa⟩ := Sym2.mem_iff_exists.mp huf
    have hua : G.Adj u a := by
      have := f.2
      rw [hfa] at this
      simpa using this
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · exact hfP (Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa))
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hdEq : i = d := Option.some.inj (hQ'.symm.trans (by simpa [hfQ] using hcf))
      exact hdi hdEq.symm
    · have hfT : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa)
      have hdEq : j = d := Option.some.inj (hT'.symm.trans (by simpa [hfT] using hcf))
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
        g.left_adj g.first_adj.symm g.middle_ne_start f hwf with hfC | hfQ
    · have hfC' : f = C := Subtype.ext (by simpa [C] using hfC)
      have hfalse : none = some d := hC'.symm.trans (by simpa [hfC'] using hcf)
      simp at hfalse
    · have hfQ' : f = Q := Subtype.ext (by simpa [Q] using hfQ)
      have hdEq : i = d := Option.some.inj (hQ'.symm.trans (by simpa [hfQ'] using hcf))
      exact hdi hdEq.symm
  have noAtX₁ (f : G.edgeSet)
      (hxf : x₁ ∈ (f : Sym2 V)) (hcf : colour f = some d) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.second_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT
    · exact hSd' (by
        have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
        simpa [hfS'] using hcf)
    · have hfT' : f = T := Subtype.ext (by simpa [T] using hfT)
      have hdEq : j = d := Option.some.inj (hT'.symm.trans (by simpa [hfT'] using hcf))
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

/-- After putting an induced colour on the selected first edge, the first
edge of the two-step arm can be made matching.  Its two endpoints have no
other matching incident edge: the centre has only the three displayed
arms, and the next edge of the two-step arm is induced. -/
theorem longPair_twoStepFirst_matching_available_after_selectedFresh
    {u v₁ v₂ v₃ z w₁ w₂ w₃ t x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (g : ThreeThreadCore G u w₁ w₂ w₃ t)
    (r : TwoStepArmCore G u x₁ x₂)
    (hvw : v₁ ≠ w₁) (hvx : v₁ ≠ x₁) (hwx : w₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4) (Dset : Set G.edgeSet)
    (d i j : Fin 4)
    (hQ : colour (⟨s(w₁, u), g.first_adj.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hS : colour (⟨s(x₁, x₂), r.second_adj⟩ : G.edgeSet) ≠ none) :
    ColorAvailableOn G Dset
      (recolor G colour
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
      (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none := by
  classical
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := ⟨s(w₁, u), g.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let S : G.edgeSet := ⟨s(x₁, x₂), r.second_adj⟩
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some d)
  have hPQ : P ≠ Q := by
    simpa [P, Q] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj g.first_adj hvw
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  have hPS : P ≠ S := by
    exact (longPair_twoTwoEdge_ne_edgeEndingAtThree G r.first_two r.second_two
      h.start_three r.second_adj h.first_adj.symm).symm
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
      have := f.2
      rw [hfa] at this
      simpa using this
    rcases longPair_eq_one_of_three_of_adj G h.start_three h.first_adj
        g.first_adj r.first_adj hvw hvx hwx hua with rfl | rfl | rfl
    · have hfP : f = P := Subtype.ext (by simpa [P, Sym2.eq_swap] using hfa)
      have hfalse : some d = none := hafterP.symm.trans (by simpa [hfP] using hcf)
      simp at hfalse
    · have hfQ : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfa)
      have hfalse : some i = none := hafterQ.symm.trans (by simpa [hfQ] using hcf)
      simp at hfalse
    · exact hfT (Subtype.ext (by simpa [T, Sym2.eq_swap] using hfa))
  have noAtX₁ (f : G.edgeSet) (hfT : f ≠ T)
      (hxf : x₁ ∈ (f : Sym2 V)) (hcf : afterP f = none) : False := by
    rcases edge_eq_left_or_right_of_incident_two G r.first_two
        r.second_adj r.first_adj.symm r.second_ne_start f hxf with hfS | hfT'
    · have hfS' : f = S := Subtype.ext (by simpa [S] using hfS)
      exact hafterS (by simpa [hfS'] using hcf)
    · exact hfT (Subtype.ext (by simpa [T] using hfT'))
  apply (colorAvailableOn_none_iff G Dset afterP T).mpr
  intro f _hfD hfT hcf a ha haf
  have hacase : a = x₁ ∨ a = u := by simpa [T] using ha
  exact hacase.elim
    (fun hax ↦ noAtX₁ f hfT (by simpa [hax] using haf) hcf)
    (fun hau ↦ noAtU f hfT (by simpa [hau] using haf) hcf)

/-- Swapping the matching role from the selected first edge to the first
edge of the two-step arm preserves inclusion-saturation even when the new
induced colour on the selected edge is not the old colour of the arm. -/
theorem longPair_oneSaturated_selectedFresh_twoStepFirstMatching
    {u v₁ v₂ v₃ z x₁ x₂ : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (r : TwoStepArmCore G u x₁ x₂)
    (hvx : v₁ ≠ x₁)
    (colour : G.edgeSet → OneTwoColor 4)
    (hold : OneSaturated G colour) (d j : Fin 4)
    (hT : colour (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none) :
    OneSaturated G
      (recolor G
        (recolor G colour
          (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) (some d))
        (⟨s(x₁, u), r.first_adj.symm⟩ : G.edgeSet) none) := by
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let T : G.edgeSet := ⟨s(x₁, u), r.first_adj.symm⟩
  let A : G.edgeSet := ⟨s(v₁, v₂), h.left_adj⟩
  let afterP : G.edgeSet → OneTwoColor 4 := recolor G colour P (some d)
  let new : G.edgeSet → OneTwoColor 4 := recolor G afterP T none
  have hPT : P ≠ T := by
    simpa [P, T] using
      longPair_firstEdges_ne_of_firstVertices_ne G h.first_adj r.first_adj hvx
  have hAP : A ≠ P := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      h.start_three h.left_adj h.first_adj.symm
  have hAT : A ≠ T := by
    exact longPair_twoTwoEdge_ne_edgeEndingAtThree G h.first_two h.middle_two
      h.start_three h.left_adj r.first_adj.symm
  have hnewP : new P = some d := by simp [new, afterP, hPT]
  have hnewT : new T = none := by simp [new]
  have hnewA : new A = none := by simp [new, afterP, hAP, hAT, A, hA]
  have hnewOff (e : G.edgeSet) (heP : e ≠ P) (heT : e ≠ T) :
      new e = colour e := by simp [new, afterP, heP, heT]
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
  obtain ⟨f, hf, y, hye, hyf⟩ := hold e heOld
  by_cases hfP : f = P
  · subst f
    have hycase : y = v₁ ∨ y = u := by simpa [P] using hyf
    rcases hycase with hyv₁ | hyu
    · exact ⟨A, hnewA, y, hye, by simpa [A, hyv₁]⟩
    · exact ⟨T, hnewT, y, hye, by simpa [T, hyu]⟩
  · have hfT : f ≠ T := by
      intro hfT
      subst f
      have hfalse : some j = none := hT.symm.trans (by simpa [T] using hf)
      simp at hfalse
    exact ⟨f, (hnewOff f hfP hfT).trans hf, y, hye, hyf⟩

end Finite

end

end LeanCo.PackingEdgeColoring
