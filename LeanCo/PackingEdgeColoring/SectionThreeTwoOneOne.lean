import LeanCo.PackingEdgeColoring.SectionThreeEasyOuter
import LeanCo.PackingEdgeColoring.SectionThreeTwoTwoZero

/-!
# The Section 3 `(2,1,1)` reduction

This module formalizes Lemma 3.5.  Remote endpoints are allowed to overlap;
no girth assumption is made.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In a `(2,1,1)` configuration, a matching-coloured first edge on one
short branch leaves at most four active blockers for the long branch's left
outer edge. -/
theorem card_activeBlockers_leftOuter_le_four_of_twoOneOne_matching
    {u a x z b c : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hc : IsTwoVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hxu : x ≠ u) (hza : z ≠ a)
    (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor 5}
    (hD : ∀ f ∈ D, f ≠ (⟨s(a, x), hax⟩ : G.edgeSet))
    (hBnone : colour (⟨s(u, b), hub⟩ : G.edgeSet) = none) :
    (activeInducedBlockerEdgesOn G D colour
      (⟨s(u, a), hua⟩ : G.edgeSet)).card ≤ 4 := by
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
  have hScard : S.card ≤ 5 := by
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
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨B, hBmem⟩
    rw [Finset.card_erase_of_mem hBmem]
    omega
  exact (Finset.card_le_card hsubErase).trans (by omega)

/-- A matching witness together with all five induced colours injects the
six semantic colours into the visible-edge set. -/
theorem six_le_card_vertexVisibleEdgeFinset_of_matching_and_full_palette
    {colour : G.edgeSet → OneTwoColor 5} {q : V}
    (hmatch : VertexSeesMatching G colour q)
    (hall : ∀ i : Fin 5, VertexSeesInduced G colour q i) :
    6 ≤ (vertexVisibleEdgeFinset G q).card := by
  classical
  obtain ⟨m, hm, hqm⟩ := (vertexSeesMatching_iff G colour q).mp hmatch
  choose f hf v hv hclose using fun i =>
    (vertexSeesInduced_iff G colour q i).mp (hall i)
  let witness : OneTwoColor 5 → G.edgeSet
    | none => m
    | some i => f i
  have hwcolour (c : OneTwoColor 5) : colour (witness c) = c := by
    cases c with
    | none => exact hm
    | some i => exact hf i
  have hwmem (c : OneTwoColor 5) :
      (witness c : Sym2 V) ∈ vertexVisibleEdgeFinset G q := by
    cases c with
    | none =>
        exact mem_vertexVisibleEdgeFinset_of_endpoint_close G hqm (Or.inl rfl)
    | some i =>
        exact mem_vertexVisibleEdgeFinset_of_endpoint_close G (hv i) (hclose i)
  let intoVisible : OneTwoColor 5 ↪
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

/-- If exactly one induced colour is available and there are at most four
active blockers, distinct active blockers have distinct colours. -/
theorem activeBlockerColour_injective_of_unique_available
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor 5)
    (e : G.edgeSet) (t : Fin 5)
    (ht : ColorAvailableOn G D colour e (some t))
    (hunique : ∀ i : Fin 5,
      ColorAvailableOn G D colour e (some i) → i = t)
    (hcard : (activeInducedBlockerEdgesOn G D colour e).card ≤ 4) :
    Function.Injective (activeBlockerColour G D colour e) := by
  classical
  let A := {f : G.edgeSet // f ∈ activeInducedBlockerEdgesOn G D colour e}
  let B := {i : Fin 5 // i ≠ t}
  let pick : A → B := fun f =>
    ⟨activeBlockerColour G D colour e f, by
      intro heq
      have hf := (mem_activeInducedBlockerEdgesOn G D colour e f.1).mp f.2
      have hcolour : colour f.1 = some t := by
        rw [← heq]
        exact colour_activeBlockerColour G D colour e f
      exact hf.2.2.1 ((colorAvailableOn_some_iff G D colour e t).mp ht
        f.1 hf.1 hf.2.1 hcolour)⟩
  have hsurj : Function.Surjective pick := by
    intro i
    have hnot : ¬ ColorAvailableOn G D colour e (some i.1) := by
      intro hi
      exact i.2 (hunique i.1 hi)
    have hiBlocked : i.1 ∈ blockedInducedColorsOn G D colour e :=
      (mem_blockedInducedColorsOn G D colour e i.1).mpr hnot
    obtain ⟨f, hf, hcolour⟩ :=
      exists_blocker_of_mem_blockedInducedColorsOn G D colour e hiBlocked
    have hfactive : f ∈ activeInducedBlockerEdgesOn G D colour e := by
      apply (mem_activeInducedBlockerEdgesOn G D colour e f).mpr
      have hf' := (mem_inducedBlockerEdgesOn G D colour e f).mp hf
      exact ⟨hf'.1, hf'.2.1, hf'.2.2, by simp [hcolour]⟩
    refine ⟨⟨f, hfactive⟩, ?_⟩
    apply Subtype.ext
    apply Option.some.inj
    exact (colour_activeBlockerColour G D colour e ⟨f, hfactive⟩).symm.trans
      hcolour
  have hAcard : Fintype.card A =
      (activeInducedBlockerEdgesOn G D colour e).card := by
    simpa [A] using
      (Fintype.card_coe (activeInducedBlockerEdgesOn G D colour e))
  have hBcard : Fintype.card B = 4 := by
    simp [B]
  have hEq : Fintype.card A = Fintype.card B := by
    apply le_antisymm
    · rw [hAcard, hBcard]
      exact hcard
    · exact Fintype.card_le_of_surjective pick hsurj
  have hinj : Function.Injective pick :=
    ((Fintype.bijective_iff_surjective_and_card pick).mpr
      ⟨hsurj, hEq⟩).1
  intro f g hfg
  have hpick : pick f = pick g := by
    apply Subtype.ext
    exact hfg
  exact hinj hpick

/-- Concrete equality-case consequence of unique availability. -/
theorem active_blockers_have_distinct_colours_of_unique_available
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor 5)
    (e : G.edgeSet) (t : Fin 5)
    (ht : ColorAvailableOn G D colour e (some t))
    (hunique : ∀ i : Fin 5,
      ColorAvailableOn G D colour e (some i) → i = t)
    (hcard : (activeInducedBlockerEdgesOn G D colour e).card ≤ 4)
    (f g : G.edgeSet)
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
  have hsub := activeBlockerColour_injective_of_unique_available G D colour e t
    ht hunique hcard hcol
  exact hfg (congrArg Subtype.val hsub)

/-! ## Condition I after recolouring the left outer edge -/

/-- Recolouring `u-a` preserves Condition I provided the matching short
branch `b` is checked explicitly.  Every other affected degree-two vertex
is automatic.  At the other short branch `c`, any incident matching edge
is accompanied in its visible neighborhood by the distinct matching edge
`u-b`. -/
theorem conditionI_recolor_leftOuter_of_safe_matching_branch
    (hsub : IsSubcubic G)
    {u a x b c : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hc : IsTwoVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x)
    (hux : u ≠ x)
    (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (base : G.edgeSet → OneTwoColor 5)
    (hcondition : ConditionI G base)
    (hBnone : base (⟨s(u, b), hub⟩ : G.edgeSet) = none)
    (j : Fin 5)
    (hbSafe : ¬ ∀ i : Fin 5,
      VertexSeesInduced G
        (recolor G base (⟨s(u, a), hua⟩ : G.edgeSet) (some j)) b i) :
    ConditionI G
      (recolor G base (⟨s(u, a), hua⟩ : G.edgeSet) (some j)) := by
  classical
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  have hBL : B ≠ L := by
    intro heq
    have hval : s(u, b) = s(u, a) := congrArg Subtype.val heq
    have hbmem : b ∈ (s(u, a) : Sym2 V) := by rw [← hval]; simp
    have hb' : b = u ∨ b = a := by simpa using hbmem
    exact hb'.elim hub.ne.symm hab.symm
  let after := recolor G base L (some j)
  apply hcondition.of_new_supports G ∅ ({L} : Set G.edgeSet)
  · intro e he
    by_cases heL : e = L
    · subst e
      change recolor G base L (some j) L = none at he
      simp at he
    · left
      change recolor G base L (some j) e = none at he
      rw [recolor_ne G base (some j) heL] at he
      exact he
  · intro e i he
    by_cases heL : e = L
    · exact Or.inr (by simpa [heL])
    · left
      change recolor G base L (some j) e = some i at he
      rw [recolor_ne G base (some j) heL] at he
      exact he
  · intro q hq haffect hmatch
    rcases haffect with hmatchAffected | hinduced
    · exact False.elim ((matchingAffectedBy_empty G q) hmatchAffected)
    obtain ⟨e, he, v, hve, hqv⟩ := hinduced
    have heL : e = L := by simpa using he
    subst e
    have hv : v = u ∨ v = a := by simpa [L] using hve
    have safeAtA (hqa : q = a) :
        ¬ ∀ i : Fin 5, VertexSeesInduced G after q i := by
      subst q
      exact paletteCondition_at_of_adjacent_two G hsub ha hax hx hmatch
    have safeAtX (hqx : q = x) :
        ¬ ∀ i : Fin 5, VertexSeesInduced G after q i := by
      subst q
      exact paletteCondition_at_of_adjacent_two G hsub hx hax.symm ha hmatch
    have safeAtB (hqb : q = b) :
        ¬ ∀ i : Fin 5, VertexSeesInduced G after q i := by
      subst q
      exact hbSafe
    have safeAtC (hqc : q = c) :
        ¬ ∀ i : Fin 5, VertexSeesInduced G after q i := by
      subst q
      obtain ⟨f, hfnone, hcf⟩ :=
        (vertexSeesMatching_iff G after c).mp hmatch
      have hBafter : after B = none := by
        change recolor G base L (some j) B = none
        rw [recolor_ne G base (some j) hBL]
        exact hBnone
      have hBf : B ≠ f := by
        intro hEq
        have hcfB : c ∈ (B : Sym2 V) := hEq ▸ hcf
        have hc' : c = u ∨ c = b := by simpa [B] using hcfB
        exact hc'.elim huc.ne.symm (fun h => hbc h.symm)
      apply paletteCondition_at_of_two_visible_matching G hsub hc B f hBf
        hBafter hfnone
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (show u ∈ (B : Sym2 V) by simp [B]) (Or.inr huc.symm)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G hcf (Or.inl rfl)
    rcases hqv with hqv | hqv
    · rcases hv with hvu | hva
      · have hqu : q = u := hqv.trans hvu
        have hq2 : G.degree q = 2 := hq
        have hq3 : G.degree q = 3 := by rw [hqu]; exact hu
        omega
      · exact safeAtA (hqv.trans hva)
    · rcases hv with hvu | hva
      · have hqu : G.Adj u q := by simpa [hvu] using hqv.symm
        rcases eq_left_or_right_or_zero_of_adj_center G hu hua hub huc
            hab hac hbc hqu with hqa | hqb | hqc
        · exact safeAtA hqa
        · exact safeAtB hqb
        · exact safeAtC hqc
      · have hqN : q ∈ G.neighborFinset a :=
          (G.mem_neighborFinset a q).mpr (by simpa [hva] using hqv.symm)
        rw [neighborFinset_eq_pair_of_isTwoVertex G ha hua.symm hax hux] at hqN
        have hq' : q = u ∨ q = x := by simpa using hqN
        rcases hq' with hqu | hqx
        · have hq2 : G.degree q = 2 := hq
          have hq3 : G.degree q = 3 := by rw [hqu]; exact hu
          omega
        · exact safeAtX hqx

/-- If `u-b` is matching-coloured and colour `t` is missing at `b`, then
recolouring `u-a` with a colour different from `t` preserves Condition I. -/
theorem conditionI_recolor_leftOuter_of_missing_at_matching_branch
    (hsub : IsSubcubic G)
    {u a x b c : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hc : IsTwoVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hux : u ≠ x)
    (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (base : G.edgeSet → OneTwoColor 5)
    (hcondition : ConditionI G base)
    (hBnone : base (⟨s(u, b), hub⟩ : G.edgeSet) = none)
    (t j : Fin 5)
    (htMissing : ¬ VertexSeesInduced G base b t)
    (hjt : j ≠ t) :
    ConditionI G
      (recolor G base (⟨s(u, a), hua⟩ : G.edgeSet) (some j)) := by
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  have hbSafe : ¬ ∀ i : Fin 5,
      VertexSeesInduced G (recolor G base L (some j)) b i := by
    intro hall
    apply htMissing
    rw [vertexSeesInduced_iff]
    obtain ⟨f, hf, w, hwf, hbw⟩ :=
      (vertexSeesInduced_iff G (recolor G base L (some j)) b t).mp (hall t)
    by_cases hfL : f = L
    · subst f
      have hjt' : some j = some t := by simpa using hf
      exact False.elim (hjt (Option.some.inj hjt'))
    · exact ⟨f, by simpa [hfL] using hf, w, hwf, hbw⟩
  exact conditionI_recolor_leftOuter_of_safe_matching_branch G hsub hu ha hx hb hc
    hua hax hux hub huc hab hac hbc base hcondition hBnone j
    (by simpa [L] using hbSafe)

/-! ## The final matching/induced shift -/

theorem shortFirst_ne_shortExternal
    {u b d : V} (hub : G.Adj u b) (hbd : G.Adj b d) (hdu : d ≠ u) :
    (⟨s(u, b), hub⟩ : G.edgeSet) ≠
      (⟨s(b, d), hbd⟩ : G.edgeSet) := by
  intro heq
  have hval : s(u, b) = s(b, d) := congrArg Subtype.val heq
  have humem : u ∈ (s(b, d) : Sym2 V) := by rw [← hval]; simp
  have hu : u = b ∨ u = d := by simpa using humem
  exact hu.elim hub.ne (fun h => hdu h.symm)

theorem leftOuter_ne_shortFirst
    {u a b : V} (hua : G.Adj u a) (hub : G.Adj u b) (hab : a ≠ b) :
    (⟨s(u, a), hua⟩ : G.edgeSet) ≠
      (⟨s(u, b), hub⟩ : G.edgeSet) := by
  intro heq
  have hval : s(u, a) = s(u, b) := congrArg Subtype.val heq
  have hamem : a ∈ (s(u, b) : Sym2 V) := by rw [← hval]; simp
  have ha : a = u ∨ a = b := by simpa using hamem
  exact ha.elim hua.ne.symm hab

theorem leftOuter_ne_shortExternal
    {u a b d : V}
    (hua : G.Adj u a) (hub : G.Adj u b) (hbd : G.Adj b d)
    (hab : a ≠ b) (hdu : d ≠ u) (hda : d ≠ a) :
    (⟨s(u, a), hua⟩ : G.edgeSet) ≠
      (⟨s(b, d), hbd⟩ : G.edgeSet) := by
  intro heq
  have hval : s(u, a) = s(b, d) := congrArg Subtype.val heq
  simp only [Sym2.eq_iff] at hval
  rcases hval with h | h
  · exact hub.ne h.1
  · exact hdu h.1.symm

/-- Condition I is preserved by the paper's final shift: `u-a` and `b-d`
gain the matching colour, while `u-b` gains an induced colour. -/
theorem conditionI_after_twoOneOne_final_shift
    (hsub : IsSubcubic G)
    {u a x b c d : V}
    (hu : IsThreeVertex G u)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hc : IsTwoVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hux : u ≠ x)
    (hub : G.Adj u b) (huc : G.Adj u c) (hbd : G.Adj b d)
    (hdu : d ≠ u) (hda : d ≠ a)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (base : G.edgeSet → OneTwoColor 5) (γ : Fin 5)
    (hcondition : ConditionI G base) :
    let L : G.edgeSet := ⟨s(u, a), hua⟩
    let B : G.edgeSet := ⟨s(u, b), hub⟩
    let BD : G.edgeSet := ⟨s(b, d), hbd⟩
    let shifted := recolor G
      (recolor G (recolor G base B (some γ)) BD none) L none
    ConditionI G shifted := by
  classical
  dsimp only
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  let BD : G.edgeSet := ⟨s(b, d), hbd⟩
  let shifted := recolor G
    (recolor G (recolor G base B (some γ)) BD none) L none
  have hLB : L ≠ B := leftOuter_ne_shortFirst G hua hub hab
  have hBBD : B ≠ BD := shortFirst_ne_shortExternal G hub hbd hdu
  have hLBD : L ≠ BD := leftOuter_ne_shortExternal G hua hub hbd hab hdu hda
  have hLnone : shifted L = none := by simp [shifted]
  have hBDnone : shifted BD = none := by
    change recolor G
      (recolor G (recolor G base B (some γ)) BD none) L none BD = none
    rw [recolor_ne G _ none hLBD.symm, recolor_eq]
  apply hcondition.of_new_supports G ({L, BD} : Set G.edgeSet)
    ({B} : Set G.edgeSet)
  · intro e he
    by_cases heL : e = L
    · exact Or.inr (by simp [heL])
    by_cases heBD : e = BD
    · exact Or.inr (by simp [heBD])
    by_cases heB : e = B
    · subst e
      change recolor G
        (recolor G (recolor G base B (some γ)) BD none) L none B = none at he
      rw [recolor_ne G _ none hLB.symm,
        recolor_ne G _ none hBBD, recolor_eq] at he
      simp at he
    · left
      change recolor G
        (recolor G (recolor G base B (some γ)) BD none) L none e = none at he
      rw [recolor_ne G _ none heL, recolor_ne G _ none heBD,
        recolor_ne G _ (some γ) heB] at he
      exact he
  · intro e i he
    by_cases heB : e = B
    · exact Or.inr (by simp [heB])
    by_cases heL : e = L
    · subst e
      change recolor G
        (recolor G (recolor G base B (some γ)) BD none) L none L = some i at he
      simp at he
    by_cases heBD : e = BD
    · subst e
      change recolor G
        (recolor G (recolor G base B (some γ)) BD none) L none BD = some i at he
      rw [recolor_ne G _ none hLBD.symm, recolor_eq] at he
      simp at he
    · left
      change recolor G
        (recolor G (recolor G base B (some γ)) BD none) L none e = some i at he
      rw [recolor_ne G _ none heL, recolor_ne G _ none heBD,
        recolor_ne G _ (some γ) heB] at he
      exact he
  · intro q hq haffect hmatch
    have safeAtA (hqa : q = a) :
        ¬ ∀ i : Fin 5, VertexSeesInduced G shifted q i := by
      subst q
      exact paletteCondition_at_of_adjacent_two G hsub ha hax hx hmatch
    have safeAtX (hqx : q = x) :
        ¬ ∀ i : Fin 5, VertexSeesInduced G shifted q i := by
      subst q
      exact paletteCondition_at_of_adjacent_two G hsub hx hax.symm ha hmatch
    have safeAtB (hqb : q = b) :
        ¬ ∀ i : Fin 5, VertexSeesInduced G shifted q i := by
      subst q
      apply paletteCondition_at_of_two_visible_matching G hsub hb L BD hLBD
        hLnone hBDnone
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (show u ∈ (L : Sym2 V) by simp [L]) (Or.inr hub.symm)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (show b ∈ (BD : Sym2 V) by simp [BD]) (Or.inl rfl)
    have safeAtC (hqc : q = c) :
        ¬ ∀ i : Fin 5, VertexSeesInduced G shifted q i := by
      subst q
      obtain ⟨f, hfnone, hcf⟩ :=
        (vertexSeesMatching_iff G shifted c).mp hmatch
      have hLf : L ≠ f := by
        intro hEq
        have hcfL : c ∈ (L : Sym2 V) := hEq ▸ hcf
        have hc' : c = u ∨ c = a := by simpa [L] using hcfL
        exact hc'.elim huc.ne.symm (fun h => hac h.symm)
      apply paletteCondition_at_of_two_visible_matching G hsub hc L f hLf
        hLnone hfnone
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G
          (show u ∈ (L : Sym2 V) by simp [L]) (Or.inr huc.symm)
      · exact mem_vertexVisibleEdgeFinset_of_endpoint_close G hcf (Or.inl rfl)
    have safeAtD (hqd : q = d) :
        ¬ ∀ i : Fin 5, VertexSeesInduced G shifted q i := by
      subst q
      exact paletteCondition_at_of_adjacent_two G hsub hq hbd.symm hb hmatch
    rcases haffect with hmatching | hinduced
    · obtain ⟨e, he, hqe⟩ := hmatching
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      · have hq' : q = u ∨ q = a := by simpa [L] using hqe
        rcases hq' with hqu | hqa
        · have hq2 : G.degree q = 2 := hq
          have hq3 : G.degree q = 3 := by rw [hqu]; exact hu
          omega
        · exact safeAtA hqa
      · have hq' : q = b ∨ q = d := by simpa [BD] using hqe
        exact hq'.elim safeAtB safeAtD
    · obtain ⟨e, he, v, hve, hqv⟩ := hinduced
      have heB : e = B := by simpa using he
      subst e
      have hv : v = u ∨ v = b := by simpa [B] using hve
      rcases hqv with hqv | hqv
      · rcases hv with hvu | hvb
        · have hqu : q = u := hqv.trans hvu
          have hq2 : G.degree q = 2 := hq
          have hq3 : G.degree q = 3 := by rw [hqu]; exact hu
          omega
        · exact safeAtB (hqv.trans hvb)
      · rcases hv with hvu | hvb
        · have huq : G.Adj u q := by simpa [hvu] using hqv.symm
          rcases eq_left_or_right_or_zero_of_adj_center G hu hua hub huc
              hab hac hbc huq with hqa | hqb | hqc
          · exact safeAtA hqa
          · exact safeAtB hqb
          · exact safeAtC hqc
        · have hqN : q ∈ G.neighborFinset b :=
            (G.mem_neighborFinset b q).mpr (by simpa [hvb] using hqv.symm)
          rw [neighborFinset_eq_pair_of_isTwoVertex G hb hub.symm hbd hdu.symm]
            at hqN
          have hq' : q = u ∨ q = d := by simpa using hqN
          rcases hq' with hqu | hqd
          · have hq2 : G.degree q = 2 := hq
            have hq3 : G.degree q = 3 := by rw [hqu]; exact hu
            omega
          · exact safeAtD hqd

/-! ## The same-induced outer case -/

set_option maxHeartbeats 2000000 in
/-- Hard kernel for Lemma 3.5.  The left and right outer edges have the
same induced colour and `u-b` is matching-coloured.  The theorem either
chooses an available colour which preserves Condition I immediately, or
uses the equality case of the blocker count and performs the final
three-edge shift. -/
theorem exists_goodFive_extension_twoOneOne_same_induced_matching_branch
    (hsub : IsSubcubic G)
    {u a x z b c d t : V}
    (hu : IsThreeVertex G u) (hz : IsThreeVertex G z)
    (ha : IsTwoVertex G a) (hx : IsTwoVertex G x)
    (hb : IsTwoVertex G b) (hc : IsTwoVertex G c)
    (hua : G.Adj u a) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hux : u ≠ x) (haz : a ≠ z)
    (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbd : G.Adj b d) (hdu : d ≠ u)
    (hct : G.Adj c t) (htu : t ≠ u)
    (base : G.edgeSet → OneTwoColor 5)
    (hvalidLeft : IsOneTwoColoringOn G
      (RetainedEdges (deleteMiddleEdge G hax) G \
        {(⟨s(u, a), hua⟩ : G.edgeSet)}) base)
    (hcondition : ConditionI G base)
    (hmiddle : base (⟨s(a, x), hax⟩ : G.edgeSet) = none)
    (α : Fin 5)
    (hleft : base (⟨s(u, a), hua⟩ : G.edgeSet) = some α)
    (hright : base (⟨s(x, z), hxz⟩ : G.edgeSet) = some α)
    (hBnone : base (⟨s(u, b), hub⟩ : G.edgeSet) = none)
    (hBmem : (⟨s(u, b), hub⟩ : G.edgeSet) ∈
      RetainedEdges (deleteMiddleEdge G hax) G)
    (hCmem : (⟨s(u, c), huc⟩ : G.edgeSet) ∈
      RetainedEdges (deleteMiddleEdge G hax) G)
    (hBDmem : (⟨s(b, d), hbd⟩ : G.edgeSet) ∈
      RetainedEdges (deleteMiddleEdge G hax) G)
    (hCTmem : (⟨s(c, t), hct⟩ : G.edgeSet) ∈
      RetainedEdges (deleteMiddleEdge G hax) G) :
    ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
  classical
  let D : Set G.edgeSet := RetainedEdges (deleteMiddleEdge G hax) G
  let E : G.edgeSet := ⟨s(a, x), hax⟩
  let L : G.edgeSet := ⟨s(u, a), hua⟩
  let R : G.edgeSet := ⟨s(x, z), hxz⟩
  let B : G.edgeSet := ⟨s(u, b), hub⟩
  let C : G.edgeSet := ⟨s(u, c), huc⟩
  let BD : G.edgeSet := ⟨s(b, d), hbd⟩
  let CT : G.edgeSet := ⟨s(c, t), hct⟩
  have hvalidLeft' : IsOneTwoColoringOn G (D \ {L}) base := by
    simpa [D, L] using hvalidLeft
  have hBmem' : B ∈ D := by simpa [B, D] using hBmem
  have hCmem' : C ∈ D := by simpa [C, D] using hCmem
  have hBDmem' : BD ∈ D := by simpa [BD, D] using hBDmem
  have hCTmem' : CT ∈ D := by simpa [CT, D] using hCTmem
  have hRmem : R ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax R).mpr
    exact (middleEdge_ne_rightOuter G hax hxz haz).symm
  have hLmem : L ∈ D := by
    apply (mem_retained_deleteMiddleEdge_iff G hax L).mpr
    exact (middleEdge_ne_leftOuter G hua hax hux).symm
  have hEL : E ≠ L := middleEdge_ne_leftOuter G hua hax hux
  have hER : E ≠ R := middleEdge_ne_rightOuter G hax hxz haz
  have hLR : L ≠ R := leftOuter_ne_rightOuter G hua hax hxz hux
  have hLB : L ≠ B := leftOuter_ne_shortFirst G hua hub hab
  have hLC : L ≠ C := leftOuter_ne_shortFirst G hua huc hac
  have hBC : B ≠ C := by
    intro heq
    have hval : s(u, b) = s(u, c) := congrArg Subtype.val heq
    have hbmem : b ∈ (s(u, c) : Sym2 V) := by rw [← hval]; simp
    have hb' : b = u ∨ b = c := by simpa using hbmem
    exact hb'.elim hub.ne.symm hbc
  have hBBD : B ≠ BD := shortFirst_ne_shortExternal G hub hbd hdu
  have hBnone' : base B = none := by simpa [B] using hBnone
  have hnotSepLR : ¬ InducedSeparated G L R := by
    intro hsep
    apply hsep.2
    exact ⟨a, by simp [L], x, by simp [R], hax⟩
  have hdelete : ∀ f ∈ D, f ≠ E := by
    intro f hf
    exact (mem_retained_deleteMiddleEdge_iff G hax f).mp hf
  have hCnot : base C ≠ none := by
    intro hCnone
    have hp := hvalidLeft' B ⟨hBmem', by simpa using hLB.symm⟩
      C ⟨hCmem', by simpa using hLC.symm⟩ hBC
    have hdisj : EndpointDisjoint G B C := by
      simpa [hBnone', hCnone] using hp
    exact hdisj u (by simp [B]) (by simp [C])
  have hmatchB : VertexSeesMatching G base b := by
    apply (vertexSeesMatching_iff G base b).mpr
    exact ⟨B, hBnone, by simp [B]⟩
  obtain ⟨τ, hτMissing⟩ : ∃ τ : Fin 5,
      ¬ VertexSeesInduced G base b τ := by
    have h := hcondition b hb hmatchB
    push_neg at h
    exact h
  have hcard : (activeInducedBlockerEdgesOn G (D \ {L}) base L).card ≤ 4 := by
    apply card_activeBlockers_leftOuter_le_four_of_twoOneOne_matching G hu ha hx
      hb hc hua hax hxz hux.symm haz.symm hub huc hab hac hbc
    · intro f hf
      exact hdelete f hf.1
    · exact hBnone
  obtain ⟨j, hj⟩ : ∃ j : Fin 5,
      ColorAvailableOn G (D \ {L}) base L (some j) := by
    apply exists_available_induced_of_card_activeBlockers_lt G
    omega
  let after := recolor G base L (some j)
  have hdomainL : insert L (D \ {L}) = D := by
    ext f
    by_cases hfL : f = L
    · subst f
      simp [hLmem]
    · simp [hfL]
  have hafterValid : IsOneTwoColoringOn G D after := by
    have h := hvalidLeft'.extend_one G (by simp) hj
    rw [hdomainL] at h
    exact h
  have hjα : j ≠ α := by
    intro hjα
    have hsep := (colorAvailableOn_some_iff G (D \ {L}) base L j).mp hj
      R ⟨hRmem, by simpa using hLR.symm⟩ hLR.symm (by simpa [hjα] using hright)
    exact hnotSepLR hsep
  have hafterMiddle : after E = none := by
    change recolor G base L (some j) E = none
    rw [recolor_ne G base (some j) hEL]
    exact hmiddle
  have hafterNotSame : ¬ ∃ i : Fin 5,
      after L = some i ∧ after R = some i := by
    rintro ⟨i, hiL, hiR⟩
    have hji : j = i := Option.some.inj (by simpa [after] using hiL)
    have hαi : α = i := by
      apply Option.some.inj
      calc
        some α = base R := hright.symm
        _ = after R := by simp [after, hLR.symm]
        _ = some i := hiR
    exact hjα (hji.trans hαi.symm)
  have finishAfter (hafterCondition : ConditionI G after) :
      ∃ colour : G.edgeSet → OneTwoColor 5, GoodFive G colour := by
    exact exists_goodFive_extension_middle_of_outer_not_same_induced G hsub
      hu hz ha hx hua hax hxz hux haz after
      (by simpa [D] using hafterValid) hafterCondition
      (by simpa [E] using hafterMiddle)
      (by simpa [L, R] using hafterNotSame)
  by_cases halt : ∃ k : Fin 5,
      ColorAvailableOn G (D \ {L}) base L (some k) ∧ k ≠ τ
  · obtain ⟨k, hk, hkτ⟩ := halt
    let goodAfter := recolor G base L (some k)
    have hgoodValid : IsOneTwoColoringOn G D goodAfter := by
      have h := hvalidLeft'.extend_one G (by simp) hk
      rw [hdomainL] at h
      exact h
    have hkα : k ≠ α := by
      intro hkα
      have hsep := (colorAvailableOn_some_iff G (D \ {L}) base L k).mp hk
        R ⟨hRmem, by simpa using hLR.symm⟩ hLR.symm
        (by simpa [hkα] using hright)
      exact hnotSepLR hsep
    have hgoodCondition :=
      conditionI_recolor_leftOuter_of_missing_at_matching_branch G hsub hu ha hx
        hb hc hua hax hux hub huc hab hac hbc base hcondition hBnone τ k
        hτMissing hkτ
    have hgoodMiddle : goodAfter E = none := by
      change recolor G base L (some k) E = none
      rw [recolor_ne G base (some k) hEL]
      exact hmiddle
    have hgoodNotSame : ¬ ∃ i : Fin 5,
        goodAfter L = some i ∧ goodAfter R = some i := by
      rintro ⟨i, hiL, hiR⟩
      have hki : k = i := Option.some.inj (by simpa [goodAfter] using hiL)
      have hαi : α = i := by
        apply Option.some.inj
        calc
          some α = base R := hright.symm
          _ = goodAfter R := by simp [goodAfter, hLR.symm]
          _ = some i := hiR
      exact hkα (hki.trans hαi.symm)
    exact exists_goodFive_extension_middle_of_outer_not_same_induced G hsub
      hu hz ha hx hua hax hxz hux haz goodAfter
      (by simpa [D] using hgoodValid) hgoodCondition
      (by simpa [E] using hgoodMiddle)
      (by simpa [L, R] using hgoodNotSame)
  · have hunique : ∀ k : Fin 5,
        ColorAvailableOn G (D \ {L}) base L (some k) → k = τ := by
      intro k hk
      by_contra hkτ
      exact halt ⟨k, hk, hkτ⟩
    have hjτ : j = τ := hunique j hj
    by_cases hafterCondition : ConditionI G after
    · exact finishAfter hafterCondition
    · have hfullB : ∀ i : Fin 5, VertexSeesInduced G after b i := by
        by_contra hsafe
        apply hafterCondition
        exact conditionI_recolor_leftOuter_of_safe_matching_branch G hsub hu ha hx
          hb hc hua hax hux hub huc hab hac hbc base hcondition hBnone j hsafe
      have hmatchBAfter : VertexSeesMatching G after b := by
        apply (vertexSeesMatching_iff G after b).mpr
        refine ⟨B, ?_, by simp [B]⟩
        change recolor G base L (some j) B = none
        rw [recolor_ne G base (some j) hLB.symm]
        exact hBnone
      have hda : d ≠ a := by
        intro hda
        have hdTwo : IsTwoVertex G d := by simpa [hda] using ha
        exact (paletteCondition_at_of_adjacent_two G hsub hb hbd hdTwo
          hmatchBAfter) hfullB
      have hLBD : L ≠ BD :=
        leftOuter_ne_shortExternal G hua hub hbd hab hdu hda
      have hBDleft : BD ∈ D \ {L} := ⟨hBDmem', by simpa using hLBD.symm⟩
      have hBDnot : base BD ≠ none := by
        intro hBDnone
        have hp := hvalidLeft' B ⟨hBmem', by simpa using hLB.symm⟩
          BD hBDleft hBBD
        have hdisj : EndpointDisjoint G B BD := by
          simpa [hBnone', hBDnone] using hp
        exact hdisj b (by simp [B]) (by simp [BD])
      obtain ⟨γ, hBDγ⟩ := Option.ne_none_iff_exists'.mp hBDnot
      have hCBD : C ≠ BD := by
        intro heq
        have hval : s(u, c) = s(b, d) := congrArg Subtype.val heq
        simp only [Sym2.eq_iff] at hval
        rcases hval with h | h
        · exact hub.ne h.1
        · exact hdu h.1.symm
      have hCγ : base C ≠ some γ := by
        intro hCeq
        have hp := hvalidLeft' C ⟨hCmem', by simpa using hLC.symm⟩
          BD hBDleft hCBD
        have hsep : InducedSeparated G C BD := by
          simpa [hCeq, hBDγ] using hp
        apply hsep.2
        exact ⟨u, by simp [C], b, by simp [BD], hub⟩
      have hBDactive : BD ∈ activeInducedBlockerEdgesOn G (D \ {L}) base L := by
        apply (mem_activeInducedBlockerEdgesOn G (D \ {L}) base L BD).mpr
        refine ⟨hBDleft, hLBD.symm, ?_, by simp [hBDγ]⟩
        intro hsep
        apply hsep.2
        exact ⟨u, by simp [L], b, by simp [BD], hub⟩
      have hCTsafe : CT = BD ∨ base CT ≠ some γ := by
        by_cases hCTBD : CT = BD
        · exact Or.inl hCTBD
        · right
          intro hCTγ
          have hCTL : CT ≠ L := by
            intro heq
            have hval : s(c, t) = s(u, a) := congrArg Subtype.val heq
            simp only [Sym2.eq_iff] at hval
            rcases hval with h | h
            · exact huc.ne h.1.symm
            · exact htu h.2
          have hCTactive : CT ∈
              activeInducedBlockerEdgesOn G (D \ {L}) base L := by
            apply (mem_activeInducedBlockerEdgesOn G (D \ {L}) base L CT).mpr
            refine ⟨⟨hCTmem', by simpa using hCTL⟩, hCTL, ?_, by simp [hCTγ]⟩
            intro hsep
            apply hsep.2
            exact ⟨u, by simp [L], c, by simp [CT], huc⟩
          exact (active_blockers_have_distinct_colours_of_unique_available G
            (D \ {L}) base L τ (by simpa [hjτ] using hj) hunique hcard
            BD CT hBDactive hCTactive (Ne.symm hCTBD)) (hBDγ.trans hCTγ.symm)
      have hnoMatchingAtD : ∀ f : G.edgeSet, d ∈ (f : Sym2 V) →
          after f ≠ none := by
        intro f hdf hfnone
        have hBf : B ≠ f := by
          intro heq
          have hdB : d ∈ (B : Sym2 V) := heq ▸ hdf
          have hd' : d = u ∨ d = b := by simpa [B] using hdB
          exact hd'.elim hdu hbd.ne.symm
        apply (paletteCondition_at_of_two_visible_matching G hsub hb B f hBf
          (by
            change recolor G base L (some j) B = none
            rw [recolor_ne G base (some j) hLB.symm]
            exact hBnone)
          hfnone
          (mem_vertexVisibleEdgeFinset_of_endpoint_close G
            (show u ∈ (B : Sym2 V) by simp [B]) (Or.inr hub.symm))
          (mem_vertexVisibleEdgeFinset_of_endpoint_close G hdf
            (Or.inr hbd))) hfullB
      let D0 : Set G.edgeSet := (D \ {L}) \ {B, BD}
      let D1 : Set G.edgeSet := (D \ {L}) \ {BD}
      have hBavailable : ColorAvailableOn G D0 base B (some γ) := by
        apply (colorAvailableOn_some_iff G D0 base B γ).mpr
        intro f hfD0 hfB hfγ
        have hfBD : f ≠ BD := by
          intro hfEq
          exact hfD0.2 (by simp [hfEq])
        by_contra hsep
        rcases secondFirst_close_imp_left_or_zeroIncident_or_secondMiddle_close G
            hu ha hb hua hax hub hbd huc hux hdu.symm hab hac hbc
            (by intro g hg; exact hdelete g hg)
            hfD0.1.1 hfB hfBD hsep with hfL | hfc | hfclose
        · exact hfD0.1.2 (by simpa [L] using hfL)
        · rcases edge_eq_left_or_right_of_incident_two G hc huc.symm hct
              htu.symm f ((mem_incidentEdgeFinset (G := G)).mp hfc) with hfC | hfCT
          · have hfEq : f = C := by
              apply Subtype.ext
              simpa only [Sym2.eq_swap] using hfC
            exact hCγ (hfEq ▸ hfγ)
          · have hfEq : f = CT := Subtype.ext hfCT
            rcases hCTsafe with hCTBD | hCTγ
            · exact hfBD (by simpa [hfEq, hCTBD])
            · exact hCTγ (hfEq ▸ hfγ)
        · have hp := hvalidLeft' BD hBDleft f hfD0.1 hfBD.symm
          have hsep' : InducedSeparated G BD f := by
            simpa [hBDγ, hfγ] using hp
          exact hfclose hsep'
      let afterB := recolor G base B (some γ)
      have hdomainB : insert B D0 = D1 := by
        ext f
        by_cases hfB : f = B
        · subst f
          simp [D0, D1, hBmem', hLB.symm, hBBD]
        · simp [D0, D1, hfB]
      have hafterB : IsOneTwoColoringOn G D1 afterB := by
        have hbase0 : IsOneTwoColoringOn G D0 base :=
          IsOneTwoColoringOn.mono (G := G) hvalidLeft' (by
            intro f hf
            exact hf.1)
        have h := hbase0.extend_one G (by simp [D0]) hBavailable
        rw [hdomainB] at h
        exact h
      have hBDavailable : ColorAvailableOn G D1 afterB BD none := by
        apply (colorAvailableOn_none_iff G D1 afterB BD).mpr
        intro f hfD1 hfBD hfnone q hqBD hqf
        have hfB : f ≠ B := by
          intro hfB
          subst f
          have : some γ = none := by simpa [afterB] using hfnone
          simp at this
        have hfbase : base f = none := by
          simpa [afterB, hfB] using hfnone
        have hq : q = b ∨ q = d := by simpa [BD] using hqBD
        rcases hq with hqb | hqd
        · have hbf : b ∈ (f : Sym2 V) := hqb ▸ hqf
          rcases edge_eq_left_or_right_of_incident_two G hb hub.symm hbd
              hdu.symm f hbf with hfB' | hfBD'
          · exact hfB (Subtype.ext (by simpa only [Sym2.eq_swap] using hfB'))
          · exact hfBD (Subtype.ext hfBD')
        · have hafterNone : after f = none := by
            change recolor G base L (some j) f = none
            have hfL : f ≠ L := by
              intro hfL
              subst f
              exact hfD1.1.2 (by simp)
            rw [recolor_ne G base (some j) hfL]
            exact hfbase
          exact hnoMatchingAtD f (hqd ▸ hqf) hafterNone
      let afterBD := recolor G afterB BD none
      have hdomainBD : insert BD D1 = D \ {L} := by
        ext f
        by_cases hfBD : f = BD
        · subst f
          simp [D1, hBDmem', hLBD.symm]
        · simp [D1, hfBD]
      have hafterBD : IsOneTwoColoringOn G (D \ {L}) afterBD := by
        have h := hafterB.extend_one G (by simp [D1]) hBDavailable
        rw [hdomainBD] at h
        exact h
      have hLavailable : ColorAvailableOn G (D \ {L}) afterBD L none := by
        apply (colorAvailableOn_none_iff G (D \ {L}) afterBD L).mpr
        intro f hfDL hfL hfnone q hqL hqf
        have hq : q = u ∨ q = a := by simpa [L] using hqL
        rcases hq with hqu | hqa
        · have huf : u ∈ (f : Sym2 V) := hqu ▸ hqf
          rcases edge_eq_one_of_three_of_incident_three G hu hua hub huc
              hab hac hbc f huf with hfL' | hfB' | hfC'
          · exact hfL (Subtype.ext hfL')
          · have hfEq : f = B := Subtype.ext hfB'
            subst f
            have : some γ = none := by
              simpa [afterBD, afterB, hBBD] using hfnone
            simp at this
          · have hfEq : f = C := Subtype.ext hfC'
            subst f
            have hCB : C ≠ B := hBC.symm
            have : base C = none := by
              simpa [afterBD, afterB, hCBD, hCB] using hfnone
            exact hCnot this
        · have haf : a ∈ (f : Sym2 V) := hqa ▸ hqf
          have hfEq := retained_edge_eq_leftOuter_of_incident G ha hua hax hux
            f hfDL.1 haf
          exact hfL hfEq
      let shifted := recolor G afterBD L none
      have hshiftedValid : IsOneTwoColoringOn G D shifted := by
        have h := hafterBD.extend_one G (by simp) hLavailable
        rw [hdomainL] at h
        exact h
      have hshiftedCondition : ConditionI G shifted := by
        simpa [shifted, afterBD, afterB, L, B, BD] using
          conditionI_after_twoOneOne_final_shift G hsub hu ha hx hb hc hua hax
            hux hub huc hbd hdu hda hab hac hbc base γ hcondition
      have hshiftedMiddle : shifted E = none := by
        change recolor G
          (recolor G (recolor G base B (some γ)) BD none) L none E = none
        rw [recolor_ne G _ none hEL, recolor_ne G _ none
          ((hdelete BD hBDmem').symm), recolor_ne G _ (some γ)
          ((hdelete B hBmem').symm)]
        exact hmiddle
      have hshiftedLeft : shifted L = none := by simp [shifted]
      have hshiftedNotSame : ¬ ∃ i : Fin 5,
          shifted L = some i ∧ shifted R = some i := by
        rintro ⟨i, hi, _⟩
        rw [hshiftedLeft] at hi
        simp at hi
      exact exists_goodFive_extension_middle_of_outer_not_same_induced G hsub
        hu hz ha hx hua hax hxz hux haz shifted
        (by simpa [D] using hshiftedValid) hshiftedCondition
        (by simpa [E] using hshiftedMiddle)
        (by simpa [L, R] using hshiftedNotSame)

end Finite

end

end LeanCo.PackingEdgeColoring
