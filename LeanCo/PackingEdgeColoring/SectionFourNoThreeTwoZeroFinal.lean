import LeanCo.PackingEdgeColoring.SectionFourNoThreeTwoZeroMatchingFar

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Endpoint classifier for the last remaining `D = k` case.  The callback
is exactly the one-matching-far-edge completion packaged separately. -/
theorem longPair_hasGoodFour_of_twoZero_terminal_complement_dispatcher
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x) (htx : t ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b) (hbu : b ≠ u)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j m k : Fin 4)
    (hij : i ≠ j) (him : i ≠ m) (hik : i ≠ k)
    (hjm : j ≠ m) (hjk : j ≠ k) (hmk : m ≠ k)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hU : colour (⟨s(x, a), ha⟩ : G.edgeSet) = none)
    (hV : colour (⟨s(x, b), hb⟩ : G.edgeSet) = some m)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (no320ThreadMiddleEdge G q hq) = none)
    (hD : colour (threadLastEdge G q hq) = some k)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : threadLastEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hret : ∀ f, IsExternalAt G t (threadLastEdge G q hq) f →
      f ∈ RetainedEdges (G.deleteIncidenceSet v₂) G) :
    HasGoodFour G := by
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let D : G.edgeSet := threadLastEdge G q hq
  obtain ⟨c, d, hcd, hcw, hdw, htc, htd, hNt⟩ :=
    exists_two_other_neighbors_of_isThreeVertex G g.end_three g.last_adj
  let E : G.edgeSet := ⟨s(t, c), htc⟩
  let F : G.edgeSet := ⟨s(t, d), htd⟩
  have hEc : E ≠ D := by
    intro heq
    have he := congrArg Subtype.val heq
    simp only [E, D, threadLastEdge, Sym2.eq_iff] at he
    rcases he with he | he
    · exact g.last_adj.ne he.1.symm
    · exact hcw he.2
  have hFc : F ≠ D := by
    intro heq
    have he := congrArg Subtype.val heq
    simp only [F, D, threadLastEdge, Sym2.eq_iff] at he
    rcases he with he | he
    · exact g.last_adj.ne he.1.symm
    · exact hdw he.2
  have hEF : E ≠ F := by
    simpa [E, F, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G htc htd hcd
  have hEext : IsExternalAt G t D E := ⟨by simp [E], hEc⟩
  have hFext : IsExternalAt G t D F := ⟨by simp [F], hFc⟩
  have classify (e : G.edgeSet) (hext : IsExternalAt G t D e) :
      e = E ∨ e = F := by
    obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hext.1
    have hty : G.Adj t y := by
      have hadj := e.2
      rw [hey] at hadj
      simpa using hadj
    rcases longPair_eq_one_of_three_of_adj G g.end_three g.last_adj.symm
        htc htd hcw.symm hdw.symm hcd hty with hy | hy | hy
    · subst y
      exact False.elim (hext.2 (Subtype.ext (by
        simpa [D, threadLastEdge, Sym2.eq_swap] using hey)))
    · subst y
      exact Or.inl (Subtype.ext (by simpa [E, Sym2.eq_swap] using hey))
    · subst y
      exact Or.inr (Subtype.ext (by simpa [F, Sym2.eq_swap] using hey))
  have hvalid : IsOneTwoColoringOn G Dset colour := by
    simpa [Dset] using hprepared.1
  have hcenter : ExternalInducedColors G colour u P = {i, j} := by
    simpa [P, threadFirstEdge, Sym2.eq_swap] using
      longPair_externalPalette_eq_pair_three_neighbors G h.start_three
        h.first_adj hq.first_step_adj r.adj hvq hvx hqx colour i j hP
          (by simpa [threadFirstEdge, Sym2.eq_swap] using hQ) hT
  have hkCenter : k ∉ ExternalInducedColors G colour u P := by
    rw [hcenter]
    simp [hik.symm, hjk.symm]
  have hmatching (E : G.edgeSet) (n : Fin 4)
      (hEext : IsExternalAt G t D E) (hE : colour E = none)
      (hfar : ExternalInducedColors G colour t D = {n}) :
      HasGoodFour G := by
    have hnk : n ≠ k := by
      intro hnk
      subst n
      have hkmem : k ∈ ExternalInducedColors G colour t D := by
        rw [hfar]
        simp
      obtain ⟨F₀, hFext, hFk⟩ := hkmem
      have hp := hvalid D (by simpa [D, Dset] using hDD)
        F₀ (by
          simpa [D, Dset] using hret F₀ (by simpa [D] using hFext))
        hFext.2.symm
      have hD' : colour D = some k := by simpa [D] using hD
      have hsep : InducedSeparated G D F₀ := by
        simpa [hD', hFk] using hp
      exact hsep.1 t (by simp [D, threadLastEdge]) hFext.1
    rcases finFour_eq_one_of_pairwise_distinct i j m k n
        hij him hik hjm hjk hmk with hni | hnj | hnm | hnk'
    · subst n
      exact longPair_hasGoodFour_matchingFar_final G hsub h q hq r
        hvq hvx hqx ha hb hNfar colour hprepared i j m k i m i
          hik.symm hjk.symm hmk.symm hjm.symm hmk him.symm
          him hij hik hP hR hQ hT hU hV hA hB hC hD E
          (by simpa [D] using hEext) hE (by simpa [D] using hfar)
          hPD hQD hCD hDP hRP hRQ
    · subst n
      exact longPair_hasGoodFour_matchingFar_final G hsub h q hq r
        hvq hvx hqx ha hb hNfar colour hprepared i j m k j i m
          hik.symm hjk.symm hmk.symm hij hik hij
          him.symm hjm.symm hmk hP hR hQ hT hU hV hA hB hC hD E
          (by simpa [D] using hEext) hE (by simpa [D] using hfar)
          hPD hQD hCD hDP hRP hRQ
    · subst n
      exact longPair_hasGoodFour_matchingFar_final G hsub h q hq r
        hvq hvx hqx ha hb hNfar colour hprepared i j m k m i m
          hik.symm hjk.symm hmk.symm hij hik him
          him.symm hjm.symm hmk hP hR hQ hT hU hV hA hB hC hD E
          (by simpa [D] using hEext) hE (by simpa [D] using hfar)
          hPD hQD hCD hDP hRP hRQ
    · exact False.elim (hnk hnk')
  cases hEval : colour E with
  | none =>
      cases hFval : colour F with
      | none =>
          have hp := hvalid E (by simpa [Dset, D] using hret E hEext)
            F (by simpa [Dset, D] using hret F hFext) hEF
          have hdisj : EndpointDisjoint G E F := by
            simpa [hEval, hFval] using hp
          exact False.elim (hdisj t (by simp [E]) (by simp [F]))
      | some n =>
          have hfar : ExternalInducedColors G colour t D = {n} := by
            ext c₀
            constructor
            · rintro ⟨e, hext, hec₀⟩
              rcases classify e hext with rfl | rfl
              · have : (none : OneTwoColor 4) = some c₀ := by
                  simpa [hEval] using hec₀
                simp at this
              · have hcol : colour F = some c₀ := by
                  simpa [F] using hec₀
                have hcn : c₀ = n := Option.some.inj (hcol.symm.trans hFval)
                simp [hcn]
            · intro hc₀
              have hcn : c₀ = n := by simpa using hc₀
              subst c₀
              exact ⟨F, hFext, by simpa [F] using hFval⟩
          exact hmatching E n (by simpa [D] using hEext)
            (by simpa [E] using hEval) (by simpa [D] using hfar)
  | some n =>
      cases hFval : colour F with
      | none =>
          have hfar : ExternalInducedColors G colour t D = {n} := by
            ext c₀
            constructor
            · rintro ⟨e, hext, hec₀⟩
              rcases classify e hext with rfl | rfl
              · have hcol : colour E = some c₀ := by
                  simpa [E] using hec₀
                have hcn : c₀ = n := Option.some.inj (hcol.symm.trans hEval)
                simp [hcn]
              · have : (none : OneTwoColor 4) = some c₀ := by
                  simpa [hFval] using hec₀
                simp at this
            · intro hc₀
              have hcn : c₀ = n := by simpa using hc₀
              subst c₀
              exact ⟨E, hEext, by simpa [E] using hEval⟩
          exact hmatching F n (by simpa [D] using hFext)
            (by simpa [F] using hFval) (by simpa [D] using hfar)
      | some l =>
          have hfarEdges : ExternalEdgesInduced G colour t D := by
            intro e hext
            rcases classify e hext with rfl | rfl
            · exact ⟨n, by simpa [E] using hEval⟩
            · exact ⟨l, by simpa [F] using hFval⟩
          by_cases hfarEq :
              ExternalInducedColors G colour t D = {i, j}
          · exact longPair_hasGoodFour_of_twoZero_terminal_complement_far_centerPair
              G hsub h q hq r hvq hvx hqx htx ha hb hNfar colour hprepared
                i j m k hij him hik hjm hjk hmk hP hR hQ hT hU hV hA hB hC
                hD hPD hQD hCD hDD hDP hRP hRQ
                (by simpa [D] using hfarEdges) (by simpa [D] using hfarEq)
          · exact longPair_hasGoodFour_after_twoThreadTail_shift_and_selected_swap_twoZero
              G hsub h q hq r hvq hvx hqx colour hprepared i j k hjk.symm
                hP hR hQ hT hA hB hC hD hPD hQD hCD hDD hDP hRP hRQ
                (by simpa [P] using hkCenter)
                (by simpa [D] using hfarEdges)
                (by
                  intro heq
                  exact hfarEq (by simpa [D] using heq.symm))

/-- Complete local hard case for a selected 3-thread, a 2-thread whose
middle edge is matching, and a zero-thread.  The zero-thread far endpoint is
oriented so that its matching edge comes first; the fourth colour then feeds
the terminal dispatcher above. -/
theorem longPair_hasGoodFour_of_twoZero_hard
    (hsub : IsSubcubic G)
    {u v₁ v₂ v₃ z t x a b : V}
    (h : ThreeThreadCore G u v₁ v₂ v₃ z)
    (q : G.Walk u t) (hq : IsKThread G q 2)
    (r : ZeroThreadCore G u x)
    (hvq : v₁ ≠ q.getVert 1) (hvx : v₁ ≠ x)
    (hqx : q.getVert 1 ≠ x) (htx : t ≠ x)
    (ha : G.Adj x a) (hb : G.Adj x b)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hNfar : G.neighborFinset x = {u, a, b})
    (colour : G.edgeSet → OneTwoColor 4)
    (hprepared : PreparedThreeThreadGap G h colour)
    (i j : Fin 4) (hij : i ≠ j)
    (hP : colour (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) = none)
    (hR : colour (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) = none)
    (hQ : colour (threadFirstEdge G q hq) = some i)
    (hT : colour (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) = some j)
    (hA : colour (⟨s(v₁, v₂), h.left_adj⟩ : G.edgeSet) = none)
    (hB : colour (⟨s(v₃, v₂), h.right_adj.symm⟩ : G.edgeSet) = none)
    (hC : colour (no320ThreadMiddleEdge G q hq) = none)
    (hPD : (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hQD : threadFirstEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hCD : no320ThreadMiddleEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDD : threadLastEdge G q hq ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hTD : (⟨s(x, u), r.adj.symm⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hUD : (⟨s(x, a), ha⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hVD : (⟨s(x, b), hb⟩ : G.edgeSet) ∈
      RetainedEdges (G.deleteIncidenceSet v₂) G)
    (hDP : threadLastEdge G q hq ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRP : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet))
    (hRQ : (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet) ≠
      threadFirstEdge G q hq)
    (hpal : ExternalInducedColors G colour u
        (⟨s(v₁, u), h.first_adj.symm⟩ : G.edgeSet) =
      ExternalInducedColors G colour z
        (⟨s(v₃, z), h.last_adj⟩ : G.edgeSet))
    (hzQ : z ∉ (threadFirstEdge G q hq : Sym2 V))
    (hret : ∀ f, IsExternalAt G t (threadLastEdge G q hq) f →
      f ∈ RetainedEdges (G.deleteIncidenceSet v₂) G) :
    HasGoodFour G := by
  classical
  let g := hq.twoThreadCoreData G
  let Dset : Set G.edgeSet := RetainedEdges (G.deleteIncidenceSet v₂) G
  let P : G.edgeSet := ⟨s(v₁, u), h.first_adj.symm⟩
  let Q : G.edgeSet := threadFirstEdge G q hq
  let T : G.edgeSet := ⟨s(x, u), r.adj.symm⟩
  let U : G.edgeSet := ⟨s(x, a), ha⟩
  let Vedge : G.edgeSet := ⟨s(x, b), hb⟩
  have hvalid : IsOneTwoColoringOn G Dset colour := by
    simpa [Dset] using hprepared.1
  have hUV : U ≠ Vedge := by
    simpa [U, Vedge, Sym2.eq_swap] using
      longPair_firstEdges_ne_of_firstVertices_ne G ha hb hab
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G
      h.first_adj r.adj hvx
  have finishOne {a₀ b₀ : V} (ha₀ : G.Adj x a₀) (hb₀ : G.Adj x b₀)
      (hb₀u : b₀ ≠ u) (hN₀ : G.neighborFinset x = {u, a₀, b₀})
      (m : Fin 4)
      (hU₀ : colour (⟨s(x, a₀), ha₀⟩ : G.edgeSet) = none)
      (hV₀ : colour (⟨s(x, b₀), hb₀⟩ : G.edgeSet) = some m)
      (hV₀D : (⟨s(x, b₀), hb₀⟩ : G.edgeSet) ∈
        RetainedEdges (G.deleteIncidenceSet v₂) G) : HasGoodFour G := by
    let V₀ : G.edgeSet := ⟨s(x, b₀), hb₀⟩
    have hQV : Q ≠ V₀ := by
      intro heq
      have hval : s(u, q.getVert 1) = s(x, b₀) := by
        simpa [Q, V₀, threadFirstEdge] using congrArg Subtype.val heq
      simp only [Sym2.eq_iff] at hval
      rcases hval with hval | hval
      · exact r.adj.ne hval.1
      · exact hqx hval.2
    have hTV : T ≠ V₀ := by
      intro heq
      have hval : s(x, u) = s(x, b₀) :=
        congrArg Subtype.val heq
      simp only [Sym2.eq_iff] at hval
      rcases hval with hval | hval
      · exact hb₀u hval.2.symm
      · exact r.adj.ne hval.2
    have hmi : m ≠ i := by
      intro hmi
      subst m
      have hp := hvalid Q (by simpa [Q, Dset] using hQD)
        V₀ (by simpa [V₀, Dset] using hV₀D) hQV
      have hsep : InducedSeparated G Q V₀ := by
        simpa [Q, V₀, hQ, hV₀] using hp
      exact hsep.2 ⟨u, by simp [Q, threadFirstEdge], x,
        by simp [V₀], r.adj⟩
    have hmj : m ≠ j := by
      intro hmj
      subst m
      have hp := hvalid T (by simpa [T, Dset] using hTD)
        V₀ (by simpa [V₀, Dset] using hV₀D) hTV
      have hsep : InducedSeparated G T V₀ := by
        simpa [T, V₀, hT, hV₀] using hp
      exact hsep.1 x (by simp [T]) (by simp [V₀])
    obtain ⟨k, hki, hkj, hkm⟩ := exists_fin4_ne_three i j m
    exact longPair_hasGoodFour_of_twoZero_middle_matching_of_complement
      G hsub h q hq r hvq hvx hqx htx ha₀ hb₀ hb₀u hN₀ colour
        hprepared i j m k hij hmi.symm hki.symm hmj.symm hkj.symm hkm.symm
        hP hR hQ hT hU₀ hV₀ hA hB hC hPD hQD hCD hDD hTD hV₀D
        hDP hRP hRQ hpal hzQ hret
        (fun hD ↦
          longPair_hasGoodFour_of_twoZero_terminal_complement_dispatcher
            G hsub h q hq r hvq hvx hqx htx ha₀ hb₀ hb₀u hN₀ colour
              hprepared i j m k hij hmi.symm hki.symm hmj.symm hkj.symm hkm.symm
              hP hR hQ hT hU₀ hV₀ hA hB hC hD hPD hQD hCD hDD hDP hRP
              hRQ hret)
  cases hUval : colour U with
  | none =>
      cases hVval : colour Vedge with
      | none =>
          have hp := hvalid U (by simpa [U, Dset] using hUD)
            Vedge (by simpa [Vedge, Dset] using hVD) hUV
          have hdisj : EndpointDisjoint G U Vedge := by
            simpa [hUval, hVval] using hp
          exact False.elim (hdisj x (by simp [U]) (by simp [Vedge]))
      | some m =>
          exact finishOne ha hb hbu hNfar m
            (by simpa [U] using hUval) (by simpa [Vedge] using hVval) hVD
  | some m =>
      cases hVval : colour Vedge with
      | none =>
          have hNswap : G.neighborFinset x = {u, b, a} := by
            simpa [Finset.pair_comm] using hNfar
          exact finishOne hb ha hau hNswap m
            (by simpa [Vedge] using hVval) (by simpa [U] using hUval) hUD
      | some n =>
          exact longPair_hasGoodFour_of_zeroThread_twoThread_far_both_induced
            G hsub h g r hvq hvx hqx ha hb hNfar colour hprepared j
              hP hR hT (by rw [hUval]; simp) (by rw [hVval]; simp)
              hA hB (Or.inl (by simpa [g, no320ThreadMiddleEdge] using hC))
              hTD (by simpa [P, T] using hPT)
              (by simpa [g, P, threadLastEdge, Sym2.eq_swap] using hDP)

end Finite

end

end LeanCo.PackingEdgeColoring
