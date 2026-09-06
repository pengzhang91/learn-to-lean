import LeanCo.SizeRamsey.FreeExtractionIteration
import LeanCo.SizeRamsey.ExtractionColoringGlue

/-!
# One deterministic round of the BLS lower-bound iteration

This module combines fractional free-subgraph extraction with the star-type
decomposition of the final residual.  The extracted pieces and only the
coloured star part are glued into a colouring of `G \ R`; the low-degree
remainder `R` is deliberately left uncoloured for the next round.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u w

variable {V : Type u} {W : Type w}

/-! ## Separation of extracted pieces from the final residual -/

/-- A piece selected at time `t` is edge-disjoint from every later
residual. -/
theorem freeExtractionPiece_disjoint_laterResidual
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    {t T : ℕ} (ht : t < T) :
    Disjoint (freeExtractionPiece G pick t)
      (freeExtractionResidual G pick T) := by
  have hnext : t + 1 ≤ T := by omega
  have hlater : freeExtractionResidual G pick T ≤
      freeExtractionResidual G pick (t + 1) :=
    freeExtractionResidual_antitone G pick hnext
  have hone : Disjoint (freeExtractionPiece G pick t)
      (freeExtractionResidual G pick (t + 1)) := by
    rw [freeExtractionResidual_succ]
    exact disjoint_sdiff_self_right
  exact hone.mono_right hlater

/-- Consequently, a selected piece lies in `G \ R` whenever `R` is a
subgraph of the final residual. -/
theorem freeExtractionPiece_le_sdiff_of_le_finalResidual
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ Q, pick Q ≤ Q) {t T : ℕ} (ht : t < T)
    {R : SimpleGraph V}
    (hR : R ≤ freeExtractionResidual G pick T) :
    freeExtractionPiece G pick t ≤ G \ R := by
  rw [le_sdiff]
  exact ⟨freeExtractionPiece_le_initial G pick hsub t,
    (freeExtractionPiece_disjoint_laterResidual G pick ht).mono_right hR⟩

/-! ## The cover of exactly `G \ R` -/

/-- Covering family for one round: the `T` extracted pieces and the coloured
part `H \ R` of the final star decomposition. -/
def pathLowerRoundCoverFamily
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (T : ℕ) (H R : SimpleGraph V) :
    Fin T ⊕ Unit → SimpleGraph V
  | Sum.inl t => freeExtractionPiece G pick t
  | Sum.inr _ => H \ R

/-- Every member of the round family is a subgraph of `G \ R`. -/
theorem pathLowerRoundCoverFamily_le
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ Q, pick Q ≤ Q) (T : ℕ)
    {H R : SimpleGraph V}
    (hH : H ≤ freeExtractionResidual G pick T)
    (hR : R ≤ freeExtractionResidual G pick T) :
    ∀ i, pathLowerRoundCoverFamily G pick T H R i ≤ G \ R := by
  intro i
  rcases i with t | u
  · exact freeExtractionPiece_le_sdiff_of_le_finalResidual
      G pick hsub t.isLt hR
  · dsimp only [pathLowerRoundCoverFamily]
    apply (le_sdiff.mpr ·)
    exact ⟨sdiff_le.trans (hH.trans (freeExtractionResidual_le G pick T)),
      disjoint_sdiff_self_left⟩

/-- The pieces together with `H \ R` cover every edge of `G \ R`, provided
the final residual decomposes as `H ⊔ R`.  This proof explicitly rejects
the `R` alternative; `R` is not included as a colour class. -/
theorem pathLowerRoundCoverFamily_covers
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ Q, pick Q ≤ Q) (T : ℕ)
    (H R : SimpleGraph V)
    (hsplit : freeExtractionResidual G pick T = H ⊔ R) :
    EdgesCoveredBy (G \ R) (pathLowerRoundCoverFamily G pick T H R) := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have htarget : (G \ R).Adj x y := by
        simpa only [mem_edgeSet] using he
      have hG : G.Adj x y := (sdiff_adj G R x y).mp htarget |>.1
      have hnotR : ¬R.Adj x y := (sdiff_adj G R x y).mp htarget |>.2
      have hdecomp := congrArg (fun Q : SimpleGraph V => Q.Adj x y)
        (freeExtraction_eq_accumulated_sup_residual G pick hsub T)
      have hcases :
          (freeExtractionAccumulated G pick T).Adj x y ∨
            (freeExtractionResidual G pick T).Adj x y := by
        simpa only [sup_adj] using hdecomp.mp hG
      rcases hcases with hacc | hfinal
      · obtain ⟨t, ht, hpiece⟩ :=
          (freeExtractionAccumulated_adj_iff G pick T x y).mp hacc
        refine ⟨Sum.inl ⟨t, ht⟩, ?_⟩
        simpa only [pathLowerRoundCoverFamily, mem_edgeSet] using hpiece
      · have hstar : H.Adj x y ∨ R.Adj x y := by
          have := congrArg (fun Q : SimpleGraph V => Q.Adj x y) hsplit
          simpa only [sup_adj] using this.mp hfinal
        have hH : H.Adj x y := hstar.resolve_right hnotR
        refine ⟨Sum.inr (), ?_⟩
        have hHR : (H \ R).Adj x y :=
          (sdiff_adj H R x y).mpr ⟨hH, hnotR⟩
        simpa only [pathLowerRoundCoverFamily, mem_edgeSet] using hHR

/-! ## Restricting and gluing the star colouring -/

/-- Restricting an edge colouring along a spanning subgraph inclusion only
shrinks each colour graph. -/
theorem labelGraph_pullback_ofLE_le
    {G' G : SimpleGraph V} (h : G' ≤ G)
    {K : Type*} (C : G.EdgeLabeling K) (k : K) :
    (C.pullback (SimpleGraph.Hom.ofLE h)).labelGraph k ≤
      C.labelGraph k := by
  intro x y hxy
  rw [EdgeLabeling.labelGraph_adj] at hxy ⊢
  obtain ⟨hG', hk⟩ := hxy
  refine ⟨h hG', ?_⟩
  let e' : G'.edgeSet := ⟨s(x, y), by
    simpa only [mem_edgeSet] using hG'⟩
  let e : G.edgeSet := ⟨s(x, y), by
    simpa only [mem_edgeSet] using h hG'⟩
  have hk' : C ((SimpleGraph.Hom.ofLE h).mapEdgeSet e') = k := by
    simpa only [EdgeLabeling.pullback_apply, e'] using hk
  have hedge :
      (SimpleGraph.Hom.ofLE h).mapEdgeSet e' = e := by
    apply Subtype.ext
    simp [SimpleGraph.Hom.mapEdgeSet, e', e]
  have hCe : C e = k := by
    rw [← hedge]
    exact hk'
  simpa only [e] using hCe

/-- An avoiding colouring restricts to every spanning subgraph. -/
theorem exists_avoidingColoring_of_le
    {F : SimpleGraph W} {G' G : SimpleGraph V} (h : G' ≤ G)
    {K : Type*} (C : G.EdgeLabeling K)
    (hC : AvoidsMonochromaticCopy F C) :
    ∃ D : G'.EdgeLabeling K, AvoidsMonochromaticCopy F D := by
  let D := C.pullback (SimpleGraph.Hom.ofLE h)
  refine ⟨D, ?_⟩
  intro k hcopy
  exact hC k (hcopy.trans_le (labelGraph_pullback_ofLE_le h C k))

/-- The extracted pieces and the restricted star part glue to a colouring
of exactly `G \ R`, with palette size `T+s`. -/
theorem exists_path_avoidingColoring_of_round_cover
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ Q, pick Q ≤ Q)
    {T s n : ℕ} (hn : 2 ≤ n)
    (hfree : ∀ Q, (pathGraph n).Free (pick Q))
    {H R : SimpleGraph V}
    (hH : H ≤ freeExtractionResidual G pick T)
    (hR : R ≤ freeExtractionResidual G pick T)
    (hsplit : freeExtractionResidual G pick T = H ⊔ R)
    (Cstar : H.EdgeLabeling (Fin s))
    (hCstar : AvoidsMonochromaticCopy (pathGraph n) Cstar) :
    ∃ C : (G \ R).EdgeLabeling (Fin (T + s)),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  apply exists_fin_path_avoidingColoring_of_cover
    (G \ R) (pathLowerRoundCoverFamily G pick T H R)
      (freeExtractionCoverBudget T s) hn
  · exact pathLowerRoundCoverFamily_le G pick hsub T hH hR
  · exact pathLowerRoundCoverFamily_covers G pick hsub T H R hsplit
  · intro i
    rcases i with t | u
    · dsimp only [pathLowerRoundCoverFamily,
        freeExtractionCoverBudget]
      exact exists_oneColor_avoidingColoring_of_free
        (pathGraph n) _ (hfree _)
    · dsimp only [pathLowerRoundCoverFamily,
        freeExtractionCoverBudget]
      exact exists_avoidingColoring_of_le sdiff_le Cstar hCstar
  · simpa only [sum_freeExtractionCoverBudget] using
      (le_refl (T + s))

/-! ## The complete deterministic round -/

/-- One generic deterministic BLS round.

The only analytic inputs are the fixed fractional gain and the final
geometric-power inequality.  All decomposition, degree, cover, and colour
bookkeeping conclusions are proved internally. -/
theorem exists_pathLowerRound
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ Q, pick Q ≤ Q)
    {n s : ℕ} (hs : 0 < s) (hn : 12 ≤ n)
    (hfree : ∀ Q, (pathGraph n).Free (pick Q))
    {a threshold : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hgain : ∀ t,
      threshold <
          (edgeCount (freeExtractionResidual G pick t) : ℝ) →
        a * (edgeCount (freeExtractionResidual G pick t) : ℝ) ≤
          (edgeCount (freeExtractionPiece G pick t) : ℝ))
    (T : ℕ)
    (hpower : (1 - a) ^ T * (edgeCount G : ℝ) ≤ threshold) :
    let F := freeExtractionResidual G pick T
    ∃ H R : SimpleGraph V,
      (edgeCount F : ℝ) ≤ threshold ∧
      H ≤ F ∧ R ≤ F ∧ R ≤ G ∧ F = H ⊔ R ∧
      (∀ v, Nat.card (R.neighborSet v) ≤
        8 * edgeCount F / (n * s)) ∧
      ∃ C : (G \ R).EdgeLabeling (Fin (T + s)),
        AvoidsMonochromaticCopy (pathGraph n) C := by
  let F := freeExtractionResidual G pick T
  have hFsmall : (edgeCount F : ℝ) ≤ threshold := by
    exact freeExtractionResidual_edgeCount_le_threshold
      G pick hsub ha0 ha1 hgain T hpower
  letI : DecidableRel F.Adj := Classical.decRel _
  obtain ⟨H, R, hHF, hRF, hsplit, hRdegree, Cstar, hCstar⟩ :=
    exists_starTypeDecomposition F hs hn
  have hRinitial : R ≤ G := by
    exact hRF.trans (freeExtractionResidual_le G pick T)
  have hroundColoring :
      ∃ C : (G \ R).EdgeLabeling (Fin (T + s)),
        AvoidsMonochromaticCopy (pathGraph n) C := by
    exact exists_path_avoidingColoring_of_round_cover
      G pick hsub (by omega) hfree
        (by simpa only [F] using hHF)
        (by simpa only [F] using hRF)
        (by simpa only [F] using hsplit)
        Cstar hCstar
  exact ⟨H, R, hFsmall, hHF, hRF, hRinitial, hsplit,
    hRdegree, hroundColoring⟩

end

end LeanCo.SizeRamsey
