import LeanCo.SizeRamsey.PathLowerBound
import Mathlib.Data.Fintype.EquivFin

/-!
# Gluing avoiding edge colourings

This file supplies the colour-bookkeeping used between rounds of the BLS
path lower-bound argument.  A cover is first coloured by its member index;
inside each selected member we use that member's own avoiding colouring.
The resulting dependent sum of local colour sets is then injected into a
common final palette.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u v w z

variable {V : Type u} {I : Type v} {W : Type w} {K : Type z}

/-! ## The dependent-sum colouring -/

/-- Refine the member index chosen by `coloringOfCover` with the local colour
of that edge inside the chosen member. -/
def sigmaColoringOfCover
    (G : SimpleGraph V) (P : I → SimpleGraph V) (budget : I → ℕ)
    (hcover : EdgesCoveredBy G P)
    (localColoring : ∀ i, (P i).EdgeLabeling (Fin (budget i))) :
    G.EdgeLabeling (Σ i, Fin (budget i)) :=
  fun e =>
    let i := coloringOfCover G P hcover e
    ⟨i, localColoring i
      ⟨e.1, coloringOfCover_edge_mem G P hcover e⟩⟩

/-- A dependent-sum colour class is contained in the corresponding local
colour class. -/
theorem labelGraph_sigmaColoringOfCover_le
    (G : SimpleGraph V) (P : I → SimpleGraph V) (budget : I → ℕ)
    (hcover : EdgesCoveredBy G P)
    (localColoring : ∀ i, (P i).EdgeLabeling (Fin (budget i)))
    (i : I) (c : Fin (budget i)) :
    (sigmaColoringOfCover G P budget hcover localColoring).labelGraph ⟨i, c⟩ ≤
      (localColoring i).labelGraph c := by
  intro x y hxy
  rw [EdgeLabeling.labelGraph_adj] at hxy ⊢
  obtain ⟨hG, hlabel⟩ := hxy
  let e : G.edgeSet := ⟨s(x, y), hG⟩
  let k : I := coloringOfCover G P hcover e
  have hmem : e.1 ∈ (P k).edgeSet :=
    coloringOfCover_edge_mem G P hcover e
  let ep : (P k).edgeSet := ⟨e.1, hmem⟩
  change (⟨k, localColoring k ep⟩ : Σ i, Fin (budget i)) = ⟨i, c⟩ at hlabel
  have hki : k = i := congrArg Sigma.fst hlabel
  subst i
  have hc : localColoring k ep = c :=
    eq_of_heq (Sigma.mk.inj_iff.mp hlabel).2
  let hP : (P k).Adj x y := by
    simpa only [mem_edgeSet, e] using hmem
  refine ⟨hP, ?_⟩
  simpa only [ep, e] using hc

/-- Local avoiding colourings on a covering family glue to one avoiding
colouring with dependent-sum palette.  The subgraph hypotheses are retained
in the interface because the rounds produce contained pieces, although the
edge-cover property alone is sufficient for the glue construction itself. -/
theorem exists_sigma_avoidingColoring_of_cover
    [Fintype I]
    (F : SimpleGraph W) (G : SimpleGraph V)
    (P : I → SimpleGraph V) (budget : I → ℕ)
    (_hsub : ∀ i, P i ≤ G)
    (hcover : EdgesCoveredBy G P)
    (hlocal : ∀ i, ∃ C : (P i).EdgeLabeling (Fin (budget i)),
      AvoidsMonochromaticCopy F C) :
    ∃ C : G.EdgeLabeling (Σ i, Fin (budget i)),
      AvoidsMonochromaticCopy F C := by
  choose localColoring hlocalAvoids using hlocal
  let C := sigmaColoringOfCover G P budget hcover localColoring
  refine ⟨C, ?_⟩
  intro color
  rcases color with ⟨i, c⟩
  intro hcopy
  exact hlocalAvoids i c
    (hcopy.trans_le (labelGraph_sigmaColoringOfCover_le
      G P budget hcover localColoring i c))

/-! ## Injective relabelling -/

/-- At a label in the image of an injective relabelling, the new colour
class is exactly the old colour class. -/
theorem labelGraph_compRight_eq_of_injective
    {G : SimpleGraph V} (C : G.EdgeLabeling K)
    {L : Type*} (f : K → L) (hf : Function.Injective f) (k : K) :
    (C.compRight f).labelGraph (f k) = C.labelGraph k := by
  ext x y
  simp only [EdgeLabeling.labelGraph_adj, EdgeLabeling.compRight_apply]
  constructor
  · rintro ⟨hG, hk⟩
    exact ⟨hG, hf hk⟩
  · rintro ⟨hG, hk⟩
    exact ⟨hG, congrArg f hk⟩

/-- A target label outside the image of a relabelling has empty colour
class. -/
theorem labelGraph_compRight_eq_bot_of_not_mem_range
    {G : SimpleGraph V} (C : G.EdgeLabeling K)
    {L : Type*} (f : K → L) {l : L} (hl : l ∉ Set.range f) :
    (C.compRight f).labelGraph l = (⊥ : SimpleGraph V) := by
  ext x y
  simp only [EdgeLabeling.labelGraph_adj, EdgeLabeling.compRight_apply,
    bot_adj, iff_false]
  rintro ⟨hG, heq⟩
  exact hl ⟨C ⟨s(x, y), hG⟩, heq⟩

/-- Injective relabelling preserves avoidance.  The explicit `F ≠ ⊥`
hypothesis is necessary for target labels outside the image: their colour
graph is `⊥`, and the empty forbidden graph is contained in `⊥`. -/
theorem avoiding_compRight_of_injective
    {F : SimpleGraph W} {G : SimpleGraph V}
    (hF : F ≠ ⊥) (C : G.EdgeLabeling K)
    (hC : AvoidsMonochromaticCopy F C)
    {L : Type*} (f : K → L) (hf : Function.Injective f) :
    AvoidsMonochromaticCopy F (C.compRight f) := by
  intro l
  by_cases hl : l ∈ Set.range f
  · obtain ⟨k, rfl⟩ := hl
    rw [labelGraph_compRight_eq_of_injective C f hf k]
    exact hC k
  · rw [labelGraph_compRight_eq_bot_of_not_mem_range C f hl]
    exact free_bot hF

/-! ## Packing the dependent palette into `Fin r` -/

/-- A dependent palette whose total cardinality is at most `r` embeds into
`Fin r`; composing with this embedding preserves avoidance. -/
theorem exists_fin_avoidingColoring_of_sigma
    [Fintype I] {budget : I → ℕ}
    {F : SimpleGraph W} {G : SimpleGraph V}
    (hF : F ≠ ⊥)
    (C : G.EdgeLabeling (Σ i, Fin (budget i)))
    (hC : AvoidsMonochromaticCopy F C)
    {r : ℕ} (hbudget : ∑ i, budget i ≤ r) :
    ∃ D : G.EdgeLabeling (Fin r), AvoidsMonochromaticCopy F D := by
  have hcard :
      Fintype.card (Σ i, Fin (budget i)) ≤ Fintype.card (Fin r) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hbudget
  let emb : (Σ i, Fin (budget i)) ↪ Fin r :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  exact ⟨C.compRight emb, avoiding_compRight_of_injective
    hF C hC emb emb.injective⟩

/-- Complete generic rounds interface: glue all local avoiding colourings and
pack their dependent palette into `Fin r`. -/
theorem exists_fin_avoidingColoring_of_cover
    [Fintype I]
    (F : SimpleGraph W) (G : SimpleGraph V)
    (P : I → SimpleGraph V) (budget : I → ℕ)
    (hF : F ≠ ⊥)
    (hsub : ∀ i, P i ≤ G)
    (hcover : EdgesCoveredBy G P)
    (hlocal : ∀ i, ∃ C : (P i).EdgeLabeling (Fin (budget i)),
      AvoidsMonochromaticCopy F C)
    {r : ℕ} (hbudget : ∑ i, budget i ≤ r) :
    ∃ C : G.EdgeLabeling (Fin r), AvoidsMonochromaticCopy F C := by
  obtain ⟨C, hC⟩ := exists_sigma_avoidingColoring_of_cover
    F G P budget hsub hcover hlocal
  exact exists_fin_avoidingColoring_of_sigma hF C hC hbudget

/-! ## Path wrapper -/

/-- A path on at least two vertices is not the empty graph. -/
theorem pathGraph_ne_bot_of_two_le_glue {n : ℕ} (hn : 2 ≤ n) :
    pathGraph n ≠ ⊥ := by
  intro hbot
  have hp : (pathGraph n).Adj
      (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) := by
    rw [pathGraph_adj]
    exact Or.inl rfl
  rw [hbot] at hp
  exact hp

/-- Final path-specific wrapper used by the rounds argument. -/
theorem exists_fin_path_avoidingColoring_of_cover
    [Fintype I]
    (G : SimpleGraph V) (P : I → SimpleGraph V) (budget : I → ℕ)
    {n r : ℕ} (hn : 2 ≤ n)
    (hsub : ∀ i, P i ≤ G)
    (hcover : EdgesCoveredBy G P)
    (hlocal : ∀ i, ∃ C : (P i).EdgeLabeling (Fin (budget i)),
      AvoidsMonochromaticCopy (pathGraph n) C)
    (hbudget : ∑ i, budget i ≤ r) :
    ∃ C : G.EdgeLabeling (Fin r),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  exact exists_fin_avoidingColoring_of_cover
    (pathGraph n) G P budget (pathGraph_ne_bot_of_two_le_glue hn)
      hsub hcover hlocal hbudget

end

end LeanCo.SizeRamsey
