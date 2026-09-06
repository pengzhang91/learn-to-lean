import LeanCo.SizeRamsey.FreeExtractionIteration
import LeanCo.SizeRamsey.AvoidingColoringGlue

/-!
# Colouring the output of an extraction iteration

Every extracted graph is assigned one fresh colour.  The final residual may
use its own local palette.  The exact decomposition proved in
`FreeExtractionIteration` then supplies a cover of the initial graph, and
`AvoidingColoringGlue` packs the dependent local palettes into `Fin r`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- The covering family consisting of the first `T` extracted pieces and
the final residual. -/
def freeExtractionCoverFamily (G : SimpleGraph V)
    (pick : SimpleGraph V → SimpleGraph V) (T : ℕ) :
    Fin T ⊕ Unit → SimpleGraph V
  | Sum.inl t => freeExtractionPiece G pick t
  | Sum.inr _ => freeExtractionResidual G pick T

/-- One colour for every extracted piece and `s` colours for the residual. -/
def freeExtractionCoverBudget (T s : ℕ) : Fin T ⊕ Unit → ℕ
  | Sum.inl _ => 1
  | Sum.inr _ => s

/-- Adjacency in the accumulated graph is exactly adjacency in one of the
pieces selected at an earlier step. -/
theorem freeExtractionAccumulated_adj_iff
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (T : ℕ) (x y : V) :
    (freeExtractionAccumulated G pick T).Adj x y ↔
      ∃ t : ℕ, t < T ∧ (freeExtractionPiece G pick t).Adj x y := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [freeExtractionAccumulated_succ, sup_adj, ih]
      constructor
      · rintro (⟨t, ht, hxy⟩ | hxy)
        · exact ⟨t, by omega, hxy⟩
        · exact ⟨T, by omega, hxy⟩
      · rintro ⟨t, ht, hxy⟩
        by_cases hlast : t = T
        · right
          simpa only [hlast] using hxy
        · left
          exact ⟨t, by omega, hxy⟩

/-- The extracted pieces together with the final residual cover every edge
of the initial graph. -/
theorem freeExtractionCoverFamily_covers
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R) (T : ℕ) :
    EdgesCoveredBy G (freeExtractionCoverFamily G pick T) := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        simpa only [mem_edgeSet] using he
      have hdecomp := congrArg (fun H : SimpleGraph V => H.Adj x y)
        (freeExtraction_eq_accumulated_sup_residual G pick hsub T)
      have hright :
          (freeExtractionAccumulated G pick T).Adj x y ∨
            (freeExtractionResidual G pick T).Adj x y := by
        simpa only [sup_adj] using hdecomp.mp hxy
      rcases hright with hacc | hres
      · obtain ⟨t, ht, hpiece⟩ :=
          (freeExtractionAccumulated_adj_iff G pick T x y).mp hacc
        refine ⟨Sum.inl ⟨t, ht⟩, ?_⟩
        simpa only [freeExtractionCoverFamily, mem_edgeSet] using hpiece
      · refine ⟨Sum.inr (), ?_⟩
        simpa only [freeExtractionCoverFamily, mem_edgeSet] using hres

/-- Every member of the extraction cover is a subgraph of the initial
graph. -/
theorem freeExtractionCoverFamily_le
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R) (T : ℕ) :
    ∀ i, freeExtractionCoverFamily G pick T i ≤ G := by
  intro i
  rcases i with t | u
  · exact freeExtractionPiece_le_initial G pick hsub t
  · exact freeExtractionResidual_le G pick T

@[simp]
theorem sum_freeExtractionCoverBudget (T s : ℕ) :
    ∑ i : Fin T ⊕ Unit, freeExtractionCoverBudget T s i = T + s := by
  rw [Fintype.sum_sum_type]
  simp [freeExtractionCoverBudget]

/-- Any one-colour labelling of a free graph is avoiding. -/
theorem exists_oneColor_avoidingColoring_of_free
    {W : Type*} (F : SimpleGraph W) (G : SimpleGraph V)
    (hfree : F.Free G) :
    ∃ C : G.EdgeLabeling (Fin 1), AvoidsMonochromaticCopy F C := by
  let C : G.EdgeLabeling (Fin 1) := fun _ => 0
  refine ⟨C, ?_⟩
  intro c hcopy
  exact hfree (hcopy.trans_le C.labelGraph_le)

/-- Complete round-colouring wrapper.  Each extracted free piece costs one
colour; a supplied `s`-colour avoiding colouring handles the final residual.
All palettes are packed into the requested final `Fin r`. -/
theorem exists_path_avoidingColoring_of_extraction
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R)
    {T s n r : ℕ} (hn : 2 ≤ n)
    (hfree : ∀ t, t < T →
      (pathGraph n).Free (freeExtractionPiece G pick t))
    (hresidual : ∃ C :
      (freeExtractionResidual G pick T).EdgeLabeling (Fin s),
        AvoidsMonochromaticCopy (pathGraph n) C)
    (hbudget : T + s ≤ r) :
    ∃ C : G.EdgeLabeling (Fin r),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  let P := freeExtractionCoverFamily G pick T
  let budget := freeExtractionCoverBudget T s
  apply exists_fin_path_avoidingColoring_of_cover
    G P budget hn
  · exact freeExtractionCoverFamily_le G pick hsub T
  · exact freeExtractionCoverFamily_covers G pick hsub T
  · intro i
    rcases i with t | u
    · dsimp only [P, budget, freeExtractionCoverFamily,
        freeExtractionCoverBudget]
      exact exists_oneColor_avoidingColoring_of_free
        (pathGraph n) _ (hfree t t.isLt)
    · dsimp only [P, budget, freeExtractionCoverFamily,
        freeExtractionCoverBudget]
      exact hresidual
  · change (∑ i : Fin T ⊕ Unit,
      freeExtractionCoverBudget T s i) ≤ r
    simpa only [sum_freeExtractionCoverBudget] using hbudget

end

end LeanCo.SizeRamsey
