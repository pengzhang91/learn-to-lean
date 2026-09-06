import LeanCo.SizeRamsey.ConditionalExtractionIteration
import LeanCo.SizeRamsey.PathLowerRound

/-!
# One BLS round with the low-degree stopping alternative

The Key Lemma gain is only needed while the residual has sufficiently large
maximum degree.  A fixed extraction block therefore has two legitimate
outcomes: the target edge mass is reached and star cleanup prepares the next
round, or the degree predicate fails and the extraction difference is already
coloured.  This is the exact logical alternative used by the terminal phase.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- The first `T` free pieces colour exactly the difference between the
initial graph and the final residual, with no colour spent on that residual. -/
theorem exists_path_avoidingColoring_of_extracted_difference
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ Q, pick Q ≤ Q)
    {T n : ℕ} (hn : 2 ≤ n)
    (hfree : ∀ Q, (pathGraph n).Free (pick Q)) :
    ∃ C : (G \ freeExtractionResidual G pick T).EdgeLabeling (Fin T),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  let Cbot : (⊥ : SimpleGraph V).EdgeLabeling (Fin 0) := fun e => by
    have : False := by simpa using e.property
    exact this.elim
  have hCbot : AvoidsMonochromaticCopy (pathGraph n) Cbot :=
    fun c ↦ Fin.elim0 c
  simpa using
    (exists_path_avoidingColoring_of_round_cover
      G pick hsub (T := T) (s := 0) (n := n) hn hfree
      (H := (⊥ : SimpleGraph V))
      (R := freeExtractionResidual G pick T)
      bot_le le_rfl (by simp) Cbot hCbot)

/-- One conditional extraction round.

In the small-edge branch, `R` is the star-cleaned residual for the next
round.  In the other branch, the final extraction residual fails `Good` and
the whole difference leading to it has already been coloured with `T`
colours. -/
theorem exists_pathLowerConditionalRound
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ Q, pick Q ≤ Q)
    (Good : SimpleGraph V → Prop)
    (hGoodUp : ∀ {A B : SimpleGraph V}, A ≤ B → Good A → Good B)
    {n s : ℕ} (hs : 0 < s) (hn : 12 ≤ n)
    (hfree : ∀ Q, (pathGraph n).Free (pick Q))
    {a threshold : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hgain : ∀ t, Good (freeExtractionResidual G pick t) →
      threshold <
          (edgeCount (freeExtractionResidual G pick t) : ℝ) →
        a * (edgeCount (freeExtractionResidual G pick t) : ℝ) ≤
          (edgeCount (freeExtractionPiece G pick t) : ℝ))
    (T : ℕ)
    (hpower : (1 - a) ^ T * (edgeCount G : ℝ) ≤ threshold) :
    let F := freeExtractionResidual G pick T
    ((edgeCount F : ℝ) ≤ threshold ∧
      ∃ H R : SimpleGraph V,
        H ≤ F ∧ R ≤ F ∧ R ≤ G ∧ F = H ⊔ R ∧
        (∀ v, Nat.card (R.neighborSet v) ≤
          8 * edgeCount F / (n * s)) ∧
        ∃ C : (G \ R).EdgeLabeling (Fin (T + s)),
          AvoidsMonochromaticCopy (pathGraph n) C) ∨
    (¬ Good F ∧
      ∃ C : (G \ F).EdgeLabeling (Fin T),
        AvoidsMonochromaticCopy (pathGraph n) C) := by
  dsimp only
  have hstop := freeExtractionResidual_small_or_not_good
    G pick hsub Good hGoodUp ha0 ha1 hgain T hpower
  rcases hstop with hsmall | hnotGood
  · left
    refine ⟨hsmall, ?_⟩
    let F := freeExtractionResidual G pick T
    letI : DecidableRel F.Adj := Classical.decRel _
    obtain ⟨H, R, hHF, hRF, hsplit, hRdegree, Cstar, hCstar⟩ :=
      exists_starTypeDecomposition F hs hn
    have hRinitial : R ≤ G :=
      hRF.trans (freeExtractionResidual_le G pick T)
    have hroundColoring :
        ∃ C : (G \ R).EdgeLabeling (Fin (T + s)),
          AvoidsMonochromaticCopy (pathGraph n) C := by
      exact exists_path_avoidingColoring_of_round_cover
        G pick hsub (T := T) (s := s) (n := n) (by omega) hfree
          (by simpa only [F] using hHF)
          (by simpa only [F] using hRF)
          (by simpa only [F] using hsplit)
          Cstar hCstar
    exact ⟨H, R, hHF, hRF, hRinitial, hsplit, hRdegree,
      hroundColoring⟩
  · right
    exact ⟨hnotGood,
      exists_path_avoidingColoring_of_extracted_difference
        G pick hsub (by omega) hfree⟩

end

end LeanCo.SizeRamsey
