import LeanCo.SizeRamsey.ApproxRegularPeeling

/-!
# Iterating fractional free-subgraph extraction

The BLS lower-bound proof repeatedly removes a forbidden-copy-free subgraph
which contains a fixed fraction of the current edge mass.  This file records
the deterministic iteration once and for all.  It is deliberately independent
of the particular Key Lemma and of the later colour bookkeeping.

If the final residual is still above a stopping threshold, then every earlier
residual was above that threshold as well.  Consequently the fractional gain
hypothesis applies at every preceding step and gives the expected geometric
decay.  A separate corollary turns a numerical power bound into termination
below the threshold.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- Residual graph after repeatedly removing `pick` from the current graph. -/
def freeExtractionResidual (G : SimpleGraph V)
    (pick : SimpleGraph V → SimpleGraph V) : ℕ → SimpleGraph V
  | 0 => G
  | t + 1 =>
      freeExtractionResidual G pick t \ pick (freeExtractionResidual G pick t)

/-- The piece selected at extraction step `t`. -/
def freeExtractionPiece (G : SimpleGraph V)
    (pick : SimpleGraph V → SimpleGraph V) (t : ℕ) : SimpleGraph V :=
  pick (freeExtractionResidual G pick t)

/-- Union of the pieces selected before time `t`. -/
def freeExtractionAccumulated (G : SimpleGraph V)
    (pick : SimpleGraph V → SimpleGraph V) : ℕ → SimpleGraph V
  | 0 => ⊥
  | t + 1 =>
      freeExtractionAccumulated G pick t ⊔ freeExtractionPiece G pick t

@[simp]
theorem freeExtractionResidual_zero (G : SimpleGraph V)
    (pick : SimpleGraph V → SimpleGraph V) :
    freeExtractionResidual G pick 0 = G := rfl

@[simp]
theorem freeExtractionResidual_succ (G : SimpleGraph V)
    (pick : SimpleGraph V → SimpleGraph V) (t : ℕ) :
    freeExtractionResidual G pick (t + 1) =
      freeExtractionResidual G pick t \ freeExtractionPiece G pick t := rfl

theorem freeExtractionPiece_le_residual
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R) (t : ℕ) :
    freeExtractionPiece G pick t ≤ freeExtractionResidual G pick t := by
  exact hsub _

theorem freeExtractionResidual_succ_le
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V) (t : ℕ) :
    freeExtractionResidual G pick (t + 1) ≤
      freeExtractionResidual G pick t := by
  rw [freeExtractionResidual_succ]
  exact sdiff_le

/-- Every residual remains a subgraph of the initial graph. -/
theorem freeExtractionResidual_le
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V) (t : ℕ) :
    freeExtractionResidual G pick t ≤ G := by
  induction t with
  | zero => simp
  | succ t ih =>
      exact (freeExtractionResidual_succ_le G pick t).trans ih

/-- The residual at a later time is contained in every earlier residual. -/
theorem freeExtractionResidual_antitone
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V) :
    Antitone (freeExtractionResidual G pick) := by
  apply antitone_nat_of_succ_le
  intro t
  simpa only [Nat.succ_eq_add_one] using
    freeExtractionResidual_succ_le G pick t

/-- One extraction step is an exact edge-disjoint decomposition. -/
theorem freeExtractionResidual_eq_piece_sup_succ
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R) (t : ℕ) :
    freeExtractionResidual G pick t =
      freeExtractionPiece G pick t ⊔
        freeExtractionResidual G pick (t + 1) := by
  rw [freeExtractionResidual_succ]
  exact (sup_sdiff_cancel_right
    (freeExtractionPiece_le_residual G pick hsub t)).symm

@[simp]
theorem freeExtractionAccumulated_zero (G : SimpleGraph V)
    (pick : SimpleGraph V → SimpleGraph V) :
    freeExtractionAccumulated G pick 0 = ⊥ := rfl

@[simp]
theorem freeExtractionAccumulated_succ (G : SimpleGraph V)
    (pick : SimpleGraph V → SimpleGraph V) (t : ℕ) :
    freeExtractionAccumulated G pick (t + 1) =
      freeExtractionAccumulated G pick t ⊔ freeExtractionPiece G pick t := rfl

/-- At every time, the initial graph is exactly the union of all pieces
already selected and the current residual. -/
theorem freeExtraction_eq_accumulated_sup_residual
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R) (t : ℕ) :
    G = freeExtractionAccumulated G pick t ⊔
      freeExtractionResidual G pick t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [freeExtractionAccumulated_succ]
      rw [freeExtractionResidual_eq_piece_sup_succ G pick hsub t] at ih
      calc
        G = freeExtractionAccumulated G pick t ⊔
              (freeExtractionPiece G pick t ⊔
                freeExtractionResidual G pick (t + 1)) := ih
        _ = (freeExtractionAccumulated G pick t ⊔
              freeExtractionPiece G pick t) ⊔
                freeExtractionResidual G pick (t + 1) := by
          rw [sup_assoc]

/-- Every selected piece is a subgraph of the initial graph. -/
theorem freeExtractionPiece_le_initial
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R) (t : ℕ) :
    freeExtractionPiece G pick t ≤ G :=
  (freeExtractionPiece_le_residual G pick hsub t).trans
    (freeExtractionResidual_le G pick t)

/-- The accumulated removed graph is a subgraph of the initial graph. -/
theorem freeExtractionAccumulated_le
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R) (t : ℕ) :
    freeExtractionAccumulated G pick t ≤ G := by
  calc
    freeExtractionAccumulated G pick t ≤
        freeExtractionAccumulated G pick t ⊔
          freeExtractionResidual G pick t := le_sup_left
    _ = G := (freeExtraction_eq_accumulated_sup_residual
      G pick hsub t).symm

/-- Exact natural edge-count recurrence for one extraction step. -/
theorem freeExtractionResidual_edgeCount_step
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R) (t : ℕ) :
    edgeCount (freeExtractionResidual G pick t) =
      edgeCount (freeExtractionPiece G pick t) +
        edgeCount (freeExtractionResidual G pick (t + 1)) := by
  rw [freeExtractionResidual_succ]
  exact edgeCount_eq_add_edgeCount_sdiff _ _
    (freeExtractionPiece_le_residual G pick hsub t)

/-- Edge counts of the residuals are non-increasing. -/
theorem freeExtractionResidual_edgeCount_antitone
    [Fintype V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V) :
    Antitone (fun t => edgeCount (freeExtractionResidual G pick t)) := by
  intro s t hst
  exact edgeCount_mono (freeExtractionResidual_antitone G pick hst)

/-- If the final residual is above the stopping threshold, fractional
extraction applied at every preceding step forces geometric decay. -/
theorem freeExtractionResidual_edgeCount_le_pow_of_final_gt
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R)
    {a threshold : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hgain : ∀ t,
      threshold < (edgeCount (freeExtractionResidual G pick t) : ℝ) →
        a * (edgeCount (freeExtractionResidual G pick t) : ℝ) ≤
          (edgeCount (freeExtractionPiece G pick t) : ℝ))
    (T : ℕ)
    (hfinal : threshold <
      (edgeCount (freeExtractionResidual G pick T) : ℝ)) :
    (edgeCount (freeExtractionResidual G pick T) : ℝ) ≤
      (1 - a) ^ T * (edgeCount G : ℝ) := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hstepNat := freeExtractionResidual_edgeCount_step
        G pick hsub T
      have hstep :
          (edgeCount (freeExtractionResidual G pick T) : ℝ) =
            (edgeCount (freeExtractionPiece G pick T) : ℝ) +
              (edgeCount (freeExtractionResidual G pick (T + 1)) : ℝ) := by
        exact_mod_cast hstepNat
      have hmonoNat :
          edgeCount (freeExtractionResidual G pick (T + 1)) ≤
            edgeCount (freeExtractionResidual G pick T) :=
        freeExtractionResidual_edgeCount_antitone G pick (Nat.le_succ T)
      have hmono :
          (edgeCount (freeExtractionResidual G pick (T + 1)) : ℝ) ≤
            (edgeCount (freeExtractionResidual G pick T) : ℝ) := by
        exact_mod_cast hmonoNat
      have hcurrent : threshold <
          (edgeCount (freeExtractionResidual G pick T) : ℝ) := by
        exact hfinal.trans_le hmono
      have hprevious := ih hcurrent
      have hgainT := hgain T hcurrent
      have hdecay :
          (edgeCount (freeExtractionResidual G pick (T + 1)) : ℝ) ≤
            (1 - a) *
              (edgeCount (freeExtractionResidual G pick T) : ℝ) := by
        nlinarith
      have honeMinus : 0 ≤ 1 - a := sub_nonneg.mpr ha1
      calc
        (edgeCount (freeExtractionResidual G pick (T + 1)) : ℝ) ≤
            (1 - a) *
              (edgeCount (freeExtractionResidual G pick T) : ℝ) := hdecay
        _ ≤ (1 - a) * ((1 - a) ^ T * (edgeCount G : ℝ)) :=
          mul_le_mul_of_nonneg_left hprevious honeMinus
        _ = (1 - a) ^ (T + 1) * (edgeCount G : ℝ) := by
          rw [pow_succ]
          ring

/-- Numerical termination wrapper: once the geometric upper bound is at
most the threshold, the actual residual is at most the threshold. -/
theorem freeExtractionResidual_edgeCount_le_threshold
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (pick : SimpleGraph V → SimpleGraph V)
    (hsub : ∀ R, pick R ≤ R)
    {a threshold : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hgain : ∀ t,
      threshold < (edgeCount (freeExtractionResidual G pick t) : ℝ) →
        a * (edgeCount (freeExtractionResidual G pick t) : ℝ) ≤
          (edgeCount (freeExtractionPiece G pick t) : ℝ))
    (T : ℕ)
    (hpower : (1 - a) ^ T * (edgeCount G : ℝ) ≤ threshold) :
    (edgeCount (freeExtractionResidual G pick T) : ℝ) ≤ threshold := by
  by_contra hnot
  have hfinal : threshold <
      (edgeCount (freeExtractionResidual G pick T) : ℝ) := lt_of_not_ge hnot
  have hdecay := freeExtractionResidual_edgeCount_le_pow_of_final_gt
    G pick hsub ha0 ha1 hgain T hfinal
  linarith

end

end LeanCo.SizeRamsey
