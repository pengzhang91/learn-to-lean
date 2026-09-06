import LeanCo.PackingEdgeColoring.Availability

/-!
# Multiplicity refinements for available induced colours

Several recolouring cases need two choices, or one choice avoiding a small
forbidden set.  This file upgrades the one-colour pigeonhole lemma to those
forms while keeping the exact blocker set visible.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Induced colours presently available for an edge. -/
noncomputable def availableInducedColorsOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i ↦
    ColorAvailableOn G D colour e (some i)

@[simp] theorem mem_availableInducedColorsOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) (i : Fin k) :
    i ∈ availableInducedColorsOn G D colour e ↔
      ColorAvailableOn G D colour e (some i) := by
  classical
  simp [availableInducedColorsOn]

/-- Available and blocked colours form an exact partition of the palette. -/
theorem availableInducedColorsOn_eq_sdiff {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) :
    availableInducedColorsOn G D colour e =
      Finset.univ \ blockedInducedColorsOn G D colour e := by
  classical
  ext i
  simp [availableInducedColorsOn]

/-- Exact cardinality partition of the palette. -/
theorem card_available_add_card_blocked {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) :
    (availableInducedColorsOn G D colour e).card +
      (blockedInducedColorsOn G D colour e).card = k := by
  classical
  rw [availableInducedColorsOn_eq_sdiff]
  simpa using Finset.card_sdiff_add_card_eq_card
    (show blockedInducedColorsOn G D colour e ⊆
        (Finset.univ : Finset (Fin k)) from Finset.subset_univ _)

/-- A blocker bound two below the palette size leaves two distinct available
induced colours. -/
theorem exists_two_distinct_available_induced_of_card_blocked_add_two_le
    {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (hcard : (blockedInducedColorsOn G D colour e).card + 2 ≤ k) :
    ∃ i j : Fin k, i ≠ j ∧
      ColorAvailableOn G D colour e (some i) ∧
      ColorAvailableOn G D colour e (some j) := by
  classical
  have hpartition := card_available_add_card_blocked G D colour e
  have havail : 1 < (availableInducedColorsOn G D colour e).card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp havail
  exact ⟨i, j, hij,
    (mem_availableInducedColorsOn G D colour e i).mp hi,
    (mem_availableInducedColorsOn G D colour e j).mp hj⟩

/-- The corresponding statement from an edge-blocker bound. -/
theorem exists_two_distinct_available_induced_of_card_blockers_add_two_le
    {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (hcard : (inducedBlockerEdgesOn G D colour e).card + 2 ≤ k) :
    ∃ i j : Fin k, i ≠ j ∧
      ColorAvailableOn G D colour e (some i) ∧
      ColorAvailableOn G D colour e (some j) := by
  apply exists_two_distinct_available_induced_of_card_blocked_add_two_le
    G D colour e
  have hle :=
    card_blockedInducedColorsOn_le_card_inducedBlockerEdgesOn G D colour e
  omega

/-- More generally, if blockers plus an explicitly forbidden colour set do
not fill the palette, there is an available colour outside that set. -/
theorem exists_available_induced_not_mem_of_card_blocked_add_card_lt
    {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (T : Finset (Fin k))
    (hcard : (blockedInducedColorsOn G D colour e).card + T.card < k) :
    ∃ i : Fin k, ColorAvailableOn G D colour e (some i) ∧ i ∉ T := by
  classical
  have hpartition := card_available_add_card_blocked G D colour e
  have hlt : T.card < (availableInducedColorsOn G D colour e).card := by omega
  have hnsub : ¬ availableInducedColorsOn G D colour e ⊆ T := by
    intro hsub
    exact (not_le_of_gt hlt) (Finset.card_le_card hsub)
  obtain ⟨i, hi, hiT⟩ := Finset.not_subset.mp hnsub
  exact ⟨i, (mem_availableInducedColorsOn G D colour e i).mp hi, hiT⟩

/-- Edge-blocker version of the avoid-a-small-set lemma. -/
theorem exists_available_induced_not_mem_of_card_blockers_add_card_lt
    {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (T : Finset (Fin k))
    (hcard : (inducedBlockerEdgesOn G D colour e).card + T.card < k) :
    ∃ i : Fin k, ColorAvailableOn G D colour e (some i) ∧ i ∉ T := by
  apply exists_available_induced_not_mem_of_card_blocked_add_card_lt
    G D colour e T
  have hle :=
    card_blockedInducedColorsOn_le_card_inducedBlockerEdgesOn G D colour e
  omega

end Finite

end

end LeanCo.PackingEdgeColoring
