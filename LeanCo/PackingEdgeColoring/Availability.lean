import LeanCo.PackingEdgeColoring.LocalColoring
import LeanCo.PackingEdgeColoring.MaximumAverageDegree

/-!
# Counting available induced colours

The reducibility arguments repeatedly say that an uncoloured edge sees fewer
than `k` already-coloured edges and therefore has an available radius-two
colour.  This file packages that pigeonhole step without referring to a
particular local configuration.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Induced colours which cannot currently be assigned to `e`. -/
noncomputable def blockedInducedColorsOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i ↦
    ¬ ColorAvailableOn G D colour e (some i)

/-- Currently relevant edges which are not induced-separated from `e`.
Every blocked induced colour is witnessed by an edge in this finite set. -/
noncomputable def inducedBlockerEdgesOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) :
    Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun f ↦
    f ∈ D ∧ f ≠ e ∧ ¬ InducedSeparated G e f

@[simp] theorem mem_blockedInducedColorsOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) (i : Fin k) :
    i ∈ blockedInducedColorsOn G D colour e ↔
      ¬ ColorAvailableOn G D colour e (some i) := by
  classical
  simp [blockedInducedColorsOn]

@[simp] theorem mem_inducedBlockerEdgesOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e f : G.edgeSet) :
    f ∈ inducedBlockerEdgesOn G D colour e ↔
      f ∈ D ∧ f ≠ e ∧ ¬ InducedSeparated G e f := by
  classical
  simp [inducedBlockerEdgesOn]

/-- A blocked induced colour has a same-coloured incompatible witness. -/
theorem exists_blocker_of_mem_blockedInducedColorsOn {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet) {i : Fin k}
    (hi : i ∈ blockedInducedColorsOn G D colour e) :
    ∃ f ∈ inducedBlockerEdgesOn G D colour e, colour f = some i := by
  classical
  have hnot : ¬ ColorAvailableOn G D colour e (some i) :=
    (mem_blockedInducedColorsOn G D colour e i).mp hi
  rw [colorAvailableOn_some_iff] at hnot
  push_neg at hnot
  obtain ⟨f, hfD, hfe, hcolour, hsep⟩ := hnot
  exact ⟨f,
    (mem_inducedBlockerEdgesOn G D colour e f).mpr ⟨hfD, hfe, hsep⟩,
    hcolour⟩

/-- Different blocked colours require different witnessing edges, so the
number of blocked induced colours is at most the number of blocker edges. -/
theorem card_blockedInducedColorsOn_le_card_inducedBlockerEdgesOn {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet) :
    (blockedInducedColorsOn G D colour e).card ≤
      (inducedBlockerEdgesOn G D colour e).card := by
  classical
  let A := {i : Fin k // i ∈ blockedInducedColorsOn G D colour e}
  let B := {f : G.edgeSet // f ∈ inducedBlockerEdgesOn G D colour e}
  let R : A → B → Prop := fun i f ↦ colour f.1 = some i.1
  letI : DecidableRel R := fun _ _ ↦ Classical.propDecidable _
  have hleft : ∀ i : A,
      1 ≤ (Finset.univ.filter fun f : B ↦ R i f).card := by
    intro i
    obtain ⟨f, hf, hcolour⟩ :=
      exists_blocker_of_mem_blockedInducedColorsOn G D colour e i.2
    apply Finset.card_pos.mpr
    exact ⟨⟨f, hf⟩, by simp [R, hcolour]⟩
  have hright : ∀ f : B,
      (Finset.univ.filter fun i : A ↦ R i f).card ≤ 1 := by
    intro f
    apply Finset.card_le_one_iff.mpr
    intro i j hi hj
    apply Subtype.ext
    have hi' : colour f.1 = some i.1 := by simpa [R] using hi
    have hj' : colour f.1 = some j.1 := by simpa [R] using hj
    exact Option.some.inj (hi'.symm.trans hj')
  have hcount := mul_card_le_mul_card_of_relation R 1 1 hleft hright
  have hA : Fintype.card A =
      (blockedInducedColorsOn G D colour e).card := by
    simpa only [A] using
      (Fintype.card_coe (blockedInducedColorsOn G D colour e))
  have hB : Fintype.card B =
      (inducedBlockerEdgesOn G D colour e).card := by
    simpa only [B] using
      (Fintype.card_coe (inducedBlockerEdgesOn G D colour e))
  rw [hA, hB] at hcount
  simpa only [Nat.one_mul] using hcount

/-- Fewer than `k` blocked colours leave an available induced colour. -/
theorem exists_available_induced_of_card_blocked_lt {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet)
    (hcard : (blockedInducedColorsOn G D colour e).card < k) :
    ∃ i : Fin k, ColorAvailableOn G D colour e (some i) := by
  classical
  by_contra hnone
  push_neg at hnone
  have hall : blockedInducedColorsOn G D colour e = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact (mem_blockedInducedColorsOn G D colour e i).mpr (hnone i)
  rw [hall, Finset.card_univ] at hcard
  simpa using hcard

/-- The standard paper step: if fewer than `k` relevant edges can block
`e`, some induced colour is available. -/
theorem exists_available_induced_of_card_blockers_lt {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet)
    (hcard : (inducedBlockerEdgesOn G D colour e).card < k) :
    ∃ i : Fin k, ColorAvailableOn G D colour e (some i) := by
  apply exists_available_induced_of_card_blocked_lt G D colour e
  exact lt_of_le_of_lt
    (card_blockedInducedColorsOn_le_card_inducedBlockerEdgesOn G D colour e)
    hcard

/-- A user-supplied finite neighbourhood may over-approximate all blocker
edges; its cardinality alone then guarantees an available induced colour. -/
theorem exists_available_induced_of_blockers_subset {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k)
    (e : G.edgeSet) (S : Finset G.edgeSet)
    (hsub : inducedBlockerEdgesOn G D colour e ⊆ S)
    (hcard : S.card < k) :
    ∃ i : Fin k, ColorAvailableOn G D colour e (some i) := by
  apply exists_available_induced_of_card_blockers_lt G D colour e
  exact lt_of_le_of_lt (Finset.card_le_card hsub) hcard

/-- Extend a valid partial colouring across one fresh edge whenever fewer
than `k` existing edges can block its induced colours. -/
theorem IsOneTwoColoringOn.extend_one_induced_of_card_blockers_lt {k : ℕ}
    [DecidableEq G.edgeSet]
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor k}
    {e : G.edgeSet}
    (hcolour : IsOneTwoColoringOn G D colour) (he : e ∉ D)
    (hcard : (inducedBlockerEdgesOn G D colour e).card < k) :
    ∃ i : Fin k,
      IsOneTwoColoringOn G (insert e D) (recolor G colour e (some i)) := by
  obtain ⟨i, hi⟩ :=
    exists_available_induced_of_card_blockers_lt G D colour e hcard
  exact ⟨i, hcolour.extend_one G he hi⟩

/-- Variant with an explicit finite over-approximation of the blocking
neighbourhood. -/
theorem IsOneTwoColoringOn.extend_one_induced_of_blockers_subset {k : ℕ}
    [DecidableEq G.edgeSet]
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor k}
    {e : G.edgeSet} (S : Finset G.edgeSet)
    (hcolour : IsOneTwoColoringOn G D colour) (he : e ∉ D)
    (hsub : inducedBlockerEdgesOn G D colour e ⊆ S)
    (hcard : S.card < k) :
    ∃ i : Fin k,
      IsOneTwoColoringOn G (insert e D) (recolor G colour e (some i)) := by
  obtain ⟨i, hi⟩ :=
    exists_available_induced_of_blockers_subset G D colour e S hsub hcard
  exact ⟨i, hcolour.extend_one G he hi⟩

end Finite

end

end LeanCo.PackingEdgeColoring
