import LeanCo.SizeRamsey.Defs
import Mathlib.Combinatorics.Pigeonhole

/-!
# The majority colour class

The upper-bound proof begins by retaining the largest colour class.  This
file proves the exact finite counting statement, including the bridge from a
fibre of an `EdgeLabeling` to the edge set of its `labelGraph`.
-/

open Finset

namespace LeanCo.SizeRamsey

open SimpleGraph

universe u v

/-- Some fibre of a map between nonempty finite sets contains at least its
proportional share of the domain.  The multiplication form avoids division
and all rounding issues. -/
theorem exists_card_le_card_mul_fiber
    {α : Type u} {κ : Type v} [DecidableEq α] [DecidableEq κ]
    (s : Finset α) (t : Finset κ) (ht : t.Nonempty) (f : α → κ)
    (hf : ∀ x ∈ s, f x ∈ t) :
    ∃ c ∈ t, s.card ≤ t.card * #{x ∈ s | f x = c} := by
  by_contra h
  push Not at h
  have hstrict :
      (∑ c ∈ t, t.card * #{x ∈ s | f x = c}) <
        ∑ _c ∈ t, s.card := by
    exact Finset.sum_lt_sum_of_nonempty ht fun c hc ↦ h c hc
  have hfibers : s.card = ∑ c ∈ t, #{x ∈ s | f x = c} :=
    Finset.card_eq_sum_card_fiberwise hf
  have hleft :
      (∑ c ∈ t, t.card * #{x ∈ s | f x = c}) = t.card * s.card := by
    rw [hfibers]
    simp only [Finset.mul_sum]
  have hright : (∑ _c ∈ t, s.card) = t.card * s.card := by
    simp
  rw [hleft, hright] at hstrict
  exact (lt_irrefl _ hstrict)

section LabelGraph

variable {V : Type u} {K : Type v} {G : SimpleGraph V}

/-- Membership in the edge set of a label graph is literal membership in the
corresponding fibre of the edge labelling. -/
theorem mem_labelGraph_edgeSet_iff (C : G.EdgeLabeling K) (c : K) (e : Sym2 V) :
    e ∈ (C.labelGraph c).edgeSet ↔
      ∃ h : e ∈ G.edgeSet, C ⟨e, h⟩ = c := by
  rw [EdgeLabeling.labelGraph, edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨he, _⟩
    exact he
  · intro h
    refine ⟨h, ?_⟩
    exact h.elim fun he _ ↦ G.not_isDiag_of_mem_edgeSet he

/-- The edge subtype of a label graph is equivalent to the corresponding
colour fibre in the host edge subtype. -/
noncomputable def labelGraphEdgeEquiv (C : G.EdgeLabeling K) (c : K) :
    (C.labelGraph c).edgeSet ≃ {e : G.edgeSet // C e = c} where
  toFun e := by
    let h := (mem_labelGraph_edgeSet_iff C c e.1).mp e.2
    let hG := Classical.choose h
    have hc := Classical.choose_spec h
    exact ⟨⟨e.1, hG⟩, hc⟩
  invFun e :=
    ⟨e.1.1, (mem_labelGraph_edgeSet_iff C c e.1.1).mpr ⟨e.1.2, e.2⟩⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

theorem edgeCount_labelGraph (C : G.EdgeLabeling K) (c : K) :
    edgeCount (C.labelGraph c) = Nat.card {e : G.edgeSet // C e = c} := by
  exact Nat.card_congr (labelGraphEdgeEquiv C c)

/-- In every finite `k`-edge-colouring, one label graph contains at least a
`1/k` share of all host edges, stated without division. -/
theorem exists_majority_label
    [Finite V] [Fintype K] [DecidableEq K] [Nonempty K]
    (C : G.EdgeLabeling K) :
    ∃ c : K, edgeCount G ≤ Fintype.card K * edgeCount (C.labelGraph c) := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  obtain ⟨c, _hc, hcount⟩ :=
    exists_card_le_card_mul_fiber
      (s := Finset.univ) (t := Finset.univ) Finset.univ_nonempty C
      (fun _ _ ↦ Finset.mem_univ _)
  refine ⟨c, ?_⟩
  rw [edgeCount, edgeCount_labelGraph]
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using hcount

end LabelGraph

end LeanCo.SizeRamsey
