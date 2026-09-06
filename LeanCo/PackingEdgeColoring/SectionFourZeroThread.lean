import LeanCo.PackingEdgeColoring.SectionFourLongTwoThreadClaim

/-!
# Zero-thread data for the final Section 4 reductions

The `330` and `320` configurations end in an ordinary edge between two
degree-three vertices, i.e. a 0-thread.  This file exposes that ordered core
and the two external neighbours at its far endpoint.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Ordered data on a zero-thread, an edge joining two degree-three
vertices. -/
structure ZeroThreadCore (u x : V) : Prop where
  start_three : IsThreeVertex G u
  end_three : IsThreeVertex G x
  adj : G.Adj u x

/-- Extract the zero-thread core from a certified 0-thread. -/
theorem IsKThread.zeroThreadCore
    {u x : V} {p : G.Walk u x} (hp : IsKThread G p 0) :
    ZeroThreadCore G u x := by
  have hlen : p.length = 1 := by simpa using hp.length
  have hend : p.getVert 1 = x := by
    rw [← hlen]
    exact p.getVert_length
  exact ⟨hp.start_three, hp.end_three, by simpa [hend] using hp.first_step_adj⟩

/-- The far endpoint data specialized to a zero-thread. -/
theorem ZeroThreadCore.exists_far_neighbors
    {u x : V} (r : ZeroThreadCore G u x) :
    ∃ a b : V, a ≠ b ∧ a ≠ u ∧ b ≠ u ∧
      G.Adj x a ∧ G.Adj x b ∧ G.neighborFinset x = {u, a, b} :=
  exists_two_other_neighbors_of_isThreeVertex G r.end_three r.adj

/-- At a three-arm centre, the external palette of one arm is exactly the
colours on the other two displayed first edges.  This generic version also
applies when one of those arms is a zero-thread. -/
theorem longPair_externalPalette_eq_pair_three_neighbors
    {u a b c : V}
    (hu : IsThreeVertex G u)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (colour : G.edgeSet → OneTwoColor 4) (i j : Fin 4)
    (hP : colour (⟨s(a, u), hua.symm⟩ : G.edgeSet) = none)
    (hQ : colour (⟨s(b, u), hub.symm⟩ : G.edgeSet) = some i)
    (hT : colour (⟨s(c, u), huc.symm⟩ : G.edgeSet) = some j) :
    ExternalInducedColors G colour u
      (⟨s(a, u), hua.symm⟩ : G.edgeSet) = {i, j} := by
  classical
  let P : G.edgeSet := ⟨s(a, u), hua.symm⟩
  let Q : G.edgeSet := ⟨s(b, u), hub.symm⟩
  let T : G.edgeSet := ⟨s(c, u), huc.symm⟩
  have hPQ : P ≠ Q := by
    simpa [P, Q] using longPair_firstEdges_ne_of_firstVertices_ne G hua hub hab
  have hPT : P ≠ T := by
    simpa [P, T] using longPair_firstEdges_ne_of_firstVertices_ne G hua huc hac
  ext d
  constructor
  · rintro ⟨f, ⟨huf, hfP⟩, hfd⟩
    obtain ⟨x, hfx⟩ := Sym2.mem_iff_exists.mp huf
    have hux : G.Adj u x := by
      have hfG := f.2
      rw [hfx] at hfG
      simpa using hfG
    rcases longPair_eq_one_of_three_of_adj G hu hua hub huc hab hac hbc hux with
      rfl | rfl | rfl
    · exact False.elim (hfP (Subtype.ext (by simpa [P, Sym2.eq_swap] using hfx)))
    · have hfEq : f = Q := Subtype.ext (by simpa [Q, Sym2.eq_swap] using hfx)
      have hfdQ : colour Q = some d := by simpa [hfEq, Q] using hfd
      have hdi : d = i := Option.some.inj (hfdQ.symm.trans hQ)
      simp [hdi]
    · have hfEq : f = T := Subtype.ext (by simpa [T, Sym2.eq_swap] using hfx)
      have hfdT : colour T = some d := by simpa [hfEq, T] using hfd
      have hdj : d = j := Option.some.inj (hfdT.symm.trans hT)
      simp [hdj]
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · exact ⟨Q, ⟨by simp [Q], hPQ.symm⟩, by simpa [Q] using hQ⟩
    · exact ⟨T, ⟨by simp [T], hPT.symm⟩, by simpa [T] using hT⟩

end Finite

end

end LeanCo.PackingEdgeColoring
