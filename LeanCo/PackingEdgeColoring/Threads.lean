import LeanCo.PackingEdgeColoring.Defs

/-!
# Chains and threads in subcubic graphs

This file formalizes the local paths used throughout Sections 3 and 4 of
Kim--Liu--Xu.  Degrees are always degrees in the ambient graph.  In
particular, deleting the internal vertices of a thread does not change what
it means for the original path to have been a thread.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A vertex of ambient degree two. -/
def IsTwoVertex (v : V) : Prop := G.degree v = 2

/-- A vertex of ambient degree three. -/
def IsThreeVertex (v : V) : Prop := G.degree v = 3

/-- A `k`-chain is a path whose support consists of exactly `k` vertices,
all of ambient degree two.  The edges continuing the chain at either end are
not part of the witnessing walk. -/
def IsKChain {u v : V} (p : G.Walk u v) (k : ℕ) : Prop :=
  p.IsPath ∧ p.support.length = k ∧
    ∀ x ∈ p.support, IsTwoVertex G x

/-- A `k`-thread is a path of length `k + 1` whose endpoints have ambient
degree three and whose `k` internal vertices have ambient degree two. -/
def IsKThread {u v : V} (p : G.Walk u v) (k : ℕ) : Prop :=
  p.IsPath ∧ p.length = k + 1 ∧
    IsThreeVertex G u ∧ IsThreeVertex G v ∧
      ∀ i : ℕ, 0 < i → i < p.length → IsTwoVertex G (p.getVert i)

/-- Existence of a `k`-thread starting at `u`. -/
def HasKThreadAt (u : V) (k : ℕ) : Prop :=
  ∃ v : V, ∃ p : G.Walk u v, IsKThread G p k

theorem IsKChain.length {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : IsKChain G p k) : p.length + 1 = k := by
  rw [← p.length_support]
  exact h.2.1

theorem IsKChain.reverse {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : IsKChain G p k) : IsKChain G p.reverse k := by
  refine ⟨h.1.reverse, ?_, ?_⟩
  · simpa [Walk.support_reverse] using h.2.1
  · intro x hx
    apply h.2.2 x
    simpa [Walk.support_reverse] using hx

theorem IsKThread.length {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : IsKThread G p k) : p.length = k + 1 :=
  h.2.1

theorem IsKThread.start_three {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : IsKThread G p k) : IsThreeVertex G u :=
  h.2.2.1

theorem IsKThread.end_three {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : IsKThread G p k) : IsThreeVertex G v :=
  h.2.2.2.1

theorem IsKThread.internal_two {u v : V} {p : G.Walk u v} {k i : ℕ}
    (h : IsKThread G p k) (hi0 : 0 < i) (hil : i < p.length) :
    IsTwoVertex G (p.getVert i) :=
  h.2.2.2.2 i hi0 hil

theorem IsKThread.reverse {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : IsKThread G p k) : IsKThread G p.reverse k := by
  refine ⟨h.1.reverse, by simpa using h.2.1, h.end_three, h.start_three, ?_⟩
  intro i hi0 hil
  rw [Walk.getVert_reverse]
  apply h.internal_two
  · rw [Walk.length_reverse] at hil
    omega
  · rw [Walk.length_reverse] at hil
    omega

theorem IsKThread.first_step_adj {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : IsKThread G p k) : G.Adj u (p.getVert 1) := by
  have hp : 0 < p.length := by
    rw [h.length]
    omega
  simpa using p.adj_getVert_succ (i := 0) hp

theorem IsKThread.last_step_adj {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : IsKThread G p k) : G.Adj (p.getVert k) v := by
  have hk : k < p.length := by
    rw [h.length]
    omega
  have hadj := p.adj_getVert_succ (i := k) hk
  have hend : p.getVert (k + 1) = v := by
    rw [← h.length]
    exact p.getVert_length
  rwa [hend] at hadj

theorem IsKThread.internal_support_length {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : IsKThread G p k) : p.support.length = k + 2 := by
  simpa [h.length, Nat.add_assoc] using p.length_support

end Finite

end


end LeanCo.PackingEdgeColoring
