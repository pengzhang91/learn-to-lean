import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Finite loopless multigraphs

This file gives the multiplicity-matrix model of the graphs used in
arXiv:2608.29981.  Parallel edges are retained through a natural-number-valued
multiplicity, while loops are excluded.  Finiteness is supplied by a
`Fintype` instance on the vertex type when it is needed.
-/

namespace LeanCo.LaplacianLFunctions

/-- An undirected loopless multigraph, represented by its symmetric edge
multiplicity matrix. -/
structure LooplessMultigraph (V : Type*) where
  /-- The number of edges joining two vertices. -/
  multiplicity : V → V → ℕ
  multiplicity_symm : ∀ v w, multiplicity v w = multiplicity w v
  multiplicity_self : ∀ v, multiplicity v v = 0

namespace LooplessMultigraph

variable {V : Type*} (G : LooplessMultigraph V)

theorem multiplicity_swap (v w : V) : G.multiplicity v w = G.multiplicity w v :=
  G.multiplicity_symm v w

@[simp]
theorem multiplicity_diag (v : V) : G.multiplicity v v = 0 :=
  G.multiplicity_self v

/-- The underlying simple graph obtained by forgetting positive edge
multiplicities. -/
def support : SimpleGraph V where
  Adj v w := 0 < G.multiplicity v w
  symm := ⟨fun v w h ↦ by simpa only [G.multiplicity_symm v w] using h⟩
  loopless := ⟨fun v h ↦ by
    have : 0 < 0 := by simpa only [G.multiplicity_self v] using h
    exact (Nat.lt_irrefl 0) this⟩

@[simp]
theorem support_adj (v w : V) : G.support.Adj v w ↔ 0 < G.multiplicity v w :=
  Iff.rfl

@[simp]
theorem support_not_adj_iff (v w : V) : ¬ G.support.Adj v w ↔ G.multiplicity v w = 0 := by
  simp [support]

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
