import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Size--Ramsey definitions

This file gives the literal finite-simple-graph definitions needed for the
multicolour size--Ramsey problem.  Host graphs are allowed to have any finite
number of vertices (represented by `Fin N`), and a `k`-edge-colouring is a
`SimpleGraph.EdgeLabeling G (Fin k)`.

The lower-bound predicate uses the strict convention natural for a statement
`m ≤ R̂ₖ(H)`: every host with fewer than `m` edges admits a colouring with
no monochromatic copy of `H`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

universe u v

variable {V : Type u} {W : Type v}

/-- The number of edges of a graph, without choosing a decidable adjacency
relation.  It is finite whenever the vertex type is finite. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

/-- A graph contains a (not necessarily induced) copy of the path on `n`
vertices. -/
def ContainsPath (G : SimpleGraph V) (n : ℕ) : Prop :=
  pathGraph n ⊑ G

/-- A graph contains a (not necessarily induced) copy of the cycle on `n`
vertices. -/
def ContainsCycle (G : SimpleGraph V) (n : ℕ) : Prop :=
  cycleGraph n ⊑ G

/-- The path on `n` vertices is contained in the cycle on `n` vertices. -/
theorem containsPath_cycleGraph (n : ℕ) : ContainsPath (cycleGraph n) n :=
  IsContained.of_le pathGraph_le_cycleGraph

/-- Every copy of an `n`-cycle contains a copy of the `n`-vertex path. -/
theorem containsPath_of_containsCycle {G : SimpleGraph V} {n : ℕ}
    (h : ContainsCycle G n) : ContainsPath G n :=
  (containsPath_cycleGraph n).trans h

/-- `C` has no colour class containing a copy of `H`. -/
def AvoidsMonochromaticCopy (H : SimpleGraph W) {K : Type*}
    {G : SimpleGraph V} (C : G.EdgeLabeling K) : Prop :=
  ∀ c : K, H.Free (C.labelGraph c)

/-- Every `K`-edge-colouring of `G` has a monochromatic copy of `H`. -/
def Arrows (G : SimpleGraph V) (K : Type*) (H : SimpleGraph W) : Prop :=
  ∀ C : G.EdgeLabeling K, ∃ c : K, H ⊑ C.labelGraph c

/-- The negation of the arrow property is exactly the existence of an avoiding
edge-colouring. -/
theorem not_arrows_iff_exists_avoidingColoring {G : SimpleGraph V}
    {K : Type*} {H : SimpleGraph W} :
    ¬ Arrows G K H ↔ ∃ C : G.EdgeLabeling K, AvoidsMonochromaticCopy H C := by
  classical
  simp only [Arrows, AvoidsMonochromaticCopy, SimpleGraph.Free]
  push Not
  rfl

/-- The cycle arrow relation in the notation of the paper. -/
def ArrowsCycle (G : SimpleGraph V) (k n : ℕ) : Prop :=
  Arrows G (Fin k) (cycleGraph n)

/-- The path arrow relation used for transferring the known path lower bound. -/
def ArrowsPath (G : SimpleGraph V) (k n : ℕ) : Prop :=
  Arrows G (Fin k) (pathGraph n)

/-- A monochromatic cycle always supplies a monochromatic path in the same
colour. -/
theorem arrowsPath_of_arrowsCycle {G : SimpleGraph V} {k n : ℕ}
    (h : ArrowsCycle G k n) : ArrowsPath G k n := by
  intro C
  obtain ⟨c, hc⟩ := h C
  exact ⟨c, (containsPath_cycleGraph n).trans hc⟩

/-- If a colouring avoids the `n`-vertex path in every colour, then it also
avoids the `n`-cycle in every colour. -/
theorem avoidsCycle_of_avoidsPath {G : SimpleGraph V} {k n : ℕ}
    {C : G.EdgeLabeling (Fin k)}
    (h : AvoidsMonochromaticCopy (pathGraph n) C) :
    AvoidsMonochromaticCopy (cycleGraph n) C := by
  intro c hcycle
  exact h c ((containsPath_cycleGraph n).trans hcycle)

/-- `m` is an upper bound for the `K`-colour size--Ramsey number of `H` if
some finite host with at most `m` edges arrows `H`. -/
def IsSizeRamseyUpperBound (K : Type*) (H : SimpleGraph W) (m : ℕ) : Prop :=
  ∃ N : ℕ, ∃ G : SimpleGraph (Fin N), edgeCount G ≤ m ∧ Arrows G K H

/-- `m` is a lower bound for the `K`-colour size--Ramsey number of `H` if
every finite host with fewer than `m` edges has a colouring avoiding `H`. -/
def IsSizeRamseyLowerBound (K : Type*) (H : SimpleGraph W) (m : ℕ) : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)), edgeCount G < m →
    ∃ C : G.EdgeLabeling K, AvoidsMonochromaticCopy H C

/-- Equivalent non-arrow formulation of a size--Ramsey lower bound. -/
theorem isSizeRamseyLowerBound_iff_forall_not_arrows
    {K : Type*} {H : SimpleGraph W} {m : ℕ} :
    IsSizeRamseyLowerBound K H m ↔
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)), edgeCount G < m → ¬ Arrows G K H := by
  classical
  simp only [IsSizeRamseyLowerBound, not_arrows_iff_exists_avoidingColoring]

/-- Cycle-specific upper-bound predicate. -/
def IsCycleSizeRamseyUpperBound (k n m : ℕ) : Prop :=
  IsSizeRamseyUpperBound (Fin k) (cycleGraph n) m

/-- Cycle-specific lower-bound predicate. -/
def IsCycleSizeRamseyLowerBound (k n m : ℕ) : Prop :=
  IsSizeRamseyLowerBound (Fin k) (cycleGraph n) m

/-- Path-specific upper-bound predicate. -/
def IsPathSizeRamseyUpperBound (k n m : ℕ) : Prop :=
  IsSizeRamseyUpperBound (Fin k) (pathGraph n) m

/-- Path-specific lower-bound predicate. -/
def IsPathSizeRamseyLowerBound (k n m : ℕ) : Prop :=
  IsSizeRamseyLowerBound (Fin k) (pathGraph n) m

/-- Any upper-bound witness for cycles is also an upper-bound witness for
paths. -/
theorem pathUpperBound_of_cycleUpperBound {k n m : ℕ}
    (h : IsCycleSizeRamseyUpperBound k n m) :
    IsPathSizeRamseyUpperBound k n m := by
  obtain ⟨N, G, hedge, harrow⟩ := h
  exact ⟨N, G, hedge, arrowsPath_of_arrowsCycle harrow⟩

/-- The path lower bound transfers verbatim to cycles because
`pathGraph n ≤ cycleGraph n`. -/
theorem cycleLowerBound_of_pathLowerBound {k n m : ℕ}
    (h : IsPathSizeRamseyLowerBound k n m) :
    IsCycleSizeRamseyLowerBound k n m := by
  intro N G hedge
  obtain ⟨C, hC⟩ := h N G hedge
  exact ⟨C, avoidsCycle_of_avoidsPath hC⟩

end LeanCo.SizeRamsey
