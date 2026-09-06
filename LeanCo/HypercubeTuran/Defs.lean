import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Real.Basic

/-!
# Hypercube Turan definitions

Definitions used in the formalization of Axenovich--Pejic,
*On high-girth layered graphs of positive Turan density in a hypercube*
(arXiv:2608.30544v1).

The paper regards the vertices of a hypercube as finite subsets of a ground
set.  We use `Finset ι` literally, so Hamming distance is the cardinality of
the symmetric difference.
-/

open scoped SimpleGraph symmDiff

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u v

/-- The hypercube on the coordinate type `ι`.  Two finite subsets are
adjacent exactly when their symmetric difference is a singleton. -/
def hypercubeGraph (ι : Type u) [DecidableEq ι] : SimpleGraph (Finset ι) :=
  SimpleGraph.fromRel fun A B => #(A ∆ B) = 1

@[simp]
theorem hypercubeGraph_adj {ι : Type u} [DecidableEq ι] (A B : Finset ι) :
    (hypercubeGraph ι).Adj A B ↔ #(A ∆ B) = 1 := by
  rw [hypercubeGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · simpa [symmDiff_comm] using h
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro hab
    subst B
    simp at h

/-- The union of two consecutive vertex layers, with all hypercube edges
between them.  Our indexing uses layers `k` and `k+1`. -/
def cubeEdgeLayer (ι : Type u) [DecidableEq ι] (k : ℕ) :
    SimpleGraph {A : Finset ι // #A = k ∨ #A = k + 1} :=
  (hypercubeGraph ι).induce {A | #A = k ∨ #A = k + 1}

/-- A finite graph is layered when it occurs as a (not necessarily induced)
subgraph of two consecutive layers of a finite hypercube. -/
def IsLayered {V : Type u} (H : SimpleGraph V) : Prop :=
  ∃ n k : ℕ, H ⊑ cubeEdgeLayer (Fin n) k

/-- The vertices of the one-subdivision of `G`: original vertices (poles)
and one new vertex for every edge. -/
abbrev SubdivisionVertex {V : Type u} (G : SimpleGraph V) := V ⊕ G.edgeSet

/-- The one-subdivision `T₁(G)`.  A pole is adjacent to an edge-vertex
precisely when it is an endpoint of that edge. -/
def oneSubdivision {V : Type u} (G : SimpleGraph V) :
    SimpleGraph (SubdivisionVertex G) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl v, Sum.inr e => v ∈ e.1
    | _, _ => False

@[simp]
theorem oneSubdivision_adj_pole_edge {V : Type u} {G : SimpleGraph V}
    (v : V) (e : G.edgeSet) :
    (oneSubdivision G).Adj (Sum.inl v) (Sum.inr e) ↔ v ∈ e.1 := by
  simp [oneSubdivision, SimpleGraph.fromRel_adj]

@[simp]
theorem oneSubdivision_adj_edge_pole {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (v : V) :
    (oneSubdivision G).Adj (Sum.inr e) (Sum.inl v) ↔ v ∈ e.1 := by
  rw [adj_comm, oneSubdivision_adj_pole_edge]

@[simp]
theorem not_oneSubdivision_adj_pole_pole {V : Type u} {G : SimpleGraph V}
    (v w : V) :
    ¬(oneSubdivision G).Adj (Sum.inl v) (Sum.inl w) := by
  simp [oneSubdivision, SimpleGraph.fromRel_adj]

@[simp]
theorem not_oneSubdivision_adj_edge_edge {V : Type u} {G : SimpleGraph V}
    (e f : G.edgeSet) :
    ¬(oneSubdivision G).Adj (Sum.inr e) (Sum.inr f) := by
  simp [oneSubdivision, SimpleGraph.fromRel_adj]

/-- A labeling has no monochromatic copy of `H`. -/
def AvoidsMonochromaticCopy {W : Type u} {V : Type v} (H : SimpleGraph W)
    {K : Type*} {G : SimpleGraph V} (C : G.EdgeLabeling K) : Prop :=
  ∀ c : K, H.Free (C.labelGraph c)

/-- The two-colour non-Ramsey conclusion of the paper for one cube. -/
def HasAvoidingTwoColoring {W : Type u} (H : SimpleGraph W) (n : ℕ) : Prop :=
  ∃ C : (hypercubeGraph (Fin n)).EdgeLabeling (Fin 2),
    AvoidsMonochromaticCopy H C

/-- Maximum number of edges in an `H`-free subgraph of `Q_n`. -/
noncomputable def cubeExtremalNumber {W : Type u} (H : SimpleGraph W) (n : ℕ) : ℕ := by
  classical
  exact Finset.sup
    (Finset.univ.filter fun G : SimpleGraph (Finset (Fin n)) =>
      G ≤ hypercubeGraph (Fin n) ∧ H.Free G)
    fun G => G.edgeSet.ncard

/-- Number of edges of `Q_n`. -/
noncomputable def cubeEdgeCount (n : ℕ) : ℕ := by
  exact (hypercubeGraph (Fin n)).edgeSet.ncard

/-- A concrete finite witness for cube Turan density at least one half. -/
def HasHalfCubeWitness {W : Type u} (H : SimpleGraph W) (n : ℕ) : Prop :=
  ∃ K : SimpleGraph (Finset (Fin n)),
    K ≤ hypercubeGraph (Fin n) ∧ H.Free K ∧
      cubeEdgeCount n ≤ 2 * K.edgeSet.ncard

/-- A pointwise lower-density certificate.  This avoids hiding the concrete
finite statement behind a limit; later we prove that it implies the paper's
limit formulation. -/
def HasCubeTuranLowerBound {W : Type u} (H : SimpleGraph W) (r : ℝ) : Prop :=
  ∀ n : ℕ, r * (cubeEdgeCount n : ℝ) ≤ (cubeExtremalNumber H n : ℝ)

/-- Literal Ramsey portion of Theorem 1.1.  The witness graph is represented
on `Fin m`, making its finiteness explicit. -/
def AxenovichPejicRamseyStatement : Prop :=
  ∀ g : ℕ, 3 ≤ g →
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
      IsLayered H ∧ g ≤ H.girth ∧ ∀ n : ℕ, HasAvoidingTwoColoring H n

end LeanCo.HypercubeTuran
