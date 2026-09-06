import LeanCo.HypercubeTuran.Defs
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Combinatorial base-graph properties

The published proof obtains its two pseudorandom properties from a spectral
gap.  For the unconditional formal proof we isolate exactly the finite
inequalities consumed downstream.  This lets the existence proof use an
elementary binomial-random-graph alteration rather than importing Friedman's
theorem as an axiom.
-/

open scoped SimpleGraph symmDiff

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Number of (undirected) edges of a finite simple graph. -/
def graphEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- Number of edges crossing from `S` to its complement.  Each crossing edge
is counted once, at its endpoint in `S`. -/
def cutSize (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ∑ v ∈ S, #(G.neighborFinset v \ S)

/-- Every independent set occupies less than one hundredth of the vertices.
The constant is deliberately weaker than the paper's spectral `1/200` bound
but is still more than sufficient for Proposition 2.3. -/
def HasSmallIndependentSets (G : SimpleGraph V) : Prop :=
  ∀ I : Finset V, G.IsIndepSet (I : Set V) →
    100 * #I < Fintype.card V

/-- A uniform lower bound on all cuts.  This is an integer-only replacement
for the lower half of the expander-mixing estimate. -/
def HasStrongCutExpansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Prop :=
  ∀ S : Finset V,
    7 * d * #S * (Fintype.card V - #S) ≤
      5 * Fintype.card V * cutSize G S

/-- A coarse upper bound on the total edge count, paired with
`HasStrongCutExpansion`. -/
def HasControlledEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Prop :=
  4 * graphEdgeCount G ≤ 5 * d * Fintype.card V

/-- The finite pseudorandom certificate used by the formal downstream proof.
All fields are decidable, finite statements for a fixed graph. -/
structure IsCombinatorialBase (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Prop where
  ten_le_card : 10 ≤ Fintype.card V
  d_pos : 0 < d
  connected : G.Connected
  edgeCount_control : HasControlledEdgeCount G d
  cut_expansion : HasStrongCutExpansion G d
  small_independent : HasSmallIndependentSets G

/-- A candidate placement of the poles of `T₁(G)` in a cube. -/
def IsPolePlacement (G : SimpleGraph V) {ι : Type*} [DecidableEq ι]
    (A : V → Finset ι) : Prop :=
  Function.Injective A ∧
    ∀ ⦃u v : V⦄, G.Adj u v → #(A u ∆ A v) = 2

/-- The concentration conclusion needed in the proof of Proposition 2.3.
It says that some pole has total Hamming distance at most `25N/7` from all
other poles.  Connectivity and the distance-two edge condition also force
every pole to lie in the same bipartition class of the cube. -/
def HasPoleConcentration (G : SimpleGraph V) : Prop :=
  ∀ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
      (A : V → Finset ι),
    IsPolePlacement G A →
      ∃ w : V,
        7 * (∑ v : V, #(A v ∆ A w)) ≤ 25 * Fintype.card V ∧
        ∀ v : V, Even #(A v ∆ A w)

/-- Bundled core assumptions after eliminating all spectral terminology. -/
structure IsAvoidanceBase (G : SimpleGraph V) : Prop where
  ten_le_card : 10 ≤ Fintype.card V
  connected : G.Connected
  concentrated : HasPoleConcentration G
  small_independent : HasSmallIndependentSets G

end LeanCo.HypercubeTuran
