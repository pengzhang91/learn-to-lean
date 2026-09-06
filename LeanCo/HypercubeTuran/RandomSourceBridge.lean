import LeanCo.HypercubeTuran.Alteration
import LeanCo.HypercubeTuran.RandomBaseExistence

/-!
# From the random good event to an alteration source

The probability layer counts selected coordinates, while the deterministic
alteration layer speaks about the associated simple graph.  These small
bridges keep that representation change out of the final theorem.
-/

open scoped SimpleGraph

namespace LeanCo.HypercubeTuran

open SimpleGraph

noncomputable section

/-- Once local sparsity has supplied disjointness of short cycles, all other
fields of the random good event translate directly to `IsAlterationSource`. -/
theorem RB.IsGoodSource.toIsAlterationSource_of_shortCyclesVertexDisjoint
    {N d g : ℕ} {E : Set (RandomEdge N)}
    (h : RB.IsGoodSource E d g) (hN : 10 ≤ N) (hd : 10 ≤ d)
    (hcycles : ShortCyclesVertexDisjoint (graphOfEdges E) g)
    [DecidableRel (graphOfEdges E).Adj] :
    IsAlterationSource (graphOfEdges E) d g := by
  refine
    { ten_le_card := by simpa using hN
      ten_le_d := hd
      edgeCount_control := ?_
      stronger_cut := ?_
      very_small_independent := by
        intro I hI
        simpa using h.small_independent I hI
      shortCycles_disjoint := hcycles }
  · unfold HasControlledEdgeCount
    rw [graphEdgeCount_graphOfEdges]
    simpa using h.edge_control
  · intro S
    rw [← RB.randomGraphCutSize_eq_cutSize]
    simpa using h.cut_expansion S

end

end LeanCo.HypercubeTuran
