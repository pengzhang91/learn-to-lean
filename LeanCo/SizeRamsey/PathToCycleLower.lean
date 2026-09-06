import LeanCo.SizeRamsey.Defs

/-!
# Transferring path size--Ramsey lower bounds to cycles

A copy of `cycleGraph n` contains `pathGraph n`.  Consequently, an edge
colouring with no monochromatic `pathGraph n` also has no monochromatic
`cycleGraph n`, and every path size--Ramsey lower bound transfers unchanged
to the cycle of the same order.

Mathlib's definitions satisfy `pathGraph n ≤ cycleGraph n` for every natural
number `n`, including the degenerate values `0`, `1`, and `2`.  We therefore
prove the bridge without discarding those cases.  A `3 ≤ n` specialization is
also provided for statements in which `cycleGraph n` is intended to denote a
nondegenerate simple cycle.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

universe u v

variable {V : Type u} {K : Type v}

/-- Under mathlib's graph definitions, the path on `n` vertices is contained
in the cycle on `n` vertices for every `n`, including `n < 3`. -/
theorem pathGraph_isContained_cycleGraph_all (n : ℕ) :
    pathGraph n ⊑ cycleGraph n :=
  IsContained.of_le pathGraph_le_cycleGraph

/-- The conventional nondegenerate-cycle specialization of
`pathGraph_isContained_cycleGraph_all`. -/
theorem pathGraph_isContained_cycleGraph_of_three_le {n : ℕ} (_hn : 3 ≤ n) :
    pathGraph n ⊑ cycleGraph n :=
  pathGraph_isContained_cycleGraph_all n

/-- Any edge colouring avoiding a monochromatic path of order `n` also
avoids a monochromatic cycle of order `n`.  The colour type is arbitrary. -/
theorem avoidsMonochromaticCycle_of_avoidsMonochromaticPath
    {G : SimpleGraph V} {n : ℕ} {C : G.EdgeLabeling K}
    (h : AvoidsMonochromaticCopy (pathGraph n) C) :
    AvoidsMonochromaticCopy (cycleGraph n) C := by
  intro colour hcycle
  exact h colour ((pathGraph_isContained_cycleGraph_all n).trans hcycle)

/-- The same avoiding-colouring transfer with the usual `3 ≤ n` cycle
hypothesis exposed in its interface. -/
theorem avoidsMonochromaticCycle_of_avoidsMonochromaticPath_of_three_le
    {G : SimpleGraph V} {n : ℕ} {C : G.EdgeLabeling K} (_hn : 3 ≤ n)
    (h : AvoidsMonochromaticCopy (pathGraph n) C) :
    AvoidsMonochromaticCopy (cycleGraph n) C :=
  avoidsMonochromaticCycle_of_avoidsMonochromaticPath h

/-- A path size--Ramsey lower bound is also a cycle size--Ramsey lower bound
at the same number of colours, order, and edge threshold. -/
theorem cycleSizeRamseyLowerBound_of_pathSizeRamseyLowerBound
    {r n m : ℕ} (h : IsPathSizeRamseyLowerBound r n m) :
    IsCycleSizeRamseyLowerBound r n m := by
  intro N G hedge
  obtain ⟨C, hC⟩ := h N G hedge
  exact ⟨C, avoidsMonochromaticCycle_of_avoidsMonochromaticPath hC⟩

/-- Nondegenerate-cycle specialization of the lower-bound transfer. -/
theorem cycleSizeRamseyLowerBound_of_pathSizeRamseyLowerBound_of_three_le
    {r n m : ℕ} (_hn : 3 ≤ n)
    (h : IsPathSizeRamseyLowerBound r n m) :
    IsCycleSizeRamseyLowerBound r n m :=
  cycleSizeRamseyLowerBound_of_pathSizeRamseyLowerBound h

end LeanCo.SizeRamsey
