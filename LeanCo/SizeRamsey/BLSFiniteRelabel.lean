import LeanCo.SizeRamsey.FiniteRelabel
import LeanCo.SizeRamsey.BLSRoundStep
import Mathlib.Tactic

/-!
# Transporting the BLS invariant and colourings to finite labels

The canonical `finiteRelabel` graph has vertex type `Fin (Fintype.card V)`.
This file records that the recursive numerical invariant is unchanged by this
relabelling and that an avoiding colouring pulls back to the original graph.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

noncomputable section

universe u v w

/-! ## Numerical invariant -/

/-- Canonical finite relabelling preserves every field of the BLS iteration
invariant: vertex cardinality, edge count, and maximum degree. -/
theorem BLSIterationInvariant_finiteRelabel
    {V : Type u} [Fintype V]
    {r n i : ℕ} {β edgeCap : ℕ → ℝ} {G : SimpleGraph V}
    (hInv : BLSIterationInvariant r n β edgeCap i G) :
    BLSIterationInvariant r n β edgeCap i (finiteRelabel G) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : DecidableRel (finiteRelabel G).Adj := Classical.decRel _
  change
    (Fintype.card V : ℝ) ≤
        ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ)) / 4 ∧
      (edgeCount G : ℝ) ≤ edgeCap i ∧
      (G.maxDegree : ℝ) ≤
        β i * (r : ℝ) * Real.log (r : ℝ) at hInv
  change
    (Fintype.card (Fin (Fintype.card V)) : ℝ) ≤
        ((r : ℝ) * Real.log (r : ℝ) * (n : ℝ)) / 4 ∧
      (edgeCount (finiteRelabel G) : ℝ) ≤ edgeCap i ∧
      ((finiteRelabel G).maxDegree : ℝ) ≤
        β i * (r : ℝ) * Real.log (r : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · simpa using hInv.1
  · simpa only [edgeCount_finiteRelabel] using hInv.2.1
  · rw [← (finiteRelabelIso G).maxDegree_eq]
    exact hInv.2.2

/-! ## Pulling back avoiding colourings -/

/-- Pullback along a graph isomorphism preserves avoidance of every fixed
graph.  The colour-class graph of the pullback is isomorphic to the original
colour-class graph. -/
theorem AvoidsMonochromaticCopy.pullback_iso
    {V : Type u} {W : Type v} {X : Type w}
    {G : SimpleGraph V} {H : SimpleGraph W} {F : SimpleGraph X}
    {K : Type*} (e : G ≃g H) (C : H.EdgeLabeling K)
    (hC : AvoidsMonochromaticCopy F C) :
    AvoidsMonochromaticCopy F (C.pullback e.toHom) := by
  intro colour hcopy
  exact hC colour
    (hcopy.trans ⟨(labelGraphPullbackIso e C colour).toCopy⟩)

/-- General finite-relabelling specialization, with an arbitrary forbidden
graph and palette. -/
theorem finiteRelabel_pullback_avoids
    {V : Type u} [Fintype V] {X : Type w}
    (G : SimpleGraph V) {F : SimpleGraph X} {K : Type*}
    (C : (finiteRelabel G).EdgeLabeling K)
    (hC : AvoidsMonochromaticCopy F C) :
    AvoidsMonochromaticCopy F
      (C.pullback (finiteRelabelIso G).toHom) :=
  hC.pullback_iso (finiteRelabelIso G) C

/-- Exact bridge used by the path-size-Ramsey recursion: a `Fin k` colouring
of the canonical relabelling pulls back with the same palette and still
avoids `pathGraph n`. -/
theorem finiteRelabel_pullback_avoids_pathGraph
    {V : Type u} [Fintype V] (G : SimpleGraph V) {k n : ℕ}
    (C : (finiteRelabel G).EdgeLabeling (Fin k))
    (hC : AvoidsMonochromaticCopy (pathGraph n) C) :
    AvoidsMonochromaticCopy (pathGraph n)
      (C.pullback (finiteRelabelIso G).toHom) :=
  finiteRelabel_pullback_avoids G C hC

end

end LeanCo.SizeRamsey
