import LeanCo.HypercubeTuran.LocalParity
import LeanCo.HypercubeTuran.TuranWitness

/-!
# Assembly of the parity-colouring conclusion

An avoidance base excludes a monochromatic copy of its one-subdivision in
each colour class of the explicit parity colouring.  This file packages that
pointwise statement as an avoiding colouring in every finite cube, including
the zero-dimensional cube, and then invokes the general majority-colour
argument to obtain the half-density Turan lower bound.
-/

namespace LeanCo.HypercubeTuran

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- The explicit parity colouring avoids the one-subdivision of every
avoidance base in every finite-dimensional cube.  No separate exceptional
case is needed for `n = 0`: the same empty edge-labelling is supplied by
`parityColoring`. -/
theorem hasAvoidingTwoColoring_oneSubdivision_of_isAvoidanceBase
    (hbase : IsAvoidanceBase G) (n : ℕ) :
    HasAvoidingTwoColoring (oneSubdivision G) n := by
  refine ⟨(parityColoring :
    (hypercubeGraph (Fin n)).EdgeLabeling (Fin 2)), ?_⟩
  intro c
  exact parityColoring_free_oneSubdivision_of_isAvoidanceBase
    (G := G) (κ := Fin n) hbase c

/-- The one-subdivision of an avoidance base has pointwise cube Turan
density at least one half. -/
theorem hasCubeTuranLowerBound_half_oneSubdivision_of_isAvoidanceBase
    (hbase : IsAvoidanceBase G) :
    HasCubeTuranLowerBound (oneSubdivision G) (1 / 2 : ℝ) :=
  hasCubeTuranLowerBound_half_of_avoiding (oneSubdivision G) fun n =>
    hasAvoidingTwoColoring_oneSubdivision_of_isAvoidanceBase hbase n

end LeanCo.HypercubeTuran
