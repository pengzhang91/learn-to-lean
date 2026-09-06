import LeanCo.SizeRamsey.ColoredLongCycle
import LeanCo.SizeRamsey.HostNumerics

/-!
# Deterministic upper-bound chain at the paper's constants

This theorem consumes exactly the three host properties produced by the
random construction and closes Claims 4.1 and 4.2 for an arbitrary edge
colouring.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

universe u

variable {X : Type u}

theorem exists_monochromatic_long_even_cycle_of_hostProperties
    (Gamma : SimpleGraph X) [Fintype X] [Nonempty X]
    [DecidableEq X] [DecidableRel Gamma.Adj]
    {k n : Nat} (hk : 2 ≤ k) (hn : 0 < n)
    (hcard : Fintype.card X = 2 * hostPartSize k n)
    (hbip : Gamma.IsBipartite)
    (hlower : hostProbability k n * (hostPartSize k n : Real) ^ 2 / 2 ≤
      (edgeCount Gamma : Real))
    (hsparse : IsLocallySparse Gamma (3 * n) (localSparsityFactor k))
    (lab : Gamma.EdgeLabeling (Fin k)) :
    ∃ color : Fin k, ∃ ell : Nat,
      Even ell ∧ n + 2 ≤ ell ∧
        ContainsCycleLength (lab.labelGraph color) ell := by
  have hdense := claim_four_one_density_of_host_lower
    Gamma hk hn hcard hlower
  exact exists_monochromatic_long_even_cycle Gamma hbip
    (by omega) hn (two_le_localDegreeThreshold hk) hdense hsparse
    (six_mul_localSparsityFactor_lt_localDegreeThreshold hk) lab

end LeanCo.SizeRamsey
