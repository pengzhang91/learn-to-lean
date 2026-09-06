import LeanCo.SizeRamsey.ColoredExactCycle
import LeanCo.SizeRamsey.RandomHost

/-!
# Exact random-host upper bound

This is the completed upper-bound witness before the routine relabelling of
its finite vertex type by a single `Fin N`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

/-- The finite random construction produces a host at the explicit paper
scale which arrows the exact admissible even cycle. -/
theorem exists_host_arrows_exact_even_cycle
    {k n : Nat} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : Real) ≤ n) (hnEven : Even n) :
    ∃ Γ : SimpleGraph (BalancedBipartiteVertex (hostPartSize k n)),
      (edgeCount Γ : Real) ≤ cycleUpperScale k n ∧
      ArrowsCycle Γ k n := by
  classical
  have hnpos : 0 < n := by
    have hlog := log_natCast_pos hk
    have hnreal : (0 : Real) < n := by nlinarith
    exact_mod_cast hnreal
  obtain ⟨Γ, hbip, hlower, hupper, hsparse⟩ :=
    exists_bipartiteHost_edgeBounds_isLocallySparse hk hn
  have hMpos : 0 < hostPartSize k n :=
    hostPartSize_pos (by omega) hnpos
  letI : Nonempty (BalancedBipartiteVertex (hostPartSize k n)) :=
    ⟨Sum.inl ⟨0, hMpos⟩⟩
  refine ⟨Γ, ?_, ?_⟩
  · rw [← two_mul_probability_mul_partSize_sq hnpos]
    exact hupper
  · intro lab
    obtain ⟨color, hcycle⟩ :=
      exists_monochromatic_exact_even_cycle_of_hostProperties
        Γ hk hn hnEven
        (by simp [BalancedBipartiteVertex, two_mul])
        hbip hlower hsparse lab
    exact ⟨color, containsCycle_of_containsCycleLength hcycle⟩

end LeanCo.SizeRamsey
