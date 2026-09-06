import LeanCo.SizeRamsey.RandomHost
import LeanCo.SizeRamsey.UpperDeterministic

/-!
# Random host joined to the deterministic long-cycle chain

This module consumes the completed finite-probability construction and feeds
its output directly into Claims 4.1 and 4.2.  The remaining upper-bound step
after this theorem is solely the exact cycle-length adjustment of Lemma 3.3.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

/-- There is a host at the paper's explicit edge scale for which every
`k`-edge-colouring contains a monochromatic even cycle of length at least
`n+2`. -/
theorem exists_host_monochromatic_long_even_cycle
    {k n : Nat} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : Real) ≤ n) :
    ∃ Γ : SimpleGraph (BalancedBipartiteVertex (hostPartSize k n)),
      (edgeCount Γ : Real) ≤ cycleUpperScale k n ∧
      Γ.IsBipartite ∧
      ∀ lab : Γ.EdgeLabeling (Fin k),
        ∃ color : Fin k, ∃ ell : Nat,
          Even ell ∧ n + 2 ≤ ell ∧
            ContainsCycleLength (lab.labelGraph color) ell := by
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
  refine ⟨Γ, ?_, hbip, ?_⟩
  · rw [← two_mul_probability_mul_partSize_sq hnpos]
    exact hupper
  · intro lab
    apply exists_monochromatic_long_even_cycle_of_hostProperties Γ hk hnpos
      (by simp [BalancedBipartiteVertex, two_mul]) hbip hlower hsparse lab

end LeanCo.SizeRamsey
