import LeanCo.SizeRamsey.FiniteRelabel
import LeanCo.SizeRamsey.RandomUpperExact
import LeanCo.SizeRamsey.UpperCeiling

/-!
# The explicit upper half of Wang--Wang's theorem

This module closes the upper-bound chain at the literal universe-safe
size--Ramsey predicate.  The witness supplied by the random construction has
vertices `Fin M ⊕ Fin M`; `finiteRelabel` transports it to a graph over one
`Fin N`, preserving both its edge count and every edge-colouring statement.
-/

namespace LeanCo.SizeRamsey

/-- For every admissible even `n`, the integer ceiling of Wang--Wang's
explicit real scale is a `k`-colour cycle size--Ramsey upper bound. -/
theorem wangWang_cycle_upper_bound
    {k n : Nat} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : Real) ≤ n) (hnEven : Even n) :
    IsCycleSizeRamseyUpperBound k n (cycleUpperNat k n) := by
  obtain ⟨Gamma, hedge, harrow⟩ :=
    exists_host_arrows_exact_even_cycle hk hn hnEven
  exact isCycleSizeRamseyUpperBound_natCeil_of_finiteWitness hedge harrow

/-- A natural number lying above the explicit real scale is also a valid
upper bound.  This form is convenient when combining the upper and lower
halves into a two-sided statement. -/
theorem wangWang_cycle_upper_bound_of_scale_le
    {k n m : Nat} (hk : 2 ≤ k)
    (hn : 100 * Real.log (k : Real) ≤ n) (hnEven : Even n)
    (hm : cycleUpperScale k n ≤ m) :
    IsCycleSizeRamseyUpperBound k n m := by
  obtain ⟨Gamma, hedge, harrow⟩ :=
    exists_host_arrows_exact_even_cycle hk hn hnEven
  apply isCycleSizeRamseyUpperBound_of_finiteWitness
    (G := Gamma) (harrow := harrow)
  have hedgeReal : (edgeCount Gamma : Real) ≤ (m : Nat) :=
    hedge.trans hm
  exact_mod_cast hedgeReal

end LeanCo.SizeRamsey
