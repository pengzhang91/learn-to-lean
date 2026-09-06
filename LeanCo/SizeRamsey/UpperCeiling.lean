import LeanCo.SizeRamsey.Defs
import LeanCo.SizeRamsey.Numerics

/-!
# Integer packaging for the explicit upper scale

The probabilistic construction naturally gives a real-valued edge estimate,
whereas `IsCycleSizeRamseyUpperBound` uses a natural number.  This file keeps
the single unavoidable ceiling visible and proves the coercion bridge once.
-/

namespace LeanCo.SizeRamsey

open SimpleGraph

universe u

/-- A real upper estimate for the (natural) edge count implies the
corresponding ceiling estimate. -/
theorem edgeCount_le_natCeil_of_real_le {V : Type u} {G : SimpleGraph V}
    {x : Real} (h : (edgeCount G : Real) ≤ x) :
    edgeCount G ≤ ⌈x⌉₊ := by
  have hx : (edgeCount G : Real) ≤ (⌈x⌉₊ : Nat) :=
    h.trans (Nat.le_ceil x)
  exact_mod_cast hx

/-- The exact integer scale used by the formal upper-bound predicate. -/
noncomputable def cycleUpperNat (k n : Nat) : Nat :=
  ⌈cycleUpperScale k n⌉₊

theorem edgeCount_le_cycleUpperNat_of_real_le
    {V : Type u} {G : SimpleGraph V} {k n : Nat}
    (h : (edgeCount G : Real) ≤ cycleUpperScale k n) :
    edgeCount G ≤ cycleUpperNat k n := by
  exact edgeCount_le_natCeil_of_real_le h

end LeanCo.SizeRamsey
