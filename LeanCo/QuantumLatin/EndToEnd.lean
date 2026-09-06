import LeanCo.QuantumLatin.FinalOrders

/-!
# End-to-end entry point for arXiv:2608.29201

The declaration below is the canonical public alias for the order
classification proved in `FinalOrders`.
-/

namespace LeanCo.QuantumLatin

/-- Zhang--Cao, Theorem 1.2. -/
theorem zhangCao_theorem_1_2_endToEnd {v : ℕ} (hv : 7 ≤ v)
    (hvNotExceptional : ¬ IsExceptionalOrder v) : ExistsMaximalRQLS v :=
  zhangCao_theorem_1_2 hv hvNotExceptional

end LeanCo.QuantumLatin
