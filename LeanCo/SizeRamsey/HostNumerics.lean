import LeanCo.SizeRamsey.Numerics
import LeanCo.SizeRamsey.GraphBasics

/-!
# Numerical bridge from the random host to Claim 4.1

The probabilistic lemma states the lower edge bound over the reals.  This
file converts it, with all rounding exposed, to the division-free natural
number inequality consumed by the monochromatic density-core theorem.
-/

namespace LeanCo.SizeRamsey

noncomputable section

universe u

variable {X : Type u}

/-- The lower edge conclusion `p M² / 2 ≤ e(Γ)` implies the exact scaled
density inequality used after choosing the majority colour. -/
theorem claim_four_one_density_of_host_lower
    (Gamma : SimpleGraph X) [Fintype X]
    {k n : Nat} (hk : 2 ≤ k) (hn : 0 < n)
    (hcard : Fintype.card X = 2 * hostPartSize k n)
    (hlower : hostProbability k n * (hostPartSize k n : Real) ^ 2 / 2 ≤
      (edgeCount Gamma : Real)) :
    k * ((16 * localDegreeThreshold k) * Fintype.card X) ≤
      2 * edgeCount Gamma := by
  have hthreshold := sixteen_mul_localDegreeThreshold_le hk
  have hk0 : (0 : Real) ≤ k := by positivity
  have hM0 : (0 : Real) ≤ hostPartSize k n := by positivity
  have hmult0 : (0 : Real) ≤ (k : Real) * (2 * hostPartSize k n) :=
    mul_nonneg hk0 (mul_nonneg (by norm_num) hM0)
  have hscaled := mul_le_mul_of_nonneg_right hthreshold hmult0
  have hidentity :
      50000 * Real.log (k : Real) *
          ((k : Real) * (2 * hostPartSize k n)) =
        hostProbability k n * (hostPartSize k n : Real) ^ 2 := by
    rw [probability_mul_partSize_sq hn]
    simp only [hostPartSize, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hlower' :
      hostProbability k n * (hostPartSize k n : Real) ^ 2 ≤
        2 * (edgeCount Gamma : Real) := by
    nlinarith
  have hreal :
      (k : Real) *
          ((16 : Real) * localDegreeThreshold k) *
          Fintype.card X ≤
        2 * (edgeCount Gamma : Real) := by
    rw [hcard]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (k : Real) * ((16 : Real) * localDegreeThreshold k) *
          (2 * hostPartSize k n) =
          ((16 : Real) * localDegreeThreshold k) *
            ((k : Real) * (2 * hostPartSize k n)) := by ring
      _ ≤ 50000 * Real.log (k : Real) *
          ((k : Real) * (2 * hostPartSize k n)) := hscaled
      _ = hostProbability k n * (hostPartSize k n : Real) ^ 2 := hidentity
      _ ≤ 2 * (edgeCount Gamma : Real) := hlower'
  have hnat :
      k * (16 * localDegreeThreshold k) * Fintype.card X ≤
        2 * edgeCount Gamma := by
    exact_mod_cast hreal
  simpa only [Nat.mul_assoc] using hnat

end

end LeanCo.SizeRamsey
