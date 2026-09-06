import LeanCo.QuantumLatin.Defs
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The cyclic Fourier construction

This file proves the character calculation underlying Construction 3.3 and
the odd-order input used by Theorem 1.1(2).  Its hypotheses are finite,
algebraic properties of a map `μ : ZMod N → ZMod N`; later files supply the
paper's explicit maps.
-/

open scoped BigOperators ComplexConjugate
open Finset AddChar

namespace LeanCo.QuantumLatin

variable (N : ℕ) [NeZero N]

/-- The real normalization `1 / sqrt N`, regarded as a complex scalar. -/
noncomputable def fourierScale : ℂ := ((Real.sqrt N : ℝ) : ℂ)⁻¹

theorem fourierScale_star_mul :
    conj (fourierScale N) * fourierScale N = (N : ℂ)⁻¹ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hs : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = N := by
    rw [Real.mul_self_sqrt]
    positivity
  rw [fourierScale]
  simp only [map_inv₀, Complex.conj_ofReal]
  rw [← mul_inv_rev, ← Complex.ofReal_mul, hs, Complex.ofReal_natCast]

theorem conj_stdAddChar (x : ZMod N) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hchar := AddChar.starComp_apply (R := ZMod N)
    (show 0 < ringChar (ZMod N) by
      rw [ZMod.ringChar_zmod_n]
      exact Nat.pos_of_ne_zero (NeZero.ne N))
    (φ := ZMod.stdAddChar) x
  simpa only [AddChar.inv_apply] using hchar

theorem sum_stdAddChar_mul (a : ZMod N) :
    ∑ t : ZMod N, ZMod.stdAddChar (t * a) =
      if a = 0 then (N : ℂ) else 0 := by
  simpa using AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar N)

/-- The exponent appearing in the paper's Fourier vectors. -/
def fourierExponent (μ : ZMod N → ZMod N) (i j t : ZMod N) : ZMod N :=
  i * μ t + j * t

/-- A normalized vector from the cyclic Fourier array. -/
noncomputable def fourierKet (μ : ZMod N → ZMod N) (i j : ZMod N) :
    Ket (ZMod N) :=
  fun t ↦ fourierScale N * ZMod.stdAddChar (fourierExponent N μ i j t)

theorem dot_fourierKet (μ : ZMod N → ZMod N)
    (i j i' j' : ZMod N) :
    dot (fourierKet N μ i j) (fourierKet N μ i' j') =
      (N : ℂ)⁻¹ * ∑ t : ZMod N,
        ZMod.stdAddChar ((i' - i) * μ t + (j' - j) * t) := by
  classical
  rw [dot]
  calc
    (∑ t : ZMod N,
        conj (fourierKet N μ i j t) * fourierKet N μ i' j' t) =
        ∑ t : ZMod N, (conj (fourierScale N) * fourierScale N) *
          (ZMod.stdAddChar (-(fourierExponent N μ i j t)) *
            ZMod.stdAddChar (fourierExponent N μ i' j' t)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [fourierKet, fourierKet, map_mul, conj_stdAddChar]
      ring
    _ = (conj (fourierScale N) * fourierScale N) *
        ∑ t : ZMod N,
          ZMod.stdAddChar
            (-(fourierExponent N μ i j t) + fourierExponent N μ i' j' t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      rw [map_add_eq_mul]
    _ = (N : ℂ)⁻¹ * ∑ t : ZMod N,
        ZMod.stdAddChar ((i' - i) * μ t + (j' - j) * t) := by
      rw [fourierScale_star_mul]
      apply congrArg ((N : ℂ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      simp only [fourierExponent]
      ring

/-- Algebraic certificate used by the cyclic construction.  `perm` gives
column orthogonality, `complete` gives the resolution, and `separating`
proves that no two cells represent the same projective ray. -/
structure CyclicCertificate (μ : ZMod N → ZMod N) : Prop where
  perm : Function.Bijective μ
  complete : Function.Bijective (fun t ↦ μ t + t)
  separating : ∀ a b : ZMod N,
    (∀ t, a * μ t + b * t = a * μ 0) → a = 0 ∧ b = 0

theorem normalized_character_sum (a : ZMod N) :
    (N : ℂ)⁻¹ * (∑ t : ZMod N, ZMod.stdAddChar (t * a)) =
      if a = 0 then 1 else 0 := by
  rw [sum_stdAddChar_mul]
  split_ifs with h
  · simp
  · simp

private theorem character_sum_comp_bijective
    (f : ZMod N → ZMod N) (hf : Function.Bijective f) (a : ZMod N) :
    (N : ℂ)⁻¹ * (∑ t : ZMod N, ZMod.stdAddChar (a * f t)) =
      if a = 0 then 1 else 0 := by
  let e : ZMod N ≃ ZMod N := Equiv.ofBijective f hf
  rw [show (∑ t : ZMod N, ZMod.stdAddChar (a * f t)) =
      ∑ u : ZMod N, ZMod.stdAddChar (a * u) by
    simpa [e] using e.sum_comp (fun u ↦ ZMod.stdAddChar (a * u))]
  simpa [mul_comm] using normalized_character_sum N a

/-- Construction 3.3 as a literal quantum Latin square. -/
noncomputable def cyclicQLS (μ : ZMod N → ZMod N)
    (hμ : CyclicCertificate N μ) : QuantumLatinSquare (ZMod N) where
  entry := fourierKet N μ
  row_orthonormal i j j' := by
    rw [dot_fourierKet]
    simp only [sub_self, zero_mul, zero_add]
    simpa [mul_comm, sub_eq_zero, eq_comm] using
      normalized_character_sum N (j' - j)
  col_orthonormal j i i' := by
    rw [dot_fourierKet]
    simp only [sub_self, zero_mul, add_zero]
    simpa [sub_eq_zero, eq_comm] using
      character_sum_comp_bijective N μ hμ.perm (i' - i)

private theorem complete_character_sum (μ : ZMod N → ZMod N)
    (hμ : CyclicCertificate N μ) (a : ZMod N) :
    (N : ℂ)⁻¹ *
        (∑ t : ZMod N, ZMod.stdAddChar (a * μ t + a * t)) =
      if a = 0 then 1 else 0 := by
  simpa [mul_add] using character_sum_comp_bijective N
    (fun t ↦ μ t + t) hμ.complete a

/-- The diagonals `j = i + s` resolve the cyclic Fourier square. -/
noncomputable def cyclicResolution (μ : ZMod N → ZMod N)
    (hμ : CyclicCertificate N μ) : (cyclicQLS N μ hμ).Resolution where
  column s := Equiv.addRight s
  covers i := by
    change Function.Bijective (fun s : ZMod N ↦ i + s)
    exact (Equiv.addLeft i).bijective
  orthonormal s i i' := by
    rw [cyclicQLS, dot_fourierKet]
    change (N : ℂ)⁻¹ * (∑ t : ZMod N,
        ZMod.stdAddChar
          ((i' - i) * μ t + ((i' + s) - (i + s)) * t)) =
      if i = i' then 1 else 0
    rw [show (∑ t : ZMod N,
        ZMod.stdAddChar ((i' - i) * μ t + ((i' + s) - (i + s)) * t)) =
          ∑ t : ZMod N,
            ZMod.stdAddChar ((i' - i) * μ t + (i' - i) * t) by
      apply Finset.sum_congr rfl
      intro t _
      congr 2
      ring]
    simpa [sub_eq_zero, eq_comm] using complete_character_sum N μ hμ (i' - i)

theorem fourierScale_ne_zero : fourierScale N ≠ 0 := by
  rw [fourierScale]
  apply inv_ne_zero
  rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

theorem fourierKet_apply_ne_zero (μ : ZMod N → ZMod N)
    (i j t : ZMod N) : fourierKet N μ i j t ≠ 0 := by
  rw [fourierKet]
  exact mul_ne_zero (fourierScale_ne_zero N) (by
    rw [ZMod.stdAddChar_apply]
    exact Circle.coe_ne_zero _)

/-- The separating clause of a cyclic certificate is precisely what turns
the Fourier array into `N²` distinct projective quantum states. -/
theorem cyclicQLS_maximal (μ : ZMod N → ZMod N)
    (hμ : CyclicCertificate N μ) :
    (cyclicQLS N μ hμ).HasMaximalCardinality := by
  intro i j i' j' hphase
  rcases hphase with ⟨z, _hz, hfun⟩
  have hs : fourierScale N ≠ 0 := fourierScale_ne_zero N
  have hsep : ∀ t : ZMod N,
      (i' - i) * μ t + (j' - j) * t = (i' - i) * μ 0 := by
    intro t
    have ht := congrFun hfun t
    have hzero := congrFun hfun 0
    change fourierKet N μ i j t = z * fourierKet N μ i' j' t at ht
    change fourierKet N μ i j 0 = z * fourierKet N μ i' j' 0 at hzero
    have hcross :
        fourierKet N μ i j t * fourierKet N μ i' j' 0 =
          fourierKet N μ i j 0 * fourierKet N μ i' j' t := by
      rw [ht, hzero]
      ring
    have hchar :
        ZMod.stdAddChar
            (fourierExponent N μ i j t + fourierExponent N μ i' j' 0) =
          ZMod.stdAddChar
            (fourierExponent N μ i j 0 + fourierExponent N μ i' j' t) := by
      rw [map_add_eq_mul, map_add_eq_mul]
      apply mul_left_cancel₀ (mul_ne_zero hs hs)
      calc
        (fourierScale N * fourierScale N) *
            (ZMod.stdAddChar (fourierExponent N μ i j t) *
              ZMod.stdAddChar (fourierExponent N μ i' j' 0)) =
          fourierKet N μ i j t * fourierKet N μ i' j' 0 := by
            simp only [fourierKet]
            ring
        _ = fourierKet N μ i j 0 * fourierKet N μ i' j' t := hcross
        _ = (fourierScale N * fourierScale N) *
            (ZMod.stdAddChar (fourierExponent N μ i j 0) *
              ZMod.stdAddChar (fourierExponent N μ i' j' t)) := by
            simp only [fourierKet]
            ring
    have heq := ZMod.injective_stdAddChar hchar
    simp only [fourierExponent] at heq
    linear_combination -heq
  rcases hμ.separating (i' - i) (j' - j) hsep with ⟨hi, hj⟩
  exact ⟨(sub_eq_zero.mp hi).symm, (sub_eq_zero.mp hj).symm⟩

/-- Construction 3.3, packaged with its resolution and maximality proof. -/
noncomputable def cyclicMaximalRQLS (μ : ZMod N → ZMod N)
    (hμ : CyclicCertificate N μ) : MaximalRQLS (ZMod N) where
  square := cyclicQLS N μ hμ
  resolution := cyclicResolution N μ hμ
  maximal := cyclicQLS_maximal N μ hμ

theorem existsMaximalRQLS_of_cyclicCertificate
    (μ : ZMod N → ZMod N) (hμ : CyclicCertificate N μ) :
    ExistsMaximalRQLS N := by
  simpa using existsMaximalRQLS_card (cyclicMaximalRQLS N μ hμ)

end LeanCo.QuantumLatin
