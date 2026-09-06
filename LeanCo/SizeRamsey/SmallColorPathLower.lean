import LeanCo.SizeRamsey.GraphBasics
import LeanCo.SizeRamsey.PathLowerBound

/-!
# The bounded-colour part of the path size--Ramsey lower bound

The asymptotic BLS argument only applies for sufficiently large colour
count.  For a fixed bounded interval of colours, a small universal constant
reduces the claimed edge threshold to an elementary observation: a copy of
`P_n` uses `n` non-isolated vertices, while a graph with `e` edges has at
most `2e` non-isolated vertices.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u}

/-- The support of a finite graph has at most twice as many vertices as the
graph has edges. -/
theorem card_support_le_twice_edgeCount [Fintype V]
    (G : SimpleGraph V) :
    G.support.ncard ≤ 2 * edgeCount G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  calc
    G.support.ncard = G.support.toFinset.card :=
      Set.ncard_eq_toFinset_card' G.support
    _ =
        ∑ v ∈ G.support.toFinset, 1 := by simp
    _ ≤ ∑ v ∈ G.support.toFinset, G.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      exact (G.degree_pos_iff_mem_support v).mpr (by simpa using hv)
    _ = 2 * G.edgeFinset.card := G.sum_degrees_support_eq_twice_card_edges
    _ = 2 * edgeCount G := by rw [edgeCount_eq_card_edgeFinset]

/-- A graph with fewer than `n/2` edges cannot contain `P_n`.  The condition
is written without natural division, which also makes all rounding explicit.
-/
theorem pathGraph_free_of_twice_edgeCount_lt [Fintype V]
    (G : SimpleGraph V) {n : ℕ} (hn : 2 ≤ n)
    (hedge : 2 * edgeCount G < n) :
    (pathGraph n).Free G := by
  classical
  intro hcopy
  obtain ⟨f⟩ := hcopy
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hall : ∀ x : Fin n, f x ∈ G.support := by
    intro x
    have hx : x ∈ (pathGraph n).support := by
      rw [(pathGraph_preconnected n).support_eq_univ]
      trivial
    obtain ⟨y, hxy⟩ := (pathGraph n).mem_support.mp hx
    exact (f.toHom.map_adj hxy).mem_support_left
  let e : Fin n ↪ ↥G.support.toFinset :=
    { toFun := fun x => ⟨f x, by simpa using hall x⟩
      inj' := by
        intro x y hxy
        apply f.injective
        exact congrArg Subtype.val hxy }
  have hcard : n ≤ G.support.toFinset.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective e e.injective
  have hsupport := card_support_le_twice_edgeCount G
  rw [Set.ncard_eq_toFinset_card'] at hsupport
  omega

/-- If `Fin r` is nonempty, the constant colouring avoids `P_n` whenever
the whole host is already `P_n`-free by the edge-count criterion. -/
theorem exists_path_avoidingColoring_of_twice_edgeCount_lt
    [Fintype V] (G : SimpleGraph V) {r n : ℕ}
    (hr : 0 < r) (hn : 2 ≤ n)
    (hedge : 2 * edgeCount G < n) :
    ∃ C : G.EdgeLabeling (Fin r),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  have hfree := pathGraph_free_of_twice_edgeCount_lt G hn hedge
  let C : G.EdgeLabeling (Fin r) := fun _ => ⟨0, hr⟩
  refine ⟨C, ?_⟩
  intro colour hcopy
  exact hfree (hcopy.trans_le C.labelGraph_le)

/-- A convenient natural threshold: fewer than `ceil(n/2)` edges suffices
for the constant colouring. -/
theorem exists_path_avoidingColoring_of_edgeCount_lt_half
    [Fintype V] (G : SimpleGraph V) {r n : ℕ}
    (hr : 0 < r) (hn : 2 ≤ n)
    (hedge : edgeCount G < (n + 1) / 2) :
    ∃ C : G.EdgeLabeling (Fin r),
      AvoidsMonochromaticCopy (pathGraph n) C := by
  apply exists_path_avoidingColoring_of_twice_edgeCount_lt G hr hn
  omega

/-- A uniform positive constant for all colour counts at most `R`.  The
extra `R+1` avoids a separate degenerate case when the bounded interval is
empty. -/
def boundedColorPathConstant (R : ℕ) : ℝ :=
  1 / (4 * ((R : ℝ) + 1) ^ 3)

theorem boundedColorPathConstant_pos (R : ℕ) :
    0 < boundedColorPathConstant R := by
  unfold boundedColorPathConstant
  positivity

/-- At bounded colour count, the scaled BLS threshold is small enough for
the elementary support argument.  This statement is valid for every `n`,
including the degenerate path sizes. -/
theorem two_mul_pathLowerScale_boundedColor_le
    {R r n : ℕ} (hr : 2 ≤ r) (hrR : r ≤ R) :
    2 * pathLowerScale (boundedColorPathConstant R) r n ≤ n := by
  have hrReal : (0 : ℝ) ≤ r := by positivity
  have hlogNonneg : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  have hlog : Real.log (r : ℝ) ≤ (r : ℝ) :=
    Real.log_le_self hrReal
  have hrRReal : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
  have hrRone : (r : ℝ) ≤ (R : ℝ) + 1 := by linarith
  have hcube : (r : ℝ) ^ 3 ≤ ((R : ℝ) + 1) ^ 3 := by
    exact pow_le_pow_left₀ hrReal hrRone 3
  have hproduct : (r : ℝ) ^ 2 * Real.log (r : ℝ) ≤ (r : ℝ) ^ 3 := by
    calc
      (r : ℝ) ^ 2 * Real.log (r : ℝ) ≤ (r : ℝ) ^ 2 * r :=
        mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
      _ = (r : ℝ) ^ 3 := by ring
  have hcNonneg : 0 ≤ boundedColorPathConstant R :=
    (boundedColorPathConstant_pos R).le
  have hcoefficient :
      boundedColorPathConstant R * (r : ℝ) ^ 2 * Real.log (r : ℝ) ≤
        (1 : ℝ) / 4 := by
    calc
      boundedColorPathConstant R * (r : ℝ) ^ 2 * Real.log (r : ℝ) =
          boundedColorPathConstant R *
            ((r : ℝ) ^ 2 * Real.log (r : ℝ)) := by ring
      _ ≤ boundedColorPathConstant R * (r : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hproduct hcNonneg
      _ ≤ boundedColorPathConstant R * ((R : ℝ) + 1) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube hcNonneg
      _ = (1 : ℝ) / 4 := by
        unfold boundedColorPathConstant
        field_simp
  let x : ℝ := boundedColorPathConstant R * (r : ℝ) ^ 2 *
    Real.log (r : ℝ) * n
  have hxNonneg : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hxUpper : x ≤ (n : ℝ) / 4 := by
    dsimp only [x]
    calc
      boundedColorPathConstant R * (r : ℝ) ^ 2 *
          Real.log (r : ℝ) * n ≤ ((1 : ℝ) / 4) * n :=
        mul_le_mul_of_nonneg_right hcoefficient (by positivity)
      _ = (n : ℝ) / 4 := by ring
  have hfloor : ((pathLowerScale
      (boundedColorPathConstant R) r n : ℕ) : ℝ) ≤ x := by
    change ((⌊x⌋₊ : ℕ) : ℝ) ≤ x
    exact Nat.floor_le hxNonneg
  have hreal : (2 : ℝ) *
      (pathLowerScale (boundedColorPathConstant R) r n : ℝ) ≤ n := by
    nlinarith
  exact_mod_cast hreal

/-- Complete bounded-colour package.  No lower bound on `n` is needed: for
`n ≤ 1` the chosen scale is zero, and for `n ≥ 2` the constant colouring
above applies. -/
theorem exists_boundedColor_pathSizeRamseyLowerBound (R : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ r n : ℕ, 2 ≤ r → r ≤ R →
        IsPathSizeRamseyLowerBound r n (pathLowerScale c r n) := by
  refine ⟨boundedColorPathConstant R, boundedColorPathConstant_pos R, ?_⟩
  intro r n hr hrR N G hedge
  have hscale := two_mul_pathLowerScale_boundedColor_le
    (n := n) hr hrR
  by_cases hn : 2 ≤ n
  · apply exists_path_avoidingColoring_of_twice_edgeCount_lt G (by omega) hn
    omega
  · have hscaleZero : pathLowerScale
        (boundedColorPathConstant R) r n = 0 := by
      omega
    rw [hscaleZero] at hedge
    omega

end

end LeanCo.SizeRamsey
