import LeanCo.LaplacianLFunctions.Picard
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Effective divisor classes and the Baker--Norine rank

This file formalizes the part of the Baker--Norine divisor theory needed to
define the graph `L`-functions in arXiv:2608.29981.  For a divisor class `C`,
we define

`h(C) = min { degree(E) | E is effective and C - [E] has no effective representative }`.

This is the paper's Definition 2.5, expressed intrinsically on the Picard
group.  In particular, it is invariant under linear equivalence by
construction.  We also prove the basic characterization

`0 < h(C) <-> C has an effective representative`

and identify the effective degree-one classes with the vertex classes.
-/

namespace LeanCo.LaplacianLFunctions

namespace Divisor

variable {V : Type*} [Fintype V]

/-- A divisor is effective when every coefficient is nonnegative. -/
def IsEffective (D : Divisor V) : Prop :=
  ∀ v, 0 ≤ D v

@[simp]
theorem isEffective_zero : IsEffective (0 : Divisor V) := by
  intro v
  simp

theorem IsEffective.add {D E : Divisor V}
    (hD : IsEffective D) (hE : IsEffective E) : IsEffective (D + E) := by
  intro v
  exact add_nonneg (hD v) (hE v)

theorem IsEffective.degree_nonneg {D : Divisor V} (hD : IsEffective D) :
    0 ≤ degree D := by
  exact Finset.sum_nonneg fun v _ ↦ hD v

/-- An effective divisor of degree zero is the zero divisor. -/
theorem IsEffective.eq_zero_of_degree_eq_zero {D : Divisor V}
    (hD : IsEffective D) (hdeg : degree D = 0) : D = 0 := by
  exact (Fintype.sum_eq_zero_iff_of_nonneg hD).mp
    (by simpa [degree] using hdeg)

/-- The effective divisor consisting of `n` chips at one vertex. -/
def vertexMultiple [DecidableEq V] (n : ℕ) (v : V) : Divisor V :=
  (n : ℤ) • vertexDivisor v

variable [DecidableEq V]

@[simp]
theorem vertexMultiple_apply (n : ℕ) (v w : V) :
    vertexMultiple n v w = if w = v then (n : ℤ) else 0 := by
  simp [vertexMultiple, vertexDivisor]

@[simp]
theorem degree_vertexMultiple (n : ℕ) (v : V) :
    degree (vertexMultiple n v) = (n : ℤ) := by
  simp [vertexMultiple]

theorem isEffective_vertexMultiple (n : ℕ) (v : V) :
    IsEffective (vertexMultiple n v) := by
  intro w
  simp only [vertexMultiple_apply]
  split_ifs <;> positivity

@[simp]
theorem isEffective_vertexDivisor (v : V) :
    IsEffective (vertexDivisor v) := by
  simpa [vertexMultiple] using isEffective_vertexMultiple 1 v

/-- Every effective divisor of degree one is concentrated at a unique
vertex.  Only existence is needed below; uniqueness follows immediately from
the pointwise description. -/
theorem IsEffective.eq_vertexDivisor_of_degree_one {D : Divisor V}
    (hD : IsEffective D) (hdeg : degree D = 1) :
    ∃ v : V, D = vertexDivisor v := by
  classical
  have hne : D ≠ 0 := by
    intro hzero
    subst D
    simp at hdeg
  have hex : ∃ v : V, D v ≠ 0 := by
    by_contra h
    apply hne
    funext v
    by_contra hv
    exact h ⟨v, hv⟩
  obtain ⟨v, hvne⟩ := hex
  have hvpos : 0 < D v := lt_of_le_of_ne (hD v) (Ne.symm hvne)
  have hsplit :
      D v + ∑ w ∈ (Finset.univ.erase v), D w = 1 := by
    rw [← hdeg]
    rw [degree]
    exact Finset.add_sum_erase _ _ (Finset.mem_univ v)
  have hrest_nonneg : 0 ≤ ∑ w ∈ (Finset.univ.erase v), D w := by
    exact Finset.sum_nonneg fun w _ ↦ hD w
  have hvone : D v = 1 := by omega
  have hrest_zero : ∑ w ∈ (Finset.univ.erase v), D w = 0 := by omega
  have hzero_off : ∀ w ∈ Finset.univ.erase v, D w = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _ ↦ hD w)).mp hrest_zero
  refine ⟨v, funext fun w ↦ ?_⟩
  by_cases hw : w = v
  · subst w
    simp [hvone]
  · have hwmem : w ∈ Finset.univ.erase v := by simp [hw]
    simp [vertexDivisor, hw, hzero_off w hwmem]

end Divisor

namespace LooplessMultigraph

variable {V : Type*} [Fintype V]

/-- The complete linear system of a Picard class, represented as the set of
its effective divisor representatives. -/
def effectiveRepresentatives (G : LooplessMultigraph V) (C : G.Picard) :
    Set (Divisor V) :=
  {D | Divisor.IsEffective D ∧ G.divisorClass D = C}

/-- A divisor class is effective when its complete linear system is nonempty. -/
def HasEffectiveRepresentative (G : LooplessMultigraph V) (C : G.Picard) : Prop :=
  (G.effectiveRepresentatives C).Nonempty

theorem hasEffectiveRepresentative_iff (G : LooplessMultigraph V)
    (C : G.Picard) :
    G.HasEffectiveRepresentative C ↔
      ∃ D : Divisor V, Divisor.IsEffective D ∧ G.divisorClass D = C := by
  rfl

theorem hasEffectiveRepresentative_divisorClass_iff
    (G : LooplessMultigraph V) (D : Divisor V) :
    G.HasEffectiveRepresentative (G.divisorClass D) ↔
      ∃ E : Divisor V, Divisor.IsEffective E ∧
        G.divisorClass E = G.divisorClass D := by
  rfl

theorem hasEffectiveRepresentative_divisorClass_of_effective
    (G : LooplessMultigraph V) {D : Divisor V}
    (hD : Divisor.IsEffective D) :
    G.HasEffectiveRepresentative (G.divisorClass D) := by
  exact ⟨D, hD, rfl⟩

theorem not_hasEffectiveRepresentative_of_picardDegree_neg
    (G : LooplessMultigraph V) (C : G.Picard)
    (hdeg : G.picardDegree C < 0) :
    ¬ G.HasEffectiveRepresentative C := by
  rintro ⟨D, hD, hclass⟩
  have hdegree_eq : Divisor.degree D = G.picardDegree C := by
    calc
      Divisor.degree D = G.picardDegree (G.divisorClass D) :=
        (G.picardDegree_divisorClass D).symm
      _ = G.picardDegree C := congrArg G.picardDegree hclass
  have := hD.degree_nonneg
  omega

/-- `n` is an admissible value in the minimization defining `h(C)`. -/
def HAdmissible (G : LooplessMultigraph V) (C : G.Picard) (n : ℕ) : Prop :=
  ∃ E : Divisor V,
    Divisor.IsEffective E ∧
      Divisor.degree E = (n : ℤ) ∧
      ¬ G.HasEffectiveRepresentative (C - G.divisorClass E)

/-- The minimization set defining `h(C)` is nonempty.  A sufficiently large
multiple of one vertex makes the residual class have negative degree. -/
theorem exists_hAdmissible (G : LooplessMultigraph V) [Nonempty V]
    [DecidableEq V] (C : G.Picard) :
    ∃ n : ℕ, G.HAdmissible C n := by
  let n : ℕ := (G.picardDegree C).toNat + 1
  let v : V := Classical.choice (inferInstance : Nonempty V)
  let E : Divisor V := Divisor.vertexMultiple n v
  refine ⟨n, E, Divisor.isEffective_vertexMultiple n v,
    Divisor.degree_vertexMultiple n v, ?_⟩
  apply G.not_hasEffectiveRepresentative_of_picardDegree_neg
  have hlt : G.picardDegree C < (n : ℤ) := by
    dsimp only [n]
    by_cases hnonneg : 0 ≤ G.picardDegree C
    · calc
        G.picardDegree C = ((G.picardDegree C).toNat : ℤ) :=
          (Int.toNat_of_nonneg hnonneg).symm
        _ < (((G.picardDegree C).toNat + 1 : ℕ) : ℤ) := by omega
    · have hneg : G.picardDegree C < 0 := lt_of_not_ge hnonneg
      have hn : 0 ≤ ((G.picardDegree C).toNat + 1 : ℕ) := Nat.zero_le _
      exact lt_of_lt_of_le hneg (by exact_mod_cast hn)
  rw [LinearMap.map_sub, G.picardDegree_divisorClass]
  simpa [E] using sub_neg.mpr hlt

/-- Baker--Norine's `h` invariant of a divisor class.  This is the exact
minimum appearing in Definition 2.5 of arXiv:2608.29981. -/
noncomputable def h (G : LooplessMultigraph V) [Nonempty V]
    [DecidableEq V] (C : G.Picard) : ℕ :=
  by
    classical
    exact Nat.find (G.exists_hAdmissible C)

theorem h_spec (G : LooplessMultigraph V) [Nonempty V]
    [DecidableEq V] (C : G.Picard) :
    G.HAdmissible C (G.h C) := by
  classical
  exact Nat.find_spec (G.exists_hAdmissible C)

/-- `h(C)` is no larger than any admissible degree. -/
theorem h_min (G : LooplessMultigraph V) [Nonempty V]
    [DecidableEq V] (C : G.Picard) {n : ℕ}
    (hn : G.HAdmissible C n) :
    G.h C ≤ n := by
  classical
  exact Nat.find_min' (G.exists_hAdmissible C) hn

/-- Exact minimum characterization of `h`. -/
theorem h_eq_iff (G : LooplessMultigraph V) [Nonempty V]
    [DecidableEq V] (C : G.Picard) (n : ℕ) :
    G.h C = n ↔
      G.HAdmissible C n ∧ ∀ m, G.HAdmissible C m → n ≤ m := by
  constructor
  · intro heq
    subst n
    exact ⟨G.h_spec C, fun m hm ↦ G.h_min C hm⟩
  · rintro ⟨hn, hleast⟩
    exact Nat.le_antisymm (G.h_min C hn) (hleast _ (G.h_spec C))

/-- A noneffective class has `h = 0`. -/
theorem h_eq_zero_of_not_hasEffectiveRepresentative
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (C : G.Picard) (hC : ¬ G.HasEffectiveRepresentative C) :
    G.h C = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply G.h_min C
  refine ⟨(0 : Divisor V), Divisor.isEffective_zero, by simp, ?_⟩
  simpa using hC

/-- If `h(C)=0`, then `C` has no effective representative. -/
theorem not_hasEffectiveRepresentative_of_h_eq_zero
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (C : G.Picard) (hzero : G.h C = 0) :
    ¬ G.HasEffectiveRepresentative C := by
  obtain ⟨E, hE, hEdeg, hres⟩ := G.h_spec C
  rw [hzero] at hEdeg
  have hEzero : E = 0 := hE.eq_zero_of_degree_eq_zero (by simpa using hEdeg)
  simpa [hEzero] using hres

/-- The basic Baker--Norine characterization used by the recovery theorem:
`h(C)` is positive exactly when `C` has an effective representative. -/
theorem h_pos_iff_hasEffectiveRepresentative
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (C : G.Picard) :
    0 < G.h C ↔ G.HasEffectiveRepresentative C := by
  constructor
  · intro hpos
    by_contra hC
    have := G.h_eq_zero_of_not_hasEffectiveRepresentative C hC
    omega
  · intro hC
    by_contra hnotpos
    have hzero : G.h C = 0 := by omega
    exact (G.not_hasEffectiveRepresentative_of_h_eq_zero C hzero) hC

@[simp]
theorem h_eq_zero_iff_not_hasEffectiveRepresentative
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (C : G.Picard) :
    G.h C = 0 ↔ ¬ G.HasEffectiveRepresentative C := by
  exact ⟨G.not_hasEffectiveRepresentative_of_h_eq_zero C,
    G.h_eq_zero_of_not_hasEffectiveRepresentative C⟩

/-- The divisor-level notation for `h`; it depends only on the divisor class. -/
noncomputable def divisorH (G : LooplessMultigraph V) [Nonempty V]
    [DecidableEq V] (D : Divisor V) : ℕ :=
  G.h (G.divisorClass D)

theorem divisorH_eq_of_divisorClass_eq
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    {D E : Divisor V} (hDE : G.divisorClass D = G.divisorClass E) :
    G.divisorH D = G.divisorH E := by
  simp [divisorH, hDE]

theorem divisorH_eq_of_sub_mem_laplacianLattice
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    {D E : Divisor V} (hDE : D - E ∈ G.laplacianLattice) :
    G.divisorH D = G.divisorH E := by
  apply G.divisorH_eq_of_divisorClass_eq
  exact (G.divisorClass_eq_iff_sub_mem D E).2 hDE

/-- The Baker--Norine rank, with the conventional value `-1` for a class
without an effective representative. -/
noncomputable def bakerNorineRank (G : LooplessMultigraph V) [Nonempty V]
    [DecidableEq V] (C : G.Picard) : ℤ :=
  (G.h C : ℤ) - 1

@[simp]
theorem bakerNorineRank_add_one
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (C : G.Picard) :
    G.bakerNorineRank C + 1 = (G.h C : ℤ) := by
  simp [bakerNorineRank]

theorem bakerNorineRank_eq_neg_one_iff
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (C : G.Picard) :
    G.bakerNorineRank C = -1 ↔ ¬ G.HasEffectiveRepresentative C := by
  constructor
  · intro hrank
    have hzero : G.h C = 0 := by
      simp only [bakerNorineRank] at hrank
      omega
    exact G.not_hasEffectiveRepresentative_of_h_eq_zero C hzero
  · intro hC
    have hzero := G.h_eq_zero_of_not_hasEffectiveRepresentative C hC
    simp [bakerNorineRank, hzero]

/-- Effective degree-one divisor classes are exactly the classes of vertex
divisors. -/
theorem hasEffectiveRepresentative_degree_one_iff
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (C : G.PicardDegree 1) :
    G.HasEffectiveRepresentative (C : G.Picard) ↔
      ∃ v : V, C = G.vertexClass v := by
  constructor
  · rintro ⟨D, hD, hclass⟩
    have hdeg : Divisor.degree D = 1 := by
      calc
        Divisor.degree D = G.picardDegree (G.divisorClass D) :=
          (G.picardDegree_divisorClass D).symm
        _ = G.picardDegree (C : G.Picard) := congrArg G.picardDegree hclass
        _ = 1 := C.2
    obtain ⟨v, rfl⟩ := hD.eq_vertexDivisor_of_degree_one hdeg
    refine ⟨v, Subtype.ext ?_⟩
    simpa using hclass.symm
  · rintro ⟨v, rfl⟩
    exact G.hasEffectiveRepresentative_divisorClass_of_effective
      (Divisor.isEffective_vertexDivisor v)

/-- Equivalently, the positive-`h` degree-one classes are exactly the vertex
classes. -/
theorem h_pos_degree_one_iff_vertexClass
    (G : LooplessMultigraph V) [Nonempty V] [DecidableEq V]
    (C : G.PicardDegree 1) :
    0 < G.h (C : G.Picard) ↔ ∃ v : V, C = G.vertexClass v := by
  rw [G.h_pos_iff_hasEffectiveRepresentative]
  exact G.hasEffectiveRepresentative_degree_one_iff C

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
