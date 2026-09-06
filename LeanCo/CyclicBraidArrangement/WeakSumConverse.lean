import LeanCo.CyclicBraidArrangement.CycleFormula
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Linear-algebraic converse for constant Hamiltonian-cycle weights. -/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace WeakSumConverse

/-- Directed arcs with loops omitted, exactly the coordinate set `Eₙ` used
in the paper's ATSP affine-hull lemma. -/
abbrev Arc (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}
abbrev ArcSpace (n : ℕ) := Arc n → ℝ
abbrev DegreeSpace (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

/-- Out- and in-degree sums of an arc vector. -/
noncomputable def degreeMap (n : ℕ) : ArcSpace n →ₗ[ℝ] DegreeSpace n := by
  classical
  exact {
    toFun := fun x ↦
      (fun i ↦ ∑ e, if e.1.1 = i then x e else 0,
       fun j ↦ ∑ e, if e.1.2 = j then x e else 0)
    map_add' := by
      intro x y
      ext i
      · simp only [Pi.add_apply, Prod.fst_add]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> simp_all
      · simp only [Pi.add_apply, Prod.snd_add]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> simp_all
    map_smul' := by
      intro c x
      ext i <;>
        simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_fst, Prod.smul_snd,
          Finset.mul_sum] <;>
        apply Finset.sum_congr rfl <;>
        intro e he <;> split_ifs <;> simp_all }

/-- The off-diagonal coefficient functional associated to a matrix. -/
noncomputable def coefficientFunctional {n : ℕ} (D : Fin n → Fin n → ℝ) :
    ArcSpace n →ₗ[ℝ] ℝ := by
  classical
  exact {
    toFun := fun x ↦ ∑ e, D e.1.1 e.1.2 * x e
    map_add' := by
      intro x y
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring }

/-- Coordinate vector supported on a single directed arc. -/
noncomputable def arcBasis {n : ℕ} (e : Arc n) : ArcSpace n := by
  classical
  exact fun a ↦ if a = e then 1 else 0

theorem coefficientFunctional_arcBasis {n : ℕ} (D : Fin n → Fin n → ℝ)
    (e : Arc n) : coefficientFunctional D (arcBasis e) = D e.1.1 e.1.2 := by
  classical
  simp [coefficientFunctional, arcBasis]

theorem degreeMap_arcBasis {n : ℕ} (e : Arc n) :
    degreeMap n (arcBasis e) =
      (fun i ↦ if e.1.1 = i then (1 : ℝ) else 0,
       fun j ↦ if e.1.2 = j then (1 : ℝ) else 0) := by
  classical
  ext i
  · change (∑ a, if a.1.1 = i then (if a = e then 1 else 0) else 0) = _
    calc
      _ = ∑ a, if a = e then (if e.1.1 = i then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : a = e <;> simp [h]
      _ = _ := by simp
  · change (∑ a, if a.1.2 = i then (if a = e then 1 else 0) else 0) = _
    calc
      _ = ∑ a, if a = e then (if e.1.2 = i then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : a = e <;> simp [h]
      _ = _ := by simp

/-- A functional vanishing on every balanced arc flow factors through the
vector of out- and in-degree sums. -/
theorem factor_through_degrees {n : ℕ} (D : Fin n → Fin n → ℝ)
    (hD : ∀ x, degreeMap n x = 0 → coefficientFunctional D x = 0) :
    ∃ F : DegreeSpace n →ₗ[ℝ] ℝ,
      coefficientFunctional D = F.comp (degreeMap n) := by
  let ℓ := coefficientFunctional D
  have hrange : ℓ ∈ LinearMap.range (degreeMap n).dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact hD x (LinearMap.mem_ker.mp hx)
  rcases hrange with ⟨F, hF⟩
  exact ⟨F, hF.symm⟩

/-- Factoring through degree sums produces explicit row and column
potentials. -/
theorem weakSum_of_factors_through_degrees {n : ℕ} (D : Fin n → Fin n → ℝ)
    (hD : ∃ F : DegreeSpace n →ₗ[ℝ] ℝ,
      coefficientFunctional D = F.comp (degreeMap n)) : IsWeakSum D := by
  classical
  rcases hD with ⟨F, hF⟩
  let ρ : Fin n → ℝ := fun i ↦ F (fun a ↦ if i = a then 1 else 0, 0)
  let γ : Fin n → ℝ := fun j ↦ F (0, fun b ↦ if j = b then 1 else 0)
  refine ⟨ρ, γ, ?_⟩
  intro i j hij
  let e : Arc n := ⟨(i, j), hij⟩
  have hcoord := congrArg (fun L : ArcSpace n →ₗ[ℝ] ℝ ↦ L (arcBasis e)) hF
  rw [coefficientFunctional_arcBasis, LinearMap.comp_apply,
    degreeMap_arcBasis] at hcoord
  dsimp [e] at hcoord
  change D i j = F ((fun a ↦ if i = a then 1 else 0), 0) +
    F (0, (fun b ↦ if j = b then 1 else 0))
  rw [← F.map_add]
  have hp :
      ((fun a ↦ if i = a then (1 : ℝ) else 0), 0) +
        (0, (fun b ↦ if j = b then (1 : ℝ) else 0)) =
      ((fun a ↦ if i = a then (1 : ℝ) else 0),
        (fun b ↦ if j = b then (1 : ℝ) else 0)) := by
    ext a <;> simp
  rw [hp]
  simpa [eq_comm] using hcoord

/-- Coefficient form of the weak-sum converse: annihilating the direction
space cut out by the degree equations forces row-plus-column form. -/
theorem weakSum_of_vanishes_on_balanced {n : ℕ} (D : Fin n → Fin n → ℝ)
    (hD : ∀ x, degreeMap n x = 0 → coefficientFunctional D x = 0) :
    IsWeakSum D :=
  weakSum_of_factors_through_degrees D (factor_through_degrees D hD)

/-- Differences of members of a family of arc vectors. -/
def differenceSet {n : ℕ} {ι : Type*} (c : ι → ArcSpace n) : Set (ArcSpace n) :=
  {x | ∃ a b, x = c a - c b}

/-- Linear form of the paper's ATSP affine-hull lemma: differences of the
Hamiltonian-cycle incidence vectors span every balanced arc flow. -/
def DifferencesSpanBalanced {n : ℕ} {ι : Type*} (c : ι → ArcSpace n) : Prop :=
  LinearMap.ker (degreeMap n) ≤ Submodule.span ℝ (differenceSet c)

/-- A linear functional constant on a family vanishes on the span of all
pairwise differences from that family. -/
theorem span_differenceSet_le_ker {n : ℕ} {ι : Type*}
    (c : ι → ArcSpace n) (ℓ : ArcSpace n →ₗ[ℝ] ℝ)
    (hconst : ∀ a b, ℓ (c a) = ℓ (c b)) :
    Submodule.span ℝ (differenceSet c) ≤ LinearMap.ker ℓ := by
  rw [Submodule.span_le]
  intro x hx
  rcases hx with ⟨a, b, rfl⟩
  change ℓ (c a - c b) = 0
  rw [ℓ.map_sub, hconst a b, sub_self]

/-- Abstract weak-sum converse used with Hamiltonian-cycle incidence vectors.
The only combinatorial input is `DifferencesSpanBalanced`, precisely the
linear direction-space consequence of the cited ATSP affine-hull lemma. -/
theorem weakSum_of_constant_on_spanning_cycles {n : ℕ} {ι : Type*}
    (D : Fin n → Fin n → ℝ) (c : ι → ArcSpace n)
    (haff : DifferencesSpanBalanced c)
    (hconst : ∀ a b, coefficientFunctional D (c a) =
      coefficientFunctional D (c b)) : IsWeakSum D := by
  apply weakSum_of_vanishes_on_balanced D
  intro x hx
  have hxker : x ∈ LinearMap.ker (degreeMap n) :=
    LinearMap.mem_ker.mpr hx
  have hxspan : x ∈ Submodule.span ℝ (differenceSet c) := haff hxker
  have hle := span_differenceSet_le_ker c (coefficientFunctional D) hconst
  exact LinearMap.mem_ker.mp (hle hxspan)

/-- The directed arc used at cyclic position `k`. -/
def cycleArc {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (w : DeformationMatrix.CyclicOrdering n) (k : Fin n) : Arc n :=
  ⟨(w k, w (DeformationMatrix.nextPosition n k)),
    w.injective.ne (DeformationMatrix.nextPosition_ne_self hn k).symm⟩

/-- Incidence vector of a directed Hamiltonian cycle.  It is presented as a
sum of coordinate vectors, which also handles the paper's `n = 2`
orientation convention directly. -/
noncomputable def cycleIncidence {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (w : DeformationMatrix.CyclicOrdering n) : ArcSpace n := by
  classical
  exact fun e ↦ ∑ k, if cycleArc hn w k = e then 1 else 0

/-- Pairing a matrix with a Hamiltonian-cycle incidence vector is its
Hamiltonian cycle weight. -/
theorem coefficientFunctional_cycleIncidence {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (D : Fin n → Fin n → ℝ)
    (w : DeformationMatrix.CyclicOrdering n) :
    coefficientFunctional D (cycleIncidence hn w) =
      additiveCycleWeight D w := by
  classical
  unfold coefficientFunctional cycleIncidence additiveCycleWeight
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single (cycleArc hn w k)]
  · simp [cycleArc]
  · intro e he hne
    simp [hne.symm]
  · simp

/-- Direction-space statement of the cited ATSP affine-hull lemma for the
actual Hamiltonian-cycle incidence vectors. -/
def HamiltonianAffineHull {n : ℕ} [NeZero n] (hn : 2 ≤ n) : Prop :=
  DifferencesSpanBalanced (cycleIncidence hn)

/-- The converse direction of the paper's weak-sum theorem, conditional only
on its separately cited ATSP affine-hull lemma. -/
theorem weakSum_of_constant_hamiltonian_weight {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (haff : HamiltonianAffineHull hn)
    (D : Fin n → Fin n → ℝ)
    (hconst : ∀ a b : DeformationMatrix.CyclicOrdering n,
      additiveCycleWeight D a = additiveCycleWeight D b) : IsWeakSum D := by
  apply weakSum_of_constant_on_spanning_cycles D (cycleIncidence hn) haff
  intro a b
  rw [coefficientFunctional_cycleIncidence,
    coefficientFunctional_cycleIncidence]
  exact hconst a b

/-- Full constant-cycle characterization, with the affine-hull input made
explicit as in the paper's proof. -/
theorem constant_hamiltonian_weight_iff_weakSum {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (haff : HamiltonianAffineHull hn)
    (D : Fin n → Fin n → ℝ) :
    (∀ a b : DeformationMatrix.CyclicOrdering n,
      additiveCycleWeight D a = additiveCycleWeight D b) ↔ IsWeakSum D := by
  constructor
  · exact weakSum_of_constant_hamiltonian_weight hn haff D
  · intro hD a b
    rcases hD with ⟨ρ, γ, hD⟩
    have weight_eq (w : DeformationMatrix.CyclicOrdering n) :
        additiveCycleWeight D w = (∑ i, ρ i) + ∑ i, γ i := by
      have hadj : ∀ k, w k ≠ w (DeformationMatrix.nextPosition n k) :=
        fun k ↦ w.injective.ne
          (DeformationMatrix.nextPosition_ne_self hn k).symm
      simp_rw [additiveCycleWeight, hD _ _ (hadj _),
        Finset.sum_add_distrib]
      rw [Equiv.sum_comp w ρ]
      simpa only [Equiv.trans_apply] using congrArg
        (fun z ↦ (∑ i, ρ i) + z)
        (Equiv.sum_comp ((DeformationMatrix.nextPosition n).trans w) γ)
    rw [weight_eq a, weight_eq b]

theorem additiveCycleWeight_sub {n : ℕ} [NeZero n]
    (N M : Fin n → Fin n → ℝ) (w : DeformationMatrix.CyclicOrdering n) :
    additiveCycleWeight (fun i j ↦ N i j - M i j) w =
      additiveCycleWeight N w - additiveCycleWeight M w := by
  unfold additiveCycleWeight
  simp only [Finset.sum_sub_distrib]

/-- Matrix form of the paper's theorem: `L_N(w)-L_M(w)` is independent of
the cyclic ordering exactly when `N-M` is weak row-plus-column off the
diagonal. -/
theorem cycleWeight_difference_constant_iff_weakSum {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (haff : HamiltonianAffineHull hn)
    (M N : Fin n → Fin n → ℝ) :
    (∀ a b : DeformationMatrix.CyclicOrdering n,
      additiveCycleWeight N a - additiveCycleWeight M a =
        additiveCycleWeight N b - additiveCycleWeight M b) ↔
      IsWeakSum (fun i j ↦ N i j - M i j) := by
  rw [← constant_hamiltonian_weight_iff_weakSum hn haff]
  constructor
  · intro h a b
    simpa only [additiveCycleWeight_sub] using h a b
  · intro h a b
    simpa only [additiveCycleWeight_sub] using h a b

end WeakSumConverse

end CyclicBraidArrangement
