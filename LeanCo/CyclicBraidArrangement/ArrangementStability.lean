import LeanCo.CyclicBraidArrangement.ArrangementCharacteristic
import Mathlib.Data.ZMod.Basic

/-!
# Stability of integral difference equations modulo a large modulus

For a fixed finite family of equations `x_target - x_source = distance`, a
solution modulo a sufficiently large modulus lifts to an integral solution.
The proof chooses one defining equation above each edge of the underlying
simple graph and integrates these edge increments along bounded simple paths.
-/

namespace CyclicBraidArrangement

open scoped BigOperators

namespace DeformationMatrix

variable {n : ℕ}

/-- A uniform bound for every distance occurring in the arrangement. -/
noncomputable def equationWeightBound (M : DeformationMatrix n) : ℕ :=
  ∑ e : M.ForbiddenEquation, e.distance M

private theorem equationGraph_adj_cases (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) {a b : Fin n}
    (h : (M.equationGraph S).Adj a b) :
    (∃ e ∈ S, e.source M = a ∧ e.target M = b) ∨
      (∃ e ∈ S, e.source M = b ∧ e.target M = a) := by
  change (SimpleGraph.fromRel fun a b ↦
    ∃ e ∈ S, e.source M = a ∧ e.target M = b).Adj a b at h
  rw [SimpleGraph.fromRel_adj] at h
  exact h.2

/-- A signed integer increment chosen above an oriented edge of the equation
graph.  Reversing an available defining equation negates its distance. -/
noncomputable def chosenEdgeIncrement (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) {a b : Fin n}
    (h : (M.equationGraph S).Adj a b) : ℤ :=
  if hab : ∃ e ∈ S, e.source M = a ∧ e.target M = b then
    (Classical.choose hab).distance M
  else
    -((Classical.choose ((equationGraph_adj_cases M S h).resolve_left hab)).distance M : ℤ)

theorem chosenEdgeIncrement_natAbs_le (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) {a b : Fin n}
    (h : (M.equationGraph S).Adj a b) :
    (M.chosenEdgeIncrement S h).natAbs ≤ M.equationWeightBound := by
  classical
  unfold chosenEdgeIncrement
  split_ifs with hab
  · let e := Classical.choose hab
    have he : e ∈ (Finset.univ : Finset M.ForbiddenEquation) := Finset.mem_univ e
    simpa [e, equationWeightBound] using
      (Finset.single_le_sum (f := fun u : M.ForbiddenEquation ↦ u.distance M)
        (fun _ _ ↦ Nat.zero_le _) he)
  · let hba := (equationGraph_adj_cases M S h).resolve_left hab
    let e := Classical.choose hba
    have he : e ∈ (Finset.univ : Finset M.ForbiddenEquation) := Finset.mem_univ e
    simpa [e, hba, equationWeightBound] using
      (Finset.single_le_sum (f := fun u : M.ForbiddenEquation ↦ u.distance M)
        (fun _ _ ↦ Nat.zero_le _) he)

theorem intCast_chosenEdgeIncrement_eq_sub (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) {q : ℕ}
    (x : M.EquationSolutions (ZMod q) S) {a b : Fin n}
    (h : (M.equationGraph S).Adj a b) :
    (M.chosenEdgeIncrement S h : ZMod q) = x.1 b - x.1 a := by
  classical
  unfold chosenEdgeIncrement
  split_ifs with hab
  · let e := Classical.choose hab
    have he := Classical.choose_spec hab
    have hx := x.2 e he.1
    change x.1 (e.target M) - x.1 (e.source M) =
      (e.distance M : ZMod q) at hx
    rw [he.2.1, he.2.2] at hx
    simpa [e] using hx.symm
  · let hba := (equationGraph_adj_cases M S h).resolve_left hab
    let e := Classical.choose hba
    have he := Classical.choose_spec hba
    have hx := x.2 e he.1
    change x.1 (e.target M) - x.1 (e.source M) =
      (e.distance M : ZMod q) at hx
    rw [he.2.1, he.2.2] at hx
    have hneg : -(e.distance M : ZMod q) = x.1 b - x.1 a := by
      linear_combination hx
    simpa [e] using hneg

/-- Integral of the chosen increments along a graph walk. -/
noncomputable def walkIncrement (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) :
    {a b : Fin n} → (M.equationGraph S).Walk a b → ℤ
  | _, _, .nil => 0
  | _, _, .cons h p => M.chosenEdgeIncrement S h + M.walkIncrement S p

theorem intCast_walkIncrement_eq_sub (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) {q : ℕ}
    (x : M.EquationSolutions (ZMod q) S) {a b : Fin n}
    (p : (M.equationGraph S).Walk a b) :
    (M.walkIncrement S p : ZMod q) = x.1 b - x.1 a := by
  induction p with
  | nil => simp [walkIncrement]
  | cons h p ih =>
      rw [walkIncrement, Int.cast_add,
        M.intCast_chosenEdgeIncrement_eq_sub S x h, ih]
      ring

theorem walkIncrement_natAbs_le (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) {a b : Fin n}
    (p : (M.equationGraph S).Walk a b) :
    (M.walkIncrement S p).natAbs ≤ p.length * M.equationWeightBound := by
  induction p with
  | nil => simp [walkIncrement]
  | cons h p ih =>
      rw [walkIncrement]
      calc
        (M.chosenEdgeIncrement S h + M.walkIncrement S p).natAbs ≤
            (M.chosenEdgeIncrement S h).natAbs +
              (M.walkIncrement S p).natAbs := Int.natAbs_add_le _ _
        _ ≤ M.equationWeightBound + p.length * M.equationWeightBound :=
          Nat.add_le_add (M.chosenEdgeIncrement_natAbs_le S h) ih
        _ = (SimpleGraph.Walk.cons h p).length * M.equationWeightBound := by
          simp [Nat.add_mul, Nat.add_comm]

/-- A deterministic representative of the connected component of `v`. -/
noncomputable def componentRoot (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) (v : Fin n) : Fin n :=
  Quot.out ((M.equationGraph S).connectedComponentMk v)

theorem connectedComponentMk_componentRoot (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) (v : Fin n) :
    (M.equationGraph S).connectedComponentMk (M.componentRoot S v) =
      (M.equationGraph S).connectedComponentMk v := by
  simp [componentRoot, SimpleGraph.connectedComponentMk]

theorem componentRoot_eq_of_adj (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) {a b : Fin n}
    (h : (M.equationGraph S).Adj a b) :
    M.componentRoot S a = M.componentRoot S b := by
  unfold componentRoot
  apply congrArg Quot.out
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h

/-- A bounded simple path from the chosen component representative to `v`. -/
noncomputable def componentRootPath (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) (v : Fin n) :
    (M.equationGraph S).Walk (M.componentRoot S v) v :=
  ((SimpleGraph.ConnectedComponent.exact
    (M.connectedComponentMk_componentRoot S v)).some).toPath

theorem componentRootPath_isPath (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) (v : Fin n) :
    (M.componentRootPath S v).IsPath :=
  (((SimpleGraph.ConnectedComponent.exact
    (M.connectedComponentMk_componentRoot S v)).some).toPath).2

theorem componentRootPath_length_lt (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) (v : Fin n) :
    (M.componentRootPath S v).length < n := by
  simpa using (M.componentRootPath_isPath S v).length_lt

/-- The integral potential obtained by integrating the chosen edge increments
from the deterministic root of each connected component. -/
noncomputable def modularLiftPotential (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) (v : Fin n) : ℤ :=
  M.walkIncrement S (M.componentRootPath S v)

theorem modularLiftPotential_natAbs_le (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) (v : Fin n) :
    (M.modularLiftPotential S v).natAbs ≤ n * M.equationWeightBound := by
  unfold modularLiftPotential
  calc
    (M.walkIncrement S (M.componentRootPath S v)).natAbs ≤
        (M.componentRootPath S v).length * M.equationWeightBound :=
      M.walkIncrement_natAbs_le S (M.componentRootPath S v)
    _ ≤ n * M.equationWeightBound :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt (M.componentRootPath_length_lt S v))

theorem intCast_modularLiftPotential_eq_sub (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) {q : ℕ}
    (x : M.EquationSolutions (ZMod q) S) (v : Fin n) :
    (M.modularLiftPotential S v : ZMod q) =
      x.1 v - x.1 (M.componentRoot S v) := by
  exact M.intCast_walkIncrement_eq_sub S x (M.componentRootPath S v)

/-- A concrete modulus threshold for stability of all selected intersections. -/
noncomputable def equationStabilityBound (M : DeformationMatrix n) : ℕ :=
  2 * n * M.equationWeightBound + M.equationWeightBound + 1

private theorem discrepancy_natAbs_le (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) (e : M.ForbiddenEquation) :
    (M.modularLiftPotential S (e.target M) -
      M.modularLiftPotential S (e.source M) - (e.distance M : ℤ)).natAbs ≤
        2 * n * M.equationWeightBound + M.equationWeightBound := by
  have ht := M.modularLiftPotential_natAbs_le S (e.target M)
  have hs := M.modularLiftPotential_natAbs_le S (e.source M)
  have hd : e.distance M ≤ M.equationWeightBound := by
    classical
    exact Finset.single_le_sum
      (f := fun u : M.ForbiddenEquation ↦ u.distance M)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ e)
  have hsub := Int.natAbs_add_le
    (M.modularLiftPotential S (e.target M))
    (-M.modularLiftPotential S (e.source M))
  have hall := Int.natAbs_add_le
    (M.modularLiftPotential S (e.target M) +
      -M.modularLiftPotential S (e.source M))
    (-(e.distance M : ℤ))
  calc
    (M.modularLiftPotential S (e.target M) -
        M.modularLiftPotential S (e.source M) - (e.distance M : ℤ)).natAbs =
        (M.modularLiftPotential S (e.target M) +
          -M.modularLiftPotential S (e.source M) +
            -(e.distance M : ℤ)).natAbs := by simp [sub_eq_add_neg]
    _ ≤ (M.modularLiftPotential S (e.target M) +
          -M.modularLiftPotential S (e.source M)).natAbs +
            (-(e.distance M : ℤ)).natAbs := hall
    _ ≤ ((M.modularLiftPotential S (e.target M)).natAbs +
          (-M.modularLiftPotential S (e.source M)).natAbs) +
            (e.distance M) := by
      exact Nat.add_le_add hsub (by simp)
    _ = (M.modularLiftPotential S (e.target M)).natAbs +
          (M.modularLiftPotential S (e.source M)).natAbs + e.distance M := by
      simp
    _ ≤ n * M.equationWeightBound + n * M.equationWeightBound +
          M.equationWeightBound := by omega
    _ = 2 * n * M.equationWeightBound + M.equationWeightBound := by ring

private theorem discrepancy_cast_eq_zero (M : DeformationMatrix n)
    (S : Finset M.ForbiddenEquation) {q : ℕ}
    (x : M.EquationSolutions (ZMod q) S)
    (e : M.ForbiddenEquation) (he : e ∈ S) :
    ((M.modularLiftPotential S (e.target M) -
      M.modularLiftPotential S (e.source M) - (e.distance M : ℤ) : ℤ) :
        ZMod q) = 0 := by
  have hroot : M.componentRoot S (e.source M) =
      M.componentRoot S (e.target M) :=
    M.componentRoot_eq_of_adj S (M.equationGraph_adj_of_mem he)
  have ht := M.intCast_modularLiftPotential_eq_sub S x (e.target M)
  have hs := M.intCast_modularLiftPotential_eq_sub S x (e.source M)
  have heq := x.2 e he
  change x.1 (e.target M) - x.1 (e.source M) =
    (e.distance M : ZMod q) at heq
  push_cast
  rw [hroot] at hs
  linear_combination ht - hs + heq

/-- The hard stability step in the finite-field method for these difference
arrangements: above an explicit bound, every modularly nonempty selected
intersection is already integrally consistent.  Primality is not needed. -/
theorem integrallyConsistent_of_equationSolutions_zmod
    (M : DeformationMatrix n) (S : Finset M.ForbiddenEquation)
    {q : ℕ} (hq : M.equationStabilityBound ≤ q)
    (x : M.EquationSolutions (ZMod q) S) :
    M.IntegrallyConsistent S := by
  refine ⟨M.modularLiftPotential S, ?_⟩
  intro e he
  let z : ℤ := M.modularLiftPotential S (e.target M) -
    M.modularLiftPotential S (e.source M) - (e.distance M : ℤ)
  have hzcast : (z : ZMod q) = 0 := by
    simpa [z] using M.discrepancy_cast_eq_zero S x e he
  have hzdiv : (q : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp hzcast
  have hzlt : z.natAbs < q := by
    have hzle := M.discrepancy_natAbs_le S e
    unfold equationStabilityBound at hq
    omega
  have hz : z = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hzdiv
    simpa using hzlt
  unfold SatisfiesEquation
  dsimp [z] at hz
  omega

/-- Above the stability threshold, an integrally inconsistent selected
intersection has no points modulo `q`. -/
theorem equationSolutions_zmod_isEmpty_of_not_integrallyConsistent
    (M : DeformationMatrix n) (S : Finset M.ForbiddenEquation)
    {q : ℕ} (hq : M.equationStabilityBound ≤ q)
    (hS : ¬M.IntegrallyConsistent S) :
    IsEmpty (M.EquationSolutions (ZMod q) S) :=
  ⟨fun x ↦ (hS (M.integrallyConsistent_of_equationSolutions_zmod S hq x)).elim⟩

/-- The independently defined Whitney polynomial evaluates, at every modulus
above the explicit stability bound, to the cardinality of the actual modular
complement.  This is the finite-field method specialized and proved for the
paper's integral difference arrangements; no primality assumption is needed
for the stability argument itself. -/
theorem eval_whitneyCharacteristicPolynomial_eq_card_zmod
    (M : DeformationMatrix n) {q : ℕ} [NeZero q]
    (hq : M.equationStabilityBound ≤ q) :
    Polynomial.eval (q : ℚ) M.whitneyCharacteristicPolynomial =
      (Fintype.card (M.FiniteFieldComplement (ZMod q)) : ℚ) := by
  classical
  rw [M.eval_whitneyCharacteristicPolynomial]
  calc
    (∑ S : Finset M.ForbiddenEquation,
        if M.IntegrallyConsistent S then
          (-1 : ℚ) ^ S.card * (q : ℚ) ^ M.equationComponentCount S
        else 0) =
        ∑ S : Finset M.ForbiddenEquation,
          (-1 : ℚ) ^ S.card *
            (Fintype.card (M.EquationSolutions (ZMod q) S) : ℚ) := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : M.IntegrallyConsistent S
      · rw [if_pos hS,
          M.card_equationSolutions_of_integrallyConsistent (ZMod q) S hS,
          ZMod.card]
        push_cast
        rfl
      · rw [if_neg hS]
        have hzero : Fintype.card (M.EquationSolutions (ZMod q) S) = 0 := by
          letI : IsEmpty (M.EquationSolutions (ZMod q) S) :=
            M.equationSolutions_zmod_isEmpty_of_not_integrallyConsistent S hq hS
          exact Fintype.card_eq_zero
        rw [hzero]
        simp
    _ = (Fintype.card (M.FiniteFieldComplement (ZMod q)) : ℚ) := by
      have hinc := M.card_finiteFieldComplement_eq_inclusionExclusion (ZMod q)
      exact_mod_cast hinc.symm

end DeformationMatrix

end CyclicBraidArrangement
