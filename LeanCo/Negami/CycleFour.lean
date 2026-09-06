import LeanCo.Negami.TwoBoundary
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# The four-cycle calculation

This file formalizes Example 6.4 of arXiv:2608.30053.  The three state sums
are genuine sums over every subset of a two- or four-element edge type.  The
closed formulas are obtained by grouping subsets by cardinality, after which
the two-boundary splitting identity is verified over an arbitrary field.
-/

namespace LeanCo.Negami

open scoped BigOperators

section StateCounts

variable {R : Type*} [CommRing R]

/-- Component count for a two-edge path on three vertices. -/
def pathComponentCount (S : Finset (Fin 2)) : ℕ := 3 - S.card

/-- The path state sum, before collecting like terms. -/
def pathStateSum (t x y : R) : R :=
  ∑ S : Finset (Fin 2),
    t ^ pathComponentCount S * x ^ S.card * y ^ (2 - S.card)

/-- Component count for two parallel edges on two vertices. -/
def parallelComponentCount (S : Finset (Fin 2)) : ℕ :=
  if S.card = 0 then 2 else 1

/-- The state sum after identifying the two boundary vertices of the path. -/
def parallelStateSum (t x y : R) : R :=
  ∑ S : Finset (Fin 2),
    t ^ parallelComponentCount S * x ^ S.card * y ^ (2 - S.card)

/-- Component count of a spanning state of the four-cycle. -/
def cycleFourComponentCount (S : Finset (Fin 4)) : ℕ :=
  if S.card = 4 then 1 else 4 - S.card

/-- The complete sixteen-state sum of the four-cycle. -/
def cycleFourStateSum (t x y : R) : R :=
  ∑ S : Finset (Fin 4),
    t ^ cycleFourComponentCount S * x ^ S.card * y ^ (4 - S.card)

/-- The path formula used in Example 6.4. -/
theorem pathStateSum_formula (t x y : R) :
    pathStateSum t x y =
      t ^ 3 * y ^ 2 + 2 * t ^ 2 * x * y + t * x ^ 2 := by
  classical
  unfold pathStateSum
  rw [← Finset.powerset_univ]
  rw [Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  let f : ℕ → R := fun k ↦ t ^ (3 - k) * x ^ k * y ^ (2 - k)
  have hinner (k : ℕ) :
      ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin 2)),
        t ^ pathComponentCount S * x ^ S.card * y ^ (2 - S.card) =
      (Finset.univ : Finset (Fin 2)).card.choose k • f k := by
    simpa [pathComponentCount, f] using
      (Finset.sum_powersetCard k (Finset.univ : Finset (Fin 2)) f)
  simp_rw [hinner]
  norm_num [Finset.sum_range_succ, Nat.choose, f]
  ring

/-- The two-parallel-edge quotient formula used in Example 6.4. -/
theorem parallelStateSum_formula (t x y : R) :
    parallelStateSum t x y =
      t ^ 2 * y ^ 2 + 2 * t * x * y + t * x ^ 2 := by
  classical
  unfold parallelStateSum
  rw [← Finset.powerset_univ]
  rw [Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  let f : ℕ → R := fun k ↦
    t ^ (if k = 0 then 2 else 1) * x ^ k * y ^ (2 - k)
  have hinner (k : ℕ) :
      ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin 2)),
        t ^ parallelComponentCount S * x ^ S.card * y ^ (2 - S.card) =
      (Finset.univ : Finset (Fin 2)).card.choose k • f k := by
    simpa [parallelComponentCount, f] using
      (Finset.sum_powersetCard k (Finset.univ : Finset (Fin 2)) f)
  simp_rw [hinner]
  norm_num [Finset.sum_range_succ, Nat.choose, f]
  ring

/-- Direct collection of all sixteen four-cycle states. -/
theorem cycleFourStateSum_formula (t x y : R) :
    cycleFourStateSum t x y =
      t ^ 4 * y ^ 4 + 4 * t ^ 3 * x * y ^ 3 +
        6 * t ^ 2 * x ^ 2 * y ^ 2 + 4 * t * x ^ 3 * y + t * x ^ 4 := by
  classical
  unfold cycleFourStateSum
  rw [← Finset.powerset_univ]
  rw [Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  let f : ℕ → R := fun k ↦
    t ^ (if k = 4 then 1 else 4 - k) * x ^ k * y ^ (4 - k)
  have hinner (k : ℕ) :
      ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin 4)),
        t ^ cycleFourComponentCount S * x ^ S.card * y ^ (4 - S.card) =
      (Finset.univ : Finset (Fin 4)).card.choose k • f k := by
    simpa [cycleFourComponentCount, f] using
      (Finset.sum_powersetCard k (Finset.univ : Finset (Fin 4)) f)
  simp_rw [hinner]
  norm_num [Finset.sum_range_succ, Nat.choose, f]
  ring

end StateCounts

section SplittingIdentity

variable {F : Type*} [Field F]

/-- Collected polynomial of the two-edge path. -/
def pathPolynomial (t x y : F) : F :=
  t ^ 3 * y ^ 2 + 2 * t ^ 2 * x * y + t * x ^ 2

/-- Collected polynomial after identifying the boundary vertices. -/
def quotientPathPolynomial (t x y : F) : F :=
  t ^ 2 * y ^ 2 + 2 * t * x * y + t * x ^ 2

/-- Collected polynomial of the four-cycle. -/
def cycleFourPolynomial (t x y : F) : F :=
  t ^ 4 * y ^ 4 + 4 * t ^ 3 * x * y ^ 3 +
    6 * t ^ 2 * x ^ 2 * y ^ 2 + 4 * t * x ^ 3 * y + t * x ^ 4

/-- Substitution into the four terms of the two-boundary splitting formula. -/
theorem cycleFour_polynomial_splitting
    (t x y : F) (ht : t ≠ 0) (ht1 : t ≠ 1) :
    let p := pathPolynomial t x y
    let q := quotientPathPolynomial t x y
    q * q / (t - 1) - q * p / (t * (t - 1)) -
        p * q / (t * (t - 1)) + p * p / (t * (t - 1)) =
      cycleFourPolynomial t x y := by
  dsimp [pathPolynomial, quotientPathPolynomial, cycleFourPolynomial]
  have hs : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  field_simp [ht, hs]
  ring

/-- End-to-end version of Example 6.4: the finite state sums themselves
satisfy the two-boundary splitting formula. -/
theorem cycleFour_stateSum_splitting
    (t x y : F) (ht : t ≠ 0) (ht1 : t ≠ 1) :
    parallelStateSum t x y * parallelStateSum t x y / (t - 1) -
        parallelStateSum t x y * pathStateSum t x y / (t * (t - 1)) -
        pathStateSum t x y * parallelStateSum t x y / (t * (t - 1)) +
        pathStateSum t x y * pathStateSum t x y / (t * (t - 1)) =
      cycleFourStateSum t x y := by
  rw [pathStateSum_formula, parallelStateSum_formula, cycleFourStateSum_formula]
  exact cycleFour_polynomial_splitting t x y ht ht1

end SplittingIdentity

end LeanCo.Negami
