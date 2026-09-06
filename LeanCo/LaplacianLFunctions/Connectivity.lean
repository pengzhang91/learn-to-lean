import LeanCo.LaplacianLFunctions.Picard
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

/-!
# Connectivity, bridge-freeness, and the degree-one Abel--Jacobi map

The multigraphs in arXiv:2608.29981 are connected.  For a loopless
multigraph, being bridge-free is equivalently expressed by requiring every
nonempty proper vertex cut to contain at least two edges, counted with
multiplicity.  This formulation avoids choosing names for parallel edges.

The main result of this file is that the degree-one vertex-class map is
injective for a bridge-free multigraph.  The proof is the integral
maximum-potential/cut argument: if

`L f = [v] - [w]`,

then the cut on which `f` is maximal has weight at most one.
-/

namespace LeanCo.LaplacianLFunctions

open scoped BigOperators

namespace LooplessMultigraph

variable {V : Type*} [Fintype V]

/-- Connectivity of a multigraph means connectivity of its support simple
graph. -/
def Connected (G : LooplessMultigraph V) : Prop :=
  G.support.Connected

/-- The number of multiedges crossing from `S` to its complement.  Each
undirected edge is counted exactly once because its endpoint in `S` is fixed
as the first endpoint. -/
noncomputable def cutWeight (G : LooplessMultigraph V) (S : Finset V) : ℕ := by
  classical
  exact ∑ v ∈ S, ∑ w, if w ∈ S then 0 else G.multiplicity v w

/-- Cut-theoretic bridge-freeness: every nonempty proper cut has at least two
edges, with parallel edges counted separately. -/
def BridgeFree (G : LooplessMultigraph V) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → 2 ≤ G.cutWeight S

/-- The vertices at the same potential as a chosen vertex `a`.  When `a` is a
global maximizer this is the maximum-potential cut. -/
def topLevelSet (D : Divisor V) (a : V) : Finset V :=
  Finset.univ.filter fun v ↦ D v = D a

@[simp]
theorem mem_topLevelSet_iff (D : Divisor V) (a v : V) :
    v ∈ topLevelSet D a ↔ D v = D a := by
  simp [topLevelSet]

theorem topLevelSet_nonempty (D : Divisor V) (a : V) :
    (topLevelSet D a).Nonempty := by
  exact ⟨a, by simp⟩

/-- At a global maximum, one boundary multiplicity is bounded by the
corresponding Laplacian summand.  Summing gives the cut inequality used in the
injectivity proof. -/
theorem intCast_cutWeight_le_sum_laplacian_of_max
    (G : LooplessMultigraph V) (D : Divisor V) (a : V)
    (hmax : ∀ v, D v ≤ D a) :
    (G.cutWeight (topLevelSet D a) : ℤ) ≤
      ∑ v ∈ topLevelSet D a, G.laplacian D v := by
  classical
  simp only [cutWeight, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
    laplacian_apply]
  apply Finset.sum_le_sum
  intro v hv
  apply Finset.sum_le_sum
  intro w hw
  have hvmax : D v = D a := (mem_topLevelSet_iff D a v).mp hv
  by_cases hwS : w ∈ topLevelSet D a
  · have hwmax : D w = D a := (mem_topLevelSet_iff D a w).mp hwS
    simp [hwS, hvmax, hwmax]
  · simp only [hwS, if_false]
    have hwne : D w ≠ D a := by
      intro h
      exact hwS ((mem_topLevelSet_iff D a w).mpr h)
    have hwlt : D w < D a := lt_of_le_of_ne (hmax w) hwne
    have hone : (1 : ℤ) ≤ D v - D w := by omega
    calc
      (G.multiplicity v w : ℤ) = (G.multiplicity v w : ℤ) * 1 := by ring
      _ ≤ (G.multiplicity v w : ℤ) * (D v - D w) :=
        mul_le_mul_of_nonneg_left hone (Int.natCast_nonneg _)

/-- A global maximum whose Laplacian is a difference of two distinct vertex
divisors has a proper maximum-level set. -/
theorem topLevelSet_ne_univ_of_laplacian_eq_vertex_sub
    (G : LooplessMultigraph V) (D : Divisor V) [DecidableEq V]
    {v w : V} (hvw : v ≠ w)
    (hD : G.laplacian D =
      Divisor.vertexDivisor v - Divisor.vertexDivisor w) (a : V) :
    topLevelSet D a ≠ Finset.univ := by
  classical
  intro htop
  have hall : ∀ x, D x = D a := by
    intro x
    apply (mem_topLevelSet_iff D a x).mp
    rw [htop]
    exact Finset.mem_univ x
  have hzero : G.laplacian D v = 0 := by
    rw [laplacian_apply]
    apply Finset.sum_eq_zero
    intro x hx
    rw [hall v, hall x]
    simp
  have hatv := congrFun hD v
  simp [hzero, Divisor.vertexDivisor, hvw] at hatv

/-- A vertex divisor contributes at most one to the sum over an arbitrary
cut, even after subtracting another vertex divisor. -/
theorem sum_vertexDivisor_sub_le_one [DecidableEq V]
    (S : Finset V) (v w : V) :
    (∑ x ∈ S,
      (Divisor.vertexDivisor v - Divisor.vertexDivisor w) x) ≤ (1 : ℤ) := by
  classical
  simp only [Pi.sub_apply, Divisor.vertexDivisor_apply,
    Finset.sum_sub_distrib]
  simp
  split_ifs <;> omega

/-- A harmonic integral potential on a connected multigraph is constant. -/
theorem constant_of_laplacian_eq_zero
    (G : LooplessMultigraph V) (hconn : G.Connected) (D : Divisor V)
    (hD : G.laplacian D = 0) :
    ∀ x y, D x = D y := by
  classical
  let a₀ : V := Classical.choice hconn.nonempty
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image Finset.univ D
    ⟨a₀, Finset.mem_univ a₀⟩
  have hmax' : ∀ z, D z ≤ D a := fun z ↦ hmax z (Finset.mem_univ z)
  have hadj : ∀ {x y : V}, D x = D a → G.support.Adj x y → D y = D a := by
    intro x y hx hxy
    have hmaxx : ∀ z, D z ≤ D x := by
      intro z
      simpa [hx] using hmax' z
    have hsum :
        (∑ z, (G.multiplicity x z : ℤ) * (D x - D z)) = 0 := by
      have hxzero := congrFun hD x
      simpa only [laplacian_apply, Pi.zero_apply] using hxzero
    have hterm : (G.multiplicity x y : ℤ) * (D x - D y) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun z hz ↦
        mul_nonneg (Int.natCast_nonneg _) (sub_nonneg.mpr (hmaxx z)))).mp
          hsum y (Finset.mem_univ y)
    have hmult : (G.multiplicity x y : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt ((support_adj G x y).mp hxy))
    have hxyD : D x - D y = 0 := (mul_eq_zero.mp hterm).resolve_left hmult
    exact (sub_eq_zero.mp hxyD).symm.trans hx
  have hwalk : ∀ {x y : V}, G.support.Walk x y → D x = D a → D y = D a := by
    intro x y p
    induction p with
    | nil => exact fun hx ↦ hx
    | cons hxy q ih =>
        intro hx
        exact ih (hadj hx hxy)
  have htoMax : ∀ x, D x = D a := by
    intro x
    obtain ⟨p⟩ := hconn.preconnected a x
    exact hwalk p rfl
  intro x y
  exact (htoMax x).trans (htoMax y).symm

/-- Bridge-freeness makes the degree-one Abel--Jacobi map injective.  This is
Corollary 2.10 in the form required by the reconstruction theorem. -/
theorem vertexClass_injective_of_bridgeFree
    (G : LooplessMultigraph V) (hbridge : G.BridgeFree) [DecidableEq V] :
    Function.Injective G.vertexClass := by
  intro v w hvwClass
  by_contra hvw
  have hprincipal := (G.vertexClass_eq_iff v w).mp hvwClass
  obtain ⟨D, hD⟩ := (G.mem_laplacianLattice_iff _).mp hprincipal
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image Finset.univ D
    ⟨v, Finset.mem_univ v⟩
  have hmax' : ∀ z, D z ≤ D a := fun z ↦ hmax z (Finset.mem_univ z)
  have hcut : 2 ≤ G.cutWeight (topLevelSet D a) :=
    hbridge (topLevelSet D a) (topLevelSet_nonempty D a)
      (G.topLevelSet_ne_univ_of_laplacian_eq_vertex_sub D hvw hD a)
  have hcutInt : (2 : ℤ) ≤ (G.cutWeight (topLevelSet D a) : ℤ) := by
    exact_mod_cast hcut
  have hupper :
      (∑ x ∈ topLevelSet D a, G.laplacian D x) ≤ (1 : ℤ) := by
    rw [hD]
    exact sum_vertexDivisor_sub_le_one (V := V) (topLevelSet D a) v w
  have hboundary := G.intCast_cutWeight_le_sum_laplacian_of_max D a hmax'
  omega

end LooplessMultigraph

end LeanCo.LaplacianLFunctions
