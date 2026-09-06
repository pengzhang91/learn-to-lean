import LeanCo.LaplacianLFunctions.GraphInvariants
import LeanCo.LaplacianLFunctions.RecoveryTheorem
import Mathlib.Tactic

/-!
# Reconstruction of saturated multigraphs

This file formalizes Definition 4.4 and Corollary 4.5 of
arXiv:2608.29981.  A graph is saturated when every two distinct vertices are
joined by an edge.  In that case its Laplacian lattice determines every row
of its Laplacian, and hence every edge multiplicity.

The reconstruction is elementary and intrinsic to the lattice.  For a fixed
vertex `v`, the `v`-th Laplacian row is the unique lattice vector which is
strictly negative away from `v` and has the smallest possible `v`-coordinate.
The discrete maximum principle gives the lower bound.  Equality, together
with saturation, forces every potential drop away from `v` to equal one.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

/-- A vertex equivalence is a multigraph isomorphism along that equivalence
when it preserves every edge multiplicity. -/
def IsIsomorphicAlong {V' V : Type*}
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    (sigma : V' ≃ V) : Prop :=
  ∀ v w, G'.multiplicity v w = G.multiplicity (sigma v) (sigma w)

/-- Two loopless multigraphs are isomorphic when some vertex equivalence
preserves every edge multiplicity. -/
def Isomorphic {V' V : Type*}
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V) : Prop :=
  ∃ sigma : V' ≃ V, G'.IsIsomorphicAlong G sigma

variable {V : Type*} [Fintype V]

/-- **Definition 4.4.**  A loopless multigraph is saturated when every two
distinct vertices are joined by at least one edge. -/
def Saturated (G : LooplessMultigraph V) : Prop :=
  ∀ v w : V, v ≠ w → 0 < G.multiplicity v w

/-- The row of the Laplacian indexed by `v`. -/
def laplacianRow (G : LooplessMultigraph V) (v : V) : Divisor V := by
  classical
  exact G.laplacian (Divisor.vertexDivisor v)

@[simp]
theorem laplacianRow_apply_self (G : LooplessMultigraph V) (v : V) :
    G.laplacianRow v v = (G.valency v : ℤ) := by
  classical
  simp only [laplacianRow, laplacian_apply, valency, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hwv : w = v
  · subst w
    simp
  · simp [Divisor.vertexDivisor, hwv]

@[simp]
theorem laplacianRow_apply_of_ne (G : LooplessMultigraph V)
    {v w : V} (h : w ≠ v) :
    G.laplacianRow v w = -(G.multiplicity w v : ℤ) := by
  classical
  simp [laplacianRow, laplacian_apply, Divisor.vertexDivisor, h]

theorem laplacianRow_mem_laplacianLattice
    (G : LooplessMultigraph V) (v : V) :
    G.laplacianRow v ∈ G.laplacianLattice := by
  classical
  exact ⟨Divisor.vertexDivisor v, rfl⟩

theorem laplacianRow_neg_of_saturated
    (G : LooplessMultigraph V) (hsat : G.Saturated)
    {v w : V} (h : w ≠ v) :
    G.laplacianRow v w < 0 := by
  rw [G.laplacianRow_apply_of_ne h]
  have hpos : 0 < (G.multiplicity w v : ℤ) := by
    exact_mod_cast hsat w v h
  omega

private theorem laplacian_nonneg_at_max
    (G : LooplessMultigraph V) (E : Divisor V) (a : V)
    (hmax : ∀ z, E z ≤ E a) :
    0 ≤ G.laplacian E a := by
  rw [laplacian_apply]
  apply Finset.sum_nonneg
  intro z hz
  exact mul_nonneg (Int.natCast_nonneg _) (sub_nonneg.mpr (hmax z))

/-- A lattice vector which is negative away from `v` is represented by a
potential having `v` as its unique maximum. -/
private theorem exists_potential_strict_max
    (G : LooplessMultigraph V) (v : V) (D : Divisor V)
    (hmem : D ∈ G.laplacianLattice)
    (hneg : ∀ w, w ≠ v → D w < 0) :
    ∃ E : Divisor V, G.laplacian E = D ∧
      ∀ w, w ≠ v → E w < E v := by
  classical
  obtain ⟨E, hE⟩ := (G.mem_laplacianLattice_iff D).mp hmem
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image Finset.univ E
    ⟨v, Finset.mem_univ v⟩
  have hmax' : ∀ z, E z ≤ E a :=
    fun z ↦ hmax z (Finset.mem_univ z)
  have haeq : a = v := by
    by_contra hav
    have hnonneg : 0 ≤ D a := by
      rw [← hE]
      exact G.laplacian_nonneg_at_max E a hmax'
    have hnegative := hneg a hav
    omega
  subst a
  refine ⟨E, hE, ?_⟩
  intro w hw
  have hwle : E w ≤ E v := hmax' w
  apply lt_of_le_of_ne hwle
  intro heq
  have hwmax : ∀ z, E z ≤ E w := by
    intro z
    simpa [heq] using hmax' z
  have hnonneg : 0 ≤ D w := by
    rw [← hE]
    exact G.laplacian_nonneg_at_max E w hwmax
  have hnegative := hneg w hw
  omega

/-- Any lattice vector which is negative away from `v` has `v`-coordinate
at least the valency at `v`.  This lower bound does not require saturation. -/
theorem intCast_valency_le_apply_of_mem_laplacianLattice_of_neg
    (G : LooplessMultigraph V) (v : V) (D : Divisor V)
    (hmem : D ∈ G.laplacianLattice)
    (hneg : ∀ w, w ≠ v → D w < 0) :
    (G.valency v : ℤ) ≤ D v := by
  classical
  obtain ⟨E, hE, hstrict⟩ :=
    G.exists_potential_strict_max v D hmem hneg
  rw [← hE]
  simp only [laplacian_apply, valency]
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro w hw
  by_cases hwv : w = v
  · subst w
    simp
  · have hgap : (1 : ℤ) ≤ E v - E w := by
      have := hstrict w hwv
      omega
    calc
      (G.multiplicity v w : ℤ) =
          (G.multiplicity v w : ℤ) * 1 := by ring
      _ ≤ (G.multiplicity v w : ℤ) * (E v - E w) :=
        mul_le_mul_of_nonneg_left hgap (Int.natCast_nonneg _)

/-- On a saturated graph, the Laplacian row at `v` is the unique lattice
vector attaining the smallest possible `v`-coordinate while being strictly
negative at every other coordinate. -/
theorem eq_laplacianRow_of_saturated_of_mem_of_neg_of_apply_le
    (G : LooplessMultigraph V) (hsat : G.Saturated)
    (v : V) (D : Divisor V)
    (hmem : D ∈ G.laplacianLattice)
    (hneg : ∀ w, w ≠ v → D w < 0)
    (hle : D v ≤ (G.valency v : ℤ)) :
    D = G.laplacianRow v := by
  classical
  obtain ⟨E, hE, hstrict⟩ :=
    G.exists_potential_strict_max v D hmem hneg
  have hlower :=
    G.intCast_valency_le_apply_of_mem_laplacianLattice_of_neg
      v D hmem hneg
  have hval : D v = (G.valency v : ℤ) := le_antisymm hle hlower
  have hterm_le : ∀ w ∈ (Finset.univ : Finset V),
      (G.multiplicity v w : ℤ) ≤
        (G.multiplicity v w : ℤ) * (E v - E w) := by
    intro w hw
    by_cases hwv : w = v
    · subst w
      simp
    · have hgap : (1 : ℤ) ≤ E v - E w := by
        have := hstrict w hwv
        omega
      calc
        (G.multiplicity v w : ℤ) =
            (G.multiplicity v w : ℤ) * 1 := by ring
        _ ≤ (G.multiplicity v w : ℤ) * (E v - E w) :=
          mul_le_mul_of_nonneg_left hgap (Int.natCast_nonneg _)
  have hsumeq :
      ∑ w : V, (G.multiplicity v w : ℤ) =
        ∑ w : V, (G.multiplicity v w : ℤ) * (E v - E w) := by
    calc
      ∑ w : V, (G.multiplicity v w : ℤ) =
          (G.valency v : ℤ) := by simp [valency]
      _ = D v := hval.symm
      _ = G.laplacian E v := by rw [hE]
      _ = _ := by rw [laplacian_apply]
  have hterm_eq : ∀ w : V,
      (G.multiplicity v w : ℤ) =
        (G.multiplicity v w : ℤ) * (E v - E w) := by
    intro w
    exact (Finset.sum_eq_sum_iff_of_le hterm_le).mp hsumeq
      w (Finset.mem_univ w)
  have hgap_eq : ∀ w, w ≠ v → E v - E w = 1 := by
    intro w hwv
    have hmpos : 0 < (G.multiplicity v w : ℤ) := by
      exact_mod_cast hsat v w (Ne.symm hwv)
    have hmne : (G.multiplicity v w : ℤ) ≠ 0 := ne_of_gt hmpos
    have heq : (G.multiplicity v w : ℤ) * 1 =
        (G.multiplicity v w : ℤ) * (E v - E w) := by
      simpa using hterm_eq w
    exact mul_left_cancel₀ hmne heq.symm
  let c : Divisor V := fun _ ↦ E v - 1
  have hEform : E = c + Divisor.vertexDivisor v := by
    funext w
    by_cases hwv : w = v
    · subst w
      simp [c, Divisor.vertexDivisor]
    · have hgap := hgap_eq w hwv
      simp only [Pi.add_apply, c, Divisor.vertexDivisor_apply, if_neg hwv]
      omega
  have hconst : G.laplacian c = 0 := by
    ext w
    simp [laplacian_apply, c]
  calc
    D = G.laplacian E := hE.symm
    _ = G.laplacian (c + Divisor.vertexDivisor v) := by rw [hEform]
    _ = G.laplacian c + G.laplacian (Divisor.vertexDivisor v) :=
      G.laplacian.map_add c (Divisor.vertexDivisor v)
    _ = G.laplacianRow v := by simp [hconst, laplacianRow]

variable {V' : Type*} [Fintype V']

/-- Saturated reconstruction from a transported Laplacian lattice.  Equality
of the lattices first identifies every corresponding Laplacian row, whose
off-diagonal entries are the negatives of the edge multiplicities. -/
theorem isIsomorphicAlong_of_saturated_of_map_laplacianLattice_eq
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    (sigma : V' ≃ V) (hsat' : G'.Saturated) (hsat : G.Saturated)
    (hlattice : Submodule.map (divisorReindex sigma).toLinearMap
      G'.laplacianLattice = G.laplacianLattice) :
    G'.IsIsomorphicAlong G sigma := by
  classical
  intro v w
  by_cases hvw : v = w
  · subst w
    simp
  · let D : Divisor V :=
      divisorReindex sigma (G'.laplacianRow v)
    have hDmem : D ∈ G.laplacianLattice := by
      rw [← hlattice]
      exact ⟨G'.laplacianRow v,
        G'.laplacianRow_mem_laplacianLattice v, rfl⟩
    have hDneg : ∀ x, x ≠ sigma v → D x < 0 := by
      intro x hx
      have hpre : sigma.symm x ≠ v := by
        intro h
        apply hx
        calc
          x = sigma (sigma.symm x) := (sigma.apply_symm_apply x).symm
          _ = sigma v := congrArg sigma h
      exact G'.laplacianRow_neg_of_saturated hsat' hpre
    have hDapply : D (sigma v) = (G'.valency v : ℤ) := by
      simp [D]
    have hforward :
        (G.valency (sigma v) : ℤ) ≤ (G'.valency v : ℤ) := by
      rw [← hDapply]
      exact G.intCast_valency_le_apply_of_mem_laplacianLattice_of_neg
        (sigma v) D hDmem hDneg
    have htargetMap : G.laplacianRow (sigma v) ∈
        Submodule.map (divisorReindex sigma).toLinearMap
          G'.laplacianLattice := by
      rw [hlattice]
      exact G.laplacianRow_mem_laplacianLattice (sigma v)
    obtain ⟨E, hEmem, hEeq⟩ := htargetMap
    have hEneg : ∀ x, x ≠ v → E x < 0 := by
      intro x hx
      have hsig : sigma x ≠ sigma v :=
        fun h ↦ hx (sigma.injective h)
      calc
        E x = divisorReindex sigma E (sigma x) := by simp
        _ = G.laplacianRow (sigma v) (sigma x) :=
          congrFun hEeq (sigma x)
        _ < 0 := G.laplacianRow_neg_of_saturated hsat hsig
    have hEapply : E v = (G.valency (sigma v) : ℤ) := by
      calc
        E v = divisorReindex sigma E (sigma v) := by simp
        _ = G.laplacianRow (sigma v) (sigma v) :=
          congrFun hEeq (sigma v)
        _ = (G.valency (sigma v) : ℤ) := by simp
    have hbackward :
        (G'.valency v : ℤ) ≤ (G.valency (sigma v) : ℤ) := by
      rw [← hEapply]
      exact G'.intCast_valency_le_apply_of_mem_laplacianLattice_of_neg
        v E hEmem hEneg
    have hvalCast :
        (G'.valency v : ℤ) = (G.valency (sigma v) : ℤ) :=
      le_antisymm hbackward hforward
    have hroweq : D = G.laplacianRow (sigma v) :=
      G.eq_laplacianRow_of_saturated_of_mem_of_neg_of_apply_le hsat
        (sigma v) D hDmem hDneg (by rw [hDapply, hvalCast])
    have hsigwv : sigma w ≠ sigma v :=
      fun h ↦ hvw (sigma.injective h).symm
    have heval := congrFun hroweq (sigma w)
    simp only [D, divisorReindex_apply, Equiv.symm_apply_apply,
      G'.laplacianRow_apply_of_ne (Ne.symm hvw),
      G.laplacianRow_apply_of_ne hsigwv] at heval
    have hcast : (G'.multiplicity w v : ℤ) =
        (G.multiplicity (sigma w) (sigma v) : ℤ) :=
      neg_inj.mp heval
    have hnat :
        G'.multiplicity w v = G.multiplicity (sigma w) (sigma v) := by
      exact_mod_cast hcast
    calc
      G'.multiplicity v w = G'.multiplicity w v :=
        G'.multiplicity_symm v w
      _ = G.multiplicity (sigma w) (sigma v) := hnat
      _ = G.multiplicity (sigma v) (sigma w) :=
        G.multiplicity_symm _ _

variable [Nonempty V'] [DecidableEq V'] [Nonempty V] [DecidableEq V]

/-- **Corollary 4.5.**  Under Theorem 4.3's hypotheses, saturated graphs
with matching transported `L`-functions are isomorphic as multigraphs. -/
theorem corollary_4_5
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    (hconn' : G'.Connected) (hconn : G.Connected)
    (hbridge' : G'.BridgeFree) (hbridge : G.BridgeFree)
    (hsat' : G'.Saturated) (hsat : G.Saturated)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (phi : G'.Jacobian ≃+ G.Jacobian) :
    letI : Fact G'.Connected := ⟨hconn'⟩
    letI : Fact G.Connected := ⟨hconn⟩
    (∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁'
          (chi.compAddMonoidHom phi.toAddMonoidHom)) →
      G'.Isomorphic G := by
  letI : Fact G'.Connected := ⟨hconn'⟩
  letI : Fact G.Connected := ⟨hconn⟩
  intro hL
  obtain ⟨sigma, hvertex, hlattice⟩ :=
    G'.recover_laplacianLattice_of_lFunction_eq G
      hbridge' hbridge D₁' D₁ phi hL
  exact ⟨sigma,
    G'.isIsomorphicAlong_of_saturated_of_map_laplacianLattice_eq
      G sigma hsat' hsat hlattice⟩

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
