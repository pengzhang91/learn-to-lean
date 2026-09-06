import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Fintype.EquivFin

/-!
# Resolvable quantum Latin squares

Literal finite-coordinate definitions for Zhang--Cao, *Resolvable quantum
Latin squares with maximal cardinality* (arXiv:2608.29201v1).

The Hilbert space of order `ι` is `ι → ℂ`, with the usual finite dot product.
Using the Kronecker-delta equations is equivalent to saying that a family of
`Fintype.card ι` vectors is an orthonormal basis; this presentation keeps all
later block constructions independent of analytic basis APIs.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

universe u v

/-- The coordinate Hilbert space used by a quantum Latin square. -/
abbrev Ket (ι : Type u) := ι → ℂ

/-- The usual Hermitian product on a finite coordinate space, conjugate-linear
in the first argument, as in the paper. -/
def dot {ι : Type u} [Fintype ι] (x y : Ket ι) : ℂ :=
  ∑ k, conj (x k) * y k

@[simp] theorem dot_self_basis [Fintype ι] [DecidableEq ι] (i : ι) :
    dot (Pi.single i 1 : Ket ι) (Pi.single i 1) = 1 := by
  classical
  rw [dot, Fintype.sum_eq_single i]
  · simp
  · intro b hbi
    simp [Pi.single_eq_of_ne hbi]

@[simp] theorem dot_basis_basis [Fintype ι] [DecidableEq ι] (i j : ι) :
    dot (Pi.single i 1 : Ket ι) (Pi.single j 1) = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp
  · rw [dot, Fintype.sum_eq_zero]
    · simp [h]
    · intro k
      by_cases hki : k = i
      · subst k
        simp [h]
      · simp [Pi.single_eq_of_ne hki]

/-- Orthonormality of a finite family, written as its Gram matrix. -/
def IsOrthonormal {κ : Type v} {ι : Type u} [Fintype ι] [DecidableEq κ]
    (x : κ → Ket ι) : Prop :=
  ∀ a b, dot (x a) (x b) = if a = b then 1 else 0

/-- Two vectors represent the same quantum state precisely when they differ
by a scalar of norm one.  `Complex.norm_eq_one_iff` proves this is exactly the
paper's `exp (θ * I)` definition. -/
def PhaseEquivalent {ι : Type u} (x y : Ket ι) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ x = z • y

theorem phaseEquivalent_iff_exp {ι : Type u} (x y : Ket ι) :
    PhaseEquivalent x y ↔ ∃ θ : ℝ, x = Complex.exp (θ * Complex.I) • y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff z).mp hz
    exact ⟨θ, by rw [hθ]⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨Complex.exp (θ * Complex.I), by simp, rfl⟩

theorem PhaseEquivalent.refl {ι : Type u} (x : Ket ι) : PhaseEquivalent x x := by
  exact ⟨1, by simp, by simp⟩

theorem PhaseEquivalent.symm {ι : Type u} {x y : Ket ι}
    (h : PhaseEquivalent x y) : PhaseEquivalent y x := by
  rcases h with ⟨z, hz, hxy⟩
  have hz0 : z ≠ 0 := by
    intro h0
    simp [h0] at hz
  refine ⟨z⁻¹, by simp [norm_inv, hz], ?_⟩
  rw [hxy]
  ext i
  simp [hz0]

theorem PhaseEquivalent.trans {ι : Type u} {x y z : Ket ι}
    (hxy : PhaseEquivalent x y) (hyz : PhaseEquivalent y z) :
    PhaseEquivalent x z := by
  rcases hxy with ⟨a, ha, rfl⟩
  rcases hyz with ⟨b, hb, rfl⟩
  refine ⟨a * b, by simp [norm_mul, ha, hb], ?_⟩
  ext i
  simp [mul_assoc]

theorem phaseEquivalent_zero_iff {ι : Type u} (x : Ket ι) :
    PhaseEquivalent x 0 ↔ x = 0 := by
  constructor
  · rintro ⟨z, -, rfl⟩
    simp
  · rintro rfl
    exact PhaseEquivalent.refl 0

/-- A literal quantum Latin square: entries are complex column vectors and
every row and column has the Gram matrix of an orthonormal basis. -/
structure QuantumLatinSquare (ι : Type u) [Fintype ι] [DecidableEq ι] where
  entry : ι → ι → Ket ι
  row_orthonormal : ∀ i, IsOrthonormal (entry i)
  col_orthonormal : ∀ j, IsOrthonormal (fun i ↦ entry i j)

namespace QuantumLatinSquare

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

@[simp] theorem row_norm (L : QuantumLatinSquare ι) (i j : ι) :
    dot (L.entry i j) (L.entry i j) = 1 := by
  simpa [IsOrthonormal] using L.row_orthonormal i j j

@[simp] theorem col_norm (L : QuantumLatinSquare ι) (i j : ι) :
    dot (L.entry i j) (L.entry i j) = 1 := by
  simpa [IsOrthonormal] using L.col_orthonormal j i i

/-- A resolution is an indexed partition of the cells into transversals.
For transversal `t`, `column t` is the permutation selecting one column in
each row.  `covers` says these selections partition every row, hence all
cells; `orthonormal` says every selected family is a basis. -/
structure Resolution (L : QuantumLatinSquare ι) where
  column : ι → Equiv.Perm ι
  covers : ∀ i, Function.Bijective (fun t ↦ column t i)
  orthonormal : ∀ t, IsOrthonormal (fun i ↦ L.entry i (column t i))

/-- The array contains the maximum possible number `|ι|²` of quantum states:
phase-equivalent entries must occupy the same cell. -/
def HasMaximalCardinality (L : QuantumLatinSquare ι) : Prop :=
  ∀ ⦃i j i' j' : ι⦄,
    PhaseEquivalent (L.entry i j) (L.entry i' j') → i = i' ∧ j = j'

end QuantumLatinSquare

/-- A maximal-cardinality resolvable quantum Latin square on an arbitrary
finite index type. -/
structure MaximalRQLS (ι : Type u) [Fintype ι] [DecidableEq ι] where
  square : QuantumLatinSquare ι
  resolution : square.Resolution
  maximal : square.HasMaximalCardinality

/-- The literal order-`n` existence predicate used in the final theorem. -/
def ExistsMaximalRQLS (n : ℕ) : Prop :=
  Nonempty (MaximalRQLS (Fin n))

section Reindex

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A computational-basis vector. -/
def basis (i : ι) : Ket ι := Pi.single i 1

@[simp] theorem basis_apply (i j : ι) :
    basis i j = if i = j then 1 else 0 := by
  simp only [basis, Pi.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Reindex a ket along an equivalence of coordinate types. -/
def reindexKet {κ : Type v} (e : ι ≃ κ) (x : Ket ι) : Ket κ :=
  fun k ↦ x (e.symm k)

@[simp] theorem reindexKet_apply {κ : Type v} (e : ι ≃ κ)
    (x : Ket ι) (k : κ) : reindexKet e x k = x (e.symm k) := rfl

theorem dot_reindexKet {κ : Type v} [Fintype κ] (e : ι ≃ κ)
    (x y : Ket ι) : dot (reindexKet e x) (reindexKet e y) = dot x y := by
  classical
  simpa [dot, reindexKet] using
    (Fintype.sum_equiv e.symm
      (fun k : κ ↦ conj (x (e.symm k)) * y (e.symm k))
      (fun i : ι ↦ conj (x i) * y i) (fun _ ↦ rfl))

/-- Transport a QLS along one equivalence used simultaneously for rows,
columns, and Hilbert-space coordinates. -/
def QuantumLatinSquare.reindex {κ : Type v} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (L : QuantumLatinSquare ι) : QuantumLatinSquare κ where
  entry i j := reindexKet e (L.entry (e.symm i) (e.symm j))
  row_orthonormal i a b := by
    rw [dot_reindexKet]
    simpa using L.row_orthonormal (e.symm i) (e.symm a) (e.symm b)
  col_orthonormal j a b := by
    rw [dot_reindexKet]
    simpa using L.col_orthonormal (e.symm j) (e.symm a) (e.symm b)

/-- Transport an entire maximal RQLS along an index equivalence. -/
noncomputable def MaximalRQLS.reindex {κ : Type v} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (R : MaximalRQLS ι) : MaximalRQLS κ where
  square := R.square.reindex e
  resolution := {
    column := fun t ↦ e.symm.trans ((R.resolution.column (e.symm t)).trans e)
    covers := fun i ↦ by
      simpa using e.bijective.comp
        ((R.resolution.covers (e.symm i)).comp e.symm.bijective)
    orthonormal := fun t a b ↦ by
      simp only [QuantumLatinSquare.reindex, Equiv.trans_apply,
        Equiv.apply_symm_apply]
      rw [dot_reindexKet]
      simpa using R.resolution.orthonormal (e.symm t) (e.symm a) (e.symm b) }
  maximal := by
    intro i j i' j' h
    rcases h with ⟨z, hz, h⟩
    have h' : PhaseEquivalent
        (R.square.entry (e.symm i) (e.symm j))
        (R.square.entry (e.symm i') (e.symm j')) := by
      refine ⟨z, hz, ?_⟩
      funext a
      have ha := congrFun h (e a)
      simpa [QuantumLatinSquare.reindex, reindexKet] using ha
    rcases R.maximal h' with ⟨hi, hj⟩
    exact ⟨e.symm.injective hi, e.symm.injective hj⟩

/-- Package a construction on any finite type as one of numerical order equal
to its cardinality. -/
theorem existsMaximalRQLS_card (R : MaximalRQLS ι) :
    ExistsMaximalRQLS (Fintype.card ι) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  exact ⟨R.reindex e⟩

end Reindex

end LeanCo.QuantumLatin
