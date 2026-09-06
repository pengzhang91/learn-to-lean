import LeanCo.QuantumLatin.Defs

/-!
# Resolvability and a classical orthogonal mate

This file formalizes Section 2 of Zhang--Cao, *Resolvable quantum Latin
squares with maximal cardinality*.  A classical quantum Latin square is
recorded by its Latin symbol table; its quantum entries are the corresponding
computational-basis vectors.  Orthogonality is expressed by the product of the
two Gram matrices, which is the inner product of the corresponding pure
tensors.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

universe u

noncomputable section

/-- A classical Latin square, retained together with the literal symbol in
each cell.  Replacing `symbol i j` by its computational-basis ket produces the
associated classical quantum Latin square. -/
structure ClassicalQuantumLatinSquare (ι : Type u) [Fintype ι] where
  symbol : ι → ι → ι
  row_bijective : ∀ i, Function.Bijective (symbol i)
  col_bijective : ∀ j, Function.Bijective (fun i ↦ symbol i j)

namespace ClassicalQuantumLatinSquare

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The classical QLS obtained by replacing every symbol by its computational
basis vector. -/
def toQuantumLatinSquare (L : ClassicalQuantumLatinSquare ι) :
    QuantumLatinSquare ι where
  entry i j := basis (L.symbol i j)
  row_orthonormal i a b := by
    change dot (Pi.single (L.symbol i a) 1) (Pi.single (L.symbol i b) 1) =
      if a = b then 1 else 0
    rw [dot_basis_basis]
    by_cases h : a = b
    · simp [h]
    · have hs : L.symbol i a ≠ L.symbol i b :=
        fun hab ↦ h ((L.row_bijective i).1 hab)
      simp [h, hs]
  col_orthonormal j a b := by
    change dot (Pi.single (L.symbol a j) 1) (Pi.single (L.symbol b j) 1) =
      if a = b then 1 else 0
    rw [dot_basis_basis]
    by_cases h : a = b
    · simp [h]
    · have hs : L.symbol a j ≠ L.symbol b j :=
        fun hab ↦ h ((L.col_bijective j).1 hab)
      simp [h, hs]

@[simp] theorem toQuantumLatinSquare_entry
    (L : ClassicalQuantumLatinSquare ι) (i j : ι) :
    L.toQuantumLatinSquare.entry i j = basis (L.symbol i j) := rfl

end ClassicalQuantumLatinSquare

/-- Mutual orthogonality of two QLSs, written exactly as the product of their
Gram entries.  This product is the inner product of the corresponding pure
tensor kets. -/
def MutuallyOrthogonal {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : QuantumLatinSquare ι) : Prop :=
  ∀ i j i' j',
    dot (A.entry i j) (A.entry i' j') *
        dot (B.entry i j) (B.entry i' j') =
      if i = i' ∧ j = j' then 1 else 0

namespace QuantumLatinSquare.Resolution

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {A : QuantumLatinSquare ι}

/-- At a fixed row, a resolution bijects transversal labels with columns. -/
def rowLabelEquiv (R : A.Resolution) (i : ι) : ι ≃ ι :=
  Equiv.ofBijective (fun t ↦ R.column t i) (R.covers i)

/-- The label of the unique transversal containing cell `(i,j)`. -/
def label (R : A.Resolution) (i j : ι) : ι :=
  (R.rowLabelEquiv i).symm j

@[simp] theorem column_label (R : A.Resolution) (i j : ι) :
    R.column (R.label i j) i = j := by
  exact (R.rowLabelEquiv i).apply_symm_apply j

@[simp] theorem label_column (R : A.Resolution) (t i : ι) :
    R.label i (R.column t i) = t := by
  exact (R.rowLabelEquiv i).symm_apply_apply t

theorem label_row_bijective (R : A.Resolution) (i : ι) :
    Function.Bijective (R.label i) :=
  (R.rowLabelEquiv i).symm.bijective

theorem label_col_bijective (R : A.Resolution) (j : ι) :
    Function.Bijective (fun i ↦ R.label i j) := by
  constructor
  · intro i i' hlabel
    have hcol : R.column (R.label i j) i =
        R.column (R.label i j) i' := by
      rw [R.column_label i j]
      have hj := (R.column_label i' j).symm
      simpa only [hlabel] using hj
    exact (R.column (R.label i j)).injective hcol
  · intro t
    let i : ι := (R.column t).symm j
    refine ⟨i, ?_⟩
    change R.label i j = t
    have hj : R.column t i = j := (R.column t).apply_symm_apply j
    rw [← hj, R.label_column]

/-- The classical square whose symbols are the labels of the transversals in
a resolution. -/
def classicalMate (R : A.Resolution) : ClassicalQuantumLatinSquare ι where
  symbol := R.label
  row_bijective := R.label_row_bijective
  col_bijective := R.label_col_bijective

end QuantumLatinSquare.Resolution

namespace QuantumLatinSquare

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Lemma 2.2, forward direction: labeling each cell by the unique
transversal that contains it gives a classical orthogonal mate. -/
theorem Resolution.mutuallyOrthogonal_classicalMate
    {A : QuantumLatinSquare ι} (R : A.Resolution) :
    MutuallyOrthogonal A R.classicalMate.toQuantumLatinSquare := by
  intro i j i' j'
  by_cases hcell : i = i' ∧ j = j'
  · rcases hcell with ⟨rfl, rfl⟩
    simp [ClassicalQuantumLatinSquare.toQuantumLatinSquare, basis]
  · rw [if_neg hcell]
    by_cases hlabel : R.label i j = R.label i' j'
    · have hii' : i ≠ i' := by
        intro hii'
        apply hcell
        refine ⟨hii', ?_⟩
        subst i'
        calc
          j = R.column (R.label i j) i := (R.column_label i j).symm
          _ = R.column (R.label i j') i := by rw [hlabel]
          _ = j' := R.column_label i j'
      have hA : dot (A.entry i j) (A.entry i' j') = 0 := by
        have horth := R.orthonormal (R.label i j) i i'
        rw [if_neg hii'] at horth
        change dot (A.entry i (R.column (R.label i j) i))
          (A.entry i' (R.column (R.label i j) i')) = 0 at horth
        have hj : R.column (R.label i j) i = j := R.column_label i j
        have hj' : R.column (R.label i j) i' = j' := by
          rw [hlabel]
          exact R.column_label i' j'
        rw [hj, hj'] at horth
        exact horth
      rw [hA]
      simp
    · have hB : dot
          (R.classicalMate.toQuantumLatinSquare.entry i j)
          (R.classicalMate.toQuantumLatinSquare.entry i' j') = 0 := by
        change dot (Pi.single (R.label i j) 1)
          (Pi.single (R.label i' j') 1) = 0
        rw [dot_basis_basis, if_neg hlabel]
      rw [hB]
      simp

end QuantumLatinSquare

namespace ClassicalQuantumLatinSquare

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Regard each row of a classical Latin square as an equivalence from
columns to symbols. -/
def rowEquiv (B : ClassicalQuantumLatinSquare ι) (i : ι) : ι ≃ ι :=
  Equiv.ofBijective (B.symbol i) (B.row_bijective i)

/-- In symbol fiber `t`, select in row `i` the unique column carrying `t`. -/
def fiberColumn (B : ClassicalQuantumLatinSquare ι) (t i : ι) : ι :=
  (B.rowEquiv i).symm t

@[simp] theorem symbol_fiberColumn
    (B : ClassicalQuantumLatinSquare ι) (t i : ι) :
    B.symbol i (B.fiberColumn t i) = t := by
  exact (B.rowEquiv i).apply_symm_apply t

@[simp] theorem fiberColumn_symbol
    (B : ClassicalQuantumLatinSquare ι) (i j : ι) :
    B.fiberColumn (B.symbol i j) i = j := by
  exact (B.rowEquiv i).symm_apply_apply j

theorem fiberColumn_bijective
    (B : ClassicalQuantumLatinSquare ι) (t : ι) :
    Function.Bijective (B.fiberColumn t) := by
  constructor
  · intro i i' hcol
    have hs : B.symbol i (B.fiberColumn t i) =
        B.symbol i' (B.fiberColumn t i) := by
      rw [B.symbol_fiberColumn t i, hcol, B.symbol_fiberColumn t i']
    exact (B.col_bijective (B.fiberColumn t i)).1 hs
  · intro j
    obtain ⟨i, hi⟩ := (B.col_bijective j).2 t
    refine ⟨i, ?_⟩
    rw [← hi]
    exact B.fiberColumn_symbol i j

end ClassicalQuantumLatinSquare

namespace QuantumLatinSquare


variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Lemma 2.2, reverse direction: the fibers of the symbols in a classical
orthogonal mate are a resolution. -/
def resolutionOfClassicalOrthogonalMate
    (A : QuantumLatinSquare ι) (B : ClassicalQuantumLatinSquare ι)
    (hAB : MutuallyOrthogonal A B.toQuantumLatinSquare) : A.Resolution where
  column t := Equiv.ofBijective (B.fiberColumn t) (B.fiberColumn_bijective t)
  covers i := by
    simpa [ClassicalQuantumLatinSquare.fiberColumn] using
      (B.rowEquiv i).symm.bijective
  orthonormal t i i' := by
    by_cases hii' : i = i'
    · subst i'
      simp
    · have hmo := hAB i (B.fiberColumn t i) i' (B.fiberColumn t i')
      have hcells : ¬(i = i' ∧ B.fiberColumn t i = B.fiberColumn t i') := by
        exact fun h ↦ hii' h.1
      rw [if_neg hcells] at hmo
      have hB : dot
          (B.toQuantumLatinSquare.entry i (B.fiberColumn t i))
          (B.toQuantumLatinSquare.entry i' (B.fiberColumn t i')) = 1 := by
        simpa [ClassicalQuantumLatinSquare.toQuantumLatinSquare, basis] using
          (dot_self_basis t)
      rw [hB, mul_one] at hmo
      simpa [hii'] using hmo

/-- Zhang--Cao Lemma 2.2: a QLS is resolvable exactly when it admits a
classical mutually orthogonal mate. -/
theorem resolution_iff_exists_classical_orthogonal_mate
    (A : QuantumLatinSquare ι) :
    Nonempty A.Resolution ↔
      ∃ B : ClassicalQuantumLatinSquare ι,
        MutuallyOrthogonal A B.toQuantumLatinSquare := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.classicalMate, R.mutuallyOrthogonal_classicalMate⟩
  · rintro ⟨B, hAB⟩
    exact ⟨resolutionOfClassicalOrthogonalMate A B hAB⟩

end QuantumLatinSquare

end

end LeanCo.QuantumLatin
