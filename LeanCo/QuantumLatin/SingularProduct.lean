import LeanCo.QuantumLatin.Biresolution
import LeanCo.QuantumLatin.ExtendedTensor
import LeanCo.QuantumLatin.Incomplete
import LeanCo.QuantumLatin.SeparatedCopies

/-!
# The singular direct product

This file gives a literal version of Construction 4.6 of Zhang--Cao.  The
final row, column, and coordinate type is `(α × β) ⊕ ρ`, of cardinality
`|α| |β| + |ρ|`.  The first resolution of the outer classical square says
which blocks are ordinary and which are punctured; the second resolution is
used to assemble the ordinary transversals of the product.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

universe u v w x

variable {α : Type u} {β : Type v} {ρ : Type w} {γ : Type x}
  [Fintype α] [Fintype β] [Fintype ρ]
  [DecidableEq α] [DecidableEq β] [DecidableEq ρ]

@[simp] theorem dot_basis_named {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a b : κ) : dot (basis a) (basis b) = if a = b then 1 else 0 := by
  simpa [basis] using LeanCo.QuantumLatin.dot_basis_basis a b

@[simp] theorem dot_basis_named_self {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : κ) : dot (basis a) (basis a) = 1 := by simp

/-- A family of pointed squares whose non-hole entries are pairwise
projectively disjoint.  The distinguished hole vector is deliberately shared
and is not part of the associated incomplete squares. -/
structure PhaseDisjointPointedRQLSFamily (ρ : Type w) (β : Type v)
    [Fintype β] [DecidableEq β] where
  copy : ρ → PointedMaximalRQLS β
  pairwise_disjoint : ∀ ⦃r s : ρ⦄, r ≠ s →
    ∀ ⦃i j i' j' : Option β⦄,
      PointedMaximalRQLS.IsNonholeCell i j →
      PointedMaximalRQLS.IsNonholeCell i' j' →
      ¬ PhaseEquivalent
        ((copy r).full.square.entry i j)
        ((copy s).full.square.entry i' j')

/-- The final block containing the exceptional square. -/
def exceptionalKet (d : Ket ρ) : Ket ((α × β) ⊕ ρ)
  | Sum.inl _ => 0
  | Sum.inr r => d r

theorem dot_exceptionalKet (d d' : Ket ρ) :
    dot (exceptionalKet (α := α) (β := β) d)
      (exceptionalKet (α := α) (β := β) d') = dot d d' := by
  classical
  simp [dot, exceptionalKet, Fintype.sum_sum_type]

theorem dot_extended_exceptional (a : Ket α) (b : Ket β) (d : Ket ρ) :
    dot (extendedTensor (ρ := ρ) a b)
      (exceptionalKet (α := α) (β := β) d) = 0 := by
  classical
  simp [dot, extendedTensor, exceptionalKet, Fintype.sum_sum_type]

theorem dot_exceptional_extended (d : Ket ρ) (a : Ket α) (b : Ket β) :
    dot (exceptionalKet (α := α) (β := β) d)
      (extendedTensor (ρ := ρ) a b) = 0 := by
  classical
  simp [dot, extendedTensor, exceptionalKet, Fintype.sum_sum_type]

theorem dot_parameter_exceptional (r : ρ) (a : Ket α)
    (c : Ket (Option β)) (d : Ket ρ) :
    dot (parameterTensor r a c)
      (exceptionalKet (α := α) (β := β) d) = conj (c none) * d r := by
  classical
  rw [dot, Fintype.sum_sum_type]
  simp only [parameterTensor, exceptionalKet, map_zero, zero_mul,
    Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_eq_single r]
  · simp
  · intro s hsr
    simp [hsr]

theorem dot_exceptional_parameter (d : Ket ρ) (r : ρ) (a : Ket α)
    (c : Ket (Option β)) :
    dot (exceptionalKet (α := α) (β := β) d)
      (parameterTensor r a c) = conj (d r) * c none := by
  classical
  simp [dot, parameterTensor, exceptionalKet, Fintype.sum_sum_type]

namespace ClassicalQuantumLatinSquare

/-- In a fixed column, the unique row carrying a prescribed symbol. -/
noncomputable def fiberRow (A : ClassicalQuantumLatinSquare α) (t j : α) : α :=
  Classical.choose ((A.col_bijective j).surjective t)

@[simp] theorem symbol_fiberRow (A : ClassicalQuantumLatinSquare α)
    (t j : α) : A.symbol (A.fiberRow t j) j = t :=
  Classical.choose_spec ((A.col_bijective j).surjective t)

@[simp] theorem fiberRow_symbol (A : ClassicalQuantumLatinSquare α)
    (i j : α) : A.fiberRow (A.symbol i j) j = i := by
  apply (A.col_bijective j).injective
  simp

theorem fiberRow_bijective (A : ClassicalQuantumLatinSquare α) (t : α) :
    Function.Bijective (A.fiberRow t) := by
  constructor
  · intro j j' h
    have hs : A.symbol (A.fiberRow t j) j =
        A.symbol (A.fiberRow t j) j' := by
      calc
        A.symbol (A.fiberRow t j) j = t := A.symbol_fiberRow t j
        _ = A.symbol (A.fiberRow t j') j' :=
          (A.symbol_fiberRow t j').symm
        _ = A.symbol (A.fiberRow t j) j' := by rw [h]
    exact (A.row_bijective (A.fiberRow t j)).injective hs
  · intro i
    obtain ⟨j, hj⟩ := (A.row_bijective i).surjective t
    refine ⟨j, ?_⟩
    rw [← hj]
    simp

end ClassicalQuantumLatinSquare

section Construction

variable [Fintype γ] [DecidableEq γ]

/-- Data needed by the singular array before its separation hypotheses are
added for maximality. -/
structure SingularProductData where
  outer : ClassicalBiresolution α
  split : α ≃ (γ ⊕ ρ)
  ordinary : PhaseDisjointMaximalRQLSFamily γ β
  special : PhaseDisjointPointedRQLSFamily ρ β
  exceptional : MaximalRQLS ρ

namespace SingularProductData

variable (X : SingularProductData (α := α) (β := β) (ρ := ρ) (γ := γ))

def specialLabel (r : ρ) : α := X.split.symm (Sum.inr r)

noncomputable def specialColumn (r : ρ) (i : α) : α :=
  X.outer.first.fiberColumn (X.specialLabel r) i

noncomputable def specialRow (r : ρ) (j : α) : α :=
  X.outer.first.fiberRow (X.specialLabel r) j

@[simp] theorem first_specialColumn (r : ρ) (i : α) :
    X.outer.first.symbol i (X.specialColumn r i) = X.specialLabel r := by
  simp [specialColumn]

@[simp] theorem first_specialRow (r : ρ) (j : α) :
    X.outer.first.symbol (X.specialRow r j) j = X.specialLabel r := by
  simp [specialRow]

/-- The array in Construction 4.6, including its three boundary pieces. -/
noncomputable def squareEntry :
    ((α × β) ⊕ ρ) → ((α × β) ⊕ ρ) → Ket ((α × β) ⊕ ρ)
  | Sum.inl (i, k), Sum.inl (j, l) =>
      match X.split (X.outer.first.symbol i j) with
      | Sum.inl g => extendedTensor (ρ := ρ)
          (basis (X.outer.base.symbol i j))
          ((X.ordinary.copy g).square.entry k l)
      | Sum.inr r => parameterTensor r
          (basis (X.outer.base.symbol i j))
          ((X.special.copy r).full.square.entry (some k) (some l))
  | Sum.inl (i, k), Sum.inr r =>
      let j := X.specialColumn r i
      parameterTensor r (basis (X.outer.base.symbol i j))
        ((X.special.copy r).full.square.entry (some k) none)
  | Sum.inr r, Sum.inl (j, l) =>
      let i := X.specialRow r j
      parameterTensor r (basis (X.outer.base.symbol i j))
        ((X.special.copy r).full.square.entry none (some l))
  | Sum.inr r, Sum.inr s =>
      exceptionalKet (α := α) (β := β)
        (X.exceptional.square.entry r s)

private theorem base_ne_of_row_ne (i : α) {j j' : α} (h : j ≠ j') :
    X.outer.base.symbol i j ≠ X.outer.base.symbol i j' :=
  fun hs ↦ h ((X.outer.base.row_bijective i).injective hs)

private theorem base_ne_of_col_ne (j : α) {i i' : α} (h : i ≠ i') :
    X.outer.base.symbol i j ≠ X.outer.base.symbol i' j :=
  fun hs ↦ h ((X.outer.base.col_bijective j).injective hs)

private theorem specialColumn_ne_of_label_ne (i j : α) (r : ρ)
    (h : X.split (X.outer.first.symbol i j) ≠ Sum.inr r) :
    j ≠ X.specialColumn r i := by
  intro hj
  apply h
  rw [hj, X.first_specialColumn]
  simp [specialLabel]

private theorem specialRow_ne_of_label_ne (i j : α) (r : ρ)
    (h : X.split (X.outer.first.symbol i j) ≠ Sum.inr r) :
    i ≠ X.specialRow r j := by
  intro hi
  apply h
  rw [hi, X.first_specialRow]
  simp [specialLabel]

theorem dot_conj_symm {κ : Type*} [Fintype κ] (x y : Ket κ) :
    dot y x = conj (dot x y) := by
  classical
  simp only [dot, map_sum, map_mul, Complex.conj_conj]
  apply Finset.sum_congr rfl
  intro z _
  ring

private theorem row_top_top (i : α) (k : β) (j l j' l') :
    dot (X.squareEntry (Sum.inl (i, k)) (Sum.inl (j, l)))
      (X.squareEntry (Sum.inl (i, k)) (Sum.inl (j', l'))) =
      if (j, l) = (j', l') then 1 else 0 := by
  by_cases hj : j = j'
  · subst j'
    cases hkind : X.split (X.outer.first.symbol i j) with
    | inl g =>
        simp only [squareEntry, hkind]
        rw [dot_extendedTensor, dot_basis_named_self,
          (X.ordinary.copy g).square.row_orthonormal]
        simp
    | inr r =>
        simp only [squareEntry, hkind]
        rw [dot_parameterTensor_same,
          (X.special.copy r).full.square.row_orthonormal]
        · simp
        · exact dot_basis_named_self _
  · have hb := X.base_ne_of_row_ne i hj
    cases hkind : X.split (X.outer.first.symbol i j) with
    | inl g =>
      cases hkind' : X.split (X.outer.first.symbol i j') with
      | inl g' =>
        simp only [squareEntry, hkind, hkind']
        rw [dot_extendedTensor, dot_basis_named, if_neg hb]
        simp [hj]
      | inr r' =>
        simp only [squareEntry, hkind, hkind']
        rw [dot_extended_parameter, dot_basis_named, if_neg hb]
        simp [hj]
    | inr r =>
      cases hkind' : X.split (X.outer.first.symbol i j') with
      | inl g' =>
        simp only [squareEntry, hkind, hkind']
        rw [dot_parameter_extended, dot_basis_named, if_neg hb]
        simp [hj]
      | inr r' =>
        have hrr : r ≠ r' := by
          intro h
          subst r'
          have hs : X.outer.first.symbol i j = X.outer.first.symbol i j' :=
            X.split.injective (hkind.trans hkind'.symm)
          exact hj ((X.outer.first.row_bijective i).injective hs)
        simp only [squareEntry, hkind, hkind']
        rw [dot_parameterTensor_basis, if_neg hb, if_neg hrr]
        simp [hj]

private theorem row_top_boundary (i : α) (k : β) (j : α) (l : β) (s : ρ) :
    dot (X.squareEntry (Sum.inl (i, k)) (Sum.inl (j, l)))
      (X.squareEntry (Sum.inl (i, k)) (Sum.inr s)) = 0 := by
  cases hkind : X.split (X.outer.first.symbol i j) with
  | inl g =>
      have hn : X.split (X.outer.first.symbol i j) ≠ Sum.inr s := by simp [hkind]
      have hj := X.specialColumn_ne_of_label_ne i j s hn
      have hb := X.base_ne_of_row_ne i hj
      simp only [squareEntry, hkind]
      rw [dot_extended_parameter, dot_basis_named, if_neg hb]
      simp
  | inr r =>
      by_cases hrs : r = s
      · subst s
        have hj : X.specialColumn r i = j := by
          apply (X.outer.first.row_bijective i).injective
          rw [X.first_specialColumn]
          apply X.split.injective
          rw [hkind]
          simp [specialLabel]
        simp only [squareEntry, hkind]
        rw [hj, dot_parameterTensor_same,
          (X.special.copy r).full.square.row_orthonormal]
        · simp
        · exact dot_basis_named_self _
      · have hn : X.split (X.outer.first.symbol i j) ≠ Sum.inr s := by
          rw [hkind]
          simp [hrs]
        have hj := X.specialColumn_ne_of_label_ne i j s hn
        have hb := X.base_ne_of_row_ne i hj
        simp only [squareEntry, hkind]
        rw [dot_parameterTensor_basis, if_neg hb, if_neg hrs]
        simp

private theorem row_boundary_boundary (i : α) (k : β) (r s : ρ) :
    dot (X.squareEntry (Sum.inl (i, k)) (Sum.inr r))
      (X.squareEntry (Sum.inl (i, k)) (Sum.inr s)) =
      if r = s then 1 else 0 := by
  by_cases hrs : r = s
  · subst s
    simp only [squareEntry]
    rw [dot_parameterTensor_same,
      (X.special.copy r).full.square.row_orthonormal]
    · simp
    · exact dot_basis_named_self _
  · have hj : X.specialColumn r i ≠ X.specialColumn s i := by
      intro h
      have hs := congrArg (X.outer.first.symbol i) h
      simp only [X.first_specialColumn] at hs
      have : Sum.inr r = (Sum.inr s : γ ⊕ ρ) := by
        simpa [specialLabel] using congrArg X.split hs
      exact hrs (Sum.inr_injective this)
    have hb := X.base_ne_of_row_ne i hj
    simp only [squareEntry]
    rw [dot_parameterTensor_basis, if_neg hb, if_neg hrs]
    simp [hrs]

private theorem row_bottom_top (r : ρ) (j l j' l') :
    dot (X.squareEntry (Sum.inr r) (Sum.inl (j, l)))
      (X.squareEntry (Sum.inr r) (Sum.inl (j', l'))) =
      if (j, l) = (j', l') then 1 else 0 := by
  by_cases hj : j = j'
  · subst j'
    simp only [squareEntry]
    rw [dot_parameterTensor_same,
      (X.special.copy r).full.square.row_orthonormal]
    · simp
    · exact dot_basis_named_self _
  · have hb : X.outer.base.symbol (X.specialRow r j) j ≠
        X.outer.base.symbol (X.specialRow r j') j' := by
      intro hs
      have hf : X.outer.first.symbol (X.specialRow r j) j =
          X.outer.first.symbol (X.specialRow r j') j' := by simp
      exact hj (X.outer.base_first hs hf).2
    simp only [squareEntry]
    rw [dot_parameterTensor_basis, if_neg hb,
      (X.special.copy r).holeRow_lastCoord_zero,
      (X.special.copy r).holeRow_lastCoord_zero]
    simp [hj]

private theorem col_top_top (j : α) (l : β) (i k i' k') :
    dot (X.squareEntry (Sum.inl (i, k)) (Sum.inl (j, l)))
      (X.squareEntry (Sum.inl (i', k')) (Sum.inl (j, l))) =
      if (i, k) = (i', k') then 1 else 0 := by
  by_cases hi : i = i'
  · subst i'
    cases hkind : X.split (X.outer.first.symbol i j) with
    | inl g =>
        simp only [squareEntry, hkind]
        rw [dot_extendedTensor, dot_basis_named_self,
          (X.ordinary.copy g).square.col_orthonormal]
        simp
    | inr r =>
        simp only [squareEntry, hkind]
        rw [dot_parameterTensor_same,
          (X.special.copy r).full.square.col_orthonormal]
        · simp
        · exact dot_basis_named_self _
  · have hb := X.base_ne_of_col_ne j hi
    cases hkind : X.split (X.outer.first.symbol i j) with
    | inl g =>
      cases hkind' : X.split (X.outer.first.symbol i' j) with
      | inl g' =>
        simp only [squareEntry, hkind, hkind']
        rw [dot_extendedTensor, dot_basis_named, if_neg hb]
        simp [hi]
      | inr r' =>
        simp only [squareEntry, hkind, hkind']
        rw [dot_extended_parameter, dot_basis_named, if_neg hb]
        simp [hi]
    | inr r =>
      cases hkind' : X.split (X.outer.first.symbol i' j) with
      | inl g' =>
        simp only [squareEntry, hkind, hkind']
        rw [dot_parameter_extended, dot_basis_named, if_neg hb]
        simp [hi]
      | inr r' =>
        have hrr : r ≠ r' := by
          intro h
          subst r'
          have hs : X.outer.first.symbol i j = X.outer.first.symbol i' j :=
            X.split.injective (hkind.trans hkind'.symm)
          exact hi ((X.outer.first.col_bijective j).injective hs)
        simp only [squareEntry, hkind, hkind']
        rw [dot_parameterTensor_basis, if_neg hb, if_neg hrr]
        simp [hi]

private theorem col_top_boundary (i : α) (k : β) (j : α) (l : β) (r : ρ) :
    dot (X.squareEntry (Sum.inl (i, k)) (Sum.inl (j, l)))
      (X.squareEntry (Sum.inr r) (Sum.inl (j, l))) = 0 := by
  cases hkind : X.split (X.outer.first.symbol i j) with
  | inl g =>
      have hn : X.split (X.outer.first.symbol i j) ≠ Sum.inr r := by simp [hkind]
      have hi := X.specialRow_ne_of_label_ne i j r hn
      have hb := X.base_ne_of_col_ne j hi
      simp only [squareEntry, hkind]
      rw [dot_extended_parameter, dot_basis_named, if_neg hb]
      simp
  | inr s =>
      by_cases hsr : s = r
      · subst r
        have hi : X.specialRow s j = i := by
          apply (X.outer.first.col_bijective j).injective
          change X.outer.first.symbol (X.specialRow s j) j =
            X.outer.first.symbol i j
          rw [X.first_specialRow]
          apply X.split.injective
          simp [specialLabel, hkind]
        simp only [squareEntry, hkind]
        rw [hi, dot_parameterTensor_same,
          (X.special.copy s).full.square.col_orthonormal]
        · simp
        · exact dot_basis_named_self _
      · have hn : X.split (X.outer.first.symbol i j) ≠ Sum.inr r := by
          rw [hkind]
          simp [hsr]
        have hi := X.specialRow_ne_of_label_ne i j r hn
        have hb := X.base_ne_of_col_ne j hi
        simp only [squareEntry, hkind]
        rw [dot_parameterTensor_basis, if_neg hb, if_neg hsr]
        simp

private theorem col_boundary_boundary (j : α) (l : β) (r s : ρ) :
    dot (X.squareEntry (Sum.inr r) (Sum.inl (j, l)))
      (X.squareEntry (Sum.inr s) (Sum.inl (j, l))) =
      if r = s then 1 else 0 := by
  by_cases hrs : r = s
  · subst s
    simp only [squareEntry]
    rw [dot_parameterTensor_same,
      (X.special.copy r).full.square.col_orthonormal]
    · simp
    · exact dot_basis_named_self _
  · have hi : X.specialRow r j ≠ X.specialRow s j := by
      intro h
      have hs := congrArg (fun i ↦ X.outer.first.symbol i j) h
      simp only [X.first_specialRow] at hs
      have : Sum.inr r = (Sum.inr s : γ ⊕ ρ) := by
        simpa [specialLabel] using congrArg X.split hs
      exact hrs (Sum.inr_injective this)
    have hb := X.base_ne_of_col_ne j hi
    simp only [squareEntry]
    rw [dot_parameterTensor_basis, if_neg hb, if_neg hrs]
    simp [hrs]

private theorem col_exception_top_top (s : ρ) (i k i' k') :
    dot (X.squareEntry (Sum.inl (i, k)) (Sum.inr s))
      (X.squareEntry (Sum.inl (i', k')) (Sum.inr s)) =
      if (i, k) = (i', k') then 1 else 0 := by
  by_cases hi : i = i'
  · subst i'
    simp only [squareEntry]
    rw [dot_parameterTensor_same,
      (X.special.copy s).full.square.col_orthonormal]
    · simp
    · exact dot_basis_named_self _
  · have hb : X.outer.base.symbol i (X.specialColumn s i) ≠
        X.outer.base.symbol i' (X.specialColumn s i') := by
      intro hs
      have hf : X.outer.first.symbol i (X.specialColumn s i) =
          X.outer.first.symbol i' (X.specialColumn s i') := by simp
      exact hi (X.outer.base_first hs hf).1
    simp only [squareEntry]
    rw [dot_parameterTensor_basis, if_neg hb,
      (X.special.copy s).holeCol_lastCoord_zero,
      (X.special.copy s).holeCol_lastCoord_zero]
    simp [hi]

/-- The singular block array is a quantum Latin square. -/
noncomputable def square : QuantumLatinSquare ((α × β) ⊕ ρ) where
  entry := X.squareEntry
  row_orthonormal row c c' := by
    rcases row with ⟨i, k⟩ | r
    · rcases c with ⟨j, l⟩ | s <;> rcases c' with ⟨j', l'⟩ | s'
      · simpa using X.row_top_top i k j l j' l'
      · simpa using X.row_top_boundary i k j l s'
      · rw [dot_conj_symm]
        simpa using congrArg conj (X.row_top_boundary i k j' l' s)
      · simpa using X.row_boundary_boundary i k s s'
    · rcases c with ⟨j, l⟩ | s <;> rcases c' with ⟨j', l'⟩ | s'
      · simpa using X.row_bottom_top r j l j' l'
      · simp only [squareEntry]
        rw [dot_parameter_exceptional,
          (X.special.copy r).holeRow_lastCoord_zero]
        simp
      · simp only [squareEntry]
        rw [dot_exceptional_parameter,
          (X.special.copy r).holeRow_lastCoord_zero]
        simp
      · simp only [squareEntry]
        rw [dot_exceptionalKet, X.exceptional.square.row_orthonormal]
        simp
  col_orthonormal c row row' := by
    rcases c with ⟨j, l⟩ | s
    · rcases row with ⟨i, k⟩ | r <;> rcases row' with ⟨i', k'⟩ | r'
      · simpa using X.col_top_top j l i k i' k'
      · simpa using X.col_top_boundary i k j l r'
      · rw [dot_conj_symm]
        simpa using congrArg conj (X.col_top_boundary i' k' j l r)
      · simpa using X.col_boundary_boundary j l r r'
    · rcases row with ⟨i, k⟩ | r <;> rcases row' with ⟨i', k'⟩ | r'
      · simpa using X.col_exception_top_top s i k i' k'
      · simp only [squareEntry]
        rw [dot_parameter_exceptional,
          (X.special.copy s).holeCol_lastCoord_zero]
        simp
      · simp only [squareEntry]
        rw [dot_exceptional_parameter,
          (X.special.copy s).holeCol_lastCoord_zero]
        simp
      · simp only [squareEntry]
        rw [dot_exceptionalKet, X.exceptional.square.col_orthonormal]
        simp

end SingularProductData

end Construction

end LeanCo.QuantumLatin
