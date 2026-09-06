import LeanCo.QuantumLatin.Biresolution
import LeanCo.QuantumLatin.Tensor
import LeanCo.QuantumLatin.SeparatedCopies

/-!
# Resolved block products

This is the ordinary block product used for the exceptional order `90`.
The outer classical square supplies a transversal label for each block, and
each label receives a projectively disjoint inner maximal RQLS copy.
-/

namespace LeanCo.QuantumLatin

universe u v

section

variable {α : Type u} {β : Type v}
  [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The block array underlying the resolved direct product. -/
def resolvedBlockSquare (A : ClassicalResolvedSquare α)
    (B : PhaseDisjointMaximalRQLSFamily α β) :
    QuantumLatinSquare (α × β) where
  entry p q := tensorKet
    (basis (A.base.symbol p.1 q.1))
    ((B.copy (A.first.symbol p.1 q.1)).square.entry p.2 q.2)
  row_orthonormal := by
    rintro ⟨i, k⟩ ⟨j, l⟩ ⟨j', l'⟩
    rw [dot_tensorKet]
    by_cases hj : j = j'
    · subst j'
      rw [show dot (basis (A.base.symbol i j))
          (basis (A.base.symbol i j)) = 1 from dot_self_basis _,
        (B.copy (A.first.symbol i j)).square.row_orthonormal]
      simp only [ite_mul, one_mul, zero_mul]
      by_cases hl : l = l'
      · simp [hl]
      · simp [hl]
    · have hs : A.base.symbol i j ≠ A.base.symbol i j' :=
        fun h ↦ hj ((A.base.row_bijective i).1 h)
      rw [show dot (basis (A.base.symbol i j))
          (basis (A.base.symbol i j')) = 0 by
        simpa [basis, hs] using
          (dot_basis_basis (A.base.symbol i j) (A.base.symbol i j')), zero_mul]
      simp [hj]
  col_orthonormal := by
    rintro ⟨j, l⟩ ⟨i, k⟩ ⟨i', k'⟩
    rw [dot_tensorKet]
    by_cases hi : i = i'
    · subst i'
      rw [show dot (basis (A.base.symbol i j))
          (basis (A.base.symbol i j)) = 1 from dot_self_basis _,
        (B.copy (A.first.symbol i j)).square.col_orthonormal]
      simp only [ite_mul, one_mul, zero_mul]
      by_cases hk : k = k'
      · simp [hk]
      · simp [hk]
    · have hs : A.base.symbol i j ≠ A.base.symbol i' j :=
        fun h ↦ hi ((A.base.col_bijective j).1 h)
      rw [show dot (basis (A.base.symbol i j))
          (basis (A.base.symbol i' j)) = 0 by
        simpa [basis, hs] using
          (dot_basis_basis (A.base.symbol i j) (A.base.symbol i' j)), zero_mul]
      simp [hi]

private noncomputable def blockColumnFun (A : ClassicalResolvedSquare α)
    (B : PhaseDisjointMaximalRQLSFamily α β) (q : α) (e : β) :
    α × β → α × β := fun p ↦
  let j := A.second.fiberColumn q p.1
  let g := A.first.symbol p.1 j
  (j, (B.copy g).resolution.column e p.2)

private theorem blockColumnFun_bijective (A : ClassicalResolvedSquare α)
    (B : PhaseDisjointMaximalRQLSFamily α β) (q : α) (e : β) :
    Function.Bijective (blockColumnFun A B q e) := by
  constructor
  · rintro ⟨i, k⟩ ⟨i', k'⟩ h
    have hj : A.second.fiberColumn q i = A.second.fiberColumn q i' :=
      congrArg Prod.fst h
    have hi : i = i' := (A.second.fiberColumn_bijective q).1 hj
    subst i'
    have hk : k = k' := by
      apply (B.copy (A.first.symbol i (A.second.fiberColumn q i))).resolution.column e |>.injective
      exact congrArg Prod.snd h
    exact Prod.ext rfl hk
  · rintro ⟨j, l⟩
    obtain ⟨i, hi⟩ := (A.second.fiberColumn_bijective q).2 j
    let g := A.first.symbol i j
    obtain ⟨k, hk⟩ := ((B.copy g).resolution.column e).surjective l
    refine ⟨(i, k), ?_⟩
    apply Prod.ext
    · exact hi
    · change (B.copy (A.first.symbol i
        (A.second.fiberColumn q i))).resolution.column e k = l
      dsimp [g] at hk
      rw [hi]
      exact hk

private noncomputable def blockCoverFun (A : ClassicalResolvedSquare α)
    (B : PhaseDisjointMaximalRQLSFamily α β) (p : α × β) :
    α × β → α × β := fun t ↦ blockColumnFun A B t.1 t.2 p

private theorem blockCoverFun_bijective (A : ClassicalResolvedSquare α)
    (B : PhaseDisjointMaximalRQLSFamily α β) (p : α × β) :
    Function.Bijective (blockCoverFun A B p) := by
  constructor
  · rintro ⟨q, e⟩ ⟨q', e'⟩ h
    have hj : A.second.fiberColumn q p.1 =
        A.second.fiberColumn q' p.1 := congrArg Prod.fst h
    have hq : q = q' := by
      have := congrArg (A.second.symbol p.1) hj
      simpa using this
    subst q'
    let j := A.second.fiberColumn q p.1
    let g := A.first.symbol p.1 j
    have he : e = e' := by
      have hl := congrArg Prod.snd h
      change (B.copy g).resolution.column e p.2 =
        (B.copy g).resolution.column e' p.2 at hl
      exact ((B.copy g).resolution.covers p.2).1 hl
    exact Prod.ext rfl he
  · rintro ⟨j, l⟩
    let q := A.second.symbol p.1 j
    have hj : A.second.fiberColumn q p.1 = j :=
      A.second.fiberColumn_symbol p.1 j
    let g := A.first.symbol p.1 j
    obtain ⟨e, he⟩ := ((B.copy g).resolution.covers p.2).2 l
    refine ⟨(q, e), ?_⟩
    apply Prod.ext
    · exact hj
    · change (B.copy (A.first.symbol p.1
        (A.second.fiberColumn q p.1))).resolution.column e p.2 = l
      dsimp [g] at he
      rw [hj]
      exact he

/-- Resolution combining the outer second transversal partition with each
inner resolution. -/
noncomputable def resolvedBlockResolution (A : ClassicalResolvedSquare α)
    (B : PhaseDisjointMaximalRQLSFamily α β) :
    (resolvedBlockSquare A B).Resolution where
  column t := Equiv.ofBijective (blockColumnFun A B t.1 t.2)
    (blockColumnFun_bijective A B t.1 t.2)
  covers p := by
    change Function.Bijective (blockCoverFun A B p)
    exact blockCoverFun_bijective A B p
  orthonormal t := by
    rintro ⟨i, k⟩ ⟨i', k'⟩
    change dot
      (tensorKet (basis (A.base.symbol i (A.second.fiberColumn t.1 i)))
        ((B.copy (A.first.symbol i (A.second.fiberColumn t.1 i))).square.entry k
          ((B.copy (A.first.symbol i (A.second.fiberColumn t.1 i))).resolution.column
            t.2 k)))
      (tensorKet (basis (A.base.symbol i' (A.second.fiberColumn t.1 i')))
        ((B.copy (A.first.symbol i' (A.second.fiberColumn t.1 i'))).square.entry k'
          ((B.copy (A.first.symbol i' (A.second.fiberColumn t.1 i'))).resolution.column
            t.2 k'))) = if (i, k) = (i', k') then 1 else 0
    rw [dot_tensorKet]
    by_cases hi : i = i'
    · subst i'
      rw [show dot (basis (A.base.symbol i (A.second.fiberColumn t.1 i)))
          (basis (A.base.symbol i (A.second.fiberColumn t.1 i))) = 1 from
        dot_self_basis _,
        (B.copy (A.first.symbol i (A.second.fiberColumn t.1 i))).resolution.orthonormal]
      by_cases hk : k = k'
      · simp [hk]
      · simp [hk]
    · have hs : A.base.symbol i (A.second.fiberColumn t.1 i) ≠
          A.base.symbol i' (A.second.fiberColumn t.1 i') := by
        intro hs
        have hl : A.second.symbol i (A.second.fiberColumn t.1 i) =
            A.second.symbol i' (A.second.fiberColumn t.1 i') := by simp
        exact hi (A.base_second hs hl).1
      rw [show dot (basis (A.base.symbol i (A.second.fiberColumn t.1 i)))
          (basis (A.base.symbol i' (A.second.fiberColumn t.1 i'))) = 0 by
        simpa [basis, hs] using
          (dot_basis_basis
            (A.base.symbol i (A.second.fiberColumn t.1 i))
            (A.base.symbol i' (A.second.fiberColumn t.1 i'))), zero_mul]
      simp [hi]

private theorem phaseEquivalent_basis_iff {x y : α} :
    PhaseEquivalent (basis x : Ket α) (basis y) ↔ x = y := by
  constructor
  · rintro ⟨z, hz, h⟩
    by_contra hxy
    have hp := congrFun h x
    simp [basis_apply, Ne.symm hxy] at hp
  · rintro rfl
    exact PhaseEquivalent.refl _

/-- Resolved block product, including the maximality argument omitted behind
the “standard direct-product argument” in the paper's order-90 proof. -/
noncomputable def resolvedBlockMaximalRQLS (A : ClassicalResolvedSquare α)
    (B : PhaseDisjointMaximalRQLSFamily α β) : MaximalRQLS (α × β) where
  square := resolvedBlockSquare A B
  resolution := resolvedBlockResolution A B
  maximal := by
    rintro ⟨i, k⟩ ⟨j, l⟩ ⟨i', k'⟩ ⟨j', l'⟩ hphase
    change PhaseEquivalent
      (tensorKet (basis (A.base.symbol i j))
        ((B.copy (A.first.symbol i j)).square.entry k l))
      (tensorKet (basis (A.base.symbol i' j'))
        ((B.copy (A.first.symbol i' j')).square.entry k' l')) at hphase
    rcases phaseEquivalent_tensorKet_factors
      (dot_self_basis _) (dot_self_basis _)
      ((B.copy (A.first.symbol i j)).square.row_norm k l)
      ((B.copy (A.first.symbol i' j')).square.row_norm k' l') hphase with
      ⟨hbase, hinner⟩
    have hs : A.base.symbol i j = A.base.symbol i' j' :=
      phaseEquivalent_basis_iff.mp hbase
    have hg : A.first.symbol i j = A.first.symbol i' j' := by
      by_contra hne
      exact B.pairwise_disjoint hne k l k' l' hinner
    rcases A.base_first hs hg with ⟨hi, hj⟩
    subst i'; subst j'
    rcases (B.copy (A.first.symbol i j)).maximal hinner with ⟨hk, hl⟩
    exact ⟨Prod.ext rfl hk, Prod.ext rfl hl⟩

end

end LeanCo.QuantumLatin
