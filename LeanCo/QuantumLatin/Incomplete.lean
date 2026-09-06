import LeanCo.QuantumLatin.Defs

/-!
# Pointed squares and incomplete resolvable squares

Deleting the distinguished lower-right basis entry from a pointed maximal
RQLS gives the `IRQLS(m+1,1)` used by the singular direct product.  We retain
the original square and resolution, which makes every row, column and
transversal law available without duplicating partial-array bookkeeping.
-/

open scoped BigOperators ComplexConjugate

namespace LeanCo.QuantumLatin

universe u

/-- An RQLS on `Option β` whose distinguished cell is the distinguished
computational basis state and lies in the distinguished transversal. -/
structure PointedMaximalRQLS (β : Type u) [Fintype β] [DecidableEq β] where
  full : MaximalRQLS (Option β)
  hole_entry : full.square.entry none none = basis none
  hole_transversal : full.resolution.column none none = none

namespace PointedMaximalRQLS

variable {β : Type u} [Fintype β] [DecidableEq β]

/-- A nonempty cell of the punctured square. -/
def IsNonholeCell (r c : Option β) : Prop := r ≠ none ∨ c ≠ none

/-- Literal maximality of the incomplete array. -/
theorem punctured_maximal (P : PointedMaximalRQLS β)
    {r c r' c' : Option β} (_h : IsNonholeCell r c)
    (_h' : IsNonholeCell r' c')
    (hp : PhaseEquivalent (P.full.square.entry r c)
      (P.full.square.entry r' c')) : r = r' ∧ c = c' :=
  P.full.maximal hp

theorem dot_basis_left (a : Option β) (x : Ket (Option β)) :
    dot (basis a) x = x a := by
  classical
  rw [dot, Fintype.sum_eq_single a]
  · simp [basis_apply]
  · intro b hba
    simp [basis_apply, Ne.symm hba]

theorem dot_basis_right (a : Option β) (x : Ket (Option β)) :
    dot x (basis a) = conj (x a) := by
  classical
  rw [dot, Fintype.sum_eq_single a]
  · simp [basis_apply]
  · intro b hba
    simp [basis_apply, Ne.symm hba]

/-- Entries in the distinguished row, other than the hole, lie in the
`β`-coordinate subspace. -/
theorem holeRow_lastCoord_zero (P : PointedMaximalRQLS β) (c : β) :
    P.full.square.entry none (some c) none = 0 := by
  have horth := P.full.square.row_orthonormal none none (some c)
  rw [if_neg (by simp)] at horth
  rw [P.hole_entry, dot_basis_left] at horth
  exact horth

/-- Entries in the distinguished column, other than the hole, lie in the
`β`-coordinate subspace. -/
theorem holeCol_lastCoord_zero (P : PointedMaximalRQLS β) (r : β) :
    P.full.square.entry (some r) none none = 0 := by
  have horth := P.full.square.col_orthonormal none none (some r)
  rw [if_neg (by simp)] at horth
  change dot (P.full.square.entry none none)
    (P.full.square.entry (some r) none) = 0 at horth
  rw [P.hole_entry, dot_basis_left] at horth
  exact horth

/-- The distinguished transversal restricts to a permutation of the
non-hole rows and columns. -/
def incompleteColumn (P : PointedMaximalRQLS β) : Equiv.Perm β where
  toFun r := (P.full.resolution.column none (some r)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hnone
    have hEq : P.full.resolution.column none (some r) =
        P.full.resolution.column none none := by
      exact hnone.trans P.hole_transversal.symm
    apply Option.some_ne_none r
    exact (P.full.resolution.column none).injective hEq)
  invFun c := ((P.full.resolution.column none).symm (some c)).get (by
    apply Option.isSome_iff_ne_none.mpr
    intro hnone
    apply Option.some_ne_none c
    calc
      some c = P.full.resolution.column none
          ((P.full.resolution.column none).symm (some c)) :=
        ((P.full.resolution.column none).apply_symm_apply (some c)).symm
      _ = P.full.resolution.column none none := by rw [hnone]
      _ = none := P.hole_transversal)
  left_inv r := by
    apply Option.some_injective
    simp only [Option.some_get]
    exact (P.full.resolution.column none).symm_apply_apply (some r)
  right_inv c := by
    apply Option.some_injective
    simp only [Option.some_get]
    exact (P.full.resolution.column none).apply_symm_apply (some c)

@[simp] theorem incompleteColumn_some (P : PointedMaximalRQLS β) (r : β) :
    some (P.incompleteColumn r) = P.full.resolution.column none (some r) := by
  simp [incompleteColumn]

/-- The incomplete transversal is an ONB of the first-coordinate subspace. -/
theorem incomplete_orthonormal (P : PointedMaximalRQLS β) :
    IsOrthonormal (fun r : β ↦
      fun c : β ↦ P.full.square.entry (some r)
        (some (P.incompleteColumn r)) (some c)) := by
  intro r r'
  have h := P.full.resolution.orthonormal none (some r) (some r')
  change dot
      (P.full.square.entry (some r)
        (P.full.resolution.column none (some r)))
      (P.full.square.entry (some r')
        (P.full.resolution.column none (some r'))) = _ at h
  rw [← P.incompleteColumn_some r, ← P.incompleteColumn_some r'] at h
  change (∑ c : Option β,
      conj (P.full.square.entry (some r) (some (P.incompleteColumn r)) c) *
        P.full.square.entry (some r') (some (P.incompleteColumn r')) c) = _ at h
  change (∑ c : β,
      conj (P.full.square.entry (some r) (some (P.incompleteColumn r)) (some c)) *
        P.full.square.entry (some r') (some (P.incompleteColumn r')) (some c)) = _
  have hz (x : β) :
      P.full.square.entry (some x)
        (P.full.resolution.column none (some x)) none = 0 := by
    have hi := P.full.resolution.orthonormal none none (some x)
    rw [if_neg (by simp)] at hi
    change dot
      (P.full.square.entry none (P.full.resolution.column none none))
      (P.full.square.entry (some x)
        (P.full.resolution.column none (some x))) = 0 at hi
    rw [P.hole_transversal, P.hole_entry, dot_basis_left] at hi
    exact hi
  rw [Fintype.sum_option] at h
  simpa [hz] using h

/-- A regular pointed square has two fixed surviving coordinates nonzero in
every non-hole entry.  This is the finite-avoidance hypothesis needed for
arbitrarily many mutually ray-disjoint punctured copies. -/
def RegularAt (P : PointedMaximalRQLS β) (d e : β) : Prop :=
  d ≠ e ∧ ∀ r c : Option β, IsNonholeCell r c →
    P.full.square.entry r c (some d) ≠ 0 ∧
      P.full.square.entry r c (some e) ≠ 0

end PointedMaximalRQLS

end LeanCo.QuantumLatin
