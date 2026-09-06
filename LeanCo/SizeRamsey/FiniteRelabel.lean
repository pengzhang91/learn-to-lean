import LeanCo.SizeRamsey.DensityCore

/-!
# Relabelling finite size--Ramsey witnesses

This file transports edge colourings and the cycle-arrow relation across graph
isomorphisms, then packages mathlib's canonical relabelling of a finite graph
onto `Fin (Fintype.card V)`.  The final theorem turns a witness on an arbitrary
finite vertex type into the literal `Fin N` witness required by
`IsCycleSizeRamseyUpperBound`.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

universe u v w

variable {V : Type u} {W : Type v} {X : Type w}

/-! ## Transporting labelled colour classes -/

/-- Pulling an edge labelling back along a graph isomorphism makes each colour
class graph isomorphic to the original colour class graph. -/
noncomputable def labelGraphPullbackIso
    {G : SimpleGraph V} {H : SimpleGraph W} {K : Type*}
    (e : G ≃g H) (C : H.EdgeLabeling K) (color : K) :
    (C.pullback e.toHom).labelGraph color ≃g C.labelGraph color where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    rw [EdgeLabeling.labelGraph_adj, EdgeLabeling.labelGraph_adj]
    constructor
    · rintro ⟨hxy, hcolor⟩
      refine ⟨e.map_adj_iff.mp hxy, ?_⟩
      exact hcolor
    · rintro ⟨hxy, hcolor⟩
      refine ⟨e.toHom.map_adj hxy, ?_⟩
      exact hcolor

/-! ## Isomorphism invariance of arrowing -/

/-- The general arrow relation is invariant under an isomorphism of its host
graph. -/
theorem arrows_iff_of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    {K : Type*} {J : SimpleGraph X} (e : G ≃g H) :
    Arrows G K J ↔ Arrows H K J := by
  constructor
  · intro h C
    obtain ⟨color, hcopy⟩ := h (C.pullback e.toHom)
    exact ⟨color, hcopy.trans ⟨(labelGraphPullbackIso e C color).toCopy⟩⟩
  · intro h C
    obtain ⟨color, hcopy⟩ := h (C.pullback e.symm.toHom)
    exact ⟨color,
      hcopy.trans ⟨(labelGraphPullbackIso e.symm C color).toCopy⟩⟩

/-- In particular, `ArrowsCycle` is invariant under graph isomorphism. -/
theorem arrowsCycle_iff_of_iso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {k n : ℕ} :
    ArrowsCycle G k n ↔ ArrowsCycle H k n :=
  arrows_iff_of_iso e

/-! ## Canonical relabelling onto a `Fin` type -/

/-- The canonical copy of a finite graph whose vertices are labelled by
`Fin (Fintype.card V)`. -/
noncomputable def finiteRelabel [Fintype V] (G : SimpleGraph V) :
    SimpleGraph (Fin (Fintype.card V)) :=
  G.overFin rfl

/-- The canonical graph isomorphism to `finiteRelabel G`. -/
noncomputable def finiteRelabelIso [Fintype V] (G : SimpleGraph V) :
    G ≃g finiteRelabel G :=
  G.overFinIso rfl

/-- Canonical finite relabelling preserves the number of edges. -/
theorem edgeCount_finiteRelabel [Fintype V] (G : SimpleGraph V) :
    edgeCount (finiteRelabel G) = edgeCount G := by
  exact (edgeCount_eq_of_iso (finiteRelabelIso G)).symm

/-- Canonical finite relabelling preserves the cycle-arrow relation. -/
theorem arrowsCycle_finiteRelabel_iff [Fintype V] (G : SimpleGraph V)
    {k n : ℕ} :
    ArrowsCycle (finiteRelabel G) k n ↔ ArrowsCycle G k n := by
  exact (arrowsCycle_iff_of_iso (finiteRelabelIso G)).symm

/-! ## Packaging a finite witness -/

/-- Any finite host witness, regardless of its original vertex type, can be
used directly as a cycle size--Ramsey upper-bound witness after canonical
relabelling. -/
theorem isCycleSizeRamseyUpperBound_of_finiteWitness
    [Fintype V] {G : SimpleGraph V} {k n m : ℕ}
    (hedge : edgeCount G ≤ m) (harrow : ArrowsCycle G k n) :
    IsCycleSizeRamseyUpperBound k n m := by
  refine ⟨Fintype.card V, finiteRelabel G, ?_, ?_⟩
  · simpa only [edgeCount_finiteRelabel] using hedge
  · exact (arrowsCycle_finiteRelabel_iff G).2 harrow

/-- Real-valued edge estimates, such as the output of `RandomUpperExact`, can
be packaged without a separate rounding argument: round the proposed bound up
and canonically relabel the finite witness. -/
theorem isCycleSizeRamseyUpperBound_natCeil_of_finiteWitness
    [Fintype V] {G : SimpleGraph V} {k n : ℕ} {bound : ℝ}
    (hedge : (edgeCount G : ℝ) ≤ bound) (harrow : ArrowsCycle G k n) :
    IsCycleSizeRamseyUpperBound k n ⌈bound⌉₊ := by
  apply isCycleSizeRamseyUpperBound_of_finiteWitness (G := G) (harrow := harrow)
  have hedge' : (edgeCount G : ℝ) ≤ (⌈bound⌉₊ : ℕ) :=
    hedge.trans (Nat.le_ceil bound)
  exact_mod_cast hedge'

end LeanCo.SizeRamsey
