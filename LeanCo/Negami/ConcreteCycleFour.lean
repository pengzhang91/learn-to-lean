import LeanCo.Negami.ConcreteTwoBoundary
import LeanCo.Negami.CycleFour

/-!
# Actual graphs for Example 6.4

This file realizes the component-count sums of `CycleFour` by labelled finite
multigraphs.  It constructs the two-edge path over its endpoint boundary, its
two-parallel-edge boundary quotient, and the four-cycle obtained by gluing two
copies of the path.  All comparison maps are genuine multigraph isomorphisms.
-/

namespace LeanCo.Negami

open scoped BigOperators

/-! ## Three explicit labelled multigraphs -/

/-- The path `0--1--2`, with its two edges carrying labels `0,1`. -/
def examplePathGraph : FiniteMultigraph where
  Vertex := Fin 3
  Edge := Fin 2
  ends := ![s(0, 1), s(1, 2)]

/-- Two labelled parallel edges between vertices `0` and `1`. -/
def exampleParallelGraph : FiniteMultigraph where
  Vertex := Fin 2
  Edge := Fin 2
  ends := ![s(0, 1), s(0, 1)]

/-- The cyclically labelled four-cycle. -/
def exampleCycleFourGraph : FiniteMultigraph where
  Vertex := Fin 4
  Edge := Fin 4
  ends := ![s(0, 1), s(1, 2), s(2, 3), s(3, 0)]

/-- The endpoint boundary embedding `0 ↦ 0`, `1 ↦ 2` for the path. -/
def examplePathBoundaryEmbedding : Fin 2 ↪ examplePathGraph.Vertex where
  toFun := (![0, 2] : Fin 2 → Fin 3)
  inj' := by decide

/-- The path regarded as a graph over its two endpoint boundary vertices. -/
def examplePathOverBoundary : GraphOverBoundary (Fin 2) where
  graph := examplePathGraph
  boundaryEmbedding := examplePathBoundaryEmbedding

/-- The actual boundary quotient obtained by identifying the two endpoints of
the path. -/
noncomputable abbrev examplePathQuotient : FiniteMultigraph :=
  examplePathOverBoundary.toBoundaryMultigraph.quotientGraph
    connectedTwoPartition

/-- The actual pushout-style gluing of two copies of the path along their
endpoint boundary. -/
noncomputable abbrev exampleGluedCycleFour : FiniteMultigraph :=
  examplePathOverBoundary.toBoundaryMultigraph.gluedGraph
    examplePathOverBoundary.toBoundaryMultigraph (Equiv.refl (Fin 2))

/-! ## A reusable component classifier -/

/-- If a vertex coloring has equal colors exactly on connected vertices and
uses every color, it identifies the connected-component quotient with the
color type. -/
noncomputable def FiniteMultigraph.stateComponentEquivOfColor
    (G : FiniteMultigraph) (S : Finset G.Edge) (C : Type)
    (color : G.Vertex → C)
    (h : ∀ u v, G.StateConnected S u v ↔ color u = color v)
    (hs : Function.Surjective color) : G.StateComponent S ≃ C :=
  Equiv.ofBijective
    (Quotient.lift color (fun u v huv => (h u v).mp huv)) ⟨by
      intro a b hab
      induction a using Quotient.inductionOn with
      | _ u =>
        induction b using Quotient.inductionOn with
        | _ v =>
          apply Quotient.sound
          exact (h u v).mpr hab, by
      intro c
      rcases hs c with ⟨v, rfl⟩
      exact ⟨@Quotient.mk' _ (G.stateSetoid S) v, rfl⟩⟩

/-- Cardinal form of `stateComponentEquivOfColor`. -/
theorem FiniteMultigraph.omega_eq_natCard_of_color
    (G : FiniteMultigraph) (S : Finset G.Edge) (C : Type)
    (color : G.Vertex → C)
    (h : ∀ u v, G.StateConnected S u v ↔ color u = color v)
    (hs : Function.Surjective color) : G.omega S = Nat.card C := by
  unfold FiniteMultigraph.omega
  exact Nat.card_congr (G.stateComponentEquivOfColor S C color h hs)

/-! ## Exact component counts for the three explicit graphs -/

private instance pathAdjDecidable (S : Finset examplePathGraph.Edge) :
    DecidableRel (examplePathGraph.stateGraph S).Adj := fun u v => by
  change Decidable
    (s(u, v) ∈ (S.image examplePathGraph.ends :
      Finset (Sym2 examplePathGraph.Vertex)) ∧ u ≠ v)
  infer_instance

private instance pathConnectedDecidable (S : Finset examplePathGraph.Edge) :
    DecidableRel (examplePathGraph.StateConnected S) := by
  unfold FiniteMultigraph.StateConnected
  infer_instance

/-- The component count of every spanning state of the actual two-edge path. -/
theorem examplePathGraph_omega (S : Finset (Fin 2)) :
    examplePathGraph.omega S = pathComponentCount S := by
  have hcases : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
    fin_cases S <;> decide
  rcases hcases with h | h | h | h
  · subst S
    change examplePathGraph.omega (∅ : Finset (Fin 2)) = 3
    simpa only [Nat.card_fin] using
      examplePathGraph.omega_eq_natCard_of_color
        (∅ : Finset (Fin 2)) (Fin 3) id (by decide) (by decide)
  · subst S
    change examplePathGraph.omega ({0} : Finset (Fin 2)) = 2
    simpa only [Nat.card_fin] using
      examplePathGraph.omega_eq_natCard_of_color
        ({0} : Finset (Fin 2)) (Fin 2) ![0, 0, 1]
        (by decide) (by decide)
  · subst S
    change examplePathGraph.omega ({1} : Finset (Fin 2)) = 2
    simpa only [Nat.card_fin] using
      examplePathGraph.omega_eq_natCard_of_color
        ({1} : Finset (Fin 2)) (Fin 2) ![0, 1, 1]
        (by decide) (by decide)
  · subst S
    change examplePathGraph.omega ({0, 1} : Finset (Fin 2)) = 1
    simpa only [Nat.card_fin] using
      examplePathGraph.omega_eq_natCard_of_color
        ({0, 1} : Finset (Fin 2)) (Fin 1) (fun _ => 0)
        (by decide) (by decide)

private instance parallelAdjDecidable
    (S : Finset exampleParallelGraph.Edge) :
    DecidableRel (exampleParallelGraph.stateGraph S).Adj := fun u v => by
  change Decidable
    (s(u, v) ∈ (S.image exampleParallelGraph.ends :
      Finset (Sym2 exampleParallelGraph.Vertex)) ∧ u ≠ v)
  infer_instance

private instance parallelConnectedDecidable
    (S : Finset exampleParallelGraph.Edge) :
    DecidableRel (exampleParallelGraph.StateConnected S) := by
  unfold FiniteMultigraph.StateConnected
  infer_instance

/-- The component count of every spanning state of the actual parallel-edge
graph. -/
theorem exampleParallelGraph_omega (S : Finset (Fin 2)) :
    exampleParallelGraph.omega S = parallelComponentCount S := by
  have hcases : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
    fin_cases S <;> decide
  rcases hcases with h | h | h | h
  · subst S
    change exampleParallelGraph.omega (∅ : Finset (Fin 2)) = 2
    simpa only [Nat.card_fin] using
      exampleParallelGraph.omega_eq_natCard_of_color
        (∅ : Finset (Fin 2)) (Fin 2) id (by decide) (by decide)
  · subst S
    change exampleParallelGraph.omega ({0} : Finset (Fin 2)) = 1
    simpa only [Nat.card_fin] using
      exampleParallelGraph.omega_eq_natCard_of_color
        ({0} : Finset (Fin 2)) (Fin 1) (fun _ => 0)
        (by decide) (by decide)
  · subst S
    change exampleParallelGraph.omega ({1} : Finset (Fin 2)) = 1
    simpa only [Nat.card_fin] using
      exampleParallelGraph.omega_eq_natCard_of_color
        ({1} : Finset (Fin 2)) (Fin 1) (fun _ => 0)
        (by decide) (by decide)
  · subst S
    change exampleParallelGraph.omega ({0, 1} : Finset (Fin 2)) = 1
    simpa only [Nat.card_fin] using
      exampleParallelGraph.omega_eq_natCard_of_color
        ({0, 1} : Finset (Fin 2)) (Fin 1) (fun _ => 0)
        (by decide) (by decide)

private instance cycleFourAdjDecidable
    (S : Finset exampleCycleFourGraph.Edge) :
    DecidableRel (exampleCycleFourGraph.stateGraph S).Adj := fun u v => by
  change Decidable
    (s(u, v) ∈ (S.image exampleCycleFourGraph.ends :
      Finset (Sym2 exampleCycleFourGraph.Vertex)) ∧ u ≠ v)
  infer_instance

private instance cycleFourConnectedDecidable
    (S : Finset exampleCycleFourGraph.Edge) :
    DecidableRel (exampleCycleFourGraph.StateConnected S) := by
  unfold FiniteMultigraph.StateConnected
  infer_instance

private theorem finset_fin_four_cases (S : Finset (Fin 4)) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} ∨
    S = {2} ∨ S = {0, 2} ∨ S = {1, 2} ∨ S = {0, 1, 2} ∨
    S = {3} ∨ S = {0, 3} ∨ S = {1, 3} ∨ S = {0, 1, 3} ∨
    S = {2, 3} ∨ S = {0, 2, 3} ∨ S = {1, 2, 3} ∨
    S = {0, 1, 2, 3} := by
  fin_cases S <;> decide

/-- The component count of every spanning state of the actual cyclic graph. -/
theorem exampleCycleFourGraph_omega (S : Finset (Fin 4)) :
    exampleCycleFourGraph.omega S = cycleFourComponentCount S := by
  rcases finset_fin_four_cases S with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst S
    change exampleCycleFourGraph.omega (∅ : Finset (Fin 4)) = 4
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        (∅ : Finset (Fin 4)) (Fin 4) id (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({0} : Finset (Fin 4)) = 3
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({0} : Finset (Fin 4)) (Fin 3) ![0, 0, 1, 2]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({1} : Finset (Fin 4)) = 3
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({1} : Finset (Fin 4)) (Fin 3) ![0, 1, 1, 2]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({0, 1} : Finset (Fin 4)) = 2
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({0, 1} : Finset (Fin 4)) (Fin 2) ![0, 0, 0, 1]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({2} : Finset (Fin 4)) = 3
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({2} : Finset (Fin 4)) (Fin 3) ![0, 1, 2, 2]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({0, 2} : Finset (Fin 4)) = 2
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({0, 2} : Finset (Fin 4)) (Fin 2) ![0, 0, 1, 1]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({1, 2} : Finset (Fin 4)) = 2
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({1, 2} : Finset (Fin 4)) (Fin 2) ![0, 1, 1, 1]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({0, 1, 2} : Finset (Fin 4)) = 1
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({0, 1, 2} : Finset (Fin 4)) (Fin 1) (fun _ => 0)
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({3} : Finset (Fin 4)) = 3
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({3} : Finset (Fin 4)) (Fin 3) ![0, 1, 2, 0]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({0, 3} : Finset (Fin 4)) = 2
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({0, 3} : Finset (Fin 4)) (Fin 2) ![0, 0, 1, 0]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({1, 3} : Finset (Fin 4)) = 2
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({1, 3} : Finset (Fin 4)) (Fin 2) ![0, 1, 1, 0]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({0, 1, 3} : Finset (Fin 4)) = 1
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({0, 1, 3} : Finset (Fin 4)) (Fin 1) (fun _ => 0)
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({2, 3} : Finset (Fin 4)) = 2
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({2, 3} : Finset (Fin 4)) (Fin 2) ![0, 1, 0, 0]
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({0, 2, 3} : Finset (Fin 4)) = 1
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({0, 2, 3} : Finset (Fin 4)) (Fin 1) (fun _ => 0)
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega ({1, 2, 3} : Finset (Fin 4)) = 1
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({1, 2, 3} : Finset (Fin 4)) (Fin 1) (fun _ => 0)
        (by decide) (by decide)
  · subst S
    change exampleCycleFourGraph.omega
      ({0, 1, 2, 3} : Finset (Fin 4)) = 1
    simpa only [Nat.card_fin] using
      exampleCycleFourGraph.omega_eq_natCard_of_color
        ({0, 1, 2, 3} : Finset (Fin 4)) (Fin 1) (fun _ => 0)
        (by decide) (by decide)

/-! ## Equality with the previously collected finite sums -/

/-- The finite component-count sum for the path is its actual graph state
sum. -/
theorem examplePathGraph_stateSum {R : Type*} [CommRing R]
    (t x y : R) :
    examplePathGraph.stateSum t x y = pathStateSum t x y := by
  classical
  unfold FiniteMultigraph.stateSum NegamiData.stateSum pathStateSum
  change (∑ S : Finset (Fin 2),
      t ^ examplePathGraph.omega S * x ^ S.card *
        y ^ (Nat.card (Fin 2) - S.card)) =
    ∑ S : Finset (Fin 2),
      t ^ pathComponentCount S * x ^ S.card * y ^ (2 - S.card)
  apply Finset.sum_congr rfl
  intro S _
  rw [examplePathGraph_omega]
  simp only [Nat.card_fin]

/-- The finite component-count sum for the parallel graph is its actual graph
state sum. -/
theorem exampleParallelGraph_stateSum {R : Type*} [CommRing R]
    (t x y : R) :
    exampleParallelGraph.stateSum t x y = parallelStateSum t x y := by
  classical
  unfold FiniteMultigraph.stateSum NegamiData.stateSum parallelStateSum
  change (∑ S : Finset (Fin 2),
      t ^ exampleParallelGraph.omega S * x ^ S.card *
        y ^ (Nat.card (Fin 2) - S.card)) =
    ∑ S : Finset (Fin 2),
      t ^ parallelComponentCount S * x ^ S.card * y ^ (2 - S.card)
  apply Finset.sum_congr rfl
  intro S _
  rw [exampleParallelGraph_omega]
  simp only [Nat.card_fin]

/-- The sixteen-state component-count sum is the state sum of the actual
cyclically labelled graph. -/
theorem exampleCycleFourGraph_stateSum {R : Type*} [CommRing R]
    (t x y : R) :
    exampleCycleFourGraph.stateSum t x y = cycleFourStateSum t x y := by
  classical
  unfold FiniteMultigraph.stateSum NegamiData.stateSum cycleFourStateSum
  change (∑ S : Finset (Fin 4),
      t ^ exampleCycleFourGraph.omega S * x ^ S.card *
        y ^ (Nat.card (Fin 4) - S.card)) =
    ∑ S : Finset (Fin 4),
      t ^ cycleFourComponentCount S * x ^ S.card * y ^ (4 - S.card)
  apply Finset.sum_congr rfl
  intro S _
  rw [exampleCycleFourGraph_omega]
  simp only [Nat.card_fin]

/-! ## The endpoint quotient is the parallel-edge graph -/

/-- Component label for the vertex quotient identifying path endpoints. -/
def examplePathQuotientColor : Fin 3 → Fin 2 := ![0, 1, 0]

/-- The generated endpoint-identification relation has exactly the two fibers
of `examplePathQuotientColor`. -/
theorem examplePathQuotient_rel_iff_color_eq (u v : Fin 3) :
    examplePathOverBoundary.toBoundaryMultigraph.boundaryQuotientSetoid
        connectedTwoPartition u v ↔
      examplePathQuotientColor u = examplePathQuotientColor v := by
  constructor
  · intro h
    change Relation.EqvGen
      (examplePathOverBoundary.toBoundaryMultigraph.boundaryIdentification
        connectedTwoPartition) u v at h
    induction h with
    | rel a b hab =>
        rcases hab with ⟨i, j, hi, hj, _⟩
        subst a
        subst b
        fin_cases i <;> fin_cases j <;> rfl
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    have huv : u = v ∨
        (u = (0 : Fin 3) ∧ v = (2 : Fin 3)) ∨
        (u = (2 : Fin 3) ∧ v = (0 : Fin 3)) := by
      fin_cases u <;> fin_cases v <;>
        simp_all [examplePathQuotientColor]
    rcases huv with huv | huv | huv
    · subst v
      exact Relation.EqvGen.refl u
    · rcases huv with ⟨rfl, rfl⟩
      apply Relation.EqvGen.rel
      exact ⟨0, 1, rfl, rfl, connectedTwoPartition_rel 0 1⟩
    · rcases huv with ⟨rfl, rfl⟩
      apply Relation.EqvGen.rel
      exact ⟨1, 0, rfl, rfl, connectedTwoPartition_rel 1 0⟩

/-- The actual quotient vertex type is canonically equivalent to the two
vertices of the parallel graph. -/
noncomputable def examplePathQuotientVertexEquiv :
    examplePathQuotient.Vertex ≃ Fin 2 :=
  Equiv.ofBijective
    (Quotient.lift examplePathQuotientColor (fun u v huv =>
      (examplePathQuotient_rel_iff_color_eq u v).mp huv)) ⟨by
      intro a b hab
      induction a using Quotient.inductionOn with
      | _ u =>
        induction b using Quotient.inductionOn with
        | _ v =>
          apply Quotient.sound
          exact (examplePathQuotient_rel_iff_color_eq u v).mpr hab, by
      intro c
      fin_cases c
      · exact ⟨examplePathOverBoundary.toBoundaryMultigraph.boundaryQuotientVertex
          connectedTwoPartition (0 : Fin 3), rfl⟩
      · exact ⟨examplePathOverBoundary.toBoundaryMultigraph.boundaryQuotientVertex
          connectedTwoPartition (1 : Fin 3), rfl⟩⟩

@[simp] theorem examplePathQuotientVertexEquiv_mk (v : Fin 3) :
    examplePathQuotientVertexEquiv
      (examplePathOverBoundary.toBoundaryMultigraph.boundaryQuotientVertex
        connectedTwoPartition v) = examplePathQuotientColor v :=
  rfl

/-- The path endpoint quotient is isomorphic, including its edge labels and
unordered endpoints, to the explicit parallel-edge multigraph. -/
noncomputable def examplePathQuotientIso :
    FiniteMultigraph.Iso examplePathQuotient exampleParallelGraph where
  vertexEquiv := examplePathQuotientVertexEquiv
  edgeEquiv := Equiv.refl _
  map_ends e := by
    change exampleParallelGraph.ends e =
      Sym2.map examplePathQuotientVertexEquiv
        (Sym2.map
          (examplePathOverBoundary.toBoundaryMultigraph.boundaryQuotientVertex
            connectedTwoPartition) (examplePathGraph.ends e))
    rw [Sym2.map_map]
    have hcomp : examplePathQuotientVertexEquiv ∘
        (examplePathOverBoundary.toBoundaryMultigraph.boundaryQuotientVertex
          connectedTwoPartition) = examplePathQuotientColor := by
      funext v
      exact examplePathQuotientVertexEquiv_mk v
    rw [hcomp]
    fin_cases e
    · change s((0 : Fin 2), (1 : Fin 2)) = s(0, 1)
      rfl
    · change s((0 : Fin 2), (1 : Fin 2)) = s(1, 0)
      exact Sym2.eq_swap

/-- The actual endpoint quotient state sum is the finite parallel-edge sum. -/
theorem examplePathQuotient_stateSum {R : Type*} [CommRing R]
    (t x y : R) :
    examplePathQuotient.stateSum t x y = parallelStateSum t x y := by
  rw [examplePathQuotientIso.stateSum_eq]
  exact exampleParallelGraph_stateSum t x y

/-! ## The glued graph is the four-cycle -/

/-- Component label on the two disjoint path vertex sets before gluing. -/
def exampleGluedCycleFourColor : Fin 3 ⊕ Fin 3 → Fin 4
  | Sum.inl v => (![0, 1, 2] : Fin 3 → Fin 4) v
  | Sum.inr v => (![0, 3, 2] : Fin 3 → Fin 4) v

@[simp] theorem exampleMatchingPartition_rel (i j : Fin 2 ⊕ Fin 2) :
    (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
      examplePathOverBoundary.toBoundaryMultigraph
        (Equiv.refl (Fin 2))).toSetoid i j ↔
      Sum.elim id id i = Sum.elim id id j := by
  change decide
    (Sum.elim id (Equiv.refl (Fin 2)).symm i =
      Sum.elim id (Equiv.refl (Fin 2)).symm j) = true ↔ _
  simp

/-- Both copies of a boundary label receive the same future cycle vertex. -/
theorem exampleGluedCycleFourColor_boundary (i : Fin 2 ⊕ Fin 2) :
    exampleGluedCycleFourColor
        ((examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
          examplePathOverBoundary.toBoundaryMultigraph).boundaryEmbedding i) =
      (![0, 2] : Fin 2 → Fin 4) (Sum.elim id id i) := by
  cases i with
  | inl i => fin_cases i <;> rfl
  | inr i => fin_cases i <;> rfl

/-- The vertex relation used in the actual gluing has exactly the four fibers
of `exampleGluedCycleFourColor`. -/
theorem exampleGluedCycleFour_rel_iff_color_eq (u v : Fin 3 ⊕ Fin 3) :
    (examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
      examplePathOverBoundary.toBoundaryMultigraph).boundaryQuotientSetoid
        (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
          examplePathOverBoundary.toBoundaryMultigraph (Equiv.refl (Fin 2))) u v ↔
      exampleGluedCycleFourColor u = exampleGluedCycleFourColor v := by
  constructor
  · intro h
    change Relation.EqvGen
      ((examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
        examplePathOverBoundary.toBoundaryMultigraph).boundaryIdentification
          (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
            examplePathOverBoundary.toBoundaryMultigraph
              (Equiv.refl (Fin 2)))) u v at h
    induction h with
    | rel a b hab =>
        rcases hab with ⟨i, j, hi, hj, hij⟩
        subst a
        subst b
        have hij' : Sum.elim id id i = Sum.elim id id j :=
          (exampleMatchingPartition_rel i j).mp hij
        rw [exampleGluedCycleFourColor_boundary,
          exampleGluedCycleFourColor_boundary, hij']
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    have huv : u = v ∨
        (u = Sum.inl (0 : Fin 3) ∧ v = Sum.inr (0 : Fin 3)) ∨
        (u = Sum.inr (0 : Fin 3) ∧ v = Sum.inl (0 : Fin 3)) ∨
        (u = Sum.inl (2 : Fin 3) ∧ v = Sum.inr (2 : Fin 3)) ∨
        (u = Sum.inr (2 : Fin 3) ∧ v = Sum.inl (2 : Fin 3)) := by
      cases u with
      | inl u =>
          cases v with
          | inl v =>
              fin_cases u <;> fin_cases v <;>
                simp_all [exampleGluedCycleFourColor]
          | inr v =>
              fin_cases u <;> fin_cases v <;>
                simp_all [exampleGluedCycleFourColor]
      | inr u =>
          cases v with
          | inl v =>
              fin_cases u <;> fin_cases v <;>
                simp_all [exampleGluedCycleFourColor]
          | inr v =>
              fin_cases u <;> fin_cases v <;>
                simp_all [exampleGluedCycleFourColor]
    rcases huv with huv | huv | huv | huv | huv
    · subst v
      exact Relation.EqvGen.refl u
    · rcases huv with ⟨rfl, rfl⟩
      apply Relation.EqvGen.rel
      refine ⟨Sum.inl 0, Sum.inr 0, rfl, rfl, ?_⟩
      exact (exampleMatchingPartition_rel _ _).mpr rfl
    · rcases huv with ⟨rfl, rfl⟩
      apply Relation.EqvGen.rel
      refine ⟨Sum.inr 0, Sum.inl 0, rfl, rfl, ?_⟩
      exact (exampleMatchingPartition_rel _ _).mpr rfl
    · rcases huv with ⟨rfl, rfl⟩
      apply Relation.EqvGen.rel
      refine ⟨Sum.inl 1, Sum.inr 1, rfl, rfl, ?_⟩
      exact (exampleMatchingPartition_rel _ _).mpr rfl
    · rcases huv with ⟨rfl, rfl⟩
      apply Relation.EqvGen.rel
      refine ⟨Sum.inr 1, Sum.inl 1, rfl, rfl, ?_⟩
      exact (exampleMatchingPartition_rel _ _).mpr rfl

/-- The vertex quotient in the glued graph is canonically the four-element
cycle vertex type. -/
noncomputable def exampleGluedCycleFourVertexEquiv :
    exampleGluedCycleFour.Vertex ≃ Fin 4 :=
  Equiv.ofBijective
    (Quotient.lift exampleGluedCycleFourColor (fun u v huv =>
      (exampleGluedCycleFour_rel_iff_color_eq u v).mp huv)) ⟨by
      intro a b hab
      induction a using Quotient.inductionOn with
      | _ u =>
        induction b using Quotient.inductionOn with
        | _ v =>
          apply Quotient.sound
          exact (exampleGluedCycleFour_rel_iff_color_eq u v).mpr hab, by
      intro c
      fin_cases c
      · exact ⟨(examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
          examplePathOverBoundary.toBoundaryMultigraph).boundaryQuotientVertex
            (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
              examplePathOverBoundary.toBoundaryMultigraph
                (Equiv.refl (Fin 2)))
            (Sum.inl (0 : Fin 3)), rfl⟩
      · exact ⟨(examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
          examplePathOverBoundary.toBoundaryMultigraph).boundaryQuotientVertex
            (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
              examplePathOverBoundary.toBoundaryMultigraph
                (Equiv.refl (Fin 2)))
            (Sum.inl (1 : Fin 3)), rfl⟩
      · exact ⟨(examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
          examplePathOverBoundary.toBoundaryMultigraph).boundaryQuotientVertex
            (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
              examplePathOverBoundary.toBoundaryMultigraph
                (Equiv.refl (Fin 2)))
            (Sum.inl (2 : Fin 3)), rfl⟩
      · exact ⟨(examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
          examplePathOverBoundary.toBoundaryMultigraph).boundaryQuotientVertex
            (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
              examplePathOverBoundary.toBoundaryMultigraph
                (Equiv.refl (Fin 2)))
            (Sum.inr (1 : Fin 3)), rfl⟩⟩

@[simp] theorem exampleGluedCycleFourVertexEquiv_mk (v : Fin 3 ⊕ Fin 3) :
    exampleGluedCycleFourVertexEquiv
      ((examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
        examplePathOverBoundary.toBoundaryMultigraph).boundaryQuotientVertex
          (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
            examplePathOverBoundary.toBoundaryMultigraph
              (Equiv.refl (Fin 2))) v) =
        exampleGluedCycleFourColor v :=
  rfl

/-- Edge labels on the two path copies, ordered cyclically. -/
def exampleGluedCycleFourEdgeEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun
    | Sum.inl e => (![0, 1] : Fin 2 → Fin 4) e
    | Sum.inr e => (![3, 2] : Fin 2 → Fin 4) e
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 0]
  left_inv e := by
    cases e with
    | inl e => fin_cases e <;> rfl
    | inr e => fin_cases e <;> rfl
  right_inv e := by
    fin_cases e <;> rfl

/-- The actual pushout-style gluing of the two paths is isomorphic, on both
vertices and labelled edges, to the explicit four-cycle. -/
noncomputable def exampleGluedCycleFourIso :
    FiniteMultigraph.Iso exampleGluedCycleFour exampleCycleFourGraph where
  vertexEquiv := exampleGluedCycleFourVertexEquiv
  edgeEquiv := exampleGluedCycleFourEdgeEquiv
  map_ends e := by
    change exampleCycleFourGraph.ends (exampleGluedCycleFourEdgeEquiv e) =
      Sym2.map exampleGluedCycleFourVertexEquiv
        (Sym2.map
          ((examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
            examplePathOverBoundary.toBoundaryMultigraph).boundaryQuotientVertex
              (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
                examplePathOverBoundary.toBoundaryMultigraph
                  (Equiv.refl (Fin 2))))
          ((examplePathGraph.disjointUnion examplePathGraph).ends e))
    rw [Sym2.map_map]
    have hcomp : exampleGluedCycleFourVertexEquiv ∘
        ((examplePathOverBoundary.toBoundaryMultigraph.disjointBoundary
          examplePathOverBoundary.toBoundaryMultigraph).boundaryQuotientVertex
            (examplePathOverBoundary.toBoundaryMultigraph.matchingPartition
              examplePathOverBoundary.toBoundaryMultigraph
                (Equiv.refl (Fin 2)))) = exampleGluedCycleFourColor := by
      funext v
      exact exampleGluedCycleFourVertexEquiv_mk v
    rw [hcomp]
    cases e with
    | inl e =>
        fin_cases e
        · change s((0 : Fin 4), (1 : Fin 4)) = s(0, 1)
          rfl
        · change s((1 : Fin 4), (2 : Fin 4)) = s(1, 2)
          rfl
    | inr e =>
        fin_cases e
        · change s((3 : Fin 4), (0 : Fin 4)) = s(0, 3)
          exact Sym2.eq_swap
        · change s((2 : Fin 4), (3 : Fin 4)) = s(3, 2)
          exact Sym2.eq_swap

/-- The actual glued graph has exactly the previously enumerated sixteen-state
sum, without any algebraic restriction on the variables. -/
theorem exampleGluedCycleFour_stateSum {R : Type*} [CommRing R]
    (t x y : R) :
    exampleGluedCycleFour.stateSum t x y = cycleFourStateSum t x y := by
  rw [exampleGluedCycleFourIso.stateSum_eq]
  exact exampleCycleFourGraph_stateSum t x y

/-- Example 6.4 as an actual-graph specialization of the concrete
two-boundary theorem.  Every term is the state sum of the displayed path,
endpoint quotient, or four-cycle graph. -/
theorem exampleCycleFour_actual_graph_splitting
    {F : Type*} [Field F] (t x y : F) (ht : t ≠ 0) (ht1 : t ≠ 1) :
    exampleCycleFourGraph.stateSum t x y =
      examplePathQuotient.stateSum t x y *
          examplePathQuotient.stateSum t x y / (t - 1) -
        examplePathQuotient.stateSum t x y *
          examplePathGraph.stateSum t x y / (t * (t - 1)) -
        examplePathGraph.stateSum t x y *
          examplePathQuotient.stateSum t x y / (t * (t - 1)) +
        examplePathGraph.stateSum t x y *
          examplePathGraph.stateSum t x y / (t * (t - 1)) := by
  rw [← exampleGluedCycleFourIso.stateSum_eq]
  exact examplePathOverBoundary.concrete_twoBoundary_four_term
    examplePathOverBoundary t x y ht ht1

/-- Rewriting the actual-graph theorem by the three exact state-sum bridges
recovers the component-count identity of Example 6.4. -/
theorem exampleCycleFour_actual_graph_splitting_counts
    {F : Type*} [Field F] (t x y : F) (ht : t ≠ 0) (ht1 : t ≠ 1) :
    cycleFourStateSum t x y =
      parallelStateSum t x y * parallelStateSum t x y / (t - 1) -
        parallelStateSum t x y * pathStateSum t x y / (t * (t - 1)) -
        pathStateSum t x y * parallelStateSum t x y / (t * (t - 1)) +
        pathStateSum t x y * pathStateSum t x y / (t * (t - 1)) := by
  rw [← exampleCycleFourGraph_stateSum,
    exampleCycleFour_actual_graph_splitting t x y ht ht1,
    examplePathQuotient_stateSum, examplePathGraph_stateSum]

end LeanCo.Negami
