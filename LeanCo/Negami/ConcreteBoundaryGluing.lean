import LeanCo.Negami.ConcreteBoundaryQuotient
import Mathlib.Data.Finset.Sum
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! Concrete gluing as a boundary quotient of a disjoint union. -/

namespace LeanCo.Negami

theorem sym2_map_inl_injective {A B : Type*} :
    Function.Injective (Sym2.map (Sum.inl : A → A ⊕ B)) := by
  intro z w h
  induction z using Sym2.inductionOn with
  | _ a b =>
    induction w using Sym2.inductionOn with
    | _ c d => simpa [Sym2.map_mk] using h

theorem sym2_map_inr_injective {A B : Type*} :
    Function.Injective (Sym2.map (Sum.inr : B → A ⊕ B)) := by
  intro z w h
  induction z using Sym2.inductionOn with
  | _ a b =>
    induction w using Sym2.inductionOn with
    | _ c d => simpa [Sym2.map_mk] using h

theorem sym2_map_inl_ne_mixed {A B : Type*} (z : Sym2 A) (a : A) (b : B) :
    Sym2.map (Sum.inl : A → A ⊕ B) z ≠ s(Sum.inl a, Sum.inr b) := by
  induction z using Sym2.inductionOn with
  | _ x y => simp [Sym2.map_mk]

theorem sym2_map_inr_ne_mixed {A B : Type*} (z : Sym2 B) (a : A) (b : B) :
    Sym2.map (Sum.inr : B → A ⊕ B) z ≠ s(Sum.inl a, Sum.inr b) := by
  induction z using Sym2.inductionOn with
  | _ x y => simp [Sym2.map_mk]

theorem sym2_map_inr_ne_inlPair {A B : Type*} (z : Sym2 B) (a b : A) :
    Sym2.map (Sum.inr : B → A ⊕ B) z ≠ s(Sum.inl a, Sum.inl b) := by
  induction z using Sym2.inductionOn with
  | _ x y => simp [Sym2.map_mk]

theorem sym2_map_inl_ne_inrPair {A B : Type*} (z : Sym2 A) (a b : B) :
    Sym2.map (Sum.inl : A → A ⊕ B) z ≠ s(Sum.inr a, Sum.inr b) := by
  induction z using Sym2.inductionOn with
  | _ x y => simp [Sym2.map_mk]

theorem reachable_sum_inl_iff {A B : Type*} {G : SimpleGraph A}
    {H : SimpleGraph B} {u v : A} :
    (G ⊕g H).Reachable (Sum.inl u) (Sum.inl v) ↔ G.Reachable u v := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    let r : (A ⊕ B) → (A ⊕ B) → Prop
      | Sum.inl a, Sum.inl b => G.Reachable a b
      | Sum.inr a, Sum.inr b => H.Reachable a b
      | _, _ => False
    have hr : Equivalence r := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        cases x <;> exact SimpleGraph.Reachable.refl _
      · intro x y hxy
        cases x <;> cases y <;> simp_all [r, SimpleGraph.reachable_comm]
      · intro x y z hxy hyz
        cases x <;> cases y <;> cases z <;> simp_all [r]
        · exact hxy.trans hyz
        · exact hxy.trans hyz
    have hadj : (G ⊕g H).Adj ≤ r := by
      intro x y hxy
      cases x <;> cases y <;> simp_all [r, SimpleGraph.Adj.reachable]
    exact Relation.reflTransGen_of_equivalence (r := r)
      (r' := (G ⊕g H).Adj) hr hadj h
  · intro h
    exact h.map SimpleGraph.Embedding.sumInl.toHom

theorem reachable_sum_inr_iff {A B : Type*} {G : SimpleGraph A}
    {H : SimpleGraph B} {u v : B} :
    (G ⊕g H).Reachable (Sum.inr u) (Sum.inr v) ↔ H.Reachable u v := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    let r : (A ⊕ B) → (A ⊕ B) → Prop
      | Sum.inl a, Sum.inl b => G.Reachable a b
      | Sum.inr a, Sum.inr b => H.Reachable a b
      | _, _ => False
    have hr : Equivalence r := by
      refine ⟨?_, ?_, ?_⟩
      · intro x
        cases x <;> exact SimpleGraph.Reachable.refl _
      · intro x y hxy
        cases x <;> cases y <;> simp_all [r, SimpleGraph.reachable_comm]
      · intro x y z hxy hyz
        cases x <;> cases y <;> cases z <;> simp_all [r]
        · exact hxy.trans hyz
        · exact hxy.trans hyz
    have hadj : (G ⊕g H).Adj ≤ r := by
      intro x y hxy
      cases x <;> cases y <;> simp_all [r, SimpleGraph.Adj.reachable]
    exact Relation.reflTransGen_of_equivalence (r := r)
      (r' := (G ⊕g H).Adj) hr hadj h
  · intro h
    exact h.map SimpleGraph.Embedding.sumInr.toHom

noncomputable def connectedComponentSumEquiv {A B : Type*}
    (G : SimpleGraph A) (H : SimpleGraph B) :
    (G ⊕g H).ConnectedComponent ≃ G.ConnectedComponent ⊕ H.ConnectedComponent where
  toFun := Quot.lift (fun x ↦ match x with
    | Sum.inl a => Sum.inl (G.connectedComponentMk a)
    | Sum.inr b => Sum.inr (H.connectedComponentMk b)) (by
      intro x y h
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              exact congrArg Sum.inl (SimpleGraph.ConnectedComponent.sound
                ((reachable_sum_inl_iff).mp
                  (show (G ⊕g H).Reachable (Sum.inl x) (Sum.inl y) from h)))
          | inr y =>
              exact (SimpleGraph.not_reachable_sum_inl_inr _ _
                (show (G ⊕g H).Reachable (Sum.inl x) (Sum.inr y) from h)).elim
      | inr x =>
          cases y with
          | inl y =>
              exact (SimpleGraph.not_reachable_sum_inl_inr _ _
                (show (G ⊕g H).Reachable (Sum.inl y) (Sum.inr x) from h.symm)).elim
          | inr y =>
              exact congrArg Sum.inr (SimpleGraph.ConnectedComponent.sound
                ((reachable_sum_inr_iff).mp
                  (show (G ⊕g H).Reachable (Sum.inr x) (Sum.inr y) from h))))
  invFun
    | Sum.inl c => Quot.map Sum.inl (fun _ _ h ↦
        (reachable_sum_inl_iff).mpr h) c
    | Sum.inr c => Quot.map Sum.inr (fun _ _ h ↦
        (reachable_sum_inr_iff).mpr h) c
  left_inv := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ x => cases x <;> rfl
  right_inv := by
    intro c
    cases c with
    | inl c => induction c using SimpleGraph.ConnectedComponent.ind with | _ x => rfl
    | inr c => induction c using SimpleGraph.ConnectedComponent.ind with | _ x => rfl

namespace FiniteMultigraph

/-- Label-preserving disjoint union of finite multigraphs. -/
abbrev disjointUnion (K H : FiniteMultigraph) : FiniteMultigraph where
  Vertex := K.Vertex ⊕ H.Vertex
  Edge := K.Edge ⊕ H.Edge
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  ends
    | Sum.inl e => Sym2.map Sum.inl (K.ends e)
    | Sum.inr e => Sym2.map Sum.inr (H.ends e)

end FiniteMultigraph

namespace BoundaryMultigraph

variable (K H : BoundaryMultigraph)

/-- Disjoint union with both boundary copies retained as distinct labels. -/
abbrev disjointBoundary : BoundaryMultigraph where
  graph := K.graph.disjointUnion H.graph
  Boundary := K.Boundary ⊕ H.Boundary
  boundaryFintype := inferInstance
  boundaryDecidableEq := inferInstance
  boundaryEmbedding :=
    ⟨Sum.elim (Sum.inl ∘ K.boundaryEmbedding)
      (Sum.inr ∘ H.boundaryEmbedding), by
        intro x y h
        cases x with
        | inl x =>
            cases y with
            | inl y =>
                change Sum.inl (K.boundaryEmbedding x) =
                  Sum.inl (K.boundaryEmbedding y) at h
                exact congrArg Sum.inl (K.boundaryEmbedding.injective
                  (Sum.inl.inj h))
            | inr y =>
                change Sum.inl (K.boundaryEmbedding x) =
                  Sum.inr (H.boundaryEmbedding y) at h
                exact False.elim (Sum.inl_ne_inr h)
        | inr x =>
            cases y with
            | inl y =>
                change Sum.inr (H.boundaryEmbedding x) =
                  Sum.inl (K.boundaryEmbedding y) at h
                exact False.elim (Sum.inr_ne_inl h)
            | inr y =>
                change Sum.inr (H.boundaryEmbedding x) =
                  Sum.inr (H.boundaryEmbedding y) at h
                exact congrArg Sum.inr (H.boundaryEmbedding.injective
                  (Sum.inr.inj h))⟩

/-- Partition pairing each left boundary label with its corresponding right
label under `e`. -/
def matchingPartition (e : K.Boundary ≃ H.Boundary) :
    FinitePartition (K.Boundary ⊕ H.Boundary) :=
  ⟨fun x y ↦ decide
      (Sum.elim id e.symm x = Sum.elim id e.symm y), by
    constructor
    · intro x
      simp
    constructor
    · intro x y
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact eq_comm
    · intro x y z hxy hyz
      simp only [decide_eq_true_eq] at hxy hyz ⊢
      exact hxy.trans hyz⟩

/-- The pushout-style graph obtained by identifying corresponding boundary
vertices in the disjoint union. -/
noncomputable abbrev gluedGraph (e : K.Boundary ≃ H.Boundary) :
    FiniteMultigraph :=
  (K.disjointBoundary H).quotientGraph (K.matchingPartition H e)

/-- States of a glued graph split uniquely into left and right edge states. -/
def gluedStateEquiv (e : K.Boundary ≃ H.Boundary) :
    Finset (K.gluedGraph H e).Edge ≃ Finset K.graph.Edge × Finset H.graph.Edge :=
  Finset.sumEquiv.toEquiv

theorem gluedStateEquiv_selected_card (e : K.Boundary ≃ H.Boundary)
    (S : Finset (K.gluedGraph H e).Edge) :
    S.card = (K.gluedStateEquiv H e S).1.card +
      (K.gluedStateEquiv H e S).2.card := by
  change S.card = S.toLeft.card + S.toRight.card
  exact (Finset.card_toLeft_add_card_toRight).symm

theorem gluedGraph_edge_card (e : K.Boundary ≃ H.Boundary) :
    Nat.card (K.gluedGraph H e).Edge =
      Nat.card K.graph.Edge + Nat.card H.graph.Edge := by
  change Nat.card (K.graph.Edge ⊕ H.graph.Edge) =
    Nat.card K.graph.Edge + Nat.card H.graph.Edge
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_sum]

/-- A selected state in the multigraph disjoint union is exactly the simple
graph disjoint sum of the two restricted selected states. -/
theorem spanningGraph_disjointUnion
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) :
    (K.graph.disjointUnion H.graph).spanningGraph S =
      K.graph.spanningGraph S.toLeft ⊕g H.graph.spanningGraph S.toRight := by
  classical
  ext u v
  cases u with
  | inl u =>
      cases v with
      | inl v =>
          simp only [FiniteMultigraph.stateGraph,
            FiniteMultigraph.disjointUnion, SimpleGraph.sum]
          rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
          constructor
          · rintro ⟨hm, hn⟩
            rcases Finset.mem_image.mp hm with ⟨a, ha, heq⟩
            cases a with
            | inl a =>
                change Sum.inl a ∈ S at ha
                refine ⟨Finset.mem_image.mpr ⟨a, by simpa, ?_⟩, ?_⟩
                · apply sym2_map_inl_injective
                  simpa [FiniteMultigraph.disjointUnion, Sym2.map_mk] using heq
                · exact fun h ↦ hn (congrArg Sum.inl h)
            | inr a =>
                exact False.elim ((sym2_map_inr_ne_inlPair (H.graph.ends a) u v)
                  (by simpa [FiniteMultigraph.disjointUnion, Sym2.map_mk] using heq))
          · rintro ⟨hm, hn⟩
            rcases Finset.mem_image.mp hm with ⟨a, ha, heq⟩
            refine ⟨Finset.mem_image.mpr ⟨Sum.inl a, ?_, ?_⟩, ?_⟩
            · simpa using ha
            · change Sym2.map Sum.inl (K.graph.ends a) = _
              rw [heq, Sym2.map_mk]
            · exact fun h ↦ hn (Sum.inl.inj h)
      | inr v =>
          simp only [FiniteMultigraph.stateGraph,
            FiniteMultigraph.disjointUnion, SimpleGraph.sum]
          rw [SimpleGraph.fromEdgeSet_adj]
          constructor
          · rintro ⟨hm, hn⟩
            rcases Finset.mem_image.mp hm with ⟨a, ha, heq⟩
            cases a with
            | inl a => exact False.elim ((sym2_map_inl_ne_mixed
                (K.graph.ends a) u v)
                (by simpa [FiniteMultigraph.disjointUnion] using heq))
            | inr a => exact False.elim ((sym2_map_inr_ne_mixed
                (H.graph.ends a) u v)
                (by simpa [FiniteMultigraph.disjointUnion] using heq))
          · simp
  | inr u =>
      cases v with
      | inl v =>
          simp only [FiniteMultigraph.stateGraph,
            FiniteMultigraph.disjointUnion, SimpleGraph.sum]
          rw [SimpleGraph.fromEdgeSet_adj]
          constructor
          · rintro ⟨hm, hn⟩
            rcases Finset.mem_image.mp hm with ⟨a, ha, heq⟩
            cases a with
            | inl a =>
                have heq' : Sym2.map Sum.inl (K.graph.ends a) =
                    s(Sum.inl v, Sum.inr u) := by
                  change Sym2.map Sum.inl (K.graph.ends a) = _ at heq
                  exact heq.trans Sym2.eq_swap
                exact False.elim ((sym2_map_inl_ne_mixed
                  (K.graph.ends a) v u) heq')
            | inr a =>
                have heq' : Sym2.map Sum.inr (H.graph.ends a) =
                    s(Sum.inl v, Sum.inr u) := by
                  change Sym2.map Sum.inr (H.graph.ends a) = _ at heq
                  exact heq.trans Sym2.eq_swap
                exact False.elim ((sym2_map_inr_ne_mixed
                  (H.graph.ends a) v u) heq')
          · simp
      | inr v =>
          simp only [FiniteMultigraph.stateGraph,
            FiniteMultigraph.disjointUnion, SimpleGraph.sum]
          rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
          constructor
          · rintro ⟨hm, hn⟩
            rcases Finset.mem_image.mp hm with ⟨a, ha, heq⟩
            cases a with
            | inl a =>
                exact False.elim ((sym2_map_inl_ne_inrPair
                  (K.graph.ends a) u v)
                  (by simpa [FiniteMultigraph.disjointUnion] using heq))
            | inr a =>
                change Sum.inr a ∈ S at ha
                refine ⟨Finset.mem_image.mpr ⟨a, by simpa, ?_⟩, ?_⟩
                · apply sym2_map_inr_injective
                  simpa [FiniteMultigraph.disjointUnion, Sym2.map_mk] using heq
                · exact fun h ↦ hn (congrArg Sum.inr h)
          · rintro ⟨hm, hn⟩
            rcases Finset.mem_image.mp hm with ⟨a, ha, heq⟩
            refine ⟨Finset.mem_image.mpr ⟨Sum.inr a, ?_, ?_⟩, ?_⟩
            · simpa using ha
            · change Sym2.map Sum.inr (H.graph.ends a) = _
              rw [heq, Sym2.map_mk]
            · exact fun h ↦ hn (Sum.inr.inj h)

theorem disjointBoundaryPartition_inl
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) (i j : K.Boundary) :
    ((K.disjointBoundary H).boundaryPartition S).toSetoid
        (Sum.inl i) (Sum.inl j) ↔
      (K.boundaryPartition S.toLeft).toSetoid i j := by
  change ((K.disjointBoundary H).boundaryPartition S).1
      (Sum.inl i) (Sum.inl j) = true ↔
    (K.boundaryPartition S.toLeft).1 i j = true
  rw [(K.disjointBoundary H).boundaryPartition_rel,
    K.boundaryPartition_rel]
  rw [K.spanningGraph_disjointUnion H S]
  exact reachable_sum_inl_iff

theorem disjointBoundaryPartition_inr
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) (i j : H.Boundary) :
    ((K.disjointBoundary H).boundaryPartition S).toSetoid
        (Sum.inr i) (Sum.inr j) ↔
      (H.boundaryPartition S.toRight).toSetoid i j := by
  change ((K.disjointBoundary H).boundaryPartition S).1
      (Sum.inr i) (Sum.inr j) = true ↔
    (H.boundaryPartition S.toRight).1 i j = true
  rw [(K.disjointBoundary H).boundaryPartition_rel,
    H.boundaryPartition_rel]
  rw [K.spanningGraph_disjointUnion H S]
  exact reachable_sum_inr_iff

theorem disjointBoundaryPartition_not_cross
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) (i : K.Boundary)
    (j : H.Boundary) :
    ¬ ((K.disjointBoundary H).boundaryPartition S).toSetoid
      (Sum.inl i) (Sum.inr j) := by
  change ¬ ((K.disjointBoundary H).boundaryPartition S).1
    (Sum.inl i) (Sum.inr j) = true
  rw [(K.disjointBoundary H).boundaryPartition_rel]
  rw [K.spanningGraph_disjointUnion H S]
  exact SimpleGraph.not_reachable_sum_inl_inr _ _

theorem disjointUnion_components
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) :
    (K.graph.disjointUnion H.graph).components S =
      K.graph.components S.toLeft + H.graph.components S.toRight := by
  calc
    (K.graph.disjointUnion H.graph).components S =
        Nat.card ((K.graph.disjointUnion H.graph).spanningGraph S).ConnectedComponent := rfl
    _ = Nat.card
        ((K.graph.spanningGraph S.toLeft ⊕g
          H.graph.spanningGraph S.toRight).ConnectedComponent) := by
      rw [K.spanningGraph_disjointUnion H S]
    _ = Nat.card (K.graph.spanningGraph S.toLeft).ConnectedComponent +
        Nat.card (H.graph.spanningGraph S.toRight).ConnectedComponent := by
      have h := Nat.card_congr (connectedComponentSumEquiv
        (K.graph.spanningGraph S.toLeft) (H.graph.spanningGraph S.toRight))
      simpa only [Nat.card_sum] using h
    _ = K.graph.components S.toLeft + H.graph.components S.toRight := rfl

/-- Boundary blocks in a disjoint state are the disjoint union of its left
and right boundary blocks. -/
noncomputable def disjointBoundaryBlockEquiv
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) :
    Quotient ((K.disjointBoundary H).boundaryPartition S).toSetoid ≃
      Quotient (K.boundaryPartition S.toLeft).toSetoid ⊕
        Quotient (H.boundaryPartition S.toRight).toSetoid where
  toFun := Quotient.lift (fun x ↦ match x with
    | Sum.inl i => Sum.inl (@Quotient.mk' _
        (K.boundaryPartition S.toLeft).toSetoid i)
    | Sum.inr j => Sum.inr (@Quotient.mk' _
        (H.boundaryPartition S.toRight).toSetoid j)) (by
      intro x y h
      cases x with
      | inl x =>
          cases y with
          | inl y => exact congrArg Sum.inl (Quotient.sound
              ((K.disjointBoundaryPartition_inl H S x y).mp h))
          | inr y => exact (K.disjointBoundaryPartition_not_cross H S x y h).elim
      | inr x =>
          cases y with
          | inl y => exact (K.disjointBoundaryPartition_not_cross H S y x
              (((K.disjointBoundary H).boundaryPartition S).toSetoid.symm h)).elim
          | inr y => exact congrArg Sum.inr (Quotient.sound
              ((K.disjointBoundaryPartition_inr H S x y).mp h)))
  invFun
    | Sum.inl q => Quotient.map Sum.inl (fun _ _ h ↦
        (K.disjointBoundaryPartition_inl H S _ _).mpr h) q
    | Sum.inr q => Quotient.map Sum.inr (fun _ _ h ↦
        (K.disjointBoundaryPartition_inr H S _ _).mpr h) q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => cases x <;> rfl
  right_inv := by
    intro q
    cases q with
    | inl q => induction q using Quotient.inductionOn with | _ x => rfl
    | inr q => induction q using Quotient.inductionOn with | _ x => rfl

theorem disjointBoundary_blocks
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) :
    FinitePartition.blocks ((K.disjointBoundary H).boundaryPartition S) =
      FinitePartition.blocks (K.boundaryPartition S.toLeft) +
        FinitePartition.blocks (H.boundaryPartition S.toRight) := by
  unfold FinitePartition.blocks
  have h := Nat.card_congr (K.disjointBoundaryBlockEquiv H S)
  simpa only [Nat.card_sum] using h

theorem disjointBoundary_internalComponents
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) :
    (K.disjointBoundary H).toBoundaryData.internalComponents S =
      K.toBoundaryData.internalComponents S.toLeft +
        H.toBoundaryData.internalComponents S.toRight := by
  unfold BoundaryData.internalComponents
  change (K.graph.disjointUnion H.graph).components S -
      FinitePartition.blocks ((K.disjointBoundary H).boundaryPartition S) =
    (K.graph.components S.toLeft -
      FinitePartition.blocks (K.boundaryPartition S.toLeft)) +
    (H.graph.components S.toRight -
      FinitePartition.blocks (H.boundaryPartition S.toRight))
  rw [K.disjointUnion_components H S, K.disjointBoundary_blocks H S]
  have hK := K.toBoundaryData.blocks_le_components S.toLeft
  have hH := H.toBoundaryData.blocks_le_components S.toRight
  change FinitePartition.blocks (K.boundaryPartition S.toLeft) ≤
    K.graph.components S.toLeft at hK
  change FinitePartition.blocks (H.boundaryPartition S.toRight) ≤
    H.graph.components S.toRight at hH
  omega

/-- Transport a partition along a boundary equivalence. -/
def pullPartition (e : K.Boundary ≃ H.Boundary)
    (σ : FinitePartition H.Boundary) : FinitePartition K.Boundary :=
  ⟨fun i j ↦ σ.1 (e i) (e j), by
    refine ⟨?_, ?_, ?_⟩
    · exact fun i ↦ σ.2.1 (e i)
    · exact fun i j ↦ σ.2.2.1 (e i) (e j)
    · exact fun i j k ↦ σ.2.2.2 (e i) (e j) (e k)⟩

theorem pullPartition_rel (e : K.Boundary ≃ H.Boundary)
    (σ : FinitePartition H.Boundary) (i j : K.Boundary) :
    (K.pullPartition H e σ).toSetoid i j ↔ σ.toSetoid (e i) (e j) :=
  Iff.rfl

/-- Collapse the doubled boundary to the common left-hand label set. -/
def collapseBoundary (e : K.Boundary ≃ H.Boundary) :
    K.Boundary ⊕ H.Boundary → K.Boundary :=
  Sum.elim id e.symm

theorem matchingPartition_rel_iff (e : K.Boundary ≃ H.Boundary)
    (x y : K.Boundary ⊕ H.Boundary) :
    (K.matchingPartition H e).toSetoid x y ↔
      K.collapseBoundary H e x = K.collapseBoundary H e y := by
  change decide (_ = _) = true ↔ _
  simp [collapseBoundary]

/-- The doubled boundary relation generated by state connectivity and matching
is precisely the ordinary join of the two transported state partitions. -/
theorem doubledJoin_rel_iff
    (e : K.Boundary ≃ H.Boundary)
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge))
    (x y : K.Boundary ⊕ H.Boundary) :
    (FinitePartition.join (K.matchingPartition H e)
        ((K.disjointBoundary H).boundaryPartition S)).toSetoid x y ↔
      (FinitePartition.join (K.boundaryPartition S.toLeft)
        (K.pullPartition H e (H.boundaryPartition S.toRight))).toSetoid
          (K.collapseBoundary H e x) (K.collapseBoundary H e y) := by
  classical
  rw [FinitePartition.join_rel, FinitePartition.join_rel]
  let π := K.boundaryPartition S.toLeft
  let σ := H.boundaryPartition S.toRight
  let τ := (K.disjointBoundary H).boundaryPartition S
  let c := K.collapseBoundary H e
  have hforward : ∀ {a b},
      Relation.EqvGen (fun p q ↦
        (K.matchingPartition H e).toSetoid p q ∨ τ.toSetoid p q) a b →
      Relation.EqvGen (fun i j ↦ π.toSetoid i j ∨
        (K.pullPartition H e σ).toSetoid i j) (c a) (c b) := by
    intro a b h
    induction h with
    | rel a b h =>
        rcases h with hm | ht
        · have heq := (K.matchingPartition_rel_iff H e a b).mp hm
          change Relation.EqvGen (fun i j ↦ π.toSetoid i j ∨
            (K.pullPartition H e σ).toSetoid i j)
            (K.collapseBoundary H e a) (K.collapseBoundary H e b)
          rw [heq]
          exact Relation.EqvGen.refl _
        · cases a with
          | inl a =>
              cases b with
              | inl b =>
                  exact Relation.EqvGen.rel _ _ (Or.inl
                    ((K.disjointBoundaryPartition_inl H S a b).mp ht))
              | inr b =>
                  exact (K.disjointBoundaryPartition_not_cross H S a b ht).elim
          | inr a =>
              cases b with
              | inl b =>
                  exact (K.disjointBoundaryPartition_not_cross H S b a
                    (τ.toSetoid.symm ht)).elim
              | inr b =>
                  apply Relation.EqvGen.rel _ _
                  right
                  change σ.toSetoid (e (e.symm a)) (e (e.symm b))
                  simpa using (K.disjointBoundaryPartition_inr H S a b).mp ht
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b d _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  constructor
  · exact hforward
  · intro h
    have hmatch : ∀ z : K.Boundary ⊕ H.Boundary,
        Relation.EqvGen (fun p q ↦
          (K.matchingPartition H e).toSetoid p q ∨ τ.toSetoid p q)
          z (Sum.inl (c z)) := by
      intro z
      apply Relation.EqvGen.rel
      left
      apply (K.matchingPartition_rel_iff H e _ _).mpr
      rfl
    have hlift : ∀ {a b : K.Boundary},
        Relation.EqvGen (fun i j ↦ π.toSetoid i j ∨
          (K.pullPartition H e σ).toSetoid i j) a b →
        Relation.EqvGen (fun p q ↦
          (K.matchingPartition H e).toSetoid p q ∨ τ.toSetoid p q)
          (Sum.inl a) (Sum.inl b) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
          rcases hab with hp | hs
          · exact Relation.EqvGen.rel _ _ (Or.inr
              ((K.disjointBoundaryPartition_inl H S a b).mpr hp))
          · apply Relation.EqvGen.trans _ (Sum.inr (e a)) _
            · exact Relation.EqvGen.rel _ _ (Or.inl
                ((K.matchingPartition_rel_iff H e _ _).mpr (by
                  simp [collapseBoundary])))
            · apply Relation.EqvGen.trans _ (Sum.inr (e b)) _
              · exact Relation.EqvGen.rel _ _ (Or.inr
                  ((K.disjointBoundaryPartition_inr H S (e a) (e b)).mpr hs))
              · exact Relation.EqvGen.rel _ _ (Or.inl
                  ((K.matchingPartition_rel_iff H e _ _).mpr (by
                    simp [collapseBoundary])))
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact ih.symm
      | trans a b d _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    exact Relation.EqvGen.trans x (Sum.inl (c x)) y (hmatch x)
      (Relation.EqvGen.trans _ (Sum.inl (c y)) _ (hlift h) (hmatch y).symm)

/-- Quotient equivalence implementing the identification of doubled joined
blocks with the usual join of the two transported boundary partitions. -/
noncomputable def doubledJoinQuotientEquiv
    (e : K.Boundary ≃ H.Boundary)
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) :
    Quotient (FinitePartition.join (K.matchingPartition H e)
        ((K.disjointBoundary H).boundaryPartition S)).toSetoid ≃
      Quotient (FinitePartition.join (K.boundaryPartition S.toLeft)
        (K.pullPartition H e (H.boundaryPartition S.toRight))).toSetoid where
  toFun := Quotient.map (K.collapseBoundary H e) (by
    intro x y h
    exact (K.doubledJoin_rel_iff H e S x y).mp h)
  invFun := Quotient.map Sum.inl (by
    intro i j h
    exact (K.doubledJoin_rel_iff H e S (Sum.inl i) (Sum.inl j)).mpr h)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      exact (K.doubledJoin_rel_iff H e S
        (Sum.inl (K.collapseBoundary H e x)) x).mpr
          (by
            change (FinitePartition.join (K.boundaryPartition S.toLeft)
              (K.pullPartition H e (H.boundaryPartition S.toRight))).toSetoid
                (K.collapseBoundary H e x) (K.collapseBoundary H e x)
            exact (FinitePartition.join (K.boundaryPartition S.toLeft)
              (K.pullPartition H e (H.boundaryPartition S.toRight))).toSetoid.refl _)
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ i => rfl

theorem doubledJoin_rho
    (e : K.Boundary ≃ H.Boundary)
    (S : Finset (K.graph.Edge ⊕ H.graph.Edge)) :
    FinitePartition.rho (K.matchingPartition H e)
        ((K.disjointBoundary H).boundaryPartition S) =
      FinitePartition.rho (K.boundaryPartition S.toLeft)
        (K.pullPartition H e (H.boundaryPartition S.toRight)) := by
  unfold FinitePartition.rho FinitePartition.blocks
  exact Nat.card_congr (K.doubledJoinQuotientEquiv H e S)

/-- Pullback preserves the number of partition blocks. -/
noncomputable def pullPartitionBlockEquiv
    (e : K.Boundary ≃ H.Boundary) (σ : FinitePartition H.Boundary) :
    Quotient (K.pullPartition H e σ).toSetoid ≃ Quotient σ.toSetoid where
  toFun := Quotient.map e (by intro i j h; exact h)
  invFun := Quotient.map e.symm (by
    intro i j h
    change σ.toSetoid (e (e.symm i)) (e (e.symm j))
    simpa using h)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ i =>
      apply Quotient.sound
      rw [e.symm_apply_apply]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ i =>
      apply Quotient.sound
      rw [e.apply_symm_apply]

theorem blocks_pullPartition
    (e : K.Boundary ≃ H.Boundary) (σ : FinitePartition H.Boundary) :
    FinitePartition.blocks (K.pullPartition H e σ) =
      FinitePartition.blocks σ := by
  unfold FinitePartition.blocks
  exact Nat.card_congr (K.pullPartitionBlockEquiv H e σ)

/-- View `H` over the left boundary's partition type. -/
noncomputable def reindexedBoundaryData
    (e : K.Boundary ≃ H.Boundary) :
    BoundaryData (FinitePartition K.Boundary) where
  toNegamiData := H.graph.toNegamiData
  boundaryType S := K.pullPartition H e (H.boundaryPartition S)
  blocks := FinitePartition.blocks
  blocks_le_components := by
    intro S
    rw [K.blocks_pullPartition H e]
    change FinitePartition.blocks (H.boundaryPartition S) ≤ H.graph.components S
    exact H.toBoundaryData.blocks_le_components S

theorem reindexed_internalComponents
    (e : K.Boundary ≃ H.Boundary) (S : Finset H.graph.Edge) :
    (K.reindexedBoundaryData H e).internalComponents S =
      H.toBoundaryData.internalComponents S := by
  unfold BoundaryData.internalComponents
  change H.graph.components S -
      FinitePartition.blocks (K.pullPartition H e (H.boundaryPartition S)) =
    H.graph.components S - FinitePartition.blocks (H.boundaryPartition S)
  rw [K.blocks_pullPartition H e]

/-- Concrete component-count formula for gluing. -/
theorem gluedGraph_component_formula
    (e : K.Boundary ≃ H.Boundary)
    (S : Finset (K.gluedGraph H e).Edge) :
    (K.gluedGraph H e).components S =
      K.toBoundaryData.internalComponents S.toLeft +
        (K.reindexedBoundaryData H e).internalComponents S.toRight +
        FinitePartition.rho (K.boundaryPartition S.toLeft)
          (K.pullPartition H e (H.boundaryPartition S.toRight)) := by
  rw [(K.disjointBoundary H).quotientGraph_component_formula
    (K.matchingPartition H e) S]
  rw [K.disjointBoundary_internalComponents H S,
    K.doubledJoin_rho H e S, K.reindexed_internalComponents H e]

/-- The explicit pushout-style graph realizes the abstract gluing witness. -/
noncomputable def concreteGluingWitness
    (e : K.Boundary ≃ H.Boundary) :
    BoundaryData.Gluing (K.gluedGraph H e).toNegamiData K.toBoundaryData
      (K.reindexedBoundaryData H e) FinitePartition.rho where
  states := K.gluedStateEquiv H e
  selected_card := K.gluedStateEquiv_selected_card H e
  edge_card := K.gluedGraph_edge_card H e
  componentEquiv := by
    intro S
    apply Fintype.equivOfCardEq
    simp only [Fintype.card_fin, Fintype.card_sum]
    change (K.gluedGraph H e).components S =
      K.toBoundaryData.internalComponents (K.gluedStateEquiv H e S).1 +
        ((K.reindexedBoundaryData H e).internalComponents
          (K.gluedStateEquiv H e S).2 +
        FinitePartition.rho
          (K.boundaryPartition (K.gluedStateEquiv H e S).1)
          (K.pullPartition H e
            (H.boundaryPartition (K.gluedStateEquiv H e S).2)))
    change (K.gluedGraph H e).components S =
      K.toBoundaryData.internalComponents S.toLeft +
        ((K.reindexedBoundaryData H e).internalComponents S.toRight +
        FinitePartition.rho (K.boundaryPartition S.toLeft)
          (K.pullPartition H e (H.boundaryPartition S.toRight)))
    simpa only [Nat.add_assoc] using K.gluedGraph_component_formula H e S

/-- Fully concrete categorical gluing: the state object of the pushout-style
graph is degree-preservingly equivalent to the paired boundary-state object. -/
noncomputable def objectEquiv_gluedGraph
    (e : K.Boundary ≃ H.Boundary) :
    GradedObject.Equiv (K.gluedGraph H e).stateObject
      (BoundaryData.pairingObject K.toBoundaryData
        (K.reindexedBoundaryData H e) FinitePartition.rho) :=
  (K.concreteGluingWitness H e).objectEquiv

/-- Fully concrete polynomial gluing theorem. -/
theorem polynomial_gluedGraph
    (e : K.Boundary ≃ H.Boundary) (R : Type*) [CommSemiring R] :
    (K.gluedGraph H e).polynomial R =
      BoundaryData.pairingPolynomial K.toBoundaryData
        (K.reindexedBoundaryData H e) FinitePartition.rho R := by
  exact BoundaryData.polynomial_gluing (K.concreteGluingWitness H e) R

end BoundaryMultigraph
end LeanCo.Negami
