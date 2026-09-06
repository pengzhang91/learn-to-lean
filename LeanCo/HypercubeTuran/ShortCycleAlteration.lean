import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
import Mathlib.Tactic

/-!
# Deleting one edge from every short cycle

We index short cycles by their edge finsets (rather than by rooted oriented
walks), choose one edge from every such finset, and delete the chosen edges.
This quotient-free representation avoids choosing the same geometric cycle
once for every rotation and orientation.
-/

open scoped SimpleGraph

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Edge sets of cycles of length strictly less than `g`. -/
abbrev ShortCycleEdgeSet (G : SimpleGraph V) (g : ℕ) :=
  {E : Finset (Sym2 V) //
    ∃ (v : V) (p : G.Walk v v),
      p.IsCycle ∧ p.length < g ∧ p.edges.toFinset = E}

/-- Vertices incident with at least one edge in `E`. -/
def edgeVertexFinset (E : Finset (Sym2 V)) : Finset V :=
  E.biUnion Sym2.toFinset

lemma mem_edgeVertexFinset_of_mem_edge {E : Finset (Sym2 V)}
    {e : Sym2 V} (he : e ∈ E) {v : V} (hv : v ∈ e) :
    v ∈ edgeVertexFinset E := by
  rw [edgeVertexFinset, Finset.mem_biUnion]
  exact ⟨e, he, by simpa using hv⟩

/-- Distinct short-cycle edge sets have vertex-disjoint supports.  This is
the deterministic local-sparsity conclusion consumed by alteration. -/
def ShortCyclesVertexDisjoint (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ X Y : ShortCycleEdgeSet G g, X ≠ Y →
    Disjoint (edgeVertexFinset X.1) (edgeVertexFinset Y.1)

private theorem shortCycleEdgeSet_nonempty {G : SimpleGraph V} {g : ℕ}
    (X : ShortCycleEdgeSet G g) : X.1.Nonempty := by
  obtain ⟨v, p, hpCycle, _hpLen, hpEdges⟩ := X.2
  have hpNotNil : ¬p.Nil := by
    intro hpNil
    have : p.length = 0 := SimpleGraph.Walk.nil_iff_length_eq.mp hpNil
    have := hpCycle.three_le_length
    omega
  have he : s(v, p.snd) ∈ p.edges := p.mk_start_snd_mem_edges hpNotNil
  rw [← hpEdges]
  exact ⟨_, List.mem_toFinset.mpr he⟩

/-- The chosen edge representing one short-cycle edge set. -/
noncomputable def chosenShortCycleEdge {G : SimpleGraph V} {g : ℕ}
    (X : ShortCycleEdgeSet G g) : Sym2 V :=
  (shortCycleEdgeSet_nonempty X).choose

lemma chosenShortCycleEdge_mem {G : SimpleGraph V} {g : ℕ}
    (X : ShortCycleEdgeSet G g) :
    chosenShortCycleEdge X ∈ X.1 :=
  (shortCycleEdgeSet_nonempty X).choose_spec

/-- One selected edge from every distinct short-cycle edge set. -/
noncomputable def shortCycleDeletionEdges (G : SimpleGraph V) (g : ℕ) :
    Finset (Sym2 V) := by
  letI : Fintype (ShortCycleEdgeSet G g) := Fintype.ofFinite _
  exact Finset.univ.image
    (fun X : ShortCycleEdgeSet G g => chosenShortCycleEdge X)

lemma chosenShortCycleEdge_mem_deletionEdges (G : SimpleGraph V) (g : ℕ)
    (X : ShortCycleEdgeSet G g) :
    chosenShortCycleEdge X ∈ shortCycleDeletionEdges G g := by
  classical
  letI : Fintype (ShortCycleEdgeSet G g) := Fintype.ofFinite _
  change chosenShortCycleEdge X ∈ Finset.univ.image
    (fun Y : ShortCycleEdgeSet G g => chosenShortCycleEdge Y)
  exact Finset.mem_image.mpr ⟨X, Finset.mem_univ X, rfl⟩

/-- Edge-set formulation of a matching: two selected edges sharing a vertex
must be equal. -/
def IsEdgeFinsetMatching (D : Finset (Sym2 V)) : Prop :=
  ∀ ⦃e f : Sym2 V⦄, e ∈ D → f ∈ D →
    (∃ v : V, v ∈ e ∧ v ∈ f) → e = f

/-- Pairwise vertex-disjoint short cycles make the selected deletion edges
a matching. -/
theorem shortCycleDeletionEdges_isMatching {G : SimpleGraph V} {g : ℕ}
    (hdis : ShortCyclesVertexDisjoint G g) :
    IsEdgeFinsetMatching (shortCycleDeletionEdges G g) := by
  classical
  letI : Fintype (ShortCycleEdgeSet G g) := Fintype.ofFinite _
  intro e f he hf hef
  change e ∈ Finset.univ.image
    (fun X : ShortCycleEdgeSet G g => chosenShortCycleEdge X) at he
  change f ∈ Finset.univ.image
    (fun X : ShortCycleEdgeSet G g => chosenShortCycleEdge X) at hf
  obtain ⟨X, _hX, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨Y, _hY, rfl⟩ := Finset.mem_image.mp hf
  by_cases hXY : X = Y
  · subst Y
    rfl
  · obtain ⟨v, hvXedge, hvYedge⟩ := hef
    have hvX : v ∈ edgeVertexFinset X.1 :=
      mem_edgeVertexFinset_of_mem_edge (chosenShortCycleEdge_mem X) hvXedge
    have hvY : v ∈ edgeVertexFinset Y.1 :=
      mem_edgeVertexFinset_of_mem_edge (chosenShortCycleEdge_mem Y) hvYedge
    exact (Finset.disjoint_left.mp (hdis X Y hXY) hvX hvY).elim

/-- The graph obtained by deleting the selected short-cycle edges. -/
noncomputable def deleteShortCycles (G : SimpleGraph V) (g : ℕ) :
    SimpleGraph V :=
  G.deleteEdges (shortCycleDeletionEdges G g : Set (Sym2 V))

noncomputable instance instDecidableRelDeleteShortCycles
    (G : SimpleGraph V) [DecidableRel G.Adj] (g : ℕ) :
    DecidableRel (deleteShortCycles G g).Adj := by
  unfold deleteShortCycles
  infer_instance

lemma deleteShortCycles_le (G : SimpleGraph V) (g : ℕ) :
    deleteShortCycles G g ≤ G :=
  SimpleGraph.deleteEdges_le _

/-- Every cycle remaining after alteration has length at least `g`. -/
theorem cycle_length_ge_of_deleteShortCycles
    (G : SimpleGraph V) (g : ℕ) {v : V}
    (p : (deleteShortCycles G g).Walk v v) (hp : p.IsCycle) :
    g ≤ p.length := by
  classical
  by_contra hlen
  have hlt : p.length < g := by omega
  let q : G.Walk v v := p.mapLe (deleteShortCycles_le G g)
  have hqCycle : q.IsCycle := hp.mapLe (deleteShortCycles_le G g)
  have hqLength : q.length < g := by
    change (p.map (.ofLE (deleteShortCycles_le G g))).length < g
    simpa only [SimpleGraph.Walk.length_map] using hlt
  let X : ShortCycleEdgeSet G g :=
    ⟨p.edges.toFinset, v, q, hqCycle, hqLength,
      by simp [q, SimpleGraph.Walk.edges_mapLe_eq_edges]⟩
  have hchosenD : chosenShortCycleEdge X ∈ shortCycleDeletionEdges G g :=
    chosenShortCycleEdge_mem_deletionEdges G g X
  have hchosenList : chosenShortCycleEdge X ∈ p.edges := by
    exact List.mem_toFinset.mp (chosenShortCycleEdge_mem X)
  have hchosenGraph : chosenShortCycleEdge X ∈
      (deleteShortCycles G g).edgeSet :=
    p.edges_subset_edgeSet hchosenList
  rw [deleteShortCycles, SimpleGraph.edgeSet_deleteEdges] at hchosenGraph
  exact hchosenGraph.2 hchosenD

/-- Extended girth of the altered graph is at least `g`; this also covers
the acyclic case, where extended girth is infinity. -/
theorem coe_le_egirth_deleteShortCycles (G : SimpleGraph V) (g : ℕ) :
    (g : ℕ∞) ≤ (deleteShortCycles G g).egirth := by
  rw [SimpleGraph.le_egirth]
  intro v p hp
  simpa only [ENat.coe_le_coe] using
    cycle_length_ge_of_deleteShortCycles G g p hp

end LeanCo.HypercubeTuran
