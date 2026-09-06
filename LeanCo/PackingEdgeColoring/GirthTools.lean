import Mathlib

/-!
# Small-cycle criteria for extended girth

The finite counterexamples are most conveniently checked by their explicit
adjacency tables.  These elementary predicates bridge those checks to
Mathlib's semantic `SimpleGraph.egirth`.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- There is no closed adjacent triple.  In a simple graph the adjacency
hypotheses already force the three vertices to be distinct. -/
def HasNoTriangle : Prop :=
  ∀ a b c : V, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)

/-- There is no simple closed adjacent quadruple.  Only the two opposite
inequalities need to be stated: adjacency supplies all consecutive ones. -/
def HasNoFourCycle : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d →
    ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

theorem four_le_egirth_of_hasNoTriangle (htriangle : HasNoTriangle G) :
    (4 : ℕ∞) ≤ G.egirth := by
  rw [le_egirth]
  intro a p hp
  norm_cast
  by_contra hfour
  have hlen : p.length = 3 := by
    have := hp.three_le_length
    omega
  have h01 := p.adj_getVert_succ (i := 0) (by omega)
  have h12 := p.adj_getVert_succ (i := 1) (by omega)
  have h23 := p.adj_getVert_succ (i := 2) (by omega)
  apply htriangle (p.getVert 0) (p.getVert 1) (p.getVert 2)
  refine ⟨h01, h12, ?_⟩
  have hend : p.getVert 3 = a := by
    rw [← hlen]
    exact p.getVert_length
  simpa [hend] using h23

theorem five_le_egirth_of_hasNoTriangle_hasNoFourCycle
    (htriangle : HasNoTriangle G) (hfourcycle : HasNoFourCycle G) :
    (5 : ℕ∞) ≤ G.egirth := by
  rw [le_egirth]
  intro a p hp
  norm_cast
  have hfour : 4 ≤ p.length := by
    have he := four_le_egirth_of_hasNoTriangle G htriangle
    rw [le_egirth] at he
    exact_mod_cast he a p hp
  by_contra hfive
  have hlen : p.length = 4 := by omega
  have h01 := p.adj_getVert_succ (i := 0) (by omega)
  have h12 := p.adj_getVert_succ (i := 1) (by omega)
  have h23 := p.adj_getVert_succ (i := 2) (by omega)
  have h34 := p.adj_getVert_succ (i := 3) (by omega)
  have h02 : p.getVert 0 ≠ p.getVert 2 := by
    simpa using hp.getVert_sub_one_ne_getVert_add_one (i := 1) (by omega)
  have h13 : p.getVert 1 ≠ p.getVert 3 := by
    simpa using hp.getVert_sub_one_ne_getVert_add_one (i := 2) (by omega)
  apply hfourcycle (p.getVert 0) (p.getVert 1) (p.getVert 2) (p.getVert 3)
    h02 h13
  refine ⟨h01, h12, h23, ?_⟩
  have hend : p.getVert 4 = a := by
    rw [← hlen]
    exact p.getVert_length
  simpa [hend] using h34

end

end LeanCo.PackingEdgeColoring
