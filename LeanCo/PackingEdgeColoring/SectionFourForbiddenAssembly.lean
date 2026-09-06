import LeanCo.PackingEdgeColoring.SectionFourThreadExtraction
import LeanCo.PackingEdgeColoring.SectionFourStructure

/-!
# Assembly of the Section 4 local exclusions

The paper proves the eight local configurations `333`, `332`, `331`,
`330`, `322`, `321`, and `320` in stages.  This file records the purely
structural step that turns those local triple-arm exclusions into the single
`HasThreeAndLongThreadAt` prohibition used by the facial discharging theorem.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The graph contains no three pairwise distinct thread arms of the given
ordered lengths at one centre. -/
def ForbidsThreadTripleLengths (a b c : ℕ) : Prop :=
  ∀ {u v w y : V} {p : G.Walk u v} {q : G.Walk u w}
      {r : G.Walk u y},
    IsKThread G p a → IsKThread G q b → IsKThread G r c →
      p.getVert 1 ≠ q.getVert 1 →
      p.getVert 1 ≠ r.getVert 1 →
      q.getVert 1 ≠ r.getVert 1 → False

/-- The four `33k` exclusions, together with short-thread extraction, rule
out two distinct 3-threads at any degree-three centre. -/
theorem no_distinct_three_three_of_local_triples
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno4 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 4)
    (h333 : ForbidsThreadTripleLengths G 3 3 3)
    (h332 : ForbidsThreadTripleLengths G 3 3 2)
    (h331 : ForbidsThreadTripleLengths G 3 3 1)
    (h330 : ForbidsThreadTripleLengths G 3 3 0) :
    ∀ u, ¬ HasDistinctThreadsAt (G := G) u 3 3 := by
  intro u hpair
  obtain ⟨v, w, p, q, hp, hq, hpq⟩ := hpair
  obtain ⟨k, hk, y, r, hr, hrp, hrq⟩ :=
    exists_complementary_short_thread G hgirth hdeg hno4 hp hq hpq
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkCases with rfl | rfl | rfl | rfl
  · exact h330 hp hq hr hpq hrp.symm hrq.symm
  · exact h331 hp hq hr hpq hrp.symm hrq.symm
  · exact h332 hp hq hr hpq hrp.symm hrq.symm
  · exact h333 hp hq hr hpq hrp.symm hrq.symm

/-- Once two 3-threads are excluded, the three remaining `32k` exclusions
rule out a distinct 3-thread/2-thread pair. -/
theorem no_distinct_three_two_of_local_triples
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno4 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 4)
    (hno33 : ∀ u, ¬ HasDistinctThreadsAt (G := G) u 3 3)
    (h322 : ForbidsThreadTripleLengths G 3 2 2)
    (h321 : ForbidsThreadTripleLengths G 3 2 1)
    (h320 : ForbidsThreadTripleLengths G 3 2 0) :
    ∀ u, ¬ HasDistinctThreadsAt (G := G) u 3 2 := by
  intro u hpair
  obtain ⟨v, w, p, q, hp, hq, hpq⟩ := hpair
  obtain ⟨k, hk, y, r, hr, hrp, hrq⟩ :=
    exists_complementary_short_thread G hgirth hdeg hno4 hp hq hpq
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkCases with rfl | rfl | rfl | rfl
  · exact h320 hp hq hr hpq hrp.symm hrq.symm
  · exact h321 hp hq hr hpq hrp.symm hrq.symm
  · exact h322 hp hq hr hpq hrp.symm hrq.symm
  · apply hno33 u
    exact ⟨v, y, p, r, hp, hr, hrp.symm⟩

/-- The seven local triple-arm exclusions are exactly enough for the single
forbidden-family hypothesis consumed by Section 4 discharging. -/
theorem no_threeAndLongThread_of_local_triples
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno4 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 4)
    (h333 : ForbidsThreadTripleLengths G 3 3 3)
    (h332 : ForbidsThreadTripleLengths G 3 3 2)
    (h331 : ForbidsThreadTripleLengths G 3 3 1)
    (h330 : ForbidsThreadTripleLengths G 3 3 0)
    (h322 : ForbidsThreadTripleLengths G 3 2 2)
    (h321 : ForbidsThreadTripleLengths G 3 2 1)
    (h320 : ForbidsThreadTripleLengths G 3 2 0) :
    ∀ u, ¬ HasThreeAndLongThreadAt (G := G) u := by
  have hno33 := no_distinct_three_three_of_local_triples G hgirth hdeg hno4
    h333 h332 h331 h330
  have hno32 := no_distinct_three_two_of_local_triples G hgirth hdeg hno4
    hno33 h322 h321 h320
  intro u h
  exact h.elim (hno32 u) (hno33 u)

end Finite

end

end LeanCo.PackingEdgeColoring
