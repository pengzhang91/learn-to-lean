import LeanCo.PackingEdgeColoring.SectionFourLongThreadPair

/-!
# Short thread extraction for Section 4

When every nonisolated vertex has degree two or three and four consecutive
degree-two vertices are forbidden, every edge leaving a degree-three vertex
extends to a `k`-thread for some `k ≤ 3`.  The girth-sixteen hypothesis keeps
the successive local continuation vertices distinct.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Chain certificates, like thread certificates, do not depend on which
decision procedure is used for adjacency. -/
theorem isKChain_change_decidableRel
    (d₁ d₂ : DecidableRel G.Adj)
    {u v : V} {p : G.Walk u v} {k : ℕ}
    (h : @IsKChain V G _ d₁ u v p k) :
    @IsKChain V G _ d₂ u v p k := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro x hx
  exact isTwoVertex_change_decidableRel d₁ d₂ (h.2.2 x hx)

/-- Four distinct consecutive degree-two vertices form a 4-chain. -/
theorem isKChain_four_of_adj
    {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbd : b ≠ d)
    (ha : IsTwoVertex G a) (hb : IsTwoVertex G b)
    (hc : IsTwoVertex G c) (hd : IsTwoVertex G d) :
    IsKChain G (.cons hab (.cons hbc (.cons hcd .nil))) 4 := by
  let p : G.Walk a d := .cons hab (.cons hbc (.cons hcd .nil))
  have hcdPath : (hcd.toWalk).IsPath := Walk.IsPath.of_adj hcd
  have hbcdPath : (Walk.cons hbc hcd.toWalk).IsPath := by
    apply hcdPath.cons
    simp [hbc.ne, hbd]
  have hp : p.IsPath := by
    apply hbcdPath.cons
    simp [p, hab.ne, hac, had]
  refine ⟨hp, rfl, ?_⟩
  intro x hx
  change x ∈ [a, b, c, d] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc
  · exact hd

/-- An edge leaving a degree-three vertex extends, within at most three
degree-two internal vertices, to a certified thread. -/
theorem exists_short_thread_through_neighbor
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno4 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 4)
    {u x : V} (hu : IsThreeVertex G u) (hux : G.Adj u x) :
    ∃ (k : ℕ) (hk : k ≤ 3) (y : V) (p : G.Walk u y),
      IsKThread G p k ∧ p.getVert 1 = x := by
  rcases hdeg x hux.degree_pos_right with hx | hx
  · obtain ⟨y₁, hy₁u, hxy₁⟩ :=
      exists_other_neighbor_of_isTwoVertex G hx hux.symm
    let p₂ : G.Walk u y₁ := .cons hux (.cons hxy₁ .nil)
    have hp₂ : p₂.IsPath := by
      apply (Walk.IsPath.of_adj hxy₁).cons
      simp [p₂, hux.ne, hy₁u.symm]
    rcases hdeg y₁ hxy₁.degree_pos_right with hy₁ | hy₁
    · obtain ⟨y₂, hy₂x, hy₁y₂⟩ :=
        exists_other_neighbor_of_isTwoVertex G hy₁ hxy₁.symm
      have hnot_y₁u : ¬ G.Adj y₁ u :=
        longPair_not_adj_endpoints_of_short_path G hgirth hp₂
          (by simp [p₂]) (by simp [p₂])
      have hy₂u : y₂ ≠ u := by
        intro heq
        subst y₂
        exact hnot_y₁u hy₁y₂
      let p₃ : G.Walk u y₂ :=
        .cons hux (.cons hxy₁ (.cons hy₁y₂ .nil))
      have hp₃ : p₃.IsPath := by
        have htail : (Walk.cons hxy₁ (Walk.cons hy₁y₂ .nil)).IsPath := by
          apply (Walk.IsPath.of_adj hy₁y₂).cons
          simp [hxy₁.ne, hy₂x.symm]
        apply htail.cons
        simp [p₃, hux.ne, hy₁u.symm, hy₂u.symm]
      rcases hdeg y₂ hy₁y₂.degree_pos_right with hy₂ | hy₂
      · obtain ⟨y₃, hy₃y₁, hy₂y₃⟩ :=
          exists_other_neighbor_of_isTwoVertex G hy₂ hy₁y₂.symm
        let q₂ : G.Walk x y₂ := .cons hxy₁ (.cons hy₁y₂ .nil)
        have hq₂ : q₂.IsPath := by
          apply (Walk.IsPath.of_adj hy₁y₂).cons
          simp [q₂, hxy₁.ne, hy₂x.symm]
        have hnot_y₂x : ¬ G.Adj y₂ x :=
          longPair_not_adj_endpoints_of_short_path G hgirth hq₂
            (by simp [q₂]) (by simp [q₂])
        have hnot_y₂u : ¬ G.Adj y₂ u :=
          longPair_not_adj_endpoints_of_short_path G hgirth hp₃
            (by simp [p₃]) (by simp [p₃])
        have hy₃x : y₃ ≠ x := by
          intro heq
          subst y₃
          exact hnot_y₂x hy₂y₃
        have hy₃u : y₃ ≠ u := by
          intro heq
          subst y₃
          exact hnot_y₂u hy₂y₃
        rcases hdeg y₃ hy₂y₃.degree_pos_right with hy₃ | hy₃
        · exact False.elim <| hno4
            (.cons hxy₁ (.cons hy₁y₂ (.cons hy₂y₃ .nil)))
            (isKChain_four_of_adj G hxy₁ hy₁y₂ hy₂y₃
              hy₂x.symm hy₃x.symm hy₃y₁.symm hx hy₁ hy₂ hy₃)
        · let p₄ : G.Walk u y₃ :=
            .cons hux (.cons hxy₁ (.cons hy₁y₂ (.cons hy₂y₃ .nil)))
          have hp₄ : p₄.IsPath := by
            have htail₂ :
                (Walk.cons hy₁y₂ (Walk.cons hy₂y₃ .nil)).IsPath := by
              apply (Walk.IsPath.of_adj hy₂y₃).cons
              simp [hy₁y₂.ne, hy₃y₁.symm]
            have htail₁ :
                (Walk.cons hxy₁
                  (Walk.cons hy₁y₂ (Walk.cons hy₂y₃ .nil))).IsPath := by
              apply htail₂.cons
              simp [hxy₁.ne, hy₂x.symm, hy₃x.symm]
            apply htail₁.cons
            simp [p₄, hux.ne, hy₁u.symm, hy₂u.symm, hy₃u.symm]
          refine ⟨3, by omega, y₃, p₄, ?_, by simp [p₄]⟩
          refine ⟨hp₄, rfl, hu, hy₃, ?_⟩
          intro i hi0 hil
          have hi : i = 1 ∨ i = 2 ∨ i = 3 := by
            change i < 4 at hil
            omega
          rcases hi with rfl | rfl | rfl
          · simpa [p₄] using hx
          · simpa [p₄] using hy₁
          · simpa [p₄] using hy₂
      · refine ⟨2, by omega, y₂, p₃, ?_, by simp [p₃]⟩
        refine ⟨hp₃, rfl, hu, hy₂, ?_⟩
        intro i hi0 hil
        have hi : i = 1 ∨ i = 2 := by
          change i < 3 at hil
          omega
        rcases hi with rfl | rfl
        · simpa [p₃] using hx
        · simpa [p₃] using hy₁
    · refine ⟨1, by omega, y₁, p₂, ?_, by simp [p₂]⟩
      refine ⟨hp₂, rfl, hu, hy₁, ?_⟩
      intro i hi0 hil
      have hi : i = 1 := by
        change i < 2 at hil
        omega
      subst i
      simpa [p₂] using hx
  · let p₁ : G.Walk u x := hux.toWalk
    refine ⟨0, by omega, x, p₁, ?_, by simp [p₁]⟩
    refine ⟨Walk.IsPath.of_adj hux, rfl, hu, hx, ?_⟩
    intro i hi0 hil
    change i < 1 at hil
    omega

/-- Two distinct certified arms at a degree-three vertex have a third
incident arm, and that arm is a `k`-thread for some `k ≤ 3`. -/
theorem exists_complementary_short_thread
    (hgirth : (16 : ℕ∞) ≤ G.egirth)
    (hdeg : ∀ v, 0 < G.degree v →
      IsTwoVertex G v ∨ IsThreeVertex G v)
    (hno4 : ∀ {a b : V} (p : G.Walk a b), ¬ IsKChain G p 4)
    {u v w : V} {p : G.Walk u v} {q : G.Walk u w} {a b : ℕ}
    (hp : IsKThread G p a) (hq : IsKThread G q b)
    (hpq : p.getVert 1 ≠ q.getVert 1) :
    ∃ (k : ℕ) (hk : k ≤ 3) (y : V) (r : G.Walk u y),
      IsKThread G r k ∧
        r.getVert 1 ≠ p.getVert 1 ∧ r.getVert 1 ≠ q.getVert 1 := by
  classical
  let x₁ : V := p.getVert 1
  let x₂ : V := q.getVert 1
  have hux₁ : G.Adj u x₁ := hp.first_step_adj
  have hux₂ : G.Adj u x₂ := hq.first_step_adj
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hp.start_three
  have hex : ∃ x : V, x ∈ G.neighborFinset u ∧ x ≠ x₁ ∧ x ≠ x₂ := by
    by_contra hn
    push_neg at hn
    have hsub : G.neighborFinset u ⊆ {x₁, x₂} := by
      intro x hx
      have hx' := hn x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hxx₁ : x = x₁
      · exact Or.inl hxx₁
      · exact Or.inr (hx' hxx₁)
    have hle : (G.neighborFinset u).card ≤ ({x₁, x₂} : Finset V).card :=
      Finset.card_le_card hsub
    have hpair : ({x₁, x₂} : Finset V).card = 2 := by
      simp [x₁, x₂, hpq]
    omega
  obtain ⟨x, hxmem, hxx₁, hxx₂⟩ := hex
  have hux : G.Adj u x := (G.mem_neighborFinset u x).mp hxmem
  obtain ⟨k, hk, y, r, hr, hrx⟩ :=
    exists_short_thread_through_neighbor G hgirth hdeg hno4 hp.start_three hux
  refine ⟨k, hk, y, r, hr, ?_, ?_⟩
  · simpa [x₁, hrx] using hxx₁
  · simpa [x₂, hrx] using hxx₂

end Finite

end

end LeanCo.PackingEdgeColoring
