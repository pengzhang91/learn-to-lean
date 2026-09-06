import LeanCo.SizeRamsey.GraphBasics
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Data.Nat.Choose.Basic

/-!
# Balanced cuts with an independent prescribed side

This file isolates the first, deterministic step of Beke--Li--Sahasrabudhe
Lemma 4.5.  The vertices are split as `V₀ ∪ U`, with `U` independent.  We
choose the ceiling half of `V₀` for the left side while keeping all of `U` on
the right, and retain at least half of all edges across the cut.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u v

variable {V : Type u}

/-! ## The crossing graph -/

/-- The spanning subgraph of `G` containing exactly the edges crossing
between the two specified finite vertex sets. -/
def crossSubgraph (G : SimpleGraph V) (A B : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧
    ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A))
  symm.symm x y hxy :=
    ⟨hxy.1.symm, hxy.2.elim
      (fun h ↦ Or.inr ⟨h.2, h.1⟩)
      (fun h ↦ Or.inl ⟨h.2, h.1⟩)⟩

@[simp]
theorem crossSubgraph_adj (G : SimpleGraph V) (A B : Finset V) {x y : V} :
    (crossSubgraph G A B).Adj x y ↔
      G.Adj x y ∧ ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)) :=
  Iff.rfl

instance [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (A B : Finset V) : DecidableRel (crossSubgraph G A B).Adj :=
  inferInstanceAs (DecidableRel fun x y ↦
    G.Adj x y ∧ ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)))

/-- A crossing graph is a subgraph of its ambient graph. -/
theorem crossSubgraph_le (G : SimpleGraph V) (A B : Finset V) :
    crossSubgraph G A B ≤ G :=
  fun _ _ h ↦ h.1

/-- Choice-free number of edges crossing the two specified sides. -/
noncomputable def crossEdgeCount (G : SimpleGraph V) (A B : Finset V) : ℕ :=
  edgeCount (crossSubgraph G A B)

/-- Crossing is symmetric in the two sides. -/
theorem crossSubgraph_comm (G : SimpleGraph V) (A B : Finset V) :
    crossSubgraph G A B = crossSubgraph G B A := by
  ext x y
  simp only [crossSubgraph_adj]
  aesop

theorem crossEdgeCount_comm (G : SimpleGraph V) (A B : Finset V) :
    crossEdgeCount G A B = crossEdgeCount G B A := by
  rw [crossEdgeCount, crossEdgeCount, crossSubgraph_comm]

/-- For disjoint sides, oriented interedges from `A` to `B` count every
undirected crossing edge exactly once. -/
theorem crossEdgeCount_eq_card_interedges
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (A B : Finset V) (hAB : Disjoint A B) :
    crossEdgeCount G A B = #(G.interedges A B) := by
  classical
  rw [crossEdgeCount, edgeCount_eq_card_edgeFinset]
  symm
  let f : (p : V × V) → p ∈ G.interedges A B → Sym2 V :=
    fun p _ ↦ s(p.1, p.2)
  refine Finset.card_bij f ?_ ?_ ?_
  · intro p hp
    rw [SimpleGraph.mem_edgeFinset]
    exact ⟨(G.mem_interedges_iff.mp hp).2.2,
      Or.inl ⟨(G.mem_interedges_iff.mp hp).1,
        (G.mem_interedges_iff.mp hp).2.1⟩⟩
  · intro p hp q hq heq
    rw [Sym2.eq, Sym2.rel_iff'] at heq
    rcases heq with heq | heq
    · exact heq
    · have hpA : p.1 ∈ A := (G.mem_interedges_iff.mp hp).1
      have hpB : p.2 ∈ B := (G.mem_interedges_iff.mp hp).2.1
      have hqA : q.1 ∈ A := (G.mem_interedges_iff.mp hq).1
      have hqB : q.2 ∈ B := (G.mem_interedges_iff.mp hq).2.1
      have hp1q2 : p.1 = q.2 := congrArg Prod.fst heq
      exact ((Finset.disjoint_left.mp hAB) hpA (hp1q2 ▸ hqB)).elim
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        crossSubgraph_adj] at he
      rcases he.2 with hxy | hyx
      · exact ⟨(x, y), G.mem_interedges_iff.mpr ⟨hxy.1, hxy.2, he.1⟩, rfl⟩
      · refine ⟨(y, x), G.mem_interedges_iff.mpr
          ⟨hyx.2, hyx.1, he.1.symm⟩, ?_⟩
        exact Sym2.eq_swap

/-! ## The prescribed right side -/

/-- Once `A ⊆ V₀` is chosen, all remaining vertices, including the
independent set `U`, form the right side. -/
def balancedRightPart [DecidableEq V] (V₀ U A : Finset V) : Finset V :=
  (V₀ \ A) ∪ U

theorem disjoint_balancedRightPart [DecidableEq V] {V₀ U A : Finset V}
    (hA : A ⊆ V₀) (hVU : Disjoint V₀ U) :
    Disjoint A (balancedRightPart V₀ U A) := by
  rw [Finset.disjoint_left]
  intro x hx
  simp only [balancedRightPart, Finset.mem_union, Finset.mem_sdiff]
  rintro (hxDiff | hxU)
  · exact hxDiff.2 hx
  · exact (Finset.disjoint_left.mp hVU) (hA hx) hxU

theorem union_balancedRightPart [Fintype V] [DecidableEq V]
    {V₀ U A : Finset V}
    (_hA : A ⊆ V₀) (hcover : V₀ ∪ U = Finset.univ) :
    A ∪ balancedRightPart V₀ U A = Finset.univ := by
  ext x
  simp only [balancedRightPart, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_univ, iff_true]
  have hx : x ∈ V₀ ∨ x ∈ U := by
    apply Finset.mem_union.mp
    rw [hcover]
    exact Finset.mem_univ x
  rcases hx with hxV | hxU
  · by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr (Or.inl ⟨hxV, hxA⟩)
  · exact Or.inr (Or.inr hxU)

theorem mem_balancedRightPart_iff_of_mem_V₀ [DecidableEq V]
    {V₀ U A : Finset V}
    (hVU : Disjoint V₀ U) {x : V} (hx : x ∈ V₀) :
    x ∈ balancedRightPart V₀ U A ↔ x ∉ A := by
  simp only [balancedRightPart, Finset.mem_union, Finset.mem_sdiff]
  have hxU : x ∉ U := fun hx' ↦ (Finset.disjoint_left.mp hVU) hx hx'
  simp [hx, hxU]

theorem subset_balancedRightPart_left [DecidableEq V]
    (V₀ U A : Finset V) : V₀ \ A ⊆ balancedRightPart V₀ U A := by
  intro x hx
  exact Finset.mem_union_left U hx

theorem subset_balancedRightPart_right [DecidableEq V]
    (V₀ U A : Finset V) : U ⊆ balancedRightPart V₀ U A := by
  intro x hx
  exact Finset.mem_union_right (V₀ \ A) hx

theorem balancedRightPart_sdiff_right [DecidableEq V]
    {V₀ U A : Finset V} (hVU : Disjoint V₀ U) :
    balancedRightPart V₀ U A \ U = V₀ \ A := by
  ext x
  simp only [balancedRightPart, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hx | hx, hxNotU⟩
    · exact hx
    · exact (hxNotU hx).elim
  · intro hx
    refine ⟨Or.inl hx, ?_⟩
    exact fun hxU ↦ (Finset.disjoint_left.mp hVU) hx.1 hxU

/-- The crossing graph is literally bipartite on its two disjoint sides. -/
theorem crossSubgraph_isBipartiteWith (G : SimpleGraph V)
    {A B : Finset V} (hAB : Disjoint A B) :
    (crossSubgraph G A B).IsBipartiteWith (A : Set V) (B : Set V) where
  disjoint := by
    simpa only [Finset.disjoint_coe] using hAB
  mem_of_adj := by
    intro x y hxy
    exact hxy.2

/-! ## Oriented-edge bookkeeping -/

theorem card_interedges_union_left_of_disjoint
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    {S T R : Finset V} (hST : Disjoint S T) :
    #(G.interedges (S ∪ T) R) =
      #(G.interedges S R) + #(G.interedges T R) := by
  have heq : G.interedges (S ∪ T) R =
      G.interedges S R ∪ G.interedges T R := by
    ext p
    simp only [G.mem_interedges_iff, Finset.mem_union]
    aesop
  rw [heq, Finset.card_union_of_disjoint]
  exact G.interedges_disjoint_left hST R

theorem card_interedges_union_right_of_disjoint
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    {R S T : Finset V} (hST : Disjoint S T) :
    #(G.interedges R (S ∪ T)) =
      #(G.interedges R S) + #(G.interedges R T) := by
  have heq : G.interedges R (S ∪ T) =
      G.interedges R S ∪ G.interedges R T := by
    ext p
    simp only [G.mem_interedges_iff, Finset.mem_union]
    aesop
  rw [heq, Finset.card_union_of_disjoint]
  exact G.interedges_disjoint_right R hST

theorem interedges_eq_empty_of_independent
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    {S : Finset V}
    (hS : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ¬G.Adj x y) :
    G.interedges S S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hS (G.mem_interedges_iff.mp hp).1
    (G.mem_interedges_iff.mp hp).2.1
    (G.mem_interedges_iff.mp hp).2.2

/-- Oriented adjacent pairs on the whole finite vertex set are the darts of
the graph, hence are twice the undirected edge count. -/
theorem card_interedges_univ_eq_two_mul_edgeCount
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    #(G.interedges Finset.univ Finset.univ) = 2 * edgeCount G := by
  classical
  calc
    #(G.interedges Finset.univ Finset.univ) = Fintype.card G.Dart := by
      rw [← Finset.card_univ]
      let f : (p : V × V) →
          p ∈ G.interedges Finset.univ Finset.univ → G.Dart :=
        fun p hp ↦ ⟨p, (G.mem_interedges_iff.mp hp).2.2⟩
      refine Finset.card_bij f ?_ ?_ ?_
      · intro p hp
        exact Finset.mem_univ _
      · intro p hp q hq heq
        exact congrArg Dart.toProd heq
      · intro d _
        refine ⟨d.toProd, ?_, ?_⟩
        · exact G.mem_interedges_iff.mpr
            ⟨Finset.mem_univ _, Finset.mem_univ _, d.adj⟩
        · apply Dart.ext
          rfl
    _ = 2 * #G.edgeFinset := G.dart_card_eq_twice_card_edges
    _ = 2 * edgeCount G := by rw [edgeCount_eq_card_edgeFinset]

/-- If `V₀ ∪ U` is the whole vertex set and `U` is independent, every dart
is either internal to `V₀` or one of the two orientations of a `V₀`--`U`
edge. -/
theorem two_mul_edgeCount_eq_internalDarts_add_crossDarts
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {V₀ U : Finset V} (hVU : Disjoint V₀ U)
    (hcover : V₀ ∪ U = Finset.univ)
    (hU : ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U → ¬G.Adj x y) :
    2 * edgeCount G =
      #(G.interedges V₀ V₀) + 2 * #(G.interedges V₀ U) := by
  letI : Std.Symm G.Adj := SimpleGraph.symm_adj (G := G) id
  have hUU : #(G.interedges U U) = 0 := by
    rw [interedges_eq_empty_of_independent G hU, Finset.card_empty]
  have hsymm : #(G.interedges U V₀) = #(G.interedges V₀ U) :=
    Rel.card_interedges_comm (r := G.Adj) U V₀
  calc
    2 * edgeCount G = #(G.interedges Finset.univ Finset.univ) :=
      (card_interedges_univ_eq_two_mul_edgeCount G).symm
    _ = #(G.interedges (V₀ ∪ U) (V₀ ∪ U)) := by rw [hcover]
    _ = #(G.interedges V₀ (V₀ ∪ U)) +
        #(G.interedges U (V₀ ∪ U)) :=
      card_interedges_union_left_of_disjoint G hVU
    _ = (#(G.interedges V₀ V₀) + #(G.interedges V₀ U)) +
        (#(G.interedges U V₀) + #(G.interedges U U)) := by
      rw [card_interedges_union_right_of_disjoint G hVU,
        card_interedges_union_right_of_disjoint G hVU]
    _ = #(G.interedges V₀ V₀) + 2 * #(G.interedges V₀ U) := by
      rw [hUU, hsymm]
      omega

/-! ## Fixed-size subset counts -/

/-- The ceiling half of a natural number, written without real arithmetic. -/
def ceilHalf (m : ℕ) : ℕ := (m + 1) / 2

theorem ceilHalf_le (m : ℕ) : ceilHalf m ≤ m := by
  unfold ceilHalf
  omega

theorem ceilHalf_pos {m : ℕ} (hm : 0 < m) : 0 < ceilHalf m := by
  unfold ceilHalf
  omega

theorem ceilHalf_pred_eq_half_pred {m : ℕ} (hm : 0 < m) :
    ceilHalf m - 1 = (m - 1) / 2 := by
  unfold ceilHalf
  omega

/-- At least half of all ceiling-half subsets contain any prescribed
element. -/
theorem choose_le_twice_choose_pred_ceilHalf {m : ℕ} (hm : 0 < m) :
    m.choose (ceilHalf m) ≤
      2 * (m - 1).choose (ceilHalf m - 1) := by
  have ha0 : 0 < ceilHalf m := ceilHalf_pos hm
  have hpascal := Nat.choose_eq_choose_pred_add (n := m)
    (k := ceilHalf m) hm ha0
  have hmiddle := Nat.choose_le_middle (ceilHalf m) (m - 1)
  rw [← ceilHalf_pred_eq_half_pred hm] at hmiddle
  omega

/-- At least half of all ceiling-half subsets separate any prescribed pair
of distinct elements. -/
theorem choose_le_four_mul_choose_pred_pred_ceilHalf {m : ℕ} (hm : 2 ≤ m) :
    m.choose (ceilHalf m) ≤
      4 * (m - 2).choose (ceilHalf m - 1) := by
  by_cases hm2 : m = 2
  · subst m
    norm_num [ceilHalf, Nat.choose]
  have hm3 : 3 ≤ m := by omega
  have ha0 : 0 < ceilHalf m := ceilHalf_pos (by omega)
  have ha1 : 0 < ceilHalf m - 1 := by
    unfold ceilHalf
    omega
  have houter := Nat.choose_eq_choose_pred_add (n := m)
    (k := ceilHalf m) (by omega) ha0
  have hleft := Nat.choose_eq_choose_pred_add (n := m - 1)
    (k := ceilHalf m - 1) (by omega) ha1
  have hright := Nat.choose_eq_choose_pred_add (n := m - 1)
    (k := ceilHalf m) (by omega) ha0
  have hmPred : m - 1 - 1 = m - 2 := by omega
  have haPred : ceilHalf m - 1 - 1 = ceilHalf m - 2 := by omega
  rw [hmPred, haPred] at hleft
  rw [hmPred] at hright
  have hk : ceilHalf m - 1 ≤ m - 2 := by
    unfold ceilHalf
    omega
  have hcomp : (m - 2) - (ceilHalf m - 1) = (m - 2) / 2 := by
    unfold ceilHalf
    omega
  have hcentral :
      (m - 2).choose ((m - 2) / 2) =
        (m - 2).choose (ceilHalf m - 1) := by
    rw [← hcomp]
    exact Nat.choose_symm hk
  have h₁ := Nat.choose_le_middle (ceilHalf m - 2) (m - 2)
  have h₂ := Nat.choose_le_middle (ceilHalf m - 1) (m - 2)
  have h₃ := Nat.choose_le_middle (ceilHalf m) (m - 2)
  rw [hcentral] at h₁ h₂ h₃
  omega

/-- Number of fixed-size subsets containing one prescribed element. -/
theorem card_powersetCard_filter_mem [DecidableEq V]
    {S : Finset V} {a : ℕ} {x : V} (hx : x ∈ S) (ha : 1 ≤ a) :
    #((S.powersetCard a).filter fun A ↦ x ∈ A) =
      (S.card - 1).choose (a - 1) := by
  have hsubset : ({x} : Finset V) ⊆ S := by simpa
  have hcard : #({x} : Finset V) ≤ a := by simp only [card_singleton]; omega
  simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using
    Finset.card_filter_powersetCard_subset ({x} : Finset V) S a hsubset hcard

/-- Number of fixed-size subsets containing two prescribed distinct
elements. -/
theorem card_powersetCard_filter_mem_mem [DecidableEq V]
    {S : Finset V} {a : ℕ} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (ha : 2 ≤ a) :
    #((S.powersetCard a).filter fun A ↦ x ∈ A ∧ y ∈ A) =
      (S.card - 2).choose (a - 2) := by
  have hsubset : ({x, y} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hpair : #({x, y} : Finset V) = 2 := by simp [hxy]
  have hcard : #({x, y} : Finset V) ≤ a := by omega
  simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
    hpair] using
    Finset.card_filter_powersetCard_subset ({x, y} : Finset V) S a
      hsubset hcard

/-- Number of fixed-size subsets which contain `x` but not a distinct `y`.
This is the fibre count used for each oriented internal edge. -/
theorem card_powersetCard_filter_mem_notMem [DecidableEq V]
    {S : Finset V} {a : ℕ} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (ha0 : 1 ≤ a) (haS : a ≤ S.card) :
    #((S.powersetCard a).filter fun A ↦ x ∈ A ∧ y ∉ A) =
      (S.card - 2).choose (a - 1) := by
  by_cases ha1 : a = 1
  · subst a
    have heq :
        (S.powersetCard 1).filter (fun A ↦ x ∈ A ∧ y ∉ A) = {{x}} := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powersetCard,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hAS, hcard⟩, hxA, _⟩
        obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
        subst A
        have hxz : x = z := by simpa using hxA
        subst z
        rfl
      · rintro rfl
        have hsingleSub : ({x} : Finset V) ⊆ S := by
          simpa only [Finset.singleton_subset_iff] using hx
        exact ⟨⟨hsingleSub, Finset.card_singleton x⟩,
          Finset.mem_singleton_self x,
          (by simpa only [Finset.mem_singleton] using hxy.symm)⟩
    rw [heq, Finset.card_singleton]
    simp only [Nat.reduceSubDiff, Nat.choose_zero_right]
  · have ha2 : 2 ≤ a := by omega
    let Fx := (S.powersetCard a).filter fun A ↦ x ∈ A
    let Fxy := (S.powersetCard a).filter fun A ↦ x ∈ A ∧ y ∈ A
    have hsub : Fxy ⊆ Fx := by
      intro A hA
      simp only [Fxy, Finset.mem_filter] at hA
      simp only [Fx, Finset.mem_filter]
      exact ⟨hA.1, hA.2.1⟩
    have heq :
        (S.powersetCard a).filter (fun A ↦ x ∈ A ∧ y ∉ A) =
          Fx \ Fxy := by
      ext A
      simp only [Fx, Fxy, Finset.mem_filter, Finset.mem_sdiff]
      aesop
    rw [heq, Finset.card_sdiff_of_subset hsub,
      card_powersetCard_filter_mem hx ha0,
      card_powersetCard_filter_mem_mem hx hy hxy ha2]
    have hS2 : 2 ≤ S.card := by
      have hpair : #({x, y} : Finset V) = 2 := by simp [hxy]
      have hpairSub : ({x, y} : Finset V) ⊆ S := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      exact hpair ▸ Finset.card_le_card hpairSub
    have hpascal := Nat.choose_eq_choose_pred_add
      (n := S.card - 1) (k := a - 1) (by omega) (by omega)
    have hSPred : S.card - 1 - 1 = S.card - 2 := by omega
    have haPred : a - 1 - 1 = a - 2 := by omega
    rw [hSPred, haPred] at hpascal
    omega

/-! ## Double-counting the balanced cuts -/

/-- Elementary finite double counting: count the pairs satisfying `R` first
by their left coordinate and then by their right coordinate. -/
theorem sum_card_filter_comm
    {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (P : Finset α) (Q : Finset β) (R : α → β → Prop) [DecidableRel R] :
    ∑ a ∈ P, #((Q.filter fun b ↦ R a b)) =
      ∑ b ∈ Q, #((P.filter fun a ↦ R a b)) := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Exact double count for oriented edges separated by a uniformly ranging
fixed-size subset. -/
theorem sum_card_interedges_powersetCard_sdiff
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) {a : ℕ} (ha0 : 1 ≤ a) (haS : a ≤ S.card) :
    (∑ A ∈ S.powersetCard a, #(G.interedges A (S \ A))) =
      (S.card - 2).choose (a - 1) * #(G.interedges S S) := by
  classical
  let P := S.powersetCard a
  let E := G.interedges S S
  let R : Finset V → (V × V) → Prop :=
    fun A p ↦ p.1 ∈ A ∧ p.2 ∉ A
  have hrewrite : ∀ A ∈ P,
      G.interedges A (S \ A) = E.filter (R A) := by
    intro A hA
    have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
    ext p
    simp only [G.mem_interedges_iff, Finset.mem_sdiff, Finset.mem_filter,
      E, R]
    constructor
    · rintro ⟨hpA, ⟨hpS, hpNotA⟩, hadj⟩
      exact ⟨⟨hAS hpA, hpS, hadj⟩, hpA, hpNotA⟩
    · rintro ⟨⟨hpS, hqS, hadj⟩, hpA, hqNotA⟩
      exact ⟨hpA, ⟨hqS, hqNotA⟩, hadj⟩
  calc
    (∑ A ∈ S.powersetCard a, #(G.interedges A (S \ A))) =
        ∑ A ∈ P, #(E.filter (R A)) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [hrewrite A hA]
    _ = ∑ p ∈ E, #(P.filter fun A ↦ R A p) :=
      sum_card_filter_comm P E R
    _ = ∑ _p ∈ E, (S.card - 2).choose (a - 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := G.mem_interedges_iff.mp hp
      exact card_powersetCard_filter_mem_notMem
        hp'.1 hp'.2.1 hp'.2.2.ne ha0 haS
    _ = (S.card - 2).choose (a - 1) * #(G.interedges S S) := by
      simp only [E, Finset.sum_const, nsmul_eq_mul]
      exact Nat.mul_comm _ _

/-- Exact double count for edges from fixed-size subsets of `S` into a
fixed outside set `U`. -/
theorem sum_card_interedges_powersetCard_fixedRight
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S U : Finset V) {a : ℕ} (ha0 : 1 ≤ a) :
    (∑ A ∈ S.powersetCard a, #(G.interedges A U)) =
      (S.card - 1).choose (a - 1) * #(G.interedges S U) := by
  classical
  let P := S.powersetCard a
  let E := G.interedges S U
  let R : Finset V → (V × V) → Prop := fun A p ↦ p.1 ∈ A
  have hrewrite : ∀ A ∈ P, G.interedges A U = E.filter (R A) := by
    intro A hA
    have hAS : A ⊆ S := (Finset.mem_powersetCard.mp hA).1
    ext p
    simp only [G.mem_interedges_iff, Finset.mem_filter, E, R]
    constructor
    · rintro ⟨hpA, hpU, hadj⟩
      exact ⟨⟨hAS hpA, hpU, hadj⟩, hpA⟩
    · rintro ⟨⟨hpS, hpU, hadj⟩, hpA⟩
      exact ⟨hpA, hpU, hadj⟩
  calc
    (∑ A ∈ S.powersetCard a, #(G.interedges A U)) =
        ∑ A ∈ P, #(E.filter (R A)) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [hrewrite A hA]
    _ = ∑ p ∈ E, #(P.filter fun A ↦ R A p) :=
      sum_card_filter_comm P E R
    _ = ∑ _p ∈ E, (S.card - 1).choose (a - 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact card_powersetCard_filter_mem
        (G.mem_interedges_iff.mp hp).1 ha0
    _ = (S.card - 1).choose (a - 1) * #(G.interedges S U) := by
      simp only [E, Finset.sum_const, nsmul_eq_mul]
      exact Nat.mul_comm _ _

/-- Exact total number of crossing edges, summed over every `a`-element
choice for the left side. -/
theorem sum_crossEdgeCount_balancedRightPart
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {V₀ U : Finset V} (hVU : Disjoint V₀ U)
    {a : ℕ} (ha0 : 1 ≤ a) (haV : a ≤ V₀.card) :
    (∑ A ∈ V₀.powersetCard a,
        crossEdgeCount G A (balancedRightPart V₀ U A)) =
      (V₀.card - 2).choose (a - 1) * #(G.interedges V₀ V₀) +
      (V₀.card - 1).choose (a - 1) * #(G.interedges V₀ U) := by
  classical
  calc
    (∑ A ∈ V₀.powersetCard a,
        crossEdgeCount G A (balancedRightPart V₀ U A)) =
        ∑ A ∈ V₀.powersetCard a,
          (#(G.interedges A (V₀ \ A)) + #(G.interedges A U)) := by
      apply Finset.sum_congr rfl
      intro A hA
      have hAV : A ⊆ V₀ := (Finset.mem_powersetCard.mp hA).1
      have hdisj := disjoint_balancedRightPart hAV hVU
      rw [crossEdgeCount_eq_card_interedges G A
        (balancedRightPart V₀ U A) hdisj]
      exact card_interedges_union_right_of_disjoint G
        (hVU.mono_left Finset.sdiff_subset)
    _ = (∑ A ∈ V₀.powersetCard a, #(G.interedges A (V₀ \ A))) +
        (∑ A ∈ V₀.powersetCard a, #(G.interedges A U)) := by
      rw [Finset.sum_add_distrib]
    _ = (V₀.card - 2).choose (a - 1) * #(G.interedges V₀ V₀) +
        (V₀.card - 1).choose (a - 1) * #(G.interedges V₀ U) := by
      rw [sum_card_interedges_powersetCard_sdiff G V₀ ha0 haV,
        sum_card_interedges_powersetCard_fixedRight G V₀ U ha0]

/-- Division-free averaged balanced-cut inequality.  Multiplying by the
number of ceiling-half subsets avoids any rational-valued expectation. -/
theorem choose_mul_edgeCount_le_twice_sum_balancedCuts
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {V₀ U : Finset V} (hVU : Disjoint V₀ U)
    (hcover : V₀ ∪ U = Finset.univ)
    (hU : ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U → ¬G.Adj x y)
    (hm : 2 ≤ V₀.card) :
    V₀.card.choose (ceilHalf V₀.card) * edgeCount G ≤
      2 * (∑ A ∈ V₀.powersetCard (ceilHalf V₀.card),
        crossEdgeCount G A (balancedRightPart V₀ U A)) := by
  let m := V₀.card
  let a := ceilHalf m
  let F := m.choose a
  let CI := (m - 2).choose (a - 1)
  let CU := (m - 1).choose (a - 1)
  let D := #(G.interedges V₀ V₀)
  let E := #(G.interedges V₀ U)
  let X := ∑ A ∈ V₀.powersetCard a,
    crossEdgeCount G A (balancedRightPart V₀ U A)
  have ha0 : 1 ≤ a := by
    dsimp only [a, m]
    simpa only [Nat.lt_iff_add_one_le, zero_add] using
      (ceilHalf_pos (m := V₀.card) (by omega))
  have haV : a ≤ V₀.card := by
    dsimp only [a, m]
    exact ceilHalf_le _
  have htotal : 2 * edgeCount G = D + 2 * E := by
    simpa only [D, E] using
      two_mul_edgeCount_eq_internalDarts_add_crossDarts G hVU hcover hU
  have hsum : X = CI * D + CU * E := by
    simpa only [X, CI, CU, D, E, a, m] using
      sum_crossEdgeCount_balancedRightPart G hVU ha0 haV
  have hI : F ≤ 4 * CI := by
    simpa only [F, CI, a, m] using
      choose_le_four_mul_choose_pred_pred_ceilHalf hm
  have hUcoeff : F ≤ 2 * CU := by
    simpa only [F, CU, a, m] using
      choose_le_twice_choose_pred_ceilHalf (show 0 < m by omega)
  have hID : F * D ≤ (4 * CI) * D := Nat.mul_le_mul_right D hI
  have hUE : (2 * F) * E ≤ (4 * CU) * E := by
    apply Nat.mul_le_mul_right E
    nlinarith
  have htwice : 2 * (F * edgeCount G) ≤ 2 * (2 * X) := by
    calc
      2 * (F * edgeCount G) = F * (2 * edgeCount G) := by ring
      _ = F * (D + 2 * E) := by rw [htotal]
      _ = F * D + (2 * F) * E := by ring
      _ ≤ (4 * CI) * D + (4 * CU) * E := Nat.add_le_add hID hUE
      _ = 2 * (2 * (CI * D + CU * E)) := by ring
      _ = 2 * (2 * X) := by rw [hsum]
  have haverage : F * edgeCount G ≤ 2 * X :=
    le_of_mul_le_mul_left htwice (by norm_num)
  simpa only [F, X, a, m] using haverage

/-- If `V₀` has at most one vertex, the partition `V₀ | U` already cuts
every edge: there are no loops inside `V₀` and `U` is independent. -/
theorem crossSubgraph_eq_of_card_le_one
    (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    {V₀ U : Finset V} (hcard : V₀.card ≤ 1)
    (hcover : V₀ ∪ U = Finset.univ)
    (hU : ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U → ¬G.Adj x y) :
    crossSubgraph G V₀ U = G := by
  apply le_antisymm (crossSubgraph_le G V₀ U)
  intro x y hxy
  refine ⟨hxy, ?_⟩
  have hx : x ∈ V₀ ∨ x ∈ U := by
    have : x ∈ V₀ ∪ U := by rw [hcover]; exact Finset.mem_univ x
    simpa only [Finset.mem_union] using this
  have hy : y ∈ V₀ ∨ y ∈ U := by
    have : y ∈ V₀ ∪ U := by rw [hcover]; exact Finset.mem_univ y
    simpa only [Finset.mem_union] using this
  rcases hx with hxV | hxU <;> rcases hy with hyV | hyU
  · have hxyEq := (Finset.card_le_one.mp hcard) x hxV y hyV
    exact (hxy.ne hxyEq).elim
  · exact Or.inl ⟨hxV, hyU⟩
  · exact Or.inr ⟨hxU, hyV⟩
  · exact (hU hxU hyU hxy).elim

/-- For the nontrivial case `|V₀| ≥ 2`, the finite average supplies one
ceiling-half subset whose cut contains at least half of all edges. -/
theorem exists_ceilingHalf_cut_of_two_le_card
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {V₀ U : Finset V} (hVU : Disjoint V₀ U)
    (hcover : V₀ ∪ U = Finset.univ)
    (hU : ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U → ¬G.Adj x y)
    (hm : 2 ≤ V₀.card) :
    ∃ A : Finset V,
      A ⊆ V₀ ∧ A.card = ceilHalf V₀.card ∧
        edgeCount G ≤
          2 * crossEdgeCount G A (balancedRightPart V₀ U A) := by
  classical
  let P := V₀.powersetCard (ceilHalf V₀.card)
  have hP : P.Nonempty := by
    dsimp only [P]
    exact Finset.powersetCard_nonempty.mpr (ceilHalf_le _)
  have havg := choose_mul_edgeCount_le_twice_sum_balancedCuts
    G hVU hcover hU hm
  have havg' : P.card * edgeCount G ≤
      2 * (∑ A ∈ P,
        crossEdgeCount G A (balancedRightPart V₀ U A)) := by
    simpa only [P, Finset.card_powersetCard] using havg
  have hex : ∃ A ∈ P, edgeCount G ≤
      2 * crossEdgeCount G A (balancedRightPart V₀ U A) := by
    by_contra hnone
    push Not at hnone
    have hltSum :
        (∑ A ∈ P,
          2 * crossEdgeCount G A (balancedRightPart V₀ U A)) <
        ∑ _A ∈ P, edgeCount G := by
      exact Finset.sum_lt_sum_of_nonempty hP fun A hA ↦ hnone A hA
    have hlt :
        2 * (∑ A ∈ P,
          crossEdgeCount G A (balancedRightPart V₀ U A)) <
        P.card * edgeCount G := by
      calc
        2 * (∑ A ∈ P,
            crossEdgeCount G A (balancedRightPart V₀ U A)) =
            ∑ A ∈ P,
              2 * crossEdgeCount G A (balancedRightPart V₀ U A) := by
          rw [Finset.mul_sum]
        _ < ∑ _A ∈ P, edgeCount G := hltSum
        _ = P.card * edgeCount G := by
          exact Finset.sum_const_nat fun _ _ ↦ rfl
    exact (not_lt_of_ge havg') hlt
  obtain ⟨A, hAP, hcut⟩ := hex
  have hA := Finset.mem_powersetCard.mp hAP
  exact ⟨A, hA.1, hA.2, hcut⟩

/-! ## BLS Lemma 4.5: the balanced-cut step -/

/-- A finite graph split as `V₀ ∪ U`, with `U` independent, admits the
balanced cut used at the start of BLS Lemma 4.5.  Besides the cardinality and
edge bound, the conclusion records the exact right-side formula, partition
facts, containment of `U`, and bipartiteness of the retained subgraph. -/
theorem exists_balancedCut_with_independent_right
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {V₀ U : Finset V} (hVU : Disjoint V₀ U)
    (hcover : V₀ ∪ U = Finset.univ)
    (hU : ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U → ¬G.Adj x y) :
    ∃ A B : Finset V,
      A ⊆ V₀ ∧
      B = balancedRightPart V₀ U A ∧
      A.card = (V₀.card + 1) / 2 ∧
      Disjoint A B ∧
      A ∪ B = Finset.univ ∧
      U ⊆ B ∧
      B \ U = V₀ \ A ∧
      (crossSubgraph G A B).IsBipartiteWith (A : Set V) (B : Set V) ∧
      edgeCount G ≤ 2 * crossEdgeCount G A B := by
  classical
  by_cases hsmall : V₀.card ≤ 1
  · let B := balancedRightPart V₀ U V₀
    have hdisj : Disjoint V₀ B :=
      disjoint_balancedRightPart Finset.Subset.rfl hVU
    have hunion : V₀ ∪ B = Finset.univ :=
      union_balancedRightPart Finset.Subset.rfl hcover
    have hgraph : crossSubgraph G V₀ B = G := by
      have hB : B = U := by
        ext x
        simp only [B, balancedRightPart, Finset.sdiff_self,
          Finset.empty_union]
      rw [hB]
      exact crossSubgraph_eq_of_card_le_one G hsmall hcover hU
    refine ⟨V₀, B, Finset.Subset.rfl, rfl, ?_, hdisj, hunion,
      subset_balancedRightPart_right V₀ U V₀,
      balancedRightPart_sdiff_right hVU,
      crossSubgraph_isBipartiteWith G hdisj, ?_⟩
    · omega
    · rw [crossEdgeCount, hgraph]
      omega
  · have hm : 2 ≤ V₀.card := by omega
    obtain ⟨A, hAV, hAcard, hcut⟩ :=
      exists_ceilingHalf_cut_of_two_le_card G hVU hcover hU hm
    let B := balancedRightPart V₀ U A
    have hdisj : Disjoint A B := disjoint_balancedRightPart hAV hVU
    refine ⟨A, B, hAV, rfl, ?_, hdisj,
      union_balancedRightPart hAV hcover,
      subset_balancedRightPart_right V₀ U A,
      balancedRightPart_sdiff_right hVU,
      crossSubgraph_isBipartiteWith G hdisj, hcut⟩
    simpa only [ceilHalf] using hAcard

end LeanCo.SizeRamsey
