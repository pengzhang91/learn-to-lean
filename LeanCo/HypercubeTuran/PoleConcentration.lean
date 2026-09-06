import LeanCo.HypercubeTuran.BaseGraph
import Mathlib.Tactic

/-!
# From cut expansion to pole concentration

This file converts the finite cut inequalities in `IsCombinatorialBase` into
the Hamming-distance concentration statement used by the avoidance argument.
-/

open scoped SimpleGraph symmDiff BigOperators

namespace LeanCo.HypercubeTuran

open Finset SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma card_symmDiff_add_twice_inter {ι : Type*} [DecidableEq ι]
    (A B : Finset ι) :
    #(A ∆ B) + 2 * #(A ∩ B) = #A + #B := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  · have hA := Finset.card_sdiff_add_card_inter A B
    have hB := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm B A] at hB
    omega
  · exact disjoint_sdiff_sdiff

lemma card_symmDiff_eq_card_sdiff_add_card_sdiff {ι : Type*}
    [DecidableEq ι] (A B : Finset ι) :
    #(A ∆ B) = #(A \ B) + #(B \ A) := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  exact disjoint_sdiff_sdiff

lemma card_mod_two_eq_of_card_symmDiff_eq_two {ι : Type*} [DecidableEq ι]
    {A B : Finset ι} (h : #(A ∆ B) = 2) :
    #A % 2 = #B % 2 := by
  have hc := card_symmDiff_add_twice_inter A B
  omega

lemma even_card_symmDiff_of_card_mod_two_eq {ι : Type*} [DecidableEq ι]
    {A B : Finset ι} (h : #A % 2 = #B % 2) :
    Even #(A ∆ B) := by
  have hc := card_symmDiff_add_twice_inter A B
  rw [Nat.even_iff]
  omega

lemma card_mod_two_eq_along_walk {G : SimpleGraph V} {ι : Type*}
    [DecidableEq ι] (A : V → Finset ι)
    (hedge : ∀ ⦃x y : V⦄, G.Adj x y → #(A x ∆ A y) = 2)
    {x y : V} (p : G.Walk x y) :
    #(A x) % 2 = #(A y) % 2 := by
  induction p with
  | nil => rfl
  | @cons x y z hxy p ih =>
      exact (card_mod_two_eq_of_card_symmDiff_eq_two (hedge hxy)).trans ih

lemma even_pole_distance_of_connected {G : SimpleGraph V} {ι : Type*}
    [DecidableEq ι] (hconn : G.Connected) (A : V → Finset ι)
    (hedge : ∀ ⦃x y : V⦄, G.Adj x y → #(A x ∆ A y) = 2)
    (x y : V) :
    Even #(A x ∆ A y) := by
  obtain ⟨p⟩ := hconn x y
  exact even_card_symmDiff_of_card_mod_two_eq
    (card_mod_two_eq_along_walk A hedge p)

lemma cutSize_eq_card_ordered_crossing (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    cutSize G S =
      #(Finset.univ.filter fun xy : V × V =>
        xy.1 ∈ S ∧ xy.2 ∉ S ∧ G.Adj xy.1 xy.2) := by
  classical
  have hinner (x : V) :
      #(G.neighborFinset x \ S) =
        ∑ y : V, if y ∉ S ∧ G.Adj x y then 1 else 0 := by
    rw [Finset.card_eq_sum_ite
      (Finset.subset_univ (G.neighborFinset x \ S))]
    apply Finset.sum_congr rfl
    intro y _
    simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
    by_cases hyS : y ∈ S <;> by_cases hxy : G.Adj x y <;> simp_all
  rw [cutSize]
  simp_rw [hinner]
  have hS : Finset.univ.filter (fun x : V => x ∈ S) = S := by
    ext x
    simp
  rw [← hS, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ S
  · simp only [hx, if_true]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ S <;> by_cases hxy : G.Adj x y <;> simp_all
  · simp [hx]

lemma card_mul_compl_card_eq_card_ordered_crossing (S : Finset V) :
    #S * (Fintype.card V - #S) =
      #(Finset.univ.filter fun xy : V × V => xy.1 ∈ S ∧ xy.2 ∉ S) := by
  classical
  have hfilter :
      (Finset.univ.filter fun xy : V × V => xy.1 ∈ S ∧ xy.2 ∉ S) =
        S ×ˢ (Finset.univ \ S) := by
    ext xy
    simp
  rw [hfilter, Finset.card_product, Finset.card_sdiff_of_subset
    (Finset.subset_univ S), Finset.card_univ]

lemma sum_card_filter_comm {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (p : α → β → Prop)
    [DecidableRel p] :
    (∑ a : α, #(Finset.univ.filter fun b : β => p a b)) =
      ∑ b : β, #(Finset.univ.filter fun a : α => p a b) := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- The side of the coordinate cut on which coordinate `i` is present. -/
def coordinateSide {ι : Type*} [DecidableEq ι]
    (A : V → Finset ι) (i : ι) : Finset V :=
  Finset.univ.filter fun v => i ∈ A v

@[simp]
lemma mem_coordinateSide {ι : Type*} [DecidableEq ι]
    {A : V → Finset ι} {i : ι} {v : V} :
    v ∈ coordinateSide A i ↔ i ∈ A v := by
  simp [coordinateSide]

/-- Double-counting coordinate-separated ordered pairs. -/
lemma sum_coordinate_products_eq_ordered_sdiff {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : V → Finset ι) :
    (∑ i : ι, #(coordinateSide A i) *
        (Fintype.card V - #(coordinateSide A i))) =
      ∑ xy : V × V, #(A xy.1 \ A xy.2) := by
  classical
  calc
    (∑ i : ι, #(coordinateSide A i) *
        (Fintype.card V - #(coordinateSide A i))) =
        ∑ i : ι, #(Finset.univ.filter fun xy : V × V =>
          xy.1 ∈ coordinateSide A i ∧ xy.2 ∉ coordinateSide A i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact card_mul_compl_card_eq_card_ordered_crossing (coordinateSide A i)
    _ = ∑ xy : V × V, #(Finset.univ.filter fun i : ι =>
          xy.1 ∈ coordinateSide A i ∧ xy.2 ∉ coordinateSide A i) := by
            exact sum_card_filter_comm
              (fun i (xy : V × V) =>
                xy.1 ∈ coordinateSide A i ∧ xy.2 ∉ coordinateSide A i)
    _ = ∑ xy : V × V, #(A xy.1 \ A xy.2) := by
            apply Finset.sum_congr rfl
            intro xy _
            congr 1
            ext i
            simp [Finset.mem_sdiff]

/-- Double-counting coordinate cuts, restricted to graph edges. -/
lemma sum_coordinate_cuts_eq_ordered_adj_sdiff (G : SimpleGraph V)
    [DecidableRel G.Adj] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : V → Finset ι) :
    (∑ i : ι, cutSize G (coordinateSide A i)) =
      ∑ xy : V × V, if G.Adj xy.1 xy.2 then #(A xy.1 \ A xy.2) else 0 := by
  classical
  calc
    (∑ i : ι, cutSize G (coordinateSide A i)) =
        ∑ i : ι, #(Finset.univ.filter fun xy : V × V =>
          xy.1 ∈ coordinateSide A i ∧ xy.2 ∉ coordinateSide A i ∧
            G.Adj xy.1 xy.2) := by
              apply Finset.sum_congr rfl
              intro i _
              exact cutSize_eq_card_ordered_crossing G (coordinateSide A i)
    _ = ∑ xy : V × V, #(Finset.univ.filter fun i : ι =>
          xy.1 ∈ coordinateSide A i ∧ xy.2 ∉ coordinateSide A i ∧
            G.Adj xy.1 xy.2) := by
              exact sum_card_filter_comm
                (fun i (xy : V × V) =>
                  xy.1 ∈ coordinateSide A i ∧ xy.2 ∉ coordinateSide A i ∧
                    G.Adj xy.1 xy.2)
    _ = ∑ xy : V × V,
        if G.Adj xy.1 xy.2 then #(A xy.1 \ A xy.2) else 0 := by
              apply Finset.sum_congr rfl
              intro xy _
              by_cases hxy : G.Adj xy.1 xy.2
              · rw [if_pos hxy]
                congr 1
                ext i
                simp [Finset.mem_sdiff, hxy]
              · rw [if_neg hxy]
                simp [hxy]

lemma ordered_sdiff_sum_symm {ι : Type*} [DecidableEq ι]
    (A : V → Finset ι) :
    (∑ xy : V × V, #(A xy.1 \ A xy.2)) =
      ∑ xy : V × V, #(A xy.2 \ A xy.1) := by
  classical
  calc
    (∑ xy : V × V, #(A xy.1 \ A xy.2)) =
        ∑ x : V, ∑ y : V, #(A x \ A y) := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ y : V, ∑ x : V, #(A x \ A y) := Finset.sum_comm
    _ = ∑ xy : V × V, #(A xy.2 \ A xy.1) := by
          rw [← Finset.univ_product_univ, Finset.sum_product]

/-- The ordered total Hamming distance is twice the one-way difference
count, hence twice the sum of the coordinate cut products. -/
lemma ordered_symmDiff_sum_eq_two_mul_coordinate_products {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : V → Finset ι) :
    (∑ xy : V × V, #(A xy.1 ∆ A xy.2)) =
      2 * (∑ i : ι, #(coordinateSide A i) *
        (Fintype.card V - #(coordinateSide A i))) := by
  have hsymm := ordered_sdiff_sum_symm A
  rw [sum_coordinate_products_eq_ordered_sdiff A]
  calc
    (∑ xy : V × V, #(A xy.1 ∆ A xy.2)) =
        ∑ xy : V × V,
          (#(A xy.1 \ A xy.2) + #(A xy.2 \ A xy.1)) := by
            apply Finset.sum_congr rfl
            intro xy _
            exact card_symmDiff_eq_card_sdiff_add_card_sdiff _ _
    _ = (∑ xy : V × V, #(A xy.1 \ A xy.2)) +
          ∑ xy : V × V, #(A xy.2 \ A xy.1) := by
            exact Finset.sum_add_distrib
    _ = 2 * (∑ xy : V × V, #(A xy.1 \ A xy.2)) := by
            rw [← hsymm]
            omega

lemma ordered_adj_sdiff_sum_symm (G : SimpleGraph V)
    [DecidableRel G.Adj] {ι : Type*} [DecidableEq ι]
    (A : V → Finset ι) :
    (∑ xy : V × V,
        if G.Adj xy.1 xy.2 then #(A xy.1 \ A xy.2) else 0) =
      ∑ xy : V × V,
        if G.Adj xy.1 xy.2 then #(A xy.2 \ A xy.1) else 0 := by
  classical
  calc
    (∑ xy : V × V,
        if G.Adj xy.1 xy.2 then #(A xy.1 \ A xy.2) else 0) =
        ∑ x : V, ∑ y : V,
          if G.Adj x y then #(A x \ A y) else 0 := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ y : V, ∑ x : V,
          if G.Adj x y then #(A x \ A y) else 0 := Finset.sum_comm
    _ = ∑ x : V, ∑ y : V,
          if G.Adj x y then #(A y \ A x) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            by_cases hxy : G.Adj x y
            · simp [hxy, G.adj_comm]
            · simp [hxy, G.adj_comm]
    _ = ∑ xy : V × V,
        if G.Adj xy.1 xy.2 then #(A xy.2 \ A xy.1) else 0 := by
            rw [← Finset.univ_product_univ, Finset.sum_product]

/-- When every graph edge is sent to Hamming distance two, each undirected
edge contributes exactly two to the sum of the coordinate cuts. -/
lemma ordered_adj_sdiff_sum_eq_twice_edgeCount (G : SimpleGraph V)
    [DecidableRel G.Adj] {ι : Type*} [DecidableEq ι]
    (A : V → Finset ι)
    (hedge : ∀ ⦃x y : V⦄, G.Adj x y → #(A x ∆ A y) = 2) :
    (∑ xy : V × V,
        if G.Adj xy.1 xy.2 then #(A xy.1 \ A xy.2) else 0) =
      2 * graphEdgeCount G := by
  classical
  let T := ∑ xy : V × V,
    if G.Adj xy.1 xy.2 then #(A xy.1 \ A xy.2) else 0
  let T' := ∑ xy : V × V,
    if G.Adj xy.1 xy.2 then #(A xy.2 \ A xy.1) else 0
  have hsymm : T = T' := ordered_adj_sdiff_sum_symm G A
  have hadd : T + T' =
      ∑ xy : V × V, if G.Adj xy.1 xy.2 then 2 else 0 := by
    dsimp only [T, T']
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro xy _
    by_cases hxy : G.Adj xy.1 xy.2
    · simp only [hxy, if_true]
      rw [← card_symmDiff_eq_card_sdiff_add_card_sdiff]
      exact hedge hxy
    · simp [hxy]
  have hcount :
      (∑ xy : V × V, if G.Adj xy.1 xy.2 then 2 else 0) =
        4 * graphEdgeCount G := by
    have hbool :
        (∑ xy : V × V, if G.Adj xy.1 xy.2 then (1 : ℕ) else 0) =
          #(Finset.univ.filter fun xy : V × V => G.Adj xy.1 xy.2) := by
      exact Finset.sum_boole (fun xy : V × V => G.Adj xy.1 xy.2) Finset.univ
    calc
      (∑ xy : V × V, if G.Adj xy.1 xy.2 then 2 else 0) =
          2 * #(Finset.univ.filter fun xy : V × V => G.Adj xy.1 xy.2) := by
            calc
              (∑ xy : V × V, if G.Adj xy.1 xy.2 then 2 else 0) =
                  2 * (∑ xy : V × V,
                    if G.Adj xy.1 xy.2 then 1 else 0) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro xy _
                      by_cases hxy : G.Adj xy.1 xy.2 <;> simp [hxy]
              _ = 2 * #(Finset.univ.filter fun xy : V × V =>
                    G.Adj xy.1 xy.2) := by
                      rw [hbool]
      _ = 4 * graphEdgeCount G := by
            rw [← G.two_mul_card_edgeFinset]
            simp only [graphEdgeCount]
            omega
  rw [hcount] at hadd
  change T = 2 * graphEdgeCount G
  omega

lemma sum_coordinate_cuts_eq_twice_edgeCount (G : SimpleGraph V)
    [DecidableRel G.Adj] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : V → Finset ι)
    (hedge : ∀ ⦃x y : V⦄, G.Adj x y → #(A x ∆ A y) = 2) :
    (∑ i : ι, cutSize G (coordinateSide A i)) =
      2 * graphEdgeCount G := by
  rw [sum_coordinate_cuts_eq_ordered_adj_sdiff G A]
  exact ordered_adj_sdiff_sum_eq_twice_edgeCount G A hedge

/-- The two finite pseudorandom inequalities imply a global bound on the
ordered sum of all pairwise Hamming distances between poles. -/
lemma ordered_symmDiff_sum_le_of_combinatorialBase (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hbase : IsCombinatorialBase G d)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : V → Finset ι)
    (hplacement : IsPolePlacement G A) :
    7 * (∑ xy : V × V, #(A xy.1 ∆ A xy.2)) ≤
      25 * Fintype.card V * Fintype.card V := by
  let P := ∑ i : ι, #(coordinateSide A i) *
    (Fintype.card V - #(coordinateSide A i))
  let C := ∑ i : ι, cutSize G (coordinateSide A i)
  let M := graphEdgeCount G
  let N := Fintype.card V
  let D := ∑ xy : V × V, #(A xy.1 ∆ A xy.2)
  have hcutEach (i : ι) :
      7 * d * #(coordinateSide A i) *
          (Fintype.card V - #(coordinateSide A i)) ≤
        5 * Fintype.card V * cutSize G (coordinateSide A i) :=
    hbase.cut_expansion (coordinateSide A i)
  have hcutSum : 7 * d * P ≤ 5 * N * C := by
    have hs := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset ι)) =>
      hcutEach i
    dsimp only [P, C, N]
    simpa only [Finset.mul_sum, Nat.mul_assoc] using hs
  have hC : C = 2 * M := by
    dsimp only [C, M]
    exact sum_coordinate_cuts_eq_twice_edgeCount G A hplacement.2
  have hD : D = 2 * P := by
    dsimp only [D, P]
    exact ordered_symmDiff_sum_eq_two_mul_coordinate_products A
  have hM : 4 * M ≤ 5 * d * N := by
    simpa only [M, N, HasControlledEdgeCount] using hbase.edgeCount_control
  have hcutScaled : 2 * (7 * d * P) ≤ 2 * (5 * N * C) :=
    Nat.mul_le_mul_left 2 hcutSum
  have hedgeScaled : (5 * N) * (4 * M) ≤ (5 * N) * (5 * d * N) :=
    Nat.mul_le_mul_left (5 * N) hM
  have hwithD : d * (7 * D) ≤ d * (25 * N * N) := by
    calc
      d * (7 * D) = 2 * (7 * d * P) := by rw [hD]; ring
      _ ≤ 2 * (5 * N * C) := hcutScaled
      _ = (5 * N) * (4 * M) := by rw [hC]; ring
      _ ≤ (5 * N) * (5 * d * N) := hedgeScaled
      _ = d * (25 * N * N) := by ring
  have hcancel : 7 * D ≤ 25 * N * N :=
    Nat.le_of_mul_le_mul_left hwithD hbase.d_pos
  dsimp only [D, N] at hcancel
  exact hcancel

/-- Every combinatorial base has the pole-concentration property required by
the parity-colouring argument. -/
theorem IsCombinatorialBase.hasPoleConcentration (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hbase : IsCombinatorialBase G d) :
    HasPoleConcentration G := by
  intro ι _instFintype _instDecidableEq A hplacement
  have hglobal :=
    ordered_symmDiff_sum_le_of_combinatorialBase G hbase A hplacement
  have hcardPos : 0 < Fintype.card V :=
    lt_of_lt_of_le (by decide : 0 < 10) hbase.ten_le_card
  letI : Nonempty V := Fintype.card_pos_iff.mp hcardPos
  have hrows :
      (∑ w : V, ∑ v : V, #(A v ∆ A w)) =
        ∑ xy : V × V, #(A xy.1 ∆ A xy.2) := by
    calc
      (∑ w : V, ∑ v : V, #(A v ∆ A w)) =
          ∑ v : V, ∑ w : V, #(A v ∆ A w) := Finset.sum_comm
      _ = ∑ xy : V × V, #(A xy.1 ∆ A xy.2) := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
  have hsumRows :
      (∑ w : V, 7 * (∑ v : V, #(A v ∆ A w))) ≤
        ∑ _w : V, 25 * Fintype.card V := by
    calc
      (∑ w : V, 7 * (∑ v : V, #(A v ∆ A w))) =
          7 * (∑ w : V, ∑ v : V, #(A v ∆ A w)) := by
            simpa only using
              (Finset.mul_sum (Finset.univ : Finset V)
                (fun w : V => ∑ v : V, #(A v ∆ A w)) 7).symm
      _ = 7 * (∑ xy : V × V, #(A xy.1 ∆ A xy.2)) := by
            exact congrArg (fun n : ℕ => 7 * n) hrows
      _ ≤ 25 * Fintype.card V * Fintype.card V := hglobal
      _ = ∑ _w : V, 25 * Fintype.card V := by
            simp [Nat.mul_comm]
  obtain ⟨w, _hwuniv, hw⟩ :=
    Finset.exists_le_of_sum_le (s := (Finset.univ : Finset V))
      Finset.univ_nonempty hsumRows
  refine ⟨w, hw, ?_⟩
  intro v
  exact even_pole_distance_of_connected hbase.connected A hplacement.2 v w

end LeanCo.HypercubeTuran
