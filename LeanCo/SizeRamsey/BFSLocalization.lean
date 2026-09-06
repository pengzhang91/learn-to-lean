import LeanCo.SizeRamsey.BFSGrowth
import LeanCo.SizeRamsey.DensityCore
import LeanCo.SizeRamsey.HostExpansion
import Mathlib.Combinatorics.SimpleGraph.Density

/-!
# Localising density in two consecutive BFS levels

This file formalizes Lemma 2.2 of Wang--Wang.  The proof stops at the first
BFS ball whose size grows by a factor at most two, proves that the induced
ball is dense, and then averages its edges over consecutive level pairs.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The union of two consecutive distance levels. -/
noncomputable def twoLevelFinset (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] (root : V) (i : Nat) : Finset V :=
  distanceLevelFinset G root i ∪ distanceLevelFinset G root (i + 1)

/-- If a graph has no edges internal to either of two disjoint finite sets,
then the edges induced by their union are counted exactly once by oriented
edges from the first set to the second. -/
theorem spannedEdgeCount_union_eq_card_interedges
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (A B : Finset V) (hAB : Disjoint A B)
    (hA : ∀ ⦃v⦄, v ∈ A → ∀ ⦃w⦄, w ∈ A → ¬ G.Adj v w)
    (hB : ∀ ⦃v⦄, v ∈ B → ∀ ⦃w⦄, w ∈ B → ¬ G.Adj v w) :
    spannedEdgeCount G ((A ∪ B : Finset V) : Set V) =
      #(G.interedges A B) := by
  classical
  rw [spannedEdgeCount, edgeCount_eq_card_edgeFinset]
  symm
  let U : Finset V := A ∪ B
  let f : (p : V × V) → p ∈ G.interedges A B → Sym2 (U : Set V) :=
    fun p hp =>
      s(⟨p.1, Finset.mem_union_left B
          ((G.mem_interedges_iff.mp hp).1)⟩,
        ⟨p.2, Finset.mem_union_right A
          ((G.mem_interedges_iff.mp hp).2.1)⟩)
  refine Finset.card_bij f ?_ ?_ ?_
  · intro p hp
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (G.mem_interedges_iff.mp hp).2.2
  · intro p hp q hq heq
    rw [Sym2.eq, Sym2.rel_iff'] at heq
    rcases heq with heq | heq
    · apply Prod.ext
      · exact congrArg (fun z : ↥(U : Set V) × ↥(U : Set V) => z.1.val) heq
      · exact congrArg (fun z : ↥(U : Set V) × ↥(U : Set V) => z.2.val) heq
    · have hpA : p.1 ∈ A := (G.mem_interedges_iff.mp hp).1
      have hpB : p.2 ∈ B := (G.mem_interedges_iff.mp hp).2.1
      have hqA : q.1 ∈ A := (G.mem_interedges_iff.mp hq).1
      have hqB : q.2 ∈ B := (G.mem_interedges_iff.mp hq).2.1
      have hp1q2 : p.1 = q.2 :=
        congrArg (fun z : ↥(U : Set V) × ↥(U : Set V) => z.1.val) heq
      exact ((Finset.disjoint_left.mp hAB) hpA (hp1q2 ▸ hqB)).elim
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : G.Adj x.val y.val := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact he
      have hx : x.val ∈ A ∨ x.val ∈ B := by simpa [U] using x.prop
      have hy : y.val ∈ A ∨ y.val ∈ B := by simpa [U] using y.prop
      rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
      · exact (hA hxA hyA hxy).elim
      · refine ⟨(x.val, y.val), ?_, ?_⟩
        · exact G.mem_interedges_iff.mpr ⟨hxA, hyB, hxy⟩
        · change s(⟨x.val, _⟩, ⟨y.val, _⟩) = s(x, y)
          rfl
      · refine ⟨(y.val, x.val), ?_, ?_⟩
        · exact G.mem_interedges_iff.mpr ⟨hyA, hxB, hxy.symm⟩
        · change s(⟨y.val, _⟩, ⟨x.val, _⟩) = s(x, y)
          rw [Sym2.eq_swap]
      · exact (hB hxB hyB hxy).elim

/-- In a connected bipartite graph, the graph induced by two consecutive
levels has exactly the edges oriented from the lower level to the upper one. -/
theorem spannedEdgeCount_twoLevel_eq_card_interedges
    (hbip : G.IsBipartite) (hG : G.Connected)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (i : Nat) :
    spannedEdgeCount G ((twoLevelFinset G root i : Finset V) : Set V) =
      #(G.interedges (distanceLevelFinset G root i)
        (distanceLevelFinset G root (i + 1))) := by
  unfold twoLevelFinset
  apply spannedEdgeCount_union_eq_card_interedges
  · exact distanceLevelFinset_disjoint root (by omega)
  · intro v hv w hw
    apply not_adj_of_dist_eq_of_bipartite hbip hG
    rw [(mem_distanceLevelFinset root).mp hv,
      (mem_distanceLevelFinset root).mp hw]
  · intro v hv w hw
    apply not_adj_of_dist_eq_of_bipartite hbip hG
    rw [(mem_distanceLevelFinset root).mp hv,
      (mem_distanceLevelFinset root).mp hw]

/-- The oriented edges between consecutive levels below radius `q`. -/
noncomputable def consecutiveInteredgesFinset (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (q : Nat) : Finset (V × V) :=
  (Finset.range q).biUnion fun i =>
    G.interedges (distanceLevelFinset G root i)
      (distanceLevelFinset G root (i + 1))

/-- Every edge induced by the radius-`q` ball has a unique orientation from
level `i` to level `i+1`, for some `i < q`. -/
theorem spannedEdgeCount_closedBall_eq_card_consecutiveInteredges
    (hbip : G.IsBipartite) (hG : G.Connected)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (q : Nat) :
    spannedEdgeCount G ((closedBallFinset G root q : Finset V) : Set V) =
      #(consecutiveInteredgesFinset G root q) := by
  classical
  rw [spannedEdgeCount, edgeCount_eq_card_edgeFinset]
  symm
  let B : Finset V := closedBallFinset G root q
  let C : Finset (V × V) := consecutiveInteredgesFinset G root q
  let f : (p : V × V) → p ∈ C → Sym2 (B : Set V) :=
    fun p hp => s(⟨p.1, by
      rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hip⟩
      change p.1 ∈ closedBallFinset G root q
      rw [mem_closedBallFinset]
      have hlevel := (G.mem_interedges_iff.mp hip).1
      rw [(mem_distanceLevelFinset root).mp hlevel]
      exact (Finset.mem_range.mp hi).le⟩,
    ⟨p.2, by
      rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hip⟩
      change p.2 ∈ closedBallFinset G root q
      rw [mem_closedBallFinset]
      have hlevel := (G.mem_interedges_iff.mp hip).2.1
      rw [(mem_distanceLevelFinset root).mp hlevel]
      exact Finset.mem_range.mp hi⟩)
  refine Finset.card_bij f ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hip⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (G.mem_interedges_iff.mp hip).2.2
  · intro p hp r hr heq
    rw [Sym2.eq, Sym2.rel_iff'] at heq
    rcases heq with heq | heq
    · apply Prod.ext
      · exact congrArg (fun z : ↥(B : Set V) × ↥(B : Set V) => z.1.val) heq
      · exact congrArg (fun z : ↥(B : Set V) × ↥(B : Set V) => z.2.val) heq
    · rcases Finset.mem_biUnion.mp hp with ⟨i, hi, hip⟩
      rcases Finset.mem_biUnion.mp hr with ⟨j, hj, hjr⟩
      have hpLo := (mem_distanceLevelFinset root).mp
        (G.mem_interedges_iff.mp hip).1
      have hpHi := (mem_distanceLevelFinset root).mp
        (G.mem_interedges_iff.mp hip).2.1
      have hrLo := (mem_distanceLevelFinset root).mp
        (G.mem_interedges_iff.mp hjr).1
      have hrHi := (mem_distanceLevelFinset root).mp
        (G.mem_interedges_iff.mp hjr).2.1
      have hfst : p.1 = r.2 :=
        congrArg (fun z : ↥(B : Set V) × ↥(B : Set V) => z.1.val) heq
      have hsnd : p.2 = r.1 :=
        congrArg (fun z : ↥(B : Set V) × ↥(B : Set V) => z.2.val) heq
      have := congrArg (G.dist root) hfst
      have := congrArg (G.dist root) hsnd
      omega
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : G.Adj x.val y.val := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact he
      have hxB : x.val ∈ closedBallFinset G root q := x.prop
      have hyB : y.val ∈ closedBallFinset G root q := y.prop
      have hxlev : x.val ∈ distanceLevelFinset G root (G.dist root x.val) := by
        simp
      have hylev : y.val ∈ distanceLevelFinset G root (G.dist root y.val) := by
        simp
      rcases adj_distanceLevel_consecutive_of_bipartite hbip hG root
          hxlev hylev hxy with hxyDist | hyxDist
      · let p : V × V := (x.val, y.val)
        have hlow : G.dist root x.val < q := by
          rw [mem_closedBallFinset] at hyB
          omega
        have hp : p ∈ C := by
          apply Finset.mem_biUnion.mpr
          refine ⟨G.dist root x.val, Finset.mem_range.mpr hlow, ?_⟩
          exact G.mem_interedges_iff.mpr ⟨hxlev, by simpa [hxyDist], hxy⟩
        refine ⟨p, hp, ?_⟩
        change s(⟨x.val, _⟩, ⟨y.val, _⟩) = s(x, y)
        rfl
      · let p : V × V := (y.val, x.val)
        have hlow : G.dist root y.val < q := by
          rw [mem_closedBallFinset] at hxB
          omega
        have hp : p ∈ C := by
          apply Finset.mem_biUnion.mpr
          refine ⟨G.dist root y.val, Finset.mem_range.mpr hlow, ?_⟩
          exact G.mem_interedges_iff.mpr ⟨hylev, by simpa [hyxDist], hxy.symm⟩
        refine ⟨p, hp, ?_⟩
        change s(⟨y.val, _⟩, ⟨x.val, _⟩) = s(x, y)
        rw [Sym2.eq_swap]

/-- The edge count inside a BFS ball is at most the sum of the edge counts
inside its consecutive two-level graphs. -/
theorem spannedEdgeCount_closedBall_le_sum_twoLevel
    (hbip : G.IsBipartite) (hG : G.Connected)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (q : Nat) :
    spannedEdgeCount G ((closedBallFinset G root q : Finset V) : Set V) ≤
      ∑ i ∈ Finset.range q,
        spannedEdgeCount G ((twoLevelFinset G root i : Finset V) : Set V) := by
  rw [spannedEdgeCount_closedBall_eq_card_consecutiveInteredges hbip hG]
  calc
    #(consecutiveInteredgesFinset G root q) ≤
        ∑ i ∈ Finset.range q,
          #(G.interedges (distanceLevelFinset G root i)
            (distanceLevelFinset G root (i + 1))) := by
      exact Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range q,
          spannedEdgeCount G ((twoLevelFinset G root i : Finset V) : Set V) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (spannedEdgeCount_twoLevel_eq_card_interedges hbip hG root i).symm

/-- A vertex of the radius-`q` ball occurs in at most two of the consecutive
level pairs indexed below `q`.  This is the weighted denominator estimate in
the averaging step of Lemma 2.2. -/
theorem sum_card_twoLevel_le_twice_closedBall
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (root : V) (q : Nat) :
    (∑ i ∈ Finset.range q, #(twoLevelFinset G root i)) ≤
      2 * #(closedBallFinset G root q) := by
  classical
  let O : Finset (Σ _i : Nat, V) :=
    (Finset.range q).sigma fun i => twoLevelFinset G root i
  let B : Finset V := closedBallFinset G root q
  let T : Finset (V × Bool) := B ×ˢ Finset.univ
  let tag : (Σ _i : Nat, V) → Bool := fun z =>
    if z.2 ∈ distanceLevelFinset G root z.1 then false else true
  let f : (Σ _i : Nat, V) → V × Bool := fun z => (z.2, tag z)
  have hmaps : Set.MapsTo f (O : Set (Σ _i : Nat, V)) (T : Set (V × Bool)) := by
    intro z hz
    have hz' : z.1 ∈ Finset.range q ∧ z.2 ∈ twoLevelFinset G root z.1 := by
      simpa [O] using hz
    change (z.2, tag z) ∈ B ×ˢ (Finset.univ : Finset Bool)
    rw [Finset.mem_product]
    constructor
    · change z.2 ∈ closedBallFinset G root q
      rw [mem_closedBallFinset]
      have hidx : z.1 < q := Finset.mem_range.mp hz'.1
      rcases (Finset.mem_union.mp hz'.2) with hlo | hhi
      · rw [(mem_distanceLevelFinset root).mp hlo]
        exact hidx.le
      · rw [(mem_distanceLevelFinset root).mp hhi]
        exact hidx
    · exact Finset.mem_univ _
  have hinj : Set.InjOn f (O : Set (Σ _i : Nat, V)) := by
    rintro ⟨i, v⟩ hiv ⟨j, w⟩ hjw hfw
    have hiv' : i ∈ Finset.range q ∧ v ∈ twoLevelFinset G root i := by
      simpa [O] using hiv
    have hjw' : j ∈ Finset.range q ∧ w ∈ twoLevelFinset G root j := by
      simpa [O] using hjw
    have hvw : v = w := congrArg Prod.fst hfw
    have htag : tag ⟨i, v⟩ = tag ⟨j, w⟩ := congrArg Prod.snd hfw
    subst w
    have hivLevels : v ∈ distanceLevelFinset G root i ∨
        v ∈ distanceLevelFinset G root (i + 1) := by
      simpa [twoLevelFinset] using Finset.mem_union.mp hiv'.2
    have hjvLevels : v ∈ distanceLevelFinset G root j ∨
        v ∈ distanceLevelFinset G root (j + 1) := by
      simpa [twoLevelFinset] using Finset.mem_union.mp hjw'.2
    by_cases hi : v ∈ distanceLevelFinset G root i
    · by_cases hj : v ∈ distanceLevelFinset G root j
      · have hdi := (mem_distanceLevelFinset root).mp hi
        have hdj := (mem_distanceLevelFinset root).mp hj
        have hij : i = j := by omega
        exact Sigma.ext hij (by simp)
      · have hfalse : (false : Bool) = true := by
          simpa only [tag, if_pos hi, if_neg hj] using htag
        exact Bool.noConfusion hfalse
    · have hi' := hivLevels.resolve_left hi
      by_cases hj : v ∈ distanceLevelFinset G root j
      · have hfalse : (true : Bool) = false := by
          simpa only [tag, if_neg hi, if_pos hj] using htag
        exact Bool.noConfusion hfalse
      · have hj' := hjvLevels.resolve_left hj
        have hdi := (mem_distanceLevelFinset root).mp hi'
        have hdj := (mem_distanceLevelFinset root).mp hj'
        have hij : i = j := by omega
        exact Sigma.ext hij (by simp)
  calc
    (∑ i ∈ Finset.range q, #(twoLevelFinset G root i)) = #O := by
      exact (Finset.card_sigma (Finset.range q) fun i =>
        twoLevelFinset G root i).symm
    _ ≤ #T := Finset.card_le_card_of_injOn f hmaps hinj
    _ = 2 * #(closedBallFinset G root q) := by
      simp [T, B, Nat.mul_comm]

/-- The ball at the first slow-growth radius has average degree strictly
greater than `4*d` when the ambient minimum degree is strictly greater than
`8*d`. -/
theorem firstSlowBall_hasAverageDegreeGreaterThan_four
    (hG : G.Connected) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (d : Nat)
    (hmin : HasMinimumDegreeGreaterThan G (8 * d)) :
    HasAverageDegreeGreaterThan
      (G.induce ((closedBallFinset G root (firstSlowBall G hG root) :
        Finset V) : Set V)) (4 * d) := by
  classical
  let q := firstSlowBall G hG root
  let S : Finset V := closedBallFinset G root (q - 1)
  let U : Finset V := closedBallFinset G root q
  have hqpos : 0 < q := firstSlowBall_pos G hG root
  have hslow : #U ≤ 2 * #S := by
    simpa [q, S, U] using (firstSlowBall_spec G hG root).2
  have hSU : S ⊆ U := by
    exact closedBallFinset_mono root (by omega)
  have hclosed : ∀ v ∈ S, G.neighborSet v ⊆ (U : Set V) := by
    intro v hv w hvw
    have hadj : G.Adj v w := (G.mem_neighborSet v w).mp hvw
    have hw := adj_mem_closedBallFinset_succ root hv hadj
    have hsucc : q - 1 + 1 = q := by omega
    simpa [U, hsucc] using hw
  have hrootS : root ∈ S := by
    change root ∈ closedBallFinset G root (q - 1)
    rw [mem_closedBallFinset]
    simp
  have hdegreeStrict : (8 * d) * #S < ∑ v ∈ S, G.degree v := by
    calc
      (8 * d) * #S = ∑ _v ∈ S, 8 * d := by simp [Nat.mul_comm]
      _ < ∑ v ∈ S, G.degree v := by
        apply Finset.sum_lt_sum
        · intro v hv
          exact (hmin v).le
        · exact ⟨root, hrootS, hmin root⟩
  have hdegreeEdges : (∑ v ∈ S, G.degree v) ≤
      2 * spannedEdgeCount G (U : Set V) :=
    sum_degrees_le_twice_spannedEdgeCount G S U hSU hclosed
  have hdense : (4 * d) * #U < 2 * spannedEdgeCount G (U : Set V) := by
    calc
      (4 * d) * #U ≤ (4 * d) * (2 * #S) :=
        Nat.mul_le_mul_left (4 * d) hslow
      _ = (8 * d) * #S := by ring
      _ < ∑ v ∈ S, G.degree v := hdegreeStrict
      _ ≤ 2 * spannedEdgeCount G (U : Set V) := hdegreeEdges
  unfold HasAverageDegreeGreaterThan
  rw [Nat.card_eq_fintype_card, card_coe_finset_set]
  exact hdense

/-- Averaging the dense stopped ball over its consecutive level pairs
produces one pair of average degree strictly greater than `2*d`. -/
theorem exists_twoLevel_hasAverageDegreeGreaterThan_two
    (hbip : G.IsBipartite) (hG : G.Connected)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (d : Nat)
    (hmin : HasMinimumDegreeGreaterThan G (8 * d)) :
    ∃ i : Nat, i < firstSlowBall G hG root ∧
      HasAverageDegreeGreaterThan
        (G.induce ((twoLevelFinset G root i : Finset V) : Set V)) (2 * d) := by
  classical
  let q := firstSlowBall G hG root
  let B : Finset V := closedBallFinset G root q
  have hballDense : (4 * d) * #B < 2 * spannedEdgeCount G (B : Set V) := by
    have hraw := firstSlowBall_hasAverageDegreeGreaterThan_four hG root d hmin
    unfold HasAverageDegreeGreaterThan at hraw
    rw [Nat.card_eq_fintype_card, card_coe_finset_set] at hraw
    simpa [q, B, spannedEdgeCount] using hraw
  have hedgeCover : spannedEdgeCount G (B : Set V) ≤
      ∑ i ∈ Finset.range q,
        spannedEdgeCount G ((twoLevelFinset G root i : Finset V) : Set V) := by
    simpa [q, B] using
      spannedEdgeCount_closedBall_le_sum_twoLevel hbip hG root q
  have hcardPairs : (∑ i ∈ Finset.range q, #(twoLevelFinset G root i)) ≤
      2 * #B := by
    simpa [B] using sum_card_twoLevel_le_twice_closedBall G root q
  by_contra hnone
  push Not at hnone
  have hpair (i : Nat) (hi : i ∈ Finset.range q) :
      2 * spannedEdgeCount G
          ((twoLevelFinset G root i : Finset V) : Set V) ≤
        (2 * d) * #(twoLevelFinset G root i) := by
    have hnot := hnone i (Finset.mem_range.mp hi)
    unfold HasAverageDegreeGreaterThan at hnot
    rw [not_lt] at hnot
    simpa [spannedEdgeCount, Nat.card_eq_fintype_card,
      card_coe_finset_set] using hnot
  have htwoCover : 2 * spannedEdgeCount G (B : Set V) ≤
      ∑ i ∈ Finset.range q,
        2 * spannedEdgeCount G
          ((twoLevelFinset G root i : Finset V) : Set V) := by
    calc
      2 * spannedEdgeCount G (B : Set V) ≤
          2 * (∑ i ∈ Finset.range q,
            spannedEdgeCount G
              ((twoLevelFinset G root i : Finset V) : Set V)) :=
        Nat.mul_le_mul_left 2 hedgeCover
      _ = ∑ i ∈ Finset.range q,
          2 * spannedEdgeCount G
            ((twoLevelFinset G root i : Finset V) : Set V) := by
        rw [Finset.mul_sum]
  have hupper : 2 * spannedEdgeCount G (B : Set V) ≤ (4 * d) * #B := by
    calc
      2 * spannedEdgeCount G (B : Set V) ≤
          ∑ i ∈ Finset.range q,
            2 * spannedEdgeCount G
              ((twoLevelFinset G root i : Finset V) : Set V) := htwoCover
      _ ≤ ∑ i ∈ Finset.range q,
          (2 * d) * #(twoLevelFinset G root i) := by
        exact Finset.sum_le_sum fun i hi => hpair i hi
      _ = (2 * d) * (∑ i ∈ Finset.range q,
          #(twoLevelFinset G root i)) := by
        rw [Finset.mul_sum]
      _ ≤ (2 * d) * (2 * #B) := Nat.mul_le_mul_left (2 * d) hcardPairs
      _ = (4 * d) * #B := by ring
  exact (Nat.not_lt_of_ge hupper) hballDense

/-- The first two BFS levels form a star (possibly with missing leaves), so
their induced graph cannot have average degree greater than `2*d` for
positive `d`.  This excludes level index zero in Lemma 2.2. -/
theorem not_twoLevel_zero_hasAverageDegreeGreaterThan_two
    (hbip : G.IsBipartite) (hG : G.Connected)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (d : Nat) (hd : 0 < d) :
    ¬ HasAverageDegreeGreaterThan
      (G.induce ((twoLevelFinset G root 0 : Finset V) : Set V)) (2 * d) := by
  classical
  let L₀ : Finset V := distanceLevelFinset G root 0
  let L₁ : Finset V := distanceLevelFinset G root 1
  have hL₀card : #L₀ = 1 := by
    rw [show L₀ = {root} by simpa [L₀] using distanceLevelFinset_zero hG root]
    simp
  have hinter : #(G.interedges L₀ L₁) ≤ #L₀ * #L₁ :=
    G.card_interedges_le_mul L₀ L₁
  have hedge : spannedEdgeCount G
      ((twoLevelFinset G root 0 : Finset V) : Set V) ≤ #L₁ := by
    calc
      spannedEdgeCount G
          ((twoLevelFinset G root 0 : Finset V) : Set V) =
          #(G.interedges L₀ L₁) := by
        simpa [L₀, L₁] using
          spannedEdgeCount_twoLevel_eq_card_interedges hbip hG root 0
      _ ≤ #L₀ * #L₁ := hinter
      _ = #L₁ := by simp [hL₀card]
  have hcard : #(twoLevelFinset G root 0) = 1 + #L₁ := by
    unfold twoLevelFinset
    rw [Finset.card_union_of_disjoint
      (distanceLevelFinset_disjoint root (by omega))]
    simp only [Nat.zero_add]
    rw [show #(distanceLevelFinset G root 0) = 1 by simpa [L₀] using hL₀card]
  intro havg
  unfold HasAverageDegreeGreaterThan at havg
  rw [Nat.card_eq_fintype_card, card_coe_finset_set] at havg
  change (2 * d) * #(twoLevelFinset G root 0) <
    2 * spannedEdgeCount G
      ((twoLevelFinset G root 0 : Finset V) : Set V) at havg
  have htwo : 2 ≤ 2 * d := by omega
  have hlower : 2 * #(twoLevelFinset G root 0) ≤
      (2 * d) * #(twoLevelFinset G root 0) :=
    Nat.mul_le_mul_right _ htwo
  have hupper : 2 * spannedEdgeCount G
      ((twoLevelFinset G root 0 : Finset V) : Set V) ≤ 2 * #L₁ :=
    Nat.mul_le_mul_left 2 hedge
  omega

/-- Strictly positive average degree forces an induced finite vertex set to
be nonempty. -/
theorem Finset.Nonempty.of_hasAverageDegreeGreaterThan_induce
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) {d : Nat}
    (h : HasAverageDegreeGreaterThan (G.induce (S : Set V)) d) :
    S.Nonempty := by
  by_contra hn
  have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  subst S
  unfold HasAverageDegreeGreaterThan at h
  simp [edgeCount] at h

/-- Choice-free cardinal form of the degree, useful when a finite graph is
packaged behind a dependent existential. -/
theorem natCard_neighborSet_eq_degree {W : Type*}
    (J : SimpleGraph W) [J.LocallyFinite]
    (v : W) : Nat.card (J.neighborSet v) = J.degree v := by
  rw [Nat.card_eq_fintype_card, J.card_neighborSet_eq_degree]

/-- Passing to a connected component preserves the choice-free cardinality
of the neighbour set. -/
theorem natCard_neighborSet_connectedComponent {W : Type*}
    (J : SimpleGraph W) (C : J.ConnectedComponent) (x : C) :
    Nat.card (C.toSimpleGraph.neighborSet x) =
      Nat.card (J.neighborSet x.val) := by
  apply Nat.card_congr
  exact
    { toFun := fun y => ⟨y.val.val, y.prop⟩
      invFun := fun y =>
        ⟨⟨y.val, C.mem_supp_of_adj_mem_supp x.prop y.prop⟩, y.prop⟩
      left_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        rfl }

/-- A connected core living inside the graph induced by levels `i` and
`i+1`.  The concrete witness is the connected component of a further induced
subgraph, so the containment certificate is an actual `SimpleGraph.Copy`. -/
def HasTwoLevelConnectedCore (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (i d : Nat) : Prop :=
  ∃ S : Finset ((twoLevelFinset G root i : Finset V) : Set V),
    ∃ C : ((G.induce ((twoLevelFinset G root i : Finset V) : Set V)).induce
        (S : Set ((twoLevelFinset G root i : Finset V) : Set V))).ConnectedComponent,
      C.toSimpleGraph.Connected ∧
        (∀ v : C, d < Nat.card (C.toSimpleGraph.neighborSet v)) ∧
        C.toSimpleGraph ⊑
          G.induce ((twoLevelFinset G root i : Finset V) : Set V)

/-- Wang--Wang Lemma 2.2, with the slightly stronger conclusion
`δ(F) > d` in place of `δ(F) ≥ d`.

For a finite connected bipartite graph of minimum degree greater than `8d`,
there is a noninitial pair of consecutive BFS levels below logarithmic depth
that contains a connected core of minimum degree greater than `d`. -/
theorem bfs_localisation
    (hbip : G.IsBipartite) (hG : G.Connected)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (root : V) (d : Nat) (hd : 2 ≤ d)
    (hmin : HasMinimumDegreeGreaterThan G (8 * d)) :
    ∃ q i : Nat,
      1 ≤ i ∧ i < q ∧
        (q : Real) < 1 + Real.logb 2 (Fintype.card V : Real) ∧
        HasTwoLevelConnectedCore G root i d := by
  classical
  let q := firstSlowBall G hG root
  have hfirst : 2 * #(closedBallFinset G root 0) <
      #(closedBallFinset G root 1) := by
    rw [card_closedBallFinset_zero hG root,
      card_closedBallFinset_one hG root]
    have hdeg := hmin root
    omega
  have hqTwo : 2 ≤ q := by
    simpa [q] using
      two_le_firstSlowBall_of_first_growth G hG root hfirst
  have hqLog : (q : Real) <
      1 + Real.logb 2 (Fintype.card V : Real) := by
    simpa [q] using firstSlowBall_lt_one_add_logb_card G hG root hqTwo
  obtain ⟨i, hiq, hiavg⟩ :=
    exists_twoLevel_hasAverageDegreeGreaterThan_two hbip hG root d hmin
  have hizero : i ≠ 0 := by
    intro hi
    subst i
    exact (not_twoLevel_zero_hasAverageDegreeGreaterThan_two
      hbip hG root d (by omega)) hiavg
  have hiOne : 1 ≤ i := by omega
  let H := G.induce ((twoLevelFinset G root i : Finset V) : Set V)
  have hHavgGT : HasAverageDegreeGreaterThan H (2 * d) := by
    simpa [H] using hiavg
  have hpairNE : (twoLevelFinset G root i).Nonempty :=
    Finset.Nonempty.of_hasAverageDegreeGreaterThan_induce G
      (twoLevelFinset G root i) hiavg
  letI : Nonempty ((twoLevelFinset G root i : Finset V) : Set V) :=
    Finset.nonempty_coe_sort.mpr hpairNE
  have hHavg : HasAverageDegreeAtLeast H (2 * d) := by
    unfold HasAverageDegreeGreaterThan at hHavgGT
    unfold HasAverageDegreeAtLeast
    exact hHavgGT.le
  obtain ⟨S, hSne, hSavg, hSmindeg⟩ :=
    exists_minimalDegree_dense_induced_finset H (by omega) hHavg
  let J := H.induce (S : Set ((twoLevelFinset G root i : Finset V) : Set V))
  letI : Nonempty S := Finset.nonempty_coe_sort.mpr hSne
  obtain ⟨C, hCavg⟩ :=
    exists_connectedComponent_hasAverageDegreeAtLeast J hSavg
  have hCcopy : C.toSimpleGraph ⊑ H :=
    ⟨(Copy.induce H (S : Set ((twoLevelFinset G root i : Finset V) : Set V))).comp
      (Copy.induce J C.supp)⟩
  refine ⟨q, i, hiOne, ?_, hqLog, ?_⟩
  · simpa [q] using hiq
  · refine ⟨S, C, C.connected_toSimpleGraph, ?_, hCcopy⟩
    intro v
    calc
      d < J.degree v.val := hSmindeg v.val
      _ = Nat.card (J.neighborSet v.val) :=
        (natCard_neighborSet_eq_degree J v.val).symm
      _ = Nat.card (C.toSimpleGraph.neighborSet v) :=
        (natCard_neighborSet_connectedComponent J C v).symm

end LeanCo.SizeRamsey
