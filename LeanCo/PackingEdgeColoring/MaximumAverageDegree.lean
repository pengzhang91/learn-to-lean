import LeanCo.PackingEdgeColoring.Defs

/-!
# Maximum average degree

Elementary consequences of the division-free maximum-average-degree
predicate used for the sparse packing edge-colouring argument.  In
particular, this file records monotonicity under deleting edges and converts
the global density inequality into the degree-sum and integral-charge forms
used in the `12 / 5` discharging contradiction.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open Finset SimpleGraph

noncomputable section

universe u

variable {V : Type u} {G H : SimpleGraph V} {p q : ℕ}

/-! ## Heredity under deleting edges -/

/-- Maximum average degree is monotone under the graph order: deleting edges
cannot violate a strict upper bound on maximum average degree. -/
theorem MaximumAverageDegreeLT.mono [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (hG : MaximumAverageDegreeLT G p q) :
    MaximumAverageDegreeLT H p q := by
  intro S hS
  have hinduce : H.induce (S : Set V) ≤ G.induce (S : Set V) :=
    fun _ _ hadj ↦ hHG hadj
  have hcard :
      (H.induce (S : Set V)).edgeFinset.card ≤
        (G.induce (S : Set V)).edgeFinset.card :=
    card_le_card (edgeFinset_mono hinduce)
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_left q (Nat.mul_le_mul_left 2 hcard))
    (hG S hS)

/-- Deleting an arbitrary set of edges preserves a maximum-average-degree
upper bound. -/
theorem MaximumAverageDegreeLT.deleteEdges [DecidableEq V] [DecidableRel G.Adj]
    (hG : MaximumAverageDegreeLT G p q) (s : Set (Sym2 V))
    [DecidablePred (fun e ↦ e ∈ s)] :
    MaximumAverageDegreeLT (G.deleteEdges s) p q := by
  exact hG.mono (G.deleteEdges_le s)

/-- Deleting all edges incident with a vertex preserves a
maximum-average-degree upper bound.  Keeping the now-isolated vertex in the
ambient type is convenient for minimal-counterexample arguments. -/
theorem MaximumAverageDegreeLT.deleteIncidenceSet [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj]
    (hG : MaximumAverageDegreeLT G p q) (v : V) :
    MaximumAverageDegreeLT (G.deleteIncidenceSet v) p q := by
  exact hG.mono (G.deleteIncidenceSet_le v)

/-! ## Global density and degree sums -/

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The vertices having degree exactly `d`. -/
def degreeClass (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ G.degree v = d

@[simp]
theorem mem_degreeClass {v : V} {d : ℕ} :
    v ∈ degreeClass G d ↔ G.degree v = d := by
  simp [degreeClass]

/-- The degree sum over one degree class. -/
theorem sum_degree_degreeClass (d : ℕ) :
    ∑ v ∈ degreeClass G d, G.degree v = d * (degreeClass G d).card := by
  calc
    ∑ v ∈ degreeClass G d, G.degree v =
        ∑ _v ∈ degreeClass G d, d := by
          apply Finset.sum_congr rfl
          intro v hv
          exact mem_degreeClass.mp hv
    _ = d * (degreeClass G d).card := by
      simp [Nat.mul_comm]

/-- Distinct degree classes are disjoint. -/
theorem degreeClass_disjoint {d e : ℕ} (hde : d ≠ e) :
    Disjoint (degreeClass G d) (degreeClass G e) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvd hve
  exact hde (mem_degreeClass.mp hvd |>.symm.trans (mem_degreeClass.mp hve))

/-- If every vertex has degree two or three, those two degree classes
partition the vertex set. -/
theorem degreeClass_two_union_three
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    degreeClass G 2 ∪ degreeClass G 3 = Finset.univ := by
  classical
  ext v
  simp only [Finset.mem_union, mem_degreeClass, Finset.mem_univ, iff_true]
  exact hdeg v

/-- Cardinality form of the degree-two/degree-three partition. -/
theorem card_degreeClass_two_add_three
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    (degreeClass G 2).card + (degreeClass G 3).card = Fintype.card V := by
  classical
  have hdisj : Disjoint (degreeClass G 2) (degreeClass G 3) :=
    degreeClass_disjoint (by omega)
  calc
    (degreeClass G 2).card + (degreeClass G 3).card =
        (degreeClass G 2 ∪ degreeClass G 3).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = Fintype.card V := by rw [degreeClass_two_union_three hdeg, Finset.card_univ]

/-- Handshaking specialized to a graph all of whose vertices have degree two
or three. -/
theorem sum_degrees_eq_two_mul_degreeTwo_add_three_mul_degreeThree
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    ∑ v, G.degree v =
      2 * (degreeClass G 2).card + 3 * (degreeClass G 3).card := by
  classical
  have hdisj : Disjoint (degreeClass G 2) (degreeClass G 3) :=
    degreeClass_disjoint (by omega)
  calc
    ∑ v, G.degree v =
        ∑ v ∈ degreeClass G 2 ∪ degreeClass G 3, G.degree v := by
      rw [degreeClass_two_union_three hdeg]
    _ = (∑ v ∈ degreeClass G 2, G.degree v) +
          ∑ v ∈ degreeClass G 3, G.degree v := by
      rw [Finset.sum_union hdisj]
    _ = 2 * (degreeClass G 2).card + 3 * (degreeClass G 3).card := by
      rw [sum_degree_degreeClass, sum_degree_degreeClass]

/-- Minimum degree at least two together with subcubicity leaves only degree
two and degree three vertices. -/
theorem degree_eq_two_or_three_of_isSubcubic
    (hmin : ∀ v, 2 ≤ G.degree v) (hsub : IsSubcubic G) :
    ∀ v, G.degree v = 2 ∨ G.degree v = 3 := by
  intro v
  have hminv := hmin v
  have hmax := hsub v
  omega

/-! ### Ignoring isolated ambient vertices

An edge-minimal counterexample on a fixed Lean vertex type may still carry
isolated ambient vertices.  Paper proofs silently delete them.  The next
lemmas instead apply the MAD inequality to the support of the graph, which is
the exact fixed-type replacement. -/

/-- If every positive-degree vertex has degree at least two in a subcubic
graph, then every degree is zero, two, or three. -/
theorem degree_eq_zero_or_two_or_three_of_active_min_degree
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G) :
    ∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 3 := by
  intro v
  by_cases hz : G.degree v = 0
  · exact Or.inl hz
  · right
    have hpos : 0 < G.degree v := Nat.pos_of_ne_zero hz
    have hlo := hmin v hpos
    have hhi := hsub v
    omega

/-- The handshaking sum only sees the degree-two and degree-three classes;
isolated vertices contribute zero. -/
theorem sum_degrees_eq_two_mul_degreeTwo_add_three_mul_degreeThree_of_active
    (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 3) :
    ∑ v, G.degree v =
      2 * (degreeClass G 2).card + 3 * (degreeClass G 3).card := by
  classical
  have hpoint : ∀ v, G.degree v =
      (if G.degree v = 2 then 2 else 0) +
        (if G.degree v = 3 then 3 else 0) := by
    intro v
    rcases hdeg v with h0 | h2 | h3
    · simp [h0]
    · simp [h2]
    · simp [h3]
  calc
    ∑ v, G.degree v = ∑ v,
        ((if G.degree v = 2 then 2 else 0) +
          (if G.degree v = 3 then 3 else 0)) := by
            apply Finset.sum_congr rfl
            intro v _
            exact hpoint v
    _ = (∑ v, if G.degree v = 2 then 2 else 0) +
        ∑ v, if G.degree v = 3 then 3 else 0 := Finset.sum_add_distrib
    _ = 2 * (degreeClass G 2).card + 3 * (degreeClass G 3).card := by
      have htwo : (∑ v, if G.degree v = 2 then 2 else 0) =
          2 * (degreeClass G 2).card := by
        rw [← Finset.sum_filter]
        simp [degreeClass, Nat.mul_comm]
      have hthree : (∑ v, if G.degree v = 3 then 3 else 0) =
          3 * (degreeClass G 3).card := by
        rw [← Finset.sum_filter]
        simp [degreeClass, Nat.mul_comm]
      rw [htwo, hthree]

/-- Under the active degree dichotomy, the graph support lies in the union
of the degree-two and degree-three classes. -/
theorem support_subset_degreeClass_two_union_three
    (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 3) :
    G.support ⊆ (degreeClass G 2 ∪ degreeClass G 3 : Finset V) := by
  intro v hv
  have hpos : 0 < G.degree v :=
    (G.degree_pos_iff_mem_support v).mpr hv
  rcases hdeg v with h0 | h2 | h3
  · omega
  · simp [degreeClass, h2]
  · simp [degreeClass, h3]

/-- MAD on the graph support yields the same strict degree-class inequality
as the usual minimum-degree-two argument, without pretending that isolated
ambient vertices have been removed. -/
theorem MaximumAverageDegreeLT.three_mul_degreeThree_lt_two_mul_degreeTwo_of_active
    (hG : MaximumAverageDegreeLT G p q)
    (hEdge : G.edgeFinset.Nonempty)
    (hmin : ∀ v, 0 < G.degree v → 2 ≤ G.degree v)
    (hsub : IsSubcubic G) (hpq : p = 12) (hqq : q = 5) :
    3 * (degreeClass G 3).card < 2 * (degreeClass G 2).card := by
  classical
  subst p
  subst q
  let S : Finset V := degreeClass G 2 ∪ degreeClass G 3
  have hdeg :=
    degree_eq_zero_or_two_or_three_of_active_min_degree (G := G) hmin hsub
  have hsupport : G.support ⊆ (S : Set V) := by
    simpa [S] using support_subset_degreeClass_two_union_three (G := G) hdeg
  have hGne : G ≠ ⊥ := (SimpleGraph.edgeFinset_nonempty (G := G)).mp hEdge
  have hsupportNonempty : G.support.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    exact hGne ((SimpleGraph.support_eq_bot_iff (G := G)).mp hempty)
  have hSNonempty : S.Nonempty := by
    obtain ⟨v, hv⟩ := hsupportNonempty
    exact ⟨v, hsupport hv⟩
  have hdensity := hG S hSNonempty
  have hmap :
      (G.induce (S : Set V)).edgeFinset.map
          (Function.Embedding.subtype (fun v ↦ v ∈ (S : Set V))).sym2Map =
        G.edgeFinset := by
    apply Finset.ext
    intro e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
      induction f using Sym2.inductionOn with
      | _ x y =>
          have hxyInduced : (G.induce (S : Set V)).Adj x y := by
            simpa only [SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet] using hf
          have hxy : G.Adj x.1 y.1 :=
            SimpleGraph.induce_adj.mp hxyInduced
          rw [Function.Embedding.sym2Map_apply, Sym2.map_mk,
            SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
          exact hxy
    · intro he
      induction e using Sym2.inductionOn with
      | _ x y =>
          have hxy : G.Adj x y := by
            simpa only [SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet] using he
          have hxSupport : x ∈ G.support := hxy.mem_support_left
          have hySupport : y ∈ G.support := hxy.mem_support_right
          let xs : {v // v ∈ (S : Set V)} := ⟨x, hsupport hxSupport⟩
          let ys : {v // v ∈ (S : Set V)} := ⟨y, hsupport hySupport⟩
          apply Finset.mem_map.mpr
          refine ⟨s(xs, ys), ?_, ?_⟩
          · simpa only [SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] using hxy
          · simp [xs, ys, Function.Embedding.sym2Map_apply, Sym2.map_mk]
  have hedgecard : (G.induce (S : Set V)).edgeFinset.card =
      G.edgeFinset.card := by
    rw [← hmap, Finset.card_map]
  rw [hedgecard] at hdensity
  have hsum :=
    sum_degrees_eq_two_mul_degreeTwo_add_three_mul_degreeThree_of_active
      (G := G) hdeg
  have hhandshake := G.sum_degrees_eq_twice_card_edges
  have hSCard : S.card =
      (degreeClass G 2).card + (degreeClass G 3).card := by
    change (degreeClass G 2 ∪ degreeClass G 3).card = _
    rw [Finset.card_union_of_disjoint]
    exact degreeClass_disjoint (G := G) (by omega)
  rw [hSCard] at hdensity
  rw [hsum] at hhandshake
  omega

/-- The defining MAD inequality applied to the full vertex set. -/
theorem MaximumAverageDegreeLT.univ_edgeDensity [Nonempty V]
    (hG : MaximumAverageDegreeLT G p q) :
    q * (2 * G.edgeFinset.card) < p * Fintype.card V := by
  have h := hG (Finset.univ : Finset V) Finset.univ_nonempty
  let e : {v // v ∈ (Finset.univ : Finset V)} ≃ V :=
    { toFun := Subtype.val
      invFun := fun v ↦ ⟨v, Finset.mem_univ v⟩
      left_inv := fun v ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
  let iso :
      G.induce ((↑(Finset.univ : Finset V) : Set V)) ≃g G :=
    { toEquiv := e
      map_rel_iff' := by intros; rfl }
  rw [iso.card_edgeFinset_eq] at h
  simpa only [Finset.card_univ] using h

/-- The global MAD inequality written using the handshaking identity. -/
theorem MaximumAverageDegreeLT.univ_sum_degrees [Nonempty V]
    (hG : MaximumAverageDegreeLT G p q) :
    q * (∑ v, G.degree v) < p * Fintype.card V := by
  rw [G.sum_degrees_eq_twice_card_edges]
  exact hG.univ_edgeDensity

/-- Expanding the integral initial charges `q * d(v) - p` gives the scaled
edge-density deficit.  Integer charges avoid all division. -/
theorem scaledDegreeCharge_sum :
    ∑ v : V, ((q : ℤ) * G.degree v - p) =
      (q : ℤ) * (2 * G.edgeFinset.card) - (p : ℤ) * Fintype.card V := by
  have hdegree :
      (∑ v : V, (G.degree v : ℤ)) = (2 * G.edgeFinset.card : ℕ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  calc
    ∑ v : V, ((q : ℤ) * G.degree v - p) =
        (q : ℤ) * (∑ v : V, (G.degree v : ℤ)) -
          (p : ℤ) * Fintype.card V := by
            rw [sum_sub_distrib, ← Finset.mul_sum]
            simp [mul_comm]
    _ = (q : ℤ) * (2 * G.edgeFinset.card) -
          (p : ℤ) * Fintype.card V := by
            rw [hdegree]
            norm_num

/-- Under `mad(G) < p/q`, the total integral initial charge
`q * d(v) - p` is strictly negative. -/
theorem MaximumAverageDegreeLT.scaledDegreeCharge_sum_neg [Nonempty V]
    (hG : MaximumAverageDegreeLT G p q) :
    ∑ v : V, ((q : ℤ) * G.degree v - p) < 0 := by
  rw [scaledDegreeCharge_sum]
  exact sub_neg.mpr (by exact_mod_cast hG.univ_edgeDensity)

/-- The exact negative-charge inequality used in the paper's `12/5`
discharging proof. -/
theorem MaximumAverageDegreeLT.fiveDegree_sub_twelve_sum_neg [Nonempty V]
    (hG : MaximumAverageDegreeLT G 12 5) :
    ∑ v : V, (5 * (G.degree v : ℤ) - 12) < 0 := by
  simpa using hG.scaledDegreeCharge_sum_neg

/-- For a graph whose degrees are all two or three, `mad(G) < 12/5` says
exactly that the positive contribution of the degree-three vertices is
strictly smaller than the deficit from the degree-two vertices. -/
theorem MaximumAverageDegreeLT.three_mul_degreeThree_lt_two_mul_degreeTwo
    [Nonempty V] (hG : MaximumAverageDegreeLT G 12 5)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    3 * (degreeClass G 3).card < 2 * (degreeClass G 2).card := by
  have hdensity := hG.univ_sum_degrees
  rw [sum_degrees_eq_two_mul_degreeTwo_add_three_mul_degreeThree hdeg] at hdensity
  have hcard := card_degreeClass_two_add_three hdeg
  rw [← hcard] at hdensity
  omega

/-- The preceding count in the form most directly supplied by the structural
lemmas of a minimal subcubic counterexample. -/
theorem MaximumAverageDegreeLT.three_mul_degreeThree_lt_two_mul_degreeTwo_of_isSubcubic
    [Nonempty V] (hG : MaximumAverageDegreeLT G 12 5)
    (hmin : ∀ v, 2 ≤ G.degree v) (hsub : IsSubcubic G) :
    3 * (degreeClass G 3).card < 2 * (degreeClass G 2).card :=
  hG.three_mul_degreeThree_lt_two_mul_degreeTwo
    (degree_eq_two_or_three_of_isSubcubic hmin hsub)

/-! ## Double-counting transfers -/

/-- Sending an integer amount `send u v` from `u` to `v` preserves the total
charge.  No sign or support assumptions are needed for this bookkeeping
identity. -/
theorem sum_charge_after_transfer (initial : V → ℤ) (send : V → V → ℤ) :
    (∑ v : V, ((initial v - ∑ w : V, send v w) +
      ∑ u : V, send u v)) =
      ∑ v : V, initial v := by
  have hdouble :
      (∑ v : V, ∑ w : V, send v w) =
        ∑ v : V, ∑ u : V, send u v := by
    rw [sum_comm]
  rw [sum_add_distrib, sum_sub_distrib, hdouble]
  omega

/-- Consequently, under a strict MAD bound every redistribution of the
scaled degree charges leaves at least one vertex with negative final charge.
This is the reusable contradiction endpoint for discharging arguments. -/
theorem MaximumAverageDegreeLT.exists_negative_charge_after_transfer
    [Nonempty V] (hG : MaximumAverageDegreeLT G p q) (send : V → V → ℤ) :
    ∃ v : V,
      ((q : ℤ) * G.degree v - p - ∑ w : V, send v w) +
          ∑ u : V, send u v < 0 := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hnonneg :
      0 ≤ (∑ v : V,
        (((q : ℤ) * G.degree v - p - ∑ w : V, send v w) +
          ∑ u : V, send u v)) :=
    sum_nonneg fun v _ ↦ h v
  have hconserve := sum_charge_after_transfer
    (V := V) (fun v ↦ (q : ℤ) * G.degree v - p) send
  have htotal_nonneg :
      0 ≤ ∑ v : V, ((q : ℤ) * G.degree v - p) :=
    hconserve ▸ hnonneg
  exact (not_le_of_gt hG.scaledDegreeCharge_sum_neg) htotal_nonneg

end Finite

/-! ## Generic finite-relation double counting -/

section DoubleCounting

universe v

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]

/-- Count a finite binary relation by either coordinate. -/
theorem sum_card_relation_fiber_comm (R : A → B → Prop) [DecidableRel R] :
    (∑ a : A, (Finset.univ.filter fun b : B ↦ R a b).card) =
      ∑ b : B, (Finset.univ.filter fun a : A ↦ R a b).card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]

/-- A reusable bipartite-incidence bound.  If every `A`-object has at least
`leftDegree` incidences and every `B`-object has at most `rightDegree`, then
`leftDegree * |A| ≤ rightDegree * |B|`. -/
theorem mul_card_le_mul_card_of_relation (R : A → B → Prop) [DecidableRel R]
    (leftDegree rightDegree : ℕ)
    (hleft : ∀ a : A,
      leftDegree ≤ (Finset.univ.filter fun b : B ↦ R a b).card)
    (hright : ∀ b : B,
      (Finset.univ.filter fun a : A ↦ R a b).card ≤ rightDegree) :
    leftDegree * Fintype.card A ≤ rightDegree * Fintype.card B := by
  calc
    leftDegree * Fintype.card A = ∑ _a : A, leftDegree := by
      simp [Nat.mul_comm]
    _ ≤ ∑ a : A, (Finset.univ.filter fun b : B ↦ R a b).card :=
      Finset.sum_le_sum fun a _ ↦ hleft a
    _ = ∑ b : B, (Finset.univ.filter fun a : A ↦ R a b).card :=
      sum_card_relation_fiber_comm R
    _ ≤ ∑ _b : B, rightDegree :=
      Finset.sum_le_sum fun b _ ↦ hright b
    _ = rightDegree * Fintype.card B := by
      simp [Nat.mul_comm]

end DoubleCounting

end

end LeanCo.PackingEdgeColoring
