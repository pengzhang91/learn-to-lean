import LeanCo.SizeRamsey.GraphBasics
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
import Mathlib.Data.List.PeriodicityLemma

/-!
# Paths of prescribed length across a vertex partition

This file develops the walk-level language used in the Gao--Huo--Ma
path-length lemma.  A path is an `A`--`B` path when its two ends lie in
opposite parts.  Length always means number of edges.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Two vertices lie in opposite (ordered) parts of a vertex partition. -/
def InOppositeParts (A B : Set V) (u v : V) : Prop :=
  (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

theorem InOppositeParts.symm {A B : Set V} {u v : V}
    (h : InOppositeParts A B u v) : InOppositeParts A B v u := by
  rcases h with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

/-- `G` has a simple `A`--`B` path with exactly `ell` edges. -/
def HasABPathLength (G : SimpleGraph V) (A B : Set V) (ell : Nat) : Prop :=
  ∃ u v, ∃ p : G.Walk u v,
    p.IsPath ∧ p.length = ell ∧ InOppositeParts A B u v

theorem HasABPathLength.symm_parts {A B : Set V} {ell : Nat}
    (h : HasABPathLength G A B ell) : HasABPathLength G B A ell := by
  obtain ⟨u, v, p, hp, hlen, huv⟩ := h
  refine ⟨u, v, p, hp, hlen, ?_⟩
  exact huv.elim (fun h => Or.inr h) (fun h => Or.inl h)

theorem HasABPathLength.mono {H : SimpleGraph V} {A B : Set V} {ell : Nat}
    (hGH : G ≤ H) (h : HasABPathLength G A B ell) :
    HasABPathLength H A B ell := by
  obtain ⟨u, v, p, hp, hlen, huv⟩ := h
  refine ⟨u, v, p.mapLe hGH, hp.mapLe hGH, ?_, huv⟩
  change (p.map (Hom.ofLE hGH)).length = ell
  rw [Walk.length_map, hlen]

/-! ## Contiguous pieces of a path -/

/-- A contiguous piece, starting after `i` edges and using `ell` edges. -/
def walkSegment {u v : V} (p : G.Walk u v) (i ell : Nat) :=
  (p.drop i).take ell

@[simp]
theorem length_walkSegment {u v : V} (p : G.Walk u v)
    (i ell : Nat) :
    (walkSegment p i ell).length = ell ⊓ (p.length - i) := by
  simp [walkSegment]

theorem length_walkSegment_of_le {u v : V} (p : G.Walk u v)
    {i ell : Nat} (h : i + ell ≤ p.length) :
    (walkSegment p i ell).length = ell := by
  rw [length_walkSegment, Nat.min_eq_left]
  omega

theorem isPath_walkSegment {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) (i ell : Nat) : (walkSegment p i ell).IsPath := by
  exact (hp.drop i).take ell

theorem hasABPathLength_of_path_segment {A B : Set V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) {i ell : Nat}
    (hi : i + ell ≤ p.length)
    (hop : InOppositeParts A B (p.getVert i) (p.getVert (i + ell))) :
    HasABPathLength G A B ell := by
  let q := walkSegment p i ell
  have hqend : (p.drop i).getVert ell = p.getVert (i + ell) := by simp
  refine ⟨p.getVert i, (p.drop i).getVert ell, q, isPath_walkSegment hp i ell,
    length_walkSegment_of_le p hi, ?_⟩
  simpa [hqend] using hop

/-! ## Elementary facts about a genuine two-part partition -/

theorem mem_right_iff_not_mem_left {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B) {v : V} :
    v ∈ B ↔ v ∉ A := by
  constructor
  · intro hvB hvA
    exact Set.disjoint_left.mp hdisj hvA hvB
  · intro hvA
    have : v ∈ A ∪ B := by simpa [hcover]
    exact this.resolve_left hvA

theorem inOppositeParts_iff_xor_left {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B) {u v : V} :
    InOppositeParts A B u v ↔ (u ∈ A ↔ v ∉ A) := by
  rw [InOppositeParts, mem_right_iff_not_mem_left hcover hdisj,
    mem_right_iff_not_mem_left hcover hdisj]
  tauto

theorem not_inOppositeParts_iff_same_left {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B) {u v : V} :
    ¬ InOppositeParts A B u v ↔ (u ∈ A ↔ v ∈ A) := by
  rw [inOppositeParts_iff_xor_left hcover hdisj]
  tauto

/-! ## Alternating chains -/

private theorem same_left_of_two_mul_crossings {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    (f : Nat → V) {start k : Nat}
    (hcross : ∀ j, start ≤ j → j < start + 2 * k →
      InOppositeParts A B (f j) (f (j + 1))) :
    (f start ∈ A ↔ f (start + 2 * k) ∈ A) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hprefix : ∀ j, start ≤ j → j < start + 2 * k →
          InOppositeParts A B (f j) (f (j + 1)) := by
        intro j hj₀ hj₁
        exact hcross j hj₀ (by omega)
      have h₁ := inOppositeParts_iff_xor_left hcover hdisj |>.mp
        (hcross (start + 2 * k) (by omega) (by omega))
      have h₂ := inOppositeParts_iff_xor_left hcover hdisj |>.mp
        (hcross (start + 2 * k + 1) (by omega) (by omega))
      have hi := ih hprefix
      simpa [Nat.mul_succ, Nat.add_assoc] using
        (show f start ∈ A ↔ f (start + 2 * k + 2) ∈ A by tauto)

theorem same_left_of_even_crossing_chain {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    (f : Nat → V) {start d : Nat}
    (hcross : ∀ j, start ≤ j → j < start + d →
      InOppositeParts A B (f j) (f (j + 1))) (hd : Even d) :
    (f start ∈ A ↔ f (start + d) ∈ A) := by
  obtain ⟨k, hk⟩ := hd
  have hd' : d = 2 * k := by omega
  have hcross' : ∀ j, start ≤ j → j < start + 2 * k →
      InOppositeParts A B (f j) (f (j + 1)) := by
    intro j hj₀ hj₁
    apply hcross j hj₀
    omega
  simpa [hd'] using same_left_of_two_mul_crossings hcover hdisj f hcross'

theorem inOppositeParts_of_odd_crossing_chain {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    (f : Nat → V) {start d : Nat}
    (hcross : ∀ j, start ≤ j → j < start + d →
      InOppositeParts A B (f j) (f (j + 1))) (hd : Odd d) :
    InOppositeParts A B (f start) (f (start + d)) := by
  obtain ⟨k, hk⟩ := hd
  have hd' : d = 2 * k + 1 := by omega
  have hprefix : ∀ j, start ≤ j → j < start + 2 * k →
      InOppositeParts A B (f j) (f (j + 1)) := by
    intro j hj₀ hj₁
    exact hcross j hj₀ (by omega)
  have heven := same_left_of_two_mul_crossings hcover hdisj f hprefix
  have hlast := inOppositeParts_iff_xor_left hcover hdisj |>.mp
    (hcross (start + 2 * k) (by omega) (by omega))
  rw [inOppositeParts_iff_xor_left hcover hdisj]
  simpa [hd', Nat.add_assoc] using
    (show f start ∈ A ↔ f (start + 2 * k + 1) ∉ A by tauto)

/-- An odd-length section of an alternating path crosses the partition. -/
theorem hasABPathLength_of_odd_alternating_path {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hcross : ∀ i, i < p.length →
      InOppositeParts A B (p.getVert i) (p.getVert (i + 1)))
    {ell : Nat} (hell : ell ≤ p.length) (hodd : Odd ell) :
    HasABPathLength G A B ell := by
  apply hasABPathLength_of_path_segment hp (i := 0) (ell := ell)
  · simpa using hell
  have hop := inOppositeParts_of_odd_crossing_chain hcover hdisj p.getVert
    (start := 0) (d := ell) (by
      intro j _hj₀ hj₁
      apply hcross j
      omega) hodd
  simpa using hop

/-- If the first edge of a path stays inside one part and every later edge
crosses the partition, then the path contains crossing subpaths of every
positive length strictly below any bound on its length. -/
theorem hasABPathLength_of_internal_first_alternating_lt {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hfirst : ¬ InOppositeParts A B (p.getVert 0) (p.getVert 1))
    (hcross : ∀ i, 1 ≤ i → i < p.length →
      InOppositeParts A B (p.getVert i) (p.getVert (i + 1)))
    {bound : Nat} (hbound : bound ≤ p.length) :
    ∀ ell, 1 ≤ ell → ell < bound → HasABPathLength G A B ell := by
  intro ell hell₁ hellb
  rcases Nat.even_or_odd ell with hellEven | hellOdd
  · have htailOdd : Odd (ell - 1) := by
      obtain ⟨k, hk⟩ := hellEven
      cases k with
      | zero => omega
      | succ k =>
          refine ⟨k, ?_⟩
          omega
    have htail : InOppositeParts A B (p.getVert 1) (p.getVert (1 + (ell - 1))) :=
      inOppositeParts_of_odd_crossing_chain hcover hdisj p.getVert
        (start := 1) (d := ell - 1) (by
          intro j hj₀ hj₁
          apply hcross j hj₀
          omega) htailOdd
    have hfirstSame := not_inOppositeParts_iff_same_left hcover hdisj |>.mp hfirst
    apply hasABPathLength_of_path_segment hp (i := 0) (ell := ell)
    · omega
    rw [inOppositeParts_iff_xor_left hcover hdisj]
    simp only [Walk.getVert_zero, zero_add]
    have htail' := inOppositeParts_iff_xor_left hcover hdisj |>.mp htail
    have hone : 1 + (ell - 1) = ell := by omega
    rw [hone] at htail'
    have hfirstSame' : u ∈ A ↔ p.getVert 1 ∈ A := by simpa using hfirstSame
    tauto
  ·
    have hop : InOppositeParts A B (p.getVert 1) (p.getVert (1 + ell)) :=
      inOppositeParts_of_odd_crossing_chain hcover hdisj p.getVert
        (start := 1) (d := ell) (by
          intro j hj₀ hj₁
          apply hcross j hj₀
          omega) hellOdd
    exact hasABPathLength_of_path_segment hp (i := 1) (ell := ell) (by omega) hop

/-- The closed-bound version needed when the requested upper bound is even. -/
theorem hasABPathLength_of_internal_first_alternating {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hfirst : ¬ InOppositeParts A B (p.getVert 0) (p.getVert 1))
    (hcross : ∀ i, 1 ≤ i → i < p.length →
      InOppositeParts A B (p.getVert i) (p.getVert (i + 1)))
    {bound : Nat} (hboundEven : Even bound) (hbound : bound ≤ p.length) :
    ∀ ell, 1 ≤ ell → ell ≤ bound → HasABPathLength G A B ell := by
  intro ell hell₁ hellb
  by_cases hlt : ell < bound
  · exact hasABPathLength_of_internal_first_alternating_lt hcover hdisj hp hfirst hcross
      hbound ell hell₁ hlt
  · have hell : ell = bound := by omega
    subst ell
    obtain ⟨k, hk⟩ := hboundEven
    cases k with
    | zero => omega
    | succ k =>
        have htailOdd : Odd (bound - 1) := by
          refine ⟨k, ?_⟩
          omega
        have htail : InOppositeParts A B
            (p.getVert 1) (p.getVert (1 + (bound - 1))) :=
          inOppositeParts_of_odd_crossing_chain hcover hdisj p.getVert
            (start := 1) (d := bound - 1) (by
              intro j hj₀ hj₁
              apply hcross j hj₀
              omega) htailOdd
        have hfirstSame := not_inOppositeParts_iff_same_left hcover hdisj |>.mp hfirst
        apply hasABPathLength_of_path_segment hp (i := 0) (ell := bound)
        · omega
        rw [inOppositeParts_iff_xor_left hcover hdisj]
        simp only [Walk.getVert_zero, zero_add]
        have htail' := inOppositeParts_iff_xor_left hcover hdisj |>.mp htail
        have hone : 1 + (bound - 1) = bound := by omega
        rw [hone] at htail'
        have hfirstSame' : u ∈ A ↔ p.getVert 1 ∈ A := by simpa using hfirstSame
        tauto

/-! ## Edges forced by the partition hypotheses -/

/-- Failure of `(A,B)` to be a graph bipartition is witnessed by an edge
whose ends lie in the same part. -/
theorem exists_internal_edge_of_not_isBipartiteWith {A B : Set V}
    (hdisj : Disjoint A B) (hnot : ¬ G.IsBipartiteWith A B) :
    ∃ u v, G.Adj u v ∧ ¬ InOppositeParts A B u v := by
  by_contra h
  apply hnot
  refine ⟨hdisj, ?_⟩
  intro u v huv
  have hop : InOppositeParts A B u v := by
    by_contra hn
    exact h ⟨u, v, huv, hn⟩
  exact hop

private theorem same_left_along_walk_of_no_crossing {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    (hno : ∀ ⦃x y⦄, G.Adj x y → ¬ InOppositeParts A B x y) :
    ∀ {x y} (p : G.Walk x y), (x ∈ A ↔ y ∈ A) := by
  intro x y p
  induction p with
  | nil => rfl
  | @cons x z y hxz p ih =>
      have hxzSame := not_inOppositeParts_iff_same_left hcover hdisj |>.mp (hno hxz)
      exact hxzSame.trans ih

/-- In a connected graph, a nontrivial vertex partition has a crossing edge. -/
theorem exists_crossing_edge_of_connected {A B : Set V}
    (hconn : G.Connected) (hcover : A ∪ B = Set.univ)
    (hdisj : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ u v, G.Adj u v ∧ InOppositeParts A B u v := by
  by_contra h
  have hno : ∀ ⦃x y⦄, G.Adj x y → ¬ InOppositeParts A B x y := by
    intro x y hxy hop
    exact h ⟨x, y, hxy, hop⟩
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨p, _hp⟩ := hconn.exists_isPath a b
  have hab := same_left_along_walk_of_no_crossing hcover hdisj hno p
  have hbnot : b ∉ A := (mem_right_iff_not_mem_left hcover hdisj).mp hb
  exact hbnot (hab.mp ha)

/-- The length-one case of the path-length lemma. -/
theorem hasABPathLength_one_of_connected {A B : Set V}
    (hconn : G.Connected) (hcover : A ∪ B = Set.univ)
    (hdisj : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty) :
    HasABPathLength G A B 1 := by
  obtain ⟨u, v, huv, hop⟩ :=
    exists_crossing_edge_of_connected hconn hcover hdisj hA hB
  exact ⟨u, v, huv.toWalk, Walk.IsPath.of_adj huv, by simp, hop⟩

/-! ## Cutting and joining paths around a cycle -/

theorem isPath_append_of_disjoint_tail {x y z : V}
    {p : G.Walk x y} {q : G.Walk y z} (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : p.support.Disjoint q.support.tail) : (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append]
  exact hp.support_nodup.append hq.support_nodup.tail hdisj

/-- A proper initial section of a simple cycle is a path. -/
theorem isCycle_isPath_take_of_lt {x : V} {c : G.Walk x x}
    (hc : c.IsCycle) {k : Nat} (hk : k < c.length) : (c.take k).IsPath := by
  have hdrop : ¬ (c.drop k).Nil := by
    rw [Walk.nil_drop_iff]
    omega
  have hcyc : ((c.take k).append (c.drop k)).IsCycle := by
    simpa using hc
  exact hcyc.isPath_of_append_left hdrop

theorem isCycle_length_take_of_lt {x : V} {c : G.Walk x x}
    (_hc : c.IsCycle) {k : Nat} (hk : k < c.length) :
    (c.take k).length = k := by
  simp [Nat.min_eq_left (Nat.le_of_lt hk)]

/-- Rotating a cycle to any vertex on it preserves its length and simplicity. -/
theorem isCycle_exists_rooted_cycle [DecidableEq V] {x y : V} {c : G.Walk x x}
    (hc : c.IsCycle) (hy : y ∈ c.support) :
    ∃ c' : G.Walk y y, c'.IsCycle ∧ c'.length = c.length ∧
      ∀ z, z ∈ c'.support ↔ z ∈ c.support := by
  refine ⟨c.rotate y hy, hc.rotate hy, by simp, ?_⟩
  intro z
  exact c.mem_support_rotate_iff y hy

/-! ## A path entering a monochromatic cycle -/

/-- If a path starts in `B`, immediately enters `A`, and meets an all-`A`
cycle only at its endpoint, its prefixes followed by initial pieces of the
cycle realize every positive length below the cycle length. -/
theorem hasABPathLengths_of_path_to_left_cycle {A B : Set V}
    (hdisj : Disjoint A B) {c₀ u x : V} {c : G.Walk c₀ c₀}
    (hc : c.IsCycle) (hxC : x ∈ c.support)
    (hcA : ∀ z, z ∈ c.support → z ∈ A)
    (q : G.Walk u x) (hq : q.IsPath) (huB : u ∈ B)
    (hqA : ∀ i, 1 ≤ i → i ≤ q.length → q.getVert i ∈ A)
    (hmeet : ∀ z, z ∈ q.support → z ∈ c.support → z = x) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  classical
  intro ell hell₁ hellC
  by_cases hellq : ell ≤ q.length
  · apply hasABPathLength_of_path_segment hq (i := 0) (ell := ell)
    · simpa using hellq
    · simp only [Walk.getVert_zero, zero_add]
      exact Or.inr ⟨huB, hqA ell hell₁ hellq⟩
  · let c' : G.Walk x x := c.rotate x hxC
    let k := ell - q.length
    let r : G.Walk x (c'.getVert k) := c'.take k
    have hkpos : 1 ≤ k := by simp only [k]; omega
    have hklt : k < c'.length := by
      simp only [k, c', Walk.length_rotate]
      omega
    have hrcycle : c'.IsCycle := hc.rotate hxC
    have hr : r.IsPath := by
      exact isCycle_isPath_take_of_lt hrcycle hklt
    have hrlen : r.length = k := isCycle_length_take_of_lt hrcycle hklt
    have hrstart_not_tail : x ∉ r.support.tail := by
      have hrnodup := hr.support_nodup
      rw [← r.cons_tail_support] at hrnodup
      exact (List.nodup_cons.mp hrnodup).1
    have hrsub : ∀ z, z ∈ r.support → z ∈ c'.support := by
      intro z hz
      exact (Walk.isSubwalk_take c' k).support_subset hz
    have hq_r_disj : q.support.Disjoint r.support.tail := by
      intro z hzq hzr
      have hzc' : z ∈ c'.support := hrsub z (List.mem_of_mem_tail hzr)
      have hzc : z ∈ c.support := (c.mem_support_rotate_iff x hxC).mp hzc'
      have hzx : z = x := hmeet z hzq hzc
      exact hrstart_not_tail (hzx ▸ hzr)
    have happ : (q.append r).IsPath := isPath_append_of_disjoint_tail hq hr hq_r_disj
    have hendA : c'.getVert k ∈ A := by
      apply hcA (c'.getVert k)
      apply (c.mem_support_rotate_iff x hxC).mp
      exact c'.getVert_mem_support k
    refine ⟨u, c'.getVert k, q.append r, happ, ?_, Or.inr ⟨huB, hendA⟩⟩
    rw [Walk.length_append, hrlen]
    simp only [k]
    omega

/-- Symmetric form when the cycle lies in the right part. -/
theorem hasABPathLengths_of_path_to_right_cycle {A B : Set V}
    (hdisj : Disjoint A B) {c₀ u x : V} {c : G.Walk c₀ c₀}
    (hc : c.IsCycle) (hxC : x ∈ c.support)
    (hcB : ∀ z, z ∈ c.support → z ∈ B)
    (q : G.Walk u x) (hq : q.IsPath) (huA : u ∈ A)
    (hqB : ∀ i, 1 ≤ i → i ≤ q.length → q.getVert i ∈ B)
    (hmeet : ∀ z, z ∈ q.support → z ∈ c.support → z = x) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  intro ell hell₁ hellC
  exact (hasABPathLengths_of_path_to_left_cycle (A := B) (B := A) hdisj.symm hc hxC hcB
    q hq huA hqB hmeet ell hell₁ hellC).symm_parts

/-- A shortest path from the right part to an all-left cycle starts in the
right part, has all its later vertices in the left part, and first meets the
cycle at its endpoint. -/
theorem exists_clean_path_to_left_cycle [Fintype V] {A B : Set V}
    (hconn : G.Connected) (hcover : A ∪ B = Set.univ)
    (hdisj : Disjoint A B) (hB : B.Nonempty)
    {c₀ : V} {c : G.Walk c₀ c₀} (hcA : ∀ z, z ∈ c.support → z ∈ A) :
    ∃ u x, ∃ q : G.Walk u x,
      u ∈ B ∧ x ∈ c.support ∧ q.IsPath ∧
      (∀ i, 1 ≤ i → i ≤ q.length → q.getVert i ∈ A) ∧
      (∀ z, z ∈ q.support → z ∈ c.support → z = x) := by
  classical
  let right : Finset V := Finset.univ.filter (· ∈ B)
  let cyc : Finset V := c.support.toFinset
  let pairs : Finset (V × V) := right ×ˢ cyc
  have hright : right.Nonempty := by
    obtain ⟨b, hb⟩ := hB
    exact ⟨b, by simp [right, hb]⟩
  have hcyc : cyc.Nonempty := by
    exact ⟨c₀, by simp [cyc]⟩
  have hpairs : pairs.Nonempty := hright.product hcyc
  obtain ⟨ux, hux, hmin⟩ := pairs.exists_min_image (fun ux => G.dist ux.1 ux.2) hpairs
  let u := ux.1
  let x := ux.2
  have huB : u ∈ B := by
    have := (Finset.mem_product.mp hux).1
    simpa [u, right] using this
  have hxC : x ∈ c.support := by
    have := (Finset.mem_product.mp hux).2
    simpa [x, cyc] using this
  obtain ⟨q, hq, hqlen⟩ := hconn.exists_path_of_dist u x
  refine ⟨u, x, q, huB, hxC, hq, ?_, ?_⟩
  · intro i hi₁ hiq
    have hiB : q.getVert i ∉ B := by
      intro hBi
      have hpair_i : (q.getVert i, x) ∈ pairs := by
        apply Finset.mem_product.mpr
        constructor
        · simp [right, hBi]
        · simpa [cyc] using hxC
      have hmin_i := hmin (q.getVert i, x) hpair_i
      change G.dist u x ≤ G.dist (q.getVert i) x at hmin_i
      have hdropDist : (q.drop i).length = G.dist (q.getVert i) x := by
        exact length_eq_dist_of_subwalk hqlen (Walk.isSubwalk_drop q i)
      rw [Walk.drop_length, hqlen] at hdropDist
      rw [← hqlen, ← hdropDist] at hmin_i
      omega
    by_contra hiA
    exact hiB ((mem_right_iff_not_mem_left hcover hdisj).mpr hiA)
  · intro z hzq hzc
    obtain ⟨i, hiz, hiq⟩ := Walk.mem_support_iff_exists_getVert.mp hzq
    have hpair_z : (u, z) ∈ pairs := by
      apply Finset.mem_product.mpr
      constructor
      · simp [right, huB]
      · simpa [cyc] using hzc
    have hmin_z := hmin (u, z) hpair_z
    change G.dist u x ≤ G.dist u z at hmin_z
    have htakeDist : (q.take i).length = G.dist u z := by
      have hsub := Walk.isSubwalk_take q i
      have := length_eq_dist_of_subwalk hqlen hsub
      simpa [hiz] using this
    rw [Walk.take_length, Nat.min_eq_left hiq] at htakeDist
    rw [← hqlen, ← htakeDist] at hmin_z
    have hiEq : i = q.length := by omega
    rw [← hiz, hiEq, q.getVert_length]

/-- Connectedness supplies the clean entering path required by
`hasABPathLengths_of_path_to_left_cycle`. -/
theorem hasABPathLengths_of_left_cycle [Fintype V] {A B : Set V}
    (hconn : G.Connected) (hcover : A ∪ B = Set.univ)
    (hdisj : Disjoint A B) (hB : B.Nonempty)
    {c₀ : V} {c : G.Walk c₀ c₀} (hc : c.IsCycle)
    (hcA : ∀ z, z ∈ c.support → z ∈ A) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  obtain ⟨u, x, q, huB, hxC, hq, hqA, hmeet⟩ :=
    exists_clean_path_to_left_cycle hconn hcover hdisj hB hcA
  exact hasABPathLengths_of_path_to_left_cycle hdisj hc hxC hcA q hq huB hqA hmeet

/-- Symmetric connected form for a cycle contained in `B`. -/
theorem hasABPathLengths_of_right_cycle [Fintype V] {A B : Set V}
    (hconn : G.Connected) (hcover : A ∪ B = Set.univ)
    (hdisj : Disjoint A B) (hA : A.Nonempty)
    {c₀ : V} {c : G.Walk c₀ c₀} (hc : c.IsCycle)
    (hcB : ∀ z, z ∈ c.support → z ∈ B) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  intro ell hell₁ hellC
  exact (hasABPathLengths_of_left_cycle (G := G) (A := B) (B := A)
    hconn (by simpa [Set.union_comm] using hcover) hdisj.symm hA hc hcB ell hell₁ hellC).symm_parts

/-! ## An external neighbour at a colour boundary of a cycle -/

/-- Chordlessness is unchanged by centering a closed walk at another vertex. -/
theorem Walk.IsChordless.rotate [DecidableEq V] {x₀ x : V} {c : G.Walk x₀ x₀}
    (h : c.IsChordless) (hx : x ∈ c.support) : (c.rotate x hx).IsChordless := by
  classical
  rw [Walk.isChordless_iff_forall_mem_edges] at h ⊢
  intro u v hu hv huv
  have hu' : u ∈ c.support := (c.mem_support_rotate_iff x hx).mp hu
  have hv' : v ∈ c.support := (c.mem_support_rotate_iff x hx).mp hv
  exact (c.rotate_edges x hx).perm.mem_iff.mpr (h hu' hv' huv)

/-- Chordlessness is unchanged by reversing a walk. -/
theorem Walk.IsChordless.reverse {u v : V} {p : G.Walk u v}
    (h : p.IsChordless) : p.reverse.IsChordless := by
  rw [Walk.isChordless_iff_forall_mem_edges] at h ⊢
  intro x y hx hy hxy
  have hx' : x ∈ p.support := by simpa [Walk.support_reverse] using hx
  have hy' : y ∈ p.support := by simpa [Walk.support_reverse] using hy
  simpa [Walk.edges_reverse] using h hx' hy' hxy

/-- In the edge graph traced by a closed walk, if some traced edge has both
ends in `B` while some traced vertex lies in the disjoint part `A`, then the
walk has two consecutive traced edges with part pattern `A,B,B`.

This is the elementary cut argument behind the colour-boundary step: take the
set of `B`-vertices incident with a traced `B`--`B` edge and cross its boundary
inside the connected subgraph traced by the walk. -/
theorem exists_ABB_of_mem_edge_and_mem_support {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} (c : G.Walk x₀ x₀)
    (hA : ∃ a, a ∈ c.support ∧ a ∈ A)
    (hBB : ∃ x y, x ∈ B ∧ y ∈ B ∧ s(x, y) ∈ c.edges) :
    ∃ z x y, z ∈ A ∧ x ∈ B ∧ y ∈ B ∧ z ≠ y ∧
      s(z, x) ∈ c.edges ∧ s(x, y) ∈ c.edges := by
  classical
  let T : Set V := {x | x ∈ B ∧ ∃ y, y ∈ B ∧ s(x, y) ∈ c.edges}
  obtain ⟨a, haC, haA⟩ := hA
  obtain ⟨x₀', y₀, hx₀B, hy₀B, hx₀y₀⟩ := hBB
  have hx₀T : x₀' ∈ T := ⟨hx₀B, y₀, hy₀B, hx₀y₀⟩
  have haT : a ∉ T := by
    intro ha
    exact Set.disjoint_left.mp hdisj haA ha.1
  have hx₀C : x₀' ∈ c.support := c.fst_mem_support_of_mem_edges hx₀y₀
  have hpre := c.toSubgraph_connected.preconnected
  rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph] at hpre
  obtain ⟨p, hp⟩ := hpre (by simpa using hx₀C) (by simpa using haC)
  obtain ⟨d, hdp, hdT, hdnotT⟩ := p.exists_boundary_dart T hx₀T haT
  have hpedge : s(d.fst, d.snd) ∈ p.edges := by
    rw [Walk.edges, List.mem_map]
    exact ⟨d, hdp, rfl⟩
  have hcedge : s(d.fst, d.snd) ∈ c.edges := by
    rw [← Walk.adj_toSubgraph_iff_mem_edges]
    exact hp.2 (Walk.adj_toSubgraph_iff_mem_edges.mpr hpedge)
  obtain ⟨hxB, y, hyB, hxy⟩ := hdT
  have hzA : d.snd ∈ A := by
    have hzpart : d.snd ∈ A ∨ d.snd ∈ B := by
      have : d.snd ∈ A ∪ B := by simpa [hcover]
      exact this
    rcases hzpart with hzA | hzB
    · exact hzA
    · exfalso
      apply hdnotT
      refine ⟨hzB, d.fst, hxB, ?_⟩
      simpa [Sym2.eq_swap] using hcedge
  have hzy : d.snd ≠ y := by
    intro h
    exact Set.disjoint_left.mp hdisj (h ▸ hzA) hyB
  exact ⟨d.snd, d.fst, y, hzA, hxB, hyB, hzy, by
    simpa [Sym2.eq_swap] using hcedge, hxy⟩

private theorem isPath_cons_cycle_take_of_outside {z x : V} {c : G.Walk x x}
    (hc : c.IsCycle) (hzx : G.Adj z x) (hz : z ∉ c.support)
    {k : Nat} (hk : k < c.length) : ((c.take k).cons hzx).IsPath := by
  rw [Walk.cons_isPath_iff]
  exact ⟨isCycle_isPath_take_of_lt hc hk,
    fun h => hz ((Walk.isSubwalk_take c k).support_subset h)⟩

/-- On a chordless cycle, a neighbour of the root which lies on the cycle is
one of the two cyclic neighbours. -/
theorem eq_snd_or_penultimate_of_adj_of_isChordless {x y : V}
    {c : G.Walk x x} (hc : c.IsCycle) (hchordless : c.IsChordless)
    (hy : y ∈ c.support) (hxy : G.Adj x y) :
    y = c.snd ∨ y = c.penultimate := by
  have hedge : s(x, y) ∈ c.edges :=
    hchordless.mem_edges c.start_mem_support hy hxy
  have htailNotNil : ¬ c.tail.Nil := by
    have hlen := Walk.length_tail_add_one hc.not_nil
    have hthree := hc.three_le_length
    rw [Walk.not_nil_iff_lt_length]
    omega
  have hpen : c.penultimate = c.tail.penultimate := by
    have h := Walk.penultimate_cons_of_not_nil (c.adj_snd hc.not_nil) c.tail htailNotNil
    rw [c.cons_tail_eq hc.not_nil] at h
    exact h
  rw [← c.cons_tail_eq hc.not_nil, Walk.edges_cons, List.mem_cons] at hedge
  rcases hedge with hedge | hedge
  · left
    rw [Sym2.eq, Sym2.rel_iff] at hedge
    rcases hedge with hedge | hedge
    · exact hedge.2
    · exact (hxy.ne hedge.2.symm).elim
  · right
    exact (hc.isPath_tail.eq_penultimate_of_mem_edges hedge).trans hpen.symm

/-- Minimum degree three forces every vertex of a chordless cycle to have a
neighbour outside that cycle. -/
theorem exists_adj_not_mem_cycle_of_three_le_degree [Fintype V]
    [DecidableRel G.Adj] {x : V} {c : G.Walk x x}
    (hc : c.IsCycle) (hchordless : c.IsChordless) (hdeg : 3 ≤ G.degree x) :
    ∃ z, G.Adj x z ∧ z ∉ c.support := by
  classical
  by_contra h
  have hall : ∀ z, G.Adj x z → z ∈ c.support := by
    intro z hxz
    by_contra hz
    exact h ⟨z, hxz, hz⟩
  have hsub : G.neighborFinset x ⊆ {c.snd, c.penultimate} := by
    intro z hz
    have hxz : G.Adj x z := by simpa using hz
    rcases eq_snd_or_penultimate_of_adj_of_isChordless hc hchordless (hall z hxz) hxz with
      hzs | hzp
    · simp [hzs]
    · simp [hzp]
  have hcard : (G.neighborFinset x).card ≤ 2 := by
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [SimpleGraph.degree] at hdeg
  omega

private theorem isPath_cons_cycle_take_of_predecessor {x : V} {c : G.Walk x x}
    (hc : c.IsCycle) (hclose : G.Adj (c.getVert (c.length - 1)) x)
    {k : Nat} (hk : k < c.length - 1) : ((c.take k).cons hclose).IsPath := by
  rw [Walk.cons_isPath_iff]
  refine ⟨isCycle_isPath_take_of_lt hc (by omega), ?_⟩
  intro hmem
  obtain ⟨i, hi, hik⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
  have hi' : i ≤ k := by
    rw [Walk.take_length] at hik
    exact (le_min_iff.mp hik).1
  have hiC : c.getVert i = c.getVert (c.length - 1) := by
    simpa [Walk.take_getVert, Nat.min_eq_right hi'] using hi
  have := hc.getVert_injOn'
    (show i ≤ c.length - 1 by omega) (show c.length - 1 ≤ c.length - 1 by omega) hiC
  omega

/-- The chordless-cycle construction at the heart of the mixed-colour case:
if three consecutive cycle vertices have colours `A,B,B` and the middle
`B` vertex has a neighbour outside the cycle, then all shorter crossing
path lengths occur.  The neighbour may lie in either part. -/
theorem hasABPathLengths_of_boundary_external_neighbor {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ z : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    (hpredA : c.getVert (c.length - 1) ∈ A)
    (hrootB : x₀ ∈ B) (hsndB : c.getVert 1 ∈ B)
    (hzroot : G.Adj z x₀) (hzoutside : z ∉ c.support) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  intro ell hell₁ hellC
  have hclose : G.Adj (c.getVert (c.length - 1)) x₀ := by
    have heq : c.length - 1 + 1 = c.length := by omega
    simpa [heq] using c.adj_getVert_succ (i := c.length - 1) (by omega)
  by_cases hellone : ell = 1
  · subst ell
    exact ⟨c.getVert (c.length - 1), x₀, hclose.toWalk,
      Walk.IsPath.of_adj hclose, by simp, Or.inl ⟨hpredA, hrootB⟩⟩
  have helltwo : 2 ≤ ell := by omega
  have hk : ell - 1 < c.length - 1 := by omega
  have hzpart : z ∈ A ∨ z ∈ B := by
    have : z ∈ A ∪ B := by simpa [hcover]
    exact this
  rcases hzpart with hzA | hzB
  · let cr : G.Walk x₀ x₀ := c.reverse
    let y := cr.getVert (ell - 1)
    have hcr : cr.IsCycle := hc.reverse
    have hcrlen : cr.length = c.length := by simp [cr]
    have hzcr : z ∉ cr.support := by simpa [cr] using hzoutside
    have hsndroot : G.Adj (c.getVert 1) x₀ := by
      simpa using (c.adj_getVert_succ (i := 0) (by omega)).symm
    have hpz : ((cr.take (ell - 1)).cons hzroot).IsPath :=
      isPath_cons_cycle_take_of_outside hcr hzroot hzcr (by simp [cr]; omega)
    have hcrpred : cr.getVert (cr.length - 1) = c.getVert 1 := by
      simp only [cr, Walk.getVert_reverse, Walk.length_reverse]
      congr 1
      omega
    have hcrclose : G.Adj (cr.getVert (cr.length - 1)) x₀ := by
      simpa [hcrpred] using hsndroot
    have hpone' : ((cr.take (ell - 1)).cons hsndroot).IsPath := by
      have hpone := isPath_cons_cycle_take_of_predecessor hcr hcrclose
        (by simpa [hcrlen] using hk)
      simpa [hcrpred] using hpone
    have hlenz : ((cr.take (ell - 1)).cons hzroot).length = ell := by
      simp [cr]
      omega
    have hlenone : ((cr.take (ell - 1)).cons hsndroot).length = ell := by
      simp [cr]
      omega
    by_cases hyA : y ∈ A
    · refine ⟨c.getVert 1, y, (cr.take (ell - 1)).cons hsndroot,
        hpone', hlenone, Or.inr ⟨hsndB, ?_⟩⟩
      exact hyA
    · have hyB : y ∈ B := (mem_right_iff_not_mem_left hcover hdisj).mpr hyA
      exact ⟨z, y, (cr.take (ell - 1)).cons hzroot,
        hpz, hlenz, Or.inl ⟨hzA, hyB⟩⟩
  · let y := c.getVert (ell - 1)
    have hpz : ((c.take (ell - 1)).cons hzroot).IsPath :=
      isPath_cons_cycle_take_of_outside hc hzroot hzoutside (by omega)
    have hppred : ((c.take (ell - 1)).cons hclose).IsPath :=
      isPath_cons_cycle_take_of_predecessor hc hclose hk
    have hlenz : ((c.take (ell - 1)).cons hzroot).length = ell := by
      simp
      omega
    have hlenpred : ((c.take (ell - 1)).cons hclose).length = ell := by
      simp
      omega
    by_cases hyA : y ∈ A
    · exact ⟨z, y, (c.take (ell - 1)).cons hzroot,
        hpz, hlenz, Or.inr ⟨hzB, hyA⟩⟩
    · have hyB : y ∈ B := (mem_right_iff_not_mem_left hcover hdisj).mpr hyA
      exact ⟨c.getVert (c.length - 1), y, (c.take (ell - 1)).cons hclose,
        hppred, hlenpred, Or.inl ⟨hpredA, hyB⟩⟩

/-- The preceding boundary construction with the outside neighbour obtained
from chordlessness and minimum degree three. -/
theorem hasABPathLengths_of_chordless_boundary [Fintype V]
    [DecidableRel G.Adj] {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    (hchordless : c.IsChordless) (hdeg : 3 ≤ G.degree x₀)
    (hpredA : c.getVert (c.length - 1) ∈ A)
    (hrootB : x₀ ∈ B) (hsndB : c.getVert 1 ∈ B) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  obtain ⟨z, hzroot, hzoutside⟩ :=
    exists_adj_not_mem_cycle_of_three_le_degree hc hchordless hdeg
  exact hasABPathLengths_of_boundary_external_neighbor hcover hdisj hc
    hpredA hrootB hsndB hzroot.symm hzoutside

/-- A coordinate-free form of the chordless boundary argument.  Two
consecutive cycle edges with part pattern `A,B,B` determine the required
rooting (possibly after reversing the cycle). -/
theorem hasABPathLengths_of_chordless_ABB [Fintype V]
    [DecidableRel G.Adj] {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    (hchordless : c.IsChordless) (hdeg : ∀ x, x ∈ c.support → 3 ≤ G.degree x)
    {z x y : V} (hzA : z ∈ A) (hxB : x ∈ B) (hyB : y ∈ B)
    (hzy : z ≠ y) (hzx : s(z, x) ∈ c.edges) (hxy : s(x, y) ∈ c.edges) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  classical
  have hxC : x ∈ c.support := c.fst_mem_support_of_mem_edges hxy
  have hzC : z ∈ c.support := c.fst_mem_support_of_mem_edges hzx
  have hyC : y ∈ c.support := c.snd_mem_support_of_mem_edges hxy
  let c' : G.Walk x x := c.rotate x hxC
  have hc' : c'.IsCycle := hc.rotate hxC
  have hchordless' : c'.IsChordless := Walk.IsChordless.rotate hchordless hxC
  have hzC' : z ∈ c'.support := (c.mem_support_rotate_iff x hxC).mpr hzC
  have hyC' : y ∈ c'.support := (c.mem_support_rotate_iff x hxC).mpr hyC
  have hzxAdj : G.Adj x z := (c.adj_of_mem_edges hzx).symm
  have hxyAdj : G.Adj x y := c.adj_of_mem_edges hxy
  have hzpos := eq_snd_or_penultimate_of_adj_of_isChordless hc' hchordless' hzC' hzxAdj
  have hypos := eq_snd_or_penultimate_of_adj_of_isChordless hc' hchordless' hyC' hxyAdj
  rcases hzpos with hzsnd | hzpred <;> rcases hypos with hysnd | hypred
  · exact (hzy (hzsnd.trans hysnd.symm)).elim
  · let cr : G.Walk x x := c'.reverse
    have hcr : cr.IsCycle := hc'.reverse
    have hcrChordless : cr.IsChordless := Walk.IsChordless.reverse hchordless'
    have hcrpredA : cr.getVert (cr.length - 1) ∈ A := by
      change cr.penultimate ∈ A
      simpa [cr, Walk.penultimate_reverse, hzsnd] using hzA
    have hcrsndB : cr.getVert 1 ∈ B := by
      change cr.snd ∈ B
      simpa [cr, Walk.snd_reverse, hypred] using hyB
    intro ell hell₁ hellC
    apply hasABPathLengths_of_chordless_boundary hcover hdisj hcr hcrChordless
      (by simpa [cr, c'] using hdeg x hxC) hcrpredA hxB hcrsndB ell hell₁
    simpa [cr, c'] using hellC
  · have hc'predA : c'.getVert (c'.length - 1) ∈ A := by
      change c'.penultimate ∈ A
      simpa [hzpred] using hzA
    have hc'sndB : c'.getVert 1 ∈ B := by
      change c'.snd ∈ B
      simpa [hysnd] using hyB
    intro ell hell₁ hellC
    apply hasABPathLengths_of_chordless_boundary hcover hdisj hc' hchordless'
      (by simpa [c'] using hdeg x hxC) hc'predA hxB hc'sndB ell hell₁
    simpa [c'] using hellC
  · exact (hzy (hzpred.trans hypred.symm)).elim

/-- If a chordless cycle meets both parts and one of its traced edges stays
inside a part, then it supplies crossing paths of every shorter length. -/
theorem hasABPathLengths_of_chordless_internal_edge [Fintype V]
    [DecidableRel G.Adj] {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    (hchordless : c.IsChordless) (hdeg : ∀ x, x ∈ c.support → 3 ≤ G.degree x)
    (hA : ∃ a, a ∈ c.support ∧ a ∈ A)
    (hB : ∃ b, b ∈ c.support ∧ b ∈ B)
    (hint : ∃ x y, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧
      ¬ InOppositeParts A B x y) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  classical
  obtain ⟨x, y, hxC, hyC, hxy, hxyInt⟩ := hint
  have hxyEdge : s(x, y) ∈ c.edges := hchordless.mem_edges hxC hyC hxy
  have hsame : x ∈ A ↔ y ∈ A :=
    (not_inOppositeParts_iff_same_left hcover hdisj).mp hxyInt
  by_cases hxA : x ∈ A
  · have hyA : y ∈ A := hsame.mp hxA
    obtain ⟨z, u, v, hzB, huA, hvA, hzv, hzu, huv⟩ :=
      exists_ABB_of_mem_edge_and_mem_support
        (A := B) (B := A) (by simpa [Set.union_comm] using hcover) hdisj.symm c hB
        ⟨x, y, hxA, hyA, hxyEdge⟩
    intro ell hell₁ hellC
    exact (hasABPathLengths_of_chordless_ABB
      (G := G) (A := B) (B := A) (by simpa [Set.union_comm] using hcover) hdisj.symm
      hc hchordless hdeg hzB huA hvA hzv hzu huv ell hell₁ hellC).symm_parts
  · have hxB : x ∈ B := (mem_right_iff_not_mem_left hcover hdisj).mpr hxA
    have hyB : y ∈ B := by
      apply (mem_right_iff_not_mem_left hcover hdisj).mpr
      exact fun hyA => hxA (hsame.mpr hyA)
    obtain ⟨z, u, v, hzA, huB, hvB, hzv, hzu, huv⟩ :=
      exists_ABB_of_mem_edge_and_mem_support hcover hdisj c hA
        ⟨x, y, hxB, hyB, hxyEdge⟩
    exact hasABPathLengths_of_chordless_ABB hcover hdisj hc hchordless hdeg
      hzA huB hvB hzv hzu huv

/-! ## Entering an alternating cycle from a same-part edge -/

/-- Choose, among all oriented same-part edges and all cycle vertices, a
shortest route from the head of the edge to the cycle.  Minimality makes
every edge of that route crossing, keeps the other end of the initial edge
off the route, and makes the route meet the cycle only at its endpoint. -/
theorem exists_clean_path_from_internal_edge_to_cycle [Fintype V]
    [DecidableRel G.Adj] {A B : Set V}
    (hconn : G.Connected) (hdisj : Disjoint A B)
    (hnot : ¬ G.IsBipartiteWith A B)
    {c₀ : V} (c : G.Walk c₀ c₀) :
    ∃ a b x, ∃ q : G.Walk b x,
      G.Adj a b ∧ ¬ InOppositeParts A B a b ∧ x ∈ c.support ∧
      q.IsPath ∧ a ∉ q.support ∧
      (a ∈ c.support → b ∈ c.support) ∧
      (∀ z, z ∈ q.support → z ∈ c.support → z = x) ∧
      (∀ i, i < q.length →
        InOppositeParts A B (q.getVert i) (q.getVert (i + 1))) := by
  classical
  let internal : Finset (V × V) :=
    (Finset.univ ×ˢ Finset.univ).filter fun ab =>
      G.Adj ab.1 ab.2 ∧ ¬ InOppositeParts A B ab.1 ab.2
  let cyc : Finset V := c.support.toFinset
  let candidates : Finset ((V × V) × V) := internal ×ˢ cyc
  obtain ⟨a₀, b₀, hab₀, hint₀⟩ :=
    exists_internal_edge_of_not_isBipartiteWith hdisj hnot
  have hinternal : internal.Nonempty := by
    refine ⟨(a₀, b₀), ?_⟩
    simp [internal, hab₀, hint₀]
  have hcyc : cyc.Nonempty := ⟨c₀, by simp [cyc]⟩
  have hcandidates : candidates.Nonempty := hinternal.product hcyc
  obtain ⟨abx, habx, hmin⟩ := candidates.exists_min_image
    (fun abx => G.dist abx.1.2 abx.2) hcandidates
  let a := abx.1.1
  let b := abx.1.2
  let x := abx.2
  have habMem : (a, b) ∈ internal := by
    exact (Finset.mem_product.mp habx).1
  have hab : G.Adj a b := by
    simpa [internal, a, b] using (Finset.mem_filter.mp habMem).2.1
  have habInternal : ¬ InOppositeParts A B a b := by
    simpa [internal, a, b] using (Finset.mem_filter.mp habMem).2.2
  have hxC : x ∈ c.support := by
    have := (Finset.mem_product.mp habx).2
    simpa [cyc, x] using this
  obtain ⟨q, hq, hqlen⟩ := hconn.exists_path_of_dist b x
  have hqcross : ∀ i, i < q.length →
      InOppositeParts A B (q.getVert i) (q.getVert (i + 1)) := by
    intro i hi
    by_contra hint
    have hadj := q.adj_getVert_succ hi
    have hcand : ((q.getVert i, q.getVert (i + 1)), x) ∈ candidates := by
      apply Finset.mem_product.mpr
      constructor
      · simp [internal, hadj, hint]
      · simpa [cyc] using hxC
    have hmini := hmin ((q.getVert i, q.getVert (i + 1)), x) hcand
    change G.dist b x ≤ G.dist (q.getVert (i + 1)) x at hmini
    have hdrop : (q.drop (i + 1)).length = G.dist (q.getVert (i + 1)) x :=
      length_eq_dist_of_subwalk hqlen (Walk.isSubwalk_drop q (i + 1))
    rw [← hdrop, Walk.drop_length, ← hqlen] at hmini
    omega
  have haNotQ : a ∉ q.support := by
    intro haQ
    obtain ⟨i, hia, hiq⟩ := Walk.mem_support_iff_exists_getVert.mp haQ
    have hiPos : 1 ≤ i := by
      by_contra hi
      have : i = 0 := by omega
      subst i
      exact hab.ne (by simpa using hia.symm)
    have hrevInternal : ¬ InOppositeParts A B b a := by
      intro hba
      exact habInternal hba.symm
    have hcand : ((b, a), x) ∈ candidates := by
      apply Finset.mem_product.mpr
      constructor
      · simp [internal, hab.symm, hrevInternal]
      · simpa [cyc] using hxC
    have hmini := hmin ((b, a), x) hcand
    change G.dist b x ≤ G.dist a x at hmini
    have hdrop : (q.drop i).length = G.dist a x := by
      have hd := length_eq_dist_of_subwalk hqlen (Walk.isSubwalk_drop q i)
      simpa [hia] using hd
    rw [← hdrop, Walk.drop_length, ← hqlen] at hmini
    omega
  have hmeet : ∀ z, z ∈ q.support → z ∈ c.support → z = x := by
    intro z hzq hzc
    obtain ⟨i, hiz, hiq⟩ := Walk.mem_support_iff_exists_getVert.mp hzq
    have hcand : ((a, b), z) ∈ candidates := by
      apply Finset.mem_product.mpr
      constructor
      · exact habMem
      · simpa [cyc] using hzc
    have hmini := hmin ((a, b), z) hcand
    change G.dist b x ≤ G.dist b z at hmini
    have htake : (q.take i).length = G.dist b z := by
      have ht := length_eq_dist_of_subwalk hqlen (Walk.isSubwalk_take q i)
      simpa [hiz] using ht
    rw [← htake, Walk.take_length, Nat.min_eq_left hiq, ← hqlen] at hmini
    have hiEq : i = q.length := by omega
    rw [← hiz, hiEq, q.getVert_length]
  have haC_imp_hbC : a ∈ c.support → b ∈ c.support := by
    intro haC
    have hrevInternal : ¬ InOppositeParts A B b a := by
      intro hba
      exact habInternal hba.symm
    have hcand : ((b, a), a) ∈ candidates := by
      apply Finset.mem_product.mpr
      constructor
      · simp [internal, hab.symm, hrevInternal]
      · simpa [cyc] using haC
    have hmini := hmin ((b, a), a) hcand
    change G.dist b x ≤ G.dist a a at hmini
    rw [dist_self] at hmini
    have hqzero : q.length = 0 := by omega
    have hbx : b = x := Walk.eq_of_length_eq_zero hqzero
    simpa [hbx] using hxC
  exact ⟨a, b, x, q, hab, habInternal, hxC, hq, haNotQ,
    haC_imp_hbC, hmeet, hqcross⟩

/-- If every edge whose ends lie on the displayed cycle crosses the
partition, then a nearest same-part edge can be joined to almost the whole
cycle to give the long alternating certificate needed for every shorter
length. -/
theorem hasABPathLengths_of_alternating_cycle [Fintype V]
    [DecidableRel G.Adj] {A B : Set V}
    (hconn : G.Connected) (hcover : A ∪ B = Set.univ)
    (hdisj : Disjoint A B) (hnot : ¬ G.IsBipartiteWith A B)
    {c₀ : V} {c : G.Walk c₀ c₀} (hc : c.IsCycle)
    (hcycleCross : ∀ ⦃u v⦄, u ∈ c.support → v ∈ c.support → G.Adj u v →
      InOppositeParts A B u v) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  classical
  obtain ⟨a, b, x, q, hab, habInternal, hxC, hq, haNotQ,
      haC_imp_hbC, hmeet, hqcross⟩ :=
    exists_clean_path_from_internal_edge_to_cycle hconn hdisj hnot c
  have haOutside : a ∉ c.support := by
    intro haC
    exact habInternal (hcycleCross haC (haC_imp_hbC haC) hab)
  let c' : G.Walk x x := c.rotate x hxC
  let r : G.Walk x (c'.getVert (c.length - 1)) := c'.take (c.length - 1)
  let q₀ : G.Walk a x := q.cons hab
  let p : G.Walk a (c'.getVert (c.length - 1)) := q₀.append r
  have hc' : c'.IsCycle := hc.rotate hxC
  have hc'len : c'.length = c.length := by simp [c']
  have hq₀ : q₀.IsPath := by
    change (q.cons hab).IsPath
    rw [Walk.cons_isPath_iff]
    exact ⟨hq, haNotQ⟩
  have hr : r.IsPath := by
    change (c'.take (c.length - 1)).IsPath
    apply isCycle_isPath_take_of_lt hc'
    have hthree := hc.three_le_length
    rw [hc'len]
    omega
  have hrlen : r.length = c.length - 1 := by
    change (c'.take (c.length - 1)).length = c.length - 1
    have hthree := hc.three_le_length
    simp [hc'len, Nat.min_eq_left (by omega)]
  have hrstartNotTail : x ∉ r.support.tail := by
    have hrnodup := hr.support_nodup
    rw [← r.cons_tail_support] at hrnodup
    exact (List.nodup_cons.mp hrnodup).1
  have hrsub : ∀ z, z ∈ r.support → z ∈ c.support := by
    intro z hzr
    have hzc' : z ∈ c'.support :=
      (Walk.isSubwalk_take c' (c.length - 1)).support_subset hzr
    exact (c.mem_support_rotate_iff x hxC).mp hzc'
  have hdisjQR : q₀.support.Disjoint r.support.tail := by
    intro z hzq₀ hzr
    have hzC := hrsub z (List.mem_of_mem_tail hzr)
    change z ∈ (q.cons hab).support at hzq₀
    rw [Walk.support_cons, List.mem_cons] at hzq₀
    rcases hzq₀ with hza | hzq
    · exact haOutside (hza ▸ hzC)
    · have hzx := hmeet z hzq hzC
      exact hrstartNotTail (hzx ▸ hzr)
  have hp : p.IsPath := isPath_append_of_disjoint_tail hq₀ hr hdisjQR
  have hplen : c.length ≤ p.length := by
    simp only [p, Walk.length_append, q₀, Walk.length_cons, hrlen]
    have hthree := hc.three_le_length
    omega
  have hpzero : p.getVert 0 = a := by simp [p, q₀]
  have hpone : p.getVert 1 = b := by
    cases q with
    | nil => simp [p, q₀, r, c']
    | cons h q => simp [p, q₀, r, c']
  have hpfirst : ¬ InOppositeParts A B (p.getVert 0) (p.getVert 1) := by
    simpa [hpzero, hpone] using habInternal
  have hpcross : ∀ i, 1 ≤ i → i < p.length →
      InOppositeParts A B (p.getVert i) (p.getVert (i + 1)) := by
    intro i hi₁ hip
    by_cases hiq₀ : i < q₀.length
    · have hiq : i - 1 < q.length := by
        simp only [q₀, Walk.length_cons] at hiq₀
        omega
      have hop := hqcross (i - 1) hiq
      have hpi : p.getVert i = q.getVert (i - 1) := by
        change (q₀.append r).getVert i = q.getVert (i - 1)
        rw [Walk.getVert_append, if_pos hiq₀]
        change (q.cons hab).getVert i = q.getVert (i - 1)
        exact Walk.getVert_cons q hab (by omega)
      have hpis : p.getVert (i + 1) = q.getVert i := by
        change (q₀.append r).getVert (i + 1) = q.getVert i
        rw [Walk.getVert_append]
        by_cases his : i + 1 < q₀.length
        · rw [if_pos his]
          change (q.cons hab).getVert (i + 1) = q.getVert i
          exact Walk.getVert_cons q hab (by omega)
        · rw [if_neg his]
          have hiend : i = q.length := by
            simp only [q₀, Walk.length_cons] at hiq₀ his
            omega
          have hsub : i + 1 - q₀.length = 0 := by
            simp only [q₀, Walk.length_cons]
            omega
          rw [hsub, Walk.getVert_zero, hiend, q.getVert_length]
      rw [hpi, hpis]
      simpa only [Nat.sub_add_cancel hi₁] using hop
    · have hir : i - q₀.length < r.length := by
        simp only [p, Walk.length_append] at hip
        omega
      have hpi : p.getVert i = r.getVert (i - q₀.length) := by
        change (q₀.append r).getVert i = r.getVert (i - q₀.length)
        rw [Walk.getVert_append, if_neg hiq₀]
      have hpis : p.getVert (i + 1) = r.getVert (i - q₀.length + 1) := by
        change (q₀.append r).getVert (i + 1) = r.getVert (i - q₀.length + 1)
        rw [Walk.getVert_append, if_neg (by omega : ¬ i + 1 < q₀.length)]
        congr 2
        omega
      rw [hpi, hpis]
      apply hcycleCross
      · exact hrsub _ (r.getVert_mem_support (i - q₀.length))
      · exact hrsub _ (r.getVert_mem_support (i - q₀.length + 1))
      · exact r.adj_getVert_succ hir
  exact hasABPathLength_of_internal_first_alternating_lt hcover hdisj hp
    hpfirst hpcross hplen

/-! ## The chordless case of the Gao--Huo--Ma lemma -/

/-! The following doubled-cycle lemma is also the basic indexing device for
the chorded-cycle case: every window of fewer than `c.length` consecutive
edges in `c ++ c` is simple. -/

/-- The membership bit word read twice around a cycle.  Its length is twice
the walk length (the repeated terminal vertex is omitted by `ofFn`). -/
private noncomputable def doubledCycleColorWord (A : Set V) {x₀ : V}
    (c : G.Walk x₀ x₀) : List Bool := by
  classical
  exact List.ofFn fun i : Fin (2 * c.length) => decide ((c.append c).getVert i ∈ A)

@[simp]
private theorem length_doubledCycleColorWord (A : Set V) {x₀ : V}
    (c : G.Walk x₀ x₀) :
    (doubledCycleColorWord A c).length = 2 * c.length := by
  simp [doubledCycleColorWord]

/-- The doubled traversal really is periodic by one cycle length. -/
private theorem getVert_append_self_add_length {x₀ : V} (c : G.Walk x₀ x₀)
    {i : Nat} (hi : i < c.length) :
    (c.append c).getVert (c.length + i) = (c.append c).getVert i := by
  rw [Walk.getVert_append, Walk.getVert_append, if_neg (by omega), if_pos hi]
  congr 1
  omega

/-- No cyclic arc of length `k` has its ends in opposite parts. -/
private def NoCrossingCycleArc (A B : Set V) {x₀ : V}
    (c : G.Walk x₀ x₀) (k : Nat) : Prop :=
  ∀ i, i < c.length →
    ¬ InOppositeParts A B ((c.append c).getVert i)
      ((c.append c).getVert (i + k))

/-- Reading twice around a cycle turns the circular equality supplied by a
missing arc length into an ordinary list period. -/
private theorem doubledCycleColorWord_hasPeriod {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} {c : G.Walk x₀ x₀} {k : Nat} (hk : k < c.length)
    (hno : NoCrossingCycleArc A B c k) :
    (doubledCycleColorWord A c).HasPeriod k := by
  classical
  rw [List.hasPeriod_iff_getElem?]
  intro i hi
  have hiw : i < 2 * c.length := by
    rw [length_doubledCycleColorWord] at hi
    omega
  have hikw : i + k < 2 * c.length := by
    rw [length_doubledCycleColorWord] at hi
    omega
  have hsame :
      ((c.append c).getVert i ∈ A ↔ (c.append c).getVert (i + k) ∈ A) := by
    by_cases hin : i < c.length
    · exact (not_inOppositeParts_iff_same_left hcover hdisj).mp (hno i hin)
    · let j := i - c.length
      have hj : j < c.length := by simp only [j]; omega
      have hjk : j + k < c.length := by simp only [j]; omega
      have hiEq : (c.append c).getVert i = (c.append c).getVert j := by
        have h := getVert_append_self_add_length c hj
        have hij : c.length + j = i := by simp only [j]; omega
        simpa [hij] using h
      have hikEq : (c.append c).getVert (i + k) =
          (c.append c).getVert (j + k) := by
        have h := getVert_append_self_add_length c hjk
        have hijk : c.length + (j + k) = i + k := by simp only [j]; omega
        simpa [hijk] using h
      simpa [hiEq, hikEq] using
        (not_inOppositeParts_iff_same_left hcover hdisj).mp (hno j hj)
  rw [List.getElem?_eq_getElem (by simp; omega),
    List.getElem?_eq_getElem (by simp; omega)]
  simp only [doubledCycleColorWord, List.getElem_ofFn, Option.some.injEq]
  exact Bool.decide_congr hsame

private theorem doubledCycleColorWord_hasPeriod_length (A : Set V)
    {x₀ : V} (c : G.Walk x₀ x₀) :
    (doubledCycleColorWord A c).HasPeriod c.length := by
  classical
  rw [List.hasPeriod_iff_getElem?]
  intro i hi
  have hin : i < c.length := by
    rw [length_doubledCycleColorWord] at hi
    omega
  have hi2 : i + c.length < 2 * c.length := by omega
  rw [List.getElem?_eq_getElem (by simp; omega),
    List.getElem?_eq_getElem (by simp; omega)]
  simp only [doubledCycleColorWord, List.getElem_ofFn, Option.some.injEq]
  apply congrArg fun v => decide (v ∈ A)
  simpa [Nat.add_comm] using (getVert_append_self_add_length c hin).symm

/-- Conversely, any short ordinary period of the doubled colour word says
that no cyclic arc of that length crosses the partition. -/
private theorem noCrossingCycleArc_of_doubledPeriod {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} {c : G.Walk x₀ x₀} {k : Nat} (hk : k < c.length)
    (hper : (doubledCycleColorWord A c).HasPeriod k) :
    NoCrossingCycleArc A B c k := by
  classical
  intro i hi
  have hidx : i < (doubledCycleColorWord A c).length - k := by
    rw [length_doubledCycleColorWord]
    omega
  have heq := List.hasPeriod_iff_getElem?.mp hper i hidx
  rw [List.getElem?_eq_getElem (by simp; omega),
    List.getElem?_eq_getElem (by simp; omega)] at heq
  simp only [doubledCycleColorWord, List.getElem_ofFn, Option.some.injEq] at heq
  apply (not_inOppositeParts_iff_same_left hcover hdisj).mpr
  exact decide_eq_decide.mp heq

/-- The least positive missing cyclic-arc length divides the cycle length.
This is the periodicity/gcd step in the Bondy--Simonovits--Verstraëte
argument, discharged using mathlib's Fine--Wilf theorem. -/
private theorem minimal_noCrossingCycleArc_dvd_length {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} {c : G.Walk x₀ x₀} {m : Nat}
    (hmpos : 1 ≤ m) (hmlt : m < c.length)
    (hm : NoCrossingCycleArc A B c m)
    (hmin : ∀ d, 1 ≤ d → d < m → ¬ NoCrossingCycleArc A B c d) :
    m ∣ c.length := by
  classical
  let w := doubledCycleColorWord A c
  have hpm : w.HasPeriod m := doubledCycleColorWord_hasPeriod hcover hdisj hmlt hm
  have hpn : w.HasPeriod c.length := doubledCycleColorWord_hasPeriod_length A c
  have hlen : m + c.length - m.gcd c.length ≤ w.length := by
    simp only [w, length_doubledCycleColorWord]
    omega
  have hpg : w.HasPeriod (m.gcd c.length) := hpm.gcd hpn hlen
  have hgdpos : 1 ≤ m.gcd c.length := Nat.gcd_pos_of_pos_left _ hmpos
  have hgdle : m.gcd c.length ≤ m := Nat.gcd_le_left _ (by omega)
  have hgdeq : m.gcd c.length = m := by
    by_contra hne
    have hgdlt : m.gcd c.length < m := lt_of_le_of_ne hgdle hne
    have hgdCycle : NoCrossingCycleArc A B c (m.gcd c.length) :=
      noCrossingCycleArc_of_doubledPeriod hcover hdisj (hgdle.trans_lt hmlt) hpg
    exact hmin _ hgdpos hgdlt hgdCycle
  exact Nat.gcd_eq_left_iff_dvd.mp hgdeq

/-- A cycle meeting both parts has a crossing traced edge, hence cyclic arc
length one cannot be missing. -/
private theorem not_noCrossingCycleArc_one_of_mixed {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} (c : G.Walk x₀ x₀)
    (hA : ∃ a, a ∈ c.support ∧ a ∈ A)
    (hB : ∃ b, b ∈ c.support ∧ b ∈ B) :
    ¬ NoCrossingCycleArc A B c 1 := by
  classical
  obtain ⟨a, haC, haA⟩ := hA
  obtain ⟨b, hbC, hbB⟩ := hB
  have haNotB : a ∉ B := fun haB => Set.disjoint_left.mp hdisj haA haB
  have hbNotA : b ∉ A := (mem_right_iff_not_mem_left hcover hdisj).mp hbB
  have hpre := c.toSubgraph_connected.preconnected
  rw [Subgraph.preconnected_iff_forall_exists_walk_subgraph] at hpre
  obtain ⟨p, hp⟩ := hpre (by simpa using haC) (by simpa using hbC)
  obtain ⟨d, hdp, hdA, hdnotA⟩ := p.exists_boundary_dart A haA hbNotA
  have hpedge : s(d.fst, d.snd) ∈ p.edges := by
    rw [Walk.edges, List.mem_map]
    exact ⟨d, hdp, rfl⟩
  have hcAdj : c.toSubgraph.Adj d.fst d.snd :=
    hp.2 (Walk.adj_toSubgraph_iff_mem_edges.mpr hpedge)
  obtain ⟨i, hiEdge, hi⟩ := c.toSubgraph_adj_iff.mp hcAdj
  have hdB : d.snd ∈ B := (mem_right_iff_not_mem_left hcover hdisj).mpr hdnotA
  have hdOpp : InOppositeParts A B d.fst d.snd := Or.inl ⟨hdA, hdB⟩
  have hiOpp : InOppositeParts A B (c.getVert i) (c.getVert (i + 1)) := by
    rw [Sym2.eq, Sym2.rel_iff'] at hiEdge
    rcases hiEdge with hiEdge | hiEdge
    · have h₁ := congrArg Prod.fst hiEdge
      have h₂ := congrArg Prod.snd hiEdge
      change c.getVert i = d.fst at h₁
      change c.getVert (i + 1) = d.snd at h₂
      rw [h₁, h₂]
      exact hdOpp
    · have h₁ := congrArg Prod.fst hiEdge
      have h₂ := congrArg Prod.snd hiEdge
      change c.getVert i = d.snd at h₁
      change c.getVert (i + 1) = d.fst at h₂
      rw [h₁, h₂]
      exact hdOpp.symm
  intro hno
  apply hno i hi
  have hstart : (c.append c).getVert i = c.getVert i := by
    rw [Walk.getVert_append, if_pos hi]
  have hend : (c.append c).getVert (i + 1) = c.getVert (i + 1) := by
    rw [Walk.getVert_append]
    by_cases hilast : i + 1 < c.length
    · rw [if_pos hilast]
    · rw [if_neg hilast]
      have heq : i + 1 = c.length := by omega
      rw [heq, Nat.sub_self, Walk.getVert_zero, c.getVert_length]
  simpa [hstart, hend] using hiOpp

private theorem isPath_walkSegment_append_self {x₀ : V} {c : G.Walk x₀ x₀}
    (hc : c.IsCycle) {i ell : Nat} (hi : i < c.length) (hell : ell < c.length) :
    (walkSegment (c.append c) i ell).IsPath := by
  let q := walkSegment (c.append c) i ell
  have hqLen : q.length = ell := by
    apply length_walkSegment_of_le
    simp only [Walk.length_append]
    omega
  rw [← Walk.IsPath.getVert_injOn_iff]
  intro j hj k hk hjk
  simp only [Set.mem_setOf_eq] at hj hk
  rw [hqLen] at hj hk
  have hjk' : (c.append c).getVert (i + j) = (c.append c).getVert (i + k) := by
    simpa [q, walkSegment, Nat.min_eq_right hj, Nat.min_eq_right hk] using hjk
  have hthree := hc.three_le_length
  rw [Walk.getVert_append, Walk.getVert_append] at hjk'
  by_cases hjn : i + j < c.length <;> by_cases hkn : i + k < c.length
  · rw [if_pos hjn, if_pos hkn] at hjk'
    exact Nat.add_left_cancel (hc.getVert_injOn' (by simp; omega) (by simp; omega) hjk')
  · rw [if_pos hjn, if_neg hkn] at hjk'
    have heq := hc.getVert_injOn' (by simp; omega) (by simp; omega) hjk'
    omega
  · rw [if_neg hjn, if_pos hkn] at hjk'
    have heq := hc.getVert_injOn' (by simp; omega) (by simp; omega) hjk'
    omega
  · rw [if_neg hjn, if_neg hkn] at hjk'
    have heq := hc.getVert_injOn' (by simp; omega) (by simp; omega) hjk'
    omega

/-- A cyclic arc beginning at any of the first `c.length` positions gives a
simple path of every shorter length. -/
theorem hasABPathLength_of_doubled_cycle_arc {A B : Set V}
    {x₀ : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    {i ell : Nat} (hi : i < c.length) (hell : ell < c.length)
    (hop : InOppositeParts A B ((c.append c).getVert i)
      ((c.append c).getVert (i + ell))) :
    HasABPathLength G A B ell := by
  apply hasABPathLength_of_path_segment
    (isPath_walkSegment_append_self hc hi hell) (i := 0) (ell := ell)
  · simp [length_walkSegment_of_le, Walk.length_append]
    omega
  simpa [walkSegment, length_walkSegment_of_le, Walk.length_append] using hop

private theorem noCrossingCycleArc_of_no_path {A B : Set V}
    {x₀ : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    {k : Nat} (hk : k < c.length) (hno : ¬ HasABPathLength G A B k) :
    NoCrossingCycleArc A B c k := by
  intro i hi hop
  exact hno (hasABPathLength_of_doubled_cycle_arc hc hi hk hop)

/-- The complementary cyclic arcs have the same two endpoints, in reverse
order.  Hence a missing positive arc length below the cycle length has a
missing complementary length as well. -/
private theorem noCrossingCycleArc_complement {A B : Set V}
    {x₀ : V} {c : G.Walk x₀ x₀} {m : Nat}
    (hmpos : 1 ≤ m) (hmlt : m < c.length)
    (hm : NoCrossingCycleArc A B c m) :
    NoCrossingCycleArc A B c (c.length - m) := by
  intro i hi hop
  by_cases hnowrap : i + (c.length - m) < c.length
  · let j := i + (c.length - m)
    have hj : j < c.length := hnowrap
    have hend : (c.append c).getVert (j + m) = (c.append c).getVert i := by
      have h := getVert_append_self_add_length c hi
      have heq : j + m = c.length + i := by simp only [j]; omega
      simpa [heq] using h
    exact hm j hj (by simpa [j, hend] using hop.symm)
  · let j := i + (c.length - m) - c.length
    have hj : j < c.length := by simp only [j]; omega
    have hjm : j + m = i := by simp only [j]; omega
    have hstart : (c.append c).getVert (i + (c.length - m)) =
        (c.append c).getVert j := by
      have h := getVert_append_self_add_length c hj
      have heq : c.length + j = i + (c.length - m) := by simp only [j]; omega
      simpa [heq] using h
    exact hm j hj (by simpa [hjm, hstart] using hop.symm)

/-- Package the least missing cyclic-arc length.  Besides minimality, it is
at least two and divides the cycle length. -/
private theorem exists_minimal_noCrossingCycleArc {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    (hA : ∃ a, a ∈ c.support ∧ a ∈ A)
    (hB : ∃ b, b ∈ c.support ∧ b ∈ B)
    (hfail : ∃ ell, 1 ≤ ell ∧ ell < c.length ∧
      ¬ HasABPathLength G A B ell) :
    ∃ m, 2 ≤ m ∧ 2 * m ≤ c.length ∧ m < c.length ∧
      NoCrossingCycleArc A B c m ∧
      m ∣ c.length ∧
      ∀ d, 1 ≤ d → d < m → ¬ NoCrossingCycleArc A B c d := by
  classical
  let missing : Finset Nat :=
    (Finset.Icc 1 (c.length - 1)).filter fun k => NoCrossingCycleArc A B c k
  obtain ⟨ell, hell₁, hellC, hnopath⟩ := hfail
  have hellMissing : ell ∈ missing := by
    simp only [missing, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hell₁, by omega⟩, noCrossingCycleArc_of_no_path hc hellC hnopath⟩
  have hmissing : missing.Nonempty := ⟨ell, hellMissing⟩
  let m := missing.min' hmissing
  have hmMem : m ∈ missing := by exact Finset.min'_mem _ _
  have hmData := Finset.mem_filter.mp hmMem
  have hmIcc : 1 ≤ m ∧ m ≤ c.length - 1 := by
    exact Finset.mem_Icc.mp hmData.1
  have hmlt : m < c.length := by omega
  have hmNo : NoCrossingCycleArc A B c m := hmData.2
  have hmTwo : 2 ≤ m := by
    by_contra hm
    have hmOne : m = 1 := by omega
    exact not_noCrossingCycleArc_one_of_mixed hcover hdisj c hA hB
      (by simpa [hmOne] using hmNo)
  have hmin : ∀ d, 1 ≤ d → d < m → ¬ NoCrossingCycleArc A B c d := by
    intro d hd₁ hdm hdNo
    have hdMissing : d ∈ missing := by
      simp only [missing, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hd₁, by omega⟩, hdNo⟩
    have hmle : m ≤ d := by
      dsimp only [m]
      exact Finset.min'_le missing d hdMissing
    omega
  have hmHalf : 2 * m ≤ c.length := by
    by_contra hhalf
    have hcompPos : 1 ≤ c.length - m := by omega
    have hcompLt : c.length - m < m := by omega
    exact hmin _ hcompPos hcompLt
      (noCrossingCycleArc_complement hmIcc.1 hmlt hmNo)
  have hmdvd : m ∣ c.length :=
    minimal_noCrossingCycleArc_dvd_length hcover hdisj hmIcc.1 hmlt hmNo hmin
  exact ⟨m, hmTwo, hmHalf, hmlt, hmNo, hmdvd, hmin⟩

/-- Once the least missing arc length is `m`, every nonmultiple of `m`
below the cycle length is realized by a crossing cyclic arc. -/
private theorem hasABPathLength_of_not_dvd_minimal_arc {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x₀ : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    {m k : Nat} (hmpos : 1 ≤ m) (hmlt : m < c.length)
    (hm : NoCrossingCycleArc A B c m)
    (hmin : ∀ d, 1 ≤ d → d < m → ¬ NoCrossingCycleArc A B c d)
    (hkpos : 1 ≤ k) (hklt : k < c.length) (hnDvd : ¬ m ∣ k) :
    HasABPathLength G A B k := by
  classical
  let r := k % m
  have hrpos : 1 ≤ r := by
    have : r ≠ 0 := by
      simpa [r, Nat.dvd_iff_mod_eq_zero] using hnDvd
    omega
  have hrlt : r < m := by
    exact Nat.mod_lt _ (by omega)
  have hrCross : ¬ NoCrossingCycleArc A B c r := hmin r hrpos hrlt
  unfold NoCrossingCycleArc at hrCross
  push Not at hrCross
  obtain ⟨i, hi, hop⟩ := hrCross
  let w := doubledCycleColorWord A c
  have hper : w.HasPeriod m := doubledCycleColorWord_hasPeriod hcover hdisj hmlt hm
  have hir : i + r < w.length := by
    simp only [w, length_doubledCycleColorWord]
    omega
  have hik : i + k < w.length := by
    simp only [w, length_doubledCycleColorWord]
    omega
  have hmod : (i + r) % m = (i + k) % m := by
    have hrmod : r % m = k % m := by simp [r]
    have hrk : r ≡ k [MOD m] := hrmod
    exact hrk.add_left i
  have hword : w[i + r]? = w[i + k]? := by
    calc
      w[i + r]? = w[(i + r) % m]? :=
        (hper.getElem?_mod m (i + r) w hir).symm
      _ = w[(i + k) % m]? := by rw [hmod]
      _ = w[i + k]? := hper.getElem?_mod m (i + k) w hik
  have hsame : (c.append c).getVert (i + r) ∈ A ↔
      (c.append c).getVert (i + k) ∈ A := by
    rw [List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hik] at hword
    simp only [w, doubledCycleColorWord, List.getElem_ofFn, Option.some.injEq] at hword
    exact decide_eq_decide.mp hword
  apply hasABPathLength_of_doubled_cycle_arc hc hi hklt
  rw [inOppositeParts_iff_xor_left hcover hdisj] at hop ⊢
  exact hop.trans (not_congr hsame)

/-- Put one endpoint of a chord at index zero and locate the other endpoint
strictly between the two cyclic neighbours. -/
private theorem exists_rooted_chord_coordinate [DecidableEq V]
    {x₀ : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    (hchorded : ¬ c.IsChordless) :
    ∃ x, ∃ c' : G.Walk x x, ∃ r,
      c'.IsCycle ∧ c'.length = c.length ∧ 2 ≤ r ∧ r + 2 ≤ c'.length ∧
      G.Adj x (c'.getVert r) ∧ s(x, c'.getVert r) ∉ c'.edges ∧
      (∀ z, z ∈ c'.support ↔ z ∈ c.support) ∧
      (∀ e, e ∈ c'.edges ↔ e ∈ c.edges) := by
  classical
  simp only [Walk.IsChordless, not_forall, not_not] at hchorded
  obtain ⟨e, he⟩ := hchorded
  induction e using Sym2.inductionOn with
  | _ x y =>
      have he' := Walk.isChord_sym2Mk.mp he
      have hxy : G.Adj x y := he'.1
      have hxyNot : s(x, y) ∉ c.edges := he'.2.1
      have hxC : x ∈ c.support := he'.2.2.1
      have hyC : y ∈ c.support := he'.2.2.2
      let c' : G.Walk x x := c.rotate x hxC
      have hc' : c'.IsCycle := hc.rotate hxC
      have hc'len : c'.length = c.length := by simp [c']
      have hyC' : y ∈ c'.support := (c.mem_support_rotate_iff x hxC).mpr hyC
      have hxyNot' : s(x, y) ∉ c'.edges := by
        intro hmem
        exact hxyNot ((c.rotate_edges x hxC).perm.mem_iff.mp hmem)
      obtain ⟨r, hry, hrle⟩ := Walk.mem_support_iff_exists_getVert.mp hyC'
      have hrpos : 1 ≤ r := by
        by_contra hr
        have hrzero : r = 0 := by omega
        subst r
        exact hxy.ne (by simpa using hry)
      have hrlt : r < c'.length := by
        by_contra hr
        have hre : r = c'.length := by omega
        subst r
        exact hxy.ne (by simpa using hry)
      have hrneOne : r ≠ 1 := by
        intro hre
        subst r
        apply hxyNot'
        rw [← hry]
        have hedge := Walk.adj_toSubgraph_iff_mem_edges.mp
          (c'.toSubgraph_adj_getVert (i := 0) (by omega))
        simpa only [Walk.getVert_zero, zero_add] using hedge
      have hrneLast : r ≠ c'.length - 1 := by
        intro hre
        apply hxyNot'
        rw [← hry, hre]
        have hedge := Walk.adj_toSubgraph_iff_mem_edges.mp
          (c'.toSubgraph_adj_getVert (i := c'.length - 1) (by omega))
        rw [show c'.length - 1 + 1 = c'.length by omega, c'.getVert_length] at hedge
        exact Sym2.eq_swap ▸ hedge
      have hrTwo : 2 ≤ r := by omega
      have hrLast : r + 2 ≤ c'.length := by omega
      refine ⟨x, c', r, hc', hc'len, hrTwo, hrLast, ?_, ?_, ?_, ?_⟩
      · simpa [hry] using hxy
      · simpa [hry] using hxyNot'
      · intro z
        exact c.mem_support_rotate_iff x hxC
      · intro e
        exact (c.rotate_edges x hxC).perm.mem_iff

/-- Choose the shorter cyclic distance between the endpoints of a chord.
Reversing the rooted cycle when necessary makes that coordinate at most
half the cycle length. -/
private theorem exists_short_rooted_chord_coordinate [DecidableEq V]
    {x₀ : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    (hchorded : ¬ c.IsChordless) :
    ∃ x, ∃ c' : G.Walk x x, ∃ r,
      c'.IsCycle ∧ c'.length = c.length ∧ 2 ≤ r ∧
      2 * r ≤ c'.length ∧ r + 2 ≤ c'.length ∧
      G.Adj x (c'.getVert r) ∧
      (∀ z, z ∈ c'.support ↔ z ∈ c.support) ∧
      (∀ e, e ∈ c'.edges ↔ e ∈ c.edges) := by
  obtain ⟨x, c', r, hc', hc'len, hrTwo, hrLast, hchord, _hnotEdge, hsupp, hedges⟩ :=
    exists_rooted_chord_coordinate hc hchorded
  by_cases hrHalf : 2 * r ≤ c'.length
  · exact ⟨x, c', r, hc', hc'len, hrTwo, hrHalf, hrLast, hchord, hsupp, hedges⟩
  · let cr := c'.reverse
    let r' := c'.length - r
    have hrLe : r ≤ c'.length := by omega
    have hr'Get : cr.getVert r' = c'.getVert r := by
      simp only [cr, r', Walk.getVert_reverse, Walk.length_reverse]
      congr 1
      omega
    have hcrLen : cr.length = c'.length := by simp [cr]
    refine ⟨x, cr, r', hc'.reverse, hcrLen.trans hc'len, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [r']; omega
    · simp only [r']; omega
    · simp only [r']; omega
    · simpa [hr'Get] using hchord
    · intro z
      simp only [cr, Walk.support_reverse, List.mem_reverse]
      exact hsupp z
    · intro e
      simp only [cr, Walk.edges_reverse, List.mem_reverse]
      exact hedges e

/-- Root and orient the cycle at a specified chord, again choosing the
shorter of the two cyclic coordinates for its other endpoint. -/
private theorem exists_short_rooted_chord_coordinate_of_chord [DecidableEq V]
    {x₀ u v : V} {c : G.Walk x₀ x₀} (hc : c.IsCycle)
    (huC : u ∈ c.support) (hvC : v ∈ c.support) (huv : G.Adj u v)
    (huvNot : s(u, v) ∉ c.edges) :
    ∃ c' : G.Walk u u, ∃ r,
      c'.IsCycle ∧ c'.length = c.length ∧ 2 ≤ r ∧
      2 * r ≤ c'.length ∧ r + 2 ≤ c'.length ∧
      c'.getVert r = v ∧ G.Adj u (c'.getVert r) ∧
      (∀ z, z ∈ c'.support ↔ z ∈ c.support) ∧
      (∀ e, e ∈ c'.edges ↔ e ∈ c.edges) := by
  let c₁ : G.Walk u u := c.rotate u huC
  have hc₁ : c₁.IsCycle := hc.rotate huC
  have hc₁len : c₁.length = c.length := by simp [c₁]
  have hvC₁ : v ∈ c₁.support := (c.mem_support_rotate_iff u huC).mpr hvC
  have huvNot₁ : s(u, v) ∉ c₁.edges := by
    intro hmem
    exact huvNot ((c.rotate_edges u huC).perm.mem_iff.mp hmem)
  obtain ⟨r, hrv, hrle⟩ := Walk.mem_support_iff_exists_getVert.mp hvC₁
  have hrPos : 1 ≤ r := by
    by_contra hr
    have hrzero : r = 0 := by omega
    subst r
    exact huv.ne (by simpa using hrv)
  have hrLt : r < c₁.length := by
    by_contra hr
    have hre : r = c₁.length := by omega
    subst r
    exact huv.ne (by simpa using hrv)
  have hrNeOne : r ≠ 1 := by
    intro hre
    subst r
    apply huvNot₁
    rw [← hrv]
    have hedge := Walk.adj_toSubgraph_iff_mem_edges.mp
      (c₁.toSubgraph_adj_getVert (i := 0) (by omega))
    simpa only [Walk.getVert_zero, zero_add] using hedge
  have hrNeLast : r ≠ c₁.length - 1 := by
    intro hre
    apply huvNot₁
    rw [← hrv, hre]
    have hedge := Walk.adj_toSubgraph_iff_mem_edges.mp
      (c₁.toSubgraph_adj_getVert (i := c₁.length - 1) (by omega))
    rw [show c₁.length - 1 + 1 = c₁.length by omega, c₁.getVert_length] at hedge
    exact Sym2.eq_swap ▸ hedge
  have hrTwo : 2 ≤ r := by omega
  have hrLast : r + 2 ≤ c₁.length := by omega
  have hsupp₁ : ∀ z, z ∈ c₁.support ↔ z ∈ c.support := by
    intro z
    exact c.mem_support_rotate_iff u huC
  have hedges₁ : ∀ e, e ∈ c₁.edges ↔ e ∈ c.edges := by
    intro e
    exact (c.rotate_edges u huC).perm.mem_iff
  by_cases hrHalf : 2 * r ≤ c₁.length
  · refine ⟨c₁, r, hc₁, hc₁len, hrTwo, hrHalf, hrLast, hrv, ?_, hsupp₁, hedges₁⟩
    simpa [hrv] using huv
  · let cr := c₁.reverse
    let r' := c₁.length - r
    have hr'Get : cr.getVert r' = c₁.getVert r := by
      simp only [cr, r', Walk.getVert_reverse]
      congr 1
      omega
    have hcrLen : cr.length = c₁.length := by simp [cr]
    refine ⟨cr, r', hc₁.reverse, hcrLen.trans hc₁len, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [r']; omega
    · simp only [r']; omega
    · simp only [r']; omega
    · exact hr'Get.trans hrv
    · rw [hr'Get, hrv]
      exact huv
    · intro z
      simp only [cr, Walk.support_reverse, List.mem_reverse]
      exact hsupp₁ z
    · intro e
      simp only [cr, Walk.edges_reverse, List.mem_reverse]
      exact hedges₁ e

/-- Extend a chord backwards by `a` cycle edges at its root and forwards by
`b` cycle edges at its other endpoint.  If the two used arc intervals are
separated, the resulting walk is a simple path of length `a + 1 + b`. -/
private theorem hasABPathLength_of_chord_extensions {A B : Set V}
    {x : V} {c : G.Walk x x} (hc : c.IsCycle) {r a b : Nat}
    (hr : 1 ≤ r) (ha : a < c.length)
    (hsep : r + b < c.length - a)
    (hchord : G.Adj x (c.getVert r))
    (hop : InOppositeParts A B (c.getVert (c.length - a))
      (c.getVert (r + b))) :
    HasABPathLength G A B (a + 1 + b) := by
  let s := c.length - a
  let left := c.drop s
  let right := (c.drop r).take b
  let chordRight := right.cons hchord
  let p := left.append chordRight
  have hspos : 1 ≤ s := by simp only [s]; omega
  have hsle : s ≤ c.length := by simp only [s]; omega
  have hrlt : r < c.length := by omega
  have hble : b ≤ c.length - r := by omega
  have hlenpos : 0 < c.length := by omega
  have hleftLen : left.length = a := by
    simp only [left, Walk.drop_length]
    dsimp only [s]
    omega
  have hrightLen : right.length = b := by
    simp [right, hble]
  have hleftPath : left.IsPath := by
    have htakeNotNil : ¬ (c.take s).Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.take_length]
      exact lt_min hspos hlenpos
    have hcycle : ((c.take s).append (c.drop s)).IsCycle := by simpa using hc
    exact hcycle.isPath_of_append_right htakeNotNil
  have hdropPath : (c.drop r).IsPath := by
    have htakeNotNil : ¬ (c.take r).Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.take_length]
      exact lt_min hr hlenpos
    have hcycle : ((c.take r).append (c.drop r)).IsCycle := by simpa using hc
    exact hcycle.isPath_of_append_right htakeNotNil
  have hrightPath : right.IsPath := hdropPath.take b
  have hrightGet : ∀ i, i ≤ right.length → right.getVert i = c.getVert (r + i) := by
    intro i hi
    simp only [right, Walk.take_getVert, Walk.drop_getVert]
    congr 1
    rw [Nat.min_eq_right]
    simpa [hrightLen] using hi
  have hxNotRight : x ∉ right.support := by
    intro hxmem
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hxmem
    have heq : c.getVert c.length = c.getVert (r + i) := by
      rw [c.getVert_length, ← hrightGet i hi]
      exact hix.symm
    have hinj := hc.getVert_injOn (by simp; omega) (by simp; omega) heq
    omega
  have hchordRightPath : chordRight.IsPath := by
    change (right.cons hchord).IsPath
    rw [Walk.cons_isPath_iff]
    exact ⟨hrightPath, hxNotRight⟩
  have hleftGet : ∀ i, i ≤ left.length → left.getVert i = c.getVert (s + i) := by
    intro i hi
    simp only [left, Walk.drop_getVert]
  have hdisj : left.support.Disjoint chordRight.support.tail := by
    intro z hzleft hzright
    change z ∈ (right.cons hchord).support.tail at hzright
    simp only [Walk.support_cons, List.tail_cons] at hzright
    obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hzleft
    obtain ⟨j, hjz, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hzright
    have heq : c.getVert (s + i) = c.getVert (r + j) := by
      rw [← hleftGet i hi, ← hrightGet j hj, hiz, hjz]
    have hinj := hc.getVert_injOn (by simp; omega) (by simp; omega) heq
    simp only [s] at hinj hsep
    omega
  have hp : p.IsPath := isPath_append_of_disjoint_tail hleftPath hchordRightPath hdisj
  have hplen : p.length = a + 1 + b := by
    simp only [p, Walk.length_append, chordRight, Walk.length_cons, hleftLen, hrightLen]
    omega
  have hpstart : p.getVert 0 = c.getVert (c.length - a) := by
    simp [p, left, s]
  have hpend : p.getVert p.length = c.getVert (r + b) := by
    rw [p.getVert_length]
    simp only [Walk.drop_getVert]
  refine ⟨_, _, p, hp, hplen, ?_⟩
  simpa [hpstart, hpend] using hop

/-- An ordinary period of the doubled colour word identifies the colours at
any two in-range indices which are congruent modulo that period. -/
private theorem same_left_of_modEq_doubledCycleColorWord {A : Set V}
    {x : V} {c : G.Walk x x} {m i j : Nat}
    (hper : (doubledCycleColorWord A c).HasPeriod m)
    (hi : i < 2 * c.length) (hj : j < 2 * c.length)
    (hmod : i % m = j % m) :
    ((c.append c).getVert i ∈ A ↔ (c.append c).getVert j ∈ A) := by
  classical
  let w := doubledCycleColorWord A c
  have hiw : i < w.length := by simpa [w] using hi
  have hjw : j < w.length := by simpa [w] using hj
  have hword : w[i]? = w[j]? := by
    calc
      w[i]? = w[i % m]? := (hper.getElem?_mod m i w hiw).symm
      _ = w[j % m]? := by rw [hmod]
      _ = w[j]? := hper.getElem?_mod m j w hjw
  rw [List.getElem?_eq_getElem hiw, List.getElem?_eq_getElem hjw] at hword
  simp only [w, doubledCycleColorWord, List.getElem_ofFn, Option.some.injEq] at hword
  exact decide_eq_decide.mp hword

/-- The preceding congruence fact transports the property of being in
opposite parts at both ends of an indexed pair. -/
private theorem inOppositeParts_of_modEq_doubledCycleColorWord {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} {m i j i' j' : Nat}
    (hper : (doubledCycleColorWord A c).HasPeriod m)
    (hi : i < 2 * c.length) (hj : j < 2 * c.length)
    (hi' : i' < 2 * c.length) (hj' : j' < 2 * c.length)
    (hmod₁ : i % m = i' % m) (hmod₂ : j % m = j' % m)
    (hop : InOppositeParts A B ((c.append c).getVert i)
      ((c.append c).getVert j)) :
    InOppositeParts A B ((c.append c).getVert i')
      ((c.append c).getVert j') := by
  have hsame₁ := same_left_of_modEq_doubledCycleColorWord hper hi hi' hmod₁
  have hsame₂ := same_left_of_modEq_doubledCycleColorWord hper hj hj' hmod₂
  rw [inOppositeParts_iff_xor_left hcover hdisj] at hop ⊢
  tauto

/-- First chord position in Verstraëte's argument.  If the second endpoint
of the rooted chord occurs no later than the least missing arc length `m`,
the chord fills every positive multiple of `m` below the cycle length. -/
private theorem hasABPathLength_of_dvd_minimal_arc_of_chord_le {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} (hc : c.IsCycle)
    {m r ell : Nat} (hmTwo : 2 ≤ m) (hmHalf : 2 * m ≤ c.length)
    (hmNo : NoCrossingCycleArc A B c m) (hmDvd : m ∣ c.length)
    (hmin : ∀ d, 1 ≤ d → d < m → ¬ NoCrossingCycleArc A B c d)
    (hrTwo : 2 ≤ r) (hrm : r ≤ m) (hchord : G.Adj x (c.getVert r))
    (hellPos : 1 ≤ ell) (hellLt : ell < c.length) (hellDvd : m ∣ ell) :
    HasABPathLength G A B ell := by
  classical
  let q := r - 1
  have hqPos : 1 ≤ q := by simp only [q]; omega
  have hqLt : q < m := by simp only [q]; omega
  have hqCross : ¬ NoCrossingCycleArc A B c q := hmin q hqPos hqLt
  unfold NoCrossingCycleArc at hqCross
  push Not at hqCross
  obtain ⟨i, hi, hop⟩ := hqCross
  let t := i % m
  have htLt : t < m := Nat.mod_lt _ (by omega)
  let a := if t = 0 then 0 else m - t
  have haLt : a < m := by
    dsimp only [a]
    split_ifs with ht
    · omega
    · omega
  have hmLeEll : m ≤ ell := Nat.le_of_dvd (by omega) hellDvd
  have haLe : a ≤ ell - 1 := by omega
  let b := ell - 1 - a
  have hlen : a + 1 + b = ell := by simp only [b]; omega
  have hdiffDvd : m ∣ c.length - ell := Nat.dvd_sub hmDvd hellDvd
  have hmLeDiff : m ≤ c.length - ell := Nat.le_of_dvd (by omega) hdiffDvd
  have hsep : r + b < c.length - a := by simp only [b]; omega
  have hsmod : (c.length - a) % m = i % m := by
    change (c.length - a) % m = t
    by_cases ht : t = 0
    · dsimp only [a]
      rw [if_pos ht, Nat.sub_zero]
      rw [Nat.dvd_iff_mod_eq_zero.mp hmDvd]
      exact ht.symm
    · have hsubDvd : m ∣ c.length - m := Nat.dvd_sub hmDvd (dvd_refl m)
      have hrewrite : c.length - (m - t) = (c.length - m) + t := by omega
      dsimp only [a]
      rw [if_neg ht, hrewrite, Nat.add_mod,
        Nat.dvd_iff_mod_eq_zero.mp hsubDvd, zero_add, Nat.mod_eq_of_lt htLt]
      exact Nat.mod_eq_of_lt htLt
  have hper := doubledCycleColorWord_hasPeriod hcover hdisj (by omega) hmNo
  let s := c.length - a
  have hsLe : s ≤ c.length := by simp only [s]; omega
  have hsLtTwo : s < 2 * c.length := by simp only [s]; omega
  have hiLtTwo : i < 2 * c.length := by omega
  have hiqLtTwo : i + q < 2 * c.length := by omega
  have hsEndLtTwo : s + ell + q < 2 * c.length := by
    simp only [s, q]
    omega
  have hmodStart : i % m = s % m := by simpa only [s] using hsmod.symm
  have hsEll : s ≡ s + ell [MOD m] := by
    simpa using (hellDvd.modEq_zero_nat.add_left s).symm
  have hmodEnd : (i + q) % m = (s + ell + q) % m := by
    exact (Nat.ModEq.add_right q (hmodStart.trans hsEll))
  have hop' : InOppositeParts A B ((c.append c).getVert s)
      ((c.append c).getVert (s + ell + q)) :=
    inOppositeParts_of_modEq_doubledCycleColorWord hcover hdisj hper
      hiLtTwo hiqLtTwo hsLtTwo hsEndLtTwo hmodStart hmodEnd hop
  have hstart : (c.append c).getVert s = c.getVert (c.length - a) := by
    by_cases ha : a = 0
    · simp [s, ha, Walk.getVert_append]
    · have hsLt : s < c.length := by simp only [s]; omega
      rw [Walk.getVert_append, if_pos hsLt]
  have hendIndex : s + ell + q = c.length + (r + b) := by
    simp only [s, q, b]
    omega
  have hrbLt : r + b < c.length := lt_of_lt_of_le hsep (Nat.sub_le ..)
  have hend : (c.append c).getVert (s + ell + q) = c.getVert (r + b) := by
    rw [hendIndex, Walk.getVert_append, if_neg (by omega)]
    congr 1
    omega
  rw [hstart, hend] at hop'
  have haCycle : a < c.length := by omega
  have hp := hasABPathLength_of_chord_extensions hc (by omega) haCycle hsep hchord hop'
  simpa only [hlen] using hp

/-- A chord path whose root arm goes forward (and is then traversed back to
the root), while its other arm goes forward from the chord endpoint.  The
two arms lie in the two different open arcs cut out by the chord. -/
private theorem hasABPathLength_of_chord_forward_arms {A B : Set V}
    {x : V} {c : G.Walk x x} (hc : c.IsCycle) {r a b : Nat}
    (hr : r < c.length) (ha : a < r) (hb : r + b < c.length)
    (hchord : G.Adj x (c.getVert r))
    (hop : InOppositeParts A B (c.getVert a) (c.getVert (r + b))) :
    HasABPathLength G A B (a + 1 + b) := by
  let left := (c.take a).reverse
  let right := (c.drop r).take b
  let chordRight := right.cons hchord
  let p := left.append chordRight
  have haCycle : a < c.length := ha.trans hr
  have hbLe : b ≤ c.length - r := by omega
  have hleftLen : left.length = a := by
    simp only [left, Walk.length_reverse, Walk.take_length, Nat.min_eq_left haCycle.le]
  have hrightLen : right.length = b := by simp [right, hbLe]
  have htakePath : (c.take a).IsPath := by
    have hdropNotNil : ¬ (c.drop a).Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.drop_length]
      omega
    have hcycle : ((c.take a).append (c.drop a)).IsCycle := by simpa using hc
    exact hcycle.isPath_of_append_left hdropNotNil
  have hleftPath : left.IsPath := htakePath.reverse
  have hdropPath : (c.drop r).IsPath := by
    have htakeNotNil : ¬ (c.take r).Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.take_length]
      exact lt_min (by omega) (by omega)
    have hcycle : ((c.take r).append (c.drop r)).IsCycle := by simpa using hc
    exact hcycle.isPath_of_append_right htakeNotNil
  have hrightPath : right.IsPath := hdropPath.take b
  have hleftGet : ∀ i, i ≤ left.length → left.getVert i = c.getVert (a - i) := by
    intro i hi
    simp only [left, Walk.getVert_reverse, Walk.length_reverse, Walk.take_length,
      Nat.min_eq_left haCycle.le, Walk.take_getVert]
    congr 1
    rw [Nat.min_eq_right]
    omega
  have hrightGet : ∀ i, i ≤ right.length → right.getVert i = c.getVert (r + i) := by
    intro i hi
    simp only [right, Walk.take_getVert, Walk.drop_getVert]
    congr 1
    rw [Nat.min_eq_right]
    simpa [hrightLen] using hi
  have hxNotRight : x ∉ right.support := by
    intro hxmem
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hxmem
    have heq : c.getVert c.length = c.getVert (r + i) := by
      rw [c.getVert_length, ← hrightGet i hi]
      exact hix.symm
    have hinj := hc.getVert_injOn (by simp; omega) (by simp; omega) heq
    omega
  have hchordRightPath : chordRight.IsPath := by
    change (right.cons hchord).IsPath
    rw [Walk.cons_isPath_iff]
    exact ⟨hrightPath, hxNotRight⟩
  have hsupports : left.support.Disjoint chordRight.support.tail := by
    intro z hzleft hzright
    change z ∈ (right.cons hchord).support.tail at hzright
    simp only [Walk.support_cons, List.tail_cons] at hzright
    obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hzleft
    obtain ⟨j, hjz, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hzright
    have heq : c.getVert (a - i) = c.getVert (r + j) := by
      rw [← hleftGet i hi, ← hrightGet j hj, hiz, hjz]
    have hjle : j ≤ b := by simpa [hrightLen] using hj
    have hrj : r + j < c.length := (Nat.add_le_add_left hjle r).trans_lt hb
    have hinj := hc.getVert_injOn' (by simp; omega) (by simp; omega) heq
    omega
  have hp : p.IsPath := isPath_append_of_disjoint_tail hleftPath hchordRightPath hsupports
  have hplen : p.length = a + 1 + b := by
    simp only [p, Walk.length_append, chordRight, Walk.length_cons, hleftLen, hrightLen]
    omega
  have hpstart : p.getVert 0 = c.getVert a := by
    simpa [p] using hleftGet 0 (by simp)
  have hpend : p.getVert p.length = c.getVert (r + b) := by
    rw [p.getVert_length]
    simp only [Walk.drop_getVert]
  refine ⟨_, _, p, hp, hplen, ?_⟩
  simpa [hpstart, hpend] using hop

/-- The complementary two-arc chord path: the root arm goes backwards
around the terminal end of the cycle and the chord-end arm also goes
backwards. -/
private theorem hasABPathLength_of_chord_backward_arms {A B : Set V}
    {x : V} {c : G.Walk x x} (hc : c.IsCycle) {r a b : Nat}
    (hr : r < c.length) (ha : a < c.length - r) (hb : b < r)
    (hchord : G.Adj x (c.getVert r))
    (hop : InOppositeParts A B (c.getVert (c.length - a))
      (c.getVert (r - b))) :
    HasABPathLength G A B (a + 1 + b) := by
  let s := c.length - a
  let left := c.drop s
  let pre := c.take r
  let right := (pre.drop (r - b)).reverse
  let chordRight := right.cons hchord
  let p := left.append chordRight
  have hsPos : 1 ≤ s := by simp only [s]; omega
  have hsLe : s ≤ c.length := by simp only [s]; omega
  have hbr : b ≤ r := hb.le
  have hpreLen : pre.length = r := by
    simp only [pre, Walk.take_length, Nat.min_eq_left hr.le]
  have hleftLen : left.length = a := by
    simp only [left, Walk.drop_length, s]
    omega
  have hrightLen : right.length = b := by
    simp only [right, Walk.length_reverse, Walk.drop_length, hpreLen]
    omega
  have hleftPath : left.IsPath := by
    have htakeNotNil : ¬ (c.take s).Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.take_length]
      exact lt_min hsPos (by omega)
    have hcycle : ((c.take s).append (c.drop s)).IsCycle := by simpa using hc
    exact hcycle.isPath_of_append_right htakeNotNil
  have hprePath : pre.IsPath := by
    have hdropNotNil : ¬ (c.drop r).Nil := by
      rw [Walk.not_nil_iff_lt_length, Walk.drop_length]
      omega
    have hcycle : ((c.take r).append (c.drop r)).IsCycle := by simpa using hc
    exact hcycle.isPath_of_append_left hdropNotNil
  have hrightPath : right.IsPath := (hprePath.drop (r - b)).reverse
  have hleftGet : ∀ i, i ≤ left.length → left.getVert i = c.getVert (s + i) := by
    intro i hi
    simp only [left, Walk.drop_getVert]
  have hrightGet : ∀ i, i ≤ right.length → right.getVert i = c.getVert (r - i) := by
    intro i hi
    rw [hrightLen] at hi
    simp only [right, Walk.getVert_reverse, Walk.drop_length, hpreLen,
      Walk.drop_getVert, pre, Walk.take_getVert]
    congr 1
    have hrsub : r - (r - b) = b := by omega
    have hinsideLe : r - b + (r - (r - b) - i) ≤ r := by
      rw [hrsub]
      omega
    rw [Nat.min_eq_right hinsideLe]
    rw [hrsub]
    omega
  have hxNotRight : x ∉ right.support := by
    intro hxmem
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hxmem
    have heq : c.getVert c.length = c.getVert (r - i) := by
      rw [c.getVert_length, ← hrightGet i hi]
      exact hix.symm
    have hiLe : i ≤ b := by simpa [hrightLen] using hi
    have hinj := hc.getVert_injOn (by simp; omega) (by simp; omega) heq
    omega
  have hchordRightPath : chordRight.IsPath := by
    change (right.cons hchord).IsPath
    rw [Walk.cons_isPath_iff]
    exact ⟨hrightPath, hxNotRight⟩
  have hsupports : left.support.Disjoint chordRight.support.tail := by
    intro z hzleft hzright
    change z ∈ (right.cons hchord).support.tail at hzright
    simp only [Walk.support_cons, List.tail_cons] at hzright
    obtain ⟨i, hiz, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hzleft
    obtain ⟨j, hjz, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hzright
    have heq : c.getVert (s + i) = c.getVert (r - j) := by
      rw [← hleftGet i hi, ← hrightGet j hj, hiz, hjz]
    have hjLe : j ≤ b := by simpa [hrightLen] using hj
    have hinj := hc.getVert_injOn (by simp; omega) (by simp; omega) heq
    simp only [s] at hinj
    omega
  have hp : p.IsPath := isPath_append_of_disjoint_tail hleftPath hchordRightPath hsupports
  have hplen : p.length = a + 1 + b := by
    simp only [p, Walk.length_append, chordRight, Walk.length_cons, hleftLen, hrightLen]
    omega
  have hpstart : p.getVert 0 = c.getVert (c.length - a) := by
    simp [p, left, s]
  have hpend : p.getVert p.length = c.getVert (r - b) := by
    rw [p.getVert_length]
    simp only [pre, Walk.take_getVert]
    rw [Nat.min_eq_right]
    omega
  refine ⟨_, _, p, hp, hplen, ?_⟩
  have hrsubLe : r - b ≤ r := Nat.sub_le ..
  simpa [s, pre, Walk.take_getVert, Nat.min_eq_right hrsubLe] using hop

private theorem getVert_append_self_eq_getVert_of_le {x : V}
    (c : G.Walk x x) {i : Nat} (hi : i ≤ c.length) :
    (c.append c).getVert i = c.getVert i := by
  rw [Walk.getVert_append]
  by_cases hil : i < c.length
  · rw [if_pos hil]
  · have hieq : i = c.length := by omega
    rw [if_neg hil, hieq, Nat.sub_self, Walk.getVert_zero, c.getVert_length]

private theorem same_left_getVert_of_modEq_doubledCycleColorWord {A : Set V}
    {x : V} {c : G.Walk x x} {m i j : Nat}
    (hper : (doubledCycleColorWord A c).HasPeriod m)
    (hi : i ≤ c.length) (hj : j ≤ c.length)
    (hmod : i % m = j % m) :
    (c.getVert i ∈ A ↔ c.getVert j ∈ A) := by
  by_cases hnzero : c.length = 0
  · have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst i
    subst j
    rfl
  · have hnpos : 0 < c.length := Nat.pos_of_ne_zero hnzero
    have hsame := same_left_of_modEq_doubledCycleColorWord hper
      (i := i) (j := j) (by omega) (by omega) hmod
    rw [getVert_append_self_eq_getVert_of_le c hi,
      getVert_append_self_eq_getVert_of_le c hj] at hsame
    exact hsame

private def BackwardChordWitness (A B : Set V) {x : V}
    (c : G.Walk x x) (r L : Nat) : Prop :=
  ∃ a b, a < c.length - r ∧ b < r ∧ a + 1 + b = L ∧
    InOppositeParts A B (c.getVert (c.length - a)) (c.getVert (r - b))

private def ForwardChordWitness (A B : Set V) {x : V}
    (c : G.Walk x x) (r L : Nat) : Prop :=
  ∃ a b, a < r ∧ r + b < c.length ∧ a + 1 + b = L ∧
    InOppositeParts A B (c.getVert a) (c.getVert (r + b))

/-- If a backward-arms chord witness has length divisible by the colour
period, one of its two arms can be extended by a whole period until the
next multiple. -/
private theorem backwardChordWitness_add_period {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} {m r L : Nat}
    (hmPos : 1 ≤ m) (hper : (doubledCycleColorWord A c).HasPeriod m)
    (hmDvdN : m ∣ c.length) (hmDvdL : m ∣ L)
    (hnext : L + m < c.length)
    (hw : BackwardChordWitness A B c r L) :
    BackwardChordWitness A B c r (L + m) := by
  obtain ⟨a, b, ha, hb, hlen, hop⟩ := hw
  have hdiffDvd : m ∣ c.length - L := Nat.dvd_sub hmDvdN hmDvdL
  have hdiff2Dvd : m ∣ (c.length - L) - m := Nat.dvd_sub hdiffDvd (dvd_refl m)
  have hmLeDiff2 : m ≤ (c.length - L) - m :=
    Nat.le_of_dvd (by omega) hdiff2Dvd
  by_cases haExt : a + m < c.length - r
  · refine ⟨a + m, b, haExt, hb, by omega, ?_⟩
    have haiLe : c.length - (a + m) ≤ c.length - a := by omega
    have hdiff : (c.length - a) - (c.length - (a + m)) = m := by omega
    have hmod : (c.length - (a + m)) % m = (c.length - a) % m := by
      apply (Nat.modEq_iff_dvd' haiLe).2
      rw [hdiff]
    have hsame := same_left_getVert_of_modEq_doubledCycleColorWord hper
      (by omega) (by omega) hmod
    rw [inOppositeParts_iff_xor_left hcover hdisj] at hop ⊢
    tauto
  · have hbExt : b + m < r := by
      by_contra hbNo
      omega
    refine ⟨a, b + m, ha, hbExt, by omega, ?_⟩
    have hnewLe : r - (b + m) ≤ r - b := by omega
    have hdiff : (r - b) - (r - (b + m)) = m := by omega
    have hmod : (r - (b + m)) % m = (r - b) % m := by
      apply (Nat.modEq_iff_dvd' hnewLe).2
      rw [hdiff]
    have hsame := same_left_getVert_of_modEq_doubledCycleColorWord hper
      (by omega) (by omega) hmod
    rw [inOppositeParts_iff_xor_left hcover hdisj] at hop ⊢
    tauto

/-- The forward-arms version of period-sized extension. -/
private theorem forwardChordWitness_add_period {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} {m r L : Nat}
    (hmPos : 1 ≤ m) (hper : (doubledCycleColorWord A c).HasPeriod m)
    (hmDvdN : m ∣ c.length) (hmDvdL : m ∣ L)
    (hnext : L + m < c.length)
    (hw : ForwardChordWitness A B c r L) :
    ForwardChordWitness A B c r (L + m) := by
  obtain ⟨a, b, ha, hb, hlen, hop⟩ := hw
  have hdiffDvd : m ∣ c.length - L := Nat.dvd_sub hmDvdN hmDvdL
  have hdiff2Dvd : m ∣ (c.length - L) - m := Nat.dvd_sub hdiffDvd (dvd_refl m)
  have hmLeDiff2 : m ≤ (c.length - L) - m :=
    Nat.le_of_dvd (by omega) hdiff2Dvd
  by_cases haExt : a + m < r
  · refine ⟨a + m, b, haExt, hb, by omega, ?_⟩
    have hmod : a % m = (a + m) % m := by simp [Nat.add_mod]
    have hsame := same_left_getVert_of_modEq_doubledCycleColorWord hper
      (by omega) (by omega) hmod
    rw [inOppositeParts_iff_xor_left hcover hdisj] at hop ⊢
    tauto
  · have hbExt : r + (b + m) < c.length := by
      by_contra hbNo
      omega
    refine ⟨a, b + m, ha, hbExt, by omega, ?_⟩
    have hmod : (r + b) % m = (r + (b + m)) % m := by
      have h : r + b ≡ r + (b + m) [MOD m] := by
        have : b ≡ b + m [MOD m] := by simp [Nat.ModEq]
        exact this.add_left r
      exact h
    have hsame := same_left_getVert_of_modEq_doubledCycleColorWord hper
      (by omega) (by omega) hmod
    rw [inOppositeParts_iff_xor_left hcover hdisj] at hop ⊢
    tauto

private theorem backwardChordWitness_mul_period {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} {m r : Nat}
    (hmPos : 1 ≤ m) (hper : (doubledCycleColorWord A c).HasPeriod m)
    (hmDvdN : m ∣ c.length) (hbase : BackwardChordWitness A B c r m) :
    ∀ k, 1 ≤ k → m * k < c.length →
      BackwardChordWitness A B c r (m * k) := by
  intro k
  induction k with
  | zero =>
      intro hk
      omega
  | succ k ih =>
      intro hkPos hkLt
      by_cases hkZero : k = 0
      · subst k
        simpa using hbase
      · have hkLt' : m * k + m < c.length := by
          simpa [Nat.mul_succ] using hkLt
        have hprevLt : m * k < c.length := by omega
        have hw := ih (by omega) hprevLt
        have hw' := backwardChordWitness_add_period hcover hdisj hmPos hper
          hmDvdN (dvd_mul_right m k) hkLt' hw
        simpa [Nat.mul_succ] using hw'

private theorem forwardChordWitness_mul_period {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} {m r : Nat}
    (hmPos : 1 ≤ m) (hper : (doubledCycleColorWord A c).HasPeriod m)
    (hmDvdN : m ∣ c.length) (hbase : ForwardChordWitness A B c r m) :
    ∀ k, 1 ≤ k → m * k < c.length →
      ForwardChordWitness A B c r (m * k) := by
  intro k
  induction k with
  | zero =>
      intro hk
      omega
  | succ k ih =>
      intro hkPos hkLt
      by_cases hkZero : k = 0
      · subst k
        simpa using hbase
      · have hkLt' : m * k + m < c.length := by
          simpa [Nat.mul_succ] using hkLt
        have hprevLt : m * k < c.length := by omega
        have hw := ih (by omega) hprevLt
        have hw' := forwardChordWitness_add_period hcover hdisj hmPos hper
          hmDvdN (dvd_mul_right m k) hkLt' hw
        simpa [Nat.mul_succ] using hw'

private theorem hasABPathLength_of_backwardChordWitness_mul {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} (hc : c.IsCycle) {m r ell : Nat}
    (hmPos : 1 ≤ m) (hmNo : NoCrossingCycleArc A B c m)
    (hmDvdN : m ∣ c.length) (hchord : G.Adj x (c.getVert r))
    (hbase : BackwardChordWitness A B c r m)
    (hellPos : 1 ≤ ell) (hellLt : ell < c.length) (hellDvd : m ∣ ell) :
    HasABPathLength G A B ell := by
  obtain ⟨k, rfl⟩ := hellDvd
  have hkPos : 1 ≤ k := by
    by_contra hk
    have : k = 0 := by omega
    subst k
    simp at hellPos
  have hmLe : m ≤ m * k := Nat.le_of_dvd (by omega) (dvd_mul_right m k)
  have hper := doubledCycleColorWord_hasPeriod hcover hdisj (hmLe.trans_lt hellLt) hmNo
  obtain ⟨a, b, ha, hb, hlen, hop⟩ :=
    backwardChordWitness_mul_period hcover hdisj hmPos hper hmDvdN hbase
      k hkPos hellLt
  have hp := hasABPathLength_of_chord_backward_arms hc (by omega) ha hb hchord hop
  simpa only [hlen] using hp

private theorem hasABPathLength_of_forwardChordWitness_mul {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} (hc : c.IsCycle) {m r ell : Nat}
    (hmPos : 1 ≤ m) (hmNo : NoCrossingCycleArc A B c m)
    (hmDvdN : m ∣ c.length) (hchord : G.Adj x (c.getVert r))
    (hbase : ForwardChordWitness A B c r m)
    (hellPos : 1 ≤ ell) (hellLt : ell < c.length) (hellDvd : m ∣ ell) :
    HasABPathLength G A B ell := by
  obtain ⟨k, rfl⟩ := hellDvd
  have hkPos : 1 ≤ k := by
    by_contra hk
    have : k = 0 := by omega
    subst k
    simp at hellPos
  have hmLe : m ≤ m * k := Nat.le_of_dvd (by omega) (dvd_mul_right m k)
  have hper := doubledCycleColorWord_hasPeriod hcover hdisj (hmLe.trans_lt hellLt) hmNo
  obtain ⟨a, b, ha, hb, hlen, hop⟩ :=
    forwardChordWitness_mul_period hcover hdisj hmPos hper hmDvdN hbase
      k hkPos hellLt
  have hp := hasABPathLength_of_chord_forward_arms hc (by omega) ha hb hchord hop
  simpa only [hlen] using hp

/-- If neither orientation supplies a crossing chord path of length `m`,
the colour pattern has period two on the `m` consecutive vertices starting
at the chord endpoint. -/
private theorem same_left_add_two_on_chord_block {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} {m r v : Nat}
    (hmPos : 1 ≤ m) (hmDvdN : m ∣ c.length)
    (hper : (doubledCycleColorWord A c).HasPeriod m)
    (hmr : m < r) (hrfar : r + m < c.length)
    (hnoBack : ¬ BackwardChordWitness A B c r m)
    (hnoForward : ¬ ForwardChordWitness A B c r m)
    (hv : r ≤ v) (hvlt : v < r + m) :
    (c.getVert v ∈ A ↔ c.getVert (v + 2) ∈ A) := by
  by_cases hvlast : v = r + m - 1
  · have hbackNot : ¬ InOppositeParts A B (c.getVert c.length)
        (c.getVert (r - (m - 1))) := by
      intro hop
      apply hnoBack
      exact ⟨0, m - 1, by omega, by omega, by omega, by simpa using hop⟩
    have hforwardNot : ¬ InOppositeParts A B (c.getVert 0)
        (c.getVert (r + (m - 1))) := by
      intro hop
      apply hnoForward
      exact ⟨0, m - 1, by omega, by omega, by omega, by simpa using hop⟩
    have hbackSame := (not_inOppositeParts_iff_same_left hcover hdisj).mp hbackNot
    have hforwardSame := (not_inOppositeParts_iff_same_left hcover hdisj).mp hforwardNot
    have hle : r - (m - 1) ≤ v + 2 := by omega
    have hdiff : (v + 2) - (r - (m - 1)) = 2 * m := by omega
    have hmod : (r - (m - 1)) % m = (v + 2) % m := by
      apply (Nat.modEq_iff_dvd' hle).2
      rw [hdiff]
      simpa [Nat.mul_comm] using (dvd_mul_right m 2)
    have hperiodSame := same_left_getVert_of_modEq_doubledCycleColorWord hper
      (by omega) (by omega) hmod
    rw [c.getVert_length] at hbackSame
    simp only [Walk.getVert_zero] at hbackSame hforwardSame
    have hvEq : r + (m - 1) = v := by omega
    rw [hvEq] at hforwardSame
    tauto
  · let a := v - r + 1
    let bBack := m - 1 - a
    let aForward := m - a
    let bForward := a - 1
    have haPos : 1 ≤ a := by simp only [a]; omega
    have haLt : a < m := by simp only [a]; omega
    have hbackNot : ¬ InOppositeParts A B (c.getVert (c.length - a))
        (c.getVert (r - bBack)) := by
      intro hop
      apply hnoBack
      have haGeom : a < c.length - r := by omega
      have hbGeom : bBack < r := by simp only [bBack]; omega
      have hlenGeom : a + 1 + bBack = m := by simp only [bBack]; omega
      exact ⟨a, bBack, haGeom, hbGeom, hlenGeom, hop⟩
    have hforwardNot : ¬ InOppositeParts A B (c.getVert aForward)
        (c.getVert (r + bForward)) := by
      intro hop
      apply hnoForward
      have haGeom : aForward < r := by simp only [aForward]; omega
      have hbGeom : r + bForward < c.length := by simp only [bForward]; omega
      have hlenGeom : aForward + 1 + bForward = m := by
        simp only [aForward, bForward]
        omega
      exact ⟨aForward, bForward, haGeom, hbGeom, hlenGeom, hop⟩
    have hbackSame := (not_inOppositeParts_iff_same_left hcover hdisj).mp hbackNot
    have hforwardSame := (not_inOppositeParts_iff_same_left hcover hdisj).mp hforwardNot
    have hle₁ : aForward ≤ c.length - a := by simp only [aForward]; omega
    have hdiff₁ : (c.length - a) - aForward = c.length - m := by
      simp only [aForward]
      omega
    have hmod₁ : (c.length - a) % m = aForward % m := by
      have hme : aForward ≡ c.length - a [MOD m] := by
        apply (Nat.modEq_iff_dvd' hle₁).2
        rw [hdiff₁]
        exact Nat.dvd_sub hmDvdN (dvd_refl m)
      exact hme.symm
    have hperiodSame₁ := same_left_getVert_of_modEq_doubledCycleColorWord hper
      (by omega) (by simp only [aForward]; omega) hmod₁
    have hle₂ : r - bBack ≤ v + 2 := by simp only [bBack, a]; omega
    have hdiff₂ : (v + 2) - (r - bBack) = m := by simp only [bBack, a]; omega
    have hmod₂ : (r - bBack) % m = (v + 2) % m := by
      apply (Nat.modEq_iff_dvd' hle₂).2
      rw [hdiff₂]
    have hperiodSame₂ := same_left_getVert_of_modEq_doubledCycleColorWord hper
      (by simp only [bBack]; omega) (by omega) hmod₂
    have hbForwardEq : r + bForward = v := by simp only [bForward, a]; omega
    rw [hbForwardEq] at hforwardSame
    tauto

private theorem noCrossingCycleArc_two_of_no_chord_witnesses {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} {m r : Nat}
    (hmPos : 1 ≤ m) (hmDvdN : m ∣ c.length)
    (hper : (doubledCycleColorWord A c).HasPeriod m)
    (hmr : m < r) (hrfar : r + m < c.length)
    (hnoBack : ¬ BackwardChordWitness A B c r m)
    (hnoForward : ¬ ForwardChordWitness A B c r m) :
    NoCrossingCycleArc A B c 2 := by
  intro i hi
  let t := (i + (m - r % m)) % m
  let v := r + t
  have htLt : t < m := Nat.mod_lt _ (by omega)
  have hv : r ≤ v := by simp only [v]; omega
  have hvlt : v < r + m := by simp only [v]; omega
  have hrmodLt : r % m < m := Nat.mod_lt _ (by omega)
  have hrME : r ≡ r % m [MOD m] := (Nat.mod_modEq r m).symm
  have htME : t ≡ i + (m - r % m) [MOD m] := by
    simpa only [t] using Nat.mod_modEq (i + (m - r % m)) m
  have hivME : i ≡ v [MOD m] := by
    have hsum := hrME.add htME
    have heq : r % m + (i + (m - r % m)) = i + m := by omega
    rw [heq] at hsum
    have him : i + m ≡ i [MOD m] := by simp [Nat.ModEq]
    exact (hsum.trans him).symm
  have hi2v2ME : i + 2 ≡ v + 2 [MOD m] := hivME.add_right 2
  have hnLarge : 3 ≤ c.length := by omega
  have hsameStart := same_left_of_modEq_doubledCycleColorWord hper
    (i := i) (j := v) (by omega) (by omega) hivME
  have hsameEnd := same_left_of_modEq_doubledCycleColorWord hper
    (i := i + 2) (j := v + 2) (by omega) (by omega) hi2v2ME
  have hlocal := same_left_add_two_on_chord_block hcover hdisj hmPos hmDvdN
    hper hmr hrfar hnoBack hnoForward hv hvlt
  have hvLe : v ≤ c.length := by omega
  have hv2Le : v + 2 ≤ c.length := by omega
  rw [getVert_append_self_eq_getVert_of_le c hvLe] at hsameStart
  rw [getVert_append_self_eq_getVert_of_le c hv2Le] at hsameEnd
  apply (not_inOppositeParts_iff_same_left hcover hdisj).mpr
  tauto

/-- The exceptional conclusion in the chorded-cycle lemma: every traced
cycle edge and the distinguished chord cross the given partition. -/
private def RootedCycleChordCrosses (A B : Set V) {x : V}
    (c : G.Walk x x) (r : Nat) : Prop :=
  (∀ i, i < c.length → InOppositeParts A B ((c.append c).getVert i)
    ((c.append c).getVert (i + 1))) ∧
  InOppositeParts A B x (c.getVert r)

/-- Far-chord case of the Bondy--Simonovits--Verstraëte lemma.  Every
requested multiple of the least missing cycle-arc period is supplied by a
chord path, unless the cycle together with this chord already has `(A,B)`
as its bipartition. -/
private theorem hasABPathLength_or_rootedCycleChordCrosses_of_far {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} (hc : c.IsCycle) {m r ell : Nat}
    (hmTwo : 2 ≤ m) (hmHalf : 2 * m ≤ c.length)
    (hmNo : NoCrossingCycleArc A B c m) (hmDvdN : m ∣ c.length)
    (hmin : ∀ d, 1 ≤ d → d < m → ¬ NoCrossingCycleArc A B c d)
    (hmr : m < r) (hrfar : r + m < c.length)
    (hchord : G.Adj x (c.getVert r))
    (hellPos : 1 ≤ ell) (hellLt : ell < c.length) :
    HasABPathLength G A B ell ∨ RootedCycleChordCrosses A B c r := by
  classical
  by_cases hellDvd : m ∣ ell
  · have hper := doubledCycleColorWord_hasPeriod hcover hdisj (by omega) hmNo
    by_cases hback : BackwardChordWitness A B c r m
    · exact Or.inl <| hasABPathLength_of_backwardChordWitness_mul hcover hdisj hc
        (by omega) hmNo hmDvdN hchord hback hellPos hellLt hellDvd
    by_cases hforward : ForwardChordWitness A B c r m
    · exact Or.inl <| hasABPathLength_of_forwardChordWitness_mul hcover hdisj hc
        (by omega) hmNo hmDvdN hchord hforward hellPos hellLt hellDvd
    have hnoTwo := noCrossingCycleArc_two_of_no_chord_witnesses hcover hdisj
      (by omega) hmDvdN hper hmr hrfar hback hforward
    have hmLeTwo : m ≤ 2 := by
      by_contra hmle
      exact hmin 2 (by omega) (by omega) hnoTwo
    have hmEq : m = 2 := by omega
    subst m
    have hperTwo : (doubledCycleColorWord A c).HasPeriod 2 := hper
    have hOneCross : ¬ NoCrossingCycleArc A B c 1 := hmin 1 (by omega) (by omega)
    unfold NoCrossingCycleArc at hOneCross
    push Not at hOneCross
    obtain ⟨i, hi, hiOpp⟩ := hOneCross
    have hnLarge : 4 ≤ c.length := by omega
    have hiShiftOpp : InOppositeParts A B ((c.append c).getVert (i + 1))
        ((c.append c).getVert (i + 2)) := by
      have hiSame := (not_inOppositeParts_iff_same_left hcover hdisj).mp (hnoTwo i hi)
      rw [inOppositeParts_iff_xor_left hcover hdisj] at hiOpp ⊢
      tauto
    have hcycleCross : ∀ j, j < c.length →
        InOppositeParts A B ((c.append c).getVert j)
          ((c.append c).getVert (j + 1)) := by
      intro j hj
      by_cases hpar : i % 2 = j % 2
      · have hpar' : (i + 1) % 2 = (j + 1) % 2 :=
          Nat.ModEq.add_right 1 hpar
        exact inOppositeParts_of_modEq_doubledCycleColorWord hcover hdisj hperTwo
          (by omega) (by omega) (by omega) (by omega) hpar hpar' hiOpp
      · have hpar₁ : (i + 1) % 2 = j % 2 := by omega
        have hpar₂ : (i + 2) % 2 = (j + 1) % 2 := by omega
        exact inOppositeParts_of_modEq_doubledCycleColorWord hcover hdisj hperTwo
          (by omega) (by omega) (by omega) (by omega) hpar₁ hpar₂ hiShiftOpp
    have hbackNot : ¬ InOppositeParts A B (c.getVert c.length)
        (c.getVert (r - 1)) := by
      intro hop
      apply hback
      exact ⟨0, 1, by omega, by omega, by omega, by simpa using hop⟩
    have hbackSame := (not_inOppositeParts_iff_same_left hcover hdisj).mp hbackNot
    rw [c.getVert_length] at hbackSame
    have hlastEdge := hcycleCross (r - 1) (by omega)
    have hlastEdge' : InOppositeParts A B (c.getVert (r - 1)) (c.getVert r) := by
      rw [Walk.getVert_append, Walk.getVert_append] at hlastEdge
      rw [if_pos (by omega), if_pos (by omega)] at hlastEdge
      simpa [show r - 1 + 1 = r by omega] using hlastEdge
    have hchordOpp : InOppositeParts A B x (c.getVert r) := by
      rw [inOppositeParts_iff_xor_left hcover hdisj] at hlastEdge' ⊢
      tauto
    exact Or.inr ⟨hcycleCross, hchordOpp⟩
  · exact Or.inl <| hasABPathLength_of_not_dvd_minimal_arc hcover hdisj hc
      (by omega) (by omega) hmNo hmin hellPos hellLt hellDvd

/-- Full chorded-cycle lemma for a rooted chord whose other endpoint uses
the shorter cyclic coordinate.  Excluding the precise bipartite exception
forces paths of every shorter length. -/
private theorem hasABPathLengths_of_short_rooted_chord {A B : Set V}
    (hcover : A ∪ B = Set.univ) (hdisj : Disjoint A B)
    {x : V} {c : G.Walk x x} (hc : c.IsCycle)
    (hcycleA : ∃ z, z ∈ c.support ∧ z ∈ A)
    (hcycleB : ∃ z, z ∈ c.support ∧ z ∈ B)
    {r : Nat} (hrTwo : 2 ≤ r) (hrHalf : 2 * r ≤ c.length)
    (hrLast : r + 2 ≤ c.length) (hchord : G.Adj x (c.getVert r))
    (hnotException : ¬ RootedCycleChordCrosses A B c r) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  classical
  intro ell hellPos hellLt
  by_contra hnPath
  have hfail : ∃ k, 1 ≤ k ∧ k < c.length ∧ ¬ HasABPathLength G A B k :=
    ⟨ell, hellPos, hellLt, hnPath⟩
  obtain ⟨m, hmTwo, hmHalf, hmLt, hmNo, hmDvdN, hmin⟩ :=
    exists_minimal_noCrossingCycleArc hcover hdisj hc hcycleA hcycleB hfail
  have hellDvd : m ∣ ell := by
    by_contra hnd
    exact hnPath (hasABPathLength_of_not_dvd_minimal_arc hcover hdisj hc
      (by omega) hmLt hmNo hmin hellPos hellLt hnd)
  by_cases hrm : r ≤ m
  · exact hnPath (hasABPathLength_of_dvd_minimal_arc_of_chord_le hcover hdisj hc
      hmTwo hmHalf hmNo hmDvdN hmin hrTwo hrm hchord hellPos hellLt hellDvd)
  · have hmr : m < r := by omega
    have hrfar : r + m < c.length := by omega
    rcases hasABPathLength_or_rootedCycleChordCrosses_of_far hcover hdisj hc
      hmTwo hmHalf hmNo hmDvdN hmin hmr hrfar hchord hellPos hellLt with hp | hex
    · exact hnPath hp
    · exact hnotException hex

/-- The full path-length conclusion when the displayed cycle is chordless.
The proof separates cycles contained in one part, genuinely alternating
cycles entered from a nearest same-part edge, and mixed cycles having a
same-part traced edge. -/
theorem hasABPathLengths_of_chordless_cycle [Fintype V]
    [DecidableRel G.Adj] {A B : Set V}
    (hconn : G.Connected) (hcover : A ∪ B = Set.univ)
    (hdisj : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hdeg : ∀ x, 3 ≤ G.degree x) (hnot : ¬ G.IsBipartiteWith A B)
    {c₀ : V} {c : G.Walk c₀ c₀} (hc : c.IsCycle)
    (hchordless : c.IsChordless) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  classical
  by_cases hallA : ∀ z, z ∈ c.support → z ∈ A
  · exact hasABPathLengths_of_left_cycle hconn hcover hdisj hB hc hallA
  by_cases hallB : ∀ z, z ∈ c.support → z ∈ B
  · exact hasABPathLengths_of_right_cycle hconn hcover hdisj hA hc hallB
  have hcycleA : ∃ z, z ∈ c.support ∧ z ∈ A := by
    push_neg at hallB
    obtain ⟨z, hzC, hzB⟩ := hallB
    refine ⟨z, hzC, ?_⟩
    have hzpart : z ∈ A ∨ z ∈ B := by
      have : z ∈ A ∪ B := by simpa [hcover]
      exact this
    exact hzpart.resolve_right hzB
  have hcycleB : ∃ z, z ∈ c.support ∧ z ∈ B := by
    push_neg at hallA
    obtain ⟨z, hzC, hzA⟩ := hallA
    refine ⟨z, hzC, ?_⟩
    exact (mem_right_iff_not_mem_left hcover hdisj).mpr hzA
  by_cases hcross : ∀ ⦃u v⦄, u ∈ c.support → v ∈ c.support → G.Adj u v →
      InOppositeParts A B u v
  · exact hasABPathLengths_of_alternating_cycle hconn hcover hdisj hnot hc hcross
  · push_neg at hcross
    obtain ⟨u, v, huC, hvC, huv, huvInt⟩ := hcross
    exact hasABPathLengths_of_chordless_internal_edge hcover hdisj hc hchordless
      (fun x hxC => hdeg x) hcycleA hcycleB ⟨u, v, huC, hvC, huv, huvInt⟩

private theorem inOppositeParts_of_mem_cycle_edges {A B : Set V}
    {x : V} {c : G.Walk x x} {u v : V}
    (hcross : ∀ i, i < c.length →
      InOppositeParts A B ((c.append c).getVert i)
        ((c.append c).getVert (i + 1)))
    (hedge : s(u, v) ∈ c.edges) : InOppositeParts A B u v := by
  have hadj : c.toSubgraph.Adj u v := Walk.adj_toSubgraph_iff_mem_edges.mpr hedge
  obtain ⟨i, hiEdge, hi⟩ := c.toSubgraph_adj_iff.mp hadj
  have hiCross := hcross i hi
  rw [getVert_append_self_eq_getVert_of_le c (by omega),
    getVert_append_self_eq_getVert_of_le c (by omega)] at hiCross
  rw [Sym2.eq, Sym2.rel_iff'] at hiEdge
  rcases hiEdge with hiEdge | hiEdge
  · have h₁ := congrArg Prod.fst hiEdge
    have h₂ := congrArg Prod.snd hiEdge
    change c.getVert i = u at h₁
    change c.getVert (i + 1) = v at h₂
    simpa [h₁, h₂] using hiCross
  · have h₁ := congrArg Prod.fst hiEdge
    have h₂ := congrArg Prod.snd hiEdge
    change c.getVert i = v at h₁
    change c.getVert (i + 1) = u at h₂
    simpa [h₁, h₂] using hiCross.symm

/-- Gao--Huo--Ma Lemma 3.2.  In a finite connected graph of minimum degree
at least three, every non-bipartition of the vertices is joined by simple
paths of every positive length shorter than any displayed cycle. -/
theorem hasABPathLengths [Fintype V] [DecidableRel G.Adj] {A B : Set V}
    (hconn : G.Connected) (hcover : A ∪ B = Set.univ)
    (hdisj : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hdeg : ∀ x, 3 ≤ G.degree x) (hnot : ¬ G.IsBipartiteWith A B)
    {c₀ : V} {c : G.Walk c₀ c₀} (hc : c.IsCycle) :
    ∀ ell, 1 ≤ ell → ell < c.length → HasABPathLength G A B ell := by
  classical
  by_cases hchordless : c.IsChordless
  · exact hasABPathLengths_of_chordless_cycle hconn hcover hdisj hA hB
      hdeg hnot hc hchordless
  by_cases hallA : ∀ z, z ∈ c.support → z ∈ A
  · exact hasABPathLengths_of_left_cycle hconn hcover hdisj hB hc hallA
  by_cases hallB : ∀ z, z ∈ c.support → z ∈ B
  · exact hasABPathLengths_of_right_cycle hconn hcover hdisj hA hc hallB
  have hcycleA : ∃ z, z ∈ c.support ∧ z ∈ A := by
    push Not at hallB
    obtain ⟨z, hzC, hzB⟩ := hallB
    refine ⟨z, hzC, ?_⟩
    have hzpart : z ∈ A ∨ z ∈ B := by
      have : z ∈ A ∪ B := by simpa [hcover]
      exact this
    exact hzpart.resolve_right hzB
  have hcycleB : ∃ z, z ∈ c.support ∧ z ∈ B := by
    push Not at hallA
    obtain ⟨z, hzC, hzA⟩ := hallA
    exact ⟨z, hzC, (mem_right_iff_not_mem_left hcover hdisj).mpr hzA⟩
  by_cases hcross : ∀ ⦃u v⦄, u ∈ c.support → v ∈ c.support → G.Adj u v →
      InOppositeParts A B u v
  · exact hasABPathLengths_of_alternating_cycle hconn hcover hdisj hnot hc hcross
  · push Not at hcross
    obtain ⟨u, v, huC, hvC, huv, huvInt⟩ := hcross
    by_cases huvEdge : s(u, v) ∈ c.edges
    · obtain ⟨x, c', r, hc', hc'len, hrTwo, hrHalf, hrLast, hchord,
          hsupp, hedges⟩ := exists_short_rooted_chord_coordinate hc hchordless
      have hcycleA' : ∃ z, z ∈ c'.support ∧ z ∈ A := by
        obtain ⟨z, hzC, hzA⟩ := hcycleA
        exact ⟨z, (hsupp z).mpr hzC, hzA⟩
      have hcycleB' : ∃ z, z ∈ c'.support ∧ z ∈ B := by
        obtain ⟨z, hzC, hzB⟩ := hcycleB
        exact ⟨z, (hsupp z).mpr hzC, hzB⟩
      have hnotException : ¬ RootedCycleChordCrosses A B c' r := by
        intro hex
        apply huvInt
        exact inOppositeParts_of_mem_cycle_edges hex.1 ((hedges s(u, v)).mpr huvEdge)
      intro ell hellPos hellLt
      apply hasABPathLengths_of_short_rooted_chord hcover hdisj hc' hcycleA'
        hcycleB' hrTwo hrHalf hrLast hchord hnotException ell hellPos
      simpa [hc'len] using hellLt
    · obtain ⟨c', r, hc', hc'len, hrTwo, hrHalf, hrLast, hrv, hchord,
          hsupp, _hedges⟩ :=
        exists_short_rooted_chord_coordinate_of_chord hc huC hvC huv huvEdge
      have hcycleA' : ∃ z, z ∈ c'.support ∧ z ∈ A := by
        obtain ⟨z, hzC, hzA⟩ := hcycleA
        exact ⟨z, (hsupp z).mpr hzC, hzA⟩
      have hcycleB' : ∃ z, z ∈ c'.support ∧ z ∈ B := by
        obtain ⟨z, hzC, hzB⟩ := hcycleB
        exact ⟨z, (hsupp z).mpr hzC, hzB⟩
      have hnotException : ¬ RootedCycleChordCrosses A B c' r := by
        intro hex
        apply huvInt
        simpa [hrv] using hex.2
      intro ell hellPos hellLt
      apply hasABPathLengths_of_short_rooted_chord hcover hdisj hc' hcycleA'
        hcycleB' hrTwo hrHalf hrLast hchord hnotException ell hellPos
      simpa [hc'len] using hellLt

end LeanCo.SizeRamsey
