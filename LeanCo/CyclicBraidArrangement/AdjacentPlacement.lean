import LeanCo.CyclicBraidArrangement.AdjacentSufficiency
import Mathlib.Logic.Equiv.Fintype

namespace CyclicBraidArrangement

open scoped BigOperators Fin.NatCast

namespace DeformationMatrix

variable {n q : ℕ}

/-- The cyclic position obtained by moving `s` places clockwise from `k`. -/
def cyclicIndex (n : ℕ) [NeZero n] (k : Fin n) (s : ℕ) : Fin n :=
  k + (s : Fin n)

@[simp] theorem cyclicIndex_zero (n : ℕ) [NeZero n] (k : Fin n) :
    cyclicIndex n k 0 = k := by
  simp [cyclicIndex]

theorem cyclicIndex_succ (n : ℕ) [NeZero n] (k : Fin n) (s : ℕ) :
    cyclicIndex n k (s + 1) = nextPosition n (cyclicIndex n k s) := by
  simp [cyclicIndex, nextPosition, add_assoc]

/-- Before one full revolution, distinct offsets give distinct cyclic positions. -/
theorem cyclicIndex_injective_below (n : ℕ) [NeZero n] (k : Fin n)
    {r s : ℕ} (hr : r < n) (hs : s < n)
    (h : cyclicIndex n k r = cyclicIndex n k s) : r = s := by
  apply_fun fun x : Fin n => x - k at h
  simp [cyclicIndex] at h
  apply_fun Fin.val at h
  simpa [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] using h

theorem cyclicIndex_ne_of_ne_below (n : ℕ) [NeZero n] (k : Fin n)
    {r s : ℕ} (hr : r < n) (hs : s < n) (hrs : r ≠ s) :
    cyclicIndex n k r ≠ cyclicIndex n k s := by
  intro h
  exact hrs (cyclicIndex_injective_below n k hr hs h)

/-- A natural gap vector with exactly `q-n` empty positions. -/
structure GapVector (n q : ℕ) where
  gap : Fin n → ℕ
  sum_eq : ∑ k, gap k = q - n

/-- A placement modulo rotation: cyclic label order plus its empty-box gaps. -/
structure CirclePlacement (n q : ℕ) where
  order : CyclicOrdering n
  gaps : GapVector n q

/-- Clockwise distance along `s` successive gaps, counting occupied endpoints. -/
def CirclePlacement.clockwiseDistance [NeZero n] (P : CirclePlacement n q)
    (k : Fin n) (s : ℕ) : ℕ :=
  ∑ r ∈ Finset.range s, (P.gaps.gap (cyclicIndex n k r) + 1)

/-- The gap inequalities attached only to consecutive labels. -/
def CirclePlacement.AdjacentBounds [NeZero n] (M : DeformationMatrix n)
    (P : CirclePlacement n q) : Prop :=
  ∀ k, M.entry (P.order k) (P.order (nextPosition n k)) ≤ P.gaps.gap k

/-- All ordered pairs avoid their forbidden clockwise interval. -/
def CirclePlacement.AvoidsAllPairs [NeZero n] (M : DeformationMatrix n)
    (P : CirclePlacement n q) : Prop :=
  ∀ (k : Fin n) (s : ℕ), 0 < s → s < n →
    M.entry (P.order k) (P.order (cyclicIndex n k s)) < P.clockwiseDistance k s

/-- Number of clockwise cyclic-order steps from label `a` to label `c`. -/
def CirclePlacement.labelSteps [NeZero n] (P : CirclePlacement n q)
    (a c : Fin n) : ℕ :=
  (P.order.symm c - P.order.symm a).val

/-- Clockwise distance between two named labels. -/
def CirclePlacement.labelDistance [NeZero n] (P : CirclePlacement n q)
    (a c : Fin n) : ℕ :=
  P.clockwiseDistance (P.order.symm a) (P.labelSteps a c)

/-- The literal all-ordered-pairs formulation from the paper. -/
def CirclePlacement.AvoidsEveryOrderedPair [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q) : Prop :=
  ∀ a c, a ≠ c → M.entry a c < P.labelDistance a c

theorem cyclicIndex_labelSteps [NeZero n] (P : CirclePlacement n q)
    {a c : Fin n} :
    cyclicIndex n (P.order.symm a) (P.labelSteps a c) = P.order.symm c := by
  let d : Fin n := P.order.symm c - P.order.symm a
  have hd : Fin.ofNat n d.val = d := by
    apply Fin.ext
    simp
  change P.order.symm a + Fin.ofNat n d.val = P.order.symm c
  rw [hd]
  simp [d]

theorem labelSteps_pos [NeZero n] (P : CirclePlacement n q)
    {a c : Fin n} (hac : a ≠ c) : 0 < P.labelSteps a c := by
  rw [CirclePlacement.labelSteps, Fin.val_pos_iff, Fin.pos_iff_ne_zero']
  intro hzero
  have hpos : P.order.symm c = P.order.symm a := sub_eq_zero.mp hzero
  exact hac (P.order.symm.injective hpos.symm)

theorem avoidsEveryOrderedPair_of_avoidsAllPairs [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q)
    (hP : P.AvoidsAllPairs M) : P.AvoidsEveryOrderedPair M := by
  intro a c hac
  have h := hP (P.order.symm a) (P.labelSteps a c)
    (labelSteps_pos P hac)
    ((P.order.symm c - P.order.symm a).isLt)
  simpa only [CirclePlacement.labelDistance, cyclicIndex_labelSteps,
    Equiv.apply_symm_apply] using h

theorem labelSteps_order_cyclicIndex [NeZero n] (P : CirclePlacement n q)
    (k : Fin n) (s : ℕ) (hsn : s < n) :
    P.labelSteps (P.order k) (P.order (cyclicIndex n k s)) = s := by
  simp [CirclePlacement.labelSteps, cyclicIndex, Nat.mod_eq_of_lt hsn]

theorem avoidsAllPairs_of_avoidsEveryOrderedPair [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q)
    (hP : P.AvoidsEveryOrderedPair M) : P.AvoidsAllPairs M := by
  intro k s hs hsn
  have hnpos : 0 < n := lt_trans hs hsn
  have hidx : cyclicIndex n k 0 ≠ cyclicIndex n k s :=
    cyclicIndex_ne_of_ne_below n k hnpos hsn (Nat.ne_of_lt hs)
  have hlabels : P.order k ≠ P.order (cyclicIndex n k s) := by
    apply P.order.injective.ne
    simpa using hidx
  have h := hP (P.order k) (P.order (cyclicIndex n k s)) hlabels
  simpa [CirclePlacement.labelDistance,
    labelSteps_order_cyclicIndex P k s hsn] using h

theorem avoidsAllPairs_iff_avoidsEveryOrderedPair [NeZero n]
    (M : DeformationMatrix n) (P : CirclePlacement n q) :
    P.AvoidsAllPairs M ↔ P.AvoidsEveryOrderedPair M :=
  ⟨avoidsEveryOrderedPair_of_avoidsAllPairs M P,
    avoidsAllPairs_of_avoidsEveryOrderedPair M P⟩

/-- Sum of the matrix lower bounds along `s` clockwise edges. -/
def cycleEntrySum [NeZero n] (M : DeformationMatrix n) (w : CyclicOrdering n)
    (k : Fin n) (s : ℕ) : ℕ :=
  ∑ r ∈ Finset.range s,
    M.entry (w (cyclicIndex n k r)) (w (cyclicIndex n k (r + 1)))

/-- The paper's iterated compatibility inequality, for an arbitrary cyclic
start position and every proper clockwise path. -/
theorem compatible_cycleEntry_bound [NeZero n] (M : DeformationMatrix n)
    (hM : M.CyclicallyCompatible) (w : CyclicOrdering n) (k : Fin n)
    (s : ℕ) (hs : 0 < s) (hsn : s < n) :
    M.entry (w k) (w (cyclicIndex n k s)) ≤
      cycleEntrySum M w k s + (s - 1) := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hzero : s = 0
      · subst s
        simp [cycleEntrySum, cyclicIndex_succ]
      · have hspos : 0 < s := Nat.pos_of_ne_zero hzero
        have hslt : s < n := lt_trans (Nat.lt_succ_self s) hsn
        have hnpos : 0 < n := lt_trans hspos hslt
        have h0s : cyclicIndex n k 0 ≠ cyclicIndex n k s :=
          cyclicIndex_ne_of_ne_below n k hnpos hslt (Nat.ne_of_lt hspos)
        have h0next : cyclicIndex n k 0 ≠ cyclicIndex n k (s + 1) :=
          cyclicIndex_ne_of_ne_below n k hnpos hsn (Nat.ne_of_lt hs)
        have hsnext : cyclicIndex n k s ≠ cyclicIndex n k (s + 1) :=
          cyclicIndex_ne_of_ne_below n k hslt hsn (Nat.ne_of_lt (Nat.lt_succ_self s))
        have hab : w k ≠ w (cyclicIndex n k s) := by
          simpa using w.injective.ne h0s
        have hac : w k ≠ w (cyclicIndex n k (s + 1)) := by
          simpa using w.injective.ne h0next
        have hbc : w (cyclicIndex n k s) ≠ w (cyclicIndex n k (s + 1)) :=
          w.injective.ne hsnext
        have hcompat := hM (w k) (w (cyclicIndex n k s))
          (w (cyclicIndex n k (s + 1))) hab hac hbc
        have hind := ih hspos hslt
        simp only [cycleEntrySum, Finset.sum_range_succ]
        simp only [cycleEntrySum] at hind
        omega

/-- Under cyclic compatibility, all adjacent lower bounds imply every
ordered-pair avoidance inequality, for every `q ≥ n`. -/
theorem adjacentBounds_imply_avoidsAllPairs [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (q : ℕ) (_hq : n ≤ q) (P : CirclePlacement n q)
    (hP : P.AdjacentBounds M) : P.AvoidsAllPairs M := by
  intro k s hs hsn
  have hpath := compatible_cycleEntry_bound M hM P.order k s hs hsn
  have hsum : cycleEntrySum M P.order k s ≤
      ∑ r ∈ Finset.range s, P.gaps.gap (cyclicIndex n k r) := by
    unfold cycleEntrySum
    apply Finset.sum_le_sum
    intro r hr
    simpa only [cyclicIndex_succ] using hP (cyclicIndex n k r)
  unfold CirclePlacement.clockwiseDistance
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  omega

theorem adjacentBounds_imply_avoidsEveryOrderedPair [NeZero n]
    (M : DeformationMatrix n) (hM : M.CyclicallyCompatible)
    (q : ℕ) (hq : n ≤ q) (P : CirclePlacement n q)
    (hP : P.AdjacentBounds M) : P.AvoidsEveryOrderedPair M :=
  avoidsEveryOrderedPair_of_avoidsAllPairs M P
    (adjacentBounds_imply_avoidsAllPairs M hM q hq P hP)

/-- The exact universally quantified property in Proposition 2.2(ii). -/
def AdjacentSufficiencyProperty [NeZero n] (M : DeformationMatrix n) : Prop :=
  ∀ (q : ℕ), n ≤ q → ∀ P : CirclePlacement n q,
    P.AdjacentBounds M → P.AvoidsEveryOrderedPair M

/-- Any three distinct labels can be made the first three consecutive labels
of a cyclic ordering. -/
theorem exists_cyclicOrdering_first_three (hn : 3 ≤ n)
    (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ w : CyclicOrdering n,
      w (Fin.castLE hn 0) = a ∧
      w (Fin.castLE hn 1) = b ∧
      w (Fin.castLE hn 2) = c := by
  let f : Fin 3 → Fin n := Fin.castLE hn
  let g : Fin 3 → Fin n := ![a, b, c]
  have hf : Function.Injective f := Fin.castLE_injective hn
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g]
  obtain ⟨w, hw⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa [f, g] using hw (0 : Fin 3)
  · simpa [f, g] using hw (1 : Fin 3)
  · simpa [f, g] using hw (2 : Fin 3)

theorem three_le_of_pairwise_ne (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ n := by
  fin_omega

/-- If compatibility fails (and there are at least three labels), there is an
actual `q ≥ n` gap placement satisfying every adjacent lower bound but
failing an all-pairs avoidance inequality. -/
theorem bad_circlePlacement_of_not_cyclicallyCompatible [NeZero n]
    (M : DeformationMatrix n) (hM : ¬M.CyclicallyCompatible) :
    ∃ q : ℕ, n ≤ q ∧ ∃ P : CirclePlacement n q,
      P.AdjacentBounds M ∧ ¬P.AvoidsEveryOrderedPair M := by
  obtain ⟨a, b, c, hab, hac, hbc, hbad⟩ :=
    M.unsafe_witness_of_not_cyclicallyCompatible hM
  have hn : 3 ≤ n := three_le_of_pairwise_ne a b c hab hac hbc
  obtain ⟨w, hw0, hw1, hw2⟩ :=
    exists_cyclicOrdering_first_three hn a b c hab hac hbc
  let gap : Fin n → ℕ := fun k ↦ M.entry (w k) (w (nextPosition n k))
  let q : ℕ := n + ∑ k, gap k
  have hq : n ≤ q := by simp [q]
  have hsum : ∑ k, gap k = q - n := by
    simp [q]
  let G : GapVector n q := ⟨gap, hsum⟩
  let P : CirclePlacement n q := ⟨w, G⟩
  refine ⟨q, hq, P, ?_, ?_⟩
  · intro k
    simp [P, G, gap]
  · intro hall
    have hall' : P.AvoidsAllPairs M :=
      avoidsAllPairs_of_avoidsEveryOrderedPair M P hall
    let k₀ : Fin n := Fin.castLE hn 0
    let k₁ : Fin n := Fin.castLE hn 1
    let k₂ : Fin n := Fin.castLE hn 2
    have hk₀ : cyclicIndex n k₀ 0 = k₀ := cyclicIndex_zero n k₀
    have hk₁ : cyclicIndex n k₀ 1 = k₁ := by
      apply Fin.ext
      simp [cyclicIndex, k₀, k₁, Fin.val_add, Nat.mod_eq_of_lt (show 1 < n by omega)]
    have hk₂ : cyclicIndex n k₀ 2 = k₂ := by
      apply Fin.ext
      simp [cyclicIndex, k₀, k₂, Fin.val_add, Nat.mod_eq_of_lt (show 2 < n by omega)]
    have havoid := hall' k₀ 2 (by omega) (by omega)
    simp only [CirclePlacement.clockwiseDistance, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, hk₀, hk₁, hk₂] at havoid
    change M.entry (w k₀) (w k₂) <
      (gap k₀ + 1) + (gap k₁ + 1) at havoid
    have hnext₀ : nextPosition n k₀ = k₁ := by
      calc
        nextPosition n k₀ = nextPosition n (cyclicIndex n k₀ 0) :=
          congrArg (nextPosition n) hk₀.symm
        _ = cyclicIndex n k₀ 1 := (cyclicIndex_succ n k₀ 0).symm
        _ = k₁ := hk₁
    have hnext₁ : nextPosition n k₁ = k₂ := by
      calc
        nextPosition n k₁ = nextPosition n (cyclicIndex n k₀ 1) :=
          congrArg (nextPosition n) hk₁.symm
        _ = cyclicIndex n k₀ 2 := (cyclicIndex_succ n k₀ 1).symm
        _ = k₂ := hk₂
    simp [gap, hnext₀, hnext₁, k₀, k₁, k₂, hw0, hw1, hw2] at havoid
    omega

/-- Proposition 2.2, exactly at the gap-placement level. -/
theorem cyclicallyCompatible_iff_adjacentSufficiencyProperty [NeZero n]
    (M : DeformationMatrix n) :
    M.CyclicallyCompatible ↔ AdjacentSufficiencyProperty M := by
  constructor
  · intro hM q hq P hP
    exact adjacentBounds_imply_avoidsEveryOrderedPair M hM q hq P hP
  · intro hprop
    by_contra hM
    obtain ⟨q, hq, P, hP, hbad⟩ :=
      bad_circlePlacement_of_not_cyclicallyCompatible M hM
    exact hbad (hprop q hq P hP)

end DeformationMatrix

end CyclicBraidArrangement
