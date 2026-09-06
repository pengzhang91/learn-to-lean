import LeanCo.InversionDescent.Permutation
import LeanCo.InversionDescent.Gaussian

/-!
# The last-zero recurrence

This file formalizes Theorem 2.5 of Pan's paper.  Proposition 2.4 says that,
in the reverse Lehmer code of an avoiding permutation, every strict rise starts
at zero.  Such a code has a unique last-zero decomposition.  If its length is
`n + 1`, either its final entry is zero, or its last zero has position `k < n`.
In the latter case the positive tail is weakly decreasing; subtracting one
from each of its `n-k` entries gives a partition in an `(n-k) x k` rectangle.

`AvoidingCode` is the resulting canonical (and disjoint) normal form.  Keeping
the normal form as a sum type makes the exhaustiveness and uniqueness of the
last-zero decomposition definitional.  `entries` below decodes it to the
ordinary inversion-sequence entries.
-/

open scoped BigOperators

namespace LeanCo

/-! ## The paper's inversion-sequence class -/

/-- Every strict rise of an inversion sequence starts at zero. -/
def RisesOnlyFromZero {n : ℕ} (a : Fin n → ℕ) : Prop :=
  ∀ ⦃i j : Fin n⦄, Permutation.Adjacent i j → a i < a j → a i = 0

/-- The inversion sequences singled out by Proposition 2.4. -/
def RestrictedInversionSequences (n : ℕ) :=
  {a : Permutation.InversionSequences n // RisesOnlyFromZero a.1}

/-- For inversion sequences, avoiding `0-12` is exactly the rise-from-zero condition. -/
theorem avoids0_12_iff_risesOnlyFromZero {n : ℕ}
    (a : Permutation.InversionSequences n) :
    Permutation.Avoids0_12 a.1 ↔ RisesOnlyFromZero a.1 := by
  constructor
  · intro hav i j hij hrij
    by_contra hne
    have hpos : 0 < a.1 i := Nat.pos_of_ne_zero hne
    let z : Fin n := ⟨0, lt_of_le_of_lt (Nat.zero_le i.1) i.2⟩
    have hz : a.1 z = 0 := by
      exact Nat.eq_zero_of_le_zero (a.2 z)
    have hzi : z < i := by
      change 0 < i.1
      by_contra hi
      have hi0 : i.1 = 0 := by omega
      have hai0 : a.1 i = 0 := Nat.eq_zero_of_le_zero (by simpa [hi0] using a.2 i)
      omega
    apply hav
    refine ⟨z, i, j, hzi, hij, ?_, hrij⟩
    rw [hz]
    exact hpos
  · intro hr hocc
    rcases hocc with ⟨i, j, k, hij, hjk, haij, hajk⟩
    have hj0 := hr hjk hajk
    omega

/-- The paper's avoiding inversion sequences, presented with its literal pattern predicate. -/
def AvoidingInversionSequences (n : ℕ) :=
  {a : Permutation.InversionSequences n // Permutation.Avoids0_12 a.1}

/-- Proposition 2.4 gives an identity-on-entries equivalence of the two presentations. -/
def restrictedAvoidingEquiv (n : ℕ) :
    RestrictedInversionSequences n ≃ AvoidingInversionSequences n where
  toFun a := ⟨a.1, (avoids0_12_iff_risesOnlyFromZero a.1).2 a.2⟩
  invFun a := ⟨a.1, (avoids0_12_iff_risesOnlyFromZero a.1).1 a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance restrictedFinite (n : ℕ) : Finite (RestrictedInversionSequences n) := by
  let f : RestrictedInversionSequences n → (∀ i : Fin n, Fin (i.1 + 1)) :=
    fun a i ↦ ⟨a.1.1 i, by have := a.1.2 i; omega⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

noncomputable instance restrictedFintype (n : ℕ) : Fintype (RestrictedInversionSequences n) :=
  Fintype.ofFinite _

noncomputable instance restrictedDecidableEq (n : ℕ) :
    DecidableEq (RestrictedInversionSequences n) := Classical.decEq _

/-- Sum of the entries, corresponding to permutation inversions under reverse Lehmer. -/
def sequenceInversionWeight {n : ℕ} (a : Permutation.InversionSequences n) : ℕ :=
  ∑ i, a.1 i

/-- Positions at which an inversion sequence has a strict rise. -/
noncomputable def riseSet {n : ℕ} (a : Fin n → ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ ∃ j, Permutation.Adjacent i j ∧ a i < a j

@[simp] theorem mem_riseSet {n : ℕ} {a : Fin n → ℕ} {i : Fin n} :
    i ∈ riseSet a ↔ ∃ j, Permutation.Adjacent i j ∧ a i < a j := by
  classical
  simp [riseSet]

/-- Number of strict rises, corresponding to descents under reverse Lehmer. -/
noncomputable def sequenceDescentWeight {n : ℕ}
    (a : Permutation.InversionSequences n) : ℕ :=
  (riseSet a.1).card

/-- Literal finite-sum enumerator of the paper's avoiding inversion sequences. -/
noncomputable def avoidingSequenceEnumerator {R : Type*} [CommSemiring R]
    (q t : R) (n : ℕ) : R :=
  ∑ a : RestrictedInversionSequences n,
    q ^ sequenceInversionWeight a.1 * t ^ sequenceDescentWeight a.1

/-- Canonical last-zero normal forms for `0-12`-avoiding inversion sequences. -/
def AvoidingCode : ℕ → Type
  | 0 => PUnit
  | n + 1 =>
      AvoidingCode n ⊕
        (Σ k : Fin n, AvoidingCode k.1 × RectanglePartition (n - k.1) k.1)
termination_by n => n

namespace AvoidingCode

/-- Unfold one positive-length last-zero normal form. -/
def split {n : ℕ} (c : AvoidingCode (n + 1)) :
    AvoidingCode n ⊕
      (Σ k : Fin n, AvoidingCode k.1 × RectanglePartition (n - k.1) k.1) := by
  simpa only [AvoidingCode] using c

/-- Fold one layer of the last-zero normal form. -/
def fold {n : ℕ}
    (c : AvoidingCode n ⊕
      (Σ k : Fin n, AvoidingCode k.1 × RectanglePartition (n - k.1) k.1)) :
    AvoidingCode (n + 1) := by
  simpa only [AvoidingCode] using c

@[simp] theorem split_fold {n : ℕ}
    (c : AvoidingCode n ⊕
      (Σ k : Fin n, AvoidingCode k.1 × RectanglePartition (n - k.1) k.1)) :
    split (fold c) = c := by
  simp [split, fold]

@[simp] theorem fold_split {n : ℕ} (c : AvoidingCode (n + 1)) :
    fold (split c) = c := by
  simp [split, fold]

/-- The one-step, disjoint last-zero decomposition as an equivalence. -/
def splitEquiv (n : ℕ) :
    AvoidingCode (n + 1) ≃
      (AvoidingCode n ⊕
        (Σ k : Fin n, AvoidingCode k.1 × RectanglePartition (n - k.1) k.1)) where
  toFun := split
  invFun := fold
  left_inv := fold_split
  right_inv := split_fold

@[simp] theorem splitEquiv_symm_apply {n : ℕ}
    (c : AvoidingCode n ⊕
      (Σ k : Fin n, AvoidingCode k.1 × RectanglePartition (n - k.1) k.1)) :
    (splitEquiv n).symm c = fold c := rfl

instance finite (n : ℕ) : Finite (AvoidingCode n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp only [AvoidingCode]
          infer_instance
      | succ n =>
          simp only [AvoidingCode]
          letI : Finite (AvoidingCode n) := ih n (by omega)
          letI (k : Fin n) : Finite (AvoidingCode k.1) := ih k.1 (by omega)
          infer_instance

noncomputable instance fintype (n : ℕ) : Fintype (AvoidingCode n) :=
  Fintype.ofFinite _

noncomputable instance decidableEq (n : ℕ) : DecidableEq (AvoidingCode n) :=
  Classical.decEq _

/-- Decode a normal form to its list of inversion-sequence entries. -/
def entries : {n : ℕ} → AvoidingCode n → List ℕ
  | 0, _ => []
  | n + 1, c =>
      match split c with
      | Sum.inl c => entries c ++ [0]
      | Sum.inr ⟨_, c, p⟩ =>
          entries c ++ 0 :: List.ofFn (fun i ↦ (p.1 i).1 + 1)
termination_by n c => n

/-- The inversion statistic of a normal form. -/
def inversionWeight : {n : ℕ} → AvoidingCode n → ℕ
  | 0, _ => 0
  | n + 1, c =>
      match split c with
      | Sum.inl c => inversionWeight c
      | Sum.inr ⟨k, c, p⟩ =>
          inversionWeight c + (n - k.1) + p.weight
termination_by n c => n

/-- The descent statistic: the number of strict rises of the reverse code. -/
def descentWeight : {n : ℕ} → AvoidingCode n → ℕ
  | 0, _ => 0
  | n + 1, c =>
      match split c with
      | Sum.inl c => descentWeight c
      | Sum.inr ⟨_, c, _⟩ => descentWeight c + 1
termination_by n c => n

@[simp]
theorem entries_length {n : ℕ} (c : AvoidingCode n) : c.entries.length = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [entries]
      | succ n =>
          rcases hsplit : split c with c' | ⟨k, c', p⟩
          · simp [entries, hsplit, ih n (by omega) c']
          · simp [entries, hsplit, ih k.1 (by omega) c']
            omega

@[simp]
theorem entries_sum_eq_inversionWeight {n : ℕ} (c : AvoidingCode n) :
    c.entries.sum = c.inversionWeight := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [entries, inversionWeight]
      | succ n =>
          rcases hsplit : split c with c' | ⟨k, c', p⟩
          · simp [entries, inversionWeight, hsplit, ih n (by omega) c']
          · simp only [entries, inversionWeight, hsplit, List.sum_append,
              List.sum_cons, List.sum_nil, add_zero, ih k.1 (by omega) c',
              List.sum_ofFn, RectanglePartition.weight]
            rw [Finset.sum_add_distrib]
            simp
            omega

/-- The entry at a genuine `Fin n` position, decoded directly from the normal form. -/
def entry : {n : ℕ} → AvoidingCode n → Fin n → ℕ
  | 0, _, i => Fin.elim0 i
  | n + 1, c, i =>
      match split c with
      | Sum.inl c' =>
          if hi : i.1 < n then entry c' ⟨i.1, hi⟩ else 0
      | Sum.inr ⟨k, c', p⟩ =>
          if hik : i.1 < k.1 then
            entry c' ⟨i.1, hik⟩
          else if heq : i.1 = k.1 then
            0
          else
            (p.1 ⟨i.1 - k.1 - 1, by omega⟩).1 + 1
termination_by n c i => n

/-- Decoded normal forms satisfy the inversion-sequence bounds. -/
theorem entry_le_index {n : ℕ} (c : AvoidingCode n) (i : Fin n) :
    c.entry i ≤ i.1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
          rcases hsplit : split c with c' | ⟨k, c', p⟩
          · by_cases hi : i.1 < n
            · let i' : Fin n := ⟨i.1, hi⟩
              have hc := ih n (by omega) c' i'
              simpa [entry, hsplit, hi, i'] using hc
            · simp [entry, hsplit, hi]
          · by_cases hik : i.1 < k.1
            · let i' : Fin k.1 := ⟨i.1, hik⟩
              have hc := ih k.1 (by omega) c' i'
              simpa [entry, hsplit, hik, i'] using hc
            · by_cases heq : i.1 = k.1
              · simp [entry, hsplit, hik, heq]
              · let r : Fin (n - k.1) := ⟨i.1 - k.1 - 1, by omega⟩
                have hp : (p.1 r).1 ≤ k.1 := by omega
                simp only [entry, hsplit, hik, heq, ↓reduceDIte]
                change (p.1 r).1 + 1 ≤ i.1
                omega

/-- Decoded normal forms have no strict rise whose left entry is positive. -/
theorem entry_risesOnlyFromZero {n : ℕ} (c : AvoidingCode n) :
    RisesOnlyFromZero c.entry := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro i j hij hrij
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
          rcases hsplit : split c with c' | ⟨k, c', p⟩
          · by_cases hjn : j.1 < n
            · have hin : i.1 < n := by
                change j.1 = i.1 + 1 at hij
                omega
              let i' : Fin n := ⟨i.1, hin⟩
              let j' : Fin n := ⟨j.1, hjn⟩
              have hij' : Permutation.Adjacent i' j' := by
                exact hij
              have hrij' : c'.entry i' < c'.entry j' := by
                simpa [entry, hsplit, hin, hjn, i', j'] using hrij
              have hz := ih n (by omega) c' hij' hrij'
              simpa [entry, hsplit, hin, i'] using hz
            · have hjEq : j.1 = n := by omega
              have hjzero : c.entry j = 0 := by
                simp [entry, hsplit, hjn]
              omega
          · by_cases hik : i.1 < k.1
            · by_cases hjk : j.1 < k.1
              · let i' : Fin k.1 := ⟨i.1, hik⟩
                let j' : Fin k.1 := ⟨j.1, hjk⟩
                have hij' : Permutation.Adjacent i' j' := by exact hij
                have hrij' : c'.entry i' < c'.entry j' := by
                  simpa [entry, hsplit, hik, hjk, i', j'] using hrij
                have hz := ih k.1 (by omega) c' hij' hrij'
                simpa [entry, hsplit, hik, i'] using hz
              · have hjEq : j.1 = k.1 := by
                  change j.1 = i.1 + 1 at hij
                  omega
                have hjzero : c.entry j = 0 := by
                  simp [entry, hsplit, hjk, hjEq]
                omega
            · by_cases hiEq : i.1 = k.1
              · simp [entry, hsplit, hik, hiEq]
              · have hki : k.1 < i.1 := by omega
                have hkj : k.1 < j.1 := by
                  change j.1 = i.1 + 1 at hij
                  omega
                have hijval : j.1 = i.1 + 1 := hij
                let r : Fin (n - k.1) := ⟨i.1 - k.1 - 1, by omega⟩
                let s : Fin (n - k.1) := ⟨j.1 - k.1 - 1, by omega⟩
                have hrs : r ≤ s := by
                  change i.1 - k.1 - 1 ≤ j.1 - k.1 - 1
                  omega
                have hp : (p.1 s).1 ≤ (p.1 r).1 := by
                  exact_mod_cast p.2 hrs
                have hjknot : ¬ j.1 < k.1 := by omega
                have hjne : ¬ j.1 = k.1 := by omega
                have hrij' : (p.1 r).1 + 1 < (p.1 s).1 + 1 := by
                  simpa [entry, hsplit, hik, hiEq, hjknot, hjne, r, s] using hrij
                omega

/-- Decode a normal form to the literal restricted inversion-sequence subtype. -/
def toRestricted {n : ℕ} (c : AvoidingCode n) : RestrictedInversionSequences n :=
  ⟨⟨c.entry, entry_le_index c⟩, entry_risesOnlyFromZero c⟩

/-- Delete the final entry of a restricted inversion sequence. -/
def restrictedPrefix {n : ℕ} (a : RestrictedInversionSequences (n + 1)) :
    RestrictedInversionSequences n := by
  refine ⟨⟨fun i ↦ a.1.1 i.castSucc, ?_⟩, ?_⟩
  · intro i
    exact a.1.2 i.castSucc
  · intro i j hij hrij
    exact a.2 (by exact hij) hrij

/-- The empty normal form. -/
def nil : AvoidingCode 0 := by
  simpa only [AvoidingCode] using PUnit.unit

@[simp] theorem entry_fold_inl_cast {n : ℕ} (c : AvoidingCode n) (i : Fin n) :
    entry (fold (Sum.inl c) : AvoidingCode (n + 1)) i.castSucc = entry c i := by
  simp [entry]

@[simp] theorem entry_fold_inl_last {n : ℕ} (c : AvoidingCode n) :
    entry (fold (Sum.inl c) : AvoidingCode (n + 1)) (Fin.last n) = 0 := by
  simp [entry]

/--
Completeness of the last-zero normal form: every literal restricted inversion
sequence is decoded by some normal form.  The nonzero-final branch chooses the
maximum zero position and turns the remaining weakly decreasing positive tail
into a rectangle partition by subtracting one.
-/
theorem exists_code_entry_eq {n : ℕ} (a : RestrictedInversionSequences n) :
    ∃ c : AvoidingCode n, ∀ i, c.entry i = a.1.1 i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact ⟨nil, fun i ↦ Fin.elim0 i⟩
      | succ n =>
          let x := a.1.1 (Fin.last n)
          by_cases hx : x = 0
          · obtain ⟨c, hc⟩ := ih n (by omega) (restrictedPrefix a)
            refine ⟨fold (Sum.inl c), ?_⟩
            intro i
            by_cases hi : i.1 < n
            · let i' : Fin n := ⟨i.1, hi⟩
              have hiCast : i'.castSucc = i := Fin.ext rfl
              rw [← hiCast]
              simpa [restrictedPrefix] using hc i'
            · have hiEq : i = Fin.last n := Fin.ext (by simp; omega)
              subst i
              simpa [x] using hx.symm
          · classical
            let Z : Finset (Fin (n + 1)) :=
              Finset.univ.filter fun i ↦ a.1.1 i = 0
            let z0 : Fin (n + 1) := ⟨0, by omega⟩
            have ha0 : a.1.1 z0 = 0 :=
              Nat.eq_zero_of_le_zero (a.1.2 z0)
            have hZ : Z.Nonempty := by
              exact ⟨z0, by simp [Z, ha0]⟩
            let z : Fin (n + 1) := Z.max' hZ
            have hzmem : z ∈ Z := Finset.max'_mem Z hZ
            have hzzero : a.1.1 z = 0 := by
              simpa [Z] using hzmem
            have hzlt : z.1 < n := by
              by_contra hnz
              have hzlast : z = Fin.last n := Fin.ext (by simp; omega)
              apply hx
              simpa [x, hzlast] using hzzero
            let k : Fin n := ⟨z.1, hzlt⟩
            let b : RestrictedInversionSequences z.1 := by
              refine ⟨⟨fun i ↦ a.1.1 ⟨i.1, by omega⟩, ?_⟩, ?_⟩
              · intro i
                exact a.1.2 ⟨i.1, by omega⟩
              · intro i j hij hrij
                exact a.2 (by exact hij) hrij
            obtain ⟨c, hc⟩ := ih z.1 (by omega) b
            let g : Fin (n - z.1) → Fin (n + 1) :=
              fun r ↦ ⟨z.1 + 1 + r.1, by omega⟩
            have hgnz (r : Fin (n - z.1)) : a.1.1 (g r) ≠ 0 := by
              intro hzero
              have hgmem : g r ∈ Z := by simp [Z, hzero]
              have hle : g r ≤ z := Finset.le_max' Z (g r) hgmem
              change z.1 + 1 + r.1 ≤ z.1 at hle
              omega
            let v : Fin (n - z.1) → ℕ := fun r ↦ a.1.1 (g r) - 1
            have hvanti : Antitone v := by
              let vf : ℕ → ℕ := fun m ↦
                if hm : m < n - z.1 then v ⟨m, hm⟩ else 0
              have hvf : Antitone vf := antitone_nat_of_succ_le fun m ↦ by
                by_cases hs : m + 1 < n - z.1
                · have hm : m < n - z.1 := by omega
                  let il : Fin (n + 1) := g ⟨m, hm⟩
                  let ir : Fin (n + 1) := g ⟨m + 1, hs⟩
                  have hilr : Permutation.Adjacent il ir := by
                    change (g ⟨m + 1, hs⟩).1 = (g ⟨m, hm⟩).1 + 1
                    simp [g]
                    omega
                  have hnonzero : a.1.1 il ≠ 0 := hgnz ⟨m, hm⟩
                  have hle : a.1.1 ir ≤ a.1.1 il := by
                    by_contra hnot
                    have hrise : a.1.1 il < a.1.1 ir := by omega
                    exact hnonzero (a.2 hilr hrise)
                  simp only [vf, dif_pos hs, dif_pos hm]
                  change v ⟨m + 1, hs⟩ ≤ v ⟨m, hm⟩
                  dsimp [v]
                  have hle' : a.1.1 (g ⟨m + 1, hs⟩) ≤ a.1.1 (g ⟨m, hm⟩) := by
                    simpa [il, ir] using hle
                  omega
                · simp only [vf, dif_neg hs]
                  exact Nat.zero_le _
              intro r s hrs
              have := hvf (show r.1 ≤ s.1 from hrs)
              simpa [vf, r.2, s.2] using this
            have hvbound (r : Fin (n - z.1)) : v r ≤ z.1 := by
              let r0 : Fin (n - z.1) := ⟨0, by omega⟩
              have hr0 : r0 ≤ r := by
                change 0 ≤ r.1
                omega
              have hvr : v r ≤ v r0 := hvanti hr0
              have hfirst := a.1.2 (g r0)
              dsimp [v, g, r0] at hvr hfirst ⊢
              omega
            let p : RectanglePartition (n - z.1) z.1 := by
              refine ⟨fun r ↦ ⟨v r, by have := hvbound r; omega⟩, ?_⟩
              intro r s hrs
              exact hvanti hrs
            refine ⟨fold (Sum.inr ⟨k, c, p⟩), ?_⟩
            intro i
            by_cases hiz : i.1 < z.1
            · let i' : Fin z.1 := ⟨i.1, hiz⟩
              have hc' := hc i'
              simpa [entry, k, hiz, b, i'] using hc'
            · by_cases hieq : i.1 = z.1
              · have hizero : a.1.1 i = 0 := by
                  have hiEq : i = z := Fin.ext hieq
                  simpa [hiEq] using hzzero
                simpa [entry, k, hiz, hieq] using hizero.symm
              · have hzi : z.1 < i.1 := by omega
                let r : Fin (n - z.1) := ⟨i.1 - z.1 - 1, by omega⟩
                have hgr : g r = i := Fin.ext (by simp [g, r]; omega)
                have hpos : 0 < a.1.1 i := by
                  have := hgnz r
                  simpa [hgr] using Nat.pos_of_ne_zero this
                simp only [entry, split_fold]
                rw [dif_neg hiz, dif_neg]
                · change (p.1 r).1 + 1 = a.1.1 i
                  change v r + 1 = a.1.1 i
                  dsimp [v]
                  rw [hgr]
                  omega
                · simpa [k] using hieq

/-- The decoding function remembers the whole normal form. -/
theorem entry_injective {n : ℕ} :
    Function.Injective (fun c : AvoidingCode n ↦ c.entry) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro c d hcd
      cases n with
      | zero =>
          letI : Subsingleton (AvoidingCode 0) := by
            simpa only [AvoidingCode] using (inferInstance : Subsingleton PUnit)
          exact Subsingleton.elim c d
      | succ n =>
          rcases hc : split c with c₀ | ⟨k, c₀, p⟩
          · rcases hd : split d with d₀ | ⟨l, d₀, s⟩
            · have hcform : c = fold (Sum.inl c₀) := by
                calc
                  c = fold (split c) := (fold_split c).symm
                  _ = fold (Sum.inl c₀) := congrArg fold hc
              have hdform : d = fold (Sum.inl d₀) := by
                calc
                  d = fold (split d) := (fold_split d).symm
                  _ = fold (Sum.inl d₀) := congrArg fold hd
              rw [hcform, hdform] at hcd ⊢
              have hpre : c₀.entry = d₀.entry := by
                funext i
                simpa using congrFun hcd i.castSucc
              have := ih n (by omega) hpre
              subst d₀
              rfl
            · have hcform : c = fold (Sum.inl c₀) := by
                calc
                  c = fold (split c) := (fold_split c).symm
                  _ = fold (Sum.inl c₀) := congrArg fold hc
              have hdform : d = fold (Sum.inr ⟨l, d₀, s⟩) := by
                calc
                  d = fold (split d) := (fold_split d).symm
                  _ = fold (Sum.inr ⟨l, d₀, s⟩) := congrArg fold hd
              rw [hcform, hdform] at hcd
              have hlast := congrFun hcd (Fin.last n)
              have hnl : ¬ n < l.1 := by omega
              have hne : ¬ n = l.1 := by omega
              simp [entry, hnl, hne] at hlast
          · rcases hd : split d with d₀ | ⟨l, d₀, s⟩
            · have hcform : c = fold (Sum.inr ⟨k, c₀, p⟩) := by
                calc
                  c = fold (split c) := (fold_split c).symm
                  _ = fold (Sum.inr ⟨k, c₀, p⟩) := congrArg fold hc
              have hdform : d = fold (Sum.inl d₀) := by
                calc
                  d = fold (split d) := (fold_split d).symm
                  _ = fold (Sum.inl d₀) := congrArg fold hd
              rw [hcform, hdform] at hcd
              have hlast := congrFun hcd (Fin.last n)
              have hnk : ¬ n < k.1 := by omega
              have hne : ¬ n = k.1 := by omega
              simp [entry, hnk, hne] at hlast
            · have hcform : c = fold (Sum.inr ⟨k, c₀, p⟩) := by
                calc
                  c = fold (split c) := (fold_split c).symm
                  _ = fold (Sum.inr ⟨k, c₀, p⟩) := congrArg fold hc
              have hdform : d = fold (Sum.inr ⟨l, d₀, s⟩) := by
                calc
                  d = fold (split d) := (fold_split d).symm
                  _ = fold (Sum.inr ⟨l, d₀, s⟩) := congrArg fold hd
              rw [hcform, hdform] at hcd ⊢
              have hkl : k.1 = l.1 := by
                by_contra hne
                rcases lt_or_gt_of_ne hne with hlt | hgt
                · let i : Fin (n + 1) := ⟨l.1, by omega⟩
                  have hiK : ¬ i.1 < k.1 := by simp [i]; omega
                  have hiKne : ¬ i.1 = k.1 := by simp [i]; omega
                  have hiL : ¬ i.1 < l.1 := by simp [i]
                  have hiLeq : i.1 = l.1 := by simp [i]
                  have heq := congrFun hcd i
                  have hlk : ¬ l < k := by omega
                  have hlkne : ¬ l.1 = k.1 := by omega
                  simp only [entry, split_fold] at heq
                  rw [dif_neg hiK, dif_neg hiKne, dif_neg hiL, dif_pos hiLeq] at heq
                  omega
                · let i : Fin (n + 1) := ⟨k.1, by omega⟩
                  have hiK : ¬ i.1 < k.1 := by simp [i]
                  have hiKeq : i.1 = k.1 := by simp [i]
                  have hiL : ¬ i.1 < l.1 := by simp [i]; omega
                  have hiLne : ¬ i.1 = l.1 := by simp [i]; omega
                  have heq := congrFun hcd i
                  have hkl' : ¬ k < l := by omega
                  have hklne : ¬ k.1 = l.1 := by omega
                  simp only [entry, split_fold] at heq
                  rw [dif_neg hiK, dif_pos hiKeq, dif_neg hiL, dif_neg hiLne] at heq
                  omega
              have hfin : k = l := Fin.ext hkl
              subst l
              have hpre : c₀.entry = d₀.entry := by
                funext i
                let j : Fin (n + 1) := ⟨i.1, by omega⟩
                have hj : j.1 < k.1 := i.2
                simpa [entry, j, hj] using congrFun hcd j
              have hc₀d₀ := ih k.1 (by omega) hpre
              subst d₀
              have hps : p = s := by
                apply Subtype.ext
                funext r
                apply Fin.ext
                let i : Fin (n + 1) := ⟨k.1 + 1 + r.1, by omega⟩
                have hik : ¬ i.1 < k.1 := by simp [i]; omega
                have hineq : ¬ i.1 = k.1 := by simp [i]; omega
                have heq := congrFun hcd i
                simp only [entry, split_fold] at heq
                simp only [dif_neg hik, dif_neg hineq] at heq
                let r' : Fin (n - k.1) := ⟨i.1 - k.1 - 1, by omega⟩
                have hr' : r' = r := Fin.ext (by simp [r', i]; omega)
                change (p.1 r').1 + 1 = (s.1 r').1 + 1 at heq
                rw [hr'] at heq
                omega
              subst s
              rfl

/-- The last-zero normal form is equivalent to the paper's literal class. -/
noncomputable def restrictedEquiv (n : ℕ) :
    AvoidingCode n ≃ RestrictedInversionSequences n :=
  Equiv.ofBijective toRestricted ⟨by
    intro c d h
    apply entry_injective
    funext i
    exact congrArg (fun a : RestrictedInversionSequences n ↦ a.1.1 i) h,
    by
      intro a
      obtain ⟨c, hc⟩ := exists_code_entry_eq a
      refine ⟨c, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext i
      exact hc i⟩

@[simp] theorem restrictedEquiv_apply {n : ℕ} (c : AvoidingCode n) :
    restrictedEquiv n c = toRestricted c := rfl

/-- The direct decoder agrees pointwise with the list decoder. -/
theorem entries_getElem?_eq_entry {n : ℕ} (c : AvoidingCode n) (i : Fin n) :
    c.entries[i.1]? = some (c.entry i) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => exact Fin.elim0 i
      | succ n =>
          rcases hsplit : split c with c' | ⟨k, c', p⟩
          · by_cases hi : i.1 < n
            · let i' : Fin n := ⟨i.1, hi⟩
              have hc := ih n (by omega) c' i'
              simp only [entry, entries, hsplit, dif_pos hi]
              rw [List.getElem?_append_left (by simp [entries_length, hi])]
              simpa [i'] using hc
            · simp only [entry, entries, hsplit, dif_neg hi]
              have hin : i.1 = n := by omega
              rw [List.getElem?_append_right (by simp [entries_length]; omega)]
              simp [entries_length, hin]
          · by_cases hik : i.1 < k.1
            · let i' : Fin k.1 := ⟨i.1, hik⟩
              have hc := ih k.1 (by omega) c' i'
              simp only [entry, entries, hsplit, dif_pos hik]
              rw [List.getElem?_append_left (by simp [entries_length, hik])]
              simpa [i'] using hc
            · by_cases heq : i.1 = k.1
              · simp only [entry, entries, hsplit, dif_neg hik, dif_pos heq]
                rw [List.getElem?_append_right (by simp [entries_length]; omega)]
                simp [entries_length, heq]
              · simp only [entry, entries, hsplit, dif_neg hik, dif_neg heq]
                have hsub : i.1 - c'.entries.length =
                    (i.1 - k.1 - 1) + 1 := by
                  simp [entries_length]
                  omega
                have hidx : i.1 - k.1 - 1 < n - k.1 := by omega
                rw [List.getElem?_append_right (by simp [entries_length]; omega)]
                conv_lhs => rw [hsub]
                rw [List.getElem?_cons_succ, List.getElem?_ofFn, dif_pos hidx]

/-- The decoded sum of entries is exactly the normal-form inversion weight. -/
theorem sequenceInversionWeight_toRestricted {n : ℕ} (c : AvoidingCode n) :
    sequenceInversionWeight (toRestricted c).1 = c.inversionWeight := by
  rw [sequenceInversionWeight]
  have hlist : List.ofFn c.entry = c.entries := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < n
    · let j : Fin n := ⟨i, hi⟩
      have hj := entries_getElem?_eq_entry c j
      simpa [j, hi] using hj.symm
    · simp [entries_length, hi]
  calc
    (∑ i, c.entry i) = (List.ofFn c.entry).sum := by simp [List.sum_ofFn]
    _ = c.entries.sum := congrArg List.sum hlist
    _ = c.inversionWeight := entries_sum_eq_inversionWeight c

/-- Appending a final zero creates no new rise. -/
theorem riseSet_fold_inl {n : ℕ} (c : AvoidingCode n) :
    riseSet (fold (Sum.inl c) : AvoidingCode (n + 1)).entry =
      (riseSet c.entry).map Fin.castSuccEmb := by
  classical
  ext i
  simp only [mem_riseSet, Finset.mem_map]
  constructor
  · rintro ⟨j, hij, hrij⟩
    have hi : i.1 < n := by
      change j.1 = i.1 + 1 at hij
      omega
    have hj : j.1 < n := by
      by_contra hj
      have hjlast : j = Fin.last n := Fin.ext (by simp; omega)
      have hjzero : entry (fold (Sum.inl c) : AvoidingCode (n + 1)) j = 0 := by
        rw [hjlast]
        exact entry_fold_inl_last c
      omega
    let i' : Fin n := ⟨i.1, hi⟩
    let j' : Fin n := ⟨j.1, hj⟩
    refine ⟨i', ?_, Fin.ext rfl⟩
    refine ⟨j', (by exact hij), ?_⟩
    have hiEq : i'.castSucc = i := Fin.ext rfl
    have hjEq : j'.castSucc = j := Fin.ext rfl
    rw [← hiEq, ← hjEq] at hrij
    simpa using hrij
  · rintro ⟨i', ⟨j', hij, hrij⟩, hi⟩
    subst i
    refine ⟨j'.castSucc, (by exact hij), ?_⟩
    simpa using hrij

/-- Embed the prefix before a chosen last-zero position. -/
def prefixEmbedding {n : ℕ} (k : Fin n) : Fin k.1 ↪ Fin (n + 1) where
  toFun i := ⟨i.1, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    simpa using congrArg Fin.val h

/-- The last-zero position as an index of the full sequence. -/
def boundaryIndex {n : ℕ} (k : Fin n) : Fin (n + 1) := ⟨k.1, by omega⟩

/-- A non-final normal form has precisely the prefix rises plus its last zero. -/
theorem riseSet_fold_inr {n : ℕ} (k : Fin n) (c : AvoidingCode k.1)
    (p : RectanglePartition (n - k.1) k.1) :
    riseSet (fold (Sum.inr ⟨k, c, p⟩) : AvoidingCode (n + 1)).entry =
      (riseSet c.entry).map (prefixEmbedding k) ∪ {boundaryIndex k} := by
  classical
  ext i
  simp only [mem_riseSet, Finset.mem_union, Finset.mem_map, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hij, hrij⟩
    have hzero : entry (fold (Sum.inr ⟨k, c, p⟩) : AvoidingCode (n + 1)) i = 0 :=
      entry_risesOnlyFromZero _ hij hrij
    by_cases hik : i.1 < k.1
    · have hjk : j.1 < k.1 := by
        by_contra hjk
        have hjEq : j.1 = k.1 := by
          change j.1 = i.1 + 1 at hij
          omega
        have hjzero : entry (fold (Sum.inr ⟨k, c, p⟩) :
            AvoidingCode (n + 1)) j = 0 := by
          simp [entry, hjEq]
        omega
      left
      let i' : Fin k.1 := ⟨i.1, hik⟩
      let j' : Fin k.1 := ⟨j.1, hjk⟩
      refine ⟨i', ?_, Fin.ext rfl⟩
      refine ⟨j', (by exact hij), ?_⟩
      simpa [entry, i', j', hik, hjk] using hrij
    · right
      have hieq : i.1 = k.1 := by
        by_contra hne
        have hki : k.1 < i.1 := by omega
        have hpos : 0 < entry (fold (Sum.inr ⟨k, c, p⟩) :
            AvoidingCode (n + 1)) i := by
          simp [entry, hik, hne]
        omega
      exact Fin.ext hieq
  · rintro (⟨i', ⟨j', hij, hrij⟩, hi⟩ | hi)
    · subst i
      refine ⟨prefixEmbedding k j', (by exact hij), ?_⟩
      simp only [entry, split_fold]
      have hiLt : (prefixEmbedding k i').1 < k.1 := by
        simpa [prefixEmbedding] using i'.2
      have hjLt : (prefixEmbedding k j').1 < k.1 := by
        simpa [prefixEmbedding] using j'.2
      rw [dif_pos hiLt, dif_pos hjLt]
      simpa [prefixEmbedding] using hrij
    · subst i
      let j : Fin (n + 1) := ⟨k.1 + 1, by omega⟩
      refine ⟨j, ?_, ?_⟩
      · rfl
      · have hknot : ¬ k.1 < k.1 := lt_irrefl _
        have hjnot : ¬ j.1 < k.1 := by simp [j]
        have hjne : ¬ j.1 = k.1 := by simp [j]
        simp [boundaryIndex, entry, hknot, hjnot, hjne, j]

/-- Cardinal form of `riseSet_fold_inr`. -/
theorem card_riseSet_fold_inr {n : ℕ} (k : Fin n) (c : AvoidingCode k.1)
    (p : RectanglePartition (n - k.1) k.1) :
    (riseSet (fold (Sum.inr ⟨k, c, p⟩) : AvoidingCode (n + 1)).entry).card =
      (riseSet c.entry).card + 1 := by
  classical
  rw [riseSet_fold_inr]
  rw [Finset.card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_singleton_right]
    intro hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hmem
    have := congrArg Fin.val hi
    simp [prefixEmbedding, boundaryIndex] at this
    omega

/-- The decoded rise count is exactly the normal-form descent weight. -/
theorem sequenceDescentWeight_toRestricted {n : ℕ} (c : AvoidingCode n) :
    sequenceDescentWeight (toRestricted c).1 = c.descentWeight := by
  change (riseSet c.entry).card = c.descentWeight
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [riseSet, descentWeight]
      | succ n =>
          rcases hsplit : split c with c' | ⟨k, c', p⟩
          · have cform : c = fold (Sum.inl c') := by
              calc
                c = fold (split c) := (fold_split c).symm
                _ = fold (Sum.inl c') := congrArg fold hsplit
            rw [cform, riseSet_fold_inl, Finset.card_map]
            simpa [descentWeight] using ih n (by omega) c'
          · have cform : c = fold (Sum.inr ⟨k, c', p⟩) := by
              calc
                c = fold (split c) := (fold_split c).symm
                _ = fold (Sum.inr ⟨k, c', p⟩) := congrArg fold hsplit
            rw [cform, card_riseSet_fold_inr]
            simpa [descentWeight] using ih k.1 (by omega) c'

end AvoidingCode

/-- The inversion-descent enumerator of avoiding codes. -/
noncomputable def inversionDescentEnumerator {R : Type*} [CommSemiring R]
    (q t : R) (n : ℕ) : R :=
  ∑ c : AvoidingCode n, q ^ c.inversionWeight * t ^ c.descentWeight

/-- Reindex the literal avoiding-sequence enumerator by the last-zero normal form. -/
theorem avoidingSequenceEnumerator_eq_inversionDescentEnumerator
    {R : Type*} [CommSemiring R] (q t : R) (n : ℕ) :
    avoidingSequenceEnumerator q t n = inversionDescentEnumerator q t n := by
  rw [avoidingSequenceEnumerator, inversionDescentEnumerator,
    ← (AvoidingCode.restrictedEquiv n).sum_comp]
  apply Fintype.sum_congr
  intro c
  simp only [AvoidingCode.restrictedEquiv_apply]
  rw [AvoidingCode.sequenceInversionWeight_toRestricted,
    AvoidingCode.sequenceDescentWeight_toRestricted]

@[simp]
theorem inversionDescentEnumerator_zero {R : Type*} [CommSemiring R] (q t : R) :
    inversionDescentEnumerator q t 0 = 1 := by
  simp [inversionDescentEnumerator, AvoidingCode, AvoidingCode.inversionWeight,
    AvoidingCode.descentWeight]

private theorem summand_split_inl {R : Type*} [CommSemiring R] (q t : R)
    {n : ℕ} (c : AvoidingCode n) :
    q ^ (AvoidingCode.fold (Sum.inl c) : AvoidingCode (n + 1)).inversionWeight *
        t ^ (AvoidingCode.fold (Sum.inl c) : AvoidingCode (n + 1)).descentWeight =
      q ^ c.inversionWeight * t ^ c.descentWeight := by
  simp [AvoidingCode.inversionWeight, AvoidingCode.descentWeight]

private theorem summand_split_inr {R : Type*} [CommSemiring R] (q t : R)
    {n : ℕ} (k : Fin n) (c : AvoidingCode k.1)
    (p : RectanglePartition (n - k.1) k.1) :
    q ^ (AvoidingCode.fold (Sum.inr ⟨k, c, p⟩) :
          AvoidingCode (n + 1)).inversionWeight *
        t ^ (AvoidingCode.fold (Sum.inr ⟨k, c, p⟩) :
          AvoidingCode (n + 1)).descentWeight =
      (t * q ^ (n - k.1)) *
        (q ^ p.weight * (q ^ c.inversionWeight * t ^ c.descentWeight)) := by
  simp only [AvoidingCode.inversionWeight, AvoidingCode.descentWeight,
    AvoidingCode.split_fold, pow_add, pow_one]
  ac_rfl

/--
Theorem 2.5, in the Lean-friendly indexing `N = n + 1`:

`I_(n+1) = I_n + sum_(k<n) t q^(n-k) [n choose k]_q I_k`.
-/
theorem inversionDescentEnumerator_succ {R : Type*} [CommSemiring R]
    (q t : R) (n : ℕ) :
    inversionDescentEnumerator q t (n + 1) =
      inversionDescentEnumerator q t n +
        ∑ k : Fin n, (t * q ^ (n - k.1)) *
          qBinomialEval q n k.1 * inversionDescentEnumerator q t k.1 := by
  rw [inversionDescentEnumerator, ← (AvoidingCode.splitEquiv n).symm.sum_comp]
  simp only [AvoidingCode.splitEquiv_symm_apply, Fintype.sum_sum_type, Fintype.sum_sigma,
    Fintype.sum_prod_type]
  congr 1
  · exact Fintype.sum_congr _ _ fun c ↦ summand_split_inl q t c
  · apply Fintype.sum_congr
    intro k
    rw [qBinomialEval_eq_rectangle q (Nat.le_of_lt k.isLt)]
    simp_rw [summand_split_inr q t k]
    simp only [inversionDescentEnumerator]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    calc
      (∑ x : RectanglePartition (n - k.1) k.1, (t * q ^ (n - k.1)) *
          (q ^ x.weight * (q ^ p.inversionWeight * t ^ p.descentWeight))) =
          ∑ x : RectanglePartition (n - k.1) k.1,
            ((t * q ^ (n - k.1)) * q ^ x.weight) *
            (q ^ p.inversionWeight * t ^ p.descentWeight) := by
              apply Fintype.sum_congr
              intro x
              ac_rfl
      _ = (∑ x : RectanglePartition (n - k.1) k.1,
          (t * q ^ (n - k.1)) * q ^ x.weight) *
          (q ^ p.inversionWeight * t ^ p.descentWeight) := by
            exact (Finset.sum_mul Finset.univ _ _).symm
      _ = ((t * q ^ (n - k.1)) *
          ∑ x : RectanglePartition (n - k.1) k.1, q ^ x.weight) *
          (q ^ p.inversionWeight * t ^ p.descentWeight) := by
            congr 1
            exact (Finset.mul_sum Finset.univ _ _).symm

/-- The paper's `n ≥ 1` indexing, with an explicit `Fin (n-1)` sum. -/
theorem theorem_2_5 {R : Type*} [CommSemiring R]
    (q t : R) {n : ℕ} (hn : 1 ≤ n) :
    inversionDescentEnumerator q t n =
      inversionDescentEnumerator q t (n - 1) +
        ∑ k : Fin (n - 1), (t * q ^ (n - k.1 - 1)) *
          qBinomialEval q (n - 1) k.1 * inversionDescentEnumerator q t k.1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [show m + 1 - 1 = m by omega, inversionDescentEnumerator_succ]
  congr 2
  funext k
  rw [show m + 1 - k.1 - 1 = m - k.1 by omega]

/-- Theorem 2.5 stated directly for the paper's literal avoiding inversion sequences. -/
theorem theorem_2_5_avoidingSequences {R : Type*} [CommSemiring R]
    (q t : R) {n : ℕ} (hn : 1 ≤ n) :
    avoidingSequenceEnumerator q t n =
      avoidingSequenceEnumerator q t (n - 1) +
        ∑ k : Fin (n - 1), (t * q ^ (n - k.1 - 1)) *
          qBinomialEval q (n - 1) k.1 * avoidingSequenceEnumerator q t k.1 := by
  simpa only [avoidingSequenceEnumerator_eq_inversionDescentEnumerator] using
    theorem_2_5 q t hn

end LeanCo
