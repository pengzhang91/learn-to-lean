import LeanCo.PackingEdgeColoring.LocalColoring

/-!
# A kernel-verified backtracking checker for small packing-colouring obstructions

This is not an oracle: the recursive Boolean search is proved complete with
respect to `IsOneTwoColoring`.  Concrete finite counterexamples may therefore
be discharged by reducing a false search result in the Lean kernel, while
pruning incompatible partial assignments instead of enumerating every total
function.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Computable reflection of pair compatibility. -/
def pairCompatibleBool {k : ℕ} (e f : G.edgeSet)
    (a b : OneTwoColor k) : Bool := by
  cases a with
  | none =>
      cases b with
      | none =>
          letI : Decidable (EndpointDisjoint G e f) :=
            Fintype.decidableForallFintype
          exact decide (EndpointDisjoint G e f)
      | some _ => exact true
  | some i =>
      cases b with
      | none => exact true
      | some j =>
          by_cases hij : i = j
          · subst j
            letI : Decidable (EndpointDisjoint G e f) :=
              Fintype.decidableForallFintype
            letI : Decidable (HasCrossEdge G e f) :=
              Fintype.decidableExistsFintype
            exact decide
              (EndpointDisjoint G e f ∧ ¬ HasCrossEdge G e f)
          · exact true

@[simp] theorem pairCompatibleBool_eq_true_iff {k : ℕ}
    (e f : G.edgeSet) (a b : OneTwoColor k) :
    pairCompatibleBool G e f a b = true ↔ PairCompatible G e f a b := by
  cases a with
  | none => cases b <;> simp [pairCompatibleBool, PairCompatible]
  | some i =>
      cases b with
      | none => simp [pairCompatibleBool, PairCompatible]
      | some j =>
          by_cases hij : i = j <;>
            simp [pairCompatibleBool, PairCompatible, InducedSeparated, hij]

/-- A computable list containing every semantic colour exactly once. -/
def oneTwoColorList (k : ℕ) : List (OneTwoColor k) :=
  none :: List.ofFn fun i : Fin k ↦ some i

@[simp] theorem mem_oneTwoColorList {k : ℕ} (a : OneTwoColor k) :
    a ∈ oneTwoColorList k := by
  cases a with
  | none => simp [oneTwoColorList]
  | some i => simp [oneTwoColorList]

/-- Check a proposed colour against a partial association list.  Repeated
edges are ignored; concrete search lists need not carry a no-duplicates proof. -/
def compatibleWith {k : ℕ} (e : G.edgeSet) (a : OneTwoColor k) :
    List (G.edgeSet × OneTwoColor k) → Bool
  | [] => true
  | (f, b) :: rest =>
      (if f = e then true else pairCompatibleBool G e f a b) &&
        compatibleWith e a rest

/-- Depth-first search with immediate pairwise-conflict pruning. -/
def packingColorSearch {k : ℕ} :
    List G.edgeSet → List (G.edgeSet × OneTwoColor k) → Bool
  | [], _ => true
  | e :: rest, assigned =>
      (oneTwoColorList k).any fun a ↦
        compatibleWith G e a assigned &&
          packingColorSearch rest ((e, a) :: assigned)

/-- A genuine total colouring passes every compatibility check against entries
of the association list that record its colours. -/
theorem compatibleWith_eq_true_of_coloring {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k}
    (hcolour : IsOneTwoColoring G colour) (e : G.edgeSet)
    (assigned : List (G.edgeSet × OneTwoColor k))
    (hassigned : ∀ p ∈ assigned, p.2 = colour p.1) :
    compatibleWith G e (colour e) assigned = true := by
  induction assigned with
  | nil => rfl
  | cons p rest ih =>
      simp only [compatibleWith, Bool.and_eq_true]
      constructor
      · by_cases hpe : p.1 = e
        · simp [hpe]
        · rw [if_neg hpe, pairCompatibleBool_eq_true_iff]
          have hpcolour : p.2 = colour p.1 := hassigned p (by simp)
          rw [hpcolour]
          exact hcolour e (by simp) p.1 (by simp) (fun h ↦ hpe h.symm)
      · apply ih
        intro q hq
        exact hassigned q (by simp [hq])

/-- Completeness of the pruned search: every semantic packing colouring gives
a successful branch, for every chosen list of edges. -/
theorem packingColorSearch_eq_true_of_coloring {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k}
    (hcolour : IsOneTwoColoring G colour)
    (edges : List G.edgeSet)
    (assigned : List (G.edgeSet × OneTwoColor k))
    (hassigned : ∀ p ∈ assigned, p.2 = colour p.1) :
    packingColorSearch G edges assigned = true := by
  induction edges generalizing assigned with
  | nil => rfl
  | cons e rest ih =>
      simp only [packingColorSearch, List.any_eq_true]
      refine ⟨colour e, ?_, ?_⟩
      · simp
      · rw [Bool.and_eq_true]
        constructor
        · exact compatibleWith_eq_true_of_coloring G hcolour e assigned hassigned
        · apply ih ((e, colour e) :: assigned)
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · rfl
          · exact hassigned p hp

/-- A kernel-reduced false result refutes every semantic colouring. -/
theorem not_exists_isOneTwoColoring_of_search_eq_false {k : ℕ}
    (edges : List G.edgeSet)
    (hfalse : packingColorSearch G (k := k) edges [] = false) :
    ¬ ∃ colour : G.edgeSet → OneTwoColor k, IsOneTwoColoring G colour := by
  rintro ⟨colour, hcolour⟩
  have htrue := packingColorSearch_eq_true_of_coloring G hcolour edges []
    (by simp)
  rw [hfalse] at htrue
  contradiction

end

end LeanCo.PackingEdgeColoring
