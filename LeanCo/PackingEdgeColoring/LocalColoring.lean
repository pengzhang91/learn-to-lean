import LeanCo.PackingEdgeColoring.Defs

/-!
# Local calculus for `(1,2^k)` packing edge-colourings

The metric definition in `Defs` is convenient for stating the final theorem,
but extension arguments should not repeatedly reason about distances in a line
graph.  This file supplies an equivalent endpoint-local formulation and a
small calculus for restricting, patching, and recolouring colourings.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- A semantic colour for a `(1,2^k)` edge-colouring.  `none` is the single
matching colour; `some i` is the `i`-th induced-matching colour. -/
abbrev OneTwoColor (k : ℕ) := Option (Fin k)

/-- The canonical equivalence between the paper-facing `Fin (k+1)` encoding
and the semantic encoding used by local recolouring arguments. -/
def finEquivOneTwoColor (k : ℕ) : Fin (k + 1) ≃ OneTwoColor k :=
  finSuccEquiv k

@[simp] theorem finEquivOneTwoColor_zero (k : ℕ) :
    finEquivOneTwoColor k 0 = none := by
  simp [finEquivOneTwoColor]

@[simp] theorem finEquivOneTwoColor_succ {k : ℕ} (i : Fin k) :
    finEquivOneTwoColor k i.succ = some i := by
  simp [finEquivOneTwoColor]

/-- Two edges have no common endpoint. -/
def EndpointDisjoint (e f : G.edgeSet) : Prop :=
  ∀ v, v ∈ (e : Sym2 V) → v ∉ (f : Sym2 V)

/-- Some endpoint of `e` is adjacent in `G` to some endpoint of `f`. -/
def HasCrossEdge (e f : G.edgeSet) : Prop :=
  ∃ u, u ∈ (e : Sym2 V) ∧ ∃ v, v ∈ (f : Sym2 V) ∧ G.Adj u v

/-- The endpoint-local separation condition for two edges in the same
induced-matching colour class. -/
def InducedSeparated (e f : G.edgeSet) : Prop :=
  EndpointDisjoint G e f ∧ ¬ HasCrossEdge G e f

theorem endpointDisjoint_comm {e f : G.edgeSet} :
    EndpointDisjoint G e f ↔ EndpointDisjoint G f e := by
  simp only [EndpointDisjoint]
  constructor
  · intro h v hvf hve
    exact h v hve hvf
  · intro h v hve hvf
    exact h v hvf hve

theorem hasCrossEdge_comm {e f : G.edgeSet} :
    HasCrossEdge G e f ↔ HasCrossEdge G f e := by
  constructor
  · rintro ⟨u, hue, v, hvf, huv⟩
    exact ⟨v, hvf, u, hue, huv.symm⟩
  · rintro ⟨v, hvf, u, hue, hvu⟩
    exact ⟨u, hue, v, hvf, hvu.symm⟩

theorem inducedSeparated_comm {e f : G.edgeSet} :
    InducedSeparated G e f ↔ InducedSeparated G f e := by
  rw [InducedSeparated, InducedSeparated, endpointDisjoint_comm,
    hasCrossEdge_comm]

theorem inducedSeparated_iff_forall_endpoints {e f : G.edgeSet} :
    InducedSeparated G e f ↔
      ∀ u, u ∈ (e : Sym2 V) → ∀ v, v ∈ (f : Sym2 V) →
        u ≠ v ∧ ¬ G.Adj u v := by
  constructor
  · rintro ⟨hdisj, hcross⟩ u hue v hvf
    constructor
    · intro huv
      subst v
      exact hdisj u hue hvf
    · intro huv
      exact hcross ⟨u, hue, v, hvf, huv⟩
  · intro h
    constructor
    · intro v hve hvf
      exact (h v hve v hvf).1 rfl
    · rintro ⟨u, hue, v, hvf, huv⟩
      exact (h u hue v hvf).2 huv

theorem endpointDisjoint_iff_not_lineGraph_adj {e f : G.edgeSet}
    (hef : e ≠ f) :
    EndpointDisjoint G e f ↔ ¬ G.lineGraph.Adj e f := by
  rw [lineGraph_adj_iff_exists]
  simp only [EndpointDisjoint]
  aesop

/-- A common line-graph neighbour is exactly a cross-edge once the two
original edges have disjoint endpoints. -/
theorem commonNeighbors_nonempty_iff_hasCrossEdge {e f : G.edgeSet}
    (hdisj : EndpointDisjoint G e f) :
    (G.lineGraph.commonNeighbors e f).Nonempty ↔ HasCrossEdge G e f := by
  constructor
  · rintro ⟨g, hg⟩
    rw [mem_commonNeighbors] at hg
    rw [lineGraph_adj_iff_exists] at hg
    rcases hg with ⟨⟨_, u, hue, hug⟩, ⟨_, v, hvf, hvg⟩⟩
    refine ⟨u, hue, v, hvf, ?_⟩
    by_cases huv : u = v
    · subst v
      exact False.elim (hdisj u hue hvf)
    · exact G.adj_of_mem_incidenceSet huv
        (G.edge_mem_incidenceSet_iff.mpr hug)
        (G.edge_mem_incidenceSet_iff.mpr hvg)
  · rintro ⟨u, hue, v, hvf, huv⟩
    let g : G.edgeSet := ⟨s(u, v), huv⟩
    have hge : g ≠ e := by
      intro h
      have hvg : v ∈ (g : Sym2 V) := Sym2.mem_mk_right u v
      rw [h] at hvg
      exact hdisj v hvg hvf
    have hgf : g ≠ f := by
      intro h
      have hug : u ∈ (g : Sym2 V) := Sym2.mem_mk_left u v
      rw [h] at hug
      exact hdisj u hue hug
    refine ⟨g, ?_⟩
    rw [mem_commonNeighbors]
    constructor
    · rw [lineGraph_adj_iff_exists]
      exact ⟨hge.symm, u, hue, Sym2.mem_mk_left u v⟩
    · rw [lineGraph_adj_iff_exists]
      exact ⟨hgf.symm, v, hvf, Sym2.mem_mk_right u v⟩

theorem endpointDisjoint_iff_two_le_edist {e f : G.edgeSet} (hef : e ≠ f) :
    EndpointDisjoint G e f ↔ (2 : ℕ∞) ≤ G.lineGraph.edist e f := by
  rw [endpointDisjoint_iff_not_lineGraph_adj G hef, ← edist_eq_one_iff_adj]
  have hpos : (0 : ℕ∞) < G.lineGraph.edist e f := edist_pos_of_ne hef
  change (G.lineGraph.edist e f ≠ 1) ↔ (1 : ℕ∞) + 1 ≤ G.lineGraph.edist e f
  rw [ENat.add_one_le_iff ENat.one_ne_top]
  constructor
  · intro hne
    exact lt_of_le_of_ne (Order.one_le_iff_pos.mpr hpos) (Ne.symm hne)
  · exact ne_of_gt

theorem inducedSeparated_iff_three_le_edist {e f : G.edgeSet} (hef : e ≠ f) :
    InducedSeparated G e f ↔ (3 : ℕ∞) ≤ G.lineGraph.edist e f := by
  change InducedSeparated G e f ↔ (2 : ℕ∞) + 1 ≤ G.lineGraph.edist e f
  rw [ENat.add_one_le_iff (by norm_num : (2 : ℕ∞) ≠ ⊤)]
  rw [G.lineGraph.two_lt_edist_iff]
  constructor
  · rintro ⟨hdisj, hcross⟩
    refine ⟨hef, (endpointDisjoint_iff_not_lineGraph_adj G hef).mp hdisj, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro g hg
    exact hcross ((commonNeighbors_nonempty_iff_hasCrossEdge G hdisj).mp ⟨g, hg⟩)
  · rintro ⟨_, hadj, hcommon⟩
    have hdisj := (endpointDisjoint_iff_not_lineGraph_adj G hef).mpr hadj
    refine ⟨hdisj, ?_⟩
    rw [← commonNeighbors_nonempty_iff_hasCrossEdge G hdisj]
    simp [hcommon]

/-- Pairwise compatibility of two coloured edges, expressed entirely using
endpoints of the original graph. -/
def PairCompatible {k : ℕ} (e f : G.edgeSet)
    (a b : OneTwoColor k) : Prop :=
  a ≠ b ∨ match a with
    | none => EndpointDisjoint G e f
    | some _ => InducedSeparated G e f

@[simp] theorem pairCompatible_none_none {k : ℕ} {e f : G.edgeSet} :
    PairCompatible G e f (none : OneTwoColor k) none ↔ EndpointDisjoint G e f := by
  simp [PairCompatible]

@[simp] theorem pairCompatible_some_self {k : ℕ} {e f : G.edgeSet} (i : Fin k) :
    PairCompatible G e f (some i) (some i) ↔ InducedSeparated G e f := by
  simp [PairCompatible]

theorem pairCompatible_of_ne {k : ℕ} {e f : G.edgeSet}
    {a b : OneTwoColor k} (hab : a ≠ b) : PairCompatible G e f a b :=
  Or.inl hab

theorem pairCompatible_comm {k : ℕ} {e f : G.edgeSet}
    {a b : OneTwoColor k} :
    PairCompatible G e f a b ↔ PairCompatible G f e b a := by
  by_cases hab : a = b
  · subst b
    cases a with
    | none => simp [PairCompatible, endpointDisjoint_comm]
    | some i => simp [PairCompatible, inducedSeparated_comm]
  · have hba : b ≠ a := Ne.symm hab
    simp [PairCompatible, hab, hba]

/-- For a single `Fin (k+1)` colour, endpoint compatibility is exactly the
separation required by its radius.  This is the bridge between the local and
metric presentations. -/
theorem pairCompatible_fin_self_iff_edist {k : ℕ} {e f : G.edgeSet}
    (hef : e ≠ f) (i : Fin (k + 1)) :
    PairCompatible G e f (finEquivOneTwoColor k i) (finEquivOneTwoColor k i) ↔
      (((oneTwoRadius k i + 1 : ℕ) : ℕ∞) ≤ G.lineGraph.edist e f) := by
  by_cases hi : i = 0
  · subst i
    simpa [PairCompatible] using endpointDisjoint_iff_two_le_edist G hef
  · generalize hc : finEquivOneTwoColor k i = c
    cases c with
    | none =>
        exfalso
        apply hi
        apply (finEquivOneTwoColor k).injective
        exact hc.trans (finEquivOneTwoColor_zero k).symm
    | some j =>
        simpa [PairCompatible, hc, oneTwoRadius_ne_zero hi] using
          inducedSeparated_iff_three_le_edist G hef

/-- A semantic colouring is valid on a set `D` of currently coloured edges.
This is the form used by deletion-and-extension proofs. -/
def IsOneTwoColoringOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) : Prop :=
  ∀ e, e ∈ D → ∀ f, f ∈ D → e ≠ f →
    PairCompatible G e f (colour e) (colour f)

/-- A total semantic `(1,2^k)` colouring. -/
def IsOneTwoColoring {k : ℕ} (colour : G.edgeSet → OneTwoColor k) : Prop :=
  IsOneTwoColoringOn G Set.univ colour

/-- Fully expanded colour-class characterization.  It is often the most
convenient introduction rule in local extension arguments. -/
theorem isOneTwoColoringOn_iff_colourClasses {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k) :
    IsOneTwoColoringOn G D colour ↔
      (∀ e, e ∈ D → ∀ f, f ∈ D → e ≠ f →
        colour e = none → colour f = none → EndpointDisjoint G e f) ∧
      (∀ i : Fin k, ∀ e, e ∈ D → ∀ f, f ∈ D → e ≠ f →
        colour e = some i → colour f = some i → InducedSeparated G e f) := by
  constructor
  · intro h
    constructor
    · intro e he f hf hef hce hcf
      simpa [hce, hcf] using h e he f hf hef
    · intro i e he f hf hef hce hcf
      simpa [hce, hcf] using h e he f hf hef
  · rintro ⟨hmatch, hinduced⟩ e he f hf hef
    cases hce : colour e with
    | none =>
        cases hcf : colour f with
        | none =>
            simpa [hce, hcf] using hmatch e he f hf hef hce hcf
        | some j =>
            exact pairCompatible_of_ne G (by simp)
    | some i =>
        cases hcf : colour f with
        | none =>
            exact pairCompatible_of_ne G (by simp)
        | some j =>
            by_cases hij : i = j
            · subst j
              simpa [hce, hcf] using hinduced i e he f hf hef hce hcf
            · exact pairCompatible_of_ne G (by simp [hij])

theorem isOneTwoColoring_iff_isPackingEdgeColoring {k : ℕ}
    (colour : G.edgeSet → Fin (k + 1)) :
    IsOneTwoColoring G (fun e => finEquivOneTwoColor k (colour e)) ↔
      IsPackingEdgeColoring G (oneTwoRadius k) colour := by
  constructor
  · intro h e f hef hc
    have hp := h e (by simp) f (by simp) hef
    apply (pairCompatible_fin_self_iff_edist G hef (colour e)).mp
    simpa [hc] using hp
  · intro h e _ f _ hef
    by_cases hc : colour e = colour f
    · have hd := h e f hef hc
      have hp := (pairCompatible_fin_self_iff_edist G hef (colour e)).mpr hd
      simpa [hc] using hp
    · left
      exact fun heq => hc ((finEquivOneTwoColor k).injective heq)

/-- Existence is unchanged when passing from the original `Fin (k+1)`
encoding to semantic colours. -/
theorem hasOneTwoPackingEdgeColoring_iff_exists_local (k : ℕ) :
    HasOneTwoPackingEdgeColoring G k ↔
      ∃ colour : G.edgeSet → OneTwoColor k, IsOneTwoColoring G colour := by
  constructor
  · rintro ⟨colour, hcolour⟩
    exact ⟨fun e => finEquivOneTwoColor k (colour e),
      (isOneTwoColoring_iff_isPackingEdgeColoring G colour).mpr hcolour⟩
  · rintro ⟨colour, hcolour⟩
    let encoded : G.edgeSet → Fin (k + 1) :=
      fun e => (finEquivOneTwoColor k).symm (colour e)
    refine ⟨encoded, (isOneTwoColoring_iff_isPackingEdgeColoring G encoded).mp ?_⟩
    simpa [encoded] using hcolour

/-! ## Restriction, patching, and recolouring -/

/-- Restrict a total colour assignment to a set of edges. -/
def restrictColoring {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) : D → OneTwoColor k :=
  fun e => colour e

@[simp] theorem restrictColoring_apply {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : D) :
    restrictColoring G D colour e = colour e := rfl

/-- Validity for a genuinely restricted assignment whose edge type is the
subtype `D`. -/
def IsRestrictedOneTwoColoring {k : ℕ} (D : Set G.edgeSet)
    (colour : D → OneTwoColor k) : Prop :=
  ∀ e f : D, e ≠ f →
    PairCompatible G e.1 f.1 (colour e) (colour f)

theorem isRestrictedOneTwoColoring_restrict_iff {k : ℕ}
    (D : Set G.edgeSet) (colour : G.edgeSet → OneTwoColor k) :
    IsRestrictedOneTwoColoring G D (restrictColoring G D colour) ↔
      IsOneTwoColoringOn G D colour := by
  constructor
  · intro h e he f hf hef
    apply h ⟨e, he⟩ ⟨f, hf⟩
    intro hEq
    exact hef (congrArg Subtype.val hEq)
  · intro h e f hef
    apply h e e.2 f f.2
    intro hEq
    exact hef (Subtype.ext hEq)

theorem IsOneTwoColoringOn.mono {k : ℕ} {D E : Set G.edgeSet}
    {colour : G.edgeSet → OneTwoColor k}
    (h : IsOneTwoColoringOn G D colour) (hED : E ⊆ D) :
    IsOneTwoColoringOn G E colour := by
  intro e he f hf hef
  exact h e (hED he) f (hED hf) hef

theorem isOneTwoColoring_iff_on_univ {k : ℕ}
    {colour : G.edgeSet → OneTwoColor k} :
    IsOneTwoColoring G colour ↔ IsOneTwoColoringOn G Set.univ colour :=
  Iff.rfl

/-- Replace a colour assignment on `S`, leaving it unchanged off `S`. -/
def patchColoring {k : ℕ} (S : Set G.edgeSet) [DecidablePred (· ∈ S)]
    (old new : G.edgeSet → OneTwoColor k) : G.edgeSet → OneTwoColor k :=
  fun e => if e ∈ S then new e else old e

@[simp] theorem patchColoring_of_mem {k : ℕ} {S : Set G.edgeSet}
    [DecidablePred (· ∈ S)] {old new : G.edgeSet → OneTwoColor k}
    {e : G.edgeSet} (he : e ∈ S) :
    patchColoring G S old new e = new e := by
  simp [patchColoring, he]

@[simp] theorem patchColoring_of_not_mem {k : ℕ} {S : Set G.edgeSet}
    [DecidablePred (· ∈ S)] {old new : G.edgeSet → OneTwoColor k}
    {e : G.edgeSet} (he : e ∉ S) :
    patchColoring G S old new e = old e := by
  simp [patchColoring, he]

/-- The only new obligations made by replacing colours on `S`: a newly
coloured edge in `S` must be compatible with every unchanged edge outside
`S`.  Internal obligations are tracked separately by
`IsOneTwoColoringOn`. -/
def PatchCrossCompatible {k : ℕ} (D S : Set G.edgeSet)
    (old new : G.edgeSet → OneTwoColor k) : Prop :=
  ∀ e, e ∈ D → e ∈ S → ∀ f, f ∈ D → f ∉ S →
    PairCompatible G e f (new e) (old f)

/-- Exact locality theorem for a patch. -/
theorem isOneTwoColoringOn_patch_iff {k : ℕ} (D S : Set G.edgeSet)
    [DecidablePred (· ∈ S)] (old new : G.edgeSet → OneTwoColor k) :
    IsOneTwoColoringOn G D (patchColoring G S old new) ↔
      IsOneTwoColoringOn G (D \ S) old ∧
      IsOneTwoColoringOn G (D ∩ S) new ∧
      PatchCrossCompatible G D S old new := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro e he f hf hef
      simpa [patchColoring, he.2, hf.2] using h e he.1 f hf.1 hef
    · intro e he f hf hef
      simpa [patchColoring, he.2, hf.2] using h e he.1 f hf.1 hef
    · intro e heD heS f hfD hfS
      have hef : e ≠ f := fun hEq => hfS (hEq ▸ heS)
      simpa [patchColoring, heS, hfS] using h e heD f hfD hef
  · rintro ⟨hOld, hNew, hCross⟩ e heD f hfD hef
    by_cases heS : e ∈ S
    · by_cases hfS : f ∈ S
      · simpa [patchColoring, heS, hfS] using
          hNew e ⟨heD, heS⟩ f ⟨hfD, hfS⟩ hef
      · simpa [patchColoring, heS, hfS] using hCross e heD heS f hfD hfS
    · by_cases hfS : f ∈ S
      · have hfe := hCross f hfD hfS e heD heS
        have hp := (pairCompatible_comm G).mpr hfe
        simpa [patchColoring, heS, hfS] using hp
      · simpa [patchColoring, heS, hfS] using
          hOld e ⟨heD, heS⟩ f ⟨hfD, hfS⟩ hef

/-- A convenient sufficient form of the patch locality theorem. -/
theorem IsOneTwoColoringOn.patch {k : ℕ} {D S : Set G.edgeSet}
    [DecidablePred (· ∈ S)] {old new : G.edgeSet → OneTwoColor k}
    (hOld : IsOneTwoColoringOn G (D \ S) old)
    (hNew : IsOneTwoColoringOn G (D ∩ S) new)
    (hCross : PatchCrossCompatible G D S old new) :
    IsOneTwoColoringOn G D (patchColoring G S old new) :=
  (isOneTwoColoringOn_patch_iff G D S old new).mpr ⟨hOld, hNew, hCross⟩

/-- Recolour one edge. -/
def recolor {k : ℕ} [DecidableEq G.edgeSet]
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (a : OneTwoColor k) : G.edgeSet → OneTwoColor k :=
  Function.update colour e a

@[simp] theorem recolor_eq {k : ℕ} [DecidableEq G.edgeSet]
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (a : OneTwoColor k) : recolor G colour e a e = a := by
  simp [recolor]

@[simp] theorem recolor_ne {k : ℕ} [DecidableEq G.edgeSet]
    (colour : G.edgeSet → OneTwoColor k) {e f : G.edgeSet}
    (a : OneTwoColor k) (hfe : f ≠ e) :
    recolor G colour e a f = colour f := by
  simp [recolor, hfe]

/-- A colour `a` can be put on `e` relative to `D` if it is compatible with
every other currently relevant edge. -/
def ColorAvailableOn {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet)
    (a : OneTwoColor k) : Prop :=
  ∀ f, f ∈ D → f ≠ e → PairCompatible G e f a (colour f)

theorem colorAvailableOn_none_iff {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) :
    ColorAvailableOn G D colour e none ↔
      ∀ f, f ∈ D → f ≠ e → colour f = none →
        EndpointDisjoint G e f := by
  constructor
  · intro h f hf hfe hcf
    simpa [hcf] using h f hf hfe
  · intro h f hf hfe
    cases hcf : colour f with
    | none => simpa [hcf] using h f hf hfe hcf
    | some i => exact pairCompatible_of_ne G (by simp)

theorem colorAvailableOn_some_iff {k : ℕ} (D : Set G.edgeSet)
    (colour : G.edgeSet → OneTwoColor k) (e : G.edgeSet) (i : Fin k) :
    ColorAvailableOn G D colour e (some i) ↔
      ∀ f, f ∈ D → f ≠ e → colour f = some i →
        InducedSeparated G e f := by
  constructor
  · intro h f hf hfe hcf
    simpa [hcf] using h f hf hfe
  · intro h f hf hfe
    cases hcf : colour f with
    | none => exact pairCompatible_of_ne G (by simp)
    | some j =>
        by_cases hij : j = i
        · subst j
          simpa [hcf] using h f hf hfe hcf
        · exact pairCompatible_of_ne G (by simp [Ne.symm hij])

/-- Exact locality theorem for recolouring one edge. -/
theorem isOneTwoColoringOn_recolor_iff {k : ℕ} [DecidableEq G.edgeSet]
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor k}
    {e : G.edgeSet} {a : OneTwoColor k} (heD : e ∈ D) :
    IsOneTwoColoringOn G D (recolor G colour e a) ↔
      IsOneTwoColoringOn G (D \ {e}) colour ∧
      ColorAvailableOn G D colour e a := by
  constructor
  · intro h
    constructor
    · intro x hx y hy hxy
      have hxe : x ≠ e := by simpa using hx.2
      have hye : y ≠ e := by simpa using hy.2
      simpa [recolor, hxe, hye] using h x hx.1 y hy.1 hxy
    · intro f hfD hfe
      simpa [recolor, hfe] using h e heD f hfD hfe.symm
  · rintro ⟨hOld, hAvail⟩ x hxD y hyD hxy
    by_cases hxe : x = e
    · subst x
      simpa [recolor, hxy, hxy.symm] using hAvail y hyD hxy.symm
    · by_cases hye : y = e
      · subst y
        have hp := hAvail x hxD hxe
        have hp' := (pairCompatible_comm G).mpr hp
        simpa [recolor, hxe] using hp'
      · simpa [recolor, hxe, hye] using
          hOld x ⟨hxD, by simpa using hxe⟩ y ⟨hyD, by simpa using hye⟩ hxy

/-- Extend a valid colouring from `D` to one fresh edge. -/
theorem IsOneTwoColoringOn.extend_one {k : ℕ} [DecidableEq G.edgeSet]
    {D : Set G.edgeSet} {colour : G.edgeSet → OneTwoColor k}
    {e : G.edgeSet} {a : OneTwoColor k}
    (h : IsOneTwoColoringOn G D colour) (he : e ∉ D)
    (ha : ColorAvailableOn G D colour e a) :
    IsOneTwoColoringOn G (insert e D) (recolor G colour e a) := by
  apply (isOneTwoColoringOn_recolor_iff G (D := insert e D)
    (colour := colour) (e := e) (a := a) (by simp)).mpr
  constructor
  · apply h.mono
    intro f hf
    rcases hf with ⟨hfIns, hfne⟩
    rcases hfIns with (rfl | hfD)
    · exact False.elim (hfne (by simp))
    · exact hfD
  · intro f hf hfe
    rcases hf with (rfl | hfD)
    · exact False.elim (hfe rfl)
    · exact ha f hfD hfe

end

end LeanCo.PackingEdgeColoring
