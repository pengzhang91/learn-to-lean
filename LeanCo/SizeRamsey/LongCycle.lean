import LeanCo.SizeRamsey.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Long cycles forced by vertex expansion

This file formalises the long-cycle lemma used as Lemma 3.1 in the paper.  We
use external neighbourhoods, so vertices of the tested set itself are removed
from the union of their neighbourhoods.
-/

open scoped SimpleGraph

namespace LeanCo.SizeRamsey

open Finset SimpleGraph

universe u

variable {V : Type u}

private theorem tail_map_eq {A B : Type*} (f : A → B) (l : List A) :
    (l.map f).tail = l.tail.map f := by
  cases l <;> rfl

/-- The external neighbourhood of a finite vertex set. -/
def externalNeighborhood [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (X : Finset V) : Finset V :=
  Finset.univ.filter fun y ↦ y ∉ X ∧ ∃ x ∈ X, G.Adj x y

@[simp]
theorem mem_externalNeighborhood [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (y : V) :
    y ∈ externalNeighborhood G X ↔ y ∉ X ∧ ∃ x ∈ X, G.Adj x y := by
  simp [externalNeighborhood]

private theorem exists_root_adjacent_component [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.Connected) (root : V)
    (C : (G.induce ({root}ᶜ : Set V)).ConnectedComponent) :
    ∃ s : C, G.Adj root s.1.1 := by
  classical
  obtain ⟨x, hxC⟩ := C.nonempty_supp
  obtain ⟨p, hp⟩ := hG.exists_isPath root x.1
  have hxroot : x.1 ≠ root := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
  have hrootx : root ≠ x.1 := hxroot.symm
  have hp_nonNil : ¬ p.Nil := by
    intro hnil
    exact hrootx (hp.nil_iff_eq.mp hnil)
  have hadj : G.Adj root p.snd := p.adj_snd hp_nonNil
  have hsne : p.snd ≠ root := hadj.ne.symm
  let s : ↑({root}ᶜ : Set V) := ⟨p.snd, by simpa using hsne⟩
  have hroot_tail : root ∉ p.support.tail := by
    have hnodup := hp.support_nodup
    rw [← p.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have htail : ∀ z ∈ p.tail.support, z ∈ ({root}ᶜ : Set V) := by
    intro z hz
    rw [p.support_tail_of_not_nil hp_nonNil] at hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hzroot
    subst z
    exact hroot_tail hz
  let q := p.tail.induce ({root}ᶜ : Set V) htail
  have hreach : (G.induce ({root}ᶜ : Set V)).Reachable s x := by
    exact ⟨q.copy (by rfl) (by rfl)⟩
  have hsC : s ∈ C.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    rw [ConnectedComponent.sound hreach]
    exact (ConnectedComponent.mem_supp_iff C x).mp hxC
  exact ⟨⟨s, hsC⟩, hadj⟩

/-- A finite family of nonnegative integer weights whose total is at least
`a` has a subfamily with total between `a / 2` and `a`.  The doubled lower
bound is the division-free form needed below. -/
private theorem exists_subset_sum_half_le
    {I : Type*} [DecidableEq I] (s : Finset I) (w : I → ℕ) {a : ℕ}
    (ha : 0 < a) (hw : ∀ i ∈ s, w i ≤ a) (hsum : a ≤ ∑ i ∈ s, w i) :
    ∃ u ⊆ s, a ≤ 2 * ∑ i ∈ u, w i ∧ ∑ i ∈ u, w i ≤ a := by
  classical
  by_cases hlarge : ∃ i ∈ s, a ≤ 2 * w i
  · obtain ⟨i, his, hi⟩ := hlarge
    exact ⟨{i}, Finset.singleton_subset_iff.mpr his, by simpa using hi, by simpa using hw i his⟩
  · push Not at hlarge
    let good : Finset (Finset I) :=
      s.powerset.filter fun u ↦ a ≤ 2 * ∑ i ∈ u, w i
    have hsgood : s ∈ good := by
      simp only [good, Finset.mem_filter, Finset.mem_powerset, subset_rfl, true_and]
      omega
    have hcards : (good.image Finset.card).Nonempty :=
      ⟨s.card, Finset.mem_image.mpr ⟨s, hsgood, rfl⟩⟩
    let m := (good.image Finset.card).min' hcards
    have hm : m ∈ good.image Finset.card := Finset.min'_mem _ _
    obtain ⟨u, hugood, hucard⟩ := Finset.mem_image.mp hm
    have hus : u ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hugood).1
    have hulower : a ≤ 2 * ∑ i ∈ u, w i := (Finset.mem_filter.mp hugood).2
    refine ⟨u, hus, hulower, ?_⟩
    by_contra hua
    have hu_nonempty : u.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hu
      subst u
      simp at hulower
      omega
    obtain ⟨i, hiu⟩ := hu_nonempty
    let u' := u.erase i
    have hu'card : u'.card < u.card := by
      simp only [u', Finset.card_erase_of_mem hiu]
      have := Finset.card_pos.mpr ⟨i, hiu⟩
      omega
    have hu'notgood : u' ∉ good := by
      intro hu'good
      have hmin := Finset.min'_le (good.image Finset.card) u'.card
        (Finset.mem_image.mpr ⟨u', hu'good, rfl⟩)
      dsimp only [m] at hucard hmin
      omega
    have hu'sub : u' ⊆ s := (Finset.erase_subset _ _).trans hus
    have hu'half : 2 * ∑ j ∈ u', w j < a := by
      have : ¬ a ≤ 2 * ∑ j ∈ u', w j := by
        intro h
        exact hu'notgood (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hu'sub, h⟩)
      omega
    have hi_small : 2 * w i < a := hlarge i (hus hiu)
    have hsplit : ∑ j ∈ u, w j = (∑ j ∈ u', w j) + w i := by
      rw [← Finset.sum_erase_add _ _ hiu]
    have : ∑ j ∈ u, w j < a := by omega
    exact hua this.le

/-- Union of a selected family of connected components, kept as a disjoint
union so its cardinality computes without inclusion--exclusion. -/
private noncomputable def componentUnion {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (U : Finset H.ConnectedComponent) : Finset W :=
  U.disjiUnion (fun C ↦ C.supp.toFinset) (by
    intro C _ D _ hCD
    exact Set.disjoint_toFinset.mpr
      (pairwise_disjoint_supp_connectedComponent H hCD))

@[simp]
private theorem mem_componentUnion {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (U : Finset H.ConnectedComponent) (x : W) :
    x ∈ componentUnion H U ↔ ∃ C ∈ U, x ∈ C.supp := by
  classical
  simp [componentUnion]

@[simp]
private theorem card_componentUnion {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (U : Finset H.ConnectedComponent) :
    (componentUnion H U).card = ∑ C ∈ U, Nat.card C := by
  classical
  unfold componentUnion
  rw [Finset.card_disjiUnion]
  apply Finset.sum_congr rfl
  intro C _
  rw [← Set.ncard_eq_toFinset_card', ← Nat.card_coe_set_eq]
  change Nat.card (↑C.supp) = Nat.card (↑C.supp)
  rfl

private theorem sum_component_card {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    (∑ C : H.ConnectedComponent, Nat.card C) = Fintype.card W := by
  classical
  rw [← card_componentUnion H (Finset.univ : Finset H.ConnectedComponent)]
  have hall : componentUnion H (Finset.univ : Finset H.ConnectedComponent) = Finset.univ := by
    ext x
    simp only [mem_componentUnion, Finset.mem_univ, true_and]
    exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨H.connectedComponentMk x, rfl⟩⟩
  rw [hall, Finset.card_univ]

/-- A path separator certificate of the kind produced by depth-first search.
The final field records that every selected vertex can be reached from the
last spine vertex while staying in the selected set after the first vertex. -/
structure PathSeparatorCertificate [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) (a : ℕ) where
  endpoint : V
  spine : G.Walk root endpoint
  chosen : Finset V
  spine_isPath : spine.IsPath
  lower_size : a ≤ 2 * chosen.card
  upper_size : chosen.card ≤ a
  disjoint_spine : Disjoint chosen spine.support.toFinset
  boundary_subset : externalNeighborhood G chosen ⊆ spine.support.toFinset
  endpoint_path : ∀ x ∈ chosen, ∃ q : G.Walk endpoint x,
    q.IsPath ∧ q.support.tail.toFinset ⊆ chosen

private theorem terminal_pathSeparatorCertificate [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.Connected)
    (root : V) {a : ℕ} (ha : 0 < a) (hcard : a < Fintype.card V)
    (hsmall : ∀ C : (G.induce ({root}ᶜ : Set V)).ConnectedComponent,
      Nat.card C ≤ a) :
    Nonempty (PathSeparatorCertificate G root a) := by
  classical
  let R : Set V := ({root}ᶜ : Set V)
  let H : SimpleGraph R := G.induce R
  have hRcard : Fintype.card R = Fintype.card V - 1 := by
    dsimp only [R]
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_compl,
      Set.ncard_singleton, Nat.card_eq_fintype_card]
  have htotal : a ≤ ∑ C : H.ConnectedComponent, Nat.card C := by
    rw [sum_component_card H, hRcard]
    omega
  obtain ⟨U, _, hUlower, hUupper⟩ :=
    exists_subset_sum_half_le (Finset.univ : Finset H.ConnectedComponent)
      (fun C ↦ Nat.card C) ha (fun C _ ↦ hsmall C) htotal
  let e : R ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let X₀ : Finset R := componentUnion H U
  let X : Finset V := X₀.map e
  refine ⟨
    { endpoint := root
      spine := .nil
      chosen := X
      spine_isPath := Walk.IsPath.nil
      lower_size := ?_
      upper_size := ?_
      disjoint_spine := ?_
      boundary_subset := ?_
      endpoint_path := ?_ }⟩
  · simpa only [X, Finset.card_map, X₀, card_componentUnion] using hUlower
  · simpa only [X, Finset.card_map, X₀, card_componentUnion] using hUupper
  · rw [Finset.disjoint_left]
    intro x hxX hxroot
    have hxroot' : x = root := by simpa using hxroot
    subst x
    obtain ⟨xr, _, hxr⟩ := Finset.mem_map.mp hxX
    dsimp only [e] at hxr
    exact xr.2 hxr
  · intro y hyN
    obtain ⟨hyX, x, hxX, hxy⟩ := (mem_externalNeighborhood G X y).mp hyN
    have hyr : y = root := by
      by_contra hyr
      let yr : R := ⟨y, by simpa [R] using hyr⟩
      obtain ⟨xr, hxrX₀, hxr⟩ := Finset.mem_map.mp hxX
      have hxr_eq : xr.1 = x := by
        dsimp only [e] at hxr
        exact hxr
      obtain ⟨C, hCU, hxrC⟩ := (mem_componentUnion H U xr).mp hxrX₀
      have hadjH : H.Adj xr yr := by
        apply SimpleGraph.induce_adj.mpr
        simpa [hxr_eq] using hxy
      have hyrC : yr ∈ C.supp := (C.mem_supp_congr_adj hadjH).mp hxrC
      have hyrX₀ : yr ∈ X₀ := by
        exact (mem_componentUnion H U yr).mpr ⟨C, hCU, hyrC⟩
      have hyrX : y ∈ X := by
        apply Finset.mem_map.mpr
        exact ⟨yr, hyrX₀, rfl⟩
      exact hyX hyrX
    subst y
    simp
  · intro x hxX
    obtain ⟨xr, hxrX₀, hxr⟩ := Finset.mem_map.mp hxX
    have hxr_eq : xr.1 = x := by
      dsimp only [e] at hxr
      exact hxr
    obtain ⟨C, hCU, hxrC⟩ := (mem_componentUnion H U xr).mp hxrX₀
    obtain ⟨s, hsadj⟩ := exists_root_adjacent_component hG root C
    have hreach : H.Reachable s.1 xr := C.reachable_of_mem_supp s.2 hxrC
    obtain ⟨p, hp⟩ := hreach.exists_isPath
    let pG : G.Walk s.1.1 x :=
      (p.map (SimpleGraph.Embedding.induce R).toHom).copy rfl hxr_eq
    let q : G.Walk root x := pG.cons hsadj
    refine ⟨q, ?_, ?_⟩
    · apply Walk.IsPath.cons
      · simpa only [pG, Walk.isPath_copy] using
          (Walk.map_isPath_of_injective
            (f := (SimpleGraph.Embedding.induce R).toHom) Subtype.val_injective hp)
      · intro hrootp
        simp only [pG, Walk.support_copy, Walk.support_map] at hrootp
        obtain ⟨z, _, hz⟩ := List.mem_map.mp hrootp
        exact z.2 (by simpa [R] using hz)
    · intro z hzq
      have hzmap : z ∈ (p.map (SimpleGraph.Embedding.induce R).toHom).support := by
        simpa [q, pG] using hzq
      rw [Walk.support_map] at hzmap
      obtain ⟨zr, hzp, hzr⟩ := List.mem_map.mp hzmap
      have hzrC : zr ∈ C.supp := by
        rw [ConnectedComponent.mem_supp_iff]
        have hscomp := (ConnectedComponent.mem_supp_iff C s.1).mp s.2
        rw [← hscomp]
        exact (ConnectedComponent.sound (p.takeUntil zr hzp).reachable).symm
      have hzrX₀ : zr ∈ X₀ :=
        (mem_componentUnion H U zr).mpr ⟨C, hCU, hzrC⟩
      apply Finset.mem_map.mpr
      exact ⟨zr, hzrX₀, hzr⟩

private noncomputable def lift_pathSeparatorCertificate [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (root : V) {a : ℕ}
    (C : (G.induce ({root}ᶜ : Set V)).ConnectedComponent) (s : C)
    [Fintype C]
    [DecidableRel C.toSimpleGraph.Adj]
    (hrs : G.Adj root s.1.1)
    (D : PathSeparatorCertificate C.toSimpleGraph s a) :
    PathSeparatorCertificate G root a := by
  classical
  let R : Set V := ({root}ᶜ : Set V)
  let H : SimpleGraph R := G.induce R
  let φ : C.toSimpleGraph →g G :=
    (SimpleGraph.Embedding.induce R).toHom.comp C.toSimpleGraph_hom
  let e : C ↪ V := ⟨fun x ↦ x.1.1, by intro x y h; exact Subtype.ext (Subtype.ext h)⟩
  let X : Finset V := D.chosen.map e
  let mappedSpine : G.Walk s.1.1 (e D.endpoint) := D.spine.map φ
  let spine : G.Walk root (e D.endpoint) := mappedSpine.cons hrs
  refine
    { endpoint := e D.endpoint
      spine := spine
      chosen := X
      spine_isPath := ?_
      lower_size := by simpa [X] using D.lower_size
      upper_size := by simpa [X] using D.upper_size
      disjoint_spine := ?_
      boundary_subset := ?_
      endpoint_path := ?_ }
  · apply Walk.IsPath.cons
    · exact Walk.map_isPath_of_injective (f := φ) (by
        intro x y h
        exact Subtype.ext (Subtype.ext h)) D.spine_isPath
    · intro hroot
      change root ∈ (D.spine.map φ).support at hroot
      rw [Walk.support_map] at hroot
      obtain ⟨z, _, hz⟩ := List.mem_map.mp hroot
      apply z.1.2
      change z.1.1 = root
      change ((C.toSimpleGraph_hom z : R) : V) = root at hz
      simpa only [ConnectedComponent.toSimpleGraph_hom_apply] using hz
  · rw [Finset.disjoint_left]
    intro x hxX hxsp
    have hxX' : x ∈ D.chosen.map e := by simpa [X] using hxX
    obtain ⟨xc, hxcD, hxc⟩ := Finset.mem_map.mp hxX'
    have hxc_eq : e xc = x := hxc
    have hx_cases : x = root ∨ x ∈ mappedSpine.support := by
      simpa [spine] using hxsp
    cases hx_cases with
    | inl hxr =>
        apply xc.1.2
        change xc.1.1 = root
        change xc.1.1 = x at hxc_eq
        exact hxc_eq.trans hxr
    | inr hxm =>
        change x ∈ (D.spine.map φ).support at hxm
        rw [Walk.support_map] at hxm
        obtain ⟨yc, hycsp, hyc⟩ := List.mem_map.mp hxm
        have hxyc : xc = yc := by
          apply e.injective
          have hyc' : e yc = x := by
            change yc.1.1 = x
            change ((C.toSimpleGraph_hom yc : R) : V) = x at hyc
            simpa only [ConnectedComponent.toSimpleGraph_hom_apply] using hyc
          exact hxc_eq.trans hyc'.symm
        subst yc
        exact (Finset.disjoint_left.mp D.disjoint_spine hxcD) (by simpa using hycsp)
  · intro y hyN
    obtain ⟨hyX, x, hxX, hxy⟩ := (mem_externalNeighborhood G X y).mp hyN
    by_cases hyr : y = root
    · subst y
      simp [spine]
    · have hxX' : x ∈ D.chosen.map e := by simpa [X] using hxX
      obtain ⟨xc, hxcD, hxc⟩ := Finset.mem_map.mp hxX'
      have hxc_eq : xc.1.1 = x := by simpa [e] using hxc
      let yr : R := ⟨y, by simpa [R] using hyr⟩
      have hadjH : H.Adj xc.1 yr := by
        apply SimpleGraph.induce_adj.mpr
        simpa [hxc_eq] using hxy
      have hyrC : yr ∈ C.supp := (C.mem_supp_congr_adj hadjH).mp xc.2
      let yc : C := ⟨yr, hyrC⟩
      have hyc_not : yc ∉ D.chosen := by
        intro hyc
        apply hyX
        apply Finset.mem_map.mpr
        refine ⟨yc, hyc, ?_⟩
        simp [e, yc, yr]
      have hadjC : C.toSimpleGraph.Adj xc yc := by
        exact (C.toSimpleGraph_adj xc.2 hyrC).mpr hadjH
      have hycN : yc ∈ externalNeighborhood C.toSimpleGraph D.chosen :=
        (mem_externalNeighborhood C.toSimpleGraph D.chosen yc).mpr
          ⟨hyc_not, xc, hxcD, hadjC⟩
      have hycsp : yc ∈ D.spine.support := by
        simpa using D.boundary_subset hycN
      have hymap : y ∈ mappedSpine.support := by
        change y ∈ (D.spine.map φ).support
        rw [Walk.support_map]
        apply List.mem_map.mpr
        refine ⟨yc, hycsp, ?_⟩
        rfl
      simpa [spine] using Or.inr hymap
  · intro x hxX
    have hxX' : x ∈ D.chosen.map e := by simpa [X] using hxX
    obtain ⟨xc, hxcD, hxc⟩ := Finset.mem_map.mp hxX'
    obtain ⟨q, hq, hqD⟩ := D.endpoint_path xc hxcD
    let qG : G.Walk (e D.endpoint) x :=
      (q.map φ).copy (by rfl) (by
        change xc.1.1 = x
        change xc.1.1 = x at hxc
        exact hxc)
    refine ⟨qG, ?_, ?_⟩
    · simpa only [qG, Walk.isPath_copy] using
        (Walk.map_isPath_of_injective (f := φ) (by
          intro z w h
          exact Subtype.ext (Subtype.ext h)) hq)
    · intro z hz
      have hzmap : z ∈ (q.map φ).support.tail := by simpa [qG] using hz
      rw [Walk.support_map, tail_map_eq] at hzmap
      obtain ⟨zc, hzc, hzval⟩ := List.mem_map.mp hzmap
      have hzcD : zc ∈ D.chosen := hqD (by simpa using hzc)
      apply Finset.mem_map.mpr
      refine ⟨zc, hzcD, ?_⟩
      change zc.1.1 = z
      change ((C.toSimpleGraph_hom zc : R) : V) = z at hzval
      simpa only [ConnectedComponent.toSimpleGraph_hom_apply] using hzval

/-- Every finite connected graph with more than `a` vertices has a DFS-style
path separator certificate.  The proof is a strong induction on the number of
vertices: delete the root, recurse into a component larger than `a`, or combine
small components at the terminal step. -/
theorem exists_pathSeparatorCertificate [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.Connected)
    (root : V) {a : ℕ} (ha : 0 < a) (hcard : a < Fintype.card V) :
    Nonempty (PathSeparatorCertificate G root a) := by
  classical
  have main : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W],
      ∀ (K : SimpleGraph W) [DecidableRel K.Adj] (r : W) (b : ℕ),
        0 < b → K.Connected → b < Fintype.card W → Fintype.card W = n →
          Nonempty (PathSeparatorCertificate K r b) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro W _ _ K _ r b hb hK hbcard hWcard
        let R : Set W := ({r}ᶜ : Set W)
        let H : SimpleGraph R := K.induce R
        by_cases hsmall : ∀ C : H.ConnectedComponent, Nat.card C ≤ b
        · apply terminal_pathSeparatorCertificate hK r hb hbcard
          intro C
          exact hsmall C
        · push Not at hsmall
          obtain ⟨C, hCbig⟩ := hsmall
          letI : Fintype C := Fintype.ofFinite C
          letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
          obtain ⟨s, hrs⟩ := exists_root_adjacent_component hK r C
          have hCltW : Fintype.card C < Fintype.card W := by
            let f : C → W := fun x ↦ x.1.1
            apply Fintype.card_lt_of_injective_not_surjective f
            · intro x y hxy
              exact Subtype.ext (Subtype.ext hxy)
            · intro hsurj
              obtain ⟨x, hx⟩ := hsurj r
              exact x.1.2 hx
          have hCrec : Nat.card C < n := by
            rw [Nat.card_eq_fintype_card]
            omega
          have hCcard : b < Fintype.card C := by
            rw [← Nat.card_eq_fintype_card]
            exact hCbig
          obtain ⟨D⟩ := ih (Nat.card C) hCrec C C.toSimpleGraph s b hb
            C.connected_toSimpleGraph hCcard (by rw [← Nat.card_eq_fintype_card])
          exact ⟨lift_pathSeparatorCertificate r C s hrs D⟩
  exact main (Fintype.card V) V G root a ha hG hcard rfl

private theorem externalNeighborhood_component_map [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (C : G.ConnectedComponent)
    [Fintype C] [DecidableRel C.toSimpleGraph.Adj] (X : Finset C) :
    externalNeighborhood G (X.map ⟨Subtype.val, Subtype.val_injective⟩) =
      (externalNeighborhood C.toSimpleGraph X).map
        ⟨Subtype.val, Subtype.val_injective⟩ := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨hyX, x, hxX, hxy⟩ :=
      (mem_externalNeighborhood G (X.map ⟨Subtype.val, Subtype.val_injective⟩) y).mp hy
    obtain ⟨xc, hxcX, hxc⟩ := Finset.mem_map.mp hxX
    have hxc_eq : xc.1 = x := by simpa using hxc
    have hyC : y ∈ C.supp := by
      apply C.mem_supp_of_adj_mem_supp xc.2
      simpa [hxc_eq] using hxy
    let yc : C := ⟨y, hyC⟩
    apply Finset.mem_map.mpr
    refine ⟨yc, ?_, rfl⟩
    apply (mem_externalNeighborhood C.toSimpleGraph X yc).mpr
    refine ⟨?_, xc, hxcX, ?_⟩
    · intro hycX
      apply hyX
      exact Finset.mem_map.mpr ⟨yc, hycX, rfl⟩
    · exact (C.toSimpleGraph_adj xc.2 hyC).mpr (by simpa [hxc_eq] using hxy)
  · intro hy
    obtain ⟨yc, hycN, hyc⟩ := Finset.mem_map.mp hy
    have hyc_eq : yc.1 = y := by simpa using hyc
    obtain ⟨hycX, xc, hxcX, hxy⟩ :=
      (mem_externalNeighborhood C.toSimpleGraph X yc).mp hycN
    apply (mem_externalNeighborhood G
      (X.map ⟨Subtype.val, Subtype.val_injective⟩) y).mpr
    refine ⟨?_, xc.1, Finset.mem_map.mpr ⟨xc, hxcX, rfl⟩, ?_⟩
    · intro hyX
      obtain ⟨zc, hzcX, hzc⟩ := Finset.mem_map.mp hyX
      apply hycX
      have : zc = yc := by
        apply Subtype.ext
        exact (by simpa [hyc_eq] using hzc)
      simpa [this] using hzcX
    · have hadjG : G.Adj xc.1 yc.1 :=
        (C.toSimpleGraph_adj xc.2 yc.2).mp hxy
      simpa [hyc_eq] using hadjG

/-- An expanding graph has a connected component larger than the upper size
allowed for the tested vertex sets.  Otherwise a union of whole components
can be greedily packed into the tested size interval, but has empty external
neighbourhood. -/
private theorem exists_large_connectedComponent_of_expansion
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {a t : ℕ} (ha : 0 < a) (ht : 0 < t) (hcard : a < Fintype.card V)
    (hexpand : ∀ X : Finset V,
      a ≤ 2 * X.card → X.card ≤ a →
        t ≤ (externalNeighborhood G X).card) :
    ∃ C : G.ConnectedComponent, a < Nat.card C := by
  classical
  by_contra hlarge
  push Not at hlarge
  have htotal : a ≤ ∑ C : G.ConnectedComponent, Nat.card C := by
    rw [sum_component_card G]
    exact hcard.le
  obtain ⟨U, _, hUlower, hUupper⟩ :=
    exists_subset_sum_half_le
      (Finset.univ : Finset G.ConnectedComponent)
      (fun C ↦ Nat.card C) ha (fun C _ ↦ hlarge C) htotal
  let X : Finset V := componentUnion G U
  have hNempty : externalNeighborhood G X = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hN
    obtain ⟨y, hyN⟩ := hN
    obtain ⟨hyX, x, hxX, hxy⟩ :=
      (mem_externalNeighborhood G X y).mp hyN
    obtain ⟨C, hCU, hxC⟩ := (mem_componentUnion G U x).mp hxX
    have hyC : y ∈ C.supp := (C.mem_supp_congr_adj hxy).mp hxC
    exact hyX ((mem_componentUnion G U y).mpr ⟨C, hCU, hyC⟩)
  have hExp : t ≤ (externalNeighborhood G X).card :=
    hexpand X
      (by simpa only [X, card_componentUnion] using hUlower)
      (by simpa only [X, card_componentUnion] using hUupper)
  rw [hNempty] at hExp
  simp only [Finset.card_empty] at hExp
  omega

namespace PathSeparatorCertificate

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {root : V} {a t : ℕ}

private theorem exists_boundary_vertex_far
    (C : PathSeparatorCertificate G root a)
    (htpos : 1 ≤ t)
    (ht : t ≤ (externalNeighborhood G C.chosen).card) :
    ∃ y ∈ externalNeighborhood G C.chosen,
      t - 1 ≤ C.spine.length - C.spine.support.idxOf y := by
  classical
  by_contra h
  push Not at h
  let f : ↑(externalNeighborhood G C.chosen) → Fin (t - 1) := fun y ↦
    ⟨C.spine.length - C.spine.support.idxOf y.1, h y.1 y.2⟩
  have hf : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    have hlen : C.spine.length - C.spine.support.idxOf y.1 =
        C.spine.length - C.spine.support.idxOf z.1 := congrArg Fin.val hyz
    have hymem : y.1 ∈ C.spine.support := by simpa using C.boundary_subset y.2
    have hzmem : z.1 ∈ C.spine.support := by simpa using C.boundary_subset z.2
    have hylt := List.idxOf_lt_length_of_mem hymem
    have hzlt := List.idxOf_lt_length_of_mem hzmem
    have hyi : C.spine.support.idxOf y.1 ≤ C.spine.length := by
      rw [C.spine.length_support] at hylt
      omega
    have hzi : C.spine.support.idxOf z.1 ≤ C.spine.length := by
      rw [C.spine.length_support] at hzlt
      omega
    have hidx : C.spine.support.idxOf y.1 = C.spine.support.idxOf z.1 := by omega
    have hyget := List.getElem_idxOf hylt
    have hzget := List.getElem_idxOf hzlt
    have helem :
        C.spine.support[C.spine.support.idxOf y.1] =
          C.spine.support[C.spine.support.idxOf z.1] := by
      simp only [hidx]
    exact hyget.symm.trans (helem.trans hzget)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe, Fintype.card_fin] at hcard
  omega

/-- A separator certificate whose external neighbourhood has size at least
`t` closes to a cycle of length at least `t + 1`. -/
theorem exists_long_cycle
    (C : PathSeparatorCertificate G root a)
    (htwo : 2 ≤ t)
    (hexpand : t ≤ (externalNeighborhood G C.chosen).card) :
    ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ t + 1 ≤ c.length := by
  classical
  obtain ⟨y, hyN, hyfar⟩ := C.exists_boundary_vertex_far (by omega) hexpand
  have hysp : y ∈ C.spine.support := by simpa using C.boundary_subset hyN
  have hyfar' : t - 1 ≤ (C.spine.dropUntil y hysp).length := by
    rw [C.spine.length_dropUntil]
    exact hyfar
  obtain ⟨hyX, x, hxX, hxy⟩ := (mem_externalNeighborhood G C.chosen y).mp hyN
  obtain ⟨q, hqpath, hqX⟩ := C.endpoint_path x hxX
  let p : G.Walk y x := (C.spine.dropUntil y hysp).append q
  have hp_path : p.IsPath := by
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
    refine ⟨(C.spine_isPath.dropUntil hysp).support_nodup,
      hqpath.support_nodup.tail, ?_⟩
    simp only [List.disjoint_left]
    intro z hzsp hzq
    have hzsp' : z ∈ C.spine.support :=
      C.spine.support_dropUntil_subset_support hysp hzsp
    have hzX : z ∈ C.chosen := by
      exact hqX (by simpa using hzq)
    exact (Finset.disjoint_left.mp C.disjoint_spine hzX) (by simpa using hzsp')
  have hy_not_tail : y ∉ p.support.tail := by
    have hnodup := hp_path.support_nodup
    rw [← p.cons_tail_support] at hnodup
    exact (List.nodup_cons.mp hnodup).1
  have hedge_path : hxy.toWalk.IsPath := SimpleGraph.Walk.IsPath.of_adj hxy
  have hdisj : p.support.tail.Disjoint hxy.toWalk.support.tail := by
    simpa [SimpleGraph.Adj.toWalk, List.disjoint_left] using hy_not_tail
  have hq_pos : 0 < q.length := by
    have hne : C.endpoint ≠ x := by
      intro heq
      have hendsp : C.endpoint ∈ C.spine.support := C.spine.end_mem_support
      exact (Finset.disjoint_left.mp C.disjoint_spine hxX)
        (by simpa [heq] using hendsp)
    exact Walk.not_nil_iff_lt_length.mp (fun hnil ↦ hne (hqpath.nil_iff_eq.mp hnil))
  have hp_long : 1 < p.length := by
    simp only [p, Walk.length_append]
    omega
  refine ⟨y, p.append hxy.toWalk,
    hp_path.isCycle_append hedge_path hdisj (Or.inl hp_long), ?_⟩
  simp only [Walk.length_append, p]
  simp
  omega

end PathSeparatorCertificate

/-- **Krivelevich's long-cycle lemma (paper Lemma 3.1).**

If `G` has more than `a` vertices and every vertex set `X` with
`a / 2 ≤ |X| ≤ a` has at least `t` external neighbours, then `G` has a
cycle of length at least `t + 1`.  Since all quantities are natural numbers,
the lower bound is stated without division as `a ≤ 2 * X.card`; this is
equivalent to the paper's inequality, including when `a` is odd. -/
theorem krivelevich_long_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {a t : ℕ}
    (ha : 0 < a) (htwo : 2 ≤ t) (hcard : a < Fintype.card V)
    (hexpand : ∀ X : Finset V,
      a ≤ 2 * X.card → X.card ≤ a →
        t ≤ (externalNeighborhood G X).card) :
    ∃ v : V, ∃ c : G.Walk v v, c.IsCycle ∧ t + 1 ≤ c.length := by
  classical
  obtain ⟨C, hCcard⟩ :=
    exists_large_connectedComponent_of_expansion ha (by omega) hcard hexpand
  letI : Fintype C := Fintype.ofFinite C
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  obtain ⟨r, hrC⟩ := C.nonempty_supp
  let root : C := ⟨r, hrC⟩
  have hCcard' : a < Fintype.card C := by
    rw [← Nat.card_eq_fintype_card]
    exact hCcard
  obtain ⟨D⟩ := exists_pathSeparatorCertificate
    C.connected_toSimpleGraph root ha hCcard'
  have hDexpand :
      t ≤ (externalNeighborhood C.toSimpleGraph D.chosen).card := by
    have hOuter := hexpand
      (D.chosen.map ⟨Subtype.val, Subtype.val_injective⟩)
      (by simpa only [Finset.card_map] using D.lower_size)
      (by simpa only [Finset.card_map] using D.upper_size)
    rw [externalNeighborhood_component_map C D.chosen] at hOuter
    simpa only [Finset.card_map] using hOuter
  obtain ⟨v, c, hcycle, hlength⟩ :=
    PathSeparatorCertificate.exists_long_cycle D htwo hDexpand
  have hinjective : Function.Injective
      (C.toSimpleGraph_hom : C → V) := by
    intro x y hxy
    exact Subtype.ext hxy
  let cG : G.Walk v.1 v.1 :=
    (c.map C.toSimpleGraph_hom).copy
      (by simp only [ConnectedComponent.toSimpleGraph_hom_apply])
      (by simp only [ConnectedComponent.toSimpleGraph_hom_apply])
  refine ⟨v.1, cG, ?_, ?_⟩
  · simpa only [cG, Walk.isCycle_copy] using hcycle.map hinjective
  · simpa only [cG, Walk.length_copy, Walk.length_map] using hlength

end LeanCo.SizeRamsey
