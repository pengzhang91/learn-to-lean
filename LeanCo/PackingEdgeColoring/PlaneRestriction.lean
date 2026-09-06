import LeanCo.PackingEdgeColoring.RotationSystem

/-!
# Restricting combinatorial maps

This file develops the finite-permutation operations needed to restrict a
rotation system after darts are deleted.  The central operation splices one
point out of a cyclic permutation: `erasePoint f x` fixes `x` and sends the
predecessor of `x` directly to `f x`.  Its restriction to the complement of
`x` is therefore the first-return permutation on the surviving points.

The graph-specific part identifies the darts of a subgraph with the subtype of
ambient darts whose adjacency is retained.  Face-count bookkeeping for edge
deletion is intentionally left to the next layer.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

namespace PermRestriction

variable {α : Type*}

/-- Transporting a permutation across an equivalence transports its cycle
relation pointwise. -/
theorem sameCycle_permCongr {β : Type*} (e : α ≃ β)
    (f : Equiv.Perm α) (x y : α) :
    (e.permCongr f).SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  constructor
  · rintro ⟨n, hn⟩
    have hp : e.permCongr (f ^ n) = e.permCongr f ^ n := by
      exact map_zpow e.permCongrHom f n
    refine ⟨n, ?_⟩
    apply e.injective
    calc
      e ((f ^ n) x) = e.permCongr (f ^ n) (e x) := by
        rw [Equiv.permCongr_apply, e.symm_apply_apply]
      _ = (e.permCongr f ^ n) (e x) := by
        rw [hp]
      _ = e y := hn
  · rintro ⟨n, hn⟩
    have hp : e.permCongr (f ^ n) = e.permCongr f ^ n := by
      exact map_zpow e.permCongrHom f n
    refine ⟨n, ?_⟩
    calc
      (e.permCongr f ^ n) (e x) = e.permCongr (f ^ n) (e x) := by
        rw [hp]
      _ = e ((f ^ n) x) := by
        rw [Equiv.permCongr_apply, e.symm_apply_apply]
      _ = e y := congrArg e hn

/-- Cyclicity on the whole type is invariant under relabelling. -/
theorem isCycleOn_univ_permCongr {β : Type*} (e : α ≃ β)
    (f : Equiv.Perm α) :
    (e.permCongr f).IsCycleOn Set.univ ↔ f.IsCycleOn Set.univ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Set.bijOn_univ] using f.bijective
    · intro x _ y _
      exact (sameCycle_permCongr e f x y).mp
        (h.2 (Set.mem_univ _) (Set.mem_univ _))
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Set.bijOn_univ] using (e.permCongr f).bijective
    · intro x _ y _
      obtain ⟨x, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := e.surjective y
      exact (sameCycle_permCongr e f x y).mpr
        (h.2 (Set.mem_univ _) (Set.mem_univ _))

/-- Splice `x` out of the cycle of `f`, leaving `x` as a fixed point. -/
def erasePoint [DecidableEq α] (f : Equiv.Perm α) (x : α) : Equiv.Perm α :=
  Equiv.swap x (f x) * f

@[simp]
theorem erasePoint_apply_self [DecidableEq α] (f : Equiv.Perm α) (x : α) :
    erasePoint f x x = x := by
  simp [erasePoint, Equiv.Perm.mul_apply]

/-- The complement of the erased point is invariant under `erasePoint`. -/
theorem erasePoint_apply_ne_iff [DecidableEq α] (f : Equiv.Perm α) (x y : α) :
    erasePoint f x y ≠ x ↔ y ≠ x := by
  constructor
  · intro h hy
    subst y
    exact h (erasePoint_apply_self f x)
  · intro h hy
    apply h
    apply (erasePoint f x).injective
    simpa only [erasePoint_apply_self] using hy

/-- The first-return permutation obtained by removing one point from the
underlying finite cycle. -/
def erasePointRestrict [DecidableEq α] (f : Equiv.Perm α) (x : α) :
    Equiv.Perm {y : α // y ∈ ({z | z ≠ x} : Set α)} :=
  (erasePoint f x).subtypePerm (erasePoint_apply_ne_iff f x)

@[simp]
theorem erasePointRestrict_apply_coe [DecidableEq α]
    (f : Equiv.Perm α) (x : α)
    (y : {y : α // y ∈ ({z | z ≠ x} : Set α)}) :
    (erasePointRestrict f x y : α) = erasePoint f x y := by
  rfl

section Finite

variable [Fintype α] [DecidableEq α]

/-- Splicing one point out of a cyclic permutation leaves a cyclic
first-return permutation on the complement.  `IsCycleOn univ` includes the
zero- and one-point cases, so this statement has no cardinality side
conditions. -/
theorem IsCycleOn.erasePoint_compl {f : Equiv.Perm α}
    (hf : f.IsCycleOn Set.univ) (x : α) :
    (erasePoint f x).IsCycleOn {y | y ≠ x} := by
  let t : Set α := {y | y ≠ x}
  rcases t.subsingleton_or_nontrivial with ht | ht
  · have hmap : Set.MapsTo (erasePoint f x) t t := by
      intro y hy
      exact (erasePoint_apply_ne_iff f x y).mpr hy
    have hbij : Set.BijOn (erasePoint f x) t t :=
      (Set.toFinite t).injOn_iff_bijOn_of_mapsTo hmap |>.mp
        (erasePoint f x).injective.injOn
    refine ⟨hbij, ?_⟩
    intro y hy z hz
    exact (ht hy hz).sameCycle _
  · have huniv : (Set.univ : Set α).Nontrivial :=
      ht.mono (Set.subset_univ t)
    have hfx : f x ≠ x := hf.apply_ne huniv (Set.mem_univ x)
    have hffx : f (f x) ≠ x := by
      intro htwo
      obtain ⟨y, hy, z, hz, hyz⟩ := ht
      have y_eq : y = f x := by
        obtain ⟨n, hn⟩ := hf.2 (Set.mem_univ x) (Set.mem_univ y)
        rcases Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self htwo n with hn' | hn'
        · exact (hy (hn.symm.trans hn')).elim
        · exact hn.symm.trans hn'
      have z_eq : z = f x := by
        obtain ⟨n, hn⟩ := hf.2 (Set.mem_univ x) (Set.mem_univ z)
        rcases Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self htwo n with hn' | hn'
        · exact (hz (hn.symm.trans hn')).elim
        · exact hn.symm.trans hn'
      exact hyz (y_eq.trans z_eq.symm)
    have hfcycle : f.IsCycle := by
      rw [Equiv.Perm.isCycle_iff_sameCycle hfx]
      intro y
      constructor
      · intro _
        exact hf.apply_ne huniv (Set.mem_univ y)
      · intro _
        exact hf.2 (Set.mem_univ x) (Set.mem_univ y)
    have hgcycle : (erasePoint f x).IsCycle := by
      exact hfcycle.swap_mul hfx hffx
    have hfsupport : f.support = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro y
      exact Equiv.Perm.mem_support.mpr (hf.apply_ne huniv (Set.mem_univ y))
    have hgsupport : (erasePoint f x).support = Finset.univ \ {x} := by
      rw [erasePoint, Equiv.Perm.support_swap_mul_eq f x hffx, hfsupport]
    have hset : {y | erasePoint f x y ≠ y} = t := by
      ext y
      change erasePoint f x y ≠ y ↔ y ∈ t
      rw [← Equiv.Perm.mem_support]
      rw [hgsupport]
      simp [t]
    change (erasePoint f x).IsCycleOn t
    rw [← hset]
    exact hgcycle.isCycleOn

/-- Subtype version of `IsCycleOn.erasePoint_compl`: the first-return
permutation is cyclic on its whole new type. -/
theorem IsCycleOn.erasePointRestrict {f : Equiv.Perm α}
    (hf : f.IsCycleOn Set.univ) (x : α) :
    (erasePointRestrict f x).IsCycleOn Set.univ := by
  exact (PermRestriction.IsCycleOn.erasePoint_compl hf x).subtypePerm

end Finite

end PermRestriction

variable {V : Type*} {G H : SimpleGraph V}

/-- The injective map from the darts of a subgraph to the ambient darts. -/
def dartEmbeddingOfLE (h : H ≤ G) : H.Dart ↪ G.Dart where
  toFun d := ⟨d.toProd, h d.adj⟩
  inj' := by
    intro d e hde
    apply Dart.ext
    exact congrArg (fun q : G.Dart ↦ q.toProd) hde

@[simp]
theorem dartEmbeddingOfLE_fst (h : H ≤ G) (d : H.Dart) :
    (dartEmbeddingOfLE h d).fst = d.fst := rfl

@[simp]
theorem dartEmbeddingOfLE_snd (h : H ≤ G) (d : H.Dart) :
    (dartEmbeddingOfLE h d).snd = d.snd := rfl

@[simp]
theorem dartEmbeddingOfLE_symm (h : H ≤ G) (d : H.Dart) :
    dartEmbeddingOfLE h d.symm = (dartEmbeddingOfLE h d).symm := rfl

/-- Darts of `H` are exactly ambient darts whose endpoints remain adjacent in
`H`. -/
def dartEquivSubtypeOfLE (h : H ≤ G) :
    H.Dart ≃ {d : G.Dart // H.Adj d.fst d.snd} where
  toFun d := ⟨dartEmbeddingOfLE h d, d.adj⟩
  invFun d := ⟨d.1.toProd, d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem dartEquivSubtypeOfLE_apply_coe (h : H ≤ G) (d : H.Dart) :
    ((dartEquivSubtypeOfLE h d : {d : G.Dart // H.Adj d.fst d.snd}) : G.Dart) =
      dartEmbeddingOfLE h d := rfl

namespace RotationSystem

variable {G : SimpleGraph V} (R : RotationSystem G)

/-- The outgoing-dart fibre at a vertex. -/
abbrev OutDart (G : SimpleGraph V) (v : V) := {d : G.Dart // d.fst = v}

/-- Regard a dart as an element of the outgoing fibre at its first vertex. -/
def outDartSelf (d : G.Dart) : OutDart G d.fst := ⟨d, rfl⟩

/-- Inclusion of one outgoing-dart fibre along a graph inclusion. -/
def outDartEmbeddingOfLE {H : SimpleGraph V} (h : H ≤ G) (v : V) :
    OutDart H v ↪ OutDart G v where
  toFun d := ⟨dartEmbeddingOfLE h d.1, d.2⟩
  inj' := by
    intro d e hde
    apply Subtype.ext
    apply (dartEmbeddingOfLE h).injective
    exact Subtype.ext_iff.mp hde

/-- At an endpoint of a deleted edge, the surviving outgoing darts are
exactly the old outgoing darts other than the oriented copy of that edge. -/
def outDartDeleteEdgeEquiv (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) :
    OutDart (G.deleteEdges {e}) a.fst ≃
      {d : OutDart G a.fst //
        d ∈ ({z | z ≠ outDartSelf a} : Set (OutDart G a.fst))} where
  toFun d := ⟨outDartEmbeddingOfLE (G.deleteEdges_le {e}) a.fst d, by
    intro hda
    have hdart : dartEmbeddingOfLE (G.deleteEdges_le {e}) d.1 = a :=
      Subtype.ext_iff.mp hda
    have hnot := (SimpleGraph.deleteEdges_adj.mp d.1.adj).2
    apply hnot
    simp only [Set.mem_singleton_iff]
    change (dartEmbeddingOfLE (G.deleteEdges_le {e}) d.1).edge = e
    rw [hdart, ha]⟩
  invFun d := by
    have hedge : d.1.1.edge ≠ e := by
      intro hde
      have heq : d.1.1.edge = a.edge := hde.trans ha.symm
      rcases (dart_edge_eq_iff d.1.1 a).mp heq with hsame | hsymm
      · exact d.2 (Subtype.ext hsame)
      · have hfst : a.fst = a.snd := by
          calc
            a.fst = d.1.1.fst := d.1.2.symm
            _ = a.symm.fst := congrArg (fun q : G.Dart ↦ q.fst) hsymm
            _ = a.snd := rfl
        exact a.fst_ne_snd hfst
    let d' : (G.deleteEdges {e}).Dart :=
      ⟨d.1.1.toProd, SimpleGraph.deleteEdges_adj.mpr
        ⟨d.1.1.adj, by
          simp only [Set.mem_singleton_iff]
          simpa only [Dart.edge] using hedge⟩⟩
    exact ⟨d', d.1.2⟩
  left_inv d := by
    apply Subtype.ext
    apply Dart.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    apply Dart.ext
    rfl

/-- Away from the two endpoints, deleting an edge does not change the
outgoing-dart fibre. -/
def outDartDeleteEdgeEquivOfNe (e : Sym2 V) (a : G.Dart) (ha : a.edge = e)
    (v : V) (hv₁ : v ≠ a.fst) (hv₂ : v ≠ a.snd) :
    OutDart (G.deleteEdges {e}) v ≃ OutDart G v where
  toFun := outDartEmbeddingOfLE (G.deleteEdges_le {e}) v
  invFun d := by
    have hedge : d.1.edge ≠ e := by
      intro hde
      have heq : d.1.edge = a.edge := hde.trans ha.symm
      rcases (dart_edge_eq_iff d.1 a).mp heq with hsame | hsymm
      · exact hv₁ (d.2.symm.trans (congrArg (fun q : G.Dart ↦ q.fst) hsame))
      · exact hv₂ (d.2.symm.trans <| (congrArg (fun q : G.Dart ↦ q.fst) hsymm).trans rfl)
    let d' : (G.deleteEdges {e}).Dart :=
      ⟨d.1.toProd, SimpleGraph.deleteEdges_adj.mpr
        ⟨d.1.adj, by
          simp only [Set.mem_singleton_iff]
          simpa only [Dart.edge] using hedge⟩⟩
    exact ⟨d', d.2⟩
  left_inv d := by
    apply Subtype.ext
    apply Dart.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    apply Dart.ext
    rfl

/-- Every dart is uniquely an outgoing dart together with its initial vertex. -/
def dartSigmaEquiv (G : SimpleGraph V) :
    G.Dart ≃ Σ v : V, OutDart G v where
  toFun d := ⟨d.fst, d, rfl⟩
  invFun d := d.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, d, hd⟩
    subst v
    rfl

/-- Assemble one permutation on every outgoing-dart fibre into a permutation
of their sigma type. -/
def fiberwisePerm (ρ : ∀ v : V, Equiv.Perm (OutDart G v)) :
    Equiv.Perm (Σ v : V, OutDart G v) where
  toFun d := ⟨d.1, ρ d.1 d.2⟩
  invFun d := ⟨d.1, (ρ d.1).symm d.2⟩
  left_inv d := by
    cases d with
    | mk v d => simp
  right_inv d := by
    cases d with
    | mk v d => simp

@[simp]
theorem fiberwisePerm_apply (ρ : ∀ v : V, Equiv.Perm (OutDart G v))
    (v : V) (d : OutDart G v) :
    fiberwisePerm ρ ⟨v, d⟩ = ⟨v, ρ v d⟩ := rfl

theorem fiberwisePerm_zpow_apply (ρ : ∀ v : V, Equiv.Perm (OutDart G v))
    (n : ℤ) (v : V) (d : OutDart G v) :
    (fiberwisePerm ρ ^ n) ⟨v, d⟩ = ⟨v, (ρ v ^ n) d⟩ := by
  induction n using Int.induction_on generalizing d with
  | zero => rfl
  | succ n ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, fiberwisePerm_apply, ih]
      rw [zpow_add_one, Equiv.Perm.mul_apply]
  | pred n ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply]
      calc
        (fiberwisePerm ρ ^ (-Int.ofNat n))
            ((fiberwisePerm ρ)⁻¹ ⟨v, d⟩) =
            (fiberwisePerm ρ ^ (-Int.ofNat n))
              ⟨v, (ρ v).symm d⟩ := rfl
        _ = ⟨v, (ρ v ^ (-Int.ofNat n)) ((ρ v).symm d)⟩ :=
          ih ((ρ v).symm d)
        _ = ⟨v, (ρ v ^ (-Int.ofNat n - 1)) d⟩ := by
          rw [zpow_sub_one, Equiv.Perm.mul_apply]
          rfl

/-- Assemble cyclic permutations on all outgoing-dart fibres into a global
rotation system. -/
def ofVertexPermutations (ρ : ∀ v : V, Equiv.Perm (OutDart G v))
    (hρ : ∀ v, (ρ v).IsCycleOn Set.univ) : RotationSystem G where
  rotation := (dartSigmaEquiv G).symm.permCongr (fiberwisePerm ρ)
  rotation_fst := by
    intro d
    change (ρ d.fst ⟨d, rfl⟩).1.fst = d.fst
    exact (ρ d.fst ⟨d, rfl⟩).2
  rotation_transitive := by
    intro d e hde
    change ((dartSigmaEquiv G).symm.permCongr (fiberwisePerm ρ)).SameCycle d e
    let de : OutDart G d.fst := ⟨d, rfl⟩
    let ee : OutDart G d.fst := ⟨e, hde.symm⟩
    have hsigma' : (fiberwisePerm ρ).SameCycle
        (⟨d.fst, de⟩ : Σ v : V, OutDart G v) ⟨d.fst, ee⟩ := by
      obtain ⟨n, hn⟩ := (hρ d.fst).2 (Set.mem_univ _) (Set.mem_univ
        ee)
      refine ⟨n, ?_⟩
      rw [fiberwisePerm_zpow_apply]
      exact congrArg (fun q : OutDart G d.fst ↦
        (⟨d.fst, q⟩ : Σ v : V, OutDart G v)) hn
    have heq : (⟨d.fst, ee⟩ : Σ v : V, OutDart G v) = dartSigmaEquiv G e := by
      apply (dartSigmaEquiv G).symm.injective
      rfl
    have hsigma : (fiberwisePerm ρ).SameCycle
        (dartSigmaEquiv G d) (dartSigmaEquiv G e) := by
      rw [← heq]
      exact hsigma'
    exact (PermRestriction.sameCycle_permCongr
      (dartSigmaEquiv G).symm (fiberwisePerm ρ)
      (dartSigmaEquiv G d) (dartSigmaEquiv G e)).mpr hsigma

/-- Restriction of the global rotation to one outgoing-dart fibre. -/
def atVertex (v : V) : Equiv.Perm (OutDart G v) :=
  R.rotation.subtypePerm (p := fun d : G.Dart ↦ d.fst = v) fun d ↦ by
    rw [R.rotation_fst]

/-- Each vertex restriction really is one cyclic permutation, including the
empty and singleton fibres. -/
theorem atVertex_isCycleOn (v : V) :
    (R.atVertex v).IsCycleOn Set.univ := by
  refine ⟨?_, ?_⟩
  · simpa only [Set.bijOn_univ] using (R.atVertex v).bijective
  · intro d _ e _
    rw [atVertex, Equiv.Perm.sameCycle_subtypePerm]
    rw [R.rotation_sameCycle_iff_fst_eq]
    exact d.2.trans e.2.symm

@[simp]
theorem atVertex_ofVertexPermutations
    (ρ : ∀ v : V, Equiv.Perm (OutDart G v))
    (hρ : ∀ v, (ρ v).IsCycleOn Set.univ) (v : V) :
    (ofVertexPermutations ρ hρ).atVertex v = ρ v := by
  apply Equiv.ext
  rintro ⟨d, hd⟩
  subst v
  apply Subtype.ext
  rfl

/-- Vertex rotations after deleting one edge.  At its endpoints we use the
first-return permutation obtained by splicing out the corresponding dart; at
all other vertices the old rotation is transported unchanged. -/
def deleteEdgeVertexPerm [DecidableEq V] (e : Sym2 V) (a : G.Dart)
    (ha : a.edge = e) (v : V) :
    Equiv.Perm (OutDart (G.deleteEdges {e}) v) := by
  classical
  by_cases hv₁ : v = a.fst
  · subst v
    exact (outDartDeleteEdgeEquiv e a ha).symm.permCongr
      (PermRestriction.erasePointRestrict (R.atVertex a.fst) (outDartSelf a))
  · by_cases hv₂ : v = a.snd
    · subst v
      have ha' : a.symm.edge = e := by simpa only [Dart.edge_symm] using ha
      exact (outDartDeleteEdgeEquiv e a.symm ha').symm.permCongr
        (PermRestriction.erasePointRestrict (R.atVertex a.snd) (outDartSelf a.symm))
    · exact (outDartDeleteEdgeEquivOfNe e a ha v hv₁ hv₂).symm.permCongr
        (R.atVertex v)

theorem deleteEdgeVertexPerm_isCycleOn [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) (v : V) :
    (R.deleteEdgeVertexPerm e a ha v).IsCycleOn Set.univ := by
  classical
  unfold deleteEdgeVertexPerm
  split_ifs with hv₁ hv₂
  · subst v
    apply (PermRestriction.isCycleOn_univ_permCongr
      (outDartDeleteEdgeEquiv e a ha).symm _).mpr
    exact PermRestriction.IsCycleOn.erasePointRestrict
      (R.atVertex_isCycleOn a.fst) (outDartSelf a)
  · subst v
    have ha' : a.symm.edge = e := by simpa only [Dart.edge_symm] using ha
    apply (PermRestriction.isCycleOn_univ_permCongr
      (outDartDeleteEdgeEquiv e a.symm ha').symm _).mpr
    exact PermRestriction.IsCycleOn.erasePointRestrict
      (R.atVertex_isCycleOn a.snd) (outDartSelf a.symm)
  · apply (PermRestriction.isCycleOn_univ_permCongr
      (outDartDeleteEdgeEquivOfNe e a ha v hv₁ hv₂).symm _).mpr
    exact R.atVertex_isCycleOn v

/-- The rotation system induced after deleting one edge. -/
def deleteEdge [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) :
    RotationSystem (G.deleteEdges {e}) :=
  ofVertexPermutations (R.deleteEdgeVertexPerm e a ha)
    (R.deleteEdgeVertexPerm_isCycleOn e a ha)

@[simp]
theorem deleteEdge_atVertex [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) (v : V) :
    (R.deleteEdge e a ha).atVertex v = R.deleteEdgeVertexPerm e a ha v := by
  apply atVertex_ofVertexPermutations

/-- Deleting an edge represented by a dart lowers the edge count by exactly
one. -/
theorem edgeFinset_deleteEdge_card_add_one [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have hedge : (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
    ext q
    simp [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [hedge]
  apply Finset.card_erase_add_one
  rw [SimpleGraph.mem_edgeFinset]
  exact ha ▸ a.edge_mem

/-- For the explicit induced rotation, preservation of spherical Euler
characteristic is *exactly* the statement that deleting the edge merges two
face cycles.  This isolates the remaining face-splicing theorem needed for
full planarity heredity. -/
theorem deleteEdge_isSpherical_iff_faceCount_add_one [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) (hR : R.IsSpherical) :
    (R.deleteEdge e a ha).IsSpherical ↔
      (R.deleteEdge e a ha).faceCount + 1 = R.faceCount := by
  have hm := edgeFinset_deleteEdge_card_add_one e a ha
  unfold IsSpherical at hR ⊢
  omega

theorem deleteEdge_isSpherical_of_faceCount_add_one [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    (e : Sym2 V) (a : G.Dart) (ha : a.edge = e) (hR : R.IsSpherical)
    (hface : (R.deleteEdge e a ha).faceCount + 1 = R.faceCount) :
    (R.deleteEdge e a ha).IsSpherical :=
  (R.deleteEdge_isSpherical_iff_faceCount_add_one e a ha hR).mpr hface

/-- Reassembling the vertex restrictions of a rotation system returns its
original global rotation permutation. -/
theorem ofVertexPermutations_rotation_atVertex :
    (ofVertexPermutations (fun v ↦ R.atVertex v) R.atVertex_isCycleOn).rotation =
      R.rotation := by
  apply Equiv.ext
  intro d
  change (R.atVertex d.fst ⟨d, rfl⟩ : OutDart G d.fst).1 = R.rotation d
  rfl

end RotationSystem

end

end LeanCo.PackingEdgeColoring
