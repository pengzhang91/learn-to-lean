import LeanCo.PackingEdgeColoring.FaceBoundaryGirth
import LeanCo.PackingEdgeColoring.BridgeFaceSurgery

/-!
# Facial boundary walks under minimum degree two

This module removes the global two-sided-dart assumption from the facial
part of Section 4.  A bridge may occur twice on one face, but minimum degree
two prevents an immediate reversal.  Such a cyclically reduced facial walk
still contains a genuine cycle, and its short initial segments are paths
below the girth.
-/

open scoped SimpleGraph

namespace LeanCo.PackingEdgeColoring

open SimpleGraph

noncomputable section

variable {V : Type*} {G : SimpleGraph V}

namespace RotationSystem

variable (R : RotationSystem G)

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Deleting the edge of a dart cannot isolate its terminal endpoint when
that endpoint originally has degree at least two. -/
theorem not_isIsolated_delete_dart_edge_of_two_le_degree
    (d : G.Dart) (hdeg : 2 ≤ G.degree d.snd) :
    ¬ (G.deleteEdges {d.edge}).IsIsolated d.snd := by
  intro hisolated
  have hsubset : G.neighborFinset d.snd ⊆ {d.fst} := by
    intro w hw
    simp only [Finset.mem_singleton]
    by_contra hwne
    have hdw : G.Adj d.snd w := (G.mem_neighborFinset d.snd w).mp hw
    have hedge : s(d.snd, w) ≠ d.edge := by
      intro heq
      change s(d.snd, w) = s(d.fst, d.snd) at heq
      rcases Sym2.eq_iff.mp heq with h | h
      · exact d.snd_ne_fst h.1
      · exact hwne h.2
    have hdelete : (G.deleteEdges {d.edge}).Adj d.snd w := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hdw, by simpa only [Set.mem_singleton_iff] using hedge⟩
    exact hisolated w hdelete
  have hcard : (G.neighborFinset d.snd).card ≤ 1 := by
    calc
      (G.neighborFinset d.snd).card ≤ ({d.fst} : Finset V).card :=
        Finset.card_le_card hsubset
      _ = 1 := Finset.card_singleton d.fst
  rw [G.card_neighborFinset_eq_degree] at hcard
  omega

/-- A facial step never immediately reverses its dart when the terminal
vertex has degree at least two. -/
theorem faceStep_ne_symm_of_two_le_degree
    (d : G.Dart) (hdeg : 2 ≤ G.degree d.snd) :
    R.faceStep d ≠ d.symm := by
  intro h
  exact not_isIsolated_delete_dart_edge_of_two_le_degree d hdeg
    ((R.faceStep_eq_symm_iff_deleteEdge_isIsolated_snd d.edge d rfl).mp h)

/-- Consecutive dart occurrences on a facial boundary are never reverse
orientations under minimum degree two. -/
theorem faceDartAt_succ_ne_symm
    (hdeg : ∀ v, 2 ≤ G.degree v) (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (i : ℕ) :
    R.faceDartAt f a (i + 1) ≠ (R.faceDartAt f a i).symm := by
  have hstep : R.faceDartAt f a (i + 1) =
      R.faceStep (R.faceDartAt f a i) := by
    unfold faceDartAt
    rw [pow_succ']
    exact R.coe_faceBoundaryPerm_apply_eq_faceStep f
      (((R.faceBoundaryPerm f) ^ i) a)
  rw [hstep]
  exact R.faceStep_ne_symm_of_two_le_degree _
    (hdeg (R.faceDartAt f a i).snd)

/-- Every dart in a facial cycle occurs in the complete boundary walk based
at any chosen occurrence of that face. -/
theorem faceDart_mem_faceBoundaryWalk_darts
    (f : R.Face) (a : {a : G.Dart // a ∈ f.1.support})
    (d : G.Dart) (hd : d ∈ f.1.support) :
    d ∈ (R.faceBoundaryWalk f a (R.faceLength f)).darts := by
  have hcycleOn : f.1.IsCycleOn (↑f.1.support : Set G.Dart) := by
    rw [show (↑f.1.support : Set G.Dart) = {d | f.1 d ≠ d} by
      ext e
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Equiv.Perm.mem_support]]
    exact (R.face_isCycle f).isCycleOn
  obtain ⟨i, hi, hid⟩ := hcycleOn.exists_pow_eq a.2 hd
  rw [R.faceBoundaryWalk_darts, List.mem_ofFn]
  refine ⟨⟨i, ?_⟩, ?_⟩
  · simpa only [faceLength] using hi
  · simpa only [R.faceDartAt_eq_face_pow f a] using hid

/-- Every facial dart supplies its ambient adjacency inside the subgraph
traced by one complete boundary walk. -/
theorem faceDart_adj_faceBoundaryWalk_toSubgraph
    (f : R.Face) (a : {a : G.Dart // a ∈ f.1.support})
    (d : G.Dart) (hd : d ∈ f.1.support) :
    (R.faceBoundaryWalk f a (R.faceLength f)).toSubgraph.Adj d.fst d.snd := by
  rw [Walk.adj_toSubgraph_iff_mem_edges, Walk.edges]
  exact List.mem_map.mpr
    ⟨d, R.faceDart_mem_faceBoundaryWalk_darts f a d hd, rfl⟩

/-- Every vertex visited by a complete facial boundary is the tail of a
dart occurrence on that same face. -/
theorem exists_faceDart_fst_eq_of_mem_boundaryWalk_toSubgraph
    (f : R.Face) (a : {a : G.Dart // a ∈ f.1.support})
    (x : V)
    (hx : x ∈ (R.faceBoundaryWalk f a (R.faceLength f)).toSubgraph.verts) :
    ∃ d : G.Dart, d ∈ f.1.support ∧ d.fst = x := by
  let w := R.faceBoundaryWalk f a (R.faceLength f)
  have hxSupport : x ∈ w.support := by
    exact w.mem_verts_toSubgraph.mp hx
  rw [Walk.mem_support_iff_exists_getVert] at hxSupport
  obtain ⟨i, hix, hi⟩ := hxSupport
  have hi' : i ≤ R.faceLength f := by
    simpa only [w, R.faceBoundaryWalk_length] using hi
  by_cases hil : i < R.faceLength f
  · refine ⟨R.faceDartAt f a i, R.faceDartAt_mem_support f a i, ?_⟩
    calc
      (R.faceDartAt f a i).fst = R.faceVertexAt f a i := rfl
      _ = w.getVert i :=
        (R.faceBoundaryWalk_getVert f a (R.faceLength f) i hi').symm
      _ = x := hix
  · have hiEq : i = R.faceLength f := by omega
    subst i
    refine ⟨a.1, a.2, ?_⟩
    calc
      a.1.fst = R.faceVertexAt f a 0 := by
        rw [R.faceVertexAt_eq_faceDartAt_fst, R.faceDartAt_zero]
      _ = R.faceVertexAt f a (R.faceLength f) := by
        rw [R.faceVertexAt_eq_faceDartAt_fst,
          R.faceVertexAt_eq_faceDartAt_fst,
          R.faceDartAt_faceLength, R.faceDartAt_zero]
      _ = w.getVert (R.faceLength f) :=
        (R.faceBoundaryWalk_getVert f a (R.faceLength f)
          (R.faceLength f) le_rfl).symm
      _ = x := hix

/-- Every vertex of the subgraph traced by a complete facial boundary has
at least two neighbours in that subgraph, provided the ambient graph has
minimum degree at least two.  This remains true when a bridge occurs twice
on the same facial boundary. -/
theorem two_le_degree_faceBoundaryWalk_toSubgraph
    (hdeg : ∀ v, 2 ≤ G.degree v) (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support})
    (x : V)
    (hx : x ∈ (R.faceBoundaryWalk f a (R.faceLength f)).toSubgraph.verts) :
    2 ≤ ((R.faceBoundaryWalk f a (R.faceLength f)).toSubgraph.neighborSet x).ncard := by
  classical
  let w := R.faceBoundaryWalk f a (R.faceLength f)
  let H := w.toSubgraph
  obtain ⟨d, hd, rfl⟩ :=
    R.exists_faceDart_fst_eq_of_mem_boundaryWalk_toSubgraph f a x hx
  let e : G.Dart := f.1.symm d
  have heApply : f.1 e = d := by
    simp only [e, Equiv.apply_symm_apply]
  have he : e ∈ f.1.support := by
    rw [Equiv.Perm.mem_support]
    intro hedge
    have hed : e = d := hedge.symm.trans heApply
    apply Equiv.Perm.mem_support.mp hd
    calc
      f.1 d = f.1 e := congrArg f.1 hed.symm
      _ = d := heApply
  have hfaceStep : R.faceStep e = d := by
    rw [← R.face_apply_eq_faceStep f he]
    exact heApply
  have heSnd : e.snd = d.fst := by
    calc
      e.snd = (R.faceStep e).fst := (R.rotation_fst e.symm).symm
      _ = d.fst := congrArg (fun z : G.Dart ↦ z.fst) hfaceStep
  have hprev : H.Adj e.fst d.fst := by
    change w.toSubgraph.Adj e.fst d.fst
    rw [← heSnd]
    exact R.faceDart_adj_faceBoundaryWalk_toSubgraph f a e he
  have hnext : H.Adj d.fst d.snd := by
    exact R.faceDart_adj_faceBoundaryWalk_toSubgraph f a d hd
  have hne : e.fst ≠ d.snd := by
    intro heq
    have hedSymm : e = d.symm := by
      apply Dart.ext
      exact Prod.ext heq heSnd
    have hbad : R.faceStep e = e.symm := by
      rw [hfaceStep, hedSymm]
      simp
    exact R.faceStep_ne_symm_of_two_le_degree e (hdeg e.snd) hbad
  have hsubset : ({e.fst, d.snd} : Finset V) ⊆ (H.neighborSet d.fst).toFinset := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Set.mem_toFinset, Subgraph.mem_neighborSet]
    rcases hy with rfl | rfl
    · exact hprev.symm
    · exact hnext
  calc
    2 = ({e.fst, d.snd} : Finset V).card := by simp [hne]
    _ ≤ (H.neighborSet d.fst).toFinset.card := Finset.card_le_card hsubset
    _ = (H.neighborSet d.fst).ncard := by
      rw [Set.ncard_eq_toFinset_card']

/-- The subgraph traced by a complete facial boundary contains a genuine
cycle when the ambient graph has minimum degree at least two.  The proof is
the finite-tree leaf argument, so it also covers facial boundaries that
traverse bridges in both directions. -/
theorem faceBoundaryWalk_toSubgraph_not_isAcyclic
    (hdeg : ∀ v, 2 ≤ G.degree v) (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    ¬ (R.faceBoundaryWalk f a (R.faceLength f)).toSubgraph.coe.IsAcyclic := by
  classical
  let w := R.faceBoundaryWalk f a (R.faceLength f)
  let H := w.toSubgraph
  have haAdj : H.Adj a.1.fst a.1.snd := by
    change w.toSubgraph.Adj a.1.fst a.1.snd
    exact R.faceDart_adj_faceBoundaryWalk_toSubgraph f a a.1 a.2
  let u : H.verts := ⟨a.1.fst, haAdj.fst_mem⟩
  let v : H.verts := ⟨a.1.snd, haAdj.snd_mem⟩
  have huv : u ≠ v := by
    intro huv'
    exact a.1.fst_ne_snd (congrArg Subtype.val huv')
  letI : Nontrivial H.verts := nontrivial_iff.mpr ⟨u, v, huv⟩
  letI boundaryCoeNeighborFintype (z : H.verts) :
      Fintype (H.coe.neighborSet z) :=
    Subtype.fintype _
  intro hacyclic
  have htree : H.coe.IsTree := ⟨w.toSubgraph_connected.coe, hacyclic⟩
  obtain ⟨z, hz⟩ := htree.exists_vert_degree_one_of_nontrivial
  have hzTwoNcard : 2 ≤ (H.neighborSet z.1).ncard := by
    apply R.two_le_degree_faceBoundaryWalk_toSubgraph hdeg f a z.1
    exact z.2
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hz
  obtain ⟨y, hy, hyUnique⟩ := hz
  have hsubsingleton : (H.neighborSet z.1).Subsingleton := by
    intro x hx y' hy'
    have hxAdj : H.Adj z.1 x := hx
    have hyAdj : H.Adj z.1 y' := hy'
    let x' : H.verts := ⟨x, hxAdj.snd_mem⟩
    let y'' : H.verts := ⟨y', hyAdj.snd_mem⟩
    have hxCoe : H.coe.Adj z x' := hxAdj
    have hyCoe : H.coe.Adj z y'' := hyAdj
    exact congrArg Subtype.val
      ((hyUnique x' hxCoe).trans (hyUnique y'' hyCoe).symm)
  have hzOneNcard : (H.neighborSet z.1).ncard ≤ 1 :=
    Set.ncard_le_one_iff_subsingleton.mpr hsubsingleton
  omega

/-- A complete facial boundary in a minimum-degree-two graph contains an
ambient simple cycle no longer than that boundary. -/
theorem exists_cycle_length_le_faceLength_of_two_le_degree
    (hdeg : ∀ v, 2 ≤ G.degree v) (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) :
    ∃ (z : V) (c : G.Walk z z),
      c.IsCycle ∧ c.length ≤ R.faceLength f := by
  classical
  let w := R.faceBoundaryWalk f a (R.faceLength f)
  let H := w.toSubgraph
  have hnot : ¬ H.coe.IsAcyclic := by
    exact R.faceBoundaryWalk_toSubgraph_not_isAcyclic hdeg f a
  obtain ⟨z, c, hc, _⟩ :=
    (SimpleGraph.exists_egirth_eq_length (G := H.coe)).mpr hnot
  let q : G.Walk z.1 z.1 := c.map H.hom
  have hqCycle : q.IsCycle := hc.map H.hom_injective
  have hqEdges : q.edges ⊆ w.edges := by
    intro edge hedge
    change edge ∈ (c.map H.hom).edges at hedge
    rw [Walk.edges_map] at hedge
    obtain ⟨edge₀, hedge₀, rfl⟩ := List.mem_map.mp hedge
    have hedgeCoe : edge₀ ∈ H.coe.edgeSet := c.edges_subset_edgeSet hedge₀
    have hedgeH : Sym2.map (↑·) edge₀ ∈ H.edgeSet := by
      simpa only [Subgraph.edgeSet_coe, Set.mem_preimage] using hedgeCoe
    change Sym2.map (↑·) edge₀ ∈ w.edges
    rw [← Walk.mem_edges_toSubgraph]
    exact hedgeH
  refine ⟨z.1, q, hqCycle, ?_⟩
  calc
    q.length = q.edges.toFinset.card := by
      rw [List.toFinset_card_of_nodup hqCycle.isTrail.edges_nodup,
        Walk.length_edges]
    _ ≤ w.edges.toFinset.card := by
      apply Finset.card_le_card
      intro edge hedge
      rw [List.mem_toFinset] at hedge ⊢
      exact hqEdges hedge
    _ ≤ w.edges.length := List.toFinset_card_le w.edges
    _ = w.length := Walk.length_edges w
    _ = R.faceLength f := R.faceBoundaryWalk_length f a (R.faceLength f)

/-- Every face has length at least the ambient girth lower bound in a
minimum-degree-two graph, without any two-sidedness assumption on its darts.
This is the form needed both by the girth-twelve density argument and by the
girth-sixteen discharging argument. -/
theorem le_faceLength_of_two_le_degree
    (n : ℕ)
    (hdeg : ∀ v, 2 ≤ G.degree v)
    (hgirth : (n : ℕ∞) ≤ G.egirth) (f : R.Face) :
    n ≤ R.faceLength f := by
  let a : {d : G.Dart // d ∈ f.1.support} :=
    ⟨Classical.choose (R.face_isCycle f).nonempty_support,
      Classical.choose_spec (R.face_isCycle f).nonempty_support⟩
  obtain ⟨z, c, hc, hlen⟩ :=
    R.exists_cycle_length_le_faceLength_of_two_le_degree hdeg f a
  have hnE : (n : ℕ∞) ≤ (c.length : ℕ∞) :=
    (le_egirth.mp hgirth) z c hc
  have hn : n ≤ c.length := by
    exact_mod_cast hnE
  omega

/-- Every face has length at least sixteen under ambient girth sixteen and
minimum degree two, without any two-sidedness assumption on its darts. -/
theorem sixteen_le_faceLength_of_two_le_degree
    (hdeg : ∀ v, 2 ≤ G.degree v)
    (hgirth : (16 : ℕ∞) ≤ G.egirth) (f : R.Face) :
    16 ≤ R.faceLength f :=
  R.le_faceLength_of_two_le_degree 16 hdeg hgirth f

/-- A facial segment of at most four edges is a trail in a
minimum-degree-two graph.  Repeated oriented darts are excluded by the face
cycle, while a repeated unoriented edge would force either an immediate
reversal, a loop, or another immediate reversal within the four-edge
window. -/
theorem faceBoundaryWalk_isTrail_of_two_le_degree_of_le_four
    (hdeg : ∀ v, 2 ≤ G.degree v) (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (n : ℕ)
    (hnface : n ≤ R.faceLength f) (hnfour : n ≤ 4) :
    (R.faceBoundaryWalk f a n).IsTrail := by
  constructor
  rw [Walk.edges, R.faceBoundaryWalk_darts f a n, List.map_ofFn,
    List.nodup_ofFn]
  intro i j hedge
  rcases (dart_edge_eq_iff (R.faceDartAt f a i)
    (R.faceDartAt f a j)).mp hedge with hdart | hreverse
  · apply Fin.ext
    exact R.faceDartAt_injective_before_length f a
      (lt_of_lt_of_le i.isLt hnface) (lt_of_lt_of_le j.isLt hnface) hdart
  · have himpossible : ∀ (r s : Fin n), r.1 < s.1 →
        R.faceDartAt f a s = (R.faceDartAt f a r).symm → False := by
      intro r s hrs hsr
      have hcases : s.1 = r.1 + 1 ∨ s.1 = r.1 + 2 ∨ s.1 = r.1 + 3 := by
        omega
      rcases hcases with hstep | hstep | hstep
      · apply R.faceDartAt_succ_ne_symm hdeg f a r.1
        simpa only [hstep] using hsr
      · have hnext₁ := R.faceDartAt_succ_fst f a r.1
        have hnext₂ := R.faceDartAt_succ_fst f a (r.1 + 1)
        have hsrFst := congrArg (fun d : G.Dart ↦ d.fst) hsr
        have hloop : (R.faceDartAt f a (r.1 + 1)).snd =
            (R.faceDartAt f a (r.1 + 1)).fst := by
          calc
            (R.faceDartAt f a (r.1 + 1)).snd =
                (R.faceDartAt f a (r.1 + 2)).fst := hnext₂.symm
            _ = (R.faceDartAt f a s).fst := by rw [hstep]
            _ = (R.faceDartAt f a r).snd := hsrFst
            _ = (R.faceDartAt f a (r.1 + 1)).fst := hnext₁.symm
        exact (R.faceDartAt f a (r.1 + 1)).snd_ne_fst hloop
      · have hnext₁ := R.faceDartAt_succ_fst f a r.1
        have hnext₂ := R.faceDartAt_succ_fst f a (r.1 + 1)
        have hnext₃ := R.faceDartAt_succ_fst f a (r.1 + 2)
        have hsrFst := congrArg (fun d : G.Dart ↦ d.fst) hsr
        have hsnd : (R.faceDartAt f a (r.1 + 2)).snd =
            (R.faceDartAt f a (r.1 + 1)).fst := by
          calc
            (R.faceDartAt f a (r.1 + 2)).snd =
                (R.faceDartAt f a (r.1 + 3)).fst := hnext₃.symm
            _ = (R.faceDartAt f a s).fst := by rw [hstep]
            _ = (R.faceDartAt f a r).snd := hsrFst
            _ = (R.faceDartAt f a (r.1 + 1)).fst := hnext₁.symm
        have hrev : R.faceDartAt f a (r.1 + 2) =
            (R.faceDartAt f a (r.1 + 1)).symm := by
          apply Dart.ext
          exact Prod.ext hnext₂ hsnd
        exact R.faceDartAt_succ_ne_symm hdeg f a (r.1 + 1) hrev
    by_cases hij : i.1 < j.1
    · apply False.elim
      apply himpossible i j hij
      simpa using (congrArg Dart.symm hreverse).symm
    · by_cases hji : j.1 < i.1
      · exact False.elim (himpossible j i hji hreverse)
      · apply Fin.ext
        omega

/-- A facial segment of at most four edges is a path below girth five when
the ambient graph has minimum degree at least two. -/
theorem faceBoundaryWalk_isPath_of_two_le_degree_of_le_four
    (hdeg : ∀ v, 2 ≤ G.degree v) (f : R.Face)
    (a : {a : G.Dart // a ∈ f.1.support}) (n : ℕ)
    (hnface : n ≤ R.faceLength f) (hnfour : n ≤ 4)
    (hgirth : (5 : ℕ∞) ≤ G.egirth) :
    (R.faceBoundaryWalk f a n).IsPath := by
  have htrail := R.faceBoundaryWalk_isTrail_of_two_le_degree_of_le_four
    hdeg f a n hnface hnfour
  rw [htrail.isPath_iff_isSubwalk_imp_not_isCycle]
  intro v w hsub hcycle
  have hfiveE : (5 : ℕ∞) ≤ (w.length : ℕ∞) :=
    (le_egirth.mp hgirth) v w hcycle
  have hfive : 5 ≤ w.length := by
    exact_mod_cast hfiveE
  have hwle : w.length ≤ n := by
    simpa only [R.faceBoundaryWalk_length f a n] using
      Walk.length_le_of_isSubwalk hsub
  omega

/-- The short facial boundary paths required by the Section 4 density
argument follow from minimum degree two and girth sixteen alone, including
in the presence of bridges. -/
theorem faceShortBoundaryPaths_of_two_le_degree_of_girth_sixteen
    (hdeg : ∀ v, 2 ≤ G.degree v)
    (hgirth : (16 : ℕ∞) ≤ G.egirth) (f : R.Face) :
    R.FaceShortBoundaryPaths f := by
  have hface : 16 ≤ R.faceLength f :=
    R.sixteen_le_faceLength_of_two_le_degree hdeg hgirth f
  have hgirthFive : (5 : ℕ∞) ≤ G.egirth :=
    (by norm_num : (5 : ℕ∞) ≤ 16).trans hgirth
  intro a n hn
  refine ⟨R.faceVertexAt f a n, R.faceBoundaryWalk f a n, ?_,
    R.faceBoundaryWalk_length f a n, ?_⟩
  · exact R.faceBoundaryWalk_isPath_of_two_le_degree_of_le_four
      hdeg f a n (hn.trans (by omega : 4 ≤ R.faceLength f)) hn hgirthFive
  · intro i hi
    exact R.faceBoundaryWalk_getVert f a n i hi

end Finite

end RotationSystem

end

end LeanCo.PackingEdgeColoring
