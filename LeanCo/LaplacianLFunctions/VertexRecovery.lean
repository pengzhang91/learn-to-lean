import LeanCo.LaplacianLFunctions.LFunction
import LeanCo.LaplacianLFunctions.PicardSplitting
import LeanCo.LaplacianLFunctions.Connectivity
import Mathlib.Tactic

/-!
# Recovering the vertex bijection from graph L-functions

This file is the Fourier-to-vertices step in Theorem 4.3 of
arXiv:2608.29981.  Equality of every character-twisted `L`-function recovers
the indicator of effective degree-one divisor classes.  Those classes are
exactly the vertex classes.  Bridge-freeness makes the two vertex-class maps
injective, so the resulting correspondence is a genuine equivalence of
vertex types.

The proof treats both directions of effective-class preservation.  In
particular, surjectivity of the recovered vertex map is proved by applying the
same indicator identity to the inverse image of a target degree-one class;
it is not inferred merely from injectivity.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V' V : Type*}
  [Fintype V'] [Nonempty V'] [DecidableEq V']
  [Fintype V] [Nonempty V] [DecidableEq V]

/-- Recombining the Jacobian coordinate of a degree-one class with degree one
recovers the class. -/
@[simp]
theorem classInDegree_one_jacobianCoordinate
    (G : LooplessMultigraph V) (D₁ : G.PicardDegree 1)
    (C : G.PicardDegree 1) :
    G.classInDegree D₁ 1 (G.jacobianCoordinate D₁ (C : G.Picard)) =
      (C : G.Picard) := by
  rw [classInDegree]
  simpa [C.2] using
    G.jacobianCoordinate_add_degree D₁ (C : G.Picard)

/-- On a degree-one slice, `picardTransport` is `classInDegree` in the
transported Jacobian coordinate. -/
theorem picardTransport_degree_one_eq_classInDegree
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (phi : G'.Jacobian ≃+ G.Jacobian) (C : G'.PicardDegree 1) :
    picardTransport G' G D₁' D₁ phi (C : G'.Picard) =
      G.classInDegree D₁ 1
        (phi (G'.jacobianCoordinate D₁' (C : G'.Picard))) := by
  rw [picardTransport_apply, classInDegree, C.2]

/-- The degree-one Picard transport preserves, in both directions, the
property of being a vertex class.  This is the exact set-level information
extracted from the `t¹u⁰` coefficients. -/
theorem exists_vertexClass_picardDegreeTransport_iff_of_lFunction_eq
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    [Fintype G'.Jacobian] [Fintype G.Jacobian]
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (phi : G'.Jacobian ≃+ G.Jacobian)
    (hL : ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁'
          (chi.compAddMonoidHom phi.toAddMonoidHom))
    (C : G'.PicardDegree 1) :
    (∃ v' : V', C = G'.vertexClass v') ↔
      ∃ v : V,
        picardDegreeTransport G' G D₁' D₁ phi 1 C =
          G.vertexClass v := by
  let a' : G'.Jacobian :=
    G'.jacobianCoordinate D₁' (C : G'.Picard)
  have hindicator :=
    G.degreeOneEffectiveIndicator_transport_of_lFunction_eq
      G' D₁ D₁' phi hL a'
  have hsourceClass :
      G'.classInDegree D₁' 1 a' = (C : G'.Picard) := by
    exact G'.classInDegree_one_jacobianCoordinate D₁' C
  have htargetClass :
      G.classInDegree D₁ 1 (phi a') =
        (picardDegreeTransport G' G D₁' D₁ phi 1 C : G.Picard) := by
    rw [picardDegreeTransport_coe]
    exact (G'.picardTransport_degree_one_eq_classInDegree
      G D₁' D₁ phi C).symm
  constructor
  · intro hsourceVertex
    have hsourcePos : 0 < G'.h (C : G'.Picard) :=
      (G'.h_pos_degree_one_iff_vertexClass C).2 hsourceVertex
    have hsourceIndicator :
        G'.degreeOneEffectiveIndicator D₁' a' = 1 := by
      apply (G'.degreeOneEffectiveIndicator_eq_one_iff D₁' a').2
      simpa [hsourceClass] using hsourcePos
    have htargetIndicator :
        G.degreeOneEffectiveIndicator D₁ (phi a') = 1 := by
      rw [hindicator]
      exact hsourceIndicator
    have htargetPos :
        0 < G.h
          (picardDegreeTransport G' G D₁' D₁ phi 1 C : G.Picard) := by
      have := (G.degreeOneEffectiveIndicator_eq_one_iff
        D₁ (phi a')).1 htargetIndicator
      simpa [htargetClass] using this
    exact (G.h_pos_degree_one_iff_vertexClass
      (picardDegreeTransport G' G D₁' D₁ phi 1 C)).1 htargetPos
  · intro htargetVertex
    have htargetPos :
        0 < G.h
          (picardDegreeTransport G' G D₁' D₁ phi 1 C : G.Picard) :=
      (G.h_pos_degree_one_iff_vertexClass
        (picardDegreeTransport G' G D₁' D₁ phi 1 C)).2
          htargetVertex
    have htargetIndicator :
        G.degreeOneEffectiveIndicator D₁ (phi a') = 1 := by
      apply (G.degreeOneEffectiveIndicator_eq_one_iff D₁ (phi a')).2
      simpa [htargetClass] using htargetPos
    have hsourceIndicator :
        G'.degreeOneEffectiveIndicator D₁' a' = 1 := by
      rw [← hindicator]
      exact htargetIndicator
    have hsourcePos : 0 < G'.h (C : G'.Picard) := by
      have := (G'.degreeOneEffectiveIndicator_eq_one_iff D₁' a').1
        hsourceIndicator
      simpa [hsourceClass] using this
    exact (G'.h_pos_degree_one_iff_vertexClass C).1 hsourcePos

/-- **Vertex-recovery theorem.**  Equality of all transported graph
`L`-functions produces a bijection of vertices under which the Picard
transport sends every source vertex class to its target vertex class. -/
theorem exists_vertexEquiv_of_lFunction_eq
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    [Fintype G'.Jacobian] [Fintype G.Jacobian]
    (hbridge' : G'.BridgeFree) (hbridge : G.BridgeFree)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (phi : G'.Jacobian ≃+ G.Jacobian)
    (hL : ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁'
          (chi.compAddMonoidHom phi.toAddMonoidHom)) :
    ∃ sigma : V' ≃ V, ∀ v' : V',
      picardTransport G' G D₁' D₁ phi
          (G'.vertexClass v' : G'.Picard) =
        (G.vertexClass (sigma v') : G.Picard) := by
  let T : G'.PicardDegree 1 ≃ G.PicardDegree 1 :=
    picardDegreeTransport G' G D₁' D₁ phi 1
  have hclassIff : ∀ C : G'.PicardDegree 1,
      (∃ v' : V', C = G'.vertexClass v') ↔
        ∃ v : V, T C = G.vertexClass v := by
    intro C
    exact G'.exists_vertexClass_picardDegreeTransport_iff_of_lFunction_eq
      G D₁' D₁ phi hL C
  have hforward : ∀ v' : V',
      ∃ v : V, T (G'.vertexClass v') = G.vertexClass v := by
    intro v'
    exact (hclassIff (G'.vertexClass v')).1 ⟨v', rfl⟩
  choose f hf using hforward
  have hf_injective : Function.Injective f := by
    intro v₁' v₂' hv
    apply G'.vertexClass_injective_of_bridgeFree hbridge'
    apply T.injective
    rw [hf v₁', hf v₂', hv]
  have hf_surjective : Function.Surjective f := by
    intro v
    let C : G'.PicardDegree 1 := T.symm (G.vertexClass v)
    have htarget : ∃ w : V, T C = G.vertexClass w := by
      refine ⟨v, ?_⟩
      simp [C]
    obtain ⟨v', hv'⟩ := (hclassIff C).2 htarget
    refine ⟨v', ?_⟩
    apply G.vertexClass_injective_of_bridgeFree hbridge
    calc
      G.vertexClass (f v') = T (G'.vertexClass v') := (hf v').symm
      _ = T C := congrArg T hv'.symm
      _ = G.vertexClass v := by simp [C]
  let sigma : V' ≃ V := Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  refine ⟨sigma, ?_⟩
  intro v'
  have hclasses := congrArg Subtype.val (hf v')
  simpa [T, sigma] using hclasses

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
