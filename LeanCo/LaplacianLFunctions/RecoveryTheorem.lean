import LeanCo.LaplacianLFunctions.JacobianFinite
import LeanCo.LaplacianLFunctions.VertexRecovery
import LeanCo.LaplacianLFunctions.LatticeTransport
import LeanCo.LaplacianLFunctions.RankRecovery

/-!
# Recovering Laplacian lattices from graph L-functions

This file assembles the end-to-end proof of Theorem 4.3 (and hence Theorem A)
of arXiv:2608.29981.  Equality of all character-twisted `L`-functions first
recovers the effective degree-one Picard classes by finite Fourier inversion.
Bridge-freeness identifies those classes with distinct vertices, producing a
vertex equivalence.  Finally, equality on the vertex basis identifies the
kernels of the two divisor-class maps, i.e. the two Laplacian lattices.

The conclusion is deliberately typed as an equality after transporting the
source lattice along the recovered vertex equivalence.  The two lattices live
in different free modules before that transport, so a raw equality would not
be well-typed.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V' V : Type*}
  [Fintype V'] [Nonempty V'] [DecidableEq V']
  [Fintype V] [Nonempty V] [DecidableEq V]

/-- **Theorem 4.3 / Theorem A, finite-Jacobian form.**

The recovered equivalence both matches the degree-one vertex classes under
Lemma 4.1's Picard transport and carries the source Laplacian lattice exactly
onto the target lattice. -/
theorem recover_laplacianLattice_of_lFunction_eq
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    [Fintype G'.Jacobian] [Fintype G.Jacobian]
    (hbridge' : G'.BridgeFree) (hbridge : G.BridgeFree)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (phi : G'.Jacobian ≃+ G.Jacobian)
    (hL : ∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁'
          (chi.compAddMonoidHom phi.toAddMonoidHom)) :
    ∃ sigma : V' ≃ V,
      (∀ v' : V',
        picardTransport G' G D₁' D₁ phi
            (G'.vertexClass v' : G'.Picard) =
          (G.vertexClass (sigma v') : G.Picard)) ∧
      Submodule.map (divisorReindex sigma).toLinearMap
          G'.laplacianLattice = G.laplacianLattice := by
  obtain ⟨sigma, hvertex⟩ :=
    G'.exists_vertexEquiv_of_lFunction_eq G hbridge' hbridge
      D₁' D₁ phi hL
  refine ⟨sigma, hvertex, ?_⟩
  exact G'.map_laplacianLattice_eq_of_picardEquiv G
    (picardTransport G' G D₁' D₁ phi) sigma hvertex

/-- Paper-facing form of Theorem 4.3.  Connectivity supplies the finiteness
of both Jacobians internally, so the visible mathematical assumptions are
exactly: finite nonempty loopless multigraphs, connectedness,
bridge-freeness, chosen degree-one classes, a Jacobian isomorphism, and
equality of all transported `L`-functions. -/
theorem recover_laplacianLattice_of_connected
    (G' : LooplessMultigraph V') (G : LooplessMultigraph V)
    (hconn' : G'.Connected) (hconn : G.Connected)
    (hbridge' : G'.BridgeFree) (hbridge : G.BridgeFree)
    (D₁' : G'.PicardDegree 1) (D₁ : G.PicardDegree 1)
    (phi : G'.Jacobian ≃+ G.Jacobian) :
    letI : Fact G'.Connected := ⟨hconn'⟩
    letI : Fact G.Connected := ⟨hconn⟩
    (∀ chi : AddChar G.Jacobian ℂ,
      G.lFunction D₁ chi =
        G'.lFunction D₁'
          (chi.compAddMonoidHom phi.toAddMonoidHom)) →
      ∃ sigma : V' ≃ V,
        (∀ v' : V',
          picardTransport G' G D₁' D₁ phi
              (G'.vertexClass v' : G'.Picard) =
            (G.vertexClass (sigma v') : G.Picard)) ∧
        Submodule.map (divisorReindex sigma).toLinearMap
            G'.laplacianLattice = G.laplacianLattice := by
  letI : Fact G'.Connected := ⟨hconn'⟩
  letI : Fact G.Connected := ⟨hconn⟩
  intro hL
  exact G'.recover_laplacianLattice_of_lFunction_eq G
    hbridge' hbridge D₁' D₁ phi hL

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
