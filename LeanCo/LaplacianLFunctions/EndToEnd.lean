import LeanCo.LaplacianLFunctions.AbelJacobi
import LeanCo.LaplacianLFunctions.ArtinObstruction
import LeanCo.LaplacianLFunctions.BridgeContraction
import LeanCo.LaplacianLFunctions.Example310
import LeanCo.LaplacianLFunctions.Examples
import LeanCo.LaplacianLFunctions.RecoveryTheorem
import LeanCo.LaplacianLFunctions.GraphInvariants
import LeanCo.LaplacianLFunctions.LFunctionBaseChange
import LeanCo.LaplacianLFunctions.LFunctionPolynomial
import LeanCo.LaplacianLFunctions.LowGenusExamples
import LeanCo.LaplacianLFunctions.PicardRankTransport
import LeanCo.LaplacianLFunctions.Proposition38
import LeanCo.LaplacianLFunctions.RiemannRochBridge
import LeanCo.LaplacianLFunctions.RiemannRochConsequences
import LeanCo.LaplacianLFunctions.SaturatedReconstruction
import LeanCo.LaplacianLFunctions.Zeta
import LeanCo.LaplacianLFunctions.ZetaIntegralBaseChange
import LeanCo.LaplacianLFunctions.ZetaRationality
import LeanCo.LaplacianLFunctions.ZetaTransport

/-!
# End-to-end entry point for arXiv:2608.29981

Importing this module exposes the paper's multigraph/divisor foundations,
the Abel--Jacobi Theorems 2.8 and 2.9, bridge-contraction invariance from
Proposition 3.5, the two-variable zeta and character-twisted `L`-functions,
the rationality and character dichotomy of Propositions 3.3 and 3.8, finite
Fourier rank recovery, the integral-to-complex zeta base change, the
genus-one obstruction of Remark 3.11, Lemmas 4.1
and 4.2, and the fully assembled Theorem
4.3 / Theorem A in `recover_laplacianLattice_of_connected`.  It also exposes
the generic low-genus formulas and the explicit certificates for Examples
3.10 and 4.6.
-/

namespace LeanCo.LaplacianLFunctions

noncomputable section

namespace LooplessMultigraph

variable {V' V : Type*}
  [Fintype V'] [Nonempty V'] [DecidableEq V']
  [Fintype V] [Nonempty V] [DecidableEq V]

/-- Labib--Lei, Theorem A / Theorem 4.3. -/
theorem labibLei_theorem_A
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
            G'.laplacianLattice = G.laplacianLattice :=
  G'.recover_laplacianLattice_of_connected G hconn' hconn hbridge' hbridge
    D₁' D₁ phi

end LooplessMultigraph

end

end LeanCo.LaplacianLFunctions
