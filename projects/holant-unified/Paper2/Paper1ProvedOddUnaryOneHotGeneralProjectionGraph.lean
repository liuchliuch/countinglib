import Paper2.Paper1ProvedOddUnaryOneHotLineVisibility
import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionGeneral
import Paper2.Paper1ProvedOddUnaryJordanProductProjectionGraph

/-! The higher-arity outside-matching source supplies an actual nonsingular
binary breaking the fixed line. All specialization caps are adjoined in
the unchanged coefficient field by executed Jordan interpolation. -/
namespace Paper2.Paper1Proved.OddUnary.IsotropicWSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.TractChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {L : Paper2.ExactInput.Language} (S : IsotropicWSource L)

/-- No projection, interpolation, or smaller-arity classification premise
is supplied. Primality and failure of the fixed matching criterion are
the concrete mathematical data of the original-table source selector. -/
theorem outside_prime_projection {m : ℕ}
    (N : NoXOrdinaryGraphAdjoin.Output S.source.H (m+2))
    (prime : Prime (⟨m+2,N.network.denote⟩ : Holant.AnySignature S.source.K))
    (u : Bool→S.source.K) (opposite : Bool)
    (c : AlgebraicComplex) (cnz : c≠0)
    (form : ∀v,S.source.K.subtype (u v)=
      c*(TensorDecisionMatching.basis opposite).matrix v false)
    (outside : ¬matchingImage opposite (m+2)
      (RingHomRealization.mapSignature S.source.K.subtype N.network.denote)) :
    letI : Algebra ℚ S.source.K := S.source.K.algebra'
    ∃V:List (Bool→S.source.K),
      ∃ E : JordanUnaryAccess.FamilyExtension S.source.F S.source.H V,
        ∃ Q : NoXOrdinaryGraphAdjoin.Output E.signatures 2,
          OneHotBinaryProjection.determinant (fun b d=>Q.network.denote ![b,d])≠0 ∧
          OneHotLineProjection.line u (fun b d=>Q.network.denote ![b,d])≠0 := by
  letI : Algebra ℚ S.source.K := S.source.K.algebra'
  obtain ⟨p,y,live⟩:=OneHotLineVisibility.visible_weighted_pair S.source.K.subtype
    N.network.denote u opposite c cnz form outside
  have hp : Prime (⟨m+2,Tensor.reindex p N.network.denote⟩ : Holant.AnySignature S.source.K) :=
    GlobalCloseCompletionC2Q4PrimeTools.prime_reindex _ prime p
  obtain ⟨z,det,line⟩:=OneHotBinaryProjection.last_two_linear_projection
    (Tensor.reindex p N.network.denote) hp (fun i j=>u i*u j) ⟨y,live⟩
  obtain ⟨E,Q,formQ⟩:=S.polynomial_matrix_projection N p z
  have matrix : (fun b d=>Q.network.denote ![b,d])=
      OneHotBinaryProjection.orderedProductProjection (Tensor.reindex p N.network.denote) z := by
    funext b d
    exact formQ b d
  refine ⟨List.ofFn (JordanProjectionGraph.covectors z),E,Q,?_,?_⟩
  · rwa [matrix]
  · rwa [matrix,OneHotLineVisibility.line_eq_weighted]

end
end Paper2.Paper1Proved.OddUnary.IsotropicWSource

