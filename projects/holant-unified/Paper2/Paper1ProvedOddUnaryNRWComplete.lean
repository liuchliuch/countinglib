import Paper2.Paper1ProvedOddUnaryNRWDispatch
import Paper2.Paper1ProvedOddUnaryNRThreeSlicesGraph

/-! The complete sourced isotropic-W resource theorem. The actual minimum
is unary or ternary; the ternary's proved support obstruction exits by a
literal ordinary self-loop, and the resulting real unary supplies the same
Jordan graph receipt as the unary minimum. -/
namespace Paper2.Paper1Proved.OddUnary
open Paper2.ExactInput
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IsotropicWSource

/-- Every sourced isotropic W obstruction produces a genuine nonscalar
Jordan binary over its retained original finite table and coefficient field.
No outside-class or successful-descent premise remains at this endpoint. -/
theorem jordan_receipt {L : Language} (S : IsotropicWSource L) :
    Nonempty (NRCanonical.JordanReceipt (H:=S.source.H) S.source.K.subtype) := by
  rcases NRCanonical.source_exits S with jordan|⟨R,v,C,⟨T⟩⟩
  · exact jordan
  · obtain ⟨U,outside⟩ := NRCanonical.ThreeSlicesGraph.exists_outside_graph
      (K:=S.source.K) (r:=S.source.count) (b:=S.source.arity) (H:=S.source.H)
      (R:=R) (v:=v)
      S.source.K.subtype C T.graph T.outside T.slices
    exact NRUnaryExit.jordan_receipt
      (K:=S.source.K) (r:=S.source.count) (a:=S.source.arity) (H:=S.source.H)
      (phi:=S.source.K.subtype) (R0:=R) (v:=v) C U outside

end IsotropicWSource

namespace Source

/-- The original ordinary nonisotropic unary branch closes every structural
case except the actual Jordan interpolation resource. All hard arms already
have the canonical original-language output contract. -/
theorem hard_or_jordan (L : Language)
    (U : GeneralOddHighTerminalAccess.Actual (signatures L) 1)
    (hn : GeneralOddNonisotropicFrame.norm U.graph.denote≠0)
    (hnot : ¬Paper2.Tractable.Tract L.family)
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted) :
    FixedFieldOutput.SharpPHard .ordinary L ∨
      ∃ S : IsotropicWSource L,
        Nonempty (NRCanonical.JordanReceipt (H:=S.source.H) S.source.K.subtype) := by
  rcases Paper2.Paper1Proved.OddUnary.Source.hard_or_isotropic_w
      L U hn hnot P PG PR PF PN with hard|source
  · exact Or.inl hard
  · obtain ⟨S⟩ := source
    exact Or.inr ⟨S,S.jordan_receipt⟩

end Source
end
end Paper2.Paper1Proved.OddUnary

