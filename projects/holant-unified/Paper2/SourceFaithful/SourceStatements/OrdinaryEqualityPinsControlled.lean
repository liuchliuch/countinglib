import Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPinsControlledStages

/-! The source Theorem 3.5 ordinary pin programme with complete actual query
and answer length control, specialized to the fixed K basis and a supplied
higher equality. The original ordinary target and palette identifications
are those proved in OrdinaryEqualityPinsSource. -/
namespace Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPinsControlled
open Paper2.ExactInput Paper2.Complexity Paper2.Paper1Proved
open Paper2.Tractable Paper2.Synthesis
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.TetrahedralCompletion
open OrdinaryEqualityPinsSource
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (L : Language) {d : ℕ} (hd : 4≤d)
variable (heq : (⟨d,DegreeCSP.equality (K:=AlgebraicComplex) d⟩ :
  Paper2.AnySignature AlgebraicComplex)∈L.family)

/-- The full controlled interpretation of the frozen actual stage chain.
It calls the original language in its actual coefficient-field codec. -/
def programme := OrdinaryEqualityPinsControlledStages.topControlled
  (table L) (anchor L hd heq)

/-- The source answer bound is derived from the actual two-pin physical
palette tables, including arbitrary occurrences of both unary rows. -/
def sourceOutputBound := outputBound
  (OrdinaryBothPins.Source.outputBound (table L) (anchor L hd heq))

/-- Every actual external query is a valid original-language input and has
the composed polynomial bit-length bound of the executed stage sequence. -/
theorem query_valid_and_length
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle
      (QuaternaryAnchorAccess.targetEncoding (s:=(inverseKLanguage L).count)
        (a:=(inverseKLanguage L).arity))
      (QuaternaryAnchorAccess.GOT.originalPresentation (table L)).encoding
      (QuaternaryAnchorAccess.GOT.originalValue (table L)) oracle)
    (r : OrdinaryBothPins.Source.Input (table L) (anchor L hd heq))
    (t : ℕ) (c : (programme L hd heq).reduction.machine.Cfg)
    (hrun : (programme L hd heq).reduction.machine.run oracle
      ((OrdinaryBothPins.Source.inputEncoding (table L) (anchor L hd heq)).encode r) t=some c)
    (hquery : (programme L hd heq).reduction.machine.IsQuery c) :
    ∃q,c.stk (programme L hd heq).reduction.machine.queryStack=
        (QuaternaryAnchorAccess.targetEncoding (s:=(inverseKLanguage L).count)
          (a:=(inverseKLanguage L).arity)).encode q ∧
      (c.stk (programme L hd heq).reduction.machine.queryStack).length≤
        (programme L hd heq).queryBound.eval
          ((OrdinaryBothPins.Source.inputEncoding (table L) (anchor L hd heq)).encode r).length :=
  (programme L hd heq).safeQuery oracle ho r t c hrun hquery

/-- The actual original-field answer bytes encountered by the programme
are polynomially bounded in the original two-pin input bytes. -/
theorem answer_length_le
    (oracle : List Bool→List Bool)
    (ho : RepresentsOracle
      (QuaternaryAnchorAccess.targetEncoding (s:=(inverseKLanguage L).count)
        (a:=(inverseKLanguage L).arity))
      (QuaternaryAnchorAccess.GOT.originalPresentation (table L)).encoding
      (QuaternaryAnchorAccess.GOT.originalValue (table L)) oracle)
    (r : OrdinaryBothPins.Source.Input (table L) (anchor L hd heq))
    (t : ℕ) (c : (programme L hd heq).reduction.machine.Cfg)
    (hrun : (programme L hd heq).reduction.machine.run oracle
      ((OrdinaryBothPins.Source.inputEncoding (table L) (anchor L hd heq)).encode r) t=some c)
    (hquery : (programme L hd heq).reduction.machine.IsQuery c) :
    (oracle (c.stk (programme L hd heq).reduction.machine.queryStack)).length≤
      ((programme L hd heq).targetOutput.bound.comp (programme L hd heq).queryBound).eval
        ((OrdinaryBothPins.Source.inputEncoding (table L) (anchor L hd heq)).encode r).length :=
  (programme L hd heq).answer_length_le oracle ho r t c hrun hquery

end
end Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPinsControlled

