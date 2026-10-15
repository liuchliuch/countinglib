import Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPinsSource
import Paper2.Paper1ProvedComplexity
import Paper2.Complexity.ControlledCompose

/-! The concrete frozen ordinary pin stages, interpreted with full query
control at every composition. Each primitive stage carries its actual valid
query and fixed-field answer length proof; the terminal is the original
language coefficient field. No generic PolyTime-to-control inference is used. -/
namespace Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPinsControlledStages
open Paper2.Paper1Proved Paper2.Complexity
open Holant Holant.Tractable Holant.Complexity.UniversalPairReduction
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.TetrahedralCompletion
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Holant.Signature AlgebraicComplex (a i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (FiniteFamily.family G))
local instance : Algebra ℚ (OrdinaryBothPins.Single.K G A) :=
  (OrdinaryBothPins.Single.K G A).algebra'
local instance : CharZero (OrdinaryBothPins.Single.K G A) :=
  Algebra.charZero_of_charZero ℚ (OrdinaryBothPins.Single.K G A)

/-- The actual ordinary equality template, edge-scale and original-field
answer converter, with their independently proved query certificates. -/
def anchorControlled :=
  (controlledReduction (QuaternaryAnchorAccess.edgeControlled G A)).controlledCompose
    ((controlledReduction (QuaternaryAnchorAccess.basisControlled G A)).controlledCompose
      ((controlledReduction (QuaternaryAnchorAccess.macroControlled G A)).controlledCompose
        (controlledReduction (QuaternaryAnchorAccess.originalControlled G A))))

def companionControlled (j : Bool) :=
  (controlledReduction (QuaternaryOrdinaryCompanion.anchorControlled G A j)).controlledCompose
    (anchorControlled G A)

def replicationControlled (j : Bool) :=
  (controlledReduction (OrdinaryReplication.anchorControlled s a G A j)).controlledCompose
    (companionControlled G A j)

/-- A real unary prefix returns to its pair base before the actual pair and
companion programmes are inlined. The same old ordinary labels survive. -/
def unaryNativeControlled (j : Bool) :=
  (controlledReduction (OrdinaryUnaryAccess.factorControlled G A j)).controlledCompose
    ((controlledReduction (OrdinaryUnaryAccess.pairControlled G A j)).controlledCompose
      (replicationControlled G A j))

def unaryControlled (j : Bool) :=
  (controlledReduction (OrdinaryUnaryAccess.paletteControlled G A j)).controlledCompose
    ((controlledReduction (OrdinaryUnaryAccess.ordinaryControlled G A j)).controlledCompose
      (unaryNativeControlled G A j))

/-- The second unary caller treats the first unary as an old physical row,
then calls its already controlled programme. -/
def pairControlled :=
  (controlledReduction (OrdinaryBothPins.pairPrefix G A)).controlledCompose
    ((controlledReduction (OrdinaryBothPins.companionPrefix G A)).controlledCompose
      (unaryControlled G A false))

def internalControlled :=
  (controlledReduction (OrdinaryBothPins.ordinaryControlled G A)).controlledCompose
    ((controlledReduction (OrdinaryBothPins.factorControlled G A)).controlledCompose
      ((controlledReduction (OrdinaryBothPins.nativePairControlled G A)).controlledCompose
        (pairControlled G A)))

/-- The full executed ordinary two-pin palette to the original language.
Its queryBound is the composition of the literal stage query polynomials. -/
def topControlled :=
  (controlledReduction (OrdinaryBothPins.Source.paletteControlled G A)).controlledCompose
    (internalControlled G A)

end
end Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPinsControlledStages

