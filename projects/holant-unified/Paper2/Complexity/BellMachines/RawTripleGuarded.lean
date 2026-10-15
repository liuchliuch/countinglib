import Paper2.Complexity.BellMachines.RawTripleValidated

/-! Executable threshold and guarded raw surgery. The threshold reads only
literal row labels. Invalid raw inputs are still processed by the finite program;
valid input closure is proved separately below. -/
namespace Paper2.Complexity.BellMachines.RawTriple
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler Paper2.Problem Paper2.ExactInput
open Paper2.BellReduction.RawOccurrence Paper2.BellReduction.RawTripleBridge
set_option maxRecDepth 8192
noncomputable section

def hasThree (G : RawClosedNetwork) : Bool := decide (3 ≤ markedCount G.vertices)

theorem third_flag (xs : List RawVertex) :
    (xs.map (fun _ => true)).getD 2 false = decide (3 ≤ xs.length) := by
  rcases xs with _ | ⟨a,xs⟩
  · rfl
  rcases xs with _ | ⟨b,xs⟩
  · rfl
  rcases xs with _ | ⟨c,xs⟩
  · rfl
  simp

def hasThreeComputes : Computes rawEncoding encodingBoolBool hasThree := by
  let prepare := pairComputes (constantComputes rawEncoding encodingBoolBool false) markedComputes
  let cell := constantComputes (pairEncoding encodingBoolBool RawClosedNetwork.vertexEncoding)
    encodingBoolBool true
  let flags := prepare.andThen (Lists.mapListComputes encodingBoolBool
    RawClosedNetwork.vertexEncoding encodingBoolBool (fun _ _ => true) cell)
  exact congrComputes (flags.andThen (getDComputes encodingBoolBool 2 false))
    (fun G => third_flag (marked G))

def guarded (coreLabel : ℕ) (G : RawClosedNetwork) : RawClosedNetwork :=
  if hasThree G then transform coreLabel G else G

def guardedComputes (coreLabel : ℕ) : Computes rawEncoding rawEncoding (guarded coreLabel) :=
  Lists.ifComputes hasThreeComputes (computes coreLabel) (identityComputes rawEncoding)

theorem guarded_wellFormed {G : RawClosedNetwork} {s : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s 1 arity) (hzero : arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < s) (ha : arity coreLabel = 8) :
    (guarded coreLabel G).WellFormed s 1 arity := by
  unfold guarded hasThree
  split
  next h => exact machine_wellFormed hG hzero (of_decide_eq_true h) coreLabel hl ha
  next => exact hG

def guardedValid (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (G : Instance L) : Instance L :=
  ⟨guarded coreLabel G.val, guarded_wellFormed G.property hzero coreLabel hl ha⟩

def guardedValidComputes (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8) :
    Computes (inputEncoding L) (inputEncoding L) (guardedValid L hzero coreLabel hl ha) :=
  recode (guardedComputes coreLabel) Subtype.val (fun _ => rfl) (fun _ => rfl)

end
end Paper2.Complexity.BellMachines.RawTriple
