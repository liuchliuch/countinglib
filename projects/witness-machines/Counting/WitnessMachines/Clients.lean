import Counting.Bridge.WitnessSharpP

/-! Concrete machine executions and a public witness → accepting paths → public
witness round trip. The two choices at each witness bit remain distinct paths. -/
namespace Counting.WitnessMachines.Clients
open Turing Computability PlanarHom.Complexity
open Counting.Bridge.WitnessSharpP

/-- Inspect the entire final configuration of the actual tagged-input machine. -/
def taggedCheck (left right : Bits) : Bool :=
  let result := (flip Option.bind TaggedToFramed.machine.step)^[3 * left.length + 2 * right.length + 4]
    (some (initList TaggedToFramed.machine (left.map Sum.inl ++ right.map Sum.inr)))
  match result with
  | none => false
  | some c => c.l.isNone && (c.var == (none, none)) &&
      ((show List (Bool ⊕ Bool) from c.stk .input) == []) &&
      ((show Bits from c.stk .scratch) == []) &&
      ((show Bits from c.stk .output) == BitEncoding.frame left ++ right)

/-- Inspect the entire final configuration of the actual framed-input machine. -/
def framedCheck (left right : Bits) : Bool :=
  let result := (flip Option.bind FramedToTagged.machine.step)^[2 * left.length + 2 * right.length + 3]
    (some (initList FramedToTagged.machine (BitEncoding.frame left ++ right)))
  match result with
  | none => false
  | some c => c.l.isNone && (c.var == (none, none)) &&
      ((show Bits from c.stk .input) == []) &&
      ((show List (Bool ⊕ Bool) from c.stk .scratch) == []) &&
      ((show List (Bool ⊕ Bool) from c.stk .output) == left.map Sum.inl ++ right.map Sum.inr)

def samples : List (Bits × Bits) :=
  [([], []), ([], [true, false]), ([false, true], []),
   ([true, false], [false, true]), ([false], [false]), ([true], [true]),
   (List.replicate 5 false, [true, false, true]), ([true, true, false], List.replicate 6 false)]

def machineChecks : Bool := samples.all (fun pair =>
  taggedCheck pair.1 pair.2 && framedCheck pair.1 pair.2)

theorem empty_tagged_execution : taggedCheck [] [] = true := by decide
theorem empty_framed_execution : framedCheck [] [] = true := by decide
theorem mixed_tagged_execution : taggedCheck [true, false] [false, true] = true := by decide
theorem mixed_framed_execution : framedCheck [true, false] [false, true] = true := by decide

noncomputable def lengthPolynomial : Polynomial ℕ := Polynomial.X + 1

/-- A real finite accepting constant verifier supplies the input F1 witness. -/
noncomputable def exponentialWitness :
    Counting.Complexity.SharpPWitness (encodingList Bool) (fun x => 2 ^ (x.length + 1)) := by
  simpa [lengthPolynomial, encodingList] using
    Counting.Complexity.allWitnesses (encodingList Bool) lengthPolynomial

/-- The reverse representation compiler and actual binary-choice generator are
both exercised by this explicit exponential-path machine. -/
noncomputable def exponentialMachine : PolynomialNondeterministicMachine :=
  witnessAcceptingMachine exponentialWitness

theorem exponentialMachine_count (x : Bits) : exponentialMachine.count x = 2 ^ (x.length + 1) :=
  witnessAcceptingMachine_count exponentialWitness x

/-- Replay this concrete machine and convert its verifier back to the F1 format. -/
noncomputable def replayedWitness :
    Counting.Complexity.SharpPWitness (encodingList Bool) exponentialMachine.count :=
  acceptingMachineWitness exponentialMachine

theorem replayedWitness_count (x : Bits) :
    Fintype.card {w : Fin (replayedWitness.witnessLength.eval x.length) → Bool //
      replayedWitness.accept (x, List.ofFn w) = true} = 2 ^ (x.length + 1) :=
  (replayedWitness.counts x).symm.trans (exponentialMachine_count x)

theorem exponential_membership_via_compilers :
    Counting.Complexity.InSharpP (encodingList Bool) (fun x : Bits => 2 ^ (x.length + 1)) :=
  (bits_inSharpP_iff_acceptingPaths _).mpr
    ⟨exponentialMachine, fun x => (exponentialMachine_count x).symm⟩

end Counting.WitnessMachines.Clients
