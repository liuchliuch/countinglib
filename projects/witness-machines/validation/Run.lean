import Counting.WitnessMachines.Clients
open Turing Counting.WitnessMachines
#eval Clients.machineChecks
#eval Clients.samples.length
#eval match (flip Option.bind (MappedReverse.machine (Sum.inr : Bool → Bool ⊕ Bool)).step)^[2]
    (some (initList (MappedReverse.machine (Sum.inr : Bool → Bool ⊕ Bool)) [false])) with
  | none => false
  | some c => c.l.isNone && (c.var == none) && ((show List Bool from c.stk .input) == []) &&
      ((show List (Bool ⊕ Bool) from c.stk .output) == [Sum.inr false])
#eval match (flip Option.bind (MappedReverse.machine (fun a : Bool ⊕ Bool => a.elim id id)).step)^[2]
    (some (initList (MappedReverse.machine (fun a : Bool ⊕ Bool => a.elim id id)) [Sum.inr true])) with
  | none => false
  | some c => c.l.isNone && (c.var == none) && ((show List (Bool ⊕ Bool) from c.stk .input) == []) &&
      ((show List Bool from c.stk .output) == [true])
