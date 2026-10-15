import Counting.Reduction.OneQuery.Clients

open PlanarHom.Complexity
open Counting.Reduction.OneQuery

def flipObserved (b : Bool) : Option Bits :=
  let m := PlanarHom.ArithmeticCircuitPrimitives.unaryMachine BitEncoding.bool Bool.not
  (m.step (Turing.initList m [b])).map (fun c => c.stk ())

def clearObserved (xs : Bits) : Option Bits :=
  let m := PlanarHom.ConstantMachines.machine []
  ((fun c : Option m.Cfg => c.bind m.step)^[xs.length + 1]
    (some (Turing.initList m xs))).map (fun c => c.stk ())

-- Execute the source primitives used by the proven compiler, and independently
-- evaluate the canonical count-answer words. The generic finite restriction and
-- oracle substitution objects are noncomputable proof-carrying structures;
-- their complete transition runs are kernel-proved in Clients, not #eval'd here.
#eval do
  let observations := [flipObserved false, flipObserved true,
    clearObserved [], clearObserved [true, false, true]]
  if observations != [some [true], some [false], some [], some []] then
    throw (IO.userError s!"primitive transition mismatch: {observations}")
  let answers := [(problem BitEncoding.bool (fun b => if b then 1 else 0)).value [true],
    (problem BitEncoding.bool (fun b => if b then 1 else 0)).value [false],
    (problem BitEncoding.bits (fun _ => 0)).value []]
  if answers != [[true], [], []] then
    throw (IO.userError s!"canonical count encoding mismatch: {answers}")
  IO.println s!"ONE_QUERY_RUNTIME_OK {observations} {answers}"
