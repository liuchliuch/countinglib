import Counting.Algorithm.KarpLubyRequest.Whole.Runtime
namespace Counting.Algorithm.KarpLubyRequest.Whole.Runtime
open Turing Holant.Complexity BinaryCompose
#eval IO.eprintln "RUNTIME_PROBE start"
#eval stackCount
#eval IO.eprintln "RUNTIME_PROBE count done"
#eval @BEq.beq State stateBEq initial initial
#eval IO.eprintln "RUNTIME_PROBE state done"
def probeStart : TM2.Cfg (fun _ : Stack => Bool) Label State :=
  ⟨some main, initial, @wordTape Stack stackDecidable input []⟩
#eval (@TM2.step Stack (fun _ => Bool) Label State stackDecidable program probeStart).isSome
#eval IO.eprintln "RUNTIME_PROBE first step done"
end Counting.Algorithm.KarpLubyRequest.Whole.Runtime
