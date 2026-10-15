import Counting.CookLevin.Clients

open Counting.CookLevin Counting.CookLevin.Clients

def main : IO Unit := do
  let samples := [binaryNor, chained, unusedWitness, repeatedInput,
    constantTrue, constantFalse, missingOutput, largeReferences]
  let counts := samples.map Instance.count
  unless counts == [1,1,2,2,1,0,0,1] do
    throw (IO.userError s!"unexpected target counts: {counts}")
  unless accept (binaryNor, [false,false,false,false]) &&
      !(accept (binaryNor, [false,false,false,true])) do
    throw (IO.userError "padding behavior differs")
  unless samples.all (fun c => Instance.encoding.decode (Instance.encoding.encode c) == some c) do
    throw (IO.userError "codec roundtrip differs")
  IO.println s!"NOR_RUNTIME_OK {counts}"

#eval main
