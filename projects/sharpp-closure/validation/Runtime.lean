import Counting.SharpPClosure.Clients

open Counting.Foundation Counting.SharpPClosure

def main : IO Unit := do
  let counts := [witnessCount 5 (paddedAccept 2 (fun bits => bits.any id)),
    witnessCount 5 (fun bits => (bits.take 2).any id),
    witnessCount 1 (paddedAccept 0 (fun _ => true)),
    witnessCount 0 (paddedAccept 0 (fun _ => true))]
  if Clients.boundaryChecks && counts == [3,24,1,1] then
    IO.println s!"padding boundary checks passed; exact/inflated/empty-prefix/zero-bit counts = {counts}"
  else
    throw (IO.userError s!"padding regression failed: {counts}")
