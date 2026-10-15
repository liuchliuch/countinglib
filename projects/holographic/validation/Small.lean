import Counting.Algorithm.Holographic
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  for m in modules do
    if m.toString.startsWith "Holant." || m.toString.startsWith "Paper" ||
        (m.toString.splitOn "Classification").length > 1 then
      throwError "Unexpected flagship dependency in the small semantic API: {m}"
  IO.println s!"SMALL_API_OK imported_modules={modules.size} no_Holant_no_Paper_no_Classification"
