import Counting.Bridge.OpenNetwork
import Lean.Elab.Command

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  for m in modules do
    if m.toString.startsWith "Holant.OpenNetworkComposition" || m.toString.startsWith "Paper" ||
        (m.toString.splitOn "Classification").length > 1 then
      throwError "Unexpected heavy dependency in the raw bridge: {m}"
  IO.println s!"SMALL_API_OK imported_modules={modules.size} no_Composition_no_Paper_no_Classification"
