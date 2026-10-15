import Counting.Algorithm.ProductFinitePalette.Machine

import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  for name in env.header.moduleNames do
    let some idx := env.getModuleIdx? name | throwError "missing module"
    let data := env.header.moduleData[idx.toNat]!
    IO.println <| "MODULE " ++ (Json.mkObj [
      ("module", toJson name.toString),
      ("imports", toJson (data.imports.map (·.module.toString)))]).compress
