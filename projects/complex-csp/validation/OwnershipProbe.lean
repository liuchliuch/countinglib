import Counting.ComplexCSP
import Lean
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let modules := env.header.moduleNames
  for moduleName in modules do
    if moduleName.toString.startsWith "ComplexCSP." || moduleName.toString.startsWith "Counting.ComplexCSP" then
      let some idx := env.getModuleIdx? moduleName | continue
      for name in env.header.moduleData[idx.toNat]!.constNames do
        if env.getModuleIdxFor? name != some idx then
          IO.println s!"SHARED {moduleName}: {name}: canonical={env.getModuleIdxFor? name |>.map (fun i => modules[i.toNat]!)} exists={env.contains name}"
