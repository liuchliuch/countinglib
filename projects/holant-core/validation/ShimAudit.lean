import Holant.Signature
import Holant.Tensor
import Holant.Network
import Counting.Upstream.HolantSignature
import Counting.Upstream.HolantTensor
import Counting.Upstream.HolantNetwork
import Counting.Bridge.Holant
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  for moduleName in #[`Counting.Upstream.HolantSignature,
      `Counting.Upstream.HolantTensor, `Counting.Upstream.HolantNetwork] do
    let some idx := env.getModuleIdx? moduleName
      | throwError "Missing shim: {moduleName}"
    let data := env.header.moduleData[idx.toNat]!
    let owned := env.constants.fold (init := 0) fun count name _ =>
      if env.getModuleIdxFor? name == some idx then count + 1 else count
    unless owned == 0 && data.constNames.isEmpty && data.extraConstNames.isEmpty do
      throwError "Shim exports declarations: {moduleName}"
    IO.println <| "SHIM_OK " ++ (Json.mkObj [
      ("module", toJson moduleName.toString),
      ("kernel_declarations", toJson owned),
      ("module_constant_names", toJson data.constNames.size),
      ("module_extra_names", toJson data.extraConstNames.size)]).compress

#check Holant.Signature
#check Holant.Network.denote
