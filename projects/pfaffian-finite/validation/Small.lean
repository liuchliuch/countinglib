import Counting.FiniteSupport
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  for m in modules do
    let s := m.toString
    if s.startsWith "PfaffianPort." || s.startsWith "Counting.Algorithm.Pfaffian" ||
        s.startsWith "PlanarHom.SharpP" || s.startsWith "PlanarHom.Nondeterministic" ||
        (s.splitOn "Classification").length > 1 || s.startsWith "Holant.Paper" then
      throwError "Unexpected application or classification dependency in small interface: {m}"
  IO.println s!"SMALL_API_OK imported_modules={modules.size} canonical_PlanarHom_compiler_no_Pfaffian_no_SharpP_no_Classification"
