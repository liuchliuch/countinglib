import Lean

/-! Read-only compatibility check against an already built library baseline.
The explicit artifact map respects separate providers sharing `Counting`.
This tool does not compile or modify another package. -/
open Lean

def main (args : List String) : IO UInt32 := do
  try
    let [artifactFile, outputFile] := args
      | throw <| IO.userError "Usage: JointImport.lean ARTIFACTS_JSON OUTPUT_JSON"
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile artifactFile)
    let arts : NameMap ImportArtifacts ← IO.ofExcept <| fromJson? json
    initSearchPath (← findSysroot)
    let env := (← importModules #[{module := `Counting.Library}, {module := `Counting.MatchgateWidth}]
      {} (loadExts := false) (level := .private) (leakEnv := true) (arts := arts)).setExporting false
    let shared := #[`finProdFinEquiv.eq_1, `Fin.cast.eq_1, `Fin.castAdd.eq_1,
      `Fin.castLE.eq_1, `Counting.Model.Occurrence.eval.eq_1,
      `Counting.Model.OpenInstance.partition.congr_simp,
      `Counting.Model.OpenInstance.partition.eq_1]
    let mut rows : Array Json := #[]
    for name in shared do
      let some info := env.checked.get.find? name
        | throw <| IO.userError s!"Missing shared generated declaration: {name}"
      let some idx := env.getModuleIdxFor? name
        | throw <| IO.userError s!"Missing canonical ownership: {name}"
      rows := rows.push <| Json.mkObj [("name", toJson name.toString),
        ("canonical_owner", toJson env.header.moduleNames[idx.toNat]!.toString),
        ("type_hash", toJson <| toString info.type.hash),
        ("body_hash", toJson <| (info.value? (allowOpaque := true)).map (toString ∘ Expr.hash))]
    let output := Json.mkObj [("status", toJson "passed"),
      ("roots", toJson #["Counting.Library", "Counting.MatchgateWidth"]),
      ("imported_modules", toJson env.header.moduleNames.size),
      ("shared_generated_declarations", toJson rows)]
    IO.FS.writeFile outputFile (output.pretty ++ "\n")
    IO.println output.compress
    return 0
  catch error =>
    IO.eprintln s!"JOINT_IMPORT_ERROR {error}"
    return 1
