import Lean

/-! Source-header inventory using the same import parser as Lake. This supplies
build inputs only; the private-environment audit independently checks the compiled
import closure and actual kernel declarations. -/
open Lean

def main (args : List String) : IO UInt32 := do
  try
    let [requestFile, outputFile] := args
      | throw <| IO.userError "Usage: ImportGraph.lean REQUEST_JSON OUTPUT_JSONL"
    let request ← IO.ofExcept <| Json.parse (← IO.FS.readFile requestFile)
    let entries : Array (String × String) ← IO.ofExcept <| fromJson? request
    let output ← IO.FS.Handle.mk outputFile .write
    for (name, path) in entries do
      let header ← Lean.parseImports' (← IO.FS.readFile path) path
      output.putStrLn <| (Json.mkObj [("module", toJson name),
        ("imports", toJson <| header.imports.map (·.module.toString))]).compress
    output.flush
    IO.println s!"IMPORT_GRAPH_OK modules={entries.size}"
    return 0
  catch error =>
    IO.eprintln s!"IMPORT_GRAPH_ERROR {error}"
    return 1
