import Lean

/-!
Unified all-declaration audit, adapted from the H1 audit. This verification tool is outside the production library.

Imports compiled production modules at private visibility, enumerates by source-module
ownership, and inspects actual kernel types and bodies. Dependency exploration is
shared between declarations. A reverse-edge fixed point propagates each reachable
axiom through cycles without the incomplete-cache problem of naive recursive DFS.
No source-text or declaration-name heuristic selects mathematical declarations.
-/

open Lean

namespace CountingUnifiedAudit

private def allowedAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def bodyConstants (info : ConstantInfo) : Array Name :=
  match info with
  | .inductInfo value => value.ctors.toArray
  | .recInfo value => value.rules.foldl (fun acc rule => acc ++ rule.rhs.getUsedConstants) #[]
  | _ => (info.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]

private def directConstants (info : ConstantInfo) : Array Name := Id.run do
  let mut names : Std.HashSet Name := {}
  for name in info.type.getUsedConstants do names := names.insert name
  for name in bodyConstants info do names := names.insert name
  return names.toArray.qsort Name.lt

private def jsonLine (handle : IO.FS.Handle) (fields : List (String × Json)) : IO Unit :=
  handle.putStrLn (Json.mkObj fields).compress

private def moduleOf (env : Environment) (name : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? name
    | throw <| IO.userError s!"Kernel declaration has no source-module ownership: {name}"
  return env.header.moduleNames[idx.toNat]!

private def propagate (parents : Array (Array Nat)) (seeds : Array (Nat × Name)) :
    Array (Array Name) := Id.run do
  let mut answer := Array.replicate parents.size (#[] : Array Name)
  for (seed, axiomName) in seeds do
    let mut pending := #[seed]
    let mut cursor := 0
    answer := answer.modify seed (·.push axiomName)
    while cursor < pending.size do
      for parent in parents[pending[cursor]!]! do
        unless answer[parent]!.contains axiomName do
          answer := answer.modify parent (·.push axiomName)
          pending := pending.push parent
      cursor := cursor + 1
  return answer.map (·.qsort Name.lt)

private def selfTest : IO Unit := do
  -- a -> b -> a, b -> c, c is an axiom: both cycle nodes must inherit c.
  let parents := #[#[1], #[0], #[1], #[]]
  let result := propagate parents #[(2, `syntheticAxiom)]
  unless result == #[#[`syntheticAxiom], #[`syntheticAxiom], #[`syntheticAxiom], #[]] do
    throw <| IO.userError "Cycle propagation self-test failed"
  -- Independent axioms and a shared dependent must remain distinguished.
  let result := propagate #[#[2], #[2], #[]] #[(0, `a), (1, `b)]
  unless result == #[#[`a], #[`b], #[`a, `b]] do
    throw <| IO.userError "Multi-axiom propagation self-test failed"
  let rejected := propagate #[#[1], #[]] #[(0, `sorryAx)]
  unless rejected[1]! == #[`sorryAx] && !(rejected[1]!.all allowedAxioms.contains) do
    throw <| IO.userError "Synthetic forbidden-axiom propagation/rejection self-test failed"
  IO.println "AUDIT_ALGORITHM_SELFTEST_OK"

private def audit (requestFile outputPrefix : String) : IO UInt32 := do
  let requestText ← IO.FS.readFile requestFile
  let request ← IO.ofExcept <| Json.parse requestText
  let sourceNames : Array String ← IO.ofExcept <| request.getObjValAs? (Array String) "modules"
  let allNames : Array String ← IO.ofExcept <| request.getObjValAs? (Array String) "all_local_modules"
  let rootNames : Array String ← IO.ofExcept <| request.getObjValAs? (Array String) "roots"
  let arts : NameMap ImportArtifacts ← IO.ofExcept <| request.getObjValAs? (NameMap ImportArtifacts) "import_artifacts"
  let sourceSet : Std.HashSet Name := Std.HashSet.ofArray <| sourceNames.map String.toName
  let allSet : Std.HashSet Name := Std.HashSet.ofArray <| allNames.map String.toName
  if sourceSet.isEmpty || sourceSet.size != sourceNames.size || rootNames.isEmpty then
    throw <| IO.userError "Source module inventory is empty or contains duplicates, or roots are empty"
  IO.println s!"AUDIT_IMPORT roots={rootNames} expected_modules={sourceSet.size}"
  initSearchPath (← findSysroot)
  let env := (← importModules (rootNames.map fun root => { module := root.toName }) {}
    (loadExts := false) (level := .private) (leakEnv := true) (arts := arts)).setExporting false
  let mut actual : Std.HashSet Name := {}
  let mut moduleIndices : Array (Name × ModuleIdx) := #[]
  for name in env.header.moduleNames do
    if allSet.contains name then
      actual := actual.insert name
      let some idx := env.getModuleIdx? name
        | throw <| IO.userError s!"Imported source module has no index: {name}"
      moduleIndices := moduleIndices.push (name, idx)
  for name in sourceSet do
    unless actual.contains name do
      throw <| IO.userError s!"Expected source module absent from actual import closure: {name}"
  for name in actual do
    unless sourceSet.contains name do
      throw <| IO.userError s!"Source module omitted from production inventory: {name}"
  -- Emit the complete actual environment closure, including external modules, so
  -- the driver can pin every artifact that was available to this audit.
  let closureFile ← IO.FS.Handle.mk (outputPrefix ++ "-closure.jsonl") .write
  for name in env.header.moduleNames do
    jsonLine closureFile [("name", toJson name.toString),
      ("production_owned", toJson <| sourceSet.contains name)]
  closureFile.flush
  let ownedIndices : Std.HashSet Nat := Std.HashSet.ofArray <| moduleIndices.map (·.2.toNat)
  let declarations := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if ownedIndices.contains idx.toNat then acc.push name else acc
    | none => acc
  let declarations := declarations.qsort Name.lt
  if declarations.isEmpty then throw <| IO.userError "No source-owned kernel declarations found"
  let declarationSet := Std.HashSet.ofArray declarations
  let mut counts : Std.HashMap Nat Nat := {}
  for name in declarations do
    let some idx := env.getModuleIdxFor? name | throw <| IO.userError s!"Missing owner: {name}"
    counts := counts.insert idx.toNat (counts.getD idx.toNat 0 + 1)
  let modulesFile ← IO.FS.Handle.mk (outputPrefix ++ "-modules.jsonl") .write
  let codegenFile ← IO.FS.Handle.mk (outputPrefix ++ "-codegen.jsonl") .write
  let reexportsFile ← IO.FS.Handle.mk (outputPrefix ++ "-reexports.jsonl") .write
  let mut codegenCount := 0
  let mut reexportCount := 0
  let mut externalExports : Std.HashMap Name (Array Json) := {}
  for (name, idx) in moduleIndices.qsort (fun a b => Name.lt a.1 b.1) do
    let data := env.header.moduleData[idx.toNat]!
    let mut moduleKernelExports := 0
    let mut moduleExternalExports := 0
    let mut moduleCodegen := 0
    for (pool, entries) in #[("constNames", data.constNames), ("extraConstNames", data.extraConstNames)] do
      for declName in entries do
        match env.checked.get.find? declName with
        | none =>
          if pool == "constNames" then
            throw <| IO.userError s!"Module constant unavailable in kernel: {name}: {declName}"
          codegenCount := codegenCount + 1
          moduleCodegen := moduleCodegen + 1
          jsonLine codegenFile [("name", toJson declName.toString),
            ("module", toJson name.toString),
            ("kind", toJson "compiler_auxiliary_without_kernel_declaration")]
        | some _ =>
          moduleKernelExports := moduleKernelExports + 1
          let canonicalOwner ← moduleOf env declName
          let isSourceOwned := sourceSet.contains canonicalOwner
          if isSourceOwned then
            unless declarationSet.contains declName do
              throw <| IO.userError s!"Source-owned exported kernel constant omitted: {name}: {declName}"
          else
            -- Generated auxiliaries may be exported compatibly by production and
            -- dependency modules. Keep their external canonical ownership, and add
            -- them as independent axiom-audit roots even when no source proof uses them.
            moduleExternalExports := moduleExternalExports + 1
            let exporter := Json.mkObj [("module", toJson name.toString), ("pool", toJson pool)]
            externalExports := externalExports.insert declName
              ((externalExports.getD declName #[]).push exporter)
          unless canonicalOwner == name do
            reexportCount := reexportCount + 1
            jsonLine reexportsFile [("name", toJson declName.toString),
              ("exporting_module", toJson name.toString), ("export_pool", toJson pool),
              ("canonical_owner", toJson canonicalOwner.toString),
              ("production_owned", toJson isSourceOwned)]
    jsonLine modulesFile [("name", toJson name.toString),
      ("kernel_declarations", toJson <| counts.getD idx.toNat 0),
      ("module_constant_names", toJson data.constNames.size),
      ("module_extra_names", toJson data.extraConstNames.size),
      ("exported_kernel_entries", toJson moduleKernelExports),
      ("exported_external_kernel_entries", toJson moduleExternalExports),
      ("compiler_only_entries", toJson moduleCodegen)]
  modulesFile.flush
  codegenFile.flush
  reexportsFile.flush
  let externalDeclarations := externalExports.keysArray.qsort Name.lt
  let auditRoots := declarations ++ externalDeclarations
  IO.println s!"AUDIT_ENUMERATED modules={actual.size} declarations={declarations.size} external_export_roots={externalDeclarations.size}"
  let mut names := auditRoots
  let mut indices : Std.HashMap Name Nat := {}
  for i in [:names.size] do indices := indices.insert names[i]! i
  let mut parents := Array.replicate names.size (#[] : Array Nat)
  let mut seeds : Array (Nat × Name) := #[]
  let mut cursor := 0
  let mut edgeCount := 0
  while cursor < names.size do
    let name := names[cursor]!
    let some info := env.checked.get.find? name
      | throw <| IO.userError s!"Referenced kernel constant unavailable: {name}"
    if info.isAxiom then seeds := seeds.push (cursor, name)
    for dependency in directConstants info do
      let depIndex ← match indices[dependency]? with
        | some index => pure index
        | none => do
          let index := names.size
          names := names.push dependency
          indices := indices.insert dependency index
          parents := parents.push #[]
          pure index
      parents := parents.modify depIndex (·.push cursor)
      edgeCount := edgeCount + 1
    cursor := cursor + 1
    if cursor % 50000 == 0 then
      IO.println s!"AUDIT_GRAPH visited={cursor} discovered={names.size} edges={edgeCount}"
  IO.println s!"AUDIT_GRAPH_COMPLETE nodes={names.size} edges={edgeCount} axioms={seeds.size}"
  let axioms := propagate parents seeds
  let declarationsFile ← IO.FS.Handle.mk (outputPrefix ++ "-declarations.jsonl") .write
  let externalFile ← IO.FS.Handle.mk (outputPrefix ++ "-external-declarations.jsonl") .write
  let axiomsFile ← IO.FS.Handle.mk (outputPrefix ++ "-axioms.jsonl") .write
  let mut localAxioms := 0
  let mut failures := 0
  let mut privateCount := 0
  let mut theoremCount := 0
  let mut unsafeCount := 0
  let mut partialCount := 0
  let mut observed : Std.HashSet Name := {}
  let mut externalFailures := 0
  for i in [:auditRoots.size] do
    let name := auditRoots[i]!
    let isSourceOwned := i < declarations.size
    let some info := env.checked.get.find? name
      | throw <| IO.userError s!"Enumerated kernel constant unavailable: {name}"
    if isSourceOwned then
      if info.isAxiom then localAxioms := localAxioms + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if isPrivateName name then privateCount := privateCount + 1
      if info.isUnsafe then unsafeCount := unsafeCount + 1
      if info.isPartial then partialCount := partialCount + 1
    for axiomName in axioms[i]! do
      observed := observed.insert axiomName
      unless allowedAxioms.contains axiomName do
        failures := failures + 1
        unless isSourceOwned do externalFailures := externalFailures + 1
    let fields := [("name", toJson name.toString),
      ("module", toJson (← moduleOf env name).toString), ("kind", toJson <| kind info),
      ("private", toJson <| isPrivateName name), ("unsafe", toJson info.isUnsafe),
      ("partial", toJson info.isPartial),
      ("universe_parameters", toJson <| info.levelParams.map Name.toString),
      ("type_representation", toJson "Lean.Expr structural hash"),
      ("type_hash", toJson <| toString info.type.hash),
      ("body_hash", toJson <| (info.value? (allowOpaque := true)).map (toString ∘ Expr.hash)),
      ("type_dependencies", toJson <| (info.type.getUsedConstants.qsort Name.lt).map Name.toString),
      ("body_dependencies", toJson <| (bodyConstants info).map Name.toString),
      ("axioms", toJson <| axioms[i]!.map Name.toString)]
    if isSourceOwned then
      jsonLine declarationsFile fields
    else
      jsonLine externalFile (fields ++ [("production_exporters", toJson <| externalExports.getD name #[]),
        ("scope", toJson "external canonical owner; independently audited production-exported kernel declaration")])
  for (_, name) in seeds do
    let sourceModule ← moduleOf env name
    jsonLine axiomsFile [("name", toJson name.toString), ("module", toJson sourceModule.toString),
      ("production_owned", toJson <| sourceSet.contains sourceModule),
      ("permitted", toJson <| allowedAxioms.contains name)]
  declarationsFile.flush
  externalFile.flush
  axiomsFile.flush
  let passed := localAxioms == 0 && failures == 0 && theoremCount > 0
  let summary := Json.mkObj [("schema_version", toJson (2 : Nat)),
    ("status", toJson <| if passed then "passed" else "failed"),
    ("roots", toJson rootNames), ("modules", toJson actual.size),
    ("declarations", toJson declarations.size), ("theorems", toJson theoremCount),
    ("external_export_declarations", toJson externalDeclarations.size),
    ("audited_kernel_roots", toJson auditRoots.size),
    ("external_export_disallowed_dependencies", toJson externalFailures),
    ("private_declarations", toJson privateCount), ("unsafe_declarations", toJson unsafeCount),
    ("partial_declarations", toJson partialCount),
    ("compiler_auxiliaries_without_kernel_declarations", toJson codegenCount),
    ("compatible_repeated_source_exports", toJson reexportCount),
    ("local_axioms", toJson localAxioms), ("disallowed_dependencies", toJson failures),
    ("dependency_graph_nodes", toJson names.size), ("dependency_graph_edges", toJson edgeCount),
    ("allowed_axioms", toJson <| allowedAxioms.map Name.toString),
    ("observed_axioms", toJson <| (observed.toArray.qsort Name.lt).map Name.toString),
    ("ownership_selection", toJson "actual source module index, all kernel declarations"),
    ("dependency_method", toJson "private kernel types/bodies; shared graph; reverse-edge axiom fixed point"),
    ("visibility", toJson "OLeanLevel.private, setExporting false"),
    ("expression_hash_note", toJson "Lean structural hashes are inventory fingerprints, not cryptographic hashes or proof certificates")]
  IO.FS.writeFile (outputPrefix ++ "-summary.json") (summary.pretty ++ "\n")
  IO.println ("AUDIT_SUMMARY " ++ summary.compress)
  return if passed then 0 else 1

end CountingUnifiedAudit

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--self-test"] => CountingUnifiedAudit.selfTest; return 0
    | [request, output] => CountingUnifiedAudit.audit request output
    | _ =>
      IO.eprintln "Usage: scripts/lake env lean --run validation/Audit.lean REQUEST_JSON OUTPUT_PREFIX"
      return 2
  catch error =>
    IO.eprintln s!"AUDIT_ERROR {error}"
    return 1
