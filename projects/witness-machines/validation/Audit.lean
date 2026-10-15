import Counting.WitnessMachines.Clients
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Compiler.Old

set_option maxHeartbeats 0

/-!
# Witness representation machine declaration audit

The package inventory is generated from its exact Lake module ownership by
`scripts/verify.py`. Audit module ownership, including private declarations,
full declaration types, and all transitive axiom dependencies. This harness is
adapted from the S1 audit, maintaining the same allowed logical axioms.
-/

open Lean Elab Command

private def auditKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

run_cmd do
  let some sourceText ← IO.getEnv "COUNTING_AUDIT_MODULES"
    | throwError "Missing source inventory. Run python3 scripts/verify.py."
  let sourceModules := (sourceText.splitOn "\n").filter (· != "")
  if sourceModules.isEmpty then
    throwError "The local library source inventory is empty."
  let env := (← getEnv).setExporting false
  let importedModules := env.header.moduleNames
  -- Check the aggregator's own dependency graph, not merely the audit file's imports.
  let mut closure : Array Name := #[`Counting.WitnessMachines.Clients]
  let mut cursor : Nat := 0
  while cursor < closure.size do
    let moduleName := closure[cursor]!
    let some moduleIdx := env.getModuleIdx? moduleName
      | throwError "Missing imported module data: {moduleName}"
    for dependency in env.header.moduleData[moduleIdx.toNat]!.imports do
      unless closure.contains dependency.module do
        closure := closure.push dependency.module
    cursor := cursor + 1
  for sourceModule in sourceModules do
    unless closure.any (fun n => n.toString == sourceModule) do
      throwError "Local source module is absent from the witness-machines acceptance import closure: {sourceModule}"
  let ownedModules : Array Name := importedModules.filter fun n =>
    sourceModules.contains n.toString
  let declarations := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if ownedModules.contains importedModules[idx.toNat]! then names.push name
      else names
    | none => names
  let declarations := declarations.qsort Name.lt
  if declarations.isEmpty then
    throwError "No declarations found in local library modules."
  -- Cross-check each module's exported constant inventory; never silently omit a name.
  let mut codegenCount : Nat := 0
  for moduleName in ownedModules do
    let some idx := env.getModuleIdx? moduleName
      | throwError "Missing owned module: {moduleName}"
    let data := env.header.moduleData[idx.toNat]!
    for name in data.constNames do
      unless declarations.contains name do
        throwError "Module-owned declaration was not enumerated: {moduleName}: {name}"
    for name in data.extraConstNames do
      unless declarations.contains name do
        codegenCount := codegenCount + 1
        IO.println <| "AUDIT_CODEGEN " ++ (Json.mkObj [
          ("name", toJson name.toString), ("module", toJson moduleName.toString),
          ("kind", toJson "compiler_auxiliary_without_kernel_declaration")]).compress
    IO.println <| "AUDIT_MODULE " ++ (Json.mkObj [
      ("name", toJson moduleName.toString),
      ("kernel_declarations", toJson <| (declarations.filter fun name =>
        env.getModuleIdxFor? name == some idx).size),
      ("module_constant_names", toJson data.constNames.size),
      ("module_extra_names", toJson data.extraConstNames.size)]).compress
  let some basicIdx := env.getModuleIdx? `PlanarHom.Basic
    | throwError "Missing Basic shim"
  unless env.header.moduleData[basicIdx.toNat]!.constNames.isEmpty do
    throwError "PlanarHom.Basic must remain a zero-declaration shim"
  for entry in #[`Counting.WitnessMachines.MappedReverse, `Counting.WitnessMachines.TaggedToFramed,
      `Counting.WitnessMachines.FramedToTagged, `Counting.Bridge.WitnessSharpP,
      `Counting.WitnessMachines.Clients] do
    let mut actual := #[entry]
    let mut pos := 0
    while pos < actual.size do
      let some idx := env.getModuleIdx? actual[pos]!
        | throwError "Missing module in dependency traversal"
      for dependency in env.header.moduleData[idx.toNat]!.imports do
        unless actual.contains dependency.module do
          actual := actual.push dependency.module
      pos := pos + 1
    let localModules := actual.filter fun name =>
      name.toString.startsWith "Counting." || name.toString.startsWith "Holant." ||
        name.toString.startsWith "PlanarHom."
    for moduleName in actual do
      if moduleName.toString.startsWith "Paper" ||
          (moduleName.toString.splitOn ".").contains "Classification" then
        throwError "Algorithm entry imports a classification module: {moduleName}"
    IO.println <| "AUDIT_CLOSURE " ++ (Json.mkObj [
      ("entry", toJson entry.toString), ("modules", toJson actual.size),
      ("local_modules", toJson <| localModules.map Name.toString)]).compress
  let allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theoremCount : Nat := 0
  let mut axiomCount : Nat := 0
  let mut privateCount : Nat := 0
  let mut failureCount : Nat := 0
  let mut recursiveAuxCount : Nat := 0
  for name in declarations do
    let some info := env.find? name
      | throwError "Enumerated declaration is unavailable: {name}"
    let some idx := env.getModuleIdxFor? name
      | throwError "Enumerated declaration has no module ownership: {name}"
    let mut recursiveAuxParent : Option Name := none
    if info.isUnsafe || info.isPartial then
      let some parent := Compiler.isUnsafeRecName? name
        | throwError "Unrecognized unsafe or partial owned declaration: {name}"
      let some parentInfo := env.find? parent
        | throwError "Generated recursive auxiliary has no safe parent: {name}"
      if parentInfo.isUnsafe || parentInfo.isPartial || info.type != parentInfo.type ||
          env.getModuleIdxFor? parent != some idx then
        throwError "Invalid safe parent for recursive auxiliary: {name}"
      recursiveAuxParent := some parent
      recursiveAuxCount := recursiveAuxCount + 1
    if info.isTheorem then theoremCount := theoremCount + 1
    if info.isAxiom then axiomCount := axiomCount + 1
    if isPrivateName name then privateCount := privateCount + 1
    let axioms ← Lean.collectAxioms name
    let fullType ← liftTermElabM do
      withOptions (fun options => options.setBool `pp.all true
        |>.setBool `pp.privateNames true
        |>.set `pp.maxSteps (10000000 : Nat)
        |>.set `maxRecDepth (10000 : Nat)) do
        return (← Meta.ppExpr info.type).pretty 120
    if fullType.contains '⋯' then
      throwError "Pretty printer omitted part of a type: {name}"
    IO.println <| "AUDIT_DECL " ++ (Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson importedModules[idx.toNat]!.toString),
      ("kind", toJson <| auditKind info),
      ("private", toJson <| isPrivateName name),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
      ("compiler_recursive_auxiliary_parent", toJson <| recursiveAuxParent.map Name.toString),
      ("direct_constants", toJson <| info.getUsedConstantsAsSet.toArray.map Name.toString),
      ("universe_parameters", toJson <| info.levelParams.map Name.toString),
      ("type", toJson fullType),
      ("axioms", toJson <| axioms.map Name.toString)]).compress
    for axiomName in axioms do
      unless allowedAxioms.contains axiomName do
        failureCount := failureCount + 1
        logError m!"Disallowed transitive axiom: {name} depends on {axiomName}"
  if axiomCount != 0 then
    throwError "Local library declares {axiomCount} new axioms."
  if failureCount != 0 then
    throwError "Axiom audit failed with {failureCount} disallowed dependencies."
  if theoremCount == 0 then
    throwError "No theorem declarations found; refusing an empty proof audit."
  IO.println <| "AUDIT_SUMMARY " ++ (Json.mkObj [
    ("modules", toJson ownedModules.size), ("declarations", toJson declarations.size),
    ("theorems", toJson theoremCount), ("private_declarations", toJson privateCount),
    ("compiler_auxiliaries_without_kernel_declarations", toJson codegenCount),
    ("compiler_recursive_auxiliaries", toJson recursiveAuxCount),
    ("local_axioms", toJson axiomCount), ("disallowed_dependencies", toJson failureCount),
    ("allowed_axioms", toJson <| allowedAxioms.map Name.toString)]).compress
  IO.println s!"AUDIT_OK modules={ownedModules.size} declarations={declarations.size} theorems={theoremCount} local_axioms={axiomCount} allowed=[propext, Classical.choice, Quot.sound]"
