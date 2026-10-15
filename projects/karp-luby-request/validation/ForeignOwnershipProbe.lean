import Counting.Algorithm.KarpLubyRequest
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import validation.RecursiveAuxiliary

/-! Full production-module ownership and transitive-axiom audit. -/

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let imported := env.header.moduleNames
  let owned := imported.filter fun moduleName =>
    moduleName == `Counting.Algorithm.KarpLubyRequest ||
      moduleName.toString.startsWith "Counting.Algorithm.KarpLubyRequest."
  IO.println <| "AUDIT_IMPORTS " ++ (toJson <| imported.map Name.toString).compress
  IO.println <| "AUDIT_OWNED " ++ (toJson <| owned.map Name.toString).compress
  let declarations := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if owned.contains imported[idx.toNat]! then names.push name else names
    | none => names
  let declarations := declarations.qsort Name.lt
  let mut auxiliaryNames : Array Name := #[]
  let mut auxiliaryOccurrences := 0
  let mut kernelReexports := 0
  for moduleName in owned do
    let some idx := env.getModuleIdx? moduleName
      | throwError "Missing module: {moduleName}"
    let data := env.header.moduleData[idx.toNat]!
    for name in data.constNames do
      unless declarations.contains name do
        throwError "Omitted module-owned declaration: {name}"
    for name in data.extraConstNames do
      unless declarations.contains name do
        match env.find? name with
        | some _ =>
          kernelReexports := kernelReexports + 1
          let owner := match env.getModuleIdxFor? name with
            | some ix => imported[ix.toNat]!.toString
            | none => "<local>"
          IO.println <| "AUDIT_REEXPORT " ++ (Json.mkObj [
            ("name", toJson name.toString), ("exported_by", toJson moduleName.toString),
            ("canonical_kernel_owner", toJson owner)]).compress
        | none =>
          auxiliaryOccurrences := auxiliaryOccurrences + 1
          unless auxiliaryNames.contains name do auxiliaryNames := auxiliaryNames.push name
          IO.println <| "AUDIT_AUX " ++ (Json.mkObj [
            ("name", toJson name.toString), ("exported_by", toJson moduleName.toString)]).compress
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theoremCount := 0
  let mut privateCount := 0
  let mut unsafeCount := 0
  let mut partialCount := 0
  let mut generatedRecursiveCount := 0
  let mut unexpectedPartialCount : Nat := 0
  let mut foreignPublicCount : Nat := 0
  for name in (declarations.push ``Nat.add) do
    let publicOwner := name.toString.startsWith "Counting.Algorithm.KarpLubyRequest."
    let privateOwner := name.toString.startsWith "_private.Counting.Algorithm.KarpLubyRequest."
    unless publicOwner || privateOwner do
      foreignPublicCount := foreignPublicCount + 1
      IO.println <| "AUDIT_FOREIGN " ++ (Json.mkObj [("name", toJson name.toString),
        ("owner", toJson <| imported[(env.getModuleIdxFor? name).get!.toNat]!.toString)]).compress
    let some info := env.find? name | throwError "Missing declaration: {name}"
    if info.isAxiom then throwError "New local axiom: {name}"
    if info.isUnsafe then unsafeCount := unsafeCount + 1
    let mut recursiveParent : Option Name := none
    let mut partialError : Option String := none
    if info.isPartial then
      partialCount := partialCount + 1
      match KarpLubyRequestAudit.recursiveAuxiliaryParent env name with
      | .ok parent =>
        recursiveParent := some parent
        generatedRecursiveCount := generatedRecursiveCount + 1
      | .error reason =>
        partialError := some reason
        unexpectedPartialCount := unexpectedPartialCount + 1
    if info.isTheorem then theoremCount := theoremCount + 1
    if isPrivateName name then privateCount := privateCount + 1
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Disallowed transitive axiom: {name} depends on {axiomName}"
    IO.println <| "AUDIT_DECL " ++ (Json.mkObj [
      ("name", toJson name.toString),
      ("owner", toJson <| imported[(env.getModuleIdxFor? name).get!.toNat]!.toString),
      ("theorem", toJson info.isTheorem), ("private", toJson <| isPrivateName name),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
      ("recursive_auxiliary_parent", toJson <| recursiveParent.map Name.toString),
      ("recursive_parent_marker", toJson <| recursiveParent.map (Meta.recExt.isTagged env)),
      ("recursive_parent_same_owner", toJson <| recursiveParent.map fun parent =>
        env.getModuleIdxFor? parent == env.getModuleIdxFor? name),
      ("recursive_parent_type_match", toJson <| recursiveParent.map fun parent =>
        (env.find? parent).get!.type == info.type),
      ("unexpected_partial_reason", toJson partialError),
      ("axioms", toJson <| axioms.map Name.toString)]).compress
  if declarations.isEmpty || theoremCount == 0 then
    throwError "Empty declaration/proof audit"
  IO.println <| "AUDIT_SUMMARY " ++ (Json.mkObj [
    ("modules", toJson owned.size), ("declarations", toJson declarations.size),
    ("theorems", toJson theoremCount), ("private_declarations", toJson privateCount),
    ("unsafe_declarations", toJson unsafeCount), ("partial_declarations", toJson partialCount),
    ("generated_recursive_auxiliaries", toJson generatedRecursiveCount),
    ("unexpected_partial_declarations", toJson unexpectedPartialCount),
    ("compiler_auxiliaries_without_kernel_declarations", toJson auxiliaryNames.size),
    ("compiler_auxiliary_export_occurrences", toJson auxiliaryOccurrences),
    ("extra_exported_existing_kernel_declarations", toJson kernelReexports),
    ("foreign_public_declarations", toJson foreignPublicCount),
    ("new_axioms", toJson (0 : Nat)), ("disallowed_axioms", toJson (0 : Nat)),
    ("allowed_axioms", toJson <| allowed.map Name.toString)]).compress

  if unexpectedPartialCount != 0 then
    throwError "Unexpected partial declarations: {unexpectedPartialCount}"
  if foreignPublicCount != 0 then
    throwError "Consumer generated {foreignPublicCount} foreign public declarations"
