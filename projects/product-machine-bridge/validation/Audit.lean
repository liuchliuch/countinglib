import Counting.Algorithm.ProductFinitePalette
import Counting.Algorithm.ProductFinitePalette.Clients
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Meta.Basic

open Lean Elab Command

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

run_cmd do
  let expected := #[`Counting.Algorithm.ProductFinitePalette,
    `Counting.Algorithm.ProductFinitePalette.Input,
    `Counting.Algorithm.ProductFinitePalette.Machine,
    `Counting.Algorithm.ProductFinitePalette.Clients]
  let env := (← getEnv).setExporting false
  let imported := env.header.moduleNames
  let owned := imported.filter fun n => expected.contains n
  unless owned.size == expected.size do throwError "Missing owned module"
  let names := (env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if owned.contains imported[idx.toNat]! then names.push name else names
    | none => names).qsort Name.lt
  for m in imported do
    let some idx := env.getModuleIdx? m | throwError "Missing imported module"
    let data := env.header.moduleData[idx.toNat]!
    IO.println <| "MODULE " ++ (Json.mkObj [
      ("name", toJson m.toString),
      ("imports", toJson (data.imports.map (·.module.toString)))]).compress
    if owned.contains m then
      for n in data.constNames do
        unless names.contains n do throwError "Unenumerated module constant {n}"
      for n in data.extraConstNames do
        unless names.contains n do
          IO.println <| "CODEGEN " ++ (Json.mkObj [
            ("name", toJson n.toString), ("module", toJson m.toString)]).compress
  for n in names do
    let some ci := env.find? n | throwError "Missing constant"
    let some idx := env.getModuleIdxFor? n | throwError "Missing owner"
    let axioms ← Lean.collectAxioms n
    for a in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Disallowed transitive axiom {a} in {n}"
    if ci.isAxiom then throwError "Local axiom {n}"
    if ci.isUnsafe then throwError "Unsafe owned declaration {n}"
    if ci.isPartial then throwError "Partial owned declaration {n}"
    let fullType ← liftTermElabM do
      withOptions (fun o => o.setBool `pp.all true |>.setBool `pp.privateNames true
        |>.set `pp.maxSteps (10000000 : Nat) |>.set `maxRecDepth (10000 : Nat)) do
        return (← Meta.ppExpr ci.type).pretty 120
    if fullType.contains '⋯' then throwError "Truncated type {n}"
    IO.println <| "DECL " ++ (Json.mkObj [
      ("name", toJson n.toString), ("module", toJson imported[idx.toNat]!.toString),
      ("kind", toJson (declarationKind ci)), ("private", toJson (isPrivateName n)),
      ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
      ("type", toJson fullType), ("axioms", toJson (axioms.map Name.toString))]).compress
  IO.println s!"PRODUCT_FRONTEND_AUDIT_OK modules={owned.size} declarations={names.size}"
