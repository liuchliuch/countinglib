import Counting.PlanarClassification
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Compiler.NoncomputableAttr

/-!
# Declaration and transitive axiom audit

Run `python3 scripts/verify.py`. The wrapper inventories every production
`PlanarHom/**/*.lean` and `Counting/**/*.lean` source.
The audit checks the actual import closure of `Counting.PlanarClassification`, then selects all
kernel declarations by module ownership, including private names, generated
names, and upstream declarations outside the `Counting` namespace.

Lean's `collectAxioms` checks transitive proof dependencies. Compiler-only auxiliary names without kernel declarations
are inventoried separately; they are not mathematical declarations.
-/

open Lean Elab Command

/-! Standalone lossless kernel-type DAG candidate; not production acceptance.
Names, universes, binder names/kinds and let nondep flags are all preserved.
Metadata payloads, syntax, raw substrings and source positions are all preserved. Every accepted type is decoded
from its serialized JSON and structurally compared to the original Expr. -/
open Lean
namespace CountingAuditDag

/-
Scalar Name/Level/BinderInfo/Literal codecs below are from pinned Lean 4.34.1
Lean/Elab/Idbg.lean, commit 5045d0056413266e57c625dcd7c365b10e377c52.
Copyright (c) 2026 Lean FRO, LLC. Authors: Sebastian Ullrich.
Released under Apache 2.0; preserved source and license are in provenance/lean-audit-codec.
-/
namespace ScalarCodec
/-- Custom `Name` serialization that preserves the exact structure.
The standard `ToJson`/`FromJson Name` uses `toString`/`toName` which doesn't
round-trip for hygienic names (e.g., names containing `@`). -/
def nameToJson : Name → Json
  | .anonymous => Json.null
  | .str p s   => Json.mkObj [("str", Json.arr #[nameToJson p, toJson s])]
  | .num p n   => Json.mkObj [("num", Json.arr #[nameToJson p, n])]

/-- Inverse of `nameToJson`. -/
partial def nameFromJson? (j : Json) : Except String Name := do
  if j.isNull then return .anonymous
  if let some arr := (j.getObjVal? "str").toOption then
    let #[p, s] := (← fromJson? arr : Array Json) | .error "str expects 2 elements"
    return .str (← nameFromJson? p) (← fromJson? s)
  if let some arr := (j.getObjVal? "num").toOption then
    let #[p, n] := (← fromJson? arr : Array Json) | .error "num expects 2 elements"
    return .num (← nameFromJson? p) (← fromJson? n)
  .error s!"expected Name, got {j}"

/-- Serialize `BinderInfo` to JSON. -/
def binderInfoToJson : BinderInfo → Json
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit   => "instImplicit"

/-- Deserialize `BinderInfo` from JSON. -/
def binderInfoFromJson? : Json → Except String BinderInfo
  | .str "default"        => .ok .default
  | .str "implicit"       => .ok .implicit
  | .str "strictImplicit" => .ok .strictImplicit
  | .str "instImplicit"   => .ok .instImplicit
  | j => .error s!"expected BinderInfo, got {j}"

/-- Serialize `Literal` to JSON. -/
def literalToJson : Literal → Json
  | .natVal n => Json.mkObj [("natVal", n)]
  | .strVal s => Json.mkObj [("strVal", s)]

/-- Deserialize `Literal` from JSON. -/
def literalFromJson? (j : Json) : Except String Literal := do
  if let some n := (j.getObjVal? "natVal").toOption then
    return .natVal (← fromJson? n)
  if let some s := (j.getObjVal? "strVal").toOption then
    return .strVal (← fromJson? s)
  .error s!"expected Literal, got {j}"

/-- Serialize `Level` to JSON. -/
partial def levelToJson : Level → Json
  | .zero     => Json.mkObj [("zero", Json.null)]
  | .succ l   => Json.mkObj [("succ", levelToJson l)]
  | .max a b  => Json.mkObj [("max", Json.arr #[levelToJson a, levelToJson b])]
  | .imax a b => Json.mkObj [("imax", Json.arr #[levelToJson a, levelToJson b])]
  | .param n  => Json.mkObj [("param", nameToJson n)]
  | .mvar id  => Json.mkObj [("mvar", nameToJson id.name)]

/-- Deserialize `Level` from JSON. -/
partial def levelFromJson? (j : Json) : Except String Level := do
  if (j.getObjVal? "zero").toOption.isSome then
    return .zero
  if let some l := (j.getObjVal? "succ").toOption then
    return .succ (← levelFromJson? l)
  if let some arr := (j.getObjVal? "max").toOption then
    let #[a, b] := (← fromJson? arr : Array Json) | .error "max expects 2 elements"
    return .max (← levelFromJson? a) (← levelFromJson? b)
  if let some arr := (j.getObjVal? "imax").toOption then
    let #[a, b] := (← fromJson? arr : Array Json) | .error "imax expects 2 elements"
    return .imax (← levelFromJson? a) (← levelFromJson? b)
  if let some n := (j.getObjVal? "param").toOption then
    return .param (← nameFromJson? n)
  if let some n := (j.getObjVal? "mvar").toOption then
    return .mvar ⟨← nameFromJson? n⟩
  .error s!"expected Level, got {j}"


end ScalarCodec

private def substringToJson (s : Substring.Raw) : Json :=
  Json.arr #[toJson s.str, toJson s.startPos.byteIdx, toJson s.stopPos.byteIdx]

private def substringFromJson (j : Json) : Except String Substring.Raw := do
  let #[s, a, b] := (← fromJson? j : Array Json) | throw "Invalid raw substring"
  return ⟨← fromJson? s, ⟨← fromJson? a⟩, ⟨← fromJson? b⟩⟩

private def sourceInfoToJson : SourceInfo → Json
  | .none => Json.arr #[toJson "none"]
  | .synthetic a b c => Json.arr #[toJson "synthetic", toJson a.byteIdx, toJson b.byteIdx, toJson c]
  | .original l a t b => Json.arr #[toJson "original", substringToJson l,
      toJson a.byteIdx, substringToJson t, toJson b.byteIdx]

private def sourceInfoFromJson (j : Json) : Except String SourceInfo := do
  match (← fromJson? j : Array Json) with
  | #[.str "none"] => return .none
  | #[.str "synthetic", a, b, c] =>
    return .synthetic ⟨← fromJson? a⟩ ⟨← fromJson? b⟩ (← fromJson? c)
  | #[.str "original", l, a, t, b] =>
    return .original (← substringFromJson l) ⟨← fromJson? a⟩
      (← substringFromJson t) ⟨← fromJson? b⟩
  | _ => throw "Invalid source info"

private def preresolvedToJson : Syntax.Preresolved → Json
  | .namespace n => Json.arr #[toJson "namespace", ScalarCodec.nameToJson n]
  | .decl n fs => Json.arr #[toJson "decl", ScalarCodec.nameToJson n, toJson fs]

private def preresolvedFromJson (j : Json) : Except String Syntax.Preresolved := do
  match (← fromJson? j : Array Json) with
  | #[.str "namespace", n] => return .namespace (← ScalarCodec.nameFromJson? n)
  | #[.str "decl", n, fs] => return .decl (← ScalarCodec.nameFromJson? n) (← fromJson? fs)
  | _ => throw "Invalid preresolved syntax name"

private partial def syntaxToJson : Syntax → Json
  | .missing => Json.arr #[toJson "missing"]
  | .atom info text => Json.arr #[toJson "atom", sourceInfoToJson info, toJson text]
  | .ident info raw name pre => Json.arr #[toJson "ident", sourceInfoToJson info,
      substringToJson raw, ScalarCodec.nameToJson name, toJson <| pre.map preresolvedToJson]
  | .node info kind args => Json.arr #[toJson "node", sourceInfoToJson info,
      ScalarCodec.nameToJson kind, toJson <| args.map syntaxToJson]

private partial def syntaxFromJson (j : Json) : Except String Syntax := do
  match (← fromJson? j : Array Json) with
  | #[.str "missing"] => return .missing
  | #[.str "atom", info, text] => return .atom (← sourceInfoFromJson info) (← fromJson? text)
  | #[.str "ident", info, raw, name, pre] =>
    let pre : List Json ← fromJson? pre
    return .ident (← sourceInfoFromJson info) (← substringFromJson raw)
      (← ScalarCodec.nameFromJson? name) (← pre.mapM preresolvedFromJson)
  | #[.str "node", info, kind, args] =>
    let args : Array Json ← fromJson? args
    return .node (← sourceInfoFromJson info) (← ScalarCodec.nameFromJson? kind)
      (← args.mapM syntaxFromJson)
  | _ => throw "Invalid syntax metadata"

private def metadataToJson (md : MData) : Except String Json := do
  let entries ← md.entries.mapM fun (name, v) => do
    let value ← match v with
      | .ofString x => pure <| Json.arr #[toJson "string", toJson x]
      | .ofBool x => pure <| Json.arr #[toJson "bool", toJson x]
      | .ofName x => pure <| Json.arr #[toJson "name", ScalarCodec.nameToJson x]
      | .ofNat x => pure <| Json.arr #[toJson "nat", toJson x]
      | .ofInt x => pure <| Json.arr #[toJson "int", toJson x]
      | .ofSyntax x => pure <| Json.arr #[toJson "syntax", syntaxToJson x]
    pure <| Json.arr #[ScalarCodec.nameToJson name, value]
  return toJson entries

private def metadataFromJson (j : Json) : Except String MData := do
  let entries : List Json ← fromJson? j
  let entries ← entries.mapM fun entry => do
    let #[n, v] := (← fromJson? entry : Array Json) | throw "Invalid metadata entry"
    let #[.str tag, data] := (← fromJson? v : Array Json) | throw "Invalid metadata payload"
    let value ← match tag with
      | "string" => pure <| DataValue.ofString (← fromJson? data)
      | "bool" => pure <| DataValue.ofBool (← fromJson? data)
      | "name" => pure <| DataValue.ofName (← ScalarCodec.nameFromJson? data)
      | "nat" => pure <| DataValue.ofNat (← fromJson? data)
      | "int" => pure <| DataValue.ofInt (← fromJson? data)
      | "syntax" => pure <| DataValue.ofSyntax (← syntaxFromJson data)
      | _ => throw "Unknown metadata payload kind"
    return (← ScalarCodec.nameFromJson? n, value)
  return {entries}

structure EncodeState where
  nodes : Array Json := #[]
  seen : ExprStructMap Nat := {}
  cache : Bool := true

private def node (tag : String) (fields : Array Json := #[]) : Json :=
  Json.arr (#[toJson tag] ++ fields)

partial def encodeNode (e : Expr) : StateT EncodeState (Except String) Nat := do
  if (← get).cache then
    if let some i := (← get).seen[{val := e : ExprStructEq}]? then return i
  let n ← match e with
    | .bvar i => pure <| node "bvar" #[toJson i]
    | .fvar id => pure <| node "fvar" #[ScalarCodec.nameToJson id.name]
    | .mvar id => pure <| node "mvar" #[ScalarCodec.nameToJson id.name]
    | .sort l => pure <| node "sort" #[ScalarCodec.levelToJson l]
    | .const n ls => pure <| node "const" #[ScalarCodec.nameToJson n, toJson <| ls.map ScalarCodec.levelToJson]
    | .app f a => do
      let fi ← encodeNode f; let ai ← encodeNode a
      pure <| node "app" #[toJson fi, toJson ai]
    | .lam n t b bi => do
      let ti ← encodeNode t; let bi' ← encodeNode b
      pure <| node "lam" #[ScalarCodec.nameToJson n, toJson ti, toJson bi', ScalarCodec.binderInfoToJson bi]
    | .forallE n t b bi => do
      let ti ← encodeNode t; let bi' ← encodeNode b
      pure <| node "forallE" #[ScalarCodec.nameToJson n, toJson ti, toJson bi', ScalarCodec.binderInfoToJson bi]
    | .letE n t v b nd => do
      let ti ← encodeNode t; let vi ← encodeNode v; let bi ← encodeNode b
      pure <| node "letE" #[ScalarCodec.nameToJson n, toJson ti, toJson vi, toJson bi, toJson nd]
    | .lit l => pure <| node "lit" #[ScalarCodec.literalToJson l]
    | .proj n i s => do
      let si ← encodeNode s
      pure <| node "proj" #[ScalarCodec.nameToJson n, toJson i, toJson si]
    | .mdata md b => do
      let metadata ← metadataToJson md
      let bi ← encodeNode b
      pure <| node "mdata" #[metadata, toJson bi]
  let state ← get
  let i := state.nodes.size
  set { state with
    nodes := state.nodes.push n
    seen := if state.cache then state.seen.insert {val := e} i else state.seen }
  return i

private def earlier (decoded : Array Expr) (j : Json) : Except String Expr := do
  let i : Nat ← fromJson? j
  let some e := decoded[i]? | throw s!"Invalid non-earlier DAG reference {i}"
  return e

def decodeNode (decoded : Array Expr) (j : Json) : Except String Expr := do
  let a : Array Json ← fromJson? j
  match a with
  | #[.str "bvar", i] => return .bvar (← fromJson? i)
  | #[.str "fvar", n] => return .fvar ⟨← ScalarCodec.nameFromJson? n⟩
  | #[.str "mvar", n] => return .mvar ⟨← ScalarCodec.nameFromJson? n⟩
  | #[.str "sort", l] => return .sort (← ScalarCodec.levelFromJson? l)
  | #[.str "const", n, ls] =>
    let ls : List Json ← fromJson? ls
    return .const (← ScalarCodec.nameFromJson? n) (← ls.mapM ScalarCodec.levelFromJson?)
  | #[.str "app", f, a] => return .app (← earlier decoded f) (← earlier decoded a)
  | #[.str "lam", n, t, b, bi] =>
    return .lam (← ScalarCodec.nameFromJson? n) (← earlier decoded t) (← earlier decoded b)
      (← ScalarCodec.binderInfoFromJson? bi)
  | #[.str "forallE", n, t, b, bi] =>
    return .forallE (← ScalarCodec.nameFromJson? n) (← earlier decoded t) (← earlier decoded b)
      (← ScalarCodec.binderInfoFromJson? bi)
  | #[.str "letE", n, t, v, b, nd] =>
    return .letE (← ScalarCodec.nameFromJson? n) (← earlier decoded t) (← earlier decoded v)
      (← earlier decoded b) (← fromJson? nd)
  | #[.str "lit", l] => return .lit (← ScalarCodec.literalFromJson? l)
  | #[.str "proj", n, i, s] =>
    return .proj (← ScalarCodec.nameFromJson? n) (← fromJson? i) (← earlier decoded s)
  | #[.str "mdata", md, b] => return .mdata (← metadataFromJson md) (← earlier decoded b)
  | _ => throw "Invalid or unsupported Expr DAG node"

def decode (j : Json) : Except String Expr := do
  let format : String ← fromJson? (← j.getObjVal? "format")
  unless format == "lean-expr-dag-v1" do throw "Unknown Expr DAG format"
  let nodes : Array Json ← fromJson? (← j.getObjVal? "nodes")
  let mut decoded : Array Expr := #[]
  for n in nodes do decoded := decoded.push (← decodeNode decoded n)
  earlier decoded (← j.getObjVal? "root")

def fullType (e : Expr) : Except String Json := do
  -- Expr.equal compares KVMap modulo entry order, and Syntax.structEq ignores
  -- source positions. Disable interning for every metadata-bearing type so
  -- the complete ordered payload and syntax source information remain exact.
  let cache := (e.find? Expr.isMData).isNone
  let (root, state) ← (encodeNode e).run {cache}
  let value := Json.mkObj [("format", toJson "lean-expr-dag-v1"),
    ("root", toJson root), ("nodes", toJson state.nodes)]
  let serialized := value.compress
  let parsed ← Json.parse serialized
  let decoded ← decode parsed
  unless Expr.equal decoded e do throw "Expr DAG failed exact structural roundtrip"
  let (roundtripRoot, roundtripState) ← (encodeNode decoded).run {cache}
  unless root == roundtripRoot && state.nodes == roundtripState.nodes do
    throw "Expr DAG JSON roundtrip changed metadata or syntax source information"
  return parsed


end CountingAuditDag

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
  let records ← IO.FS.Handle.mk "validation/audit-records.jsonl" .write
  let progress ← IO.FS.Handle.mk "validation/audit-progress.jsonl" .write
  let emit : String → IO Unit := records.putStrLn
  let started ← IO.monoMsNow
  let some sourceText ← IO.getEnv "COUNTING_AUDIT_MODULES"
    | throwError "Missing source inventory. Run python3 scripts/verify.py."
  let sourceModules := (sourceText.splitOn "\n").filter (· != "")
  if sourceModules.isEmpty then
    throwError "The local library source inventory is empty."
  let env := (← getEnv).setExporting false
  let importedModules := env.header.moduleNames
  -- Check the aggregator's own dependency graph, not merely the audit file's imports.
  let mut closure : Array Name := #[`Counting.PlanarClassification]
  let mut closureSet : Std.HashSet Name := Std.HashSet.ofArray closure
  let mut cursor : Nat := 0
  while cursor < closure.size do
    let moduleName := closure[cursor]!
    let some moduleIdx := env.getModuleIdx? moduleName
      | throwError "Missing imported module data: {moduleName}"
    for dependency in env.header.moduleData[moduleIdx.toNat]!.imports do
      unless closureSet.contains dependency.module do
        closure := closure.push dependency.module
        closureSet := closureSet.insert dependency.module
    cursor := cursor + 1
  for moduleName in closure do
    emit <| "AUDIT_CLOSURE " ++ (toJson moduleName.toString).compress
  for sourceModule in sourceModules do
    unless closureSet.contains sourceModule.toName do
      throwError "Local source module is absent from Counting.PlanarClassification's import closure: {sourceModule}"
  let sourceSet : Std.HashSet Name := Std.HashSet.ofArray <| sourceModules.toArray.map String.toName
  let ownedModules : Array Name := importedModules.filter sourceSet.contains
  let ownedModuleSet : Std.HashSet Name := Std.HashSet.ofArray ownedModules
  let declarations := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if ownedModuleSet.contains importedModules[idx.toNat]! then names.push name
      else names
    | none => names
  -- Lean can deduplicate a generated declaration shared by independently compiled modules.
  -- Retain canonical ownership and every owned-module reference from both export pools.
  -- Extra exports count as compiler-only only when the checked kernel map has no entry.
  let ownedDeclarations := declarations
  let ownedDeclarationSet : Std.HashSet Name := Std.HashSet.ofArray ownedDeclarations
  let mut allDeclarations := declarations
  let mut declarationSet := ownedDeclarationSet
  let mut references : Std.HashMap Name (Array Name) := {}
  for moduleName in ownedModules do
    let some idx := env.getModuleIdx? moduleName
      | throwError "Missing owned module: {moduleName}"
    let data := env.header.moduleData[idx.toNat]!
    for (pool, entries) in #[("constNames", data.constNames), ("extraConstNames", data.extraConstNames)] do
      for name in entries do
        match env.checked.get.find? name with
        | none =>
          if pool == "constNames" then
            throwError "Module constant is absent from kernel environment: {moduleName}: {name}"
        | some _ =>
          let prior := references.getD name #[]
          unless prior.contains moduleName do
            references := references.insert name (prior.push moduleName)
          unless declarationSet.contains name do
            allDeclarations := allDeclarations.push name
            declarationSet := declarationSet.insert name
  let declarations := allDeclarations.qsort Name.lt
  if declarations.isEmpty then
    throwError "No declarations found in local library modules."
  let mut moduleCounts : Std.HashMap Nat Nat := {}
  for name in declarations do
    let some idx := env.getModuleIdxFor? name
      | throwError "Enumerated declaration has no module ownership: {name}"
    moduleCounts := moduleCounts.insert idx.toNat (moduleCounts.getD idx.toNat 0 + 1)
  -- Cross-check each module's exported constant inventory; never silently omit a name.
  let mut codegenCount : Nat := 0
  for moduleName in ownedModules do
    let some idx := env.getModuleIdx? moduleName
      | throwError "Missing owned module: {moduleName}"
    let data := env.header.moduleData[idx.toNat]!
    for name in data.constNames do
      unless declarationSet.contains name do
        throwError "Module-owned declaration was not enumerated: {moduleName}: {name}"
    for name in data.extraConstNames do
      if (env.checked.get.find? name).isSome then
        unless declarationSet.contains name do
          throwError "Exported extra kernel constant was not enumerated: {moduleName}: {name}"
      else
        codegenCount := codegenCount + 1
        emit <| "AUDIT_CODEGEN " ++ (Json.mkObj [
          ("name", toJson name.toString), ("module", toJson moduleName.toString),
          ("kind", toJson "compiler_auxiliary_without_kernel_declaration")]).compress
    emit <| "AUDIT_MODULE " ++ (Json.mkObj [
      ("name", toJson moduleName.toString),
      ("kernel_declarations", toJson <| moduleCounts.getD idx.toNat 0),
      ("module_constant_names", toJson data.constNames.size),
      ("module_extra_names", toJson data.extraConstNames.size)]).compress
  let allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut theoremCount : Nat := 0
  let mut axiomCount : Nat := 0
  let mut privateCount : Nat := 0
  let mut recursiveAuxCount : Nat := 0
  let mut failureCount : Nat := 0
  let mut checked : Nat := 0
  progress.putStrLn <| (Json.mkObj [("checked", toJson checked), ("expected", toJson declarations.size),
    ("elapsed_ms", toJson ((← IO.monoMsNow) - started))]).compress
  progress.flush
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
    let fullType ← IO.ofExcept (CountingAuditDag.fullType info.type)
    let sourceReferences := references.getD name #[]
    emit <| "AUDIT_DECL " ++ (Json.mkObj [
      ("ownership", toJson <| if ownedDeclarationSet.contains name then "canonical_owned" else "shared_generated_reference"),
      ("source_reference_modules", toJson <| sourceReferences.map Name.toString),
      ("name", toJson name.toString),
      ("module", toJson importedModules[idx.toNat]!.toString),
      ("kind", toJson <| auditKind info),
      ("private", toJson <| isPrivateName name),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
      ("compiler_recursive_auxiliary_parent", toJson <| recursiveAuxParent.map Name.toString),
      ("universe_parameters", toJson <| info.levelParams.map Name.toString),
      ("type", fullType),
      ("type_encoding", toJson "lean-expr-dag-v1"),
      ("type_roundtrip", toJson "Expr.equal plus exact JSON reencoding"),
      ("axioms", toJson <| axioms.map Name.toString)]).compress
    checked := checked + 1
    if checked % 1000 == 0 || checked == declarations.size then
      records.flush
      progress.putStrLn <| (Json.mkObj [("checked", toJson checked), ("expected", toJson declarations.size),
        ("name", toJson name.toString), ("elapsed_ms", toJson ((← IO.monoMsNow) - started))]).compress
      progress.flush
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
  emit <| "AUDIT_SUMMARY " ++ (Json.mkObj [
    ("modules", toJson ownedModules.size), ("declarations", toJson declarations.size),
    ("canonical_owned_declarations", toJson ownedDeclarations.size),
    ("shared_generated_declarations", toJson (declarations.size - ownedDeclarations.size)),
    ("theorems", toJson theoremCount), ("private_declarations", toJson privateCount),
    ("compiler_auxiliaries_without_kernel_declarations", toJson codegenCount),
    ("compiler_recursive_auxiliaries", toJson recursiveAuxCount),
    ("local_axioms", toJson axiomCount), ("disallowed_dependencies", toJson failureCount),
    ("allowed_axioms", toJson <| allowedAxioms.map Name.toString)]).compress
  emit s!"AUDIT_OK modules={ownedModules.size} declarations={declarations.size} theorems={theoremCount} local_axioms={axiomCount} allowed=[propext, Classical.choice, Quot.sound]"

  records.flush
  progress.flush
