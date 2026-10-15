import Lean.Compiler.Old
import Lean.Meta.RecExt

/-! Validation-only recognition of the compiler's executable recursive auxiliaries.
Every accepted auxiliary still receives the audit's full transitive-axiom check. -/

open Lean

namespace KarpLubyRequestAudit

/-- A name suffix alone is never sufficient: require a safe total recursive
kernel definition in the same imported module, with exactly the same type. -/
def recursiveAuxiliaryParent (env : Environment) (name : Name) : Except String Name := do
  let some info := env.find? name | throw "missing auxiliary declaration"
  unless info.isPartial do throw "declaration is not partial"
  if info.isUnsafe then throw "auxiliary is unsafe"
  let some parent := Compiler.isUnsafeRecName? name | throw "not a compiler recursive auxiliary name"
  let some parentInfo := env.find? parent | throw "missing parent declaration"
  match parentInfo with
  | .defnInfo _ => pure ()
  | _ => throw "parent is not a kernel definition"
  if parentInfo.isUnsafe then throw "parent is unsafe"
  if parentInfo.isPartial then throw "parent is partial"
  unless Meta.recExt.isTagged env parent do throw "parent lacks recursive-definition marker"
  unless info.type == parentInfo.type do throw "parent type differs"
  let some owner := env.getModuleIdxFor? name | throw "auxiliary has no imported owner"
  unless env.getModuleIdxFor? parent == some owner do throw "parent owner differs"
  return parent

end KarpLubyRequestAudit
