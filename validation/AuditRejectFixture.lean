import Lean

/-!
Verification-only rejection fixture. No axiom is introduced here. This theorem
uses an existing compiler-trust axiom from Lean's distribution, which is outside
the unified audit's exact permitted axiom list. It is not imported by production modules.
-/
namespace CountingAuditRejectFixture

set_option linter.deprecated false in
theorem externalCompilerTrust (a b : Bool) (h : Lean.reduceBool a = b) : a = b :=
  Lean.ofReduceBool a b h

end CountingAuditRejectFixture
