import Lean

/-! Verification-only fixture. It is never imported by production modules. -/
namespace CountingAuditFixture

private theorem privatePropext (p q : Prop) (h : p ↔ q) : p = q := propext h

theorem viaPrivate (p q : Prop) (h : p ↔ q) : p = q := privatePropext p q h

noncomputable def choose (α : Sort u) (h : Nonempty α) : α := Classical.choice h

structure Box where
  contents : Nat
  positive : 0 < contents

def alternate : Nat → Bool
  | 0 => true
  | n + 1 => !(alternate n)

theorem alternate_zero : alternate 0 = true := rfl

end CountingAuditFixture
