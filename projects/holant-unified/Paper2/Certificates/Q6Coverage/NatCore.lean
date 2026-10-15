import Paper2.Certificates.Q6Coverage.Core

/-! Compact storage for precisely the original twenty signed coordinates.
All signed-state transition and orbit theorems still run through the same
kernel-checked checker. No bit decoding equation is accepted as an axiom. -/
namespace Paper2.Certificates.Q6.Coverage

def natTerm (n : Nat) : Term :=
  if h : n < 20 then .pos ⟨n,h⟩
  else if h' : n < 40 then .neg ⟨n-20,by omega⟩
  else .zero

def natState (n : Nat) : State :=
  fun i => natTerm ((n >>> (6*i.val)) % 64)

end Paper2.Certificates.Q6.Coverage
