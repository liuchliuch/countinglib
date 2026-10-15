import Holant.Proofs.Tractability.AffineMachine.FamilySolver

/-!
# Fixed finite-language Boolean machines

This separate entry retains the source's validated raw-network encoding, original
coefficient-field output and polynomial-time Boolean-stack machine. It does not
assert uniform polynomial evaluation when the signature language varies.
-/
namespace Counting.Algorithm.Affine.FixedLanguage

open Holant.Complexity Turing Computability
open Holant.LocalDrafts.Tractability

abbrev Family := AffineMachine.Assembly.Family

noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ} (D : Family s b arity)

/-- The same actual machine, time polynomial and original output codec as H1. -/
def computes := AffineMachine.FamilySolver.computes D

/-- Output is in the original coefficient field, even when the sum cancels. -/
theorem computedValue_exact
    (r : Holant.Complexity.FixedGadgetSubstitution.Compiler.Input s b arity) :
    AffineMachine.RawMachine.computedValue D r = AffineMachine.FamilyField.originalValue D r :=
  AffineMachine.FamilySolver.computedValue_exact D r

theorem inFP : InFP (RawClosedNetwork.validatedEncoding s b arity)
    (AffineMachine.FamilyField.originalPresentation D).encoding (AffineMachine.FamilyField.originalValue D) :=
  AffineMachine.FamilySolver.inFP D

/-- Preserve the finite alphabet certificates, with no extra premise. -/
def polyTime : PolyTime (RawClosedNetwork.validatedEncoding s b arity)
    (AffineMachine.FamilyField.originalPresentation D).encoding (AffineMachine.FamilyField.originalValue D) :=
  (computes D).toPolyTime

instance finiteStackAlphabet (k : (polyTime D).tm.K) : Fintype ((polyTime D).tm.Γ k) :=
  (polyTime D).finiteAlphabets k

/-- Every internal stack alphabet of the actual source machine is Boolean. -/
theorem stackAlphabet (k : (computes D).machine.K) :
    (computes D).machine.computer.Γ k = Bool := rfl

/-- Exact semantic value of the original coefficient-field answer. -/
theorem output_value
    (r : Holant.Complexity.FixedGadgetSubstitution.Compiler.Input s b arity) :
    (AffineMachine.FamilyField.originalValue D r : Holant.Tractable.AlgebraicComplex) =
      (r.val.realize r.property D.signatures D.kernels).denote Fin.elim0 :=
  AffineMachine.FamilyField.originalValue_exact D r

/-- Primitive cost is charged on the same successful physical machine run. -/
theorem primitive_bound
    (r : Holant.Complexity.FixedGadgetSubstitution.Compiler.Input s b arity) :
    FixedFieldMachines.primitiveCost (computes D).machine ((computes D).outputs r).steps
      (some (initList (computes D).machine.computer
        (RawClosedNetwork.encoding.encode r.val))) ≤
      (FixedFieldMachines.primitivePolynomial (computes D)).eval
        (RawClosedNetwork.encoding.encode r.val).length :=
  FixedFieldMachines.computes_primitive_cost (computes D) r

end
end Counting.Algorithm.Affine.FixedLanguage
