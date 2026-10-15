import Counting.Algorithm.FieldArithmetic.Clients.Composition
import Counting.Algorithm.FieldArithmetic.Clients.Interpolation
import Counting.Algorithm.FieldArithmetic.Clients.HeightBounds
import Counting.Algorithm.InterpolationMachine.Materialized.Clients

/-! Joint regression imports the unchanged original consumer and routes its
exact quadratic runtime table through the new public-entry-derived computer.
This is an acceptance entry, not part of ordinary arithmetic imports. -/
namespace Counting.Algorithm.FieldArithmetic.Acceptance
open Turing PlanarHom.Complexity
open Counting.Algorithm.InterpolationMachine.Materialized.Clients

noncomputable def originalQuadraticViaPublicEntry :
    TM2OutputsInTime (Clients.Interpolation.computer rationalBasis).tm
      (((Clients.Interpolation.inputEncoding rationalBasis).encode quadratic).map
        (Clients.Interpolation.computer rationalBasis).inputAlphabet.symm)
      (some (((numberFieldEncoding rationalBasis).encode 2).map
        (Clients.Interpolation.computer rationalBasis).outputAlphabet.symm))
      ((Clients.Interpolation.computer rationalBasis).time.eval
        ((Clients.Interpolation.inputEncoding rationalBasis).encode quadratic).length) := by
  simpa only [quadratic_recover] using Clients.Interpolation.outputs rationalBasis quadratic

end Counting.Algorithm.FieldArithmetic.Acceptance
