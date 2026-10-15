import PlanarHom.FixedFieldArithmeticMachines

/-! # Exact arithmetic in a fixed rational basis

This entry keeps the original `PlanarHom.Complexity.numberFieldEncoding`,
`BitEncoding`, `FP`, and `Turing.TM2ComputableInPolyTime` contracts. A field,
dimension, and rational basis are fixed program parameters, not runtime input.
Inversion and division are total field operations, including `0⁻¹ = 0`.

The original declarations remain owned by `planar-machines`; these are public
aliases. Uniform coordinate heights and materialized list operations are separate
optional entries. No classification, field search, or representation conversion is
introduced here.
-/
namespace Counting.Algorithm.FieldArithmetic

export PlanarHom.Complexity (BitEncoding numberFieldEncoding FP)
export PlanarHom.FixedFieldArithmetic
  (fp_coordinate fp_of_coordinates fp_addition fp_negation fp_subtraction
   fp_multiplication fp_inverse fp_division fp_equality)

end Counting.Algorithm.FieldArithmetic
