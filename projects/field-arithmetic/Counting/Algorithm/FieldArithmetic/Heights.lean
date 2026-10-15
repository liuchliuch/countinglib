import Counting.Algorithm.FieldArithmetic
import PlanarHom.UniformFieldArithmeticHeights

/-! Optional canonical-coordinate size contracts. The explicit dimension and
cleared-coordinate height budgets are retained verbatim; these are encoding-size
bounds, not a uniform runtime field/basis compiler. -/
namespace Counting.Algorithm.FieldArithmetic.Heights

export PlanarHom.UniformFieldHeights
  (canonical_bounded encoding_length_uniform inverseExponentConstant inversePolynomial
   inverse_neg_encoding_bound operationPolynomial operationPolynomial_ge operations_encoding_bound)

end Counting.Algorithm.FieldArithmetic.Heights
