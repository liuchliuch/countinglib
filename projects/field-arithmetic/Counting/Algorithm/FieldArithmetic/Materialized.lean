import Counting.Algorithm.FieldArithmetic
import PlanarHom.MaterializedFieldListMachines

/-! Optional list sum/product machines and all-prefix canonical bit bounds.
The arithmetic entry itself does not import this fold/height closure. -/
namespace Counting.Algorithm.FieldArithmetic.Materialized

export PlanarHom.MaterializedFieldListMachines (fp_sum fp_product)
export PlanarHom.MaterializedFieldHeights (exists_polynomial_prefix_encoding_bound)

end Counting.Algorithm.FieldArithmetic.Materialized
