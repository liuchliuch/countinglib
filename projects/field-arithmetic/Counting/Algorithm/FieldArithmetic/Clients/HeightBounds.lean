import Counting.Algorithm.FieldArithmetic.Heights

/-! A two-stage canonical-size calculation using the optional uniform height
entry. The supplied clearing data and its budget are fixed explicit data. -/
namespace Counting.Algorithm.FieldArithmetic.Clients.HeightBounds
open PlanarHom PlanarHom.FieldCoordinateCertificates PlanarHom.IntegerCoordinateBounds
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable {basis : Module.Basis (Fin dimension) ℚ K}

theorem normalized_difference_bound
    (data : ClearedCoordinates basis (fun k : Fin dimension => basis k))
    {c H N : ℕ} (hd : dimension ≤ c) (hdata : Certificate.heightConstant data ≤ 2 ^ H)
    (x y divisor : K)
    (hx : ((numberFieldEncoding basis).encode x).length ≤ N)
    (hy : ((numberFieldEncoding basis).encode y).length ≤ N)
    (hz : ((numberFieldEncoding basis).encode divisor).length ≤ N) :
    ((numberFieldEncoding basis).encode ((x - y) / divisor)).length ≤
      (Heights.operationPolynomial c).eval ((Heights.operationPolynomial c).eval (N + H) + H) := by
  have hs := (Heights.operations_encoding_bound data hd hdata x y N hx hy).2.1
  have hz' := hz.trans ((Nat.le_add_right N H).trans
    (Heights.operationPolynomial_ge c (N + H)).1)
  exact (Heights.operations_encoding_bound data hd hdata (x - y) divisor
    ((Heights.operationPolynomial c).eval (N + H)) hs hz').2.2.2

end
end Counting.Algorithm.FieldArithmetic.Clients.HeightBounds
