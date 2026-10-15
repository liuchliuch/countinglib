import ComplexCSP.Instances.ConditionedMatrixCode
import ComplexCSP.Instances.RootedCSPMachines

/-! # Polynomial-time shared-root triangle compiler on the actual raw codec -/
namespace ComplexCSP.ConditionedMatrixCode
open PlanarHom PlanarHom.Complexity PairProjectionMachines
open ComplexityCSPCode ComplexityGadgetSubstitution RootedCSPProjection

theorem fp_edgeTriangles : FP constraintEncoding constraintEncoding.list edgeTriangles := by
  let ex := constraintEncoding
  have hs := fp_snd BitEncoding.nat BitEncoding.nat.list
  have hu := ((hs.comp (fp_getD BitEncoding.nat 0 0)).pair
    (fp_const ex BitEncoding.nat 1)).comp BinaryArithmetic.fp_addition
  have hv := ((hs.comp (fp_getD BitEncoding.nat 1 0)).pair
    (fp_const ex BitEncoding.nat 1)).comp BinaryArithmetic.fp_addition
  have hz := fp_const ex BitEncoding.nat 0
  have scope2 {u v : (ℕ × List ℕ) → ℕ}
      (hU : FP ex BitEncoding.nat u) (hV : FP ex BitEncoding.nat v) :
      FP ex BitEncoding.nat.list (fun c => [u c,v c]) :=
    (hU.pair ((hV.pair (fp_const ex BitEncoding.nat.list [])).comp
      (ListMutationMachines.fp_cons BitEncoding.nat))).comp
        (ListMutationMachines.fp_cons BitEncoding.nat)
  have h1 := hz.pair (scope2 hu hv)
  have h2 := hz.pair (scope2 hu hz)
  have h3 := hz.pair (scope2 hv hz)
  exact (h1.pair ((h2.pair ((h3.pair (fp_const ex constraintEncoding.list [])).comp
    (ListMutationMachines.fp_cons constraintEncoding))).comp
      (ListMutationMachines.fp_cons constraintEncoding))).comp
        (ListMutationMachines.fp_cons constraintEncoding)

theorem fp_rootCode : FP encoding encoding rootCode := by
  have hv := ((fp_const encoding BitEncoding.unaryNat 1).pair fp_vertices).comp
    UnaryPolynomialMachines.fp_add
  have hc := (fp_constraints.comp
    (ListMapMachines.fp_map constraintEncoding constraintEncoding.list edgeTriangles fp_edgeTriangles)).comp
      (ListFlattenMachines.fp_flatten constraintEncoding)
  exact (hv.pair hc).transportOutput (fun _ => rfl)

end ComplexCSP.ConditionedMatrixCode
