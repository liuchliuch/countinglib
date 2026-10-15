import Counting.Algorithm.FieldArithmetic.Acceptance
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms

open Lean Elab Command
open Counting.Algorithm

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[`Counting.Algorithm.FieldArithmetic,
    `Counting.Algorithm.FieldArithmetic.Heights,
    `Counting.Algorithm.FieldArithmetic.Materialized,
    `Counting.Algorithm.FieldArithmetic.Clients.Composition,
    `Counting.Algorithm.FieldArithmetic.Clients.Interpolation,
    `Counting.Algorithm.FieldArithmetic.Clients.HeightBounds,
    `Counting.Algorithm.FieldArithmetic.Acceptance]
  for root in roots do
    let mut closure : Array Name := #[root]
    let mut cursor := 0
    while cursor < closure.size do
      let some idx := env.getModuleIdx? closure[cursor]!
        | throwError "Missing compiled module: {closure[cursor]!}"
      for dep in env.header.moduleData[idx.toNat]!.imports do
        unless closure.contains dep.module do
          closure := closure.push dep.module
      cursor := cursor + 1
    IO.println <| "FIELD_CLOSURE " ++ (Json.mkObj [
      ("root", toJson root.toString),
      ("modules", toJson <| (closure.qsort Name.lt).map Name.toString)]).compress
  let declarations := #[
    ``PlanarHom.Complexity.numberFieldEncoding, ``PlanarHom.Complexity.FP,
    ``FieldArithmetic.fp_coordinate, ``FieldArithmetic.fp_of_coordinates,
    ``FieldArithmetic.fp_addition, ``FieldArithmetic.fp_negation,
    ``FieldArithmetic.fp_subtraction, ``FieldArithmetic.fp_multiplication,
    ``FieldArithmetic.fp_inverse, ``FieldArithmetic.fp_division,
    ``FieldArithmetic.fp_equality,
    ``FieldArithmetic.Heights.operations_encoding_bound,
    ``FieldArithmetic.Heights.inverse_neg_encoding_bound,
    ``FieldArithmetic.Materialized.fp_sum, ``FieldArithmetic.Materialized.fp_product,
    ``FieldArithmetic.Materialized.exists_polynomial_prefix_encoding_bound,
    ``FieldArithmetic.Clients.Composition.fp_normalizeAndCompare,
    ``FieldArithmetic.Clients.Composition.computer,
    ``FieldArithmetic.Clients.Composition.outputs,
    ``FieldArithmetic.Clients.Composition.steps_bound,
    ``FieldArithmetic.Clients.Composition.output_length_bound,
    ``FieldArithmetic.Clients.Interpolation.fp_recover,
    ``FieldArithmetic.Clients.Interpolation.computer,
    ``FieldArithmetic.Clients.Interpolation.outputs_coefficient,
    ``FieldArithmetic.Clients.Interpolation.intermediate_stack_bound,
    ``FieldArithmetic.Acceptance.originalQuadraticViaPublicEntry]
  for name in declarations do
    let some info := env.find? name | throwError "Missing declaration {name}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing owner {name}"
    let fullType ← liftTermElabM do
      withOptions (fun o => o.setBool `pp.all true |>.setBool `pp.privateNames true
        |>.set `pp.maxSteps (10000000 : Nat) |>.set `maxRecDepth (10000 : Nat)) do
        return (← Meta.ppExpr info.type).pretty 120
    if fullType.contains '⋯' then throwError "Truncated type: {name}"
    let axioms ← Lean.collectAxioms name
    for a in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "Unexpected axiom {a} in {name}"
    IO.println <| "FIELD_DECL " ++ (Json.mkObj [
      ("name", toJson name.toString), ("module", toJson env.header.moduleNames[idx.toNat]!.toString),
      ("type", toJson fullType), ("axioms", toJson <| axioms.map Name.toString)]).compress
