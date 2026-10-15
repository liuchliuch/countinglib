import Counting.ComplexCSPClassification
open ComplexCSP.MaltsevWitness ComplexCSP.MaltsevRelations
open Counting.ComplexCSP.Classification.Maltsev

private def singletonMaltsev : Operation (Fin 1) := fun _ => 0
private def rejectingUnary : FiniteConstraint 1 1 := ⟨1, fun _ => 0, fun _ => false⟩

#eval do
  unless solve singletonMaltsev 0 ([] : List (FiniteConstraint 1 1)) do
    throw (IO.userError "the empty singleton CSP should have a witness")
  if solve singletonMaltsev 0 [rejectingUnary] then
    throw (IO.userError "the rejecting unary CSP should have no witness")
  IO.println "CSP_CLASSIFICATION_PRELUDE_SMOKE_OK satisfiable=true unsatisfiable=false"

private def sampleRow : Fin 3 → ℚ := ![0, 2, 4]
private def cancellingRow : Fin 2 → ℚ := ![1, -1]

#eval do
  let normalized := ComplexCSP.ComplexityRowNormalization.normalize sampleRow
  match normalized with
  | none => throw (IO.userError "a nonzero rational row lost its anchor")
  | some (anchor, row) =>
    unless anchor.val == 1 && row 0 == 0 && row 1 == 1 && row 2 == 2 do
      throw (IO.userError "first-anchor normalization returned wrong exact ratios")
  unless (ComplexCSP.ComplexityRowNormalization.normalize (fun _ : Fin 3 => (0 : ℚ))).isNone do
    throw (IO.userError "zero rows should have no anchor")
  unless ComplexCSP.ComplexityRowNormalization.rowSum sampleRow == 6 do
    throw (IO.userError "exact row summation is incorrect")
  unless ComplexCSP.ComplexityRowNormalization.rowSum cancellingRow == 0 do
    throw (IO.userError "exact row summation must preserve cancellation")
  IO.println "CSP_WEIGHTED_ROWS_SMOKE_OK normalized=[0,1,2] zero=none sum=6 cancellation=0"

private def binaryMaltsev (x y z : Fin 2) : Fin 2 := if x = y then z else x

#eval do
  let table : List (ℕ × List ℕ) := [(3, [7, 9]), (8, [])]
  unless ComplexCSP.ComplexityFiniteLookup.lookup [0] table 3 == [7, 9] do
    throw (IO.userError "finite lookup changed the stored output word")
  unless ComplexCSP.ComplexityFiniteLookup.lookup [0] table (2^80) == [0] do
    throw (IO.userError "missing binary lookup key lost its fixed default")
  let mapped := ComplexCSP.ComplexityWitnessPrimitives.mapOperation 2 binaryMaltsev
    [0, 1, 1] [0, 0, 1] [1, 0, 0]
  unless mapped == [1, 1, 0] do
    throw (IO.userError "runtime word operation disagrees with finite operation")
  unless ComplexCSP.ComplexityWitnessPrimitives.operation 2 binaryMaltsev (2^80) 0 0 == 0 do
    throw (IO.userError "out-of-domain input should produce the fixed default")
  unless ComplexCSP.ComplexityWitnessPrimitives.mapOperation 2 binaryMaltsev [] [] [] == [] do
    throw (IO.userError "zero-dimensional word should stay empty")
  IO.println "CSP_WITNESS_WORDS_SMOKE_OK lookup=[7,9] missing=[0] map=[1,1,0] invalid=0 empty=[]"

#eval do
  let countAt := ComplexCSP.ComplexityCountRecovery.recover (4 : ℚ) [1, 2] [4, 6]
  unless countAt 0 == 1 && countAt 1 == 2 && countAt 2 == 1 && countAt 3 == 0 do
    throw (IO.userError "moment postprocessing lost a zero, repeated, or absent weight")
  IO.println "CSP_COUNT_RECOVERY_SMOKE_OK zero=1 repeated=2 distinct=1 absent=0"

private def equalityLanguage : ComplexCSP.Language (Fin 2) ℚ (Fin 1) where
  arity := fun _ => 2
  arity_pos := fun _ => by decide
  value := fun _ xs => if xs 0 = xs 1 then 1 else 0

private def codedSample : ComplexCSP.ComplexityCSPCode.Code :=
  ⟨4, [(0, [0, 0]), (0, [1, 2]) ]⟩

#eval do
  unless decide (ComplexCSP.ComplexityCSPCode.Valid equalityLanguage codedSample) do
    throw (IO.userError "the repeated-position sample code should be valid")
  let qs := ComplexCSP.ComplexityCSPQueries.queries codedSample 2
  unless qs.map (fun g : ComplexCSP.ComplexityCSPCode.Code => g.vertices) == [4, 4, 4] &&
      qs.map (fun g : ComplexCSP.ComplexityCSPCode.Code => g.constraints.length) == [0, 2, 4] do
    throw (IO.userError "query construction lost variables or repeated occurrences")
  unless qs.map (ComplexCSP.ComplexityCSPCode.partition equalityLanguage) == [16, 8, 8] do
    throw (IO.userError "literal query semantics lost an isolated variable or scope position")
  unless ComplexCSP.ComplexityCSPCode.countAt equalityLanguage codedSample 0 == 8 &&
      ComplexCSP.ComplexityCSPCode.countAt equalityLanguage codedSample 1 == 8 do
    throw (IO.userError "coded assignment counts failed to retain zero-weight assignments")
  IO.println "CSP_COUNT_REDUCTION_QUERIES_SMOKE_OK vertices=[4,4,4] occurrences=[0,2,4] moments=[16,8,8] zero=8 one=8"

private def equalityPathTemplate : ComplexCSP.ComplexityGadgetSubstitution.Template :=
  ⟨2, 1, [(0, [0, 2]), (0, [2, 1])]⟩

#eval do
  let compiled := ComplexCSP.ComplexityGadgetSubstitution.compile [equalityPathTemplate] codedSample
  unless compiled.vertices == 6 && compiled.constraints ==
      [(0, [0, 4]), (0, [4, 0]), (0, [1, 5]), (0, [5, 2])] do
    throw (IO.userError "literal gadget compilation lost private-block freshness or port order")
  unless decide (ComplexCSP.ComplexityCSPCode.Valid equalityLanguage compiled) &&
      ComplexCSP.ComplexityCSPCode.partition equalityLanguage compiled == 8 do
    throw (IO.userError "compiled equality gadgets changed the exact partition value")
  IO.println "CSP_GADGET_SUBSTITUTION_SMOKE_OK fresh_private=[4,5] vertices=6 occurrences=4 partition=8"

private def tupleEqualityLanguage : ComplexCSP.Language (Fin 2 → Fin 2) ℚ (Fin 1) where
  arity _ := 2
  arity_pos _ := by decide
  value _ a := if a 0 = a 1 then 1 else 0

#eval do
  let compiled := ComplexCSP.ComplexityTupleExpansion.compile 2 codedSample
  unless compiled.vertices == 8 && compiled.constraints ==
      [(0,[0,1,0,1]),(0,[2,3,4,5])] do
    throw (IO.userError "tuple-domain expansion changed ordered coordinates")
  unless decide (ComplexCSP.ComplexityCSPCode.Valid
      (ComplexCSP.ComplexityTupleExpansion.language tupleEqualityLanguage (by decide)) compiled) &&
      ComplexCSP.ComplexityCSPCode.partition
        (ComplexCSP.ComplexityTupleExpansion.language tupleEqualityLanguage (by decide)) compiled == 64 do
    throw (IO.userError "tuple-domain expansion changed exact partition")
  IO.println "CSP_TUPLE_EXPANSION_SMOKE_OK vertices=8 ordered_ports=true isolated_coordinates=2 partition=64"

#eval do
  let build := ComplexCSP.ComplexitySupportWitnessPrimitives.rawSupportCompiler
    equalityLanguage binaryMaltsev 0
  let W := build codedSample
  unless W.1.length == 4 && W.1.all (fun row => row.length == 2) do
    throw (IO.userError "initial support compilation lost an isolated variable or color slot")
  unless W.1.flatten.flatten.all (fun xs => xs.length == 4 && xs[1]? == xs[2]?) do
    throw (IO.userError "stored support tuples violate the actual equality constraint")
  unless (build ⟨0, []⟩) == ([], [[]]) do
    throw (IO.userError "zero variables must retain a present empty tuple")
  let malformed := {codedSample with constraints := codedSample.constraints ++
    [(0,[0]), (2^80,[0,0]), (0,[2^80,0])]}
  unless build malformed == W do
    throw (IO.userError "invalid arity, symbol or address was not skipped by the raw compiler")
  let retained := ComplexCSP.ComplexityMarginalSupport.retainedWitnesses
    ([(0,((0:ℚ),([], [[]]))), (1,((2:ℚ),([], [[]]))), (2,((-3:ℚ),([], [])))] :
      ComplexCSP.ComplexityWeightedLayers.Layer ℚ)
  unless retained == [([], [[]]), ([], [])] do
    throw (IO.userError "factor filtering confused absent and present-empty witnesses")
  IO.println "CSP_POSITIVE_SUPPORT_SMOKE_OK dimension=4 zero_dimension=present_empty malformed=skipped zero_factor=removed"
