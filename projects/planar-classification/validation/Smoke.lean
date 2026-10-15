import Counting.PlanarClassification

#eval do
  let coefficients := PlanarHom.LagrangeCoefficientMachines.productCoefficients ([2, 3] : List ℚ)
  unless coefficients == [6, -5, 1] do
    throw (IO.userError "materialized linear-factor coefficients are incorrect")
  let recovered := PlanarHom.MaterializedLagrangeRecoveryMachines.recover
    (([(1, 3), (2, 5)], [18, 32]) : List (ℚ × ℚ) × List ℚ)
  unless recovered == 47 do
    throw (IO.userError "shifted-Lagrange recovery changed the exact weighted sum")
  let empty := PlanarHom.MaterializedLagrangeRecoveryMachines.recover
    (([], []) : List (ℚ × ℚ) × List ℚ)
  unless empty == 0 do
    throw (IO.userError "empty recovery should be zero")
  IO.println "PH_MATERIALIZED_RECOVERY_SMOKE_OK coefficients=[6,-5,1] recovered=47 empty=0"

private def incidenceSample : PlanarHom.Complexity.MixedCode :=
  ⟨3, [(0, (0, 0)), (0, (1, 0)), (0, (1, 0))], []⟩

#eval do
  let ds := PlanarHom.GraphDegreeMachines.degrees incidenceSample
  unless ds == [0, 2, 4] do
    throw (IO.userError "loops, parallel edges, or the isolated vertex lost incidences")
  IO.println "PH_RANK_ONE_DEGREES_SMOKE_OK descending_degrees=[0,2,4]"

example : PlanarHom.RankOneEvaluationMachine.evaluate
    (fun _ : Fin 1 => (2 : ℚ)) (fun _ : Fin 1 => (3 : ℚ)) incidenceSample = 1728 := by
  norm_num [PlanarHom.RankOneEvaluationMachine.evaluate,
    PlanarHom.RankOneEvaluationMachine.factor, PlanarHom.GraphDegreeMachines.degrees,
    PlanarHom.GraphDegreeMachines.degree, PlanarHom.GraphDegreeMachines.endpoints,
    incidenceSample, List.range_succ]

#eval do
  let value := PlanarHom.MaterializedPolynomialEvaluationMachines.evaluate (4 : ℚ) [6, -5, 1]
  unless value == 2 do
    throw (IO.userError "runtime coefficient evaluation returned a wrong exact value")
  let quotient := PlanarHom.CoefficientListAlgebra.quotientCoefficients (2 : ℚ) [6, -5, 1]
  unless quotient == [-3, 1, 0] do
    throw (IO.userError "synthetic division lost ascending order or its trailing zero")
  IO.println "PH_RUNTIME_POLYNOMIAL_SMOKE_OK evaluation=2 quotient=[-3,1,0]"

private def boolWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolWords n).flatMap (fun w => [false :: w, true :: w])

private def formulaSatisfied
    (f : PlanarHom.ParsimoniousNorOneInThree.NumericFormula) (w : List Bool) : Bool :=
  f.2.all (fun c =>
    (PlanarHom.CountingCookLevin.readBit w c.1).toNat +
    (PlanarHom.CountingCookLevin.readBit w c.2.1).toNat +
    (PlanarHom.CountingCookLevin.readBit w c.2.2).toNat == 1)

private theorem formulaSatisfied_correct
    (f : PlanarHom.ParsimoniousNorOneInThree.NumericFormula) (w : List Bool) :
    formulaSatisfied f w = true ↔
      PlanarHom.ParsimoniousNorOneInThree.Satisfies f.2
        (PlanarHom.CountingCookLevin.readBit w) := by
  simp [formulaSatisfied, PlanarHom.ParsimoniousNorOneInThree.Satisfies,
    PlanarHom.ParsimoniousNorOneInThree.ExactlyOne, List.all_eq_true]

#eval do
  let p : PlanarHom.CountingNorProgram.Program := (2, ([(0,1)], 6))
  let f := PlanarHom.NorExactOne.compile p
  unless f.1 == 13 && f.2.length == 9 do
    throw (IO.userError "NOR compiler changed its explicit auxiliaries or clause count")
  let count := ((boolWords f.1).filter (formulaSatisfied f)).length
  unless count == 1 do
    throw (IO.userError "NOR compiler lost unique auxiliary extension")
  let repeated := PlanarHom.NorExactOne.compile (2, ([(0,0)], 6))
  unless ((boolWords repeated.1).filter (formulaSatisfied repeated)).length == 2 do
    throw (IO.userError "repeated input port or unused witness bit was lost")
  let invalid := PlanarHom.NorExactOne.compile (2, ([(0,1)], 2^80))
  unless ((boolWords invalid.1).filter (formulaSatisfied invalid)).length == 0 do
    throw (IO.userError "out-of-range output should read the fixed false register")
  IO.println "PH_EXACT_ONE_SMOKE_OK variables=13 clauses=9 counts=[1,2,0] unique_auxiliaries=true"

#eval do
  let word := [true,false,true]
  let tail := [false,true]
  let parsed := PlanarHom.RawFrameParser.parse
    (PlanarHom.Complexity.BitEncoding.frame word ++ tail)
  unless parsed == (true,word,tail) do
    throw (IO.userError "raw frame parser changed payload or suffix")
  unless (PlanarHom.RawFrameParser.parse [true]).1 == false do
    throw (IO.userError "unfinished escaped frame should fail")
  let graph : PlanarHom.Complexity.GraphCode := ⟨3,[(0,0),(0,1),(0,1)]⟩
  let raw := PlanarHom.Complexity.GraphCode.encoding.encode graph
  let p := PlanarHom.Complexity.GraphCode.totalParser.run raw
  unless p.1 && decide (p.2 = graph) do
    throw (IO.userError "graph parser lost a loop, parallel edge or isolated vertex")
  unless (PlanarHom.Complexity.GraphCode.totalParser.run []).1 == false do
    throw (IO.userError "empty raw graph code should fail")
  let noncanonical := PlanarHom.Complexity.BitEncoding.frame [false,false,false] ++
    (PlanarHom.Complexity.BitEncoding.nat.prod PlanarHom.Complexity.BitEncoding.nat).list.encode graph.edges
  let pn := PlanarHom.Complexity.GraphCode.totalParser.run noncanonical
  unless pn.1 && decide (pn.2 = graph) do
    throw (IO.userError "noncanonical successful graph word changed decoder semantics")
  let huge := PlanarHom.Complexity.BitEncoding.frame
    (PlanarHom.Complexity.BitEncoding.nat.encode (2^80))
  unless ((PlanarHom.Complexity.BitEncoding.TotalParser.nat).list.run huge).1 == false do
    throw (IO.userError "huge absent frame list should fail")
  let good := [true,false,true,false,false,true]
  unless PlanarHom.ZeroOneSharpPMembership.padding graph.vertices 2 good do
    throw (IO.userError "canonical witness padding rejected")
  unless !(PlanarHom.ZeroOneSharpPMembership.padding graph.vertices 2 (good++[true])) do
    throw (IO.userError "nonzero padding introduced an extra witness")
  IO.println "PH_TOTAL_PARSER_VERIFIER_SMOKE_OK frame_suffix=true malformed=false noncanonical_success=true huge_header_rejected=true loop_parallel_isolated=true zero_padding=true"
