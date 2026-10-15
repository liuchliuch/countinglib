import Counting.Algorithm.InterpolationMachine.Materialized.Clients
import Counting.Algorithm.InterpolationMachine.Clients
open Counting.Algorithm.InterpolationMachine
open Holant.Complexity.BinaryInterpolation
open Holant.OneHot.StackProgram
#eval Clients.runQuadratic.map Prod.fst
#eval Counting.Algorithm.Interpolation.evaluate (nodes false (2:ℚ) 2) (normalized 2 2 Clients.samples)
#eval (run (WeightFormulas.coefficients (2:ℚ) 2) (WeightCompiler.reference true 0) [-16]).map Prod.fst
#eval (run (WeightFormulas.coefficients (2:ℚ) 2) (WeightCompiler.reference false 2) [0,0,0]).map Prod.fst

#eval Materialized.recover Materialized.Clients.quadratic
#eval Materialized.recover ([(0, 7), (2, 7)] : Materialized.Table ℚ)
#eval Materialized.recover ([(0, 2), (0, 3)] : Materialized.Table ℚ)
#eval Materialized.recover ([(0, -16)] : Materialized.Table ℚ)
#eval Materialized.recover ([] : Materialized.Table ℚ)
