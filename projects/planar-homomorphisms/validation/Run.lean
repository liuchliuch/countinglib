import Counting.Examples.PlanarHomSharpP
open PlanarHom.NondeterministicComputationTree Counting.Examples.PlanarHomSharpP
#eval acceptingCount mergedView 1 false
#eval acceptingCount mergedView 17 false
#eval replay mergedView false [false, false, false]
#eval replay mergedView false [true, false, false]
#eval replay mergedView false [true, false, true]
#eval replay mergedView false []
