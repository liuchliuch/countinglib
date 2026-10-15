import Counting.ComplexCSPClassification
import Counting.PlanarClassification

/-! Compiled public endpoint signatures from the complete source-build state.
This is a type export, not the complete declaration/axiom acceptance audit. -/
set_option pp.all true
set_option pp.privateNames true
set_option pp.maxSteps 1000000
set_option maxRecDepth 10000

#check PlanarHom.MainDichotomyScope.theorem11
#check PlanarHom.MainDichotomyScope.theorem13
#print PlanarHom.MainDichotomyScope.Theorem11Statement
#print PlanarHom.MainDichotomyScope.Theorem13Statement
#check ComplexCSP.Recognition.encodedGlobalTest_complexity
#check ComplexCSP.Recognition.encodedDegreeGlobalTest_complexity
#check ComplexCSP.ComplexityClassification.ordinary_conditions
#check ComplexCSP.ComplexityClassification.degree_conditions
