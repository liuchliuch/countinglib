import ComplexCSP.Complexity.SupportInitialMachine
import ComplexCSP.Complexity.MarginalSupport
private def eqLanguage : ComplexCSP.Language (Fin 2) ℚ (Fin 1) where
  arity _ := 2
  arity_pos _ := by decide
  value _ a := if a 0 = a 1 then 1 else 0
private def binaryMaltsev (x y z : Fin 2) : Fin 2 := if x = y then z else x
#eval ComplexCSP.ComplexitySupportWitnessPrimitives.rawSupportCompiler eqLanguage binaryMaltsev 0 ⟨4, [(0,[0,0]),(0,[1,2])]⟩
#eval ComplexCSP.ComplexitySupportWitnessPrimitives.rawSupportCompiler eqLanguage binaryMaltsev 0 ⟨0, []⟩
#eval ComplexCSP.ComplexitySupportWitnessPrimitives.rawSupportCompiler eqLanguage binaryMaltsev 0 ⟨4, [(0,[0,0]),(0,[1,2]), (0,[0]), (2^80,[0,0]), (0,[2^80,0])]⟩
#eval ComplexCSP.ComplexityMarginalSupport.retainedWitnesses ([(0,((0:ℚ),([], [[]]))), (1,((2:ℚ),([], [[]]))), (2,((-3:ℚ),([], [])))] : ComplexCSP.ComplexityWeightedLayers.Layer ℚ)
