import ComplexCSP.Complexity.CSPCode
import ComplexCSP.Instances.ValueTransport

/-! # Literal raw-code evaluation under coefficient homomorphisms -/
namespace ComplexCSP.ComplexityCSPCoefficientTransport
open ComplexityCSPCode
variable {D K R : Type} {s : ℕ} [CommSemiring K] [CommSemiring R]
variable (L : Language D K (Fin s)) (φ : K →+* R)

theorem eval_mapValues (g : Code) (a : Fin g.vertices → D) :
    eval (L.mapValues φ) g a=φ (eval L g a) := by
  simp only [eval,assignmentWord,map_list_prod,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [constraintEntry]
  split_ifs <;> first | rfl | contradiction | simp only [entryValue,map_one]

theorem partition_mapValues [Fintype D] (g : Code) :
    partition (L.mapValues φ) g=φ (partition L g) := by
  simp only [partition,map_sum,eval_mapValues]

end ComplexCSP.ComplexityCSPCoefficientTransport
