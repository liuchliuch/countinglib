import Counting.CookLevin.Reduction

/-! Boundary and nontrivial executable clients of the independent target. -/
namespace Counting.CookLevin.Clients

def binaryNor : Instance := (2, ([(0, 1)], 6))
def chained : Instance := (2, ([(0, 0), (6, 1)], 10))
def unusedWitness : Instance := (3, ([(0, 1)], 7))
def repeatedInput : Instance := (2, ([(0, 0)], 6))
def constantTrue : Instance := (0, ([], 0))
def constantFalse : Instance := (0, ([], 1))
def missingOutput : Instance := (2, ([], 100))
def largeReferences : Instance := (0, ([(2^128, 2^128)], 4))

theorem binaryNor_count : binaryNor.count = 1 := by decide
theorem chained_count : chained.count = 1 := by decide
theorem unusedWitness_count : unusedWitness.count = 2 := by decide
theorem repeatedInput_count : repeatedInput.count = 2 := by decide
theorem constantTrue_count : constantTrue.count = 1 := by decide
theorem constantFalse_count : constantFalse.count = 0 := by decide
theorem missingOutput_count : missingOutput.count = 0 := by decide
theorem largeReferences_count : largeReferences.count = 1 := by decide

theorem false_tail_accepts : accept (binaryNor, [false,false,false,false]) = true := by decide
theorem true_tail_rejects : accept (binaryNor, [false,false,false,true]) = false := by decide

theorem padded_count : Counting.Foundation.witnessCount
    (Instance.encoding.encode binaryNor).length (fun w => accept (binaryNor,w)) = 1 :=
  (accept_count binaryNor).trans binaryNor_count

theorem arbitrary_bits_source {f : List Bool → ℕ}
    (hf : Counting.Complexity.InSharpP (Computability.encodingList Bool) f) :
    Counting.Complexity.ParsimoniousReduces (Computability.encodingList Bool)
      Instance.encoding.toFinEncoding f Instance.count := sharpP_reduces hf

end Counting.CookLevin.Clients
