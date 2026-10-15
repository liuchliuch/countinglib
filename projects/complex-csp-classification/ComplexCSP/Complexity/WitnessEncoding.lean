import ComplexCSP.Complexity.WitnessPrimitives
import ComplexCSP.Structure.MaltsevWitness

/-! # Exact raw-word interface for finite-domain witness tuples

The unbounded coordinate dimension is retained in the mathematical interface;
the machine uses ordinary lists. Valid tuples are related by literal natural
labels, without a tuple-evaluation oracle or an assumed machine compiler.
-/
namespace ComplexCSP.ComplexityWitnessEncoding
open MaltsevWitness MaltsevRelations ComplexityWitnessPrimitives

/-- Literal binary natural labels of a finite-domain vector. -/
def word {d n : ℕ} (x : Tuple (Fin d) n) : List ℕ := x.toList.map Fin.val

@[simp] theorem word_length {d n : ℕ} (x : Tuple (Fin d) n) : (word x).length = n := by
  simp [word]

@[simp] theorem word_getD {d n : ℕ} (x : Tuple (Fin d) n) (i : Fin n) :
    (word x).getD i.val 0 = (view x i).val := by
  simp [List.getD_eq_getElem?_getD, word, view]

@[simp] theorem operation_fin {d : ℕ} (m : Fin d → Fin d → Fin d → Fin d)
    (x y z : Fin d) : operation d m x.val y.val z.val = (m x y z).val := by
  simp [operation, x.isLt, y.isLt, z.isLt]

/-- The actual FP word operation agrees exactly with coordinatewise Mal'tsev
application on every valid finite-domain tuple, including dimension zero. -/
theorem mapOperation_word {d n : ℕ} (m : Operation (Fin d))
    (x y z : Tuple (Fin d) n) :
    mapOperation d (fun a b c => m (a,b,c)) (word x) (word y) (word z) =
      word (Vector.ofFn (map₃ m (view x) (view y) (view z))) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hin : i < n := by simpa using hi
    have hiw : i < (word x).length := by simpa using hin
    have hx : (word x)[i]'hiw = (view x ⟨i,hin⟩).val := by simp [word, view]
    simp only [mapOperation, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    rw [hx, word_getD y ⟨i,hin⟩, word_getD z ⟨i,hin⟩, operation_fin]
    simp [word, view, map₃]

end ComplexCSP.ComplexityWitnessEncoding
