import ComplexCSP.Complexity.SupportPrefixFrame
import ComplexCSP.Structure.MaltsevWitnessConstraint

/-! # Exact ordered prefix-frame agreement -/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityProjectedClosure
variable {d n : ℕ}

private theorem fold_prefix_cons (m : Fin d → Fin d → Fin d → Fin d)
    (a : ℕ) (state : PrefixState) (xs : List ℕ) :
    xs.foldl (prefixStep d m) (a::state.1,state.2) =
      let result := xs.foldl (prefixStep d m) state
      (a::result.1,result.2) := by
  induction xs generalizing state with
  | nil => rfl
  | cons b xs ih => exact ih (prefixStep d m state b)

private theorem frameRows_cons (a : ℕ) (state : PrefixState) :
    frameRows (a::state.1,state.2) = (frameRows state).map (List.cons a) := by
  simp only [frameRows,List.map_map,Function.comp_def,List.cons_append]

/-- Operational prefix peeling uses the original first-anchor choices. -/
theorem prefixFrame_cons (m : Fin d → Fin d → Fin d → Fin d)
    (W : RawWitness) (a : ℕ) (target : List ℕ) (k : ℕ) :
    prefixFrame d m (W,a::target,k+1) =
      (prefixFrame d m (pinDrop d m (W,a),target,k)).map (List.cons a) := by
  simp only [prefixFrame,List.take_succ_cons,List.foldl_cons,prefixStep,List.nil_append]
  rw [fold_prefix_cons m a ([],pinDrop d m (W,a)) (target.take k)]
  exact frameRows_cons a _

private theorem word_ofFn (x : Tuple (Fin d) n) :
    word x = List.ofFn (fun i => (view x i).val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [word,view]

theorem word_head_tail (x : Tuple (Fin d) (n+1)) :
    word x = (view x 0).val :: word (tailTuple x) := by
  simp only [word_ofFn,List.ofFn_succ,tailTuple,view_ofFn]

theorem consTuple_word (a : Fin d) (x : Tuple (Fin d) n) :
    word (consTuple a x) = a.val :: word x := by
  simp only [word_ofFn,consTuple,view_ofFn,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]

/-- The raw fold returns exactly the mathematical prefix-frame list, in order.
This bridge is independent of the relation represented by the witness. -/
theorem prefixFrame_word (m : Operation (Fin d)) (W : Code (Fin d) n)
    (target : Tuple (Fin d) n) (k : ℕ) :
    prefixFrame d (fun a b c => m (a,b,c)) (encodeCode W,word target,k) =
      (MaltsevWitness.prefixFrame m W target k).map word := by
  induction k generalizing n with
  | zero => simp [prefixFrame,frameRows,MaltsevWitness.prefixFrame,storedRows_encodeCode]
  | succ k ih =>
    cases n with
    | zero =>
      have hw : word target = [] := List.length_eq_zero_iff.mp (word_length target)
      simp [prefixFrame,frameRows,MaltsevWitness.prefixFrame,hw,storedRows_encodeCode]
    | succ n =>
      rw [word_head_tail,prefixFrame_cons,pinDrop_encodeCode,ih]
      simp only [MaltsevWitness.prefixFrame,storeCode_toCode,List.map_map,Function.comp_def,consTuple_word]

/-- Typed callers prepare the restricted input using only erased proofs. -/
theorem prefixInputValid_encode (W : Code (Fin d) n) (target : Tuple (Fin d) n) (k : ℕ) :
    PrefixInputValid d (encodeCode W,word target,k) := by
  refine ⟨n,W,rfl,(word_length target).le,?_⟩
  intro a ha
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp ha
  exact c.isLt

end ComplexCSP.ComplexitySupportWitnessPrimitives
