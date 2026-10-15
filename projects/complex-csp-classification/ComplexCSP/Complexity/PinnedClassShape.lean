import ComplexCSP.Complexity.PinnedClassAgreement
import ComplexCSP.Complexity.LabelExtensionShape

/-! # Unconditional finite-witness shape of capped class construction

These results hold for arbitrary operation tables, labels and caps. They need
no support relation, Correct witness, Maltsev identity, or query-correctness
hypothesis, and therefore support the outer capped machine invariant.
-/
noncomputable section
namespace ComplexCSP.ComplexityPinnedClass
open MaltsevWitness MaltsevRelations WeightedMaltsev ComplexityWitnessEncoding
open ComplexityWitnessPrimitives ComplexitySupportWitnessPrimitives ComplexityProjectedClosure
open ComplexityLabelExtension
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension n : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Operation (Fin d)) (space : Polynomial ℕ) (defaultValue : Fin d)
variable (base : ComplexityTypeRowCallback.Context K) (W : Code (Fin d) n)

/-- At most one word, and every coordinate is a color of the fixed domain. -/
def MaybeShape (d n : ℕ) (ws : MaybeWord) : Prop :=
  ∃ o : Option (Tuple (Fin d) n), ws=maybeWord o

theorem seed_shape (wanted : RowLabel K d) (a : Fin d) :
    MaybeShape d n (seed L basis (curried m) space a (inputView (packContext base W,wanted))) := by
  unfold seed
  have ht : List.replicate n a.val=word (Vector.ofFn (fun _ : Fin n => a)) := by
    simp [word,Vector.toList_ofFn,List.ofFn_const]
  change MaybeShape d n ((extendQuery L basis (curried m) space
    ((packContext base W).val,wanted,0,List.replicate n a.val)).toList)
  rw [ht,packContext_store]
  cases h : extendQuery L basis (curried m) space
    (ComplexityTypeStackConcrete.storedContext base (storeCode W),wanted,0,
      word (Vector.ofFn (fun _ : Fin n => a))) with
  | none => exact ⟨none,rfl⟩
  | some w =>
    obtain ⟨x,hx⟩ := extendQuery_stored_shape L basis m space base (storeCode W) wanted 0
      (Nat.zero_le n) (Vector.ofFn (fun _ => a)) h
    exact ⟨some x,by simp [maybeWord,hx]⟩

theorem extension_shape (wanted : RowLabel K d) (i : Fin n) (a : Fin d) (z : Tuple (Fin d) n) :
    MaybeShape d n (extension L basis (curried m) space
      (inputView (packContext base W,wanted),i.val,a.val,word z)) := by
  unfold extension
  rw [replaceAt_word]
  change MaybeShape d n ((extendQuery L basis (curried m) space
    ((packContext base W).val,wanted,i.val+1,word (replaceCoordinate z i a))).toList)
  rw [packContext_store]
  cases h : extendQuery L basis (curried m) space
    (ComplexityTypeStackConcrete.storedContext base (storeCode W),wanted,i.val+1,
      word (replaceCoordinate z i a)) with
  | none => exact ⟨none,rfl⟩
  | some w =>
    obtain ⟨x,hx⟩ := extendQuery_stored_shape L basis m space base (storeCode W) wanted (i.val+1)
      (by have := i.isLt; omega) (replaceCoordinate z i a) h
    exact ⟨some x,by simp [maybeWord,hx]⟩

theorem coordinateWitness_shape (wanted : RowLabel K d) (i : Fin n) (a : Fin d) :
    MaybeShape d n (coordinateWitness L basis (curried m) space defaultValue a
      ((packContext base W,wanted),i.val)) := by
  unfold coordinateWitness
  have hp : pinnedInput (curried m) defaultValue a ((packContext base W,wanted),i.val)=
      inputView (packContext base (coordinatePinCode m W i a).toCode,wanted) := by
    unfold pinnedInput inputView packContext
    have hw : contextWitness (⟨(base,n,encodeCode W),W,rfl⟩ : Context K d)=packCode W := rfl
    rw [hw,unaryPin_encodeCode]
  rw [hp]
  exact seed_shape L basis m space base (coordinatePinCode m W i a).toCode wanted a

theorem candidates_shape (wanted : RowLabel K d) (i : Fin n) {w : List ℕ}
    (hw : w∈candidates L basis (curried m) space defaultValue ((packContext base W,wanted),i.val)) :
    ∃ x : Tuple (Fin d) n, w=word x := by
  obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hw
  obtain ⟨o,ho⟩ := coordinateWitness_shape L basis m space defaultValue base W wanted i a
  rw [ho] at ha
  cases o with
  | none => simp [maybeWord] at ha
  | some x => exact ⟨x,by simpa [maybeWord] using ha⟩

theorem lookup_shape (wanted : RowLabel K d) (i : Fin n) (a : Fin d) :
    MaybeShape d n (lookup L basis (curried m) space defaultValue ((packContext base W,wanted),i.val,a.val)) := by
  unfold lookup lookupFrom anchor ComplexitySupportWitnessPrimitives.first
  cases hf : (candidates L basis (curried m) space defaultValue ((packContext base W,wanted),i.val)).filter
    (fun w => accepts L basis (curried m) space ((inputView (packContext base W,wanted),i.val,a.val),w)) with
  | nil => exact ⟨none,rfl⟩
  | cons w ws =>
    have hw : w∈candidates L basis (curried m) space defaultValue ((packContext base W,wanted),i.val) :=
      List.mem_of_mem_filter (by rw [hf]; exact List.mem_cons_self)
    obtain ⟨z,rfl⟩ := candidates_shape L basis m space defaultValue base W wanted i hw
    simpa only [List.head?_cons,Option.toList_some,List.cons_ne_self,↓reduceIte,List.headD_cons,probe] using
      extension_shape L basis m space base W wanted i a z

theorem build_shape (wanted : RowLabel K d) :
    ∃ U : Code (Fin d) n, build L basis (curried m) space defaultValue (packContext base W,wanted)=encodeCode U := by
  choose seedValue hseed using seed_shape L basis m space base W wanted defaultValue
  have hc := fun (i : Fin n) (a : Fin d) => lookup_shape L basis m space defaultValue base W wanted i a
  choose cells hcells using hc
  refine ⟨⟨seedValue,cells⟩,?_⟩
  apply Prod.ext
  · apply List.ext_getElem
    · simp [build,encodeCode,packContext]
    · intro i hi hi'
      have hin : i<n := by simpa [encodeCode] using hi'
      simp only [build,packContext,encodeCode,List.getElem_map,List.getElem_range,List.getElem_ofFn]
      apply List.ext_getElem
      · simp
      · intro a ha ha'
        have had : a<d := by simpa using ha'
        simp only [List.getElem_map,List.getElem_finRange,List.getElem_ofFn]
        simpa only [packContext,encodeCode,Fin.val_cast] using hcells ⟨i,hin⟩ ⟨a,had⟩
  · exact hseed

theorem build_shape_context (c : Context K d) (wanted : RowLabel K d) :
    ∃ U : Code (Fin d) c.val.2.1, build L basis (curried m) space defaultValue (c,wanted)=encodeCode U := by
  obtain ⟨W,hW⟩ := c.property
  have hc : c=packContext c.val.1 W := by apply Subtype.ext; exact Prod.ext rfl (Prod.ext rfl hW)
  have h := build_shape L basis m space defaultValue c.val.1 W wanted
  simpa only [←hc] using h

end ComplexCSP.ComplexityPinnedClass
