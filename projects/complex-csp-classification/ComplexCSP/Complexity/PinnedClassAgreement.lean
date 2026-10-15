import ComplexCSP.Complexity.PinnedLayer
import ComplexCSP.Complexity.LabelExtensionMarginal

/-! # Literal agreement of the compiled class constructor

The compositional interface in this file is discharged from the proved shared
marginal-query bound in ComplexityPinnedLayerCorrectness. It records exact
witness choices, rather than merely asserting existence of some Correct code.
-/
namespace ComplexCSP.ComplexityPinnedClass
open MaltsevWitness MaltsevRelations WeightedMaltsev ComplexityWitnessEncoding
open ComplexityWitnessPrimitives ComplexitySupportWitnessPrimitives ComplexityProjectedClosure
open ComplexityLabelExtension
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension n : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Operation (Fin d)) (space : Polynomial ℕ) (defaultValue : Fin d)
variable (base : ComplexityTypeRowCallback.Context K) (W : Code (Fin d) n)
variable (label : Tuple (Fin d) n → RowLabel K d)

/-- Exact subprogram agreement, used only as an internal compositional lemma. -/
def ExtensionAgrees : Prop := ∀ (wanted : RowLabel K d) (fuel len : ℕ), len+fuel=n →
  ∀ target : Tuple (Fin d) n,
    extendQuery L basis (curried m) space ((packContext base W).val,wanted,len,word target)=
      (labelExtension m W label wanted fuel len target).map word

omit [Field K] [DecidableEq K] [Algebra ℚ K] in
theorem packContext_store : (packContext base W).val =
    ComplexityTypeStackConcrete.storedContext base (storeCode W) := by
  simp only [packContext,ComplexityTypeStackConcrete.storedContext,encodeCode_store]

omit [Field K] [DecidableEq K] [Algebra ℚ K] in
theorem packContext_stored (U : StoredCode d n) : (packContext base U.toCode).val =
    ComplexityTypeStackConcrete.storedContext base U := by
  simp only [packContext,ComplexityTypeStackConcrete.storedContext,encodeCode_stored]

variable (hext : ExtensionAgrees L basis m space base W label)
include hext in
theorem seed_eq (wanted : RowLabel K d) (a : Fin d) :
    seed L basis (curried m) space a (inputView (packContext base W,wanted)) =
      maybeWord (labelExtension m W label wanted n 0 (Vector.ofFn (fun _ => a))) := by
  unfold seed
  have ht : List.replicate n a.val=word (Vector.ofFn (fun _ : Fin n => a)) := by
    simp [word,Vector.toList_ofFn,List.ofFn_const]
  change (extendQuery L basis (curried m) space
    ((packContext base W).val,wanted,0,List.replicate n a.val)).toList=_
  rw [ht,hext wanted n 0 (by omega)]
  simp only [maybeWord,Option.toList_map]

include hext in
theorem extension_eq (wanted : RowLabel K d) (i : Fin n) (a : Fin d) (z : Tuple (Fin d) n) :
    extension L basis (curried m) space
      (inputView (packContext base W,wanted),i.val,a.val,word z)=
      maybeWord (typeClassExtension m W label wanted i a z) := by
  unfold extension
  rw [replaceAt_word]
  change (extendQuery L basis (curried m) space
    ((packContext base W).val,wanted,i.val+1,word (replaceCoordinate z i a))).toList=_
  rw [hext wanted (n-(i.val+1)) (i.val+1) (by have := i.isLt; omega)]
  simp only [typeClassExtension,maybeWord,Option.toList_map]

variable (hpins : ∀ (i : Fin n) (a : Fin d), ExtensionAgrees L basis m space base
  (coordinatePinCode m W i a).toCode label)

include hpins in
theorem coordinateWitness_eq (wanted : RowLabel K d) (i : Fin n) (a : Fin d) :
    coordinateWitness L basis (curried m) space defaultValue a ( (packContext base W,wanted),i.val)=
      maybeWord (pinnedTypeCoordinateWitness m W label wanted i a) := by
  unfold coordinateWitness
  have hp : pinnedInput (curried m) defaultValue a ((packContext base W,wanted),i.val)=
      inputView (packContext base (coordinatePinCode m W i a).toCode,wanted) := by
    unfold pinnedInput inputView packContext
    have hw : contextWitness (⟨(base,n,encodeCode W),W,rfl⟩ : Context K d)=packCode W := rfl
    rw [hw,unaryPin_encodeCode]
  rw [hp]
  exact seed_eq L basis m space base (coordinatePinCode m W i a).toCode label (hpins i a) wanted a

include hpins in
theorem candidates_eq (wanted : RowLabel K d) (i : Fin n) :
    candidates L basis (curried m) space defaultValue ((packContext base W,wanted),i.val)=
      (pinnedTypeClassCandidates m W label wanted i).map word := by
  unfold candidates
  simp_rw [coordinateWitness_eq L basis m space defaultValue base W label hpins]
  simp only [pinnedTypeClassCandidates,maybeWord,List.flatMap_def,List.map_flatten,List.map_map]
  congr 1
  simp [List.ofFn_eq_map]

include hext hpins in
theorem anchor_eq (wanted : RowLabel K d) (i : Fin n) (a : Fin d) :
    anchor L basis (curried m) space
      ((inputView (packContext base W,wanted),i.val,a.val),
        candidates L basis (curried m) space defaultValue ((packContext base W,wanted),i.val))=
      maybeWord (pinnedTypeClassAnchor m W label wanted i a) := by
  rw [candidates_eq L basis m space defaultValue base W label hpins]
  unfold anchor
  rw [List.filter_map]
  have ht : ∀ z : Tuple (Fin d) n,
      accepts L basis (curried m) space ((inputView (packContext base W,wanted),i.val,a.val),word z)=
        (typeClassExtension m W label wanted i a z).isSome := by
    intro z
    unfold accepts probe
    rw [extension_eq L basis m space base W label hext]
    cases h : typeClassExtension m W label wanted i a z <;> simp [maybeWord]
  rw [first_map_word,List.head?_filter]
  have hf : ((fun w => accepts L basis (curried m) space
      ((inputView (packContext base W,wanted),i.val,a.val),w)) ∘ word) =
      (fun z => (typeClassExtension m W label wanted i a z).isSome) := funext ht
  rw [hf]
  rfl

include hext hpins in
theorem lookup_eq (wanted : RowLabel K d) (i : Fin n) (a : Fin d) :
    lookup L basis (curried m) space defaultValue ((packContext base W,wanted),i.val,a.val)=
      maybeWord ((pinnedTypeClassCode m W label wanted defaultValue).lookup i a) := by
  unfold lookup lookupFrom
  rw [anchor_eq L basis m space defaultValue base W label hext hpins]
  cases ha : pinnedTypeClassAnchor m W label wanted i a with
  | none => simp [maybeWord,pinnedTypeClassCode,ha]
  | some z =>
    simp only [maybeWord,Option.toList_some,List.map_singleton,List.cons_ne_self,↓reduceIte,List.headD_cons]
    change extension L basis (curried m) space
      (inputView (packContext base W,wanted),i.val,a.val,word z)=_
    rw [extension_eq L basis m space base W label hext]
    simp [pinnedTypeClassCode,ha,maybeWord]

include hext hpins in
theorem build_eq (wanted : RowLabel K d) :
    build L basis (curried m) space defaultValue (packContext base W,wanted)=
      encodeCode (pinnedTypeClassCode m W label wanted defaultValue) := by
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
        simpa only [packContext, encodeCode, Fin.val_cast] using
          lookup_eq L basis m space defaultValue base W label hext hpins wanted ⟨i,hin⟩ ⟨a,had⟩
  · exact seed_eq L basis m space base W label hext wanted defaultValue

end ComplexCSP.ComplexityPinnedClass
