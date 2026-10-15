import ComplexCSP.Complexity.WitnessUnion
import ComplexCSP.Complexity.SupportWitnessSemantics

/-! # Exact union-witness machine agreement, including empty families -/
namespace ComplexCSP.ComplexityWitnessUnion
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexitySupportWitnessPrimitives
variable {ι : Type} {d n : ℕ}

private theorem first_flatMap_maybeWord (xs : List ι) (f : ι → Option (Tuple (Fin d) n)) :
    first (xs.flatMap (fun i => maybeWord (f i))) = maybeWord (xs.findSome? f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : f x with
    | none => simpa only [List.flatMap_cons,hx,maybeWord,Option.toList_none,List.map_nil,
        List.nil_append,List.findSome?,hx] using ih
    | some z => simp [List.flatMap_cons,maybeWord,hx,ComplexitySupportWitnessPrimitives.first,List.findSome?]

theorem extension_encode (m : Operation (Fin d)) (indices : List ι) (W : ι → Code (Fin d) n)
    (i : Fin n) (a : Fin d) (z : Tuple (Fin d) n) :
    extension (fun x y z => m (x,y,z)) (indices.map (fun p => encodeCode (W p)),i.val,a.val,word z) =
      maybeWord (unionExtension m indices W i a z) := by
  have h : ∀ p, reconstructRawTo d (fun x y z => m (x,y,z)) (encodeCode (W p)).1
      (MaltsevTypeStack.replaceAt (word z) i.val a.val) (encodeCode (W p)).2 (i.val+1) =
      maybeWord (reconstructTo m (W p) (replaceCoordinate z i a) (i.val+1)) := by
    intro p
    rw [replaceAt_word,encodeCode_store]
    simpa only [storeCode_toCode] using reconstructRawTo_stored m (storeCode (W p))
      (replaceCoordinate z i a) (i.val+1) (by omega)
  change first ((indices.map (fun p => encodeCode (W p))).flatMap _) = _
  rw [List.flatMap_map]
  simp only [h]
  exact first_flatMap_maybeWord indices _

theorem candidates_encode (indices : List ι) (W : ι → Code (Fin d) n) (i : Fin n) :
    candidates (indices.map (fun p => encodeCode (W p)),i.val) =
      (unionCandidates indices W i).map word := by
  simp only [candidates,List.flatMap_map,unionCandidates,List.map_flatMap]
  congr 1
  funext p
  simp [encodeCode,List.getD_eq_getElem?_getD,i.isLt,List.map_ofFn,maybeWord,List.flatMap_def,Function.comp_def]

theorem anchor_encode (m : Operation (Fin d)) (indices : List ι) (W : ι → Code (Fin d) n)
    (i : Fin n) (a : Fin d) :
    anchor (fun x y z => m (x,y,z)) (indices.map (fun p => encodeCode (W p)),i.val,a.val) =
      maybeWord (unionAnchor m indices W i a) := by
  rw [anchor,candidates_encode,List.filter_map]
  simp only [Function.comp_def,extension_encode]
  have h : ∀ z : Tuple (Fin d) n, decide (maybeWord (unionExtension m indices W i a z) ≠ []) =
      (unionExtension m indices W i a z).isSome := by
    intro z
    cases h : unionExtension m indices W i a z <;> simp [maybeWord]
  simp_rw [h]
  rw [first_map_word,List.head?_filter]
  rfl

theorem lookup_encode (m : Operation (Fin d)) (indices : List ι) (W : ι → Code (Fin d) n)
    (i : Fin n) (a : Fin d) :
    lookup (fun x y z => m (x,y,z)) (indices.map (fun p => encodeCode (W p)),i.val,a.val) =
      maybeWord ((unionCode m indices W).lookup i a) := by
  rw [lookup,anchor_encode]
  cases h : unionAnchor m indices W i a with
  | none => simp [maybeWord,unionCode,h]
  | some z => simpa [maybeWord,unionCode,h] using extension_encode m indices W i a z

private theorem map_range_eq_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp

/-- Literal table/seed equality is independent of semantic Correct hypotheses.
In particular, an empty union still contains n*d absent lookup slots. -/
theorem build_encode (m : Operation (Fin d)) (indices : List ι) (W : ι → Code (Fin d) n) :
    build (fun x y z => m (x,y,z)) (n,indices.map (fun p => encodeCode (W p))) =
      encodeCode (unionCode m indices W) := by
  apply Prod.ext
  · simp only [build,map_range_eq_ofFn,encodeCode]
    congr 1
    funext i
    congr 1
    funext a
    exact lookup_encode m indices W i a
  · change first ((indices.map (fun p => encodeCode (W p))).flatMap Prod.snd) = _
    simp only [List.flatMap_map,encodeCode]
    exact first_flatMap_maybeWord indices (fun p => (W p).seed)

end ComplexCSP.ComplexityWitnessUnion
