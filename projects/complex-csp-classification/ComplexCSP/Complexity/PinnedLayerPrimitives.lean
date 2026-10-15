import ComplexCSP.Complexity.SupportFullCode
import ComplexCSP.Complexity.TypeRowCallback
import ComplexCSP.Structure.WeightedMaltsevPinnedLayer
import PlanarHom.ListPrefixMachines

/-! # Concrete projections and weighted class serialization

All tuple and witness operations act on literal runtime lists. Projection also
handles dimension zero, retaining a present empty tuple as `[[]]` rather than
confusing it with a missing witness. Label serialization uses the actual fixed
field sum machine.
-/
namespace ComplexCSP.ComplexityPinnedLayer
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexitySupportWitnessPrimitives
open ComplexityTypeStackMachines MaltsevWitness WeightedMaltsev

/-- Fixed finite parallel branches are real list-constructor programs. -/
theorem fp_fixedList {A X Y : Type} (ex : BitEncoding X) (ey : BitEncoding Y)
    (as : List A) (f : X → A → Y) (hf : ∀ a ∈ as, FP ex ey (fun x => f x a)) :
    FP ex ey.list (fun x => as.map (f x)) := by
  induction as with
  | nil => exact fp_const _ _ []
  | cons a as ih => exact ((hf a (by simp)).pair
      (ih (fun b hb => hf b (by simp [hb])))).comp (ListMutationMachines.fp_cons ey)

def projectWitness (p : ℕ × RawWitness) : RawWitness :=
  ((p.2.1.take p.1).map (fun row => row.map (fun ws => ws.map (List.take p.1))),
    p.2.2.map (List.take p.1))

theorem fp_projectWitness : FP (BitEncoding.unaryNat.prod witnessCode) witnessCode projectWitness := by
  let ei := BitEncoding.unaryNat.prod witnessCode
  have hn := (fp_fst BitEncoding.unaryNat witnessCode).comp UnaryNatConversionMachine.fp_conversion
  have hw := fp_snd BitEncoding.unaryNat witnessCode
  have ht := hw.comp (fp_fst tableCode maybeCode)
  have hs := hw.comp (fp_snd tableCode maybeCode)
  have htake : FP (BitEncoding.nat.prod wordCode) wordCode (fun p => p.2.take p.1) :=
    ((fp_snd BitEncoding.nat wordCode).pair (fp_fst BitEncoding.nat wordCode)).comp
      (ListPrefixMachines.fp_take BitEncoding.nat)
  have hm := ListContextMachines.fp_mapWithContext BitEncoding.nat wordCode wordCode _ htake
  have hr := ListContextMachines.fp_mapWithContext BitEncoding.nat maybeCode maybeCode _ hm
  have htableTake := (ht.pair hn).comp (ListPrefixMachines.fp_take maybeCode.list)
  have htable := (hn.pair htableTake).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat maybeCode.list maybeCode.list _ hr)
  exact htable.pair ((hn.pair hs).comp hm)

theorem word_project {d n k : ℕ} (hk : k ≤ n) (x : Tuple (Fin d) n) :
    (word x).take k = word (Vector.ofFn (fun i : Fin k => view x (Fin.castLE hk i))) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hk]
  · intro j hj hj'
    simp [word,view]

theorem projectWitness_encode {d n k : ℕ} (W : Code (Fin d) n) (hk : k ≤ n) :
    projectWitness (k,encodeCode W) = encodeCode (projectCode W k hk) := by
  apply Prod.ext
  · apply List.ext_getElem
    · simp [projectWitness,encodeCode,Nat.min_eq_left hk]
    · intro i hi hi'
      have hi : i < k := by simpa [encodeCode] using hi'
      have hin : i < n := lt_of_lt_of_le hi hk
      simp only [projectWitness,encodeCode,List.getElem_map,List.getElem_take,List.getElem_ofFn]
      rw [List.map_ofFn]
      congr 1
      funext a
      cases h : W.lookup ⟨i,hin⟩ a <;>
        simp [maybeWord,projectCode,h,word_project hk]
  · change (W.seed.toList.map word).map (List.take k) = _
    cases h : W.seed <;> simp [encodeCode,projectCode,maybeWord,h,word_project hk]

variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

noncomputable def rawLabelCode : BitEncoding (List (ℕ × (Fin d → K))) :=
  (BitEncoding.nat.prod (ComplexityRowNormalization.rowEncoding basis d)).list

def rawLabel (label : RowLabel K d) : List (ℕ × (Fin d → K)) :=
  (decodeLabel label).toList.map (fun p => (p.1.val,p.2))

omit [DecidableEq K] in
theorem fp_rawLabel : FP (ComplexityCSPMarginalRowBounds.labelEncoding basis d)
    (rawLabelCode (d:=d) basis) rawLabel := fp_code_view _ _ _ (fun _ => rfl)

omit [DecidableEq K] in
theorem fp_labelAnchor : FP (ComplexityCSPMarginalRowBounds.labelEncoding basis d)
    BitEncoding.nat labelAnchor := by
  have h := ((fp_rawLabel (d:=d) basis).comp
    (ListDecompositionMachines.fp_headD
      (BitEncoding.nat.prod (ComplexityRowNormalization.rowEncoding basis d)) (0,fun _ => 0))).comp
      (fp_fst BitEncoding.nat (ComplexityRowNormalization.rowEncoding basis d))
  exact h.congr (fun a => by cases a <;> rfl)

omit [DecidableEq K] in
theorem fp_labelFactor : FP (ComplexityCSPMarginalRowBounds.labelEncoding basis d)
    (numberFieldEncoding basis) labelFactor := by
  have h := (((fp_rawLabel (d:=d) basis).comp
    (ListDecompositionMachines.fp_headD
      (BitEncoding.nat.prod (ComplexityRowNormalization.rowEncoding basis d)) (0,fun _ => 0))).comp
      (fp_snd BitEncoding.nat (ComplexityRowNormalization.rowEncoding basis d))).comp
        (ComplexityRowNormalization.fp_rowSum basis)
  apply h.congr
  intro a
  cases a <;> simp [rawLabel,decodeLabel,labelFactor,ComplexityRowNormalization.rowSum]

def packClass (p : RowLabel K d × RawWitness) : ComplexityWeightedLayers.ClassRecord K :=
  (labelAnchor p.1,labelFactor p.1,p.2)

omit [DecidableEq K] in
theorem fp_packClass :
    FP ((ComplexityCSPMarginalRowBounds.labelEncoding basis d).prod witnessCode)
      (ComplexityWeightedLayers.classCode basis) packClass := by
  have hl := fp_fst (ComplexityCSPMarginalRowBounds.labelEncoding basis d) witnessCode
  have hw := fp_snd (ComplexityCSPMarginalRowBounds.labelEncoding basis d) witnessCode
  exact (hl.comp (fp_labelAnchor basis)).pair ((hl.comp (fp_labelFactor basis)).pair hw)

omit [DecidableEq K] [Algebra ℚ K] in
theorem packClass_encode {n : ℕ} (label : RowLabel K d) (W : StoredCode d n) :
    packClass (label,encodeCode W.toCode) = encodeClass (label,W) := by
  rw [encodeCode_stored]
  rfl

end ComplexCSP.ComplexityPinnedLayer
