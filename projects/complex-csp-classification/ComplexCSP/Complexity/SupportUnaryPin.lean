import ComplexCSP.Complexity.SupportConstraintSemantics
import ComplexCSP.Structure.MaltsevTypeRestriction

/-! # Safe unary coordinate pinning for materialized class constructors

The input codec is the unchanged raw witness word restricted to actual encoded
finite-domain Code shapes, allowing dimension zero. A zero-dimensional witness
is explicitly replaced by a fixed one-variable full witness before eager pin
branches; valid coordinate calls retain the exact original constructor result.
-/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityProjectedClosure
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
variable {d n : ℕ}

def ShapedWitness (W : RawWitness) : Prop := ∃ n : ℕ, ∃ U : Code (Fin d) n, W=encodeCode U

noncomputable def shapedWitnessCode (d : ℕ) : BitEncoding {W : RawWitness // ShapedWitness (d:=d) W} :=
  witnessCode.restrict (ShapedWitness (d:=d))

def packCode (W : Code (Fin d) n) : {W : RawWitness // ShapedWitness (d:=d) W} :=
  ⟨encodeCode W,n,W,rfl⟩

def packStored (W : StoredCode d n) : {W : RawWitness // ShapedWitness (d:=d) W} :=
  ⟨(rawTable W,maybeWord W.seed),n,W.toCode,(encodeCode_stored W).symm⟩

def positiveToShaped (W : {W : RawWitness // PositiveWitness (d:=d) W}) :
    {W : RawWitness // ShapedWitness (d:=d) W} :=
  ⟨W.val,by obtain ⟨n,_,U,hU⟩ := W.property; exact ⟨n,U,hU⟩⟩

theorem fp_positiveToShaped : FP (positiveWitnessCode d) (shapedWitnessCode d) positiveToShaped :=
  fp_code_view _ _ _ (fun _ => rfl)

/-- The fallback is concrete finite data, not an assumed pinning or support oracle. -/
def preparePositiveWitness (defaultValue : Fin d)
    (W : {W : RawWitness // ShapedWitness (d:=d) W}) :
    {W : RawWitness // PositiveWitness (d:=d) W} :=
  if h : W.val.1.length=0 then
    ⟨fullCode defaultValue 1,1,by decide,MaltsevWitness.fullCode defaultValue 1,fullCode_encode defaultValue 1⟩
  else ⟨W.val,by
    obtain ⟨n,U,hU⟩ := W.property
    refine ⟨n,?_,U,hU⟩
    have hl : W.val.1.length=n := by rw [hU,encodeCode_table_length]
    omega⟩

theorem fp_preparePositiveWitness (defaultValue : Fin d) :
    FP (shapedWitnessCode d) (positiveWitnessCode d) (preparePositiveWitness defaultValue) := by
  have hv : FP (shapedWitnessCode d) witnessCode (fun p => p.val) := fp_code_view _ _ _ (fun _ => rfl)
  have hn := (hv.comp (fp_fst tableCode maybeCode)).comp (ListCodecMachines.fp_length maybeCode.list)
  have hz := (hn.pair (fp_const (shapedWitnessCode d) BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  have hout := hz.ite (fp_const (shapedWitnessCode d) witnessCode (fullCode defaultValue 1)) hv
  apply hout.transportOutput
  intro W
  by_cases h : W.val.1.length=0
  · simp only [Function.comp_apply,h,ite_true,preparePositiveWitness]
    rfl
  · simp only [Function.comp_apply,h,ite_false,preparePositiveWitness]
    rfl

theorem preparePositiveWitness_actual (defaultValue : Fin d) (W : Code (Fin d) n) (hn : 0<n) :
    (preparePositiveWitness defaultValue (packCode W)).val = encodeCode W := by
  simp [preparePositiveWitness,packCode,encodeCode_table_length,show n≠0 by omega]

def unaryPin (defaultValue : Fin d) (m : Fin d → Fin d → Fin d → Fin d) (a : Fin d)
    (p : {W : RawWitness // ShapedWitness (d:=d) W} × ℕ) :
    {W : RawWitness // PositiveWitness (d:=d) W} :=
  insertScoped m (fun x : Fin 1 → Fin d => decide (x 0=a))
    (prepareScope 1 (preparePositiveWitness defaultValue p.1,[p.2]))

/-- Actual unary-pin adapter, safe at zero dimension and at every runtime index.
The sole input promise is the constructor-produced witness shape, encoded with
exactly the ordinary table/seed word. -/
theorem fp_unaryPin (defaultValue : Fin d) (m : Fin d → Fin d → Fin d → Fin d) (a : Fin d) :
    FP ((shapedWitnessCode d).prod BitEncoding.nat) (positiveWitnessCode d) (unaryPin defaultValue m a) := by
  have hW := (fp_fst (shapedWitnessCode d) BitEncoding.nat).comp (fp_preparePositiveWitness defaultValue)
  have hi := fp_snd (shapedWitnessCode d) BitEncoding.nat
  have hscope := (hi.pair (fp_const ((shapedWitnessCode d).prod BitEncoding.nat) wordCode [])).comp
    (ListMutationMachines.fp_cons BitEncoding.nat)
  exact ((hW.pair hscope).comp (fp_prepareScope 1)).comp
    (fp_insertScoped m (fun x : Fin 1 → Fin d => decide (x 0=a)))

theorem fp_unaryPin_raw (defaultValue : Fin d) (m : Fin d → Fin d → Fin d → Fin d) (a : Fin d) :
    FP ((shapedWitnessCode d).prod BitEncoding.nat) witnessCode
      (fun p => (unaryPin defaultValue m a p).val) :=
  (fp_unaryPin defaultValue m a).transportOutput (fun _ => rfl)

/-- On every actual coordinate, the fallback is inactive and the exact typed
coordinate-pin constructor, including its witness choices, is recovered. -/
theorem unaryPin_encodeCode (defaultValue : Fin d) (m : Operation (Fin d))
    (W : Code (Fin d) n) (i : Fin n) (a : Fin d) :
    (unaryPin defaultValue (fun a b c => m (a,b,c)) a (packCode W,i.val)).val =
      encodeCode (coordinatePinCode m W i a).toCode := by
  have hn : 0<n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hs : [i.val] = scopeWord (fun _ : Fin 1 => i) := by
    simp [scopeWord,List.ofFn_succ]
  change insertConstraint (fun a b c => m (a,b,c)) (fun x : Fin 1 → Fin d => decide (x 0=a))
    ((preparePositiveWitness defaultValue (packCode W)).val,
      safeScope 1 ((preparePositiveWitness defaultValue (packCode W)).val,[i.val])) = _
  rw [preparePositiveWitness_actual defaultValue W hn,hs,safeScope_actual]
  simpa only [coordinatePinCode,storeCode_toCode] using
    insertConstraint_encodeCode m W (fun _ : Fin 1 => i) (fun x => decide (x 0=a))

/-- Raw-output alias for the pinned-class compiler. -/
def coordinatePin (defaultValue : Fin d) (m : Fin d → Fin d → Fin d → Fin d) (a : Fin d)
    (p : {W : RawWitness // ShapedWitness (d:=d) W} × ℕ) : RawWitness :=
  (unaryPin defaultValue m a p).val

theorem fp_coordinatePin (defaultValue : Fin d) (m : Fin d → Fin d → Fin d → Fin d) (a : Fin d) :
    FP ((shapedWitnessCode d).prod BitEncoding.nat) witnessCode (coordinatePin defaultValue m a) :=
  fp_unaryPin_raw defaultValue m a

theorem coordinatePin_encode (defaultValue : Fin d) (m : Operation (Fin d))
    (W : Code (Fin d) n) (i : Fin n) (a : Fin d) :
    coordinatePin defaultValue (fun a b c => m (a,b,c)) a (packCode W,i.val) =
      encodeCode (coordinatePinCode m W i a).toCode :=
  unaryPin_encodeCode defaultValue m W i a

end ComplexCSP.ComplexitySupportWitnessPrimitives
