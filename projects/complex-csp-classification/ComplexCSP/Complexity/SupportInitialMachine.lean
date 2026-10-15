import ComplexCSP.Complexity.SupportUnaryPin
import ComplexCSP.Complexity.WitnessSizeBounds
import ComplexCSP.Structure.MaltsevCSPCode

/-! # Actual FP initial-support compilation on raw CSP codes

The language, finite domain and operation are fixed. Every symbol branch is
compiled from its fixed Boolean support table. Invalid rows are explicitly
skipped; every eagerly materialized alternative receives a safe prepared scope.
All witness states have the original positive dimension, giving a single proved
polynomial bound throughout the constraint fold. Dimension zero is handled by
an explicit one-variable safe preparation and final empty-tuple selection.
-/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityWitnessSizeBounds ComplexityCSPValidation
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.MachineComposition

private theorem fp_finiteCase {A B : Type} (ea : BitEncoding A) (eb : BitEncoding B)
    (n : ℕ) (key : A → ℕ) (hk : FP ea BitEncoding.nat key)
    (f : Fin n → A → B) (hf : ∀ i, FP ea eb (f i)) (fallback : A → B)
    (hd : FP ea eb fallback) :
    FP ea eb (fun a => if h : key a < n then f ⟨key a,h⟩ a else fallback a) := by
  induction n with
  | zero => simpa using hd
  | succ n ih =>
    let g : Fin n → A → B := fun i => f i.castSucc
    have hg : ∀ i, FP ea eb (g i) := fun i => hf i.castSucc
    have hrec := ih g hg
    have ht := (hk.pair (fp_const ea BitEncoding.nat n)).comp NatListSumMachines.fp_equal
    apply (ht.ite (hf (Fin.last n)) hrec).congr
    intro a
    by_cases he : key a=n
    · simp only [he,Nat.lt_succ_self,↓reduceDIte,↓reduceIte]
      rfl
    · simp only [he,↓reduceIte]
      by_cases hlt : key a<n
      · simp only [hlt,↓reduceDIte,show key a<n+1 by omega]
        rfl
      · simp only [hlt,↓reduceDIte,show ¬key a<n+1 by omega]

variable {K : Type} [Zero K] [DecidableEq K] {d s : ℕ}
variable (L : Language (Fin d) K (Fin s)) (m : Fin d → Fin d → Fin d → Fin d)

abbrev PositiveData (d : ℕ) := {W : RawWitness // PositiveWitness (d:=d) W}
abbrev RawConstraint := ℕ × List ℕ

def insertBySymbol (p : PositiveData d × RawConstraint) : PositiveData d :=
  if h : p.2.1<s then
    let i : Fin s := ⟨p.2.1,h⟩
    insertScoped m (fun x => decide (L.value i x ≠ 0)) (prepareScope (L.arity i) (p.1,p.2.2))
  else p.1

theorem fp_insertBySymbol : FP ((positiveWitnessCode d).prod ComplexityCSPCode.constraintEncoding)
    (positiveWitnessCode d) (insertBySymbol L m) := by
  let e := (positiveWitnessCode d).prod ComplexityCSPCode.constraintEncoding
  have hW := fp_fst (positiveWitnessCode d) ComplexityCSPCode.constraintEncoding
  have hc := fp_snd (positiveWitnessCode d) ComplexityCSPCode.constraintEncoding
  have hsymbol := hc.comp (fp_fst BitEncoding.nat wordCode)
  have hscope := hc.comp (fp_snd BitEncoding.nat wordCode)
  exact fp_finiteCase e (positiveWitnessCode d) s (fun p => p.2.1) hsymbol _
    (fun i => ((hW.pair hscope).comp (fp_prepareScope (L.arity i))).comp
      (fp_insertScoped m (fun x => decide (L.value i x ≠ 0)))) _ hW

def supportStep (W : PositiveData d) (c : RawConstraint) : PositiveData d :=
  if constraintValidTest L (W.val.1.length,c) then insertBySymbol L m (W,c) else W

theorem fp_supportStep : FP ((positiveWitnessCode d).prod ComplexityCSPCode.constraintEncoding)
    (positiveWitnessCode d) (fun p => supportStep L m p.1 p.2) := by
  let e := (positiveWitnessCode d).prod ComplexityCSPCode.constraintEncoding
  have hW := fp_fst (positiveWitnessCode d) ComplexityCSPCode.constraintEncoding
  have hv : FP (positiveWitnessCode d) witnessCode (fun p => p.val) := fp_code_view _ _ _ (fun _ => rfl)
  have hn := ((hW.comp hv).comp (fp_fst tableCode maybeCode)).comp
    (ListUnaryLengthMachine.fp_length maybeCode.list)
  have hc := fp_snd (positiveWitnessCode d) ComplexityCSPCode.constraintEncoding
  have ht := (hn.pair hc).comp (fp_constraintValidTest L)
  have ht' : FP e BitEncoding.bool (fun p => decide (constraintValidTest L (p.1.val.1.length,p.2)=true)) :=
    ht.congr (fun p => by
      change constraintValidTest L (p.1.val.1.length,p.2) = decide (constraintValidTest L (p.1.val.1.length,p.2)=true)
      cases constraintValidTest L (p.1.val.1.length,p.2) <;> rfl)
  exact ht'.ite (fp_insertBySymbol L m) hW

@[simp] theorem insertBySymbol_dimension (p : PositiveData d × RawConstraint) :
    (insertBySymbol L m p).val.1.length = p.1.val.1.length := by
  unfold insertBySymbol
  split
  · exact insertScoped_dimension _ _ _
  · rfl

@[simp] theorem supportStep_dimension (W : PositiveData d) (c : RawConstraint) :
    (supportStep L m W c).val.1.length = W.val.1.length := by
  unfold supportStep
  split
  · exact insertBySymbol_dimension L m _
  · rfl

theorem fold_supportStep_dimension (W : PositiveData d) (cs : List RawConstraint) :
    (cs.foldl (supportStep L m) W).val.1.length = W.val.1.length := by
  induction cs generalizing W with
  | nil => rfl
  | cons c cs ih => rw [List.foldl_cons,ih,supportStep_dimension]

omit [Zero K] [DecidableEq K] in
theorem positive_code_bound (W : PositiveData d) :
    ((positiveWitnessCode d).encode W).length ≤ (storedPolynomial d).eval W.val.1.length := by
  obtain ⟨n,_,U,hU⟩ := W.property
  change (witnessCode.encode W.val).length ≤ _
  rw [hU,encodeCode_table_length,encodeCode_store]
  exact stored_code_bound (storeCode U)

omit [Zero K] [DecidableEq K] in
theorem positive_dimension_le_code (W : PositiveData d) :
    W.val.1.length ≤ ((positiveWitnessCode d).encode W).length := by
  have h := BitEncoding.list_length_le maybeCode.list W.val.1
  change W.val.1.length ≤ (tableCode.encode W.val.1).length at h
  change W.val.1.length ≤ (witnessCode.encode W.val).length
  rw [BitEncoding.prod_length]
  omega

/-- Every intermediate actual support witness has one original-input bound. -/
theorem support_fold_bound (W : PositiveData d) (cs : List RawConstraint) (i : ℕ) :
    ((positiveWitnessCode d).encode ((cs.take i).foldl (supportStep L m) W)).length ≤
      (storedPolynomial d).eval (((positiveWitnessCode d).prod ComplexityCSPCode.constraintEncoding.list).encode (W,cs)).length := by
  have h := positive_code_bound ((cs.take i).foldl (supportStep L m) W)
  rw [fold_supportStep_dimension] at h
  apply h.trans
  apply natPolynomial_monotone
  have hd := positive_dimension_le_code W
  rw [BitEncoding.prod_length]
  dsimp only
  omega

/-- Every raw row is checked by the actual validator before its selected result
is retained. Eager unselected insertion branches use the safe scope preparer. -/
theorem fp_supportFold : FP ((positiveWitnessCode d).prod ComplexityCSPCode.constraintEncoding.list)
    (positiveWitnessCode d) (fun p => p.2.foldl (supportStep L m) p.1) :=
  ListFoldMachines.fp_foldl ComplexityCSPCode.constraintEncoding (positiveWitnessCode d)
    (supportStep L m) (fp_supportStep L m) (storedPolynomial d)
    (fun W cs i _ => support_fold_bound L m W cs i)

def fullShaped (defaultValue : Fin d) (n : ℕ) : {W : RawWitness // ShapedWitness (d:=d) W} :=
  packCode (MaltsevWitness.fullCode defaultValue n)

theorem fp_fullShaped (defaultValue : Fin d) : FP BitEncoding.unaryNat (shapedWitnessCode d) (fullShaped defaultValue) := by
  apply (fp_fullCode defaultValue).transportOutput
  intro n
  change witnessCode.encode (fullCode defaultValue n) = witnessCode.encode (encodeCode (MaltsevWitness.fullCode defaultValue n))
  rw [fullCode_encode]

def initialWitness (defaultValue : Fin d) (g : ComplexityCSPCode.Code) : PositiveData d :=
  preparePositiveWitness defaultValue (fullShaped defaultValue g.vertices)

def constructPositive (defaultValue : Fin d) (g : ComplexityCSPCode.Code) : PositiveData d :=
  g.constraints.foldl (supportStep L m) (initialWitness defaultValue g)

def rawSupportCompiler (defaultValue : Fin d) (g : ComplexityCSPCode.Code) : RawWitness :=
  if g.vertices=0 then fullCode defaultValue 0 else (constructPositive L m defaultValue g).val

theorem fp_initialWitness (defaultValue : Fin d) : FP ComplexityCSPCode.encoding (positiveWitnessCode d) (initialWitness defaultValue) := by
  have hv : FP ComplexityCSPCode.encoding
      (BitEncoding.unaryNat.prod ComplexityCSPCode.constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hn := hv.comp (fp_fst BitEncoding.unaryNat ComplexityCSPCode.constraintEncoding.list)
  exact (hn.comp (fp_fullShaped defaultValue)).comp (fp_preparePositiveWitness defaultValue)

theorem fp_constructPositive (defaultValue : Fin d) : FP ComplexityCSPCode.encoding
    (positiveWitnessCode d) (constructPositive L m defaultValue) := by
  have hv : FP ComplexityCSPCode.encoding
      (BitEncoding.unaryNat.prod ComplexityCSPCode.constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hc := hv.comp (fp_snd BitEncoding.unaryNat ComplexityCSPCode.constraintEncoding.list)
  exact ((fp_initialWitness defaultValue).pair hc).comp (fp_supportFold L m)

/-- Genuine FP on all raw CSP Code values. The only constants are the fixed
language, operation and a domain color. Invalid rows are explicit unit-default
support steps. The zero-variable branch's eagerly computed alternative is a
concrete safe one-variable construction, never an unprepared restricted call. -/
theorem fp_rawSupportCompiler (defaultValue : Fin d) : FP ComplexityCSPCode.encoding witnessCode
    (rawSupportCompiler L m defaultValue) := by
  have hv : FP ComplexityCSPCode.encoding
      (BitEncoding.unaryNat.prod ComplexityCSPCode.constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hn := (hv.comp (fp_fst BitEncoding.unaryNat ComplexityCSPCode.constraintEncoding.list)).comp
    UnaryNatConversionMachine.fp_conversion
  have hz := (hn.pair (fp_const ComplexityCSPCode.encoding BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  have hout : FP ComplexityCSPCode.encoding witnessCode (fun g => (constructPositive L m defaultValue g).val) :=
    (fp_constructPositive L m defaultValue).transportOutput (fun _ => rfl)
  exact hz.ite (fp_const ComplexityCSPCode.encoding witnessCode (fullCode defaultValue 0)) hout

end ComplexCSP.ComplexitySupportWitnessPrimitives
