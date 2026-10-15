import Paper2.FixedFieldOutput.FieldInclusion
import Paper2.Complexity.BellMachines.BellPostprocessing
import Paper2.Complexity.BellMachines.GraphPreprocessing.FiniteRecode

/-! Canonical-coordinate Bell postprocessing with both closed-circle factors
retained for each of the three actual queries. Flags are physical caller context;
field lifts, factors 1/2/4, additions and fixed scalar division are true machines. -/
namespace Paper2.FixedFieldOutput.BellPostprocessing
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines BellMachines
open GraphPreprocessing UniversalPairReduction.ThreeQuery
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.Algebraic
noncomputable section

abbrev Flags := (Bool × Bool) × ((Bool × Bool) × (Bool × Bool))
abbrev pairBoolEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev flagsEncoding : Encoding Flags Bool := pairEncoding pairBoolEncoding
  (pairEncoding pairBoolEncoding pairBoolEncoding)
abbrev PostInput (base : Language) := Answer base × (Answer base × (Answer base × Flags))
abbrev postEncoding (base : Language) := contextEncoding (answerEncoding base) flagsEncoding

def flag (b : Bool) : ℕ := if b then 2 else 1
 def pairFactor {K : Type} [Field K] (p : Bool × Bool) : K := flag p.1 * flag p.2

def readValue (base : Language) (i : Fin 3) (p : PostInput base) : Answer base :=
  ![p.1,p.2.1,p.2.2.1] i
 def readFlag (i : Fin 3) (p : Flags) : Bool × Bool := ![p.1,p.2.1,p.2.2] i

 def readValueComputes (base : Language) (i : Fin 3) :
    Computes (postEncoding base) (answerEncoding base) (readValue base i) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun z => Fin.elim0 z) k) j) i
  · exact Wiring.firstComputes _ _
  · exact (Wiring.secondComputes _ _).andThen (Wiring.firstComputes _ _)
  · exact ((Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _)).andThen
      (Wiring.firstComputes _ _)

 def allFlagsComputes (base : Language) : Computes (postEncoding base) flagsEncoding
    (fun p => p.2.2.2) :=
  ((Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _)).andThen
    (Wiring.secondComputes _ _)

 def readFlagComputes (i : Fin 3) : Computes flagsEncoding pairBoolEncoding (readFlag i) := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun z => Fin.elim0 z) k) j) i
  · exact Wiring.firstComputes _ _
  · exact (Wiring.secondComputes _ _).andThen (Wiring.firstComputes _ _)
  · exact (Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _)

 def flagComputes {K : Type} [Field K] [Algebra ℚ K] {n : ℕ} (F : FixedField K n) :
    Computes encodingBoolBool F.encoding (fun b => (flag b : K)) :=
  FiniteRecode.computes encodingBoolBool F.encoding (fun b => (flag b : K)) 1
    (fun b => by cases b <;> decide)

 def pairFactorComputes {K : Type} [Field K] [Algebra ℚ K] {n : ℕ} (F : FixedField K n) :
    Computes pairBoolEncoding F.encoding (pairFactor (K := K)) :=
  (pairComputes ((Wiring.firstComputes _ _).andThen (flagComputes F))
    ((Wiring.secondComputes _ _).andThen (flagComputes F))).andThen (fieldMultiplication F)

 def term (base work : Language) (coeff : Fin 3 → work.coefficientField) (i : Fin 3)
    (p : PostInput base) : work.coefficientField :=
  (toField base work (readValue base i p) * pairFactor (readFlag i p.2.2.2)) * coeff i

 def termComputes (base work : Language) (coeff : Fin 3 → work.coefficientField) (i : Fin 3) :
    Computes (postEncoding base) work.fieldPresentation.encoding (term base work coeff i) := by
  let value := (readValueComputes base i).andThen (toFieldComputes base work)
  let factor := ((allFlagsComputes base).andThen (readFlagComputes i)).andThen
    (pairFactorComputes work.fieldPresentation)
  exact scaleComputes work.fieldPresentation
    ((pairComputes value factor).andThen (fieldMultiplication work.fieldPresentation)) (coeff i)

 def post (base work : Language) (coeff : Fin 3 → work.coefficientField)
    (p : PostInput base) : Answer work :=
  work.fieldPresentation.basis.equivFun
    (term base work coeff 0 p + term base work coeff 1 p + term base work coeff 2 p)

 def computes (base work : Language) (coeff : Fin 3 → work.coefficientField) :
    Computes (postEncoding base) (answerEncoding work) (post base work coeff) :=
  (addComputes work.fieldPresentation
    (addComputes work.fieldPresentation (termComputes base work coeff 0) (termComputes base work coeff 1))
    (termComputes base work coeff 2)).andThen (fromFieldComputes work)

/-- Query modes are in literal order 12|34,13|24,14|23. -/
 def twoYCoefficients (work : Language) : Fin 3 → work.coefficientField := ![0,-1,1]
 def twoICoefficients (work : Language) : Fin 3 → work.coefficientField := ![-(2⁻¹),2⁻¹,2⁻¹]
 def oneYCoefficients (work : Language) (κ : work.coefficientField) : Fin 3 → work.coefficientField :=
  ![0,κ⁻¹,-κ⁻¹]

 theorem post_correct (base work : Language) (hsub : base.family ⊆ work.family)
    (coeff : Fin 3 → work.coefficientField) (q : Fin 3 → Instance base) (flags : Flags) :
    (work.fieldPresentation.decode
      (post base work coeff (answer .nativeX base (q 0),answer .nativeX base (q 1),
        answer .nativeX base (q 2),flags)) : AlgebraicComplex) =
    (value .nativeX base (q 0) * (pairFactor (readFlag 0 flags) : AlgebraicComplex)) * coeff 0 +
    (value .nativeX base (q 1) * (pairFactor (readFlag 1 flags) : AlgebraicComplex)) * coeff 1 +
    (value .nativeX base (q 2) * (pairFactor (readFlag 2 flags) : AlgebraicComplex)) * coeff 2 := by
  unfold post
  rw [show work.fieldPresentation.decode (work.fieldPresentation.basis.equivFun _) = _ from
    work.fieldPresentation.basis.equivFun.symm_apply_apply _]
  change work.coefficientField.val (_+_+_) = _
  simp only [map_add,term,map_mul,readValue,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.head_fin_const]
  change (((toField base work (answer .nativeX base (q 0)) : AlgebraicComplex) * _) * _) +
    (((toField base work (answer .nativeX base (q 1)) : AlgebraicComplex) * _) * _) +
    (((toField base work (answer .nativeX base (q 2)) : AlgebraicComplex) * _) * _) = _
  simp only [toField_answer_coe _ _ _ hsub]
  simp [pairFactor]

end
end Paper2.FixedFieldOutput.BellPostprocessing
