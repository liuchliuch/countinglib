import Paper2.ExactInput.FiniteLanguage
import Holant.Proofs.AlgebraicRecognition.ComplexIsolation.CertificateMachine.Codec
import Holant.Proofs.Algorithms.TransformRecognition.RationalTableMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalFamilyPackingMachine
import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.RightFold

/-! Concrete syntax conversion for the proved varying-layout Paper 1 recognizer.
The rectangle wire is regrouped by a fixed finite program. Dense table entries
are selected using the actual least-significant-port index, so the two truth
table orders are not identified by assumption. No validity test is used. -/
namespace Paper2.Paper1ProvedRecognition
open Computability Paper2.ExactInput
open Holant.Complexity Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.Complexity.GraphPreprocessing
open Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
noncomputable section

def root (c : Paper2.ExactInput.RootCode) : Holant.LocalDrafts.EffectiveAlgebraic.RootCode :=
  ⟨c.coefficients,⟨c.rectangle.reLower,c.rectangle.reUpper,
    c.rectangle.imLower,c.rectangle.imUpper⟩⟩

@[simp] theorem polynomial_eq (c : Paper2.ExactInput.RootCode) :
    (root c).polynomial = c.polynomial := by
  change Holant.LocalDrafts.EffectiveAlgebraic.RationalPolynomialCode.polynomial c.coefficients =
    Paper2.ExactInput.RationalPolynomialCode.polynomial c.coefficients
  induction c.coefficients with
  | nil => rfl
  | cons t ts ih =>
    cases t
    simp only [Holant.LocalDrafts.EffectiveAlgebraic.RationalPolynomialCode.polynomial,
      Paper2.ExactInput.RationalPolynomialCode.polynomial,ih]

theorem represents (c : Paper2.ExactInput.RootCode) (z : ℂ) :
    (root c).Represents z ↔ c.Represents z := by
  change (_ ≠ 0 ∧ _ ∧ Polynomial.aeval z _ = 0 ∧ _) ↔
    (_ ≠ 0 ∧ _ ∧ Polynomial.aeval z _ = 0 ∧ _)
  rw [polynomial_eq]
  rfl

private theorem frame_eq (bs : List Bool) :
    Holant.Algebraic.frame bs = Paper2.Algebraic.frame bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [Holant.Algebraic.frame,Paper2.Algebraic.frame,ih]

private theorem polynomial_bytes (p : Paper2.ExactInput.RationalPolynomialCode) :
    CertificateMachine.polynomialEncoding.encode p = polynomialEncoding.encode p := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    change Holant.Complexity.framedListEncode CertificateMachine.termEncoding ts =
      Paper2.Complexity.framedListEncode
        (Paper2.Complexity.framedProductEncoding encodingNatBool Paper2.Algebraic.rationalEncoding) ts at ih
    change true :: (Holant.Algebraic.frame
      (Holant.Algebraic.frame (encodingNatBool.encode t.1) ++
        Holant.Algebraic.rationalEncoding.encode t.2) ++ _) =
      true :: (Paper2.Algebraic.frame
      (Paper2.Algebraic.frame (encodingNatBool.encode t.1) ++
        Paper2.Algebraic.rationalEncoding.encode t.2) ++ _)
    rw [frame_eq,frame_eq,ih]
    rfl

abbrev Four := ℚ × (ℚ × (ℚ × ℚ))
abbrev fourEncoding := pairEncoding Holant.Algebraic.rationalEncoding
  (pairEncoding Holant.Algebraic.rationalEncoding
    (pairEncoding Holant.Algebraic.rationalEncoding Holant.Algebraic.rationalEncoding))
abbrev wireEncoding := pairEncoding CertificateMachine.polynomialEncoding fourEncoding
abbrev Wire := Paper2.ExactInput.RationalPolynomialCode × Four
def wire (c : Paper2.ExactInput.RootCode) : Wire :=
  (c.coefficients,c.rectangle.reLower,c.rectangle.reUpper,
    c.rectangle.imLower,c.rectangle.imUpper)

theorem wire_bytes (c : Paper2.ExactInput.RootCode) :
    wireEncoding.encode (wire c) = rootEncoding.encode c := by
  change Holant.Algebraic.frame (CertificateMachine.polynomialEncoding.encode c.coefficients) ++
    (Holant.Algebraic.frame (Holant.Algebraic.rationalEncoding.encode c.rectangle.reLower) ++
    (Holant.Algebraic.frame (Holant.Algebraic.rationalEncoding.encode c.rectangle.reUpper) ++
    (Holant.Algebraic.frame (Holant.Algebraic.rationalEncoding.encode c.rectangle.imLower) ++
    Holant.Algebraic.rationalEncoding.encode c.rectangle.imUpper))) = _
  simp only [polynomial_bytes,frame_eq]
  rfl

def regroup : Computes fourEncoding CertificateMachine.rectangleWireEncoding
    (fun p : Four => ((p.1,p.2.1),(p.2.2.1,p.2.2.2))) := by
  let q := Holant.Algebraic.rationalEncoding
  let a := Wiring.firstComputes q (pairEncoding q (pairEncoding q q))
  let tail := Wiring.secondComputes q (pairEncoding q (pairEncoding q q))
  let b := tail.andThen (Wiring.firstComputes q (pairEncoding q q))
  let rest := tail.andThen (Wiring.secondComputes q (pairEncoding q q))
  exact pairComputes (pairComputes a b) rest

def rootComputes : Computes rootEncoding CertificateMachine.rootEncoding root := by
  let p := Wiring.firstComputes CertificateMachine.polynomialEncoding fourEncoding
  let r := (Wiring.secondComputes CertificateMachine.polynomialEncoding fourEncoding).andThen regroup
  exact recode (pairComputes p r) wire wire_bytes (fun _ => rfl)

/-- Literal binary value of a port list, with its head at the least significant bit. -/
def wordValue (xs : List Bool) : ℕ := xs.foldr (fun b n => (if b then 1 else 0)+2*n) 0

theorem wordValue_ofFn {n : ℕ} (x : Fin n → Bool) :
    wordValue (List.ofFn x) = (wordIndex n x).val := by
  change _ = ∑ i : Fin n, (finTwoEquiv.symm (x i)).val * 2^i.val
  induction n with
  | zero => simp [wordValue]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [wordValue,List.foldr_cons]
    rw [Fin.sum_univ_succ]
    change (if x 0 then 1 else 0)+2*wordValue (List.ofFn (Fin.tail x)) = _
    rw [ih]
    simp only [Fin.val_zero,Fin.val_succ,pow_zero,mul_one,pow_succ']
    have hb : (finTwoEquiv.symm (x 0)).val = (if x 0 then 1 else 0) := by
      cases x 0 <;> rfl
    rw [hb]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.tail]
    ring

def wordCell : Computes
    (pairEncoding Holant.Complexity.GraphPreprocessing.Frame.wordEncoding
      (pairEncoding encodingBoolBool encodingNatBool)) encodingNatBool
    (fun p => (if p.2.1 then 1 else 0)+2*p.2.2) := by
  let tail := Wiring.secondComputes Frame.wordEncoding (pairEncoding encodingBoolBool encodingNatBool)
  let bit := tail.andThen (Wiring.firstComputes encodingBoolBool encodingNatBool)
  let acc := tail.andThen (Wiring.secondComputes encodingBoolBool encodingNatBool)
  let value := ifComputes bit (constantComputes _ encodingNatBool 1)
    (constantComputes _ encodingNatBool 0)
  let twice := (pairComputes acc acc).andThen RationalInputMachine.Programs.add
  exact congrComputes ((pairComputes value twice).andThen RationalInputMachine.Programs.add)
    (fun p => by simp only [Function.comp_apply]; omega)

def wordValueExecutes : Executes RationalTableMachine.wordEncoding encodingNatBool wordValue := by
  let prepare := Executes.ofComputes
    (pairComputes (constantComputes RationalTableMachine.wordEncoding Frame.wordEncoding [])
      (pairComputes (identityComputes RationalTableMachine.wordEncoding)
        (constantComputes RationalTableMachine.wordEncoding encodingNatBool 0)))
  exact (prepare.comp (PositiveCertificateMachine.RightFold.executes
    Frame.wordEncoding encodingBoolBool encodingNatBool
    (fun _ b n => (if b then 1 else 0)+2*n) false (Executes.ofComputes wordCell))).congr
      (fun _ => rfl)

private theorem list_bytes {A : Type} (e : Encoding A Bool) (xs : List A) :
    (Holant.Complexity.framedListEncoding e).encode xs =
      (Paper2.Complexity.framedListEncoding e).encode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Holant.Complexity.framedListEncode e xs = Paper2.Complexity.framedListEncode e xs at ih
    change true :: (Holant.Algebraic.frame (e.encode x) ++ _) =
      true :: (Paper2.Algebraic.frame (e.encode x) ++ _)
    rw [frame_eq,ih]

def rootsComputes : Computes (Paper2.Complexity.framedListEncoding rootEncoding)
    CommonFieldMachine.rootsEncoding (List.map root) :=
  recode (WireLists.mapComputes rootEncoding CertificateMachine.rootEncoding root rootComputes)
    id (list_bytes rootEncoding) (fun _ => rfl)

def base (c : SignatureCode) : OriginalFamilyPackingMachine.Vertex :=
  (c.arity,c.entries.map root)

private theorem signature_bytes (c : SignatureCode) :
    (pairEncoding encodingNatBool (Paper2.Complexity.framedListEncoding rootEncoding)).encode
      (c.arity,c.entries) = SignatureCode.encoding.encode c := by
  change Holant.Algebraic.frame (encodingNatBool.encode c.arity) ++ _ =
    Paper2.Algebraic.frame (encodingNatBool.encode c.arity) ++ _
  rw [frame_eq]

def baseComputes : Computes SignatureCode.encoding OriginalFamilyPackingMachine.vertexEncoding base := by
  let entries := Paper2.Complexity.framedListEncoding rootEncoding
  let arity := Wiring.firstComputes encodingNatBool entries
  let roots := (Wiring.secondComputes encodingNatBool entries).andThen rootsComputes
  exact recode (pairComputes arity roots) (fun c => (c.arity,c.entries))
    signature_bytes (fun _ => rfl)

def arityComputes : Computes SignatureCode.encoding encodingNatBool SignatureCode.arity :=
  baseComputes.andThen (Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding)

def vertex (c : SignatureCode) : OriginalFamilyPackingMachine.Vertex :=
  (c.arity,(RationalTableMachine.words c.arity).map
    (fun w => (base c).2.getD (wordValue w) (RationalRootCode.code 0)))

def vertexCell : Executes (pairEncoding SignatureCode.encoding RationalTableMachine.wordEncoding)
    CertificateMachine.rootEncoding
    (fun p : SignatureCode × List Bool =>
      (base p.1).2.getD (wordValue p.2) (RationalRootCode.code 0)) := by
  let c := Wiring.firstComputes SignatureCode.encoding RationalTableMachine.wordEncoding
  let w := Wiring.secondComputes SignatureCode.encoding RationalTableMachine.wordEncoding
  let entries := (c.andThen baseComputes).andThen
    (Wiring.secondComputes encodingNatBool CommonFieldMachine.rootsEncoding)
  let index := (Executes.ofComputes w).comp wordValueExecutes
  exact ((Executes.ofComputes entries).pair index).comp
    (NegativeCertificateMachine.Lists.lookup CertificateMachine.rootEncoding (RationalRootCode.code 0))

def vertexExecutes : Executes SignatureCode.encoding OriginalFamilyPackingMachine.vertexEncoding vertex := by
  let words := (Executes.ofComputes arityComputes).comp RationalTableMachine.wordsExecutes
  let rows := NegativeCertificateMachine.Lists.map SignatureCode.encoding RationalTableMachine.wordEncoding
    CertificateMachine.rootEncoding words
    (fun c w => (base c).2.getD (wordValue w) (RationalRootCode.code 0)) vertexCell
  exact (Executes.ofComputes arityComputes).pair rows

def packed (raw : RawLanguage) : OriginalFamilyPackingMachine.Input :=
  (raw.map vertex,false)

def packedExecutes : Executes rawLanguageEncoding OriginalFamilyPackingMachine.encoding packed := by
  let prepare := Executes.ofComputes
    (pairComputes (constantComputes (Holant.Complexity.framedListEncoding SignatureCode.encoding)
      Frame.wordEncoding []) (identityComputes (Holant.Complexity.framedListEncoding SignatureCode.encoding)))
  let cell := (Executes.ofComputes
    (Wiring.secondComputes Frame.wordEncoding SignatureCode.encoding)).comp vertexExecutes
  let rows := prepare.comp (Executes.mapList Frame.wordEncoding SignatureCode.encoding
    OriginalFamilyPackingMachine.vertexEncoding (fun _ c => vertex c) cell)
  let converted := Executes.recode rows id (list_bytes SignatureCode.encoding) (fun _ => rfl)
  exact converted.pair (Executes.ofComputes (constantComputes rawLanguageEncoding encodingBoolBool false))

end
end Paper2.Paper1ProvedRecognition
