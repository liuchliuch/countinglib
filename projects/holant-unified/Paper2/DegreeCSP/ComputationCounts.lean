import Paper2.DegreeCSP.ComputationRecords
import Paper2.DegreeCSP.ComputationDivide
import Paper2.DegreeCSP.ComputationRawLayout

/-! Literal occurrence and macro counts. Every unbounded sum is an actual
indexed scan of the declared variables. Fixed multiplication is finite program
composition, and division is the checked k-phase physical-token machine. -/
namespace Paper2.DegreeCSP.ComputationRecords.Counts
open Holant Holant.Algebraic Holant.Complexity Computability
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.Complexity.GraphPreprocessing Holant.Complexity.GraphPreprocessing.OriginalCoefficient
open Holant.Complexity.FixedGadgetSubstitution Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program
open ComputationLayout
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

def unaryScaleComputes (k : ℕ) :
    Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun n=>n*k) := by
  induction k with
  | zero => exact congrComputes (constantComputes _ _ 0) (by intro n; simp)
  | succ k ih =>
    exact congrComputes (Arithmetic.unaryAdd ih (identityComputes UnaryBinary.unaryEncoding))
      (by intro n; simp [Nat.mul_succ])

def binaryScale {A : Type} {ea : Encoding A Bool} {f : A → ℕ}
    (u : Computes ea encodingNatBool f) (k : ℕ) :
    Computes ea encodingNatBool (fun a=>f a*k) := by
  induction k with
  | zero => exact congrComputes (constantComputes _ _ 0) (by intro a; simp)
  | succ k ih => exact congrComputes (Arithmetic.add ih u) (by intro a; simp [Nat.mul_succ])

def internalCountComputes (k : ℕ) (hk : 0<k) :
    Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (internalCount k) := by
  let zero := Arithmetic.equal UnaryBinary.computes (constantComputes _ encodingNatBool 0)
  let positive := ((ComputationDivide.computes k hk).andThen
    UniversalPairReduction.SmoothingCompiler.Endpoints.unaryPredecessorComputes).andThen
      (unaryScaleComputes k)
  exact congrComputes (Arithmetic.choose UnaryBinary.unaryEncoding _ _ _ zero
    (constantComputes _ _ k) positive)
    (by intro d; simp only [Function.comp_def,id_eq,internalCount,ComputationLayout.multiplicity,decide_eq_true_eq])

def variableMultiplicityComputes (k : ℕ) (hk : 0<k) :
    Computes Records.variableEncoding UnaryBinary.unaryEncoding
      (fun x=>ComputationLayout.multiplicity k (Raw.degree x.1 x.2.val)) :=
  variableDegreeComputes.andThen (ComputationDivide.computes k hk)

def variableInternalCountComputes (k : ℕ) (hk : 0<k) :
    Computes Records.variableEncoding UnaryBinary.unaryEncoding
      (fun x=>internalCount k (Raw.degree x.1 x.2.val)) :=
  variableDegreeComputes.andThen (internalCountComputes k hk)

def occurrenceCountComputes : Computes Raw.encoding UnaryBinary.unaryEncoding occurrenceCountRaw :=
  Indexed.sum Raw.encoding (fun r : Raw=>r.variables) Records.variablesComputes _ variableDegreeComputes

def internalTotalComputes (k : ℕ) (hk : 0<k) :
    Computes Raw.encoding UnaryBinary.unaryEncoding
      (fun r=>∑i : Fin r.variables,internalCount k (Raw.degree r i.val)) :=
  Indexed.sum Raw.encoding (fun r : Raw=>r.variables) Records.variablesComputes _ (variableInternalCountComputes k hk)

abbrev PrefixInput := Indexed.Input (fun x : Context=>x.1.variables)
abbrev prefixEncoding := Indexed.encoding encoding (fun x : Context=>x.1.variables)

def selectedVariableComputes : Computes prefixEncoding Records.variableEncoding
    (fun x=>(⟨x.1.1,x.2⟩ : Records.Variable)) :=
  recode (pairComputes ((Indexed.context encoding (fun x : Context=>x.1.variables)).andThen sourceComputes)
    (Indexed.index encoding (fun x : Context=>x.1.variables))) id (fun _=>rfl) (fun _=>rfl)

def outerOffsetComputes : Computes encoding UnaryBinary.unaryEncoding
    (fun x=>outerOffsetRaw x.1 x.2) := by
  let count := sourceComputes.andThen Records.variablesComputes
  let target := (Indexed.context encoding (fun x : Context=>x.1.variables)).andThen addressComputes
  let index := (Indexed.index encoding (fun x : Context=>x.1.variables)).andThen UnaryBinary.computes
  let chosen := Arithmetic.choose UnaryBinary.unaryEncoding _ _ _ (Arithmetic.less index target)
    (selectedVariableComputes.andThen variableDegreeComputes)
    (constantComputes prefixEncoding UnaryBinary.unaryEncoding 0)
  exact congrComputes (Indexed.sum encoding _ count _ chosen)
    (by intro x; simp only [Function.comp_def,id_eq,outerOffsetRaw,decide_eq_true_eq])

def internalPrefixComputes (k : ℕ) (hk : 0<k) : Computes encoding UnaryBinary.unaryEncoding
    (fun x=>∑i : Fin x.1.variables,if i.val<x.2 then internalCount k (Raw.degree x.1 i.val) else 0) := by
  let count := sourceComputes.andThen Records.variablesComputes
  let target := (Indexed.context encoding (fun x : Context=>x.1.variables)).andThen addressComputes
  let index := (Indexed.index encoding (fun x : Context=>x.1.variables)).andThen UnaryBinary.computes
  let chosen := Arithmetic.choose UnaryBinary.unaryEncoding _ _ _ (Arithmetic.less index target)
    (selectedVariableComputes.andThen (variableInternalCountComputes k hk))
    (constantComputes prefixEncoding UnaryBinary.unaryEncoding 0)
  exact congrComputes (Indexed.sum encoding _ count _ chosen)
    (by intro x; simp only [Function.comp_def,id_eq,decide_eq_true_eq])

def innerOffsetComputes (k : ℕ) (hk : 0<k) : Computes encoding UnaryBinary.unaryEncoding
    (fun x=>innerOffsetRaw k x.1 x.2) :=
  Arithmetic.unaryAdd (sourceComputes.andThen occurrenceCountComputes) (internalPrefixComputes k hk)

def edgeCountComputes (k : ℕ) (hk : 0<k) :
    Computes Raw.encoding UnaryBinary.unaryEncoding (edgeCountRaw k) :=
  Arithmetic.unaryAdd occurrenceCountComputes (internalTotalComputes k hk)

def variableOuterOffsetComputes : Computes Records.variableEncoding UnaryBinary.unaryEncoding
    (fun x=>outerOffsetRaw x.1 x.2.val) := variableContextComputes.andThen outerOffsetComputes

def variableInnerOffsetComputes (k : ℕ) (hk : 0<k) :
    Computes Records.variableEncoding UnaryBinary.unaryEncoding
      (fun x=>innerOffsetRaw k x.1 x.2.val) :=
  variableContextComputes.andThen (innerOffsetComputes k hk)

end
end Paper2.DegreeCSP.ComputationRecords.Counts
