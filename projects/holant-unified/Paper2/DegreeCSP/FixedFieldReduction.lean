import Paper2.DegreeCSP.ComputationValidated
import Paper2.DegreeCSP.QueryCorrect
import Paper2.FixedFieldOutput.Problem
import Paper2.Complexity.ControlledCompose
import Paper2.Paper1ProvedComplexity
import Holant.Proofs.Algorithms.ControlledReduction

/-! The degree-CSP source has the original language's canonical field answers.
Its reduction executes the certified incidence compiler and one actual oracle
call. The imported controller proves validity and size for every actual query. -/
namespace Paper2.DegreeCSP
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity Paper2.Complexity.BinaryCompose
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private def originalMachine (m : Machine) : Holant.Complexity.BinaryCompose.Machine where
  K := m.K
  decidableK := m.decidableK
  finiteK := m.finiteK
  input := m.input
  output := m.output
  Label := m.Label
  finiteLabel := m.finiteLabel
  main := m.main
  State := m.State
  finiteState := m.finiteState
  initial := m.initial
  program := m.program

private def originalComputes {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (m : Computes ea eb f) : Holant.Complexity.BinaryCompose.Computes ea eb f where
  machine := originalMachine m.machine
  time := m.time
  outputs := m.outputs

private def originalBound {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (size : PolynomialOutputBound ea eb f) :
    Holant.Complexity.PolynomialOutputBound ea eb f where
  bound := size.bound
  length_le := size.length_le

/-- Literal interface translation of the already proved one-query controller.
The finite instructions, timed runs and actual-query certificate are retained. -/
def oneQueryOfEq {A B X Y : Type}
    {ea : Encoding A Bool} {eb : Encoding B Bool}
    {ex : Encoding X Bool} {ey : Encoding Y Bool}
    {pre : A → X} {post : Y → B} {g : X → Y}
    (a : Computes ea ex pre) (b : Computes ey eb post)
    (size : PolynomialOutputBound ex ey g) (f : A → B)
    (heq : ∀ x, f x=post (g (pre x))) : LengthControlledOracleReduction ea eb ex ey f g :=
  Paper1Proved.controlledReduction
    (Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
      (originalComputes a) (originalComputes b) (originalBound size) f heq)

namespace FixedField
open scoped BigOperators

abbrev Input (L : Language) (k : ℕ) := Raw.Input L.count L.arity k
abbrev inputEncoding (L : Language) (k : ℕ) := Raw.validatedEncoding L.count L.arity k

/-- The literal degree-CSP sum lies in the language's own fixed field. -/
def sourceValue (L : Language) (k : ℕ) (r : Input L k) : L.coefficientField :=
  Raw.value L.fieldSignature r

def sourceAnswer (L : Language) (k : ℕ) (r : Input L k) : FixedFieldOutput.Answer L :=
  L.fieldPresentation.decode.symm (sourceValue L k r)

theorem sourceValue_coe (L : Language) (k : ℕ) (r : Input L k) :
    (sourceValue L k r : AlgebraicComplex) = Raw.value L.signature r := by
  change L.coefficientField.subtype (Raw.value L.fieldSignature r) = _
  simp only [Raw.value,Raw.factorWeight,map_sum,map_prod]
  rfl

theorem sourceAnswer_correct (L : Language) (k : ℕ) (r : Input L k) :
    (L.fieldPresentation.decode (sourceAnswer L k r) : AlgebraicComplex) = Raw.value L.signature r := by
  rw [sourceAnswer,LinearEquiv.apply_symm_apply]
  exact sourceValue_coe L k r

variable (L : Language) (k : ℕ) (hk : 3 ≤ k) (jK : Fin L.count)
variable (hK : (⟨L.arity jK.val,L.signature jK⟩ : AnySignature AlgebraicComplex) = ⟨k,equality k⟩)

def query (r : Input L k) : Problem.Instance L :=
  QueryGraph.query L.signature hk r jK (congrArg Sigma.fst hK)

def queryComputes : Computes (inputEncoding L k) (Problem.inputEncoding L) (query L k hk jK hK) :=
  QueryGraph.queryComputes L.signature hk jK (congrArg Sigma.fst hK)

theorem query_value (r : Input L k) :
    Problem.value .nativeX L (query L k hk jK hK r) = Raw.value L.signature r :=
  QueryGraph.query_partition L.signature hk r jK hK

theorem answer_query (r : Input L k) :
    sourceAnswer L k r = FixedFieldOutput.answer .nativeX L (query L k hk jK hK r) := by
  apply FixedFieldOutput.answer_unique
  exact (sourceAnswer_correct L k r).trans (query_value L k hk jK hK r).symm

/-- The one-call reduction retains the actual incidence program and its
polynomial query bound. Its answer decoder is the identity word machine. -/
def reduction : LengthControlledOracleReduction
    (inputEncoding L k) (FixedFieldOutput.answerEncoding L)
    (Problem.inputEncoding L) (FixedFieldOutput.answerEncoding L)
    (sourceAnswer L k) (FixedFieldOutput.answer .nativeX L) :=
  oneQueryOfEq (queryComputes L k hk jK hK)
    (identityComputes (FixedFieldOutput.answerEncoding L))
    (FixedFieldOutput.outputBound .nativeX L) (sourceAnswer L k)
    (answer_query L k hk jK hK)

/-- The source answer convention itself has a proved polynomial byte bound. -/
def sourceOutputBound : PolynomialOutputBound (inputEncoding L k)
    (FixedFieldOutput.answerEncoding L) (sourceAnswer L k) where
  bound := (FixedFieldOutput.outputBound .nativeX L).bound.comp
    (queryComputes L k hk jK hK).outputBound.bound
  length_le r := by
    rw [answer_query L k hk jK hK r]
    exact le_trans ((FixedFieldOutput.outputBound .nativeX L).length_le _)
      (by simpa only [Polynomial.eval_comp] using (natPolynomial_eval_mono
        (FixedFieldOutput.outputBound .nativeX L).bound
        ((queryComputes L k hk jK hK).outputBound.length_le r)))

/-- This defines the exact degree-CSP hardness source; it is not asserted. -/
def SharpPHard (L : Language) (k : ℕ) : Prop :=
  ∀ f : List Bool → ℕ, InSharpP (encodingList Bool) f →
    Nonempty (LengthControlledOracleReduction (encodingList Bool) encodingNatBool
      (inputEncoding L k) (FixedFieldOutput.answerEncoding L) f (sourceAnswer L k))

include hk jK hK in
theorem hardness_transport (hard : SharpPHard L k) : FixedFieldOutput.SharpPHard .nativeX L := by
  intro f hf
  obtain ⟨r⟩ := hard f hf
  exact ⟨r.controlledCompose (reduction L k hk jK hK)⟩

end FixedField
end
end Paper2.DegreeCSP
