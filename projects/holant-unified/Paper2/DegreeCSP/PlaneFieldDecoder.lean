import Paper2.DegreeCSP.FixedFieldReduction
import Paper2.TractableAlgorithms.Paper1Machine
import Holant.Proofs.Reductions.EightVertexNonexception.Source

/-! The literal plane source keeps its original complex coefficient field.
Finiteness proves every element algebraic, and an actual fixed rational basis
converter returns the canonical native answer to that original field encoding. -/
namespace Paper2.DegreeCSP.PlaneFieldDecoder
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity Paper2.Complexity.BinaryCompose
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Every element of an actual finite rational subfield of C has its literal
algebraicity certificate. Its complex value is unchanged by this embedding. -/
def algebraicEmbedding (E : IntermediateField ℚ ℂ) [FiniteDimensional ℚ E] :
    E →ₐ[ℚ] AlgebraicComplex where
  toFun x := ⟨(x : ℂ),(Algebra.IsAlgebraic.isAlgebraic x).isIntegral.map E.val⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

@[simp] theorem algebraicEmbedding_coe (E : IntermediateField ℚ ℂ) [FiniteDimensional ℚ E]
    (x : E) : (algebraicEmbedding E x : ℂ)=(x : ℂ) := rfl

namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field coefficient coefficient_algebraic presentation TargetInput targetEncoding targetValue)
end O

variable (M : Holant.Signature ℂ 4) (halg : ∀ x,IsAlgebraic ℚ (M x))

def embedding : O.field M →ₐ[ℚ] AlgebraicComplex := by
  let _ : FiniteDimensional ℚ (O.field M) :=
    Holant.Algebraic.familyField_finiteDimensional (O.coefficient M) (O.coefficient_algebraic M halg)
  exact algebraicEmbedding (O.field M)

@[simp] theorem embedding_coe (x : O.field M) : (embedding M halg x : ℂ)=(x : ℂ) := rfl

theorem embedding_injective : Function.Injective (embedding M halg) := (embedding M halg).injective

variable (L : Language)

/-- The original plane answer encoding is returned by an executed rational
matrix converter fixed before any instance is read. -/
def decoder : Computes (FixedFieldOutput.answerEncoding L) (O.presentation M halg).encoding
    (fun v => (O.presentation M halg).decode
      (TractableAlgorithms.Paper1Machine.reverseCoordinates L (O.presentation M halg)
        (embedding M halg).toLinearMap v)) :=
  TractableAlgorithms.Paper1Machine.fieldConversionBack L (O.presentation M halg)
    (embedding M halg).toLinearMap

variable (k : ℕ) (hk : 3 ≤ k) (jK : Fin L.count)
variable (hK : (⟨L.arity jK.val,L.signature jK⟩ : AnySignature AlgebraicComplex)=⟨k,equality k⟩)
variable (q : O.TargetInput → FixedField.Input L k)
variable (pre : Computes O.targetEncoding (FixedField.inputEncoding L k) q)
variable (hv : ∀ G : O.TargetInput,
  (O.targetValue M halg G : ℂ)=((Raw.value L.signature (q G) : AlgebraicComplex) : ℂ))

include hv in
theorem query_value (G : O.TargetInput) :
    embedding M halg (O.targetValue M halg G) =
      Problem.value .nativeX L (FixedField.query L k hk jK hK (q G)) := by
  apply Subtype.ext
  change (O.targetValue M halg G : ℂ)=
    (Problem.value .nativeX L (FixedField.query L k hk jK hK (q G)) : ℂ)
  rw [FixedField.query_value]
  exact hv G

/-- The exact old plane oracle is reduced to the canonical native oracle.
The input compiler, field decoder, valid queries and query lengths all have
actual finite programs; the mathematical identity is the proved lift value. -/
def reduction : LengthControlledOracleReduction O.targetEncoding (O.presentation M halg).encoding
    (Problem.inputEncoding L) (FixedFieldOutput.answerEncoding L)
    (O.targetValue M halg) (FixedFieldOutput.answer .nativeX L) :=
  oneQueryOfEq (pre.andThen (FixedField.queryComputes L k hk jK hK))
    (decoder M halg L) (FixedFieldOutput.outputBound .nativeX L) (O.targetValue M halg)
    (fun G => (TractableAlgorithms.Paper1Machine.fieldConversionBack_correct
      L (O.presentation M halg) (embedding M halg).toLinearMap (embedding_injective M halg)
      .nativeX (FixedField.query L k hk jK hK (q G)) (O.targetValue M halg G)
      (query_value M halg L k hk jK hK q hv G)).symm)

end
end Paper2.DegreeCSP.PlaneFieldDecoder
