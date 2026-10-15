import Paper2.DegreeCSP.BooleanObstruction
import Paper2.DegreeCSP.BinaryPlaneSource
import Paper2.DegreeCSP.PlaneFieldDecoder
import Paper2.DegreeCSP.LanguageLabels
import Paper2.DegreeCSP.QuarticLiftComputation
import Paper2.DegreeCSP.QuarticLiftInstanceRawValue
import Paper2.DegreeCSP.GeneratedMonotone
import Paper2.DegreeCSP.DisequalitySource
import Holant.NetworkAlgebra

/-! The literal non-BO binary witness has an executed counting source on its
opposite-pair lift. Its finite controls, oracle commands and query bounds pass
unchanged to the Paper 2 computation interface. -/
namespace Paper2.DegreeCSP.BooleanHardness
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.Complexity
open Paper2.Complexity.BinaryCompose Paper2.Complexity.FixedFieldMachines
open Paper2.TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def planeSource {A : Type} {ea : Encoding A Bool} {count : A→ℕ}
    (g : Signature AlgebraicComplex 2)
    (hbad : ¬OriginalBO.BlockOrthogonal (fun s t : Bool=>(g ![s,t] : ℂ)))
    (w : SharpPWitness ea count) :
    LengthControlledOracleReduction ea encodingNatBool
      BinaryPlaneSource.O.targetEncoding
      (BinaryPlaneSource.O.presentation (BinaryPlaneSource.lifted g)
        (BinaryPlaneSource.lifted_algebraic g)).encoding
      count (BinaryPlaneSource.O.targetValue (BinaryPlaneSource.lifted g)
        (BinaryPlaneSource.lifted_algebraic g)) :=
  Paper1Proved.controlledReduction
    (BinaryPlaneSource.source g hbad (Paper1Proved.sharpPWitness w))

theorem liftedGraph_coe (g : Signature AlgebraicComplex 2)
    (r : QuarticLiftLayout.Input) :
    (((r.val.realize r.property
      (fun _=>Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift g)
      (fun _=>Signature.disequality)).denote Fin.elim0 : AlgebraicComplex) : ℂ) =
      (r.val.realize r.property (fun _=>BinaryPlaneSource.lifted g)
        (fun _=>Signature.disequality)).denote Fin.elim0 := by
  let N := r.val.realize r.property
    (fun _=>Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift g)
    (fun _=>Signature.disequality)
  have h := Holant.Network.denote_map AlgebraicComplex.subtype N Fin.elim0
  have hmap : N.map AlgebraicComplex.subtype =
      r.val.realize r.property (fun _=>BinaryPlaneSource.lifted g)
        (fun _=>Signature.disequality) := by
    unfold Holant.Network.map N Holant.Complexity.RawClosedNetwork.realize
    congr 1
    funext e a b
    cases a <;> cases b <;> simp [Signature.disequality]
  rw [hmap] at h
  exact h.symm

theorem planeValue_coe (g : Signature AlgebraicComplex 2)
    (r : QuarticLiftLayout.Input) :
    (BinaryPlaneSource.O.targetValue (BinaryPlaneSource.lifted g)
      (BinaryPlaneSource.lifted_algebraic g) r : ℂ) =
    (((r.val.realize r.property
      (fun _=>Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift g)
      (fun _=>Signature.disequality)).denote Fin.elim0 : AlgebraicComplex) : ℂ) :=
  (BinaryPlaneSource.O.target_value_exact (BinaryPlaneSource.lifted g)
    (BinaryPlaneSource.lifted_algebraic g) r).trans (liftedGraph_coe g r).symm

variable (L : Language) (k : ℕ)
variable (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈L.family)

def xLabel : Fin L.count := LanguageLabels.ofMember L _ hX

theorem xLabel_literal :
    (⟨L.arity (xLabel L hX).val,L.signature (xLabel L hX)⟩ : AnySignature AlgebraicComplex)=
      ⟨2,kernelSignature Signature.disequality⟩ := LanguageLabels.ofMember_literal L _ hX

variable (P : Presentation AlgebraicComplex (Fin 2))
variable (hUses : P.Uses L.family) (hDiv : P.DegreeDivisible k)

def liftInput : QuarticLiftLayout.Input→FixedField.Input L k :=
  QuarticLiftInstance.rawInput P (LanguageLabels.naturals L P hUses) k (xLabel L hX).val
    (LanguageLabels.naturals_lt L P hUses) (LanguageLabels.naturals_arity L P hUses)
    (xLabel L hX).isLt (congrArg Sigma.fst (xLabel_literal L hX)) hDiv

/-- The checked raw emitter is restricted to its proved degree promise with
identical output bytes. No compiler is passed as a premise. -/
def liftComputes : Computes BinaryPlaneSource.O.targetEncoding (FixedField.inputEncoding L k)
    (liftInput L k hX P hUses hDiv) :=
  recode (QuarticLiftComputation.computes P (LanguageLabels.naturals L P hUses)
    k (xLabel L hX).val) id (fun _=>rfl) (fun _=>rfl)

theorem liftValue {g : Signature AlgebraicComplex 2} (hPg : P.value=g) (hk : 0<k)
    (r : QuarticLiftLayout.Input) :
    (BinaryPlaneSource.O.targetValue (BinaryPlaneSource.lifted g)
      (BinaryPlaneSource.lifted_algebraic g) r : ℂ)=
      ((Raw.value L.signature (liftInput L k hX P hUses hDiv r) : AlgebraicComplex) : ℂ) := by
  have h := QuarticLiftInstance.rawValue P (LanguageLabels.naturals L P hUses)
    k (xLabel L hX).val (LanguageLabels.naturals_lt L P hUses)
    (LanguageLabels.naturals_arity L P hUses) (xLabel L hX).isLt
    (congrArg Sigma.fst (xLabel_literal L hX)) hDiv L.signature
    (LanguageLabels.ofUses_literal L P hUses) (xLabel_literal L hX) r hPg hk
  exact (planeValue_coe g r).trans (congrArg (fun z : AlgebraicComplex=>(z : ℂ)) h).symm

/-- The generated binary plane oracle is compiled into the original native
oracle with executed input and fixed-basis answer conversion programs. -/
def planeReduction (hk : 3≤k)
    (heq : (⟨k,equality k⟩ : AnySignature AlgebraicComplex)∈L.family)
    (g : Signature AlgebraicComplex 2) (hPg : P.value=g) :
    LengthControlledOracleReduction BinaryPlaneSource.O.targetEncoding
      (BinaryPlaneSource.O.presentation (BinaryPlaneSource.lifted g)
        (BinaryPlaneSource.lifted_algebraic g)).encoding
      (Problem.inputEncoding L) (FixedFieldOutput.answerEncoding L)
      (BinaryPlaneSource.O.targetValue (BinaryPlaneSource.lifted g)
        (BinaryPlaneSource.lifted_algebraic g)) (FixedFieldOutput.answer .nativeX L) :=
  PlaneFieldDecoder.reduction (BinaryPlaneSource.lifted g) (BinaryPlaneSource.lifted_algebraic g)
    L k hk (LanguageLabels.ofMember L _ heq) (LanguageLabels.ofMember_literal L _ heq)
    (liftInput L k hX P hUses hDiv) (liftComputes L k hX P hUses hDiv)
    (liftValue L k hX P hUses hDiv hPg (by omega))

include hX in
/-- A failed BO condition on the actual degree-generated family yields
canonical native hardness, without an external degree-CSP source assumption. -/
theorem hard_of_not_allBO (hk : 3≤k)
    (heq : (⟨k,equality k⟩ : AnySignature AlgebraicComplex)∈L.family)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈L.family)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈L.family)
    (hbad : ¬OriginalBO.AllGeneratedOriginalBO L.family k) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨g,hg,hbadg⟩ := BooleanObstruction.exists_bad_binary_generated (by omega) h0 h1 hX hbad
  obtain ⟨P,hUses,hDiv,hPg⟩ := hg
  intro count hcount
  obtain ⟨w⟩ := hcount
  exact ⟨(planeSource g hbadg w).controlledCompose
    (planeReduction L k hX P hUses hDiv hk heq g hPg)⟩

include hX in
theorem hard_of_not_allBO_withX (hk : 3≤k)
    (heq : (⟨k,equality k⟩ : AnySignature AlgebraicComplex)∈L.family)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈L.family)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈L.family)
    (hbad : ¬OriginalBO.AllGeneratedOriginalBO L.family k) :
    FixedFieldOutput.SharpPHard .nativeX L :=
  hard_of_not_allBO L k hX hk heq h0 h1 hbad

/-- Eq_k supplies the literal X gadget, and the actual controlled back
compiler removes that extra dictionary entry from the final target. -/
theorem hard_of_not_allBO_withoutX (L : Language) (k : ℕ) (hk : 3≤k)
    (heq : (⟨k,equality k⟩ : AnySignature AlgebraicComplex)∈L.family)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈L.family)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈L.family)
    (hbad : ¬OriginalBO.AllGeneratedOriginalBO L.family k) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  let M := DisequalitySource.language L k hk heq
  have hsub : L.family⊆M.family := by
    rw [DisequalitySource.family]
    exact Set.subset_insert _ _
  have hx : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈M.family := by
    rw [DisequalitySource.family]
    exact Set.mem_insert _ _
  have hb : ¬OriginalBO.AllGeneratedOriginalBO M.family k :=
    fun h=>hbad (h.mono hsub)
  have hm := hard_of_not_allBO M k hx hk (hsub heq) (hsub h0) (hsub h1) hb
  intro f hf
  obtain ⟨r⟩ := hm f hf
  exact ⟨r.controlledCompose (DisequalitySource.back L k hk heq)⟩

end
end Paper2.DegreeCSP.BooleanHardness
