import Paper2.FixedFieldOutput.IndexedPost
import Paper2.FixedFieldOutput.Normalization

/-! Finite 0/1/2 occurrence dispatch around one real three-query controller.
Branch data consists of actual raw precompilers, valid-graph proofs and literal
value identities. It is not an accepted hardness or Bell-reduction assumption. -/
namespace Paper2.FixedFieldOutput.ResidualCompiler
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines BellMachines
open GraphPreprocessing UniversalPairReduction.ThreeQuery
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.RelativeEO
open BellPostprocessing
noncomputable section

abbrev Plan (L : Language) := Instance L × (Instance L × (Instance L × Flags))
abbrev RawPlan := RawClosedNetwork × (RawClosedNetwork × (RawClosedNetwork × Flags))
abbrev planEncoding (L : Language) := contextEncoding (inputEncoding L) flagsEncoding
abbrev rawPlanEncoding := contextEncoding RawClosedNetwork.encoding flagsEncoding

def toRaw {L : Language} (p : Plan L) : RawPlan := (p.1.val,p.2.1.val,p.2.2.1.val,p.2.2.2)

structure Branch (L : Language) (g : Signature AlgebraicComplex 2) (i : Fin 3) where
  raw : RawClosedNetwork → RawPlan
  computes : Computes RawClosedNetwork.encoding rawPlanEncoding raw
  plan : TaggedInstance L g (fun k => k = i.val) → Plan L
  raw_spec : ∀ G, raw G.val.val = toRaw (plan G)
  coeff : Fin 3 → (tagged L g).coefficientField
  correct : ∀ G, ((tagged L g).fieldPresentation.decode
    (BellPostprocessing.post L (tagged L g) coeff (answers (answer .nativeX L) (plan G))) :
      AlgebraicComplex) = value .nativeX (tagged L g) G.val

abbrev Input (L : Language) (g : Signature AlgebraicComplex 2) := ResidualInstance (tagged L g)
 def label (L : Language) (g : Signature AlgebraicComplex 2) (G : Input L g) : Fin 3 :=
  ⟨BellReduction.RawOccurrence.markedCount G.val.val.vertices,by have h := G.property; omega⟩

 def labelUnaryComputes (L : Language) (g : Signature AlgebraicComplex 2) :
    Computes (residualEncoding (tagged L g)) UnaryBinary.unaryEncoding (fun G => (label L g G).val) :=
  recode (RawTriple.markedComputes.andThen (Lists.lengthUnaryComputes RawClosedNetwork.vertexEncoding))
    (fun G => G.val.val) (fun _ => rfl) (fun _ => rfl)

 def labelComputes (L : Language) (g : Signature AlgebraicComplex 2) :
    Computes (residualEncoding (tagged L g)) IndexedPost.indexEncoding (label L g) :=
  recode (labelUnaryComputes L g) id (fun _ => rfl) (fun _ => rfl)

 def branchInput (L : Language) (g : Signature AlgebraicComplex 2) (G : Input L g) :
    TaggedInstance L g (fun k => k = (label L g G).val) := ⟨G.val,rfl⟩

 def selectedPlan (L : Language) (g : Signature AlgebraicComplex 2)
    (B : ∀ i : Fin 3, Branch L g i) (G : Input L g) : Plan L :=
  (B (label L g G)).plan (branchInput L g G)

 def selectedComputes (L : Language) (g : Signature AlgebraicComplex 2)
    (B : ∀ i : Fin 3, Branch L g i) :
    Computes (residualEncoding (tagged L g)) (planEncoding L) (selectedPlan L g B) := by
  let rawSelected := Lists.chooseComputes (residualEncoding (tagged L g)) rawPlanEncoding 3
    (label L g) (fun G i => (B i).raw G.val.val) (labelUnaryComputes L g)
    (fun i => recode (B i).computes (fun G => G.val.val) (fun _ => rfl) (fun _ => rfl))
  apply recode rawSelected id (fun _ => rfl)
  intro G
  change rawPlanEncoding.encode ((B (label L g G)).raw (branchInput L g G).val.val) = _
  rw [(B (label L g G)).raw_spec (branchInput L g G)]
  rfl

 def pre (L : Language) (g : Signature AlgebraicComplex 2)
    (B : ∀ i : Fin 3, Branch L g i) (G : Input L g) :
    Instance L × (Instance L × (Instance L × (Flags × Fin 3))) :=
  let p := selectedPlan L g B G
  (p.1,p.2.1,p.2.2.1,p.2.2.2,label L g G)

 def preComputes (L : Language) (g : Signature AlgebraicComplex 2)
    (B : ∀ i : Fin 3, Branch L g i) :
    Computes (residualEncoding (tagged L g))
      (contextEncoding (inputEncoding L) IndexedPost.context) (pre L g B) := by
  let plan := selectedComputes L g B
  let q0 := plan.andThen (Wiring.firstComputes (inputEncoding L)
    (pairEncoding (inputEncoding L) (pairEncoding (inputEncoding L) flagsEncoding)))
  let tail := plan.andThen (Wiring.secondComputes (inputEncoding L)
    (pairEncoding (inputEncoding L) (pairEncoding (inputEncoding L) flagsEncoding)))
  let q1 := tail.andThen (Wiring.firstComputes (inputEncoding L) (pairEncoding (inputEncoding L) flagsEncoding))
  let tail2 := tail.andThen (Wiring.secondComputes (inputEncoding L) (pairEncoding (inputEncoding L) flagsEncoding))
  let q2 := tail2.andThen (Wiring.firstComputes (inputEncoding L) flagsEncoding)
  let flags := tail2.andThen (Wiring.secondComputes (inputEncoding L) flagsEncoding)
  exact pairComputes q0 (pairComputes q1 (pairComputes q2 (pairComputes flags (labelComputes L g))))

 def reduction (L : Language) (g : Signature AlgebraicComplex 2)
    (B : ∀ i : Fin 3, Branch L g i) :
    LengthControlledOracleReduction (residualEncoding (tagged L g)) (answerEncoding (tagged L g))
      (inputEncoding L) (answerEncoding L) (residualAnswer (tagged L g)) (answer .nativeX L) := by
  apply controlledOfEq (preComputes L g B)
    (IndexedPost.computes L (tagged L g) (fun i => (B i).coeff)) (outputBound .nativeX L) _
  intro G
  symm
  apply answer_unique
  exact (B (label L g G)).correct (branchInput L g G)

end
end Paper2.FixedFieldOutput.ResidualCompiler
