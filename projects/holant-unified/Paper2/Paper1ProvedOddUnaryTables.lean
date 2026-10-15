import Paper2.Paper1ProvedOracleAdapters
import Paper2.Paper1ProvedOddUnaryEquality
import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion

/-! Fixed finite field tables retain their actual labels in a literal exact
language. The validated input adapter copies the graph bytes and proves the
ordinary field evaluation equal to the canonical problem value. -/
namespace Paper2.Paper1Proved.OddUnary.Tables
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation Paper2.Problem
open Holant.Algebraic
open Holant.LocalDrafts.MainChain
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {s : ℕ} (a : ℕ → ℕ)
variable (H : (i : Fin s) → Signature AlgebraicComplex (a i.val))

def language : Language := by
  refine ⟨List.ofFn (fun i : Fin s => codeOf (H i)),?_⟩
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  exact codeOf_valid _

@[simp] theorem count : (language a H).count = s := by
  simp [language,Language.count]

@[simp] theorem code (i : Fin s) :
    (language a H).code (Fin.cast (count a H).symm i) = codeOf (H i) := by
  simp only [Language.code,language,List.get_eq_getElem,List.getElem_ofFn]
  rfl

theorem any (i : Fin s) :
    (⟨(language a H).arity i.val,
      (language a H).signature (Fin.cast (count a H).symm i)⟩ : AnySignature AlgebraicComplex) =
        ⟨a i.val,H i⟩ := by
  have ha : (language a H).arity i.val = a i.val := by
    have hh := (language a H).arity_index (Fin.cast (count a H).symm i)
    exact hh.trans (congrArg SignatureCode.arity (code a H i))
  apply Sigma.ext ha
  exact (language_signature_heq _ _).trans
    ((denote_code_heq (code a H i) _ _).trans (heq_of_eq (codeOf_denote _)))

theorem arity (i : Fin s) : (language a H).arity i.val = a i.val :=
  congrArg Sigma.fst (any a H i)

theorem family : (language a H).family = Set.range (fun i : Fin s =>
    (⟨a i.val,H i⟩ : AnySignature AlgebraicComplex)) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    let j : Fin s := Fin.cast (count a H) i
    refine ⟨j,?_⟩
    have hj : Fin.cast (count a H).symm j = i := Fin.ext rfl
    exact (any a H j).symm.trans (congrArg (fun k : Fin (language a H).count =>
      (⟨(language a H).arity k.val,(language a H).signature k⟩ : AnySignature AlgebraicComplex)) hj)
  · rintro ⟨i,rfl⟩
    exact ⟨Fin.cast (count a H).symm i,any a H i⟩

def input (G : Instance (language a H)) :
    {r : Holant.Complexity.RawClosedNetwork // r.WellFormed s 1 a} := by
  let R := Paper2.Paper1Proved.input (language a H) G
  refine ⟨R.val,?_⟩
  refine ⟨?_,R.property.2⟩
  intro v
  have hv := R.property.1 v
  have bound : (R.val.vertices.get v).1 < s := by simpa only [count] using hv.1
  exact ⟨bound,hv.2.trans (arity a H ⟨_,bound⟩)⟩

theorem input_bytes (G : Instance (language a H)) :
    (Holant.Complexity.RawClosedNetwork.validatedEncoding s 1 a).encode (input a H G) =
      (Paper2.Problem.inputEncoding (language a H)).encode G :=
  Paper2.Paper1Proved.input_bytes (language a H) G

def inputComputes : Paper2.Complexity.BinaryCompose.Computes
    (Paper2.Problem.inputEncoding (language a H))
    (Holant.Complexity.RawClosedNetwork.validatedEncoding s 1 a) (input a H) :=
  Paper2.Complexity.FixedFieldMachines.recode
    (Paper2.Complexity.BinaryCompose.identityComputes (Paper2.Problem.inputEncoding (language a H)))
    id (fun _ => rfl) (fun G => (input_bytes a H G).symm)

section Field
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable {degree : ℕ} (F : FixedField K degree)
variable (J : (i : Fin s) → Holant.Signature K (a i.val))

def mapped (i : Fin s) : Signature AlgebraicComplex (a i.val) := fun x => J i x

abbrev fieldLanguage := language a (mapped a K J)
abbrev fieldInput := input a (mapped a K J)
abbrev fieldValue := (QuaternaryOrdinaryCompanion.tables F J).evaluate F

theorem graph_value (G : Instance (fieldLanguage a K J)) :
    ((fieldInput a K J G).val.realize (fieldInput a K J G).property
      (mapped a K J) (fun _ => Holant.Signature.equality)).denote Fin.elim0 =
      Paper2.Problem.value .ordinary (fieldLanguage a K J) G := by
  have hn := network_value .ordinary (fieldLanguage a K J) G
  rw [show Paper2.Paper1Proved.kernels .ordinary =
    (fun _ : Fin 1 => Holant.Signature.equality) from rfl] at hn
  apply Eq.trans ?_ hn
  simp only [Holant.Network.denote,Holant.Complexity.RawClosedNetwork.realize]
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    let R := fieldInput a K J G
    let S := Paper2.Paper1Proved.input (fieldLanguage a K J) G
    let i : Fin s := R.val.signatureLabel R.property v
    let k : Fin (fieldLanguage a K J).count := S.val.signatureLabel S.property v
    have hk : Fin.cast (count a (mapped a K J)).symm i = k := Fin.ext rfl
    have hl : (⟨(fieldLanguage a K J).arity k.val,(fieldLanguage a K J).signature k⟩ :
        AnySignature AlgebraicComplex) = ⟨a i.val,mapped a K J i⟩ :=
      (congrArg (fun k : Fin (fieldLanguage a K J).count =>
        (⟨(fieldLanguage a K J).arity k.val,(fieldLanguage a K J).signature k⟩ :
          AnySignature AlgebraicComplex)) hk).symm.trans (any a (mapped a K J) i)
    have ha := congrArg Sigma.fst hl
    have he := Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      ((fieldLanguage a K J).signature k) (mapped a K J i) hl ha
      (fun j => z (R.val.route R.property ⟨v,j⟩))
    change mapped a K J i (fun j => z (R.val.route R.property ⟨v,j⟩)) = _
    rw [← he]
    congr 1
  · rfl

theorem field_value_correct (G : Instance (fieldLanguage a K J)) :
    (fieldValue a K F J (fieldInput a K J G) : AlgebraicComplex) =
      Paper2.Problem.value .ordinary (fieldLanguage a K J) G := by
  rw [fieldValue,Holant.Complexity.ExactSignatureTables.evaluate_eq_decoded]
  change K.subtype _ = _
  rw [← Holant.Network.denote_map K.subtype]
  have hm : (((fieldInput a K J G).val.realize (fieldInput a K J G).property
      (fun i x => F.decode ((QuaternaryOrdinaryCompanion.tables F J).vertex i x))
      (fun i u v => F.decode ((QuaternaryOrdinaryCompanion.tables F J).edge i u v))).map K.subtype) =
      (fieldInput a K J G).val.realize (fieldInput a K J G).property
        (mapped a K J) (fun _ => Holant.Signature.equality) := by
    unfold Holant.Network.map Holant.Complexity.RawClosedNetwork.realize
    congr 1
    · funext v x
      simp [QuaternaryOrdinaryCompanion.tables,mapped]
      rfl
    · funext e u v
      cases u <;> cases v <;> simp [QuaternaryOrdinaryCompanion.tables,Holant.Signature.equality]
  rw [hm]
  exact graph_value a K J G

end Field
end
end Paper2.Paper1Proved.OddUnary.Tables
