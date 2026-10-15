import Paper2.Paper1ProvedOracleAdapters
import Paper2.Paper1ProvedTensorSplit
import Holant.Proofs.Reductions.FactorSaturation.PrefixMachine
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget

/-! Controlled extraction of a prescribed finite factor catalogue. Each macro
is the actual no-identity power exposure graph. Its scalar and every literal
coefficient are included in one finite field before any instance is read. -/
namespace Paper2.Paper1Proved.FactorProvider
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity Paper2.FixedFieldOutput
open Paper2.TractableAlgorithms.Paper1Machine
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FactorSaturation
open Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant.Complexity.UniversalPairReduction.Surgery
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Catalogue
variable {s N : ℕ} {A : ℕ → ℕ}
variable (T : (i : ℕ) → Holant.Signature AlgebraicComplex (A i))
variable (P : (j : Fin N) → GeneralPowerExposure.PowerMacro
  (PrefixMachine.family (s:=s) T 0) (T (s+j.val)))

abbrev Index := (Σ i : Fin (s+N), Fin (A i.val) → Bool) ⊕ Fin N

def coefficient : Index (s:=s) (N:=N) (A:=A) → AlgebraicComplex
  | .inl ⟨i,x⟩ => T i.val x
  | .inr j => (P j).scale

theorem algebraic (i : Index (s:=s) (N:=N) (A:=A)) :
    IsAlgebraic ℚ (coefficient T P i) := Algebra.IsAlgebraic.isAlgebraic _

abbrev field := Holant.Algebraic.familyField (coefficient T P)
abbrev presentation := Holant.Algebraic.familyPresentation (coefficient T P) (algebraic T P)

def table (i : ℕ) (x : Fin (A i) → Bool) : field T P :=
  if hi : i < s+N then
    Holant.Algebraic.fieldCoefficient (coefficient T P) (.inl ⟨⟨i,hi⟩,x⟩) else 0

theorem table_exact (i : ℕ) (hi : i < s+N) (x : Fin (A i) → Bool) :
    (table T P i x : AlgebraicComplex) = T i x := by
  simp only [table, dite_eq_left hi]
  rfl

theorem base_exact (i : Fin s) (x : Fin (A i.val) → Bool) :
    (PrefixMachine.family (s:=s) (table T P) 0 i x : AlgebraicComplex) =
      PrefixMachine.family (s:=s) T 0 i x :=
  table_exact T P i.val (by have := i.isLt; omega) x

def scale (j : Fin N) : field T P :=
  Holant.Algebraic.fieldCoefficient (coefficient T P) (.inr j)

theorem scale_nonzero (j : Fin N) : scale T P j ≠ 0 := by
  intro h
  exact (P j).scale_ne_zero (congrArg (fun x : field T P => (x : AlgebraicComplex)) h)

def «macro» (j : Fin N) : GeneralPowerExposure.PowerMacro
    (PrefixMachine.family (s:=s) (table T P) 0) (table T P (s+j.val)) where
  exponent := (P j).exponent
  positive := (P j).positive
  scale := scale T P j
  scale_ne_zero := scale_nonzero T P j
  network := (P j).labels.sourceNetwork (PrefixMachine.family (s:=s) (table T P) 0)
    (fun _ => Holant.Signature.disequality)
  labels := (P j).labels
  value := by
    let Q := P j
    let V := Q.labels.template.network Q.labels.wellFormed
      (PrefixMachine.family (s:=s) (table T P) 0)
      (fun _ : Fin 1 => Holant.Signature.disequality)
    have he : V.map (field T P).subtype = Q.labels.template.network Q.labels.wellFormed
        (PrefixMachine.family (s:=s) T 0) (fun _ => Holant.Signature.disequality) := by
      unfold V Holant.Network.map Holant.Complexity.FixedGadgetSubstitution.Template.network
      congr 1
      · funext v x
        exact base_exact T P _ _
      · funext e a b
        cases a <;> cases b <;> rfl
    funext x
    apply Subtype.ext
    change (field T P).subtype (V.denote x) = _
    rw [← Holant.Network.denote_map, he, Q.value]
    simp only [Carrier.blockPower]
    congr 1
    change _ = (field T P).subtype _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact (table_exact T P (s+j.val) (by have := j.isLt; omega) _).symm

def chain : RecursiveMachine.Chain (PrefixMachine.family (s:=s) (table T P) 0)
    (PrefixMachine.family (s:=s) (table T P) N) :=
  PrefixMachine.chain (table T P) («macro» T P) N le_rfl

def value (n : ℕ)
    (r : Holant.Complexity.ExactSignatureTables.Input (s+n) 1 A) : field T P :=
  (GeneralFieldReduction.targetTables (presentation T P)
    (PrefixMachine.family (s:=s) (table T P) n)).evaluate (presentation T P) r

theorem value_exact (n : ℕ) (hn : n ≤ N)
    (r : Holant.Complexity.ExactSignatureTables.Input (s+n) 1 A) :
    (value T P n r : AlgebraicComplex) =
      (r.val.realize r.property (PrefixMachine.family (s:=s) T n)
        (fun _ => Holant.Signature.disequality)).denote Fin.elim0 := by
  unfold value
  rw [FieldReduction.target_evaluate]
  change (field T P).subtype _ = _
  rw [← Holant.Network.denote_map]
  congr 1
  unfold Holant.Network.map Holant.Complexity.RawClosedNetwork.realize
  congr 1
  · funext v x
    exact table_exact T P _ (by
      have hi : (r.val.vertices.get v).1 < s+n :=
        (r.val.signatureLabel r.property v).isLt
      omega) x
  · funext e a b
    cases a <;> cases b <;> rfl

end Catalogue

/-- The exact stored extraction chain is interpreted with controlled
composition at every step, including every intermediate query bound. -/
def interpret {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {A : ℕ → ℕ}
    (F : Holant.Algebraic.FixedField K d)
    {G : (i : Fin s) → Holant.Signature K (A i.val)}
    {Q B : Type} {eq : Encoding Q Bool} {eb : Encoding B Bool} {g : Q → B}
    (base : LengthControlledOracleReduction
      (Holant.Complexity.RawClosedNetwork.validatedEncoding s 1 A) F.encoding eq eb
      ((GeneralFieldReduction.targetTables F G).evaluate F) g)
    {n : ℕ} {H : (i : Fin n) → Holant.Signature K (A i.val)}
    (C : RecursiveMachine.Chain G H) :
    LengthControlledOracleReduction
      (Holant.Complexity.RawClosedNetwork.validatedEncoding n 1 A) F.encoding eq eb
      ((GeneralFieldReduction.targetTables F H).evaluate F) g :=
  match C with
  | .nil => base
  | .snoc previous f power =>
      (controlledReduction (RecursiveMachine.step F f power)).controlledCompose
        (interpret F base previous)

theorem relabelDenote {m n : ℕ} {A B : ℕ → ℕ}
    (F : (i : Fin m) → Holant.Signature AlgebraicComplex (A i.val))
    (H : (i : Fin n) → Holant.Signature AlgebraicComplex (B i.val))
    (σ : Fin m → Fin n)
    (hl : ∀ i, (⟨B (σ i).val,H (σ i)⟩ : AnySignature AlgebraicComplex) = ⟨A i.val,F i⟩)
    (r : Holant.Complexity.ExactSignatureTables.Input m 1 A) :
    (r.val.realize r.property F (fun _ => Holant.Signature.disequality)).denote Fin.elim0 =
      ((CanonicalFamily.Relabel.input σ (fun i => congrArg Sigma.fst (hl i)) r).val.realize
        (CanonicalFamily.Relabel.input σ (fun i => congrArg Sigma.fst (hl i)) r).property H
        (fun _ => Holant.Signature.disequality)).denote Fin.elim0 := by
  have ht : ∀ i : Fin m, ∀ bits,
      Choice.table F i.val bits = (1 : AlgebraicComplex) * Choice.table H (σ i).val bits := by
    intro i bits
    have he := congrArg (fun f : AnySignature AlgebraicComplex =>
      f.2 (fun j => bits.getD j.val false)) (hl i)
    simpa [Choice.table,i.isLt,(σ i).isLt] using he.symm
  have hones : RootPreprocessing.OccurrenceProduct.value
      (fun _ : Fin m => (1 : AlgebraicComplex)) r.val = 1 := by
    unfold RootPreprocessing.OccurrenceProduct.value
    have hm : r.val.vertices.map (fun row => RootPreprocessing.OccurrenceProduct.total
        (fun _ : Fin m => (1 : AlgebraicComplex)) row.1) =
        r.val.vertices.map (fun _ => (1 : AlgebraicComplex)) := by
      apply List.map_congr_left
      intro row hr
      have hi := ((RawGrouping.wellFormed_iff_members _ _ _ _).mp r.property).1 row hr
      simp [RootPreprocessing.OccurrenceProduct.total,hi.1]
    rw [hm]
    simp
  have hv := CanonicalFamily.Relabel.value_scaled σ (Choice.table F) (Choice.table H)
    (fun _ => (1 : AlgebraicComplex)) (fun i => congrArg Sigma.fst (hl i)) r ht
  rw [hones,one_mul] at hv
  rw [Choice.denote_eq_evaluate,Choice.denote_eq_evaluate]
  exact hv

def sourceLabel {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : L.family ⊆ Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex))) : Fin L.count → Fin n :=
  fun i => Classical.choose (h ⟨i,rfl⟩)

theorem sourceLiteral {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : L.family ⊆ Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex))) (i : Fin L.count) :
    (⟨A (sourceLabel G L h i).val,G (sourceLabel G L h i)⟩ : AnySignature AlgebraicComplex) =
      ⟨L.arity i.val,L.signature i⟩ := Classical.choose_spec (h ⟨i,rfl⟩)

def sourceInput {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : L.family ⊆ Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex))) :
    Instance L → Holant.Complexity.ExactSignatureTables.Input n 1 A :=
  fun r => CanonicalFamily.Relabel.input (sourceLabel G L h)
    (fun i => congrArg Sigma.fst (sourceLiteral G L h i)) (input L r)

def sourceComputes {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : L.family ⊆ Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex))) :
    Paper2.Complexity.BinaryCompose.Computes (inputEncoding L)
      (Holant.Complexity.RawClosedNetwork.validatedEncoding n 1 A) (sourceInput G L h) :=
  Paper2.Complexity.FixedFieldMachines.recode (computes (CanonicalFamily.Relabel.computes
    (sourceLabel G L h) (fun i => congrArg Sigma.fst (sourceLiteral G L h i))))
    (input L) (input_bytes L) (fun _ => rfl)

theorem sourceDenote {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : L.family ⊆ Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex))) (r : Instance L) :
    ((sourceInput G L h r).val.realize (sourceInput G L h r).property G
      (fun _ => Holant.Signature.disequality)).denote Fin.elim0 = Problem.value .nativeX L r := by
  have hv := relabelDenote (signatures L) G (sourceLabel G L h)
    (sourceLiteral G L h) (input L r)
  exact hv.symm

def targetLabel {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex)) ⊆ L.family) : Fin n → Fin L.count :=
  fun i => Classical.choose (h ⟨i,rfl⟩)

theorem targetLiteral {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex)) ⊆ L.family) (i : Fin n) :
    (⟨L.arity (targetLabel G L h i).val,L.signature (targetLabel G L h i)⟩ :
      AnySignature AlgebraicComplex) = ⟨A i.val,G i⟩ := Classical.choose_spec (h ⟨i,rfl⟩)

def targetInput {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex)) ⊆ L.family) :
    Holant.Complexity.ExactSignatureTables.Input n 1 A → Instance L :=
  fun r => (inputIso L).symm (CanonicalFamily.Relabel.input (targetLabel G L h)
    (fun i => congrArg Sigma.fst (targetLiteral G L h i)) r)

def targetComputes {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex)) ⊆ L.family) :
    Paper2.Complexity.BinaryCompose.Computes
      (Holant.Complexity.RawClosedNetwork.validatedEncoding n 1 A)
      (inputEncoding L) (targetInput G L h) :=
  Paper2.Complexity.FixedFieldMachines.recode (computes (CanonicalFamily.Relabel.computes
    (targetLabel G L h) (fun i => congrArg Sigma.fst (targetLiteral G L h i))))
    id (fun _ => rfl) (fun _ => input_bytes_back L _)

theorem targetDenote {n : ℕ} {A : ℕ → ℕ}
    (G : (i : Fin n) → Holant.Signature AlgebraicComplex (A i.val))
    (L : Language) (h : Set.range (fun i =>
      (⟨A i.val,G i⟩ : AnySignature AlgebraicComplex)) ⊆ L.family)
    (r : Holant.Complexity.ExactSignatureTables.Input n 1 A) :
    (r.val.realize r.property G (fun _ => Holant.Signature.disequality)).denote Fin.elim0 =
      Problem.value .nativeX L (targetInput G L h r) := by
  have hv := relabelDenote G (signatures L) (targetLabel G L h) (targetLiteral G L h) r
  exact hv

/-- The retained factor catalogue is reduced by the actual stored macro chain,
using the literal finite label scanners at both canonical endpoints. -/
theorem catalogueReduction {s N : ℕ} {A : ℕ → ℕ}
    (T : (i : ℕ) → Holant.Signature AlgebraicComplex (A i))
    (P : (j : Fin N) → GeneralPowerExposure.PowerMacro
      (PrefixMachine.family (s:=s) T 0) (T (s+j.val)))
    (L M : Language)
    (hL : Set.range (fun i : Fin s =>
      (⟨A i.val,T i.val⟩ : AnySignature AlgebraicComplex)) ⊆ L.family)
    (hM : M.family ⊆ Set.range (fun i : Fin (s+N) =>
      (⟨A i.val,T i.val⟩ : AnySignature AlgebraicComplex))) :
    FixedFieldOutput.Reduces .nativeX M L := by
  let F := Catalogue.presentation T P
  let embed := (Catalogue.field T P).val.toLinearMap
  let baseG := PrefixMachine.family (s:=s) T 0
  let smallG := PrefixMachine.family (s:=s) (Catalogue.table T P) 0
  let f := (GeneralFieldReduction.targetTables F smallG).evaluate F
  let q := targetInput baseG L hL
  let pre := targetComputes baseG L hL
  let prep := Paper2.Complexity.FixedFieldMachines.pairComputes pre
    (Paper2.Complexity.FixedFieldMachines.pairComputes pre
      (Paper2.Complexity.FixedFieldMachines.pairComputes pre
        (Paper2.Complexity.FixedFieldMachines.constantComputes
          (Holant.Complexity.RawClosedNetwork.validatedEncoding s 1 A)
          encodingBoolBool false)))
  let first := Paper2.Complexity.FixedFieldMachines.Wiring.firstComputes
    (answerEncoding L) (Paper2.Complexity.FixedFieldMachines.pairEncoding
      (answerEncoding L) (Paper2.Complexity.FixedFieldMachines.pairEncoding
        (answerEncoding L) encodingBoolBool))
  let post := first.andThen (fieldConversionBack L F embed)
  have hc : ∀ r, embed (f r) = Problem.value .nativeX L (q r) := by
    intro r
    exact (Catalogue.value_exact T P 0 (by omega) r).trans (targetDenote baseG L hL r)
  let base : LengthControlledOracleReduction
      (Holant.Complexity.RawClosedNetwork.validatedEncoding s 1 A) F.encoding
      (inputEncoding L) (answerEncoding L) f (answer .nativeX L) :=
    UniversalPairReduction.ThreeQuery.controlledOfEq prep post
      (FixedFieldOutput.outputBound .nativeX L) f
      (fun r => (fieldConversionBack_correct L F embed Subtype.val_injective
        .nativeX (q r) (f r) (hc r)).symm)
  let all := interpret F base (Catalogue.chain T P)
  let topG := PrefixMachine.family (s:=s) T N
  let smallTop := PrefixMachine.family (s:=s) (Catalogue.table T P) N
  let fs := (GeneralFieldReduction.targetTables F smallTop).evaluate F
  let qs := sourceInput topG M hM
  have hcs : ∀ r, embed (fs (qs r)) = Problem.value .nativeX M r := by
    intro r
    exact (Catalogue.value_exact T P N le_rfl (qs r)).trans (sourceDenote topG M hM r)
  exact ⟨(sourceFieldAdapter .nativeX M
    (Holant.Complexity.RawClosedNetwork.validatedEncoding (s+N) 1 A)
    F embed fs qs (sourceComputes topG M hM) all.sourceOutputBound hcs).controlledCompose all⟩

namespace FiniteAugmentation
variable (B : Language) {J : Type} [Fintype J] (added : J → AnySignature AlgebraicComplex)

abbrev count := Fintype.card J
def enumerate : Fin (count (J:=J)) ≃ J := (Fintype.equivFin J).symm

def lookup (i : ℕ) : AnySignature AlgebraicComplex :=
  if hi : i < B.count then ⟨B.arity i,B.signature ⟨i,hi⟩⟩ else
  if hj : i-B.count < count (J:=J) then added (enumerate ⟨i-B.count,hj⟩) else ⟨0,0⟩

def arity (i : ℕ) : ℕ := (lookup B added i).1
def table (i : ℕ) : Holant.Signature AlgebraicComplex (arity B added i) := (lookup B added i).2
abbrev base := PrefixMachine.family (s:=B.count) (table B added) 0

@[simp] theorem lookup_old (i : Fin B.count) :
    lookup B added i.val = ⟨B.arity i.val,B.signature i⟩ := by
  simp only [lookup,dite_eq_left i.isLt]

@[simp] theorem lookup_new (j : Fin (count (J:=J))) :
    lookup B added (B.count+j.val) = added (enumerate j) := by
  unfold lookup
  rw [dite_eq_right (by omega),dite_eq_left (by omega)]
  apply congrArg added
  apply congrArg enumerate
  apply Fin.ext
  change B.count+j.val-B.count = j.val
  omega

theorem base_family : Set.range (fun i : Fin B.count =>
    (⟨arity B added i.val,base B added i⟩ : AnySignature AlgebraicComplex)) = B.family := by
  congr 1
  funext i
  exact lookup_old B added i

theorem full_family : Set.range (fun i : Fin (B.count+count (J:=J)) =>
    (⟨arity B added i.val,table B added i.val⟩ : AnySignature AlgebraicComplex)) =
      B.family ∪ Set.range added := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val < B.count
    · left
      exact ⟨⟨i.val,hi⟩,(lookup_old B added ⟨i.val,hi⟩).symm⟩
    · right
      let j : Fin (count (J:=J)) := ⟨i.val-B.count,by omega⟩
      refine ⟨enumerate j,?_⟩
      change added (enumerate j) = lookup B added i.val
      have he : i.val = B.count+j.val := by dsimp [j]; omega
      rw [he,lookup_new]
  · rintro (⟨i,rfl⟩ | ⟨j,rfl⟩)
    · exact ⟨⟨i.val,by have := i.isLt; omega⟩,lookup_old B added i⟩
    · let k := (enumerate (J:=J)).symm j
      refine ⟨⟨B.count+k.val,by have := k.isLt; omega⟩,?_⟩
      change lookup B added (B.count+k.val) = added j
      rw [lookup_new,Equiv.apply_symm_apply]

def powers
    (p : ∀ j : J, Nonempty (GeneralPowerExposure.PowerMacro (base B added) (added j).2))
    (j : Fin (count (J:=J))) : GeneralPowerExposure.PowerMacro
      (base B added) (table B added (B.count+j.val)) := by
  have h := Classical.choice (p (enumerate j))
  change GeneralPowerExposure.PowerMacro (base B added) (lookup B added (B.count+j.val)).2
  rw [lookup_new]
  exact h

theorem reduction
    (p : ∀ j : J, Nonempty (GeneralPowerExposure.PowerMacro (base B added) (added j).2))
    (M : Language) (hM : M.family ⊆ B.family ∪ Set.range added) :
    FixedFieldOutput.Reduces .nativeX M B := by
  apply catalogueReduction (table B added) (powers B added p) B M
  · exact Set.Subset.rfl.trans_eq (base_family B added)
  · exact hM.trans_eq (full_family B added).symm

end FiniteAugmentation

namespace PrescribedFactors
variable {L : Language} (D : PrimeFactorization L)

abbrev MultiIndex := {ij : D.Index // 1 < (D.decomposition ij.1).count}

def added (ij : MultiIndex D) : AnySignature AlgebraicComplex :=
  ⟨(D.decomposition ij.val.1).arity ij.val.2,(D.decomposition ij.val.1).factor ij.val.2⟩

def helper (ij : D.Index) : AnySignature AlgebraicComplex :=
  if 1 < (D.decomposition ij.1).count then
    ⟨(D.decomposition ij.1).arity ij.2 + TensorSplit.remainderArity (D.decomposition ij.1) ij.2,
      Signature.tensor ((D.decomposition ij.1).factor ij.2)
        (TensorSplit.remainder (D.decomposition ij.1) ij.2)⟩
  else ⟨(D.decomposition ij.1).arity ij.2,(D.decomposition ij.1).factor ij.2⟩

theorem helper_realized (ij : D.Index) :
    NativeNetworkRealizesUpTo L.family (helper D ij).2 := by
  have hr : (⟨L.arity ij.1.val,(D.decomposition ij.1).value⟩ :
      AnySignature AlgebraicComplex) ∈ L.family := by
    rw [D.exact_value]
    exact ⟨ij.1,rfl⟩
  by_cases hc : 1 < (D.decomposition ij.1).count
  · have he : helper D ij = (⟨(D.decomposition ij.1).arity ij.2 +
        TensorSplit.remainderArity (D.decomposition ij.1) ij.2,
        Signature.tensor ((D.decomposition ij.1).factor ij.2)
          (TensorSplit.remainder (D.decomposition ij.1) ij.2)⟩ : AnySignature AlgebraicComplex) := by
      simp only [helper,ite_eq_left hc]
    exact (congrArg (fun f : AnySignature AlgebraicComplex =>
      NativeNetworkRealizesUpTo L.family f.2) he).mpr
      (TensorSplit.reindex_realized L (D.decomposition ij.1) ij.2 hr)
  · have hone : (D.decomposition ij.1).count = 1 := by
      have := ij.2.isLt
      omega
    have he : helper D ij = (⟨(D.decomposition ij.1).arity ij.2,
        (D.decomposition ij.1).factor ij.2⟩ : AnySignature AlgebraicComplex) := by
      simp only [helper,ite_eq_right hc]
    exact (congrArg (fun f : AnySignature AlgebraicComplex =>
      NativeNetworkRealizesUpTo L.family f.2) he).mpr
      (TensorSplit.singleton_realized L (D.decomposition ij.1) ij.2 hone hr)

theorem powers (B : Language)
    (hB : B.family = L.family ∪ Set.range (helper D))
    (htwo : ¬ CommonOneSided L.family) :
    ∀ j : MultiIndex D, Nonempty (GeneralPowerExposure.PowerMacro
      (FiniteAugmentation.base B (added D)) (added D j).2) := by
  have hLB : L.family ⊆ B.family := by rw [hB]; exact Set.subset_union_left
  have ht : ¬ Holant.Tractable.CommonOneSided B.family := by
    intro hs
    apply htwo
    rcases hs with hs | hs
    · left; intro f hf x hx; exact hs f (hLB hf) x hx
    · right; intro f hf x hx; exact hs f (hLB hf) x hx
  have hm := GeneralPowerExposure.mixedSupport_of_source ht
  rw [← FiniteAugmentation.base_family B (added D)] at hm
  intro j
  let E := D.decomposition j.val.1
  let k := j.val.2
  have hg : TensorSplit.remainder E k ≠ 0 :=
    TensorSplit.remainder_nonzero E k (fun i => (D.prime j.val.1 i).1)
  have hn : 0 < TensorSplit.remainderArity E k :=
    TensorSplit.remainder_positive E k (by change 2 ≤ (D.decomposition j.val.1).count; have := j.property; omega) (D.positive j.val.1)
  have hf : (⟨E.arity k + TensorSplit.remainderArity E k,
      Signature.tensor (E.factor k) (TensorSplit.remainder E k)⟩ : AnySignature AlgebraicComplex) ∈
      Set.range (fun i => (⟨FiniteAugmentation.arity B (added D) i.val,
        FiniteAugmentation.base B (added D) i⟩ : AnySignature AlgebraicComplex)) := by
    have hb : (⟨E.arity k + TensorSplit.remainderArity E k,
        Signature.tensor (E.factor k) (TensorSplit.remainder E k)⟩ : AnySignature AlgebraicComplex) ∈ B.family := by
      rw [hB]
      right
      refine ⟨j.val,?_⟩
      simp only [helper,ite_eq_left j.property]
      rfl
    exact (FiniteAugmentation.base_family B (added D)).symm ▸ hb
  exact GeneralPowerExposure.labelled_power (FiniteAugmentation.base B (added D))
    (by norm_num) hm (E.factor k) (TensorSplit.remainder E k) hn hg hf

theorem source_subset (B : Language)
    (hB : B.family = L.family ∪ Set.range (helper D))
    (M : Language) (hM : M.family = L.family ∪ D.factors) :
    M.family ⊆ B.family ∪ Set.range (added D) := by
  rw [hM]
  rintro f (hf | ⟨ij,rfl⟩)
  · left; rw [hB]; exact Or.inl hf
  · by_cases hc : 1 < (D.decomposition ij.1).count
    · right; exact ⟨⟨ij,hc⟩,rfl⟩
    · left
      rw [hB]
      right
      refine ⟨ij,?_⟩
      simp only [helper,ite_eq_right hc]

theorem forward (htwo : ¬ CommonOneSided L.family)
    (M : Language) (hM : M.family = L.family ∪ D.factors) :
    FixedFieldOutput.Reduces .nativeX M L := by
  obtain ⟨B,hB⟩ := Language.coverage_family (L.family ∪ Set.range (helper D))
    (L.family_finite.union (Set.finite_range _))
  have hLB : L.family ⊆ B.family := by rw [hB]; exact Set.subset_union_left
  have hBL : FixedFieldOutput.Reduces .nativeX B L :=
    directGadgetProvider.directGadget_2_5 L B hLB (by
      rw [hB]
      rintro f (hf | ⟨ij,rfl⟩)
      · exact NativeNetworkRealizesUpTo.of_mem hf
      · exact helper_realized D ij)
  exact (FiniteAugmentation.reduction B (added D) (powers D B hB htwo)
    M (source_subset D B hB M hM)).trans hBL

end PrescribedFactors

end
end Paper2.Paper1Proved.FactorProvider

namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput
noncomputable section

theorem factorProvider : SourceFaithful.Paper1FactorClosureAccepted := by
  constructor
  intro L _ htwo D M hM
  refine ⟨FactorProvider.PrescribedFactors.forward D htwo M hM,?_⟩
  apply restriction L M
  rw [hM]
  exact Set.subset_union_left

end
end Paper2.Paper1Proved
