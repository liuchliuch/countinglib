import Paper2.FixedFieldOutput.OccurrenceReductions
import Paper2.Synthesis.OrdinaryTransport

/-! Literal ordinary/native transport of designated-occurrence promises.
Label zero, every original label, ordered ports and graph bytes are unchanged.
Canonical field answers are converted by executed fixed rational matrices. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.SourceStatements.ReplicationTransport
noncomputable section
open Paper2 Tractable ExactInput ExactInput.Computation Problem RelativeEO Synthesis
open Computability Paper2.Complexity BinaryCompose
open FixedFieldMachines
open UniversalPairReduction.ThreeQuery

abbrev nativeTagged (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n) :=
  tagged (inverseKLanguage L) (sourceKBasis.symm.action g)

lemma tagged_count_eq (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n) :
    (tagged L g).count = (nativeTagged L g).count := by simp

lemma tagged_arity_eq (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n) :
    (tagged L g).arity = (nativeTagged L g).arity := by
  funext i
  cases i <;> simp [nativeTagged]

lemma tagged_vertex_any (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (i : Fin (tagged L g).count) :
    (⟨(nativeTagged L g).arity i.val,
      (nativeTagged L g).signature (Fin.cast (tagged_count_eq L g) i)⟩ :
      AnySignature AlgebraicComplex) =
    ⟨(tagged L g).arity i.val, sourceKBasis.symm.action ((tagged L g).signature i)⟩ := by
  let act : AnySignature AlgebraicComplex → AnySignature AlgebraicComplex :=
    fun f => ⟨f.1, sourceKBasis.symm.action f.2⟩
  change _ = act ⟨(tagged L g).arity i.val, (tagged L g).signature i⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · have hi : Fin.cast (tagged_count_eq L g) (0 : Fin (L.count + 1)) =
        (⟨0, by simp [nativeTagged]⟩ : Fin (nativeTagged L g).count) := Fin.ext rfl
    change (⟨(nativeTagged L g).arity (Fin.cast (tagged_count_eq L g) (0 : Fin (L.count + 1))).val,
      (nativeTagged L g).signature (Fin.cast (tagged_count_eq L g) (0 : Fin (L.count + 1)))⟩ :
      AnySignature AlgebraicComplex) = _
    rw [hi, tagged_zero]
    exact (congrArg act (tagged_zero L g)).symm
  · let j' : Fin (inverseKLanguage L).count := Fin.cast (inverseKLanguage_count L).symm j
    have hi : Fin.cast (tagged_count_eq L g) j.succ = j'.succ := Fin.ext rfl
    change (⟨(nativeTagged L g).arity (Fin.cast (tagged_count_eq L g) j.succ).val,
      (nativeTagged L g).signature (Fin.cast (tagged_count_eq L g) j.succ)⟩ :
      AnySignature AlgebraicComplex) = _
    rw [hi, tagged_succ, tagged_succ]
    exact indexedLanguage_any L (fun _ f => sourceKBasis.symm.action f) j

lemma tagged_vertex_heq (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (i : Fin (tagged L g).count) :
    HEq ((nativeTagged L g).signature (Fin.cast (tagged_count_eq L g) i))
      (sourceKBasis.symm.action ((tagged L g).signature i)) :=
  (Sigma.mk.inj_iff.mp (tagged_vertex_any L g i)).2

/-- Every decidable occurrence promise is transported on precisely the same
raw graph, so the designated occurrence count is literally unchanged. -/
def taggedInstanceEquiv (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (p : ℕ → Prop) : TaggedInstance L g p ≃
      TaggedInstance (inverseKLanguage L) (sourceKBasis.symm.action g) p where
  toFun G := ⟨reinterpret (tagged_count_eq L g) (tagged_arity_eq L g) G.val, G.property⟩
  invFun G := ⟨reinterpret (tagged_count_eq L g).symm (tagged_arity_eq L g).symm G.val,
    G.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)

@[simp] lemma taggedInstance_raw (L : Language) {n : ℕ}
    (g : Signature AlgebraicComplex n) (p : ℕ → Prop) (G : TaggedInstance L g p) :
    (taggedInstanceEquiv L g p G).val.val = G.val.val := rfl

@[simp] lemma taggedInstance_bytes (L : Language) {n : ℕ}
    (g : Signature AlgebraicComplex n) (p : ℕ → Prop) [DecidablePred p]
    (G : TaggedInstance L g p) :
    (taggedEncoding (inverseKLanguage L) (sourceKBasis.symm.action g) p).encode
      (taggedInstanceEquiv L g p G) = (taggedEncoding L g p).encode G := rfl

theorem taggedInstance_value (L : Language) {n : ℕ}
    (g : Signature AlgebraicComplex n) (p : ℕ → Prop) (G : TaggedInstance L g p) :
    value .nativeX (nativeTagged L g) (taggedInstanceEquiv L g p G).val =
      value .ordinary (tagged L g) G.val := by
  have h := reinterpret_denote (tagged_count_eq L g) (tagged_arity_eq L g) G.val
    (tagged L g).signature (nativeTagged L g).signature
    (fun _ => Signature.equality) (fun _ => Signature.disequality)
    KMatrix KInverse KMatrix_mul_inverse (tagged_vertex_heq L g)
    (fun _ => sourceKBasis_pullback.symm)
  exact congrFun h Fin.elim0

/-- The literal identity bit program, with proof-only validation transport. -/
def promiseSameBytesComputes {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool)
    (q : α → β) (bytes : ∀ G, eb.encode (q G) = ea.encode G) : Computes ea eb q :=
  recode (identityComputes ea) id (fun _ => rfl) (fun G => (bytes G).symm)

/-- A true constant-query promised adapter. All three queries satisfy the same
occurrence promise; the executed postprocessor converts canonical fields. -/
def promiseSameValueReduction (ws wt : Wiring) (L M : Language) {n m : ℕ}
    (g : Signature AlgebraicComplex n) (h : Signature AlgebraicComplex m)
    (p : ℕ → Prop) [DecidablePred p]
    (q : TaggedInstance L g p → TaggedInstance M h p)
    (pre : Computes (taggedEncoding L g p) (taggedEncoding M h p) q)
    (values : ∀ G, value ws (tagged L g) G.val = value wt (tagged M h) (q G).val) :
    LengthControlledOracleReduction
      (taggedEncoding L g p) (FixedFieldOutput.answerEncoding (tagged L g))
      (taggedEncoding M h p) (FixedFieldOutput.answerEncoding (tagged M h))
      (FixedFieldOutput.taggedAnswer ws L g p) (FixedFieldOutput.taggedAnswer wt M h p) := by
  let pre3 := pairComputes pre (pairComputes pre
    (pairComputes pre (constantComputes (taggedEncoding L g p) encodingBoolBool false)))
  let first := FixedFieldMachines.Wiring.firstComputes (FixedFieldOutput.answerEncoding (tagged M h))
    (pairEncoding (FixedFieldOutput.answerEncoding (tagged M h))
      (pairEncoding (FixedFieldOutput.answerEncoding (tagged M h)) encodingBoolBool))
  let post := first.andThen (FixedFieldOutput.conversionComputes (tagged M h) (tagged L g))
  exact controlledOfEq pre3 post (FixedFieldOutput.taggedOutputBound wt M h p)
    (FixedFieldOutput.taggedAnswer ws L g p)
    (fun G => (FixedFieldOutput.conversion_answer wt ws (tagged M h) (tagged L g)
      (q G).val G.val (values G).symm).symm)

def ordinaryToNativeTagged (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (p : ℕ → Prop) [DecidablePred p] :
    LengthControlledOracleReduction
      (taggedEncoding L g p) (FixedFieldOutput.answerEncoding (tagged L g))
      (taggedEncoding (inverseKLanguage L) (sourceKBasis.symm.action g) p)
      (FixedFieldOutput.answerEncoding (nativeTagged L g))
      (FixedFieldOutput.taggedAnswer .ordinary L g p)
      (FixedFieldOutput.taggedAnswer .nativeX (inverseKLanguage L) (sourceKBasis.symm.action g) p) :=
  promiseSameValueReduction .ordinary .nativeX L (inverseKLanguage L) g
    (sourceKBasis.symm.action g) p (taggedInstanceEquiv L g p)
    (promiseSameBytesComputes _ _ _ (taggedInstance_bytes L g p))
    (fun G => (taggedInstance_value L g p G).symm)

def nativeToOrdinaryTagged (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (p : ℕ → Prop) [DecidablePred p] :
    LengthControlledOracleReduction
      (taggedEncoding (inverseKLanguage L) (sourceKBasis.symm.action g) p)
      (FixedFieldOutput.answerEncoding (nativeTagged L g))
      (taggedEncoding L g p) (FixedFieldOutput.answerEncoding (tagged L g))
      (FixedFieldOutput.taggedAnswer .nativeX (inverseKLanguage L) (sourceKBasis.symm.action g) p)
      (FixedFieldOutput.taggedAnswer .ordinary L g p) := by
  let e := taggedInstanceEquiv L g p
  have bytes (G : TaggedInstance (inverseKLanguage L) (sourceKBasis.symm.action g) p) :
      (taggedEncoding L g p).encode (e.symm G) =
        (taggedEncoding (inverseKLanguage L) (sourceKBasis.symm.action g) p).encode G := by
    exact (taggedInstance_bytes L g p (e.symm G)).symm.trans
      (congrArg _ (e.apply_symm_apply G))
  refine promiseSameValueReduction .nativeX .ordinary (inverseKLanguage L) L
    (sourceKBasis.symm.action g) g p e.symm (promiseSameBytesComputes _ _ _ bytes) ?_
  intro G
  simpa only [e, Equiv.apply_symm_apply] using taggedInstance_value L g p (e.symm G)

/-- Transport the exact one-occurrence premise by genuine promise-preserving
machines and fixed field converters. No original reduction is reinterpreted
under a different oracle-output representation. -/
theorem ordinaryOne_to_native (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (one : FixedFieldOutput.TaggedReduces .ordinary L g (fun k => k = 1) L) :
    FixedFieldOutput.TaggedReduces .nativeX (inverseKLanguage L)
      (sourceKBasis.symm.action g) (fun k => k = 1) (inverseKLanguage L) := by
  obtain ⟨one⟩ := one
  let r := (nativeToOrdinaryTagged L g (fun k => k = 1)).controlledCompose one
  let target := FixedFieldOutput.sameValueReduction .ordinary .nativeX L (inverseKLanguage L)
    (inverseKInstanceEquiv L)
    (FixedFieldOutput.sameBytesComputes L (inverseKLanguage L) _ (inverseKInstance_bytes L))
    (fun G => (inverseKInstance_value L G).symm)
  exact ⟨r.controlledCompose target⟩

/-- The reverse promised reduction is obtained with the actual inverse graph
adapter and the same explicit canonical field conversion. -/
theorem nativeOne_to_ordinary (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (one : FixedFieldOutput.TaggedReduces .nativeX (inverseKLanguage L)
      (sourceKBasis.symm.action g) (fun k => k = 1) (inverseKLanguage L)) :
    FixedFieldOutput.TaggedReduces .ordinary L g (fun k => k = 1) L := by
  obtain ⟨one⟩ := one
  let e := inverseKInstanceEquiv L
  have bytes (G : Instance (inverseKLanguage L)) :
      (inputEncoding L).encode (e.symm G) = (inputEncoding (inverseKLanguage L)).encode G := by
    exact (inverseKInstance_bytes L (e.symm G)).symm.trans
      (congrArg _ (e.apply_symm_apply G))
  let target := FixedFieldOutput.sameValueReduction .nativeX .ordinary (inverseKLanguage L) L
    e.symm (FixedFieldOutput.sameBytesComputes (inverseKLanguage L) L _ bytes)
    (fun G => by simpa only [e, Equiv.apply_symm_apply] using inverseKInstance_value L (e.symm G))
  exact ⟨((ordinaryToNativeTagged L g (fun k => k = 1)).controlledCompose one).controlledCompose target⟩


end
end Paper2.SourceFaithful.SourceStatements.ReplicationTransport
