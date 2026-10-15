import Paper2.Synthesis.SameGraphHardness
import Paper2.Tractable.Conformal.CommonBasis

/-! The final ordinary/native coordinate change on unchanged original graph
bytes.  The constants in this fixed-language transport need no uniform input-
table conversion algorithm.  All oracle-machine costs have already been proved
in `SameGraphHardness`; no reduction convention is assumed here. -/
namespace Paper2.Synthesis
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation Paper2.Problem

noncomputable def inverseKLanguage (L : Language) : Language :=
  indexedLanguage L (fun _ f => sourceKBasis.symm.action f)

@[simp] theorem inverseKLanguage_count (L : Language) :
    (inverseKLanguage L).count = L.count := indexedLanguage_count L _

@[simp] theorem inverseKLanguage_arity (L : Language) :
    (inverseKLanguage L).arity = L.arity := indexedLanguage_arity L _

@[simp] theorem inverseKLanguage_family (L : Language) :
    (inverseKLanguage L).family = kCoordinates L.family := indexedLanguage_family L _

@[simp] theorem kImage_inverseKLanguage (L : Language) :
    kImage (inverseKLanguage L) = L.family := by
  simp only [kImage, inverseKLanguage_family, kCoordinates, Conformal.familyAction_action_symm]

noncomputable def inverseKInstanceEquiv (L : Language) :
    Instance L ≃ Instance (inverseKLanguage L) :=
  reinterpretEquiv (inverseKLanguage_count L).symm (inverseKLanguage_arity L).symm

@[simp] theorem inverseKInstance_raw (L : Language) (G : Instance L) :
    (inverseKInstanceEquiv L G).val = G.val := rfl

@[simp] theorem inverseKInstance_bytes (L : Language) (G : Instance L) :
    (inputEncoding (inverseKLanguage L)).encode (inverseKInstanceEquiv L G) =
      (inputEncoding L).encode G := rfl

theorem inverseKInstance_value (L : Language) (G : Instance L) :
    value .nativeX (inverseKLanguage L) (inverseKInstanceEquiv L G) =
      value .ordinary L G := by
  have h := reinterpret_denote (inverseKLanguage_count L).symm (inverseKLanguage_arity L).symm G
    L.signature (inverseKLanguage L).signature
    (fun _ => Signature.equality) (fun _ => Signature.disequality)
    KMatrix KInverse KMatrix_mul_inverse
    (fun i => indexedLanguage_signature L (fun _ f => sourceKBasis.symm.action f) i)
    (fun _ => sourceKBasis_pullback.symm)
  exact congrFun h Fin.elim0

/-- No code conversion, scalar correction, or change of oracle program occurs. -/
theorem ordinary_hard_iff_inverseK_native (L : Language) :
    SharpPHard .ordinary L ↔ SharpPHard .nativeX (inverseKLanguage L) := by
  constructor
  · intro h
    exact h.sameGraph (inverseKInstanceEquiv L)
      (inverseKInstance_bytes L) (inverseKInstance_value L)
  · intro h
    apply h.sameGraph (inverseKInstanceEquiv L).symm
    · intro G
      exact (inverseKInstance_bytes L ((inverseKInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((inverseKInstanceEquiv L).apply_symm_apply G))
    · intro G
      exact (inverseKInstance_value L ((inverseKInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((inverseKInstanceEquiv L).apply_symm_apply G))

end Paper2.Synthesis
