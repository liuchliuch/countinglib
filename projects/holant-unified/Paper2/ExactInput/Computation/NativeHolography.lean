import Paper2.ExactInput.Computation.IndexedLanguage
import Paper2.ExactInput.Computation.GraphReinterpretation
import Paper2.Paper1Accepted

/-! Fixed-L exact K-coordinate transport. The normalization of the source K is
essential: edge pullback is exactly equality, with no graph-dependent scalar.
Every original graph record is retained byte-for-byte. -/
namespace Paper2.ExactInput.Computation
open Paper2.Tractable Paper2.Problem

noncomputable def kLanguage (L : Language) : Language :=
  indexedLanguage L (fun _ f => sourceKBasis.action f)

@[simp] theorem kLanguage_count (L : Language) : (kLanguage L).count = L.count :=
  indexedLanguage_count L _

@[simp] theorem kLanguage_arity (L : Language) : (kLanguage L).arity = L.arity :=
  indexedLanguage_arity L _

@[simp] theorem kLanguage_family (L : Language) : (kLanguage L).family = kImage L :=
  indexedLanguage_family L _

noncomputable def kInstanceEquiv (L : Language) : Instance L ≃ Instance (kLanguage L) :=
  reinterpretEquiv (kLanguage_count L).symm (kLanguage_arity L).symm

@[simp] theorem kInstance_raw (L : Language) (G : Instance L) :
    (kInstanceEquiv L G).val = G.val := rfl

/-- Same bits, not merely a polynomial-sized or computable translation. -/
@[simp] theorem kInstance_bytes (L : Language) (G : Instance L) :
    (inputEncoding (kLanguage L)).encode (kInstanceEquiv L G) = (inputEncoding L).encode G := rfl

/-- K^{-T} X K^{-1}=I follows from the exact normalized K^T K=X identity. -/
theorem inverseK_pullback : Kernel.pullback Signature.disequality KInverse = Signature.equality := by
  change Kernel.pullback Signature.disequality sourceKBasis.inverse = _
  rw [← sourceKBasis_pullback, ← pullback_mul, sourceKBasis.matrix_inverse]
  simp [Kernel.pullback]

/-- Literal exact value preservation, including zero/nullary labels and loops. -/
theorem kInstance_value (L : Language) (G : Instance L) :
    value .ordinary (kLanguage L) (kInstanceEquiv L G) = value .nativeX L G := by
  have h := reinterpret_denote (kLanguage_count L).symm (kLanguage_arity L).symm G
    L.signature (kLanguage L).signature
    (fun _ => Signature.disequality) (fun _ => Signature.equality)
    KInverse KMatrix KInverse_mul_matrix
    (fun i => indexedLanguage_signature L (fun _ f => sourceKBasis.action f) i)
    (fun _ => inverseK_pullback.symm)
  exact congrFun h Fin.elim0

end Paper2.ExactInput.Computation
