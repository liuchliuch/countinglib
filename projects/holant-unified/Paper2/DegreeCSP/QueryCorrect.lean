import Paper2.DegreeCSP.QueryRecordIdentity
import Paper2.DegreeCSP.QueryValue

/-! The literal runtime query preserves the degree-CSP sum. The output
dictionary contains a literal Eq_k table and every edge is native X. -/
namespace Paper2.DegreeCSP.QueryGraph
open Paper2.Tractable Paper2.ExactInput Paper2.Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hk : 3 ≤ k) (r : Raw.Input s a k) (jK : Fin s)
variable (hK : (⟨a jK.val,G jK⟩ : AnySignature AlgebraicComplex) = ⟨k,equality k⟩)

/-- The ordered records emitted by the actual compiler compute the original
Boolean degree-CSP partition function without any scalar correction. -/
theorem query_partition :
    ((query G hk r jK (congrArg Sigma.fst hK)).val.realize
      (query G hk r jK (congrArg Sigma.fst hK)).property G
      (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 = Raw.value G r := by
  have he : query G hk r jK (congrArg Sigma.fst hK) =
      (⟨raw G hk r jK (congrArg Sigma.fst hK),
        raw_valid G hk r jK (congrArg Sigma.fst hK)⟩ :
        {q : RawClosedNetwork // q.WellFormed s 1 a}) :=
    Subtype.ext (raw_identity G hk r jK (congrArg Sigma.fst hK)).symm
  rw [he]
  exact raw_partition G hk r jK hK

end
end Paper2.DegreeCSP.QueryGraph
