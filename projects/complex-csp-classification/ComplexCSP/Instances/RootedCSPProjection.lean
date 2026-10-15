import ComplexCSP.Complexity.GadgetSubstitutionPresentation
import PlanarHom.RootedSignatureSpan

/-! # Finite, fixed-query recovery of one actual pinned CSP table value

The finite projection is over the complete family of actual rooted presentations.
It is valid for arbitrary graphs, including repeated scopes, parallel constraints,
and isolated variables. Only one fixed boundary block is recovered; there is no
claim that independently pinning every varying input vertex has constant cost.
-/
namespace ComplexCSP.RootedCSPProjection
open scoped BigOperators
open ComplexityGadgetSubstitution

variable {D K : Type} [Fintype D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s b : ℕ} (L : Language D K (Fin s))

/-- A fixed finite collection of genuine presentations recovers an arbitrary
fixed boundary pin by pairing against every varying actual presentation. -/
theorem exists_fixed_queries (a : Fin b → D) :
    ∃ n : ℕ, ∃ P : Fin n → Presentation L (Fin b), ∃ c : Fin n → K,
      ∀ Q : Presentation L (Fin b),
        Q.table a = ∑ j, c j * ComplexityCSPCode.partition L (presentationCode (Q.mul (P j))) := by
  classical
  obtain ⟨n,P,c,h⟩ := PlanarHom.RootedSignatureSpan.exists_family_coefficients
    (fun _ : (Fin b → D) => (1 : K)) (fun _ => zero_lt_one)
    (fun Q : Presentation L (Fin b) => Q.table) (Pi.single a 1)
  refine ⟨n,P,c,fun Q => ?_⟩
  have he := h Q
  simpa [PlanarHom.RootedSignatureSpan.pairing, Pi.single_apply,
    partition_presentationCode,Presentation.table_mul,mul_comm] using he

/-- The universal projection statement stores only finitely many fixed gadgets
and coefficients. It is obtained above without a graph-family or hardness oracle. -/
structure Data (a : Fin b → D) where
  count : ℕ
  gadgets : Fin count → Presentation L (Fin b)
  coefficients : Fin count → K
  correct : ∀ Q : Presentation L (Fin b),
    Q.table a = ∑ j, coefficients j *
      ComplexityCSPCode.partition L (presentationCode (Q.mul (gadgets j)))

noncomputable def choose (a : Fin b → D) : Data L a := by
  let h := exists_fixed_queries L a
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec⟩

end ComplexCSP.RootedCSPProjection
