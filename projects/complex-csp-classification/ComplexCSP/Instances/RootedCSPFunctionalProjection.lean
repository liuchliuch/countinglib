import ComplexCSP.Instances.RootedCSPProjection

/-! # Fixed root-subset sums, with all original color multiplicities retained -/
namespace ComplexCSP.RootedCSPProjection
open scoped BigOperators
open ComplexityGadgetSubstitution
variable {D K : Type} [Fintype D] [Field K]
variable {s b : ℕ} (L : Language D K (Fin s))

structure FunctionalData (target : (Fin b → D) → K) where
  count : ℕ
  gadgets : Fin count → Presentation L (Fin b)
  coefficients : Fin count → K
  correct : ∀ Q : Presentation L (Fin b),
    (∑ a, target a * Q.table a) = ∑ j, coefficients j *
      ComplexityCSPCode.partition L (presentationCode (Q.mul (gadgets j)))

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem exists_functional_queries (target : (Fin b → D) → K) :
    Nonempty (FunctionalData L target) := by
  classical
  obtain ⟨n,P,c,h⟩ := PlanarHom.RootedSignatureSpan.exists_family_coefficients
    (fun _ : (Fin b → D) => (1 : K)) (fun _ => zero_lt_one)
    (fun Q : Presentation L (Fin b) => Q.table) target
  refine ⟨⟨n,P,c,fun Q => ?_⟩⟩
  simpa only [PlanarHom.RootedSignatureSpan.pairing,one_mul,mul_one,
    partition_presentationCode,Presentation.table_mul,mul_comm] using h Q

noncomputable def chooseFunctional (target : (Fin b → D) → K) : FunctionalData L target :=
  Classical.choice (exists_functional_queries L target)

end ComplexCSP.RootedCSPProjection
