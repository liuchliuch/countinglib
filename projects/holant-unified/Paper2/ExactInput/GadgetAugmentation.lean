import Paper2.ExactInput.Reductions
import Paper2.ExactInput.Coverage

/-! Actual graph realizations yield finite literal input augmentations under
only the explicitly accepted source direct-gadget reduction convention. -/
namespace Paper2
open Tractable ExactInput

private def suppliedShape (n : ℕ) : NetworkShape n where
  vertices := 1
  arity _ := n
  edges := 0
  ports := {
    toFun p := .inl p.2
    invFun p := Sum.elim (fun i => ⟨0, i⟩) (fun q => Fin.elim0 q.1) p
    left_inv p := by
      rcases p with ⟨v, i⟩
      have hv : v = 0 := Fin.eq_zero v
      subst v
      rfl
    right_inv p := by
      cases p with
      | inl i => rfl
      | inr q => exact Fin.elim0 q.1 }

private noncomputable def suppliedNetwork {n : ℕ} (f : Signature AlgebraicComplex n) :
    Network AlgebraicComplex n where
  shape := suppliedShape n
  vertex _ := f
  edge e := Fin.elim0 e

private theorem suppliedNetwork_denote {n : ℕ} (f : Signature AlgebraicComplex n) :
    (suppliedNetwork f).denote = f := by
  funext x
  dsimp only [suppliedNetwork, Network.denote, suppliedShape, NetworkShape.assignment]
  simp
  rfl

namespace NativeNetworkRealizesUpTo

theorem of_mem {F : SignatureFamily AlgebraicComplex} {n : ℕ}
    {f : Signature AlgebraicComplex n} (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NativeNetworkRealizesUpTo F f := by
  refine ⟨suppliedNetwork f, fun _ => hf, ?_, 1, one_ne_zero, ?_⟩
  · intro e
    exact Fin.elim0 e
  · simpa using suppliedNetwork_denote f

theorem of_realizable {F : SignatureFamily AlgebraicComplex} {n : ℕ}
    {f : Signature AlgebraicComplex n} (hf : NetworkRealizable F f) :
    NativeNetworkRealizesUpTo F f := by
  obtain ⟨N, hU, hX, hN⟩ := hf.ordered
  exact ⟨N, hU, hX, 1, one_ne_zero, by simpa using hN⟩

end NativeNetworkRealizesUpTo

namespace Paper1DirectGadgetAccepted

/-- The augmentation is an actual finite minimal-root-coded language, preserving
all original members and with a genuine length-controlled machine reduction. -/
theorem adjoin (P : Paper1DirectGadgetAccepted) (L : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : NativeNetworkRealizesUpTo L.family f) :
    ∃ M : Language, M.family = insert (⟨n, f⟩ : AnySignature AlgebraicComplex) L.family ∧
      Problem.Reduces .nativeX M L := by
  obtain ⟨M, hM⟩ := Language.coverage_family _ (L.family_finite.insert ⟨n, f⟩)
  refine ⟨M, hM, P.directGadget_2_5 L M ?_ ?_⟩
  · rw [hM]
    exact Set.subset_insert _ _
  · intro g hg
    rw [hM] at hg
    rcases hg with he | hg
    · subst g
      exact hf
    · exact NativeNetworkRealizesUpTo.of_mem hg

/-- Direct connection to the new Paper 2 concrete-network charge construction. -/
theorem adjoin_realizable (P : Paper1DirectGadgetAccepted) (L : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : NetworkRealizable L.family f) :
    ∃ M : Language, M.family = insert (⟨n, f⟩ : AnySignature AlgebraicComplex) L.family ∧
      Problem.Reduces .nativeX M L :=
  P.adjoin L f (NativeNetworkRealizesUpTo.of_realizable hf)

end Paper1DirectGadgetAccepted
end Paper2
