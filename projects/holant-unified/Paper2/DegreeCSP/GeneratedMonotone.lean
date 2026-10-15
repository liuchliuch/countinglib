import Paper2.DegreeCSP.GeneratedOrthogonality

/-! A literal family inclusion preserves the same generated presentation;
its scopes, degrees, hidden assignments and coefficients do not change. -/
namespace Paper2.DegreeCSP
noncomputable section

theorem generated_mono {K : Type} [CommSemiring K] {F G : SignatureFamily K}
    {k n : ℕ} {f : Signature K n} (hf : Generated F k f) (hFG : F⊆G) :
    Generated G k f := by
  obtain ⟨P,hUses,hDiv,hValue⟩ := hf
  exact ⟨P,fun c=>hFG (hUses c),hDiv,hValue⟩

theorem OriginalBO.AllGeneratedOriginalBO.mono {F G : SignatureFamily Tractable.AlgebraicComplex}
    {k : ℕ} (h : OriginalBO.AllGeneratedOriginalBO G k) (hFG : F⊆G) :
    OriginalBO.AllGeneratedOriginalBO F k :=
  fun n f hf=>h n f (generated_mono hf hFG)

end
end Paper2.DegreeCSP
