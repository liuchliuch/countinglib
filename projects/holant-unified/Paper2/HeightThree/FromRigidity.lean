import Paper2.HeightThree.LoopObstruction
import Paper2.HeightThree.MountainCoordinates

/-! The logical use of joint-deck rigidity in Theorem 7.5. This intermediate
lemma explicitly consumes the finite-certificate conclusion; it does not
assume any new complexity exit. The caller supplies the checked A.4 theorem. -/
namespace Paper2.HeightThree
open Certificates.Q6 Tractable

lemma member_realizable (F : SignatureFamily AlgebraicComplex) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NetworkRealizable F f := by
  let e : (Σ _ : Unit, Fin n) ≃ Fin n := {
    toFun := fun p => p.2
    invFun := fun i => ⟨(),i⟩
    left_inv := by rintro ⟨u,i⟩; cases u; rfl
    right_inv := fun _ => rfl }
  have h := (NetworkRealizable.piTensor (fun _ : Unit => n) (fun _ => f) (fun _ => hf)).reindex e
  have hh : Tensor.reindex e (Tensor.piTensor (fun _ : Unit => f)) = f := by
    funext x
    simp [Tensor.reindex,Tensor.piTensor,e]
  exact hh ▸ h

lemma card_realizable (F : SignatureFamily AlgebraicComplex) (M : Signature AlgebraicComplex 6)
    (hM : (⟨6,M⟩ : AnySignature AlgebraicComplex) ∈ F) (s : CardSpec) (hs : RawValidCardSpec s) :
    NetworkRealizable F (cardNetwork s hs M).denote :=
  ⟨4,cardNetwork s hs M,Equiv.refl _,cardNetwork_uses s hs M F hM,
    cardNetwork_nativeX s hs M,rfl⟩

/-- The only input not yet about the physical graph is the separate proved
finite-rigidity implication. No such input is accepted as a Paper1 interface. -/
theorem nonmatching_of_rigidity (F : SignatureFamily AlgebraicComplex)
    (a b : AlgebraicComplex) (q : Fin 20 → AlgebraicComplex) (hab : a*b ≠ 0)
    (hM : (⟨6,coordinateMountain a b q⟩ : AnySignature AlgebraicComplex) ∈ F)
    (rigidity : AllLoopSafe q → AllTwoCopySafe q (a*b) → OneComplementPair q) :
    ∃ h : Signature AlgebraicComplex 4, h ≠ 0 ∧ IsEO ⟨4,h⟩ ∧
      ¬ WeightedMatching.IsProduct h ∧ NetworkRealizable F h := by
  classical
  by_cases hl : ∀ i : Fin 15, loopSignature (coordinateMountain a b q) i = 0 ∨
      WeightedMatching.IsProduct (loopSignature (coordinateMountain a b q) i)
  · by_cases hc : ∀ s : CardSpec, ∀ hs : ValidCardSpec s,
        (cardNetwork s hs.raw (coordinateMountain a b q)).denote = 0 ∨
          WeightedMatching.IsProduct (cardNetwork s hs.raw (coordinateMountain a b q)).denote
    · have hls : AllLoopSafe q := by
        intro i
        have hh := matching_or_zero_necessary_safe _ (hl i)
        have he : (fun e => loopSignature (coordinateMountain a b q) i (eoWords e)) =
            loopArray q (loopSpecs i) := funext (loopSignature_array a b q i)
        rwa [he] at hh
      have hcs : AllTwoCopySafe q (a*b) := by
        intro s hs
        have hh := matching_or_zero_necessary_safe _ (hc s hs)
        have he : (fun e => (cardNetwork s hs.raw (coordinateMountain a b q)).denote (eoWords e)) =
            twoCopyArray q (a*b) s := funext (cardNetwork_array a b q s hs.raw)
        rwa [he] at hh
      have hp := rigidity hls hcs
      by_cases hq : q = 0
      · subst q
        let hs : ValidCardSpec (denseSpecs 0) := dense_specs_valid 0
        have hn := zero_center_card_nonmatching a b hab (denseSpecs 0) hs.raw
        exact False.elim ((hc (denseSpecs 0) hs).elim hn.1 hn.2)
      · obtain ⟨i,hne,hnot⟩ := revealingLoop_nonmatching a b q hq hp
        exact False.elim ((hl i).elim hne hnot)
    · obtain ⟨s,hs⟩ := not_forall.mp hc
      obtain ⟨hvalid,hbad⟩ := not_forall.mp hs
      refine ⟨(cardNetwork s hvalid.raw (coordinateMountain a b q)).denote,
        (fun hz => hbad (Or.inl hz)),cardNetwork_isEO a b q s hvalid.raw,
        (fun hp => hbad (Or.inr hp)),card_realizable F _ hM s hvalid.raw⟩
  · obtain ⟨i,hbad⟩ := not_forall.mp hl
    refine ⟨loopSignature (coordinateMountain a b q) i,
      (fun hz => hbad (Or.inl hz)),loopSignature_isEO a b q i,
      (fun hp => hbad (Or.inr hp)),?_⟩
    exact loopSignature_realizable F _ (member_realizable F _ hM) i

end Paper2.HeightThree
