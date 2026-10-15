import Holant.Dihedral.TwoCardLocalization.ActualCards

/-! Extraction on one shared original edge without assuming that the rest of
the two matchings agree. Both edge ID and endpoint orientation are recovered
from the original port equivalences. -/
namespace Paper2.SourceFaithful.SourceStatements
noncomputable section
open Holant Holant.Marked Holant.Certificates
open Holant.Dihedral.EndpointParallelogram
open Holant.Dihedral.TwoCardLocalization
set_option backward.isDefEq.respectTransparency false

variable {s n : ℕ}

/-- Recover the two original endpoints of one common matched edge. -/
theorem common_edge_endpoints (p₀ p₁ : (Fin s × Bool) ≃ Fin n) (e : Fin s)
    (hm : (Pairing.ofPorts p₁).mate (p₀ (e,false)) = p₀ (e,true)) :
    let j := (p₁.symm (p₀ (e,false))).1
    let flip := (p₁.symm (p₀ (e,false))).2
    p₁ (j,flip) = p₀ (e,false) ∧ p₁ (j,!flip) = p₀ (e,true) := by
  exact ⟨p₁.apply_symm_apply _,hm⟩

private theorem insertPair_swap (u v : Fin n) (huv : u ≠ v)
    (a b : Bool) (x : Fin n → Bool) :
    MatchingContractionClosure.insertPair u v a b x =
      MatchingContractionClosure.insertPair v u b a x := by
  funext i
  by_cases hiu : i = u
  · subst i
    simp [MatchingContractionClosure.insertPair,huv]
  by_cases hiv : i = v
  · subst i
    simp [MatchingContractionClosure.insertPair,Ne.symm huv]
  simp [MatchingContractionClosure.insertPair,hiu,hiv]

/-- Extract the actual factor of the second matching on one common original
edge, with the original endpoint reversal accounted for. -/
theorem common_edge_extract (p₀ p₁ : (Fin s × Bool) ≃ Fin n)
    (A : Fin s → Mat) (κ : Scalar) (e : Fin s)
    (hm : (Pairing.ofPorts p₁).mate (p₀ (e,false)) = p₀ (e,true))
    (u v : Bool) (x : Fin n → Bool) :
    Holant.Dihedral.CompatibleClosure.productValue p₁ A κ
      (MatchingContractionClosure.insertPair (p₀ (e,false)) (p₀ (e,true)) u v x) =
    relativeFactor p₀ p₁ A e u v *
      (κ * ∏ d ∈ ({(p₁.symm (p₀ (e,false))).1}ᶜ : Finset (Fin s)),
        A d (x (p₁ (d,false))) (x (p₁ (d,true)))) := by
  classical
  obtain ⟨hfirst,hsecond⟩ := common_edge_endpoints p₀ p₁ e hm
  let j := (p₁.symm (p₀ (e,false))).1
  let flip := (p₁.symm (p₀ (e,false))).2
  change p₁ (j,flip) = p₀ (e,false) at hfirst
  change p₁ (j,!flip) = p₀ (e,true) at hsecond
  change MatchingContractionClosure.productValue p₁ A κ _ = _
  have hdist : p₀ (e,false) ≠ p₀ (e,true) := by
    intro h
    have hh := congrArg Prod.snd (p₀.injective h)
    cases hh
  cases hflip : flip
  · have h₀ : p₁ (j,false) = p₀ (e,false) := by simpa only [hflip] using hfirst
    have h₁ : p₁ (j,true) = p₀ (e,true) := by simpa only [hflip,Bool.not_false] using hsecond
    rw [← h₀,← h₁,MatchingContractionClosure.product_extract_edge]
    simp [relativeFactor,← h₀]
  · have h₀ : p₁ (j,true) = p₀ (e,false) := by simpa only [hflip] using hfirst
    have h₁ : p₁ (j,false) = p₀ (e,true) := by simpa only [hflip,Bool.not_true] using hsecond
    rw [insertPair_swap _ _ hdist,← h₀,← h₁,MatchingContractionClosure.product_extract_edge]
    simp [relativeFactor,← h₀]

/-- The actual locally aligned factor remains nonsingular monomial. -/
theorem relativeFactor_isMonomial (p₀ p₁ : (Fin s × Bool) ≃ Fin n)
    (A : Fin s → Mat) (hA : ∀ e, IsMonomial (A e)) (e : Fin s) :
    IsMonomial (relativeFactor p₀ p₁ A e) := by
  dsimp only [relativeFactor]
  split
  · exact (hA _).transpose
  · exact hA _

end
end Paper2.SourceFaithful.SourceStatements

