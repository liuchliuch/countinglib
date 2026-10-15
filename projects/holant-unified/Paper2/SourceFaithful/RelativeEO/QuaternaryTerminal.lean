import Paper2.RelativeEO.QuaternaryForms
import Paper2.RelativeEO.BinaryClassDeterminant
import Paper2.SourceFaithful.RelativeEO.PairTableNetwork
import Paper2.SourceFaithful.RelativeEO.FixedCoordinateExit

/-! Canonical fixed-field answer version of the proved local construction.
The pure signatures/networks are unchanged. Machine reductions are proved again
from the separately named source-exact records; no output-code conversion or
old strict-root classification is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO

private theorem binWord_eq_vector (a b : Bool) : binWord a b = ![a,b] := by
  funext i; fin_cases i <;> rfl

theorem quaternary_nonmatching_terminal (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (f : Signature AlgebraicComplex 4)
    (hf : f ≠ 0) (he : Signature.CentralSupport f)
    (hmem : (⟨4,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hout : ¬ WeightedMatching.IsProduct f) : FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  obtain ⟨H,hH⟩ := Language.coverage_family ({⟨4,f⟩} : SignatureFamily AlgebraicComplex)
    (Set.finite_singleton _)
  have hpreH : Preprocessed H.family := by
    intro g hg
    rw [hH,Set.mem_singleton_iff] at hg
    subst g
    exact ⟨by change 0 < (4 : ℕ); decide,hf⟩
  have heH : ∀ g ∈ H.family, IsEO g := by
    intro g hg
    rw [hH,Set.mem_singleton_iff] at hg
    subst g
    exact ⟨⟨2,rfl⟩,he⟩
  have hfH : (⟨4,f⟩ : AnySignature AlgebraicComplex) ∈ H.family := by rw [hH]; exact Set.mem_singleton _
  by_cases ht : EOTract H.family
  · rcases eoTract_quaternary_forms H.family ht f hfH with hfix | hcomp | hpair
    · obtain ⟨i,b,hfix⟩ := hfix
      exact fixed_coordinate_hard F U L hpre hboth hnot f hf hmem i b hfix
    · obtain ⟨s,p,q,hs,hp,hq,hform⟩ := hcomp
      exact complementary_hard G O F U L hpre hboth hnot s hs p q hp hq (hform ▸ hmem)
    · obtain ⟨e,g,hform,hfull,hclass⟩ := hpair
      have hdet : ¬ g (binWord false false) * g (binWord true true) =
          g (binWord false true) * g (binWord true false) := by
        intro hdet
        have hh := IsProduct_reindex (pairTable_isProduct g hfull hdet) e.symm
        rw [← hform,Tensor.reindex_symm] at hh
        exact hout hh
      have hneg : g (binWord false false) * g (binWord true true) +
          g (binWord false true) * g (binWord true false) = 0 := by
        rcases hclass with hA | hP
        · have hh := affine_binary_full_support hA hfull
          simp only [← binWord_eq_vector] at hh
          rcases hh with hpos | hneg
          · exact False.elim (hdet hpos)
          · linear_combination hneg
        · exact False.elim (hdet (by simpa only [← binWord_eq_vector] using product_binary_full_support hP hfull))
      exact realized_complementary_hard G O F U L hpre hboth hnot
        (quadWord false true true false) (by decide) _ _
        (mul_ne_zero (mul_ne_zero (by norm_num) (hfull _)) (hfull _))
        (mul_ne_zero (mul_ne_zero (by norm_num) (hfull _)) (hfull _))
        (pairNetwork_realizable f e g hform hmem hneg)
  · have hh := (E.eo_2_16 H hpreH heH).2 ht
    exact hh.transport (R.restriction_2_5 H L (by
      intro g hg
      rw [hH,Set.mem_singleton_iff] at hg
      exact hg ▸ hmem))


end Paper2.SourceFaithful.RelativeEO
