import Paper2.SourceFaithful.SourceStatements.AlgebraicWitness
import Holant.Proofs.Tractability.EOEvaluation.EOConditionCertificate.LiteralProduct

/-! Class soundness for a fixed algebraic returned matrix. Only the free
normal-form parameters descend here; the supplied table and matrix are
retained. This is the semantic bridge needed by the actual witness emitter. -/
namespace Paper2.SourceFaithful.SourceStatements.AlgebraicWitness
set_option backward.isDefEq.respectTransparency false
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate
open Holant.Tractable
noncomputable section

private theorem affine_of_complex {n : ℕ}
    (f : Paper2.Signature Paper2.Tractable.AlgebraicComplex n)
    (h : ComplexMember .affine (fun x => (f x : ℂ))) : Paper2.Tractable.Affine f := by
  obtain ⟨C,c,hc⟩ := (ExtensionAffine.affine_iff
    (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) _).mp h
  have he : ∃ c : ℂ, ∀ x, (f x : ℂ) =
      c * (AffineNormalForm.formula C 1 x : ℂ) := by
    refine ⟨c,?_⟩
    intro x
    have hco : ExtensionAffine.coefficient C x = AffineNormalForm.formula C 1 x := by
      simpa only [ExtensionAffine.formula,RingHom.id_apply,one_mul] using
        congrFun (ExtensionAffine.formula_id C 1) x
    change (f x : ℂ) = c *
      (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) (AffineNormalForm.formula C 1 x)
    simpa only [ExtensionAffine.formula,hco] using congrFun hc x
  obtain ⟨d,hd⟩ := (LiteralAffine.scalar_descent C f).mp he
  exact (Paper2.Paper1Proved.affine_iff f).mpr
    ((AffineNormalForm.affine_iff f).mpr ⟨C,d,hd⟩)

private theorem product_of_complex {n : ℕ}
    (f : Paper2.Signature Paper2.Tractable.AlgebraicComplex n)
    (h : ComplexMember .product (fun x => (f x : ℂ))) : Paper2.Tractable.Product f := by
  obtain ⟨S,c,hc⟩ := (ExtensionSource.productOver_iff _).mp h
  obtain ⟨d,hd⟩ := (LiteralProduct.parameter_descent S f).mp
    ⟨c,fun x => congrFun hc x⟩
  exact (Paper2.Paper1Proved.product_iff f).mpr ((product_iff f).mpr ⟨S,d,hd⟩)

/-- Complex normal-form parameters do not enlarge any of the three source
classes for a fixed algebraic table. In particular this preserves the table
obtained from the literal returned matrix. -/
theorem member_of_complex {n : ℕ} (C : Class)
    (f : Paper2.Signature Paper2.Tractable.AlgebraicComplex n)
    (h : ComplexMember C (fun x => (f x : ℂ))) : Member C f := by
  cases C with
  | affine => exact affine_of_complex f h
  | product => exact product_of_complex f h
  | localAffine =>
    apply (Paper2.Paper1Proved.localAffine_iff f).mpr
    intro alpha ha
    have ha' : (f alpha : ℂ) ≠ 0 := by
      intro hz
      exact ha (Subtype.ext hz)
    have ht := h alpha ha'
    let g := ExtensionLocalAffine.twist
      (RingHom.id Paper2.Tractable.AlgebraicComplex) alpha f
    have he : ExtensionLocalAffine.twist
        (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) alpha
        (fun x => (f x : ℂ)) = fun x => (g x : ℂ) := by
      funext x
      dsimp only [ExtensionLocalAffine.twist,g,RingHom.id_apply]
      change (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) _ *
          (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) (f x) =
        (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) (_ * f x)
      exact (map_mul _ _ _).symm
    rw [he] at ht
    have hg := (Paper2.Paper1Proved.affine_iff g).mp (affine_of_complex g ht)
    simpa only [g,ExtensionLocalAffine.twist_id] using hg

/-- The supplied algebraic matrix itself is a source witness when its
transformed tables have the displayed complex normal forms. -/
theorem witness_at_of_complex {s : ℕ} {arity : Fin s → ℕ} (C : Class)
    (G : (i : Fin s) → Paper2.Signature Paper2.Tractable.AlgebraicComplex (arity i))
    (E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex)
    (U : Paper2.Tractable.InvertibleKernel)
    (hG : ∀ i, ComplexMember C (fun x => (U.symm.action (G i) x : ℂ)))
    (hE : ComplexMember C (fun x =>
      (Paper2.Tractable.kernelSignature (Paper2.Kernel.pullback E U.matrix) x : ℂ))) :
    (∀ i, Member C (U.symm.action (G i))) ∧
      Member C (Paper2.Tractable.kernelSignature (Paper2.Kernel.pullback E U.matrix)) :=
  ⟨fun i => member_of_complex C _ (hG i),member_of_complex C _ hE⟩

end
end Paper2.SourceFaithful.SourceStatements.AlgebraicWitness

