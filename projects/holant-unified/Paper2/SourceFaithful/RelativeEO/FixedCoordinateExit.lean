import Paper2.RelativeEO.FixedCoordinateExit
import Paper2.SourceFaithful.RelativeEO.WeightedComplementaryExit

/-! Canonical fixed-field answer version of the proved local construction.
The pure signatures/networks are unchanged. Machine reductions are proved again
from the separately named source-exact records; no output-code conversion or
old strict-root classification is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO

theorem fixed_coordinate_hard (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (f : Signature AlgebraicComplex 4)
    (hf : f ≠ 0) (hmem : (⟨4,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (i : Fin 4) (b : Bool) (hfix : ∀ x, f x ≠ 0 → x i = b) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  let e := Equiv.swap (0 : Fin 4) i
  let q := Tensor.reindex e f
  have hq : q ≠ 0 := by
    intro hz
    have hh := congrArg (Tensor.reindex e.symm) hz
    rw [Tensor.reindex_symm] at hh
    exact hf hh
  have hqfix : ∀ x, q x ≠ 0 → x 0 = b := by
    intro x hx
    have hh := hfix (fun j => x (e j)) hx
    simpa [e] using hh
  let g := Signature.pin q b
  have hqfactor : q = Signature.tensor (TensorDecomposition.literalPin b) g := fixed_first_factor q b hqfix
  have hg : g ≠ 0 := by
    intro hz
    apply hq
    rw [hqfactor,hz]
    funext x
    simp [Signature.tensor_apply]
  obtain ⟨B,hB,hBp,hBt⟩ := exists_prime_decomposition g (by decide) hg
  let A := TensorDecomposition.singleton (TensorDecomposition.literalPin b)
  let D := (A.append B).reindex e.symm
  have hval : D.value = f := by
    rw [TensorDecomposition.value_reindex,TensorDecomposition.value_append,
      TensorDecomposition.value_singleton,hB,← hqfactor]
    exact Tensor.reindex_symm e f
  have hpos : ∀ j, 0 < D.arity j :=
    TensorDecomposition.factors_append A B (fun n _ => 0 < n) (fun _ => Nat.zero_lt_one) hBp
  have hprime : ∀ j, TensorPrime (D.factor j) :=
    TensorDecomposition.factors_append A B (fun _ q => TensorPrime q)
      (fun _ => unary_tensorPrime _ (TensorDecomposition.literalPin_ne_zero b)) hBt
  obtain ⟨N,hLN,hfac,_,_,hNL,_⟩ := factorClosure_with_member_decomposition F L hpre
    (bothChargeSigns_not_oneSided hboth) f hmem D hval hpos hprime
  have hpin := hfac (A.appendIndexLeft B (0 : Fin 1))
  change (⟨(A.append B).arity (A.appendIndexLeft B (0 : Fin 1)),
    (A.append B).factor (A.appendIndexLeft B (0 : Fin 1))⟩ : AnySignature AlgebraicComplex) ∈ N.family at hpin
  rw [TensorDecomposition.append_factor_left A B (0 : Fin 1)] at hpin
  rcases U.unary_3_4 N (TensorDecomposition.literalPin b)
    (TensorDecomposition.literalPin_ne_zero b) hpin with ht | hh
  · exact False.elim (hnot (ht.mono_family (familyAction_mono sourceKBasis hLN)))
  · exact hh.transport hNL


end Paper2.SourceFaithful.RelativeEO
