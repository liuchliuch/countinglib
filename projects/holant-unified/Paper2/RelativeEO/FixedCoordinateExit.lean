import Paper2.RelativeEO.ARSMatching
import Paper2.RelativeEO.WeightedComplementaryExit

/-! A genuinely fixed coordinate supplies an actual unary prime factor. The
slice in the proof is used only to prove a tensor identity; it is never silently
adjoined as a pinning gadget. Paper 1 factor extraction is invoked afterwards. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem

/-- The first fixed coordinate separates as an ordered tensor factor. -/
theorem fixed_first_factor (f : Signature AlgebraicComplex 4) (b : Bool)
    (h : ∀ x, f x ≠ 0 → x 0 = b) :
    f = Signature.tensor (TensorDecomposition.literalPin b) (Signature.pin f b) := by
  funext x
  change f x = (if x 0 = b then 1 else 0) * f (Fin.cons b (fun j => x (Fin.natAdd 1 j)))
  by_cases hx : x 0 = b
  · rw [if_pos hx,one_mul]
    congr 1
    funext i
    fin_cases i
    · exact hx
    · rfl
    · rfl
    · rfl
  · rw [if_neg hx,zero_mul]
    by_contra hz
    exact hx (h x hz)

/-- The exact retained-language hardness exit for any fixed quaternary port. -/
theorem fixed_coordinate_hard (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (f : Signature AlgebraicComplex 4)
    (hf : f ≠ 0) (hmem : (⟨4,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (i : Fin 4) (b : Bool) (hfix : ∀ x, f x ≠ 0 → x i = b) :
    SharpPHard .nativeX L := by
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
  · exact hh.transport_unconditional hNL

end Paper2.RelativeEO
