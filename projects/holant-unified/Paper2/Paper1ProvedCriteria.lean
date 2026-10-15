import Paper2.Tractable.Criteria
import Holant.Tractable.Criteria

/-! Structural correspondence to the actual proved Paper 1 criterion. The
algebraic carrier and tensor tables agree definitionally. Existential witnesses
live in separately declared record types; their complete data are transported
in both directions here, retaining phases, scale, ports and the common basis. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable
noncomputable section

def affineSystemIso (n : ℕ) : Paper2.Tractable.AffineSystem n ≃ Holant.Tractable.AffineSystem n where
  toFun v := ⟨v.rows, v.matrix, v.rhs⟩
  invFun v := ⟨v.rows, v.matrix, v.rhs⟩
  left_inv _ := rfl
  right_inv _ := rfl

def quadraticPhaseIso (n : ℕ) : Paper2.Tractable.QuadraticPhase n ≃ Holant.Tractable.QuadraticPhase n where
  toFun v := ⟨v.constant, v.linear, v.mixed, v.even_mixed⟩
  invFun v := ⟨v.constant, v.linear, v.mixed, v.even_mixed⟩
  left_inv _ := rfl
  right_inv _ := rfl

def invertibleKernelIso : Paper2.Tractable.InvertibleKernel ≃ Holant.Tractable.InvertibleKernel where
  toFun v := ⟨v.matrix, v.inverse, v.matrix_inverse, v.inverse_matrix⟩
  invFun v := ⟨v.matrix, v.inverse, v.matrix_inverse, v.inverse_matrix⟩
  left_inv _ := rfl
  right_inv _ := rfl

def tensorDecompositionIso (n : ℕ) : Paper2.TensorDecomposition AlgebraicComplex n ≃ Holant.TensorDecomposition AlgebraicComplex n where
  toFun v := ⟨v.count, v.arity, v.factor, v.ports, v.scale⟩
  invFun v := ⟨v.count, v.arity, v.factor, v.ports, v.scale⟩
  left_inv _ := rfl
  right_inv _ := rfl

def orientedPerfectPairingIso (n : ℕ) : Paper2.Tractable.OrientedPerfectPairing n ≃ Holant.Tractable.OrientedPerfectPairing n where
  toFun v := ⟨v.count, v.ports⟩
  invFun v := ⟨v.count, v.ports⟩
  left_inv _ := rfl
  right_inv _ := rfl

def productFactorIso (n : ℕ) : ProductFactor n ≃ Holant.Tractable.ProductFactor n where
  toFun
    | .unary j u h => .unary j u h
    | .equality j k => .equality j k
    | .disequality j k => .disequality j k
  invFun
    | .unary j u h => .unary j u h
    | .equality j k => .equality j k
    | .disequality j k => .disequality j k
  left_inv v := by cases v <;> rfl
  right_inv v := by cases v <;> rfl

@[simp] theorem productFactor_eval {n : ℕ} (v : ProductFactor n) :
    (productFactorIso n v).eval = v.eval := by cases v <;> rfl
@[simp] theorem productFactor_eval_back {n : ℕ} (v : Holant.Tractable.ProductFactor n) :
    ((productFactorIso n).symm v).eval = v.eval := by cases v <;> rfl

@[simp] theorem affineFormula_forward {n : ℕ} (c : AlgebraicComplex)
    (S : AffineSystem n) (Q : QuadraticPhase n) :
    Holant.Tractable.affineFormula c (affineSystemIso n S) (quadraticPhaseIso n Q) =
      affineFormula c S Q := rfl
@[simp] theorem affineFormula_backward {n : ℕ} (c : AlgebraicComplex)
    (S : Holant.Tractable.AffineSystem n) (Q : Holant.Tractable.QuadraticPhase n) :
    affineFormula c ((affineSystemIso n).symm S) ((quadraticPhaseIso n).symm Q) =
      Holant.Tractable.affineFormula c S Q := rfl

 theorem affine_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    Affine f ↔ Holant.Tractable.Affine f := by
  constructor
  · rintro (h | ⟨c,hc,S,Q,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c,hc,affineSystemIso n S,quadraticPhaseIso n Q,h⟩
  · rintro (h | ⟨c,hc,S,Q,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c,hc,(affineSystemIso n).symm S,(quadraticPhaseIso n).symm Q,h⟩

@[simp] theorem productFormula_forward {n : ℕ} (c : AlgebraicComplex)
    (vs : List (ProductFactor n)) :
    Holant.Tractable.productFormula c (vs.map (productFactorIso n)) = productFormula c vs := by
  funext x
  simp only [Holant.Tractable.productFormula, productFormula, List.map_map,
    Function.comp_def, productFactor_eval]
@[simp] theorem productFormula_backward {n : ℕ} (c : AlgebraicComplex)
    (vs : List (Holant.Tractable.ProductFactor n)) :
    productFormula c (vs.map (productFactorIso n).symm) =
      Holant.Tractable.productFormula c vs := by
  funext x
  simp only [Holant.Tractable.productFormula, productFormula, List.map_map,
    Function.comp_def, productFactor_eval_back]

 theorem product_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    Product f ↔ Holant.Tractable.Product f := by
  constructor
  · rintro (h | ⟨c,hc,vs,h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨c,hc,vs.map (productFactorIso n),?_⟩
      simpa only [productFormula_forward] using h
  · rintro (h | ⟨c,hc,vs,h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨c,hc,vs.map (productFactorIso n).symm,?_⟩
      simpa only [productFormula_backward] using h

 theorem localAffine_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    LocalAffine f ↔ Holant.Tractable.LocalAffine f := by
  constructor
  · intro h alpha ha
    exact (affine_iff _).mp (h alpha ha)
  · intro h alpha ha
    exact (affine_iff _).mpr (h alpha ha)

/-- The matrix, both inverse equations and the whole-signature action are retained. -/
 theorem commonTransformable_iff
    (C D : SignatureFamily AlgebraicComplex)
    (hCD : ∀ f, f ∈ C ↔ f ∈ D) (F : SignatureFamily AlgebraicComplex) :
    CommonTransformable C F ↔ Holant.Tractable.CommonTransformable D F := by
  constructor
  · rintro ⟨hf,B,he,hfB⟩
    exact ⟨hf,invertibleKernelIso B,(hCD _).mp he,fun f h => (hCD _).mp (hfB f h)⟩
  · rintro ⟨hf,B,he,hfB⟩
    exact ⟨hf,invertibleKernelIso.symm B,(hCD _).mpr he,fun f h => (hCD _).mpr (hfB f h)⟩

 theorem tensorClosure_iff
    (C D : (n : ℕ) → Signature AlgebraicComplex n → Prop)
    (hCD : ∀ n f, C n f ↔ D n f) {n : ℕ} (f : Signature AlgebraicComplex n) :
    Signature.TensorClosure C f ↔ Holant.Signature.TensorClosure D f := by
  constructor
  · rintro ⟨T,hT,h⟩
    exact ⟨tensorDecompositionIso n T,fun i => (hCD _ _).mp (hT i),h⟩
  · rintro ⟨T,hT,h⟩
    exact ⟨(tensorDecompositionIso n).symm T,fun i => (hCD _ _).mpr (hT i),h⟩

 theorem sourceTensorClosure_iff
    (C D : (n : ℕ) → Signature AlgebraicComplex n → Prop)
    (hCD : ∀ n f, C n f ↔ D n f) {n : ℕ} (f : Signature AlgebraicComplex n) :
    SourceTensorClosure C f ↔ Holant.Tractable.SourceTensorClosure D f :=
  or_congr Iff.rfl (tensorClosure_iff C D hCD f)

 theorem arityTwo_iff (F : SignatureFamily AlgebraicComplex) :
    ArityTwoAlternative F ↔ Holant.Tractable.ArityTwoAlternative F := by
  unfold ArityTwoAlternative Holant.Tractable.ArityTwoAlternative
  exact forall_congr' fun f => forall_congr' fun _ =>
    sourceTensorClosure_iff _ _ (fun _ _ => Iff.rfl) _

 theorem matching_iff (F : SignatureFamily AlgebraicComplex) :
    MatchingAlternative F ↔ Holant.Tractable.MatchingAlternative F := by
  unfold MatchingAlternative Holant.Tractable.MatchingAlternative
  apply or_congr
  all_goals
    exact forall_congr' fun f => forall_congr' fun _ =>
      sourceTensorClosure_iff _ _ (fun _ _ => Iff.rfl) _

def eoSignIso : EOSign ≃ Holant.Tractable.EOSign where
  toFun | .positive => .positive | .negative => .negative
  invFun | .positive => .positive | .negative => .negative
  left_inv v := by cases v <;> rfl
  right_inv v := by cases v <;> rfl

def eoClassIso : EOClass ≃ Holant.Tractable.EOClass where
  toFun | .affine => .affine | .product => .product
  invFun | .affine => .affine | .product => .product
  left_inv v := by cases v <;> rfl
  right_inv v := by cases v <;> rfl

 theorem eoClass_iff {n : ℕ} (C : EOClass) (f : Signature AlgebraicComplex n) :
    C.Holds f ↔ (eoClassIso C).Holds f := by
  cases C
  · exact affine_iff f
  · exact product_iff f

 theorem eoTract_iff (F : SignatureFamily AlgebraicComplex) :
    EOTract F ↔ Holant.Tractable.EOTract F := by
  constructor
  · rintro ⟨hf,he,sign,C,hcharge,hpairs⟩
    refine ⟨hf,he,eoSignIso sign,eoClassIso C,?_,?_⟩
    · cases sign <;> exact hcharge
    · intro f h p
      exact (eoClass_iff C _).mp (hpairs f h ((orientedPerfectPairingIso f.1).symm p))
  · rintro ⟨hf,he,sign,C,hcharge,hpairs⟩
    refine ⟨hf,he,eoSignIso.symm sign,eoClassIso.symm C,?_,?_⟩
    · cases sign <;> exact hcharge
    · intro f h p
      have hc := hpairs f h (orientedPerfectPairingIso f.1 p)
      cases C
      · exact (affine_iff _).mpr hc
      · exact (product_iff _).mpr hc

 theorem oneSided_iff (F : SignatureFamily AlgebraicComplex) :
    OneSidedAlternative F ↔ Holant.Tractable.OneSidedAlternative F :=
  and_congr Iff.rfl (eoTract_iff _)

 theorem singleWeight_iff (F : SignatureFamily AlgebraicComplex) :
    SingleWeightAlternative F ↔ Holant.Tractable.SingleWeightAlternative F :=
  and_congr Iff.rfl (and_congr Iff.rfl (eoTract_iff _))

 theorem tractCore_iff (F : SignatureFamily AlgebraicComplex) :
    TractCore F ↔ Holant.Tractable.TractCore F := by
  unfold TractCore Holant.Tractable.TractCore
  exact or_congr (oneSided_iff F) (or_congr (singleWeight_iff F)
    (or_congr (arityTwo_iff F) (or_congr (matching_iff F)
      (or_congr (commonTransformable_iff _ _ (fun f => affine_iff f.2) F)
        (or_congr (commonTransformable_iff _ _ (fun f => product_iff f.2) F)
          (commonTransformable_iff _ _ (fun f => localAffine_iff f.2) F))))))

 theorem tractXCore_iff (F : SignatureFamily AlgebraicComplex) :
    TractXCore F ↔ Holant.Tractable.TractXCore F := by
  unfold TractXCore Holant.Tractable.TractXCore
  exact or_congr (arityTwo_iff F)
    (or_congr (commonTransformable_iff _ _ (fun f => affine_iff f.2) F)
      (or_congr (commonTransformable_iff _ _ (fun f => product_iff f.2) F)
        (commonTransformable_iff _ _ (fun f => localAffine_iff f.2) F)))

/-- Every seven-clause witness is transported in both directions. -/
 theorem tract_iff (F : SignatureFamily AlgebraicComplex) :
    Tract F ↔ Holant.Tractable.Tract F :=
  and_congr Iff.rfl (tractCore_iff _)

 theorem tractX_iff (F : SignatureFamily AlgebraicComplex) :
    TractX F ↔ Holant.Tractable.TractX F :=
  and_congr Iff.rfl (tractXCore_iff _)

end
end Paper2.Paper1Proved
