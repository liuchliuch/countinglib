import Paper2.DegreeCSP.OriginalThreeFaceCharges
import Paper2.DegreeCSP.PartialContextProducts

/-! The signed eight-face cubic normalizer is an actual partial context.
Each positive face uses one source context. Each negative face uses 4k-1
disjoint copies, retaining its hidden variables and the exact scalar. -/
namespace Paper2.DegreeCSP.PartialTernaryCubicContext
open Tractable TensorDecomposition
open scoped BigOperators
open Holant.Tractable.AffinePhase (Word origin)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1400000

variable {n : ℕ}

def faceCopies (k : ℕ) (u : Word 3) : ℕ :=
  if SignedCubeNormalizer.faceSign u=1 then 1 else 4*k-1

private def faceIndex : Word 3≃Fin (Fintype.card (Word 3)) := Fintype.equivFin _

def presentation (p : Word 3→Word n) (f : Signature AlgebraicComplex n) (k : ℕ) :
    Presentation AlgebraicComplex (Fin 7) :=
  PartialUnaryProducts.product (Fintype.card (Word 3))
    (fun i=>OriginalThreeFaceContext.facePresentation p f k (faceIndex.symm i))
    (fun i=>faceCopies k (faceIndex.symm i))

def table (p : Word 3→Word n) (f : Signature AlgebraicComplex n) :
    TernaryBundleGauge.Table := fun x y z=>f (p ![x,y,z])

def scalar (p : Word 3→Word n) (f : Signature AlgebraicComplex n) (k : ℕ) :
    AlgebraicComplex := (f (p (origin 3))^(4*k))^4

def parameter (p : Word 3→Word n) (f : Signature AlgebraicComplex n) :
    AlgebraicComplex := TernaryBundleGauge.cubeRatio (table p f)

/-- A natural representative is the literal top context's occupied degree;
its residue is the signed count of the original triple-character ports. -/
def charge (p : Word 3→Word n) (f : Signature AlgebraicComplex n) (k : ℕ) : ℕ :=
  (OriginalThreeFaceContext.presentation p f k).degree (Sum.inl 6)

theorem uses (p : Word 3→Word n) (f : Signature AlgebraicComplex n) (k : ℕ)
    (F : SignatureFamily AlgebraicComplex)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F) :
    (presentation p f k).Uses F := by
  apply PartialUnaryProducts.product_uses
  intro i
  exact OriginalThreeFaceContext.face_uses p f k F hf h0 h1 hX (faceIndex.symm i)

theorem hidden_divisible (p : Word 3→Word n) (f : Signature AlgebraicComplex n)
    {k : ℕ} (hk : 0<k) :
    PartialUnaryProducts.HiddenDivisible (presentation p f k) k := by
  apply PartialUnaryProducts.product_hidden_divisible_family
  intro i
  exact OriginalThreeFaceContext.face_hidden_divisible p f hk (faceIndex.symm i)

theorem faceCopies_charge {k : ℕ} (hk : 0<k) (u : Word 3) :
    (faceCopies k u : ZMod k)=(SignedCubeNormalizer.faceSign u : ZMod k) := by
  have he : 4*k-1+1=4*k := by omega
  have h := congrArg (fun a : ℕ=>(a : ZMod k)) he
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,
    ZMod.natCast_self,mul_zero] at h
  have hn : ((4*k-1 : ℕ) : ZMod k)= -1 := eq_neg_iff_add_eq_zero.mpr h
  unfold faceCopies SignedCubeNormalizer.faceSign
  split_ifs <;> simp_all

theorem boundary_charge (p : Word 3→Word n) (f : Signature AlgebraicComplex n)
    {k : ℕ} (hk : 0<k) (j : Fin 7) :
    ((presentation p f k).degree (Sum.inl j) : ZMod k)=
      (charge p f k : ZMod k)*(SignedCubeNormalizer.bundleSign j : ZMod k) := by
  rw [presentation,PartialUnaryProducts.product_boundary_degree]
  simp only [Nat.cast_sum,Nat.cast_mul]
  rw [faceIndex.symm.sum_comp (fun u : Word 3=>
    (faceCopies k u : ZMod k)*
      ((OriginalThreeFaceContext.facePresentation p f k u).degree (Sum.inl j) : ZMod k))]
  simp_rw [faceCopies_charge hk]
  have hc (u : Word 3) :
      ((OriginalThreeFaceContext.facePresentation p f k u).degree (Sum.inl j) : ZMod k)=
        OriginalThreeFaceCharges.boundaryCharge (OriginalThreeFaceContext.faceMap p u) k j :=
    (OriginalThreeFaceCharges.boundaryCharge_degree _ f k j).symm
  simp_rw [hc]
  rw [OriginalThreeFaceCharges.boundary_charge_faces hk]
  rw [OriginalThreeFaceCharges.boundaryCharge_degree]
  rfl

theorem scalar_nonzero (p : Word 3→Word n) (f : Signature AlgebraicComplex n)
    (k : ℕ) (ha : ∀ z,f (p z)≠0) : scalar p f k≠0 :=
  pow_ne_zero _ (pow_ne_zero _ (ha (origin 3)))

theorem parameter_nonzero (p : Word 3→Word n) (f : Signature AlgebraicComplex n)
    (ha : ∀ z,f (p z)≠0) : parameter p f≠0 := by
  unfold parameter TernaryBundleGauge.cubeRatio table
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (ha _) (ha _)) (ha _)) (ha _))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (ha _) (ha _)) (ha _)) (ha _))

private def wordEquiv : Word 3≃Bool×(Bool×Bool) where
  toFun x := (x 0,x 1,x 2)
  invFun p := ![p.1,p.2.1,p.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨x,y,z⟩; rfl

private theorem zeroFace_vector (u x : Word 3) :
    OriginalThreeFaceContext.zeroFace u x=![x 0 && u 0,x 1 && u 1,x 2 && u 2] := by
  funext i
  fin_cases i <;> rfl

private theorem inverse_coefficient (p : Word 3→Word n) (f : Signature AlgebraicComplex n)
    {k : ℕ} (hk : 0<k) (ha : ∀ z,f (p z)≠0)
    (hpower : ∀ z,f (p z)^(4*k)=f (p (origin 3))^(4*k)) (z : Word 3) :
    f (p z)^(4*k-1)=f (p (origin 3))^(4*k)/f (p z) := by
  apply (eq_div_iff (ha z)).mpr
  rw [←pow_succ]
  have he : 4*k-1+1=4*k := by omega
  rw [he,hpower z]

private theorem alternating_product (A : TernaryBundleGauge.Table)
    (L : AlgebraicComplex) (ha : ∀ x y z,A x y z≠0) (x : Word 3) :
    (∏ u : Word 3,if SignedCubeNormalizer.faceSign u=1 then
      A (x 0 && u 0) (x 1 && u 1) (x 2 && u 2) else
      L/A (x 0 && u 0) (x 1 && u 1) (x 2 && u 2))=
        L^4*SignedCubeNormalizer.normalize A (x 0) (x 1) (x 2) := by
  rw [←wordEquiv.symm.prod_comp]
  have tail (a b c : Bool) : (![a,b,c] : Word 3) 2=c := rfl
  simp [Fintype.prod_prod_type,wordEquiv,
    SignedCubeNormalizer.faceSign,tail]
  unfold SignedCubeNormalizer.normalize
  field_simp [ha]

/-- The actual eight-face context retains the original cubic coefficient.
Its nonzero scalar accounts for four inverse-power face replacements. -/
theorem value_code (p : Word 3→Word n) (hp : IsAffineMap p)
    (f : Signature AlgebraicComplex n) {k : ℕ} (hk : 2≤k)
    (ha : ∀ z,f (p z)≠0)
    (hpower : ∀ z,f (p z)^(4*k)=f (p (origin 3))^(4*k)) (x : Word 3) :
    (presentation p f k).value (GeneratedCodeSeven.code x)=
      scalar p f k*parameter p f^(bitValue ℕ (x 0)*bitValue ℕ (x 1)*bitValue ℕ (x 2)) := by
  rw [presentation,PartialUnaryProducts.product_value]
  rw [faceIndex.symm.prod_comp (fun u : Word 3=>
    (OriginalThreeFaceContext.facePresentation p f k u).value (GeneratedCodeSeven.code x)^
      faceCopies k u)]
  simp_rw [OriginalThreeFaceContext.face_value_code p hp f hk]
  have hf (u : Word 3) :
      f (p (OriginalThreeFaceContext.zeroFace u x))^(faceCopies k u)=
        if SignedCubeNormalizer.faceSign u=1 then
          f (p (OriginalThreeFaceContext.zeroFace u x)) else
          f (p (origin 3))^(4*k)/f (p (OriginalThreeFaceContext.zeroFace u x)) := by
    unfold faceCopies
    split_ifs
    · exact pow_one _
    · exact inverse_coefficient p f (by omega) ha hpower _
  simp_rw [hf,zeroFace_vector]
  change (∏u : Word 3,if SignedCubeNormalizer.faceSign u=1 then
      table p f (x 0 && u 0) (x 1 && u 1) (x 2 && u 2) else
      f (p (origin 3))^(4*k)/table p f (x 0 && u 0) (x 1 && u 1) (x 2 && u 2))=_
  rw [alternating_product (table p f) (f (p (origin 3))^(4*k))
    (fun a b c=>ha ![a,b,c]) x]
  rw [SignedCubeNormalizer.normalize_eq (table p f) (fun a b c=>ha ![a,b,c])]
  cases hx : x 0 <;> cases hy : x 1 <;> cases hz : x 2
  all_goals simp [scalar,parameter,bitValue]


end
end Paper2.DegreeCSP.PartialTernaryCubicContext
