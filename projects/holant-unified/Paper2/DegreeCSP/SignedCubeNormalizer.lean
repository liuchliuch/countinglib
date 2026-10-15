import Paper2.DegreeCSP.TernaryBundleGauge

/-! Exact coefficient identities for the signed eight-face cube normalizer.
The incidence calculation records the seven nonconstant bundle charges.
These identities impose no generation or degree-divisibility premise. -/
namespace Paper2.DegreeCSP.SignedCubeNormalizer
open Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1000000

abbrev Table := TernaryBundleGauge.Table

/-- The alternating product of the eight coordinate-zero faces. -/
def normalize (A : Table) (x y z : Bool) : AlgebraicComplex :=
  (A x y z*A x false false*A false y false*A false false z)/
    (A x y false*A x false z*A false y z*A false false false)

theorem normalize_eq (A : Table) (ha : ∀ x y z,A x y z≠0)
    (x y z : Bool) :
    normalize A x y z=
      if x && y && z then TernaryBundleGauge.cubeRatio A else 1 := by
  cases x <;> cases y <;> cases z
  all_goals simp [normalize,TernaryBundleGauge.cubeRatio,ha]
  all_goals field_simp [ha]

theorem normalize_nonzero (A : Table) (ha : ∀ x y z,A x y z≠0)
    (x y z : Bool) : normalize A x y z≠0 :=
  div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (ha x y z) (ha x false false))
      (ha false y false)) (ha false false z))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (ha x y false) (ha x false z))
      (ha false y z)) (ha false false false))

theorem normalize_eq_power (A : Table) (ha : ∀ x y z,A x y z≠0)
    (x y z : Bool) :
    normalize A x y z=
      TernaryBundleGauge.cubeRatio A^(if x && y && z then 1 else 0) := by
  rw [normalize_eq A ha]
  cases h : x && y && z <;> simp

/-- The three rank-two zero faces and four unary/constant corrections. -/
def faceCorrection (A : Table) (x y z : Bool) : AlgebraicComplex :=
  (A x false false*A false y false*A false false z)/
    (A x y false*A x false z*A false y z*A false false false)

theorem normalize_factorization (A : Table) (x y z : Bool) :
    normalize A x y z=A x y z*faceCorrection A x y z := by
  simp only [normalize,faceCorrection,mul_div_assoc]
  ring

/-- The seven nonzero Boolean linear forms in the source bundle order. -/
def code (x y z : Bool) : Fin 7 → Bool :=
  ![x,y,z,Bool.xor y z,Bool.xor x z,Bool.xor x y,
    Bool.xor (Bool.xor x y) z]

def bundleSign : Fin 7 → ℤ := ![1,1,1,-1,-1,-1,1]

def sevenForm (v : AlgebraicComplex) (x y z : Bool) : AlgebraicComplex :=
  ∏ i : Fin 7,(if code x y z i then v else 1)^bundleSign i

/-- Its charge is zero on the seven proper cube corners and four on 111. -/
theorem sevenForm_eq (v : AlgebraicComplex) (hv : v≠0) (x y z : Bool) :
    sevenForm v x y z=if x && y && z then v^4 else 1 := by
  cases x <;> cases y <;> cases z
  all_goals simp [sevenForm,code,bundleSign,Fin.prod_univ_succ]
  all_goals field_simp [hv]

theorem sevenForm_eq_power (v : AlgebraicComplex) (hv : v≠0) (x y z : Bool) :
    sevenForm v x y z=(v^4)^(if x && y && z then 1 else 0) := by
  rw [sevenForm_eq v hv]
  cases h : x && y && z <;> simp

def quadraticCorner (R : AlgebraicComplex) (x y : Bool) : AlgebraicComplex :=
  if x && y then R else 1

/-- Substitution of y xor z into a rank-two mixed phase changes only the
cubic corner; the multiplier there is the inverse square of its phase. -/
theorem quadratic_xor_quotient (R : AlgebraicComplex) (hR : R≠0)
    (x y z : Bool) :
    quadraticCorner R x (Bool.xor y z)/
      (quadraticCorner R x y*quadraticCorner R x z)=
      if x && y && z then (R^2)⁻¹ else 1 := by
  cases x <;> cases y <;> cases z
  all_goals simp [quadraticCorner,pow_two,hR]

theorem quadratic_xor_quotient_zpow (R : AlgebraicComplex) (hR : R≠0)
    (x y z : Bool) :
    quadraticCorner R x (Bool.xor y z)/
      (quadraticCorner R x y*quadraticCorner R x z)=
      (R^(-2 : ℤ))^(if x && y && z then 1 else 0) := by
  rw [quadratic_xor_quotient R hR]
  cases h : x && y && z <;> simp [zpow_neg,zpow_ofNat]

abbrev Mask := Fin 3 → Bool

def intersection (s t : Mask) : Mask := fun i => s i && t i

/-- The alternating cube sign is positive on odd-cardinality faces. -/
def faceSign (t : Mask) : ℤ :=
  if Bool.xor (Bool.xor (t 0) (t 1)) (t 2) then 1 else -1

def signedIncidence (s t : Mask) : ℤ :=
  ∑ u : Mask,if intersection s u=t then faceSign u else 0

def topMask : Mask := ![true,true,true]

def bundleMask : Fin 7 → Mask :=
  ![![true,false,false],![false,true,false],![false,false,true],
    ![false,true,true],![true,false,true],![true,true,false],![true,true,true]]

private def maskEquiv : Mask ≃ Bool × (Bool × Bool) where
  toFun x := (x 0,x 1,x 2)
  invFun p := ![p.1,p.2.1,p.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl

private theorem mask_eta (x : Mask) : x=![x 0,x 1,x 2] := by
  funext i; fin_cases i <;> rfl

/-- Every proper source form cancels. Only the full three-bit form keeps
the signed target-face incidence, including the constant face. -/
theorem signedIncidence_eq (s t : Mask) :
    signedIncidence s t=if s=topMask then faceSign t else 0 := by
  unfold signedIncidence
  rw [←maskEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,maskEquiv]
  rw [mask_eta s,mask_eta t]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals cases k0 : t 0 <;> cases k1 : t 1 <;> cases k2 : t 2
  all_goals norm_num [intersection,faceSign,topMask,funext_iff,Fin.forall_fin_succ]

theorem signedIncidence_bundle (s : Mask) (i : Fin 7) :
    signedIncidence s (bundleMask i)=
      if s=topMask then bundleSign i else 0 := by
  rw [signedIncidence_eq]
  have hs : faceSign (bundleMask i)=bundleSign i := by
    fin_cases i <;> rfl
  rw [hs]

theorem seven_signed_charge (x y z : Bool) :
    (∑ i : Fin 7,if code x y z i then bundleSign i else 0)=
      if x && y && z then 4 else 0 := by
  cases x <;> cases y <;> cases z
  all_goals norm_num [code,bundleSign,Fin.sum_univ_succ]


end
end Paper2.DegreeCSP.SignedCubeNormalizer
