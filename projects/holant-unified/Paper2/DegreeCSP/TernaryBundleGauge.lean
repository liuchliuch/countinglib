import Paper2.DegreeCSP.BinaryParityGauge

/-! Exact original-coefficient phase equations on a monotone rank-three
bundle chart. The cube ratio keeps the signed third difference. The three
zero-base mixed faces retain the separate XOR-bundle multiplicities.
No physical bundle-divisibility or affine-class premise is added here. -/
namespace Paper2.DegreeCSP.TernaryBundleGauge
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 800000

abbrev Table := Bool → Bool → Bool → AlgebraicComplex

/-- Bundle order: x, y, z, y xor z, x xor z, x xor y, x xor y xor z. -/
def bundleWeight (n : Fin 7 → ℕ) (a b c : Bool) : ℕ :=
  (if a then n 0 else 0)+(if b then n 1 else 0)+(if c then n 2 else 0)+
  (if Bool.xor b c then n 3 else 0)+(if Bool.xor a c then n 4 else 0)+
  (if Bool.xor a b then n 5 else 0)+(if Bool.xor (Bool.xor a b) c then n 6 else 0)

def twist (A : Table) (psi : AlgebraicComplex) (n : Fin 7 → ℕ) : Table :=
  fun a b c => A a b c*psi⁻¹^(bundleWeight n a b c)

/-- Odd vertices are in the numerator and even vertices in the denominator,
so this ratio represents the signed third coefficient of the phase. -/
def cubeRatio (A : Table) : AlgebraicComplex :=
  (A true false false*A false true false*A false false true*A true true true)/
  (A false false false*A true true false*A true false true*A false true true)

def face01 (A : Table) : BinaryParityGauge.Table := fun a b => A a b false
def face02 (A : Table) : BinaryParityGauge.Table := fun a c => A a false c
def face12 (A : Table) : BinaryParityGauge.Table := fun b c => A false b c

theorem face01_twist (A : Table) (psi : AlgebraicComplex) (n : Fin 7 → ℕ) :
    face01 (twist A psi n)=
      BinaryParityGauge.twist (face01 A) psi (n 0+n 4) (n 1+n 3) (n 5+n 6) := by
  funext a b
  have hw : bundleWeight n a b false=
      BinaryParityGauge.bundleWeight (n 0+n 4) (n 1+n 3) (n 5+n 6) a b := by
    cases a <;> cases b <;> simp [bundleWeight,BinaryParityGauge.bundleWeight] <;> omega
  simp only [face01,twist,BinaryParityGauge.twist,hw]

theorem face02_twist (A : Table) (psi : AlgebraicComplex) (n : Fin 7 → ℕ) :
    face02 (twist A psi n)=
      BinaryParityGauge.twist (face02 A) psi (n 0+n 5) (n 2+n 3) (n 4+n 6) := by
  funext a c
  have hw : bundleWeight n a false c=
      BinaryParityGauge.bundleWeight (n 0+n 5) (n 2+n 3) (n 4+n 6) a c := by
    cases a <;> cases c <;> simp [bundleWeight,BinaryParityGauge.bundleWeight] <;> omega
  simp only [face02,twist,BinaryParityGauge.twist,hw]

theorem face12_twist (A : Table) (psi : AlgebraicComplex) (n : Fin 7 → ℕ) :
    face12 (twist A psi n)=
      BinaryParityGauge.twist (face12 A) psi (n 1+n 5) (n 2+n 4) (n 3+n 6) := by
  funext b c
  have hw : bundleWeight n false b c=
      BinaryParityGauge.bundleWeight (n 1+n 5) (n 2+n 4) (n 3+n 6) b c := by
    cases b <;> cases c <;> simp [bundleWeight,BinaryParityGauge.bundleWeight] <;> omega
  simp only [face12,twist,BinaryParityGauge.twist,hw]

theorem squared_cross_face01 (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n : Fin 7 → ℕ) :
    BinaryParityGauge.cross (face01 (twist A psi n))^2=
      BinaryParityGauge.cross (face01 A)^2*(psi^4)^(n 5+n 6) := by
  rw [face01_twist]
  exact BinaryParityGauge.squared_cross_twist _ psi hp _ _ _

theorem squared_cross_face02 (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n : Fin 7 → ℕ) :
    BinaryParityGauge.cross (face02 (twist A psi n))^2=
      BinaryParityGauge.cross (face02 A)^2*(psi^4)^(n 4+n 6) := by
  rw [face02_twist]
  exact BinaryParityGauge.squared_cross_twist _ psi hp _ _ _

theorem squared_cross_face12 (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n : Fin 7 → ℕ) :
    BinaryParityGauge.cross (face12 (twist A psi n))^2=
      BinaryParityGauge.cross (face12 A)^2*(psi^4)^(n 3+n 6) := by
  rw [face12_twist]
  exact BinaryParityGauge.squared_cross_twist _ psi hp _ _ _

theorem cubeRatio_twist (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n : Fin 7 → ℕ) :
    cubeRatio (twist A psi n)=cubeRatio A/(psi^4)^(n 6) := by
  have he : (psi^4)^(n 6)=(psi^(n 6))^4 := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm]
  rw [he]
  simp [cubeRatio,twist,bundleWeight,pow_add,inv_pow]
  field_simp [hp]

/-- The third-coefficient test is a literal constraint on the same theta
as the binary mixed tests, rather than a test after an even power. -/
theorem cubeRatio_twist_eq_one_iff (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n : Fin 7 → ℕ) :
    cubeRatio (twist A psi n)=1 ↔ cubeRatio A=(psi^4)^(n 6) := by
  rw [cubeRatio_twist A psi hp]
  exact div_eq_one_iff_eq (pow_ne_zero _ (pow_ne_zero 4 hp))

theorem face01_affine_iff (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n : Fin 7 → ℕ) (ha : ∀ a b c,A a b c≠0)
    (hroot : ∀ a b,
      (face01 (twist A psi n) a b/face01 (twist A psi n) false false)^4=1) :
    Affine (BinaryParityGauge.signature (face01 (twist A psi n))) ↔
      BinaryParityGauge.cross (face01 A)^2*(psi^4)^(n 5+n 6)=1 := by
  have hn (a b : Bool) : face01 (twist A psi n) a b≠0 :=
    mul_ne_zero (ha a b false) (pow_ne_zero _ (inv_ne_zero hp))
  rw [BinaryParityGauge.affine_iff_squared_cross _ hn hroot,squared_cross_face01 A psi hp]

theorem face02_affine_iff (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n : Fin 7 → ℕ) (ha : ∀ a b c,A a b c≠0)
    (hroot : ∀ a c,
      (face02 (twist A psi n) a c/face02 (twist A psi n) false false)^4=1) :
    Affine (BinaryParityGauge.signature (face02 (twist A psi n))) ↔
      BinaryParityGauge.cross (face02 A)^2*(psi^4)^(n 4+n 6)=1 := by
  have hn (a c : Bool) : face02 (twist A psi n) a c≠0 :=
    mul_ne_zero (ha a false c) (pow_ne_zero _ (inv_ne_zero hp))
  rw [BinaryParityGauge.affine_iff_squared_cross _ hn hroot,squared_cross_face02 A psi hp]

theorem face12_affine_iff (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n : Fin 7 → ℕ) (ha : ∀ a b c,A a b c≠0)
    (hroot : ∀ b c,
      (face12 (twist A psi n) b c/face12 (twist A psi n) false false)^4=1) :
    Affine (BinaryParityGauge.signature (face12 (twist A psi n))) ↔
      BinaryParityGauge.cross (face12 A)^2*(psi^4)^(n 3+n 6)=1 := by
  have hn (b c : Bool) : face12 (twist A psi n) b c≠0 :=
    mul_ne_zero (ha false b c) (pow_ne_zero _ (inv_ne_zero hp))
  rw [BinaryParityGauge.affine_iff_squared_cross _ hn hroot,squared_cross_face12 A psi hp]


end
end Paper2.DegreeCSP.TernaryBundleGauge
