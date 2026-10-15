import Paper2.DegreeCSP.OriginalThreeFaceCharges
import Paper2.DegreeCSP.TernaryBundleGauge

/-! Exact weight and phase equations for original coordinate bundles, including
literal fixed and complemented ports. The signed counts are the same integer
charges whose residues are the degrees of the actual context presentations. -/
namespace Paper2.DegreeCSP.SignedBundleGauge
open Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1200000

variable {n : ℕ}

def bit (b : Bool) : ℤ := if b then 1 else 0

def weight (x : Fin n → Bool) : ℤ := ∑ i, bit (x i)

def signedCharge (E : Fin n → MultiCoordinateContext.Expr 7) (j : Fin 7) : ℤ :=
  ∑ i, OriginalThreeFaceCharges.portCharge (E i) j

def originWeight (E : Fin n → MultiCoordinateContext.Expr 7) : ℤ :=
  weight (MultiCoordinateContext.word E (fun _ => false))

private theorem port_weight (e : MultiCoordinateContext.Expr 7) (x : Fin 7 → Bool) :
    bit (MultiCoordinateContext.eval e x) =
      bit (MultiCoordinateContext.eval e (fun _ => false)) +
        ∑ j, OriginalThreeFaceCharges.portCharge e j * bit (x j) := by
  rcases e with b | ⟨j,b⟩
  · simp [OriginalThreeFaceCharges.portCharge, MultiCoordinateContext.eval]
  · cases b
    · have hs : (∑ q : Fin 7,
          OriginalThreeFaceCharges.portCharge (Sum.inr (j,false)) q * bit (x q)) =
          bit (x j) := by
        simp [OriginalThreeFaceCharges.portCharge]
      rw [hs]
      simp [MultiCoordinateContext.eval, bit]
    · have hs : (∑ q : Fin 7,
          OriginalThreeFaceCharges.portCharge (Sum.inr (j,true)) q * bit (x q)) =
          -bit (x j) := by
        simp [OriginalThreeFaceCharges.portCharge]
      rw [hs]
      cases hx : x j <;> simp [MultiCoordinateContext.eval, hx, bit]

/-- Each complemented original coordinate contributes minus its selected bit;
its constant contribution is recorded at the zero word. -/
theorem word_weight (E : Fin n → MultiCoordinateContext.Expr 7) (x : Fin 7 → Bool) :
    weight (MultiCoordinateContext.word E x) =
      originWeight E + ∑ j, signedCharge E j * bit (x j) := by
  unfold weight MultiCoordinateContext.word originWeight
  calc
    _ = ∑ i, (bit (MultiCoordinateContext.eval (E i) (fun _ => false)) +
        ∑ j, OriginalThreeFaceCharges.portCharge (E i) j * bit (x j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact port_weight (E i) x
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      rfl

def bundleWeight (s : Fin 7 → ℤ) (a b c : Bool) : ℤ :=
  (if a then s 0 else 0)+(if b then s 1 else 0)+(if c then s 2 else 0)+
  (if Bool.xor b c then s 3 else 0)+(if Bool.xor a c then s 4 else 0)+
  (if Bool.xor a b then s 5 else 0)+
  (if Bool.xor (Bool.xor a b) c then s 6 else 0)

theorem word_weight_code (E : Fin n → MultiCoordinateContext.Expr 7) (a b c : Bool) :
    weight (MultiCoordinateContext.word E (GeneratedCodeSeven.code ![a,b,c])) =
      originWeight E + bundleWeight (signedCharge E) a b c := by
  rw [word_weight]
  congr 1
  simp [GeneratedCodeSeven.code, bundleWeight, bit, Fin.sum_univ_succ]
  ring

def twist (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (origin : ℤ) (s : Fin 7 → ℤ) : TernaryBundleGauge.Table :=
  fun a b c => A a b c * psi ^ (-(origin + bundleWeight s a b c))

def wordTwist (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (E : Fin n → MultiCoordinateContext.Expr 7) : TernaryBundleGauge.Table :=
  fun a b c => A a b c *
    psi ^ (-weight (MultiCoordinateContext.word E (GeneratedCodeSeven.code ![a,b,c])))

theorem wordTwist_eq (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (E : Fin n → MultiCoordinateContext.Expr 7) :
    wordTwist A psi E = twist A psi (originWeight E) (signedCharge E) := by
  funext a b c
  simp only [wordTwist, twist, word_weight_code]

private theorem cross_zpow (A : BinaryParityGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (w : Bool → Bool → ℤ) :
    BinaryParityGauge.cross (fun a b => A a b * psi ^ w a b) =
      BinaryParityGauge.cross A *
        psi ^ (w false false + w true true - (w false true + w true false)) := by
  rw [zpow_sub₀ hp, zpow_add₀ hp, zpow_add₀ hp]
  simp only [BinaryParityGauge.cross, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem cube_zpow (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (w : Bool → Bool → Bool → ℤ) :
    TernaryBundleGauge.cubeRatio (fun a b c => A a b c * psi ^ w a b c) =
      TernaryBundleGauge.cubeRatio A * psi ^
        ((w true false false + w false true false + w false false true + w true true true) -
          (w false false false + w true true false + w true false true + w false true true)) := by
  rw [zpow_sub₀ hp]
  simp only [zpow_add₀ hp, TernaryBundleGauge.cubeRatio, div_eq_mul_inv, mul_inv_rev]
  ring

theorem cross_face01 (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (origin : ℤ) (s : Fin 7 → ℤ) :
    BinaryParityGauge.cross (TernaryBundleGauge.face01 (twist A psi origin s)) =
      BinaryParityGauge.cross (TernaryBundleGauge.face01 A) * psi ^ (2 * (s 5 + s 6)) := by
  change BinaryParityGauge.cross (fun a b => A a b false *
    psi ^ (-(origin + bundleWeight s a b false))) = _
  rw [cross_zpow _ psi hp]
  congr 2
  simp [bundleWeight]
  ring

theorem cross_face02 (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (origin : ℤ) (s : Fin 7 → ℤ) :
    BinaryParityGauge.cross (TernaryBundleGauge.face02 (twist A psi origin s)) =
      BinaryParityGauge.cross (TernaryBundleGauge.face02 A) * psi ^ (2 * (s 4 + s 6)) := by
  change BinaryParityGauge.cross (fun a c => A a false c *
    psi ^ (-(origin + bundleWeight s a false c))) = _
  rw [cross_zpow _ psi hp]
  congr 2
  simp [bundleWeight]
  ring

theorem cross_face12 (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (origin : ℤ) (s : Fin 7 → ℤ) :
    BinaryParityGauge.cross (TernaryBundleGauge.face12 (twist A psi origin s)) =
      BinaryParityGauge.cross (TernaryBundleGauge.face12 A) * psi ^ (2 * (s 3 + s 6)) := by
  change BinaryParityGauge.cross (fun b c => A false b c *
    psi ^ (-(origin + bundleWeight s false b c))) = _
  rw [cross_zpow _ psi hp]
  congr 2
  simp [bundleWeight]
  ring

private theorem zpow_twice_square (psi : AlgebraicComplex) (s : ℤ) :
    (psi ^ (2*s))^2 = (psi^4)^s := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

theorem squared_cross_face01 (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (origin : ℤ) (s : Fin 7 → ℤ) :
    BinaryParityGauge.cross (TernaryBundleGauge.face01 (twist A psi origin s))^2 =
      BinaryParityGauge.cross (TernaryBundleGauge.face01 A)^2 * (psi^4)^(s 5+s 6) := by
  rw [cross_face01 A psi hp, mul_pow, zpow_twice_square]

theorem squared_cross_face02 (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (origin : ℤ) (s : Fin 7 → ℤ) :
    BinaryParityGauge.cross (TernaryBundleGauge.face02 (twist A psi origin s))^2 =
      BinaryParityGauge.cross (TernaryBundleGauge.face02 A)^2 * (psi^4)^(s 4+s 6) := by
  rw [cross_face02 A psi hp, mul_pow, zpow_twice_square]

theorem squared_cross_face12 (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (origin : ℤ) (s : Fin 7 → ℤ) :
    BinaryParityGauge.cross (TernaryBundleGauge.face12 (twist A psi origin s))^2 =
      BinaryParityGauge.cross (TernaryBundleGauge.face12 A)^2 * (psi^4)^(s 3+s 6) := by
  rw [cross_face12 A psi hp, mul_pow, zpow_twice_square]

theorem cubeRatio_twist (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (origin : ℤ) (s : Fin 7 → ℤ) :
    TernaryBundleGauge.cubeRatio (twist A psi origin s) =
      TernaryBundleGauge.cubeRatio A / (psi^4)^(s 6) := by
  change TernaryBundleGauge.cubeRatio (fun a b c =>
    A a b c * psi ^ (-(origin + bundleWeight s a b c))) = _
  rw [cube_zpow _ psi hp]
  have he :
      ((-(origin+bundleWeight s true false false) + -(origin+bundleWeight s false true false) +
          -(origin+bundleWeight s false false true) + -(origin+bundleWeight s true true true)) -
        (-(origin+bundleWeight s false false false) + -(origin+bundleWeight s true true false) +
          -(origin+bundleWeight s true false true) + -(origin+bundleWeight s false true true))) =
      -(4*s 6) := by simp [bundleWeight]; ring
  rw [he, zpow_neg, zpow_mul, div_eq_mul_inv]
  rfl

theorem cubeRatio_wordTwist (A : TernaryBundleGauge.Table) (psi : AlgebraicComplex)
    (hp : psi ≠ 0) (E : Fin n → MultiCoordinateContext.Expr 7) :
    TernaryBundleGauge.cubeRatio (wordTwist A psi E) =
      TernaryBundleGauge.cubeRatio A / (psi^4)^(signedCharge E 6) := by
  rw [wordTwist_eq, cubeRatio_twist A psi hp]

/-- Integer signed counts and the actual natural boundary degree give the
same power of a k-th root whenever their genuine charges agree. -/
theorem zpow_eq_pow_of_charge {k : ℕ} (theta : AlgebraicComplex)
    (ht : theta ≠ 0) (hcycle : theta^k=1) (s : ℤ) (d : ℕ)
    (hc : (s : ZMod k)=(d : ZMod k)) : theta^s=theta^d := by
  have hd : (k : ℤ) ∣ s-(d : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (d : ℤ) s k).mp (by
      simpa only [Int.cast_natCast] using hc.symm)
  obtain ⟨z,hz⟩ := hd
  have hs : s=(d : ℤ)+(k : ℤ)*z := by omega
  rw [hs,zpow_add₀ ht,zpow_mul]
  simp only [zpow_natCast,hcycle,one_zpow,mul_one]

/-- A source cube constraint with the actual context degree is exactly the
third-coefficient cancellation after the selected original weight twist. -/
theorem cubeRatio_wordTwist_eq_one_of_charge {k : ℕ}
    (A : TernaryBundleGauge.Table) (psi theta : AlgebraicComplex)
    (hp : psi ≠ 0) (hpsi : psi^4=theta) (hcycle : theta^k=1)
    (E : Fin n → MultiCoordinateContext.Expr 7) (d : ℕ)
    (hc : (signedCharge E 6 : ZMod k)=(d : ZMod k))
    (hA : TernaryBundleGauge.cubeRatio A=theta^d) :
    TernaryBundleGauge.cubeRatio (wordTwist A psi E)=1 := by
  have ht : theta ≠ 0 := hpsi ▸ pow_ne_zero 4 hp
  rw [cubeRatio_wordTwist A psi hp,hpsi,
    zpow_eq_pow_of_charge theta ht hcycle _ d hc,hA]
  exact div_self (pow_ne_zero d ht)

/-- The original decoder's signed counts are precisely the residue of the
actual top-context boundary degree. -/
theorem decoder_charge (p : Holant.Tractable.AffinePhase.Word 3 →
    Holant.Tractable.AffinePhase.Word n) {k : ℕ} (hk : 0<k) :
    (signedCharge (AffineThreeFaceDecoder.decoder p) 6 : ZMod k) =
      OriginalThreeFaceCharges.boundaryCharge p k 6 := by
  rw [OriginalThreeFaceCharges.boundaryCharge_eq_sum hk]
  simp only [signedCharge,Int.cast_sum]

theorem cubeRatio_decoder_twist_eq_one {k : ℕ}
    (A : TernaryBundleGauge.Table) (psi theta : AlgebraicComplex)
    (hp : psi ≠ 0) (hpsi : psi^4=theta) (hcycle : theta^k=1)
    (p : Holant.Tractable.AffinePhase.Word 3 → Holant.Tractable.AffinePhase.Word n)
    (f : Signature AlgebraicComplex n) (hk : 0<k)
    (hA : TernaryBundleGauge.cubeRatio A =
      theta^((OriginalThreeFaceContext.presentation p f k).degree (Sum.inl (6 : Fin 7)))) :
    TernaryBundleGauge.cubeRatio
      (wordTwist A psi (AffineThreeFaceDecoder.decoder p))=1 := by
  apply cubeRatio_wordTwist_eq_one_of_charge A psi theta hp hpsi hcycle _ _ _ hA
  rw [decoder_charge p hk]
  exact OriginalThreeFaceCharges.boundaryCharge_degree p f k 6

end
end Paper2.DegreeCSP.SignedBundleGauge
