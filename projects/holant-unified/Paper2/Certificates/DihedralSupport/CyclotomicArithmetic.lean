import Holant.Algebraic.QuadraticField
import Paper2.Tractable.Scalars
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Exact rational-pair arithmetic for the Appendix A.1 coefficient checks.
This is the actual quadratic field with relation ω² = -1 - ω. Its operations
are rational arithmetic, and its semantic map is an injective ring homomorphism
to the manuscript's algebraic-complex field. -/
namespace Paper2.Certificates.DihedralSupport.CyclotomicArithmetic
open Paper2.Tractable

instance cube_no_rational_root : Fact (∀r : ℚ,r^2≠(-1 : ℚ)+(-1)*r) := by
  constructor
  intro r h
  nlinarith [sq_nonneg (2*r+1)]

/-- Computable elements are exactly two rational coefficients `(a,b)`. -/
abbrev Scalar := QuadraticAlgebra ℚ (-1) (-1)

def pair (a b : ℚ) : Scalar := ⟨a,b⟩

def omega : Scalar := pair 0 1

@[simp] theorem pair_re (a b : ℚ) : (pair a b).re=a := rfl
@[simp] theorem pair_im (a b : ℚ) : (pair a b).im=b := rfl

@[simp] theorem pair_eq_pair_iff (a b c d : ℚ) : pair a b=pair c d ↔ a=c ∧ b=d :=
  QuadraticAlgebra.ext_iff

@[simp] theorem pair_eq_zero_iff (a b : ℚ) : pair a b=0 ↔ a=0 ∧ b=0 := by
  exact QuadraticAlgebra.ext_iff

@[simp] theorem pair_add (a b c d : ℚ) : pair a b+pair c d=pair (a+c) (b+d) := rfl
@[simp] theorem pair_neg (a b : ℚ) : -pair a b=pair (-a) (-b) := rfl

theorem pair_mul (a b c d : ℚ) :
    pair a b*pair c d=pair (a*c-b*d) (a*d+b*c-b*d) := by
  ext <;> simp [pair] <;> ring

def norm (z : Scalar) : ℚ := z.re^2-z.re*z.im+z.im^2

theorem norm_eq_quadratic_norm (z : Scalar) : norm z=QuadraticAlgebra.norm z := by
  simp [norm,QuadraticAlgebra.norm_def]
  ring

theorem norm_eq_zero_iff (z : Scalar) : norm z=0 ↔ z=0 := by
  rw [norm_eq_quadratic_norm]
  exact QuadraticAlgebra.norm_eq_zero_iff_eq_zero

/-- The denominator and both coefficients match the source verifier exactly;
the formula also has the field convention `0⁻¹=0`. -/
theorem inverse_pair (a b : ℚ) :
    (pair a b)⁻¹=pair ((a-b)/(a^2-a*b+b^2)) (-b/(a^2-a*b+b^2)) := by
  ext <;> simp [pair,QuadraticAlgebra.inv_def,QuadraticAlgebra.norm_def,
    div_eq_mul_inv] <;> ring

@[simp] theorem omega_poly : omega^2+omega+1=0 := by decide +kernel
@[simp] theorem omega_cube : omega^3=1 := by decide +kernel
@[simp] theorem omega_ne_one : omega≠1 := by decide
@[simp] theorem omega_ne_zero : omega≠0 := by decide

theorem omega_primitive : IsPrimitiveRoot omega 3 := by
  apply IsPrimitiveRoot.mk_of_lt omega (by decide) omega_cube
  intro n hn hn3
  have h : n=1 ∨ n=2 := by omega
  rcases h with rfl | rfl <;> decide +kernel

/-- Frozen Paper1's exact multiplication table and basis presentation. -/
def arithmeticData : Holant.Algebraic.ArithmeticData 2 :=
  Holant.Algebraic.quadraticData (-1) (-1)

noncomputable def fixedField : Holant.Algebraic.FixedField Scalar 2 :=
  Holant.Algebraic.quadraticField (-1) (-1)

def encoding : Computability.Encoding Scalar Bool :=
  Holant.Algebraic.quadraticEncoding (-1) (-1)

@[simp] theorem decode_encoding (z : Scalar) : encoding.decode (encoding.encode z)=some z :=
  encoding.decode_encode z

/-- Any actual root of Φ₃ supplies a faithful semantic interpretation. -/
noncomputable def embed (w : AlgebraicComplex) (hw : w^2+w+1=0) :
    Scalar →+* AlgebraicComplex :=
  (QuadraticAlgebra.lift
    (show {u : AlgebraicComplex // u*u=(-1 : ℚ) • 1+(-1 : ℚ) • u} from
      ⟨w,by simp only [Rat.smul_def]; norm_num; linear_combination hw⟩)).toRingHom

theorem embed_injective (w : AlgebraicComplex) (hw : w^2+w+1=0) :
    Function.Injective (embed w hw) := (embed w hw).injective

@[simp] theorem embed_apply (w : AlgebraicComplex) (hw : w^2+w+1=0) (z : Scalar) :
    embed w hw z=(z.re : AlgebraicComplex)+(z.im : AlgebraicComplex)*w := by
  simp [embed,QuadraticAlgebra.lift,Algebra.smul_def]

@[simp] theorem embed_pair (w : AlgebraicComplex) (hw : w^2+w+1=0) (a b : ℚ) :
    embed w hw (pair a b)=(a : AlgebraicComplex)+(b : AlgebraicComplex)*w := by
  simp

@[simp] theorem embed_omega (w : AlgebraicComplex) (hw : w^2+w+1=0) :
    embed w hw omega=w := by simp [omega]

@[simp] theorem embed_eq_zero_iff (w : AlgebraicComplex) (hw : w^2+w+1=0) (z : Scalar) :
    embed w hw z=0 ↔ z=0 := map_eq_zero_iff (embed w hw) (embed_injective w hw)

theorem embed_eq_iff (w : AlgebraicComplex) (hw : w^2+w+1=0) (z t : Scalar) :
    embed w hw z=embed w hw t ↔ z=t := (embed_injective w hw).eq_iff

@[simp] theorem embed_inv (w : AlgebraicComplex) (hw : w^2+w+1=0) (z : Scalar) :
    embed w hw z⁻¹=(embed w hw z)⁻¹ := map_inv₀ (embed w hw) z

@[simp] theorem embed_div (w : AlgebraicComplex) (hw : w^2+w+1=0) (z t : Scalar) :
    embed w hw (z/t)=embed w hw z/embed w hw t := map_div₀ (embed w hw) z t

def phase (r : Fin 3) : Scalar := omega^r.val

theorem phase_ne_zero (r : Fin 3) : phase r≠0 := pow_ne_zero _ omega_ne_zero

theorem phase_injective : Function.Injective phase := by
  decide +kernel

@[simp] theorem embed_phase (w : AlgebraicComplex) (hw : w^2+w+1=0) (r : Fin 3) :
    embed w hw (phase r)=w^r.val := by
  change embed w hw (omega^r.val)=_
  rw [map_pow,embed_omega]

theorem polynomial_of_primitive (w : AlgebraicComplex) (hw : IsPrimitiveRoot w 3) :
    w^2+w+1=0 := by
  have hf : (w-1)*(w^2+w+1)=0 := by
    calc
      (w-1)*(w^2+w+1)=w^3-1 := by ring
      _ = 0 := by rw [hw.pow_eq_one]; ring
  exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr (hw.ne_one (by decide)))

/-- The factor identity proves exhaustive phase coverage in the semantic field,
so the three exact phase labels do not omit roots after scalar extension. -/
theorem cubic_factorization (w : AlgebraicComplex) (hw : w^2+w+1=0)
    (z : AlgebraicComplex) : (z-1)*(z-w)*(z-w^2)=z^3-1 := by
  have hc : w^3=1 := by linear_combination (w-1)*hw
  linear_combination (-z^2+z)*hw+(z-1)*hc

theorem cube_roots_complete (w : AlgebraicComplex) (hw : w^2+w+1=0)
    (z : AlgebraicComplex) (hz : z^3=1) : ∃r : Fin 3,z=embed w hw (phase r) := by
  have hf : (z-1)*(z-w)*(z-w^2)=0 := by rw [cubic_factorization w hw,hz]; ring
  rcases mul_eq_zero.mp hf with h | h
  · rcases mul_eq_zero.mp h with h | h
    · refine ⟨0,?_⟩
      rw [embed_phase]
      simpa using sub_eq_zero.mp h
    · refine ⟨1,?_⟩
      rw [embed_phase]
      simpa using sub_eq_zero.mp h
  · refine ⟨2,?_⟩
    rw [embed_phase]
    simpa using sub_eq_zero.mp h

/-- Projective equality includes one actual nonzero common scalar. -/
def Proportional {K ι : Type*} [Field K] (v u : ι→K) : Prop :=
  ∃c : K,c≠0 ∧ ∀i,v i=c*u i

/-- Extension to algebraic complex numbers neither merges nor separates exact
projective points. A complex proportionality scalar is recovered from a
nonzero exact pivot, rather than assumed to lie in the quadratic field. -/
theorem proportional_embed_iff {ι : Type*} (w : AlgebraicComplex)
    (hw : w^2+w+1=0) (v u : ι→Scalar) :
    Proportional (fun i=>embed w hw (v i)) (fun i=>embed w hw (u i)) ↔ Proportional v u := by
  classical
  constructor
  · rintro ⟨c,hc,h⟩
    change ∀i,embed w hw (v i)=c*embed w hw (u i) at h
    by_cases hu : u=0
    · have hv (i : ι) : v i=0 := by
        apply (embed_eq_zero_iff w hw _).mp
        simpa [hu] using h i
      exact ⟨1,one_ne_zero,fun i=>by simp [hv i,hu]⟩
    · obtain ⟨i,hi⟩ : ∃i,u i≠0 := by
        by_contra hn
        apply hu
        funext i
        by_contra hi
        exact hn ⟨i,hi⟩
      have hui : embed w hw (u i)≠0 := by
        intro hz
        exact hi ((embed_eq_zero_iff w hw _).mp hz)
      let d := v i/u i
      have hdmap : embed w hw d=c := by
        dsimp only [d]
        rw [map_div₀,h i,mul_div_cancel_right₀ c hui]
      have hd : d≠0 := by
        intro hz
        apply hc
        rw [←hdmap,hz,map_zero]
      refine ⟨d,hd,fun j=>?_⟩
      apply embed_injective w hw
      rw [map_mul,hdmap]
      exact h j
  · rintro ⟨c,hc,h⟩
    refine ⟨embed w hw c,?_,fun i=>?_⟩
    · exact fun hz=>hc ((embed_eq_zero_iff w hw _).mp hz)
    · change embed w hw (v i)=embed w hw c*embed w hw (u i)
      rw [h i,map_mul]

end Paper2.Certificates.DihedralSupport.CyclotomicArithmetic

