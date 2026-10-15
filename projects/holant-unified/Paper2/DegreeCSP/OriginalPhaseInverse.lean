import Paper2.DegreeCSP.OriginalContextCommonPhase

/-! A genuine inverse table on original live rows is obtained by repeated
literal source constraints. The exponent 4k-1 gives boundary degree -1
modulo k; no generated inverse, scalar oracle, or free inverse signature is
assumed. The associated 4k-copy table is an actual scaled support indicator.
-/
namespace Paper2.DegreeCSP.OriginalPhaseInverse
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem equal_high_powers {k : ℕ} (theta a b : AlgebraicComplex) (d : ℕ)
    (hcycle : theta^k=1) (ha : a≠0) (hratio : (b/a)^4=theta^d) :
    b^(4*k)=a^(4*k) := by
  have he : (b/a)^(4*k)=1 := by
    rw [pow_mul,hratio,←pow_mul,Nat.mul_comm d k,pow_mul,hcycle,one_pow]
  rw [div_pow] at he
  exact (div_eq_one_iff_eq (pow_ne_zero _ ha)).mp he

/-- The common actual context character controls high powers of every
original signature, independently of its arity or occupied-weight layer. -/
theorem uniform_power (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {k : ℕ} (hk : 0<k)
    (hp0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈F)
    (hp1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (unary : ∀g : Signature AlgebraicComplex 1,Generated F k g→Affine g) :
    ∀{n : ℕ}(f : Signature AlgebraicComplex n),
      (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F→∀x y,
      f x≠0→f y≠0→f y^(4*k)=f x^(4*k) := by
  obtain ⟨theta,hcycle,hratio⟩ :=
    OriginalContextCommonPhase.common_phase F hF hk hp0 hp1 hX unary
  intro n f hf x y hx hy
  exact equal_high_powers theta (f x) (f y) _ hcycle hx (hratio f hf x y hx hy)

def inversePresentation {n : ℕ} (f : Signature AlgebraicComplex n) (k : ℕ) :
    Presentation AlgebraicComplex (Fin n) := Presentation.power f (4*k-1)

theorem inverse_uses {F : SignatureFamily AlgebraicComplex} {n : ℕ}
    (f : Signature AlgebraicComplex n) (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F)
    (k : ℕ) : (inversePresentation f k).Uses F := Presentation.power_uses F f hf _

theorem inverse_boundary_degree {n : ℕ} (f : Signature AlgebraicComplex n)
    (k : ℕ) (i : Fin n) : (inversePresentation f k).degree (Sum.inl i)=4*k-1 :=
  Presentation.power_degree f _ i

theorem inverse_hidden_divisible {n : ℕ} (f : Signature AlgebraicComplex n)
    (k : ℕ) : PartialUnaryProducts.HiddenDivisible (inversePresentation f k) k :=
  fun h=>Fin.elim0 h

theorem inverse_value {n : ℕ} (f : Signature AlgebraicComplex n) {k : ℕ}
    (hk : 0<k) (a x : Fin n→Bool) (hx : f x≠0)
    (hpower : f x^(4*k)=f a^(4*k)) :
    (inversePresentation f k).value x=f a^(4*k)/f x := by
  rw [inversePresentation,Presentation.power_value]
  apply (eq_div_iff hx).mpr
  rw [←pow_succ]
  have he : 4*k-1+1=4*k := by omega
  rw [he,hpower]

/-- The inverse value identity is exact on zero rows too. Total division
returns zero there and the literal positive power has the same value. -/
theorem inverse_value_total {n : ℕ} (f : Signature AlgebraicComplex n) {k : ℕ}
    (hk : 0<k) (a : Fin n→Bool)
    (hpower : ∀x,f x≠0→f x^(4*k)=f a^(4*k)) (x : Fin n→Bool) :
    (inversePresentation f k).value x=f a^(4*k)/f x := by
  by_cases hx:f x≠0
  · exact inverse_value f hk a x hx (hpower x hx)
  · rw [inversePresentation,Presentation.power_value,not_ne_iff.mp hx,
      zero_pow (by omega : 4*k-1≠0),div_zero]

theorem inverse_plus_source_divisible {k : ℕ} (hk : 0<k) : k ∣ (4*k-1)+1 := by
  have he : 4*k-1+1=4*k := by omega
  rw [he]
  exact dvd_mul_left k 4

/-- The source is repeated 4k times. Its scalar is retained in the returned
table instead of claiming free normalization of a support indicator. -/
theorem generated_scaled_indicator {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hk : 0<k) (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex)∈F) (a : Fin n→Bool)
    (hpower : ∀x,f x≠0→f x^(4*k)=f a^(4*k)) :
    Generated F k (fun x=>if f x≠0 then f a^(4*k) else 0) := by
  classical
  have hgen := generated_power F f hf (dvd_mul_left k 4)
  convert hgen using 1
  funext x
  by_cases hx:f x≠0
  · rw [ite_eq_left hx,hpower x hx]
  · rw [ite_eq_right hx,not_ne_iff.mp hx,zero_pow (by omega : 4*k≠0)]

end
end Paper2.DegreeCSP.OriginalPhaseInverse
