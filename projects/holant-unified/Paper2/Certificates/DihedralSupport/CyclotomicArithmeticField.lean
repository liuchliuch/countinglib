import Paper2.Certificates.DihedralSupport.CyclotomicArithmetic

/-! The exact rational-pair field embeds faithfully into every
characteristic-zero field containing a root of Φ₃, including ℂ itself. -/
namespace Paper2.Certificates.DihedralSupport.CyclotomicArithmetic
variable {K : Type*} [Field K] [CharZero K]

noncomputable def embedField (w : K) (hw : w^2+w+1=0) : Scalar→+*K :=
  (QuadraticAlgebra.lift
    (show {u : K // u*u=(-1 : ℚ) • 1+(-1 : ℚ) • u} from
      ⟨w,by simp only [Rat.smul_def]; norm_num; linear_combination hw⟩)).toRingHom

theorem embedField_injective (w : K) (hw : w^2+w+1=0) :
    Function.Injective (embedField w hw) := (embedField w hw).injective

theorem embedField_apply (w : K) (hw : w^2+w+1=0) (z : Scalar) :
    embedField w hw z=(z.re : K)+(z.im : K)*w := by
  simp [embedField,QuadraticAlgebra.lift,Algebra.smul_def]

@[simp] theorem embedField_pair (w : K) (hw : w^2+w+1=0) (a b : ℚ) :
    embedField w hw (pair a b)=(a : K)+(b : K)*w := by
  simp [embedField_apply]

@[simp] theorem embedField_omega (w : K) (hw : w^2+w+1=0) :
    embedField w hw omega=w := by simp [omega]

@[simp] theorem embedField_eq_zero_iff (w : K) (hw : w^2+w+1=0) (z : Scalar) :
    embedField w hw z=0 ↔ z=0 := map_eq_zero_iff (embedField w hw) (embedField_injective w hw)

theorem embedField_eq_iff (w : K) (hw : w^2+w+1=0) (z t : Scalar) :
    embedField w hw z=embedField w hw t ↔ z=t := (embedField_injective w hw).eq_iff

@[simp] theorem embedField_inv (w : K) (hw : w^2+w+1=0) (z : Scalar) :
    embedField w hw z⁻¹=(embedField w hw z)⁻¹ := map_inv₀ (embedField w hw) z

@[simp] theorem embedField_div (w : K) (hw : w^2+w+1=0) (z t : Scalar) :
    embedField w hw (z/t)=embedField w hw z/embedField w hw t := map_div₀ (embedField w hw) z t

@[simp] theorem embedField_phase (w : K) (hw : w^2+w+1=0) (r : Fin 3) :
    embedField w hw (phase r)=w^r.val := by
  change embedField w hw (omega^r.val)=_
  rw [map_pow,embedField_omega]

theorem proportional_embedField_iff {ι : Type*} (w : K)
    (hw : w^2+w+1=0) (v u : ι→Scalar) :
    Proportional (fun i=>embedField w hw (v i)) (fun i=>embedField w hw (u i)) ↔
      Proportional v u := by
  classical
  constructor
  · rintro ⟨c,hc,h⟩
    change ∀i,embedField w hw (v i)=c*embedField w hw (u i) at h
    by_cases hu : u=0
    · have hv (i : ι) : v i=0 := by
        apply (embedField_eq_zero_iff w hw _).mp
        simpa [hu] using h i
      exact ⟨1,one_ne_zero,fun i=>by simp [hv i,hu]⟩
    · obtain ⟨i,hi⟩ : ∃i,u i≠0 := by
        by_contra hn
        apply hu
        funext i
        by_contra hi
        exact hn ⟨i,hi⟩
      have hui : embedField w hw (u i)≠0 := by
        intro hz
        exact hi ((embedField_eq_zero_iff w hw _).mp hz)
      let d := v i/u i
      have hdmap : embedField w hw d=c := by
        dsimp only [d]
        rw [map_div₀,h i,mul_div_cancel_right₀ c hui]
      have hd : d≠0 := by
        intro hz
        apply hc
        rw [←hdmap,hz,map_zero]
      refine ⟨d,hd,fun j=>?_⟩
      apply embedField_injective w hw
      rw [map_mul,hdmap]
      exact h j
  · rintro ⟨c,hc,h⟩
    refine ⟨embedField w hw c,?_,fun i=>?_⟩
    · exact fun hz=>hc ((embedField_eq_zero_iff w hw _).mp hz)
    · change embedField w hw (v i)=embedField w hw c*embedField w hw (u i)
      rw [h i,map_mul]

end Paper2.Certificates.DihedralSupport.CyclotomicArithmetic

