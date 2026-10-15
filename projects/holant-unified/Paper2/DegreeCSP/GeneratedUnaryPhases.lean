import Paper2.DegreeCSP.GeneratedGram

/-! A genuine signed binary anchor constrains every genuinely generated
full-support unary. The unary is multiplied into an actual shared boundary,
and the resulting Gram sums quantify its retained phase. -/
namespace Paper2.DegreeCSP
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneratedUnaryPhases

theorem eighth {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (f : Signature AlgebraicComplex 2) (hf : Generated F k f)
    (a u v : ℂ) (ha : a ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ∀ b c,(f ![b,c] : ℂ)=OriginalBO.phaseChart a u v b c)
    (g : Signature AlgebraicComplex 1) (hg : Generated F k g)
    (h0 : g ![false] ≠ 0) (h1 : g ![true] ≠ 0) :
    ((g ![true] : ℂ)/(g ![false] : ℂ))^8 = 1 := by
  let r : ℂ := (g ![true] : ℂ)/(g ![false] : ℂ)
  have h0c : (g ![false] : ℂ) ≠ 0 := by exact_mod_cast h0
  have h1c : (g ![true] : ℂ) ≠ 0 := by exact_mod_cast h1
  have hr : r ≠ 0 := div_ne_zero h1c h0c
  let M : Signature AlgebraicComplex 2 := fun x => f x*g ![x 0]
  have hM : Generated F k M := by
    have hgp := generated_pullback hg (fun _ : Fin 1 => (0 : Fin 2))
    have hh := generated_hadamard hf hgp
    have he : (fun x => f x * g (fun _ : Fin 1 => x 0)) = M := by
      funext x
      congr 2
      funext i
      rw [Fin.eq_zero i]
      rfl
    rw [he] at hh
    exact hh
  have hMc (b c : Bool) : (M ![b,c] : ℂ) =
      OriginalBO.phaseChart (a*(g ![false] : ℂ)) (u*r) v b c := by
    change ((f ![b,c]*g ![b]) : ℂ) = _
    push_cast
    rw [h b c]
    cases b <;> cases c <;>
      simp only [OriginalBO.phaseChart,Bool.false_eq_true,ite_false,ite_true,
        Bool.false_and,Bool.and_false,Bool.and_self,mul_one] <;>
      (try simp only [r]) <;> field_simp [h0c] <;> ring
  have hMu := (GeneratedGram.both_phase_eighth hBO M hM
    (a*(g ![false] : ℂ)) (u*r) v (mul_ne_zero ha h0c) (mul_ne_zero hu hr) hv hMc).1
  have hu8 := (GeneratedGram.both_phase_eighth hBO f hf a u v ha hu hv h).1
  rw [mul_pow,hu8,one_mul] at hMu
  exact hMu

end GeneratedUnaryPhases
end
end Paper2.DegreeCSP
