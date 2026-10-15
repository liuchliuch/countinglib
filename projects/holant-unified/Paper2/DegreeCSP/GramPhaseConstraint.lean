import Paper2.DegreeCSP.BooleanOrthogonality

/-! A pure coefficient constraint for a weighted binary Gram table. BO is
always imposed on the original complex coefficients, including their
actual square. Zero-support cases are retained explicitly. -/
namespace Paper2.DegreeCSP.OriginalBO
noncomputable section

def weightedGram (u t : ℂ) (b c : Bool) : ℂ :=
  (if b then u else 1)*(if c then u else 1)*
    (1+t*(if b=c then 1 else -1))

/-- A nontrivial weighted hidden coordinate has fourth-root phase under
the original-table and square-table block-orthogonality constraints. -/
theorem weighted_gram_phase (u t : ℂ) (hu : u≠0)
    (h : BlockOrthogonal (weightedGram u t))
    (h2 : BlockOrthogonal (fun b c => weightedGram u t b c^2)) :
    t=0 ∨ t^4=1 := by
  by_cases positive : t=1
  · right
    rw [positive]
    norm_num
  by_cases negative : t= -1
  · right
    rw [negative]
    norm_num
  have plus : 1+t≠0 := by
    intro zero
    apply negative
    linear_combination zero
  have minus : 1-t≠0 := by
    intro zero
    apply positive
    linear_combination -zero
  have full : ∀ b c,weightedGram u t b c≠0 := by
    intro b c
    cases b <;> cases c
    · simpa [weightedGram] using plus
    · simpa [weightedGram,sub_eq_add_neg] using mul_ne_zero hu minus
    · simpa [weightedGram,sub_eq_add_neg] using mul_ne_zero hu minus
    · simpa [weightedGram] using mul_ne_zero (mul_ne_zero hu hu) plus
  have cross := binary_squared_cross (weightedGram u t) full h h2
  simp only [weightedGram,ite_true,Bool.false_eq_true,Bool.true_eq_false,ite_false,
    mul_one,one_mul,mul_neg_one] at cross
  have vanishing : (8*u^4)*(t*(1+t^2))=0 := by
    linear_combination cross
  have scale : (8 : ℂ)*u^4≠0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hu)
  have inner : t*(1+t^2)=0 := (mul_eq_zero.mp vanishing).resolve_left scale
  rcases mul_eq_zero.mp inner with zero|square
  · exact Or.inl zero
  · right
    have sq : t^2= -1 := by linear_combination square
    calc
      t^4=(t^2)^2 := by ring
      _=1 := by rw [sq]; norm_num

end
end Paper2.DegreeCSP.OriginalBO

