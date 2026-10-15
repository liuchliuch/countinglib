import Paper2.DegreeCSP.NoAnchorWeightedSupport
import Paper2.DegreeCSP.GeneratedCompose
import Paper2.DegreeCSP.GeneratedPullback

/-! A genuine weighted parity face constrains every generated nonzero unary
in the no-anchor branch. The finite marginal has actual full-support
coefficients, and productness forces their literal cross-product equality. -/
namespace Paper2.DegreeCSP.NoAnchorWeightedParity
open scoped BigOperators
open Tractable NoAnchorWeightedSupport
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def table (A B : Bool→AlgebraicComplex) (offset : Bool) : Signature AlgebraicComplex 3 :=
  fun x=>if x 2=Bool.xor (Bool.xor (x 0) (x 1)) offset then A (x 0)*B (x 1) else 0

def marginal (A B : Bool→AlgebraicComplex) (offset : Bool) : Signature AlgebraicComplex 2 :=
  fun x=>A (x 0)*B (Bool.xor (Bool.xor (x 0) (x 1)) offset)

theorem marginal_generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (A B : Bool→AlgebraicComplex) (offset : Bool)
    (hf : Generated F k (table A B offset)) : Generated F k (marginal A B offset) := by
  have h := generated_sum_last (generated_pullback hf (![0,2,1] : Fin 3→Fin 3))
  convert h using 1
  funext x
  have hw (b : Bool) : (fun i : Fin 3=>Fin.snoc (α:=fun _=>Bool) x b (![0,2,1] i))=
      ![x 0,b,x 1] := by
    funext i
    fin_cases i <;> rfl
  simp only [hw]
  cases hx0:x 0 <;> cases hx1:x 1 <;> cases offset <;>
    simp [table,marginal,hx0,hx1]

theorem product_fullsupport_cross (f : Signature AlgebraicComplex 2)
    (hp : Product f) (hne : ∀x,f x≠0) :
    f ![false,false]*f ![true,true]=f ![false,true]*f ![true,false] := by
  obtain ⟨c,u,_,_,he⟩ := FullSupportProduct.unary_factorization f hp hne
  simp only [he,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- The one-bit hidden sum has full support; its product-class determinant
forces the squared weights on the hidden free bit to be equal. -/
theorem weight_square {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hno : AllFullSupportProduct F k) (A B : Bool→AlgebraicComplex) (offset : Bool)
    (hA : ∀b,A b≠0) (hB : ∀b,B b≠0)
    (hf : Generated F k (table A B offset)) : B false^2=B true^2 := by
  have hne : ∀x,marginal A B offset x≠0 := fun x=>mul_ne_zero (hA _) (hB _)
  have hp := hno 2 _ (marginal_generated A B offset hf) hne
  have hcross := product_fullsupport_cross _ hp hne
  have hzero : (A false*A true)*(B false^2-B true^2)=0 := by
    cases offset
    · simp [marginal] at hcross
      linear_combination hcross
    · simp [marginal] at hcross
      linear_combination -hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (hA _) (hA _)))

theorem swapped_generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (A B : Bool→AlgebraicComplex) (offset : Bool)
    (hf : Generated F k (table A B offset)) : Generated F k (table B A offset) := by
  convert generated_pullback hf (![1,0,2] : Fin 3→Fin 3) using 1
  funext x
  cases hx0:x 0 <;> cases hx1:x 1 <;> cases hx2:x 2 <;> cases offset <;>
    simp [table,hx0,hx1,hx2,mul_comm]

theorem both_weight_squares {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hno : AllFullSupportProduct F k) (A B : Bool→AlgebraicComplex) (offset : Bool)
    (hA : ∀b,A b≠0) (hB : ∀b,B b≠0)
    (hf : Generated F k (table A B offset)) :
    A false^2=A true^2 ∧ B false^2=B true^2 :=
  ⟨weight_square hno B A offset hB hA (swapped_generated A B offset hf),
    weight_square hno A B offset hA hB hf⟩

theorem unary_dressing_generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (A B : Bool→AlgebraicComplex) (offset : Bool)
    (hf : Generated F k (table A B offset))
    (u : Signature AlgebraicComplex 1) (hu : Generated F k u) :
    Generated F k (table A (fun b=>B b*u ![b]) offset) := by
  convert generated_hadamard hf (generated_pullback hu (fun _ : Fin 1=>(1 : Fin 3))) using 1
  funext x
  have hw : (fun _ : Fin 1=>x 1)=![x 1] := by funext i;rw [Fin.eq_zero i];rfl
  rw [hw]
  unfold table
  split_ifs <;> ring

/-- Any genuinely generated unary with both entries nonzero can be dressed
onto this same parity face. Its squared ratio is then exactly one. -/
theorem generated_unary_square {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hno : AllFullSupportProduct F k) (A B : Bool→AlgebraicComplex) (offset : Bool)
    (hA : ∀b,A b≠0) (hB : ∀b,B b≠0)
    (hf : Generated F k (table A B offset))
    (u : Signature AlgebraicComplex 1) (hu : Generated F k u) (hne : ∀b,u ![b]≠0) :
    u ![false]^2=u ![true]^2 := by
  have hbase := weight_square hno A B offset hA hB hf
  have hwith := weight_square hno A (fun b=>B b*u ![b]) offset hA
    (fun b=>mul_ne_zero (hB b) (hne b)) (unary_dressing_generated A B offset hf u hu)
  have he : B false^2*u ![false]^2=B false^2*u ![true]^2 := by
    simpa only [mul_pow,←hbase] using hwith
  exact mul_left_cancel₀ (pow_ne_zero 2 (hB false)) he

end
end Paper2.DegreeCSP.NoAnchorWeightedParity
