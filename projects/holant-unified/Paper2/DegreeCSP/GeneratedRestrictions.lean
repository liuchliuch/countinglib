import Paper2.DegreeCSP.GeneratedPins

/-! Arbitrary selected faces come from actual pin constraints and hidden
assignment sums. Free coordinates may be repeated or unused; fixed positions
retain their exact prescribed Boolean value. -/
namespace Paper2.DegreeCSP
open Tractable TensorDecomposition
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem generated_pin_suffix {F : SignatureFamily AlgebraicComplex} {k m n : ℕ}
    {f : Signature AlgebraicComplex (m+n)} (hf : Generated F k f)
    (hpin0 : Generated F k (literalPin false)) (hpin1 : Generated F k (literalPin true))
    (a : Fin n→Bool) :
    Generated F k (fun x : Fin m→Bool=>f (Fin.append x a)) := by
  induction n with
  | zero =>
    convert hf using 1
    funext x
    congr 1
    simpa only [Function.comp_def,Fin.cast_eq_self] using Fin.append_right_nil x a rfl
  | succ n ih =>
    let b := a (Fin.last n)
    have hb : Generated F k (literalPin b) := by
      cases he : b
      · exact hpin0
      · exact hpin1
    let g : Signature AlgebraicComplex (m+n) := fun x=>f (Fin.snoc x b)
    have hg : Generated F k g := generated_pin_last hf b hb
    have h := ih hg (Fin.init a)
    convert h using 1
    funext x
    change f (Fin.append x a)=f (Fin.snoc (Fin.append x (Fin.init a)) b)
    rw [←Fin.append_snoc]
    congr 1
    congr 1
    exact (Fin.snoc_init_self a).symm

/-- A partial boundary map is implemented by keeping its free addresses,
appending all fixed positions and restricting that actual suffix. -/
theorem generated_restrict {F : SignatureFamily AlgebraicComplex} {k n m : ℕ}
    {f : Signature AlgebraicComplex n} (hf : Generated F k f)
    (hpin0 : Generated F k (literalPin false)) (hpin1 : Generated F k (literalPin true))
    (r : Fin n→Option (Fin m)) (a : Fin n→Bool) :
    Generated F k (fun x : Fin m→Bool=>f (fun i=>
      match r i with
      | some j => x j
      | none => a i)) := by
  let route : Fin n→Fin (m+n) := fun i=>
    match r i with
    | some j => j.castAdd n
    | none => Fin.natAdd m i
  have h := generated_pin_suffix (generated_pullback hf route) hpin0 hpin1 a
  convert h using 1
  funext x
  congr 1
  funext i
  cases hr : r i <;> simp [route,hr]

/-- Contracting a whole suffix is an actual succession of hidden-variable
sums, retaining precisely the literal finite assignment sum. -/
theorem generated_sum_suffix {F : SignatureFamily AlgebraicComplex} {k m n : ℕ}
    {f : Signature AlgebraicComplex (m+n)} (hf : Generated F k f) :
    Generated F k (fun x : Fin m→Bool=>∑ y : Fin n→Bool,f (Fin.append x y)) := by
  induction n with
  | zero =>
    convert hf using 1
    funext x
    rw [Fintype.sum_unique]
    congr 1
    exact Fin.append_right_nil x _ rfl
  | succ n ih =>
    let g : Signature AlgebraicComplex (m+n) := fun z=>∑ b : Bool,f (Fin.snoc z b)
    have hg : Generated F k g := generated_sum_last hf
    have h := ih hg
    convert h using 1
    funext x
    let e := Fin.snocEquiv (fun _ : Fin (n+1)=>Bool)
    rw [←e.sum_comp,Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro b _
    change f (Fin.append x (Fin.snoc y b))=f (Fin.snoc (Fin.append x y) b)
    rw [Fin.append_snoc]

end
end Paper2.DegreeCSP
