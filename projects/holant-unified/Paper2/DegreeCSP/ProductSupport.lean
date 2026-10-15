import Paper2.DegreeCSP.BooleanSupport
import Paper2.Tractable.Product

/-! Literal unary, equality and disequality factors have discriminator-closed
supports. This remains true under all repeated factors, nonzero scales and
inconsistent products, so a product support indicator retains the actual
support operation used in the degree-CSP classification. -/
namespace Paper2.DegreeCSP.ProductSupport
open Tractable BooleanStructure
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {n : ℕ}

theorem factor (p : ProductFactor n) : Preserves discriminator {x|p.eval x≠0} := by
  intro x hx y hy z hz
  cases p with
  | unary j u hu=>
    change u (x j) ≠ 0 at hx
    change u (z j) ≠ 0 at hz
    change u (discriminator (x j,y j,z j)) ≠ 0
    by_cases h:x j=y j
    · simpa only [discriminator,h,ite_true] using hz
    · simpa only [discriminator,h,ite_false] using hx
  | equality i j=>
    change (Signature.equality (x i) (x j) : AlgebraicComplex) ≠ 0 at hx
    change (Signature.equality (y i) (y j) : AlgebraicComplex) ≠ 0 at hy
    change (Signature.equality (z i) (z j) : AlgebraicComplex) ≠ 0 at hz
    change (Signature.equality (discriminator (x i,y i,z i))
      (discriminator (x j,y j,z j)) : AlgebraicComplex) ≠ 0
    cases hxi : x i <;> cases hxj : x j <;> cases hyi : y i <;>
      cases hyj : y j <;> cases hzi : z i <;> cases hzj : z j <;>
      simp_all [Signature.equality,discriminator]
  | disequality i j=>
    change (Signature.disequality (x i) (x j) : AlgebraicComplex) ≠ 0 at hx
    change (Signature.disequality (y i) (y j) : AlgebraicComplex) ≠ 0 at hy
    change (Signature.disequality (z i) (z j) : AlgebraicComplex) ≠ 0 at hz
    change (Signature.disequality (discriminator (x i,y i,z i))
      (discriminator (x j,y j,z j)) : AlgebraicComplex) ≠ 0
    cases hxi : x i <;> cases hxj : x j <;> cases hyi : y i <;>
      cases hyj : y j <;> cases hzi : z i <;> cases hzj : z j <;>
      simp_all [Signature.disequality,discriminator]

theorem formula (c : AlgebraicComplex) (ps : List (ProductFactor n)) :
    Preserves discriminator {x|productFormula c ps x≠0} := by
  induction ps with
  | nil=>
    intro x hx y hy z hz
    exact hx
  | cons p ps ih=>
    have he (x : Fin n→Bool) : productFormula c (p::ps) x=p.eval x*productFormula c ps x := by
      simp only [productFormula,List.map_cons,List.prod_cons]
      ring
    intro x hx y hy z hz
    change productFormula c (p::ps) x ≠ 0 at hx
    change productFormula c (p::ps) y ≠ 0 at hy
    change productFormula c (p::ps) z ≠ 0 at hz
    change productFormula c (p::ps) (fun i => discriminator (x i,y i,z i)) ≠ 0
    rw [he] at hx hy hz ⊢
    exact mul_ne_zero (factor p x (mul_ne_zero_iff.mp hx).1 y (mul_ne_zero_iff.mp hy).1
      z (mul_ne_zero_iff.mp hz).1)
      (ih x (mul_ne_zero_iff.mp hx).2 y (mul_ne_zero_iff.mp hy).2
        z (mul_ne_zero_iff.mp hz).2)

theorem discriminator (f : Signature AlgebraicComplex n) (hf : Product f) :
    Preserves BooleanStructure.discriminator {x|f x≠0} := by
  rcases hf with rfl|⟨c,hc,ps,rfl⟩
  · intro x hx
    exact False.elim (hx rfl)
  · exact formula c ps

theorem indicator_discriminator (R : Set (Fin n→Bool)) (hp : Product (indicator R)) :
    Preserves BooleanStructure.discriminator R := by
  have he : {x|indicator R x≠0}=R := by
    ext x
    exact indicator_ne_zero R x
  simpa only [he] using discriminator (indicator R) hp

end
end Paper2.DegreeCSP.ProductSupport

