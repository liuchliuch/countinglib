import Paper2.RelativeEO.ARSMatching
import Paper2.RelativeEO.WeightedComplementaryNormalization

/-! The ordered pair-support quaternary and its genuine matching factorization.
No compressed restriction is asserted to be an available signature. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Paper2.RelativeEO
open Paper2.Tractable
open scoped BigOperators

noncomputable def pairTable (g : Signature AlgebraicComplex 2) : Signature AlgebraicComplex 4 :=
  fun x => if x 1 = !(x 0) ∧ x 3 = !(x 2) then g (binWord (x 0) (x 2)) else 0

def canonicalPairing : OrientedPerfectPairing 4 where
  count := 2
  ports := {
    toFun := fun p => Fin.cases (if p.2 then 1 else 0) (fun _ => if p.2 then 3 else 2) p.1
    invFun := fun i => Fin.cases (0,false) (Fin.cases (0,true) (Fin.cases (1,false) (fun _ => (1,true)))) i
    left_inv := by rintro ⟨j,b⟩; fin_cases j <;> cases b <;> rfl
    right_inv := by intro i; fin_cases i <;> rfl }

theorem IsProduct_reindex {n : ℕ} {f : Signature AlgebraicComplex n}
    (h : WeightedMatching.IsProduct f) (e : Equiv.Perm (Fin n)) :
    WeightedMatching.IsProduct (Tensor.reindex e f) := by
  obtain ⟨P,p,q,c,hn,hf⟩ := h
  refine ⟨⟨P.count,P.ports.trans e⟩,p,q,c,hn,?_⟩
  rw [hf]
  rfl

/-- A genuine rank-one compressed table is a disjoint matching tensor. -/
theorem pairTable_isProduct (g : Signature AlgebraicComplex 2)
    (hfull : ∀ x, g x ≠ 0)
    (hdet : g (binWord false false) * g (binWord true true) =
      g (binWord false true) * g (binWord true false)) :
    WeightedMatching.IsProduct (pairTable g) := by
  let a := g (binWord false false)
  let b := g (binWord false true)
  let c := g (binWord true false)
  let d := g (binWord true true)
  have ha : a ≠ 0 := hfull _
  have hb : b ≠ 0 := hfull _
  have hc : c ≠ 0 := hfull _
  have hd : d = c * (b/a) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff ha).mpr
    change d * a = c * b
    dsimp [a,b,c,d]
    linear_combination hdet
  refine ⟨canonicalPairing,(fun j => Fin.cases a (fun _ => 1) j),
    (fun j => Fin.cases c (fun _ => b/a) j),1,?_,?_⟩
  · change (1 : AlgebraicComplex) * (∏ j : Fin 2, Fin.cases a (fun _ => 1) j * Fin.cases c (fun _ => b/a) j) ≠ 0
    rw [Fin.prod_univ_two]
    change (1 : AlgebraicComplex) * (a*c*(1*(b/a))) ≠ 0
    simpa only [one_mul] using mul_ne_zero (mul_ne_zero ha hc) (div_ne_zero hb ha)
  · funext x
    change pairTable g x = (1 : AlgebraicComplex) * (∏ j : Fin 2,
      WeightedMatching.binary (Fin.cases a (fun _ => 1) j) (Fin.cases c (fun _ => b/a) j)
      (x (canonicalPairing.ports (j,false))) (x (canonicalPairing.ports (j,true))))
    rw [Fin.prod_univ_two,one_mul]
    change pairTable g x = WeightedMatching.binary a c (x 0) (x 1) *
      WeightedMatching.binary 1 (b/a) (x 2) (x 3)
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp only [pairTable,WeightedMatching.binary,h0,h1,h2,h3,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,Bool.true_eq_false,and_self,ite_true,ite_false,
        false_and,and_false,one_mul,mul_one,mul_zero,zero_mul]
    · rfl
    · exact (mul_div_cancel₀ b ha).symm
    · rfl
    · exact hd

end Paper2.RelativeEO
