import Paper2.DegreeCSP.BooleanQuadratic
import Paper2.DegreeCSP.BooleanOrthogonality

/-! An odd Boolean sign cube has a literal two-copy Gram table whose
first-coordinate rows fail original block orthogonality. The obstruction
uses overlapping full and singleton row supports of the actual coefficients. -/
namespace Paper2.DegreeCSP.BadCubeGram
open scoped BigOperators
open OriginalBO
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def sign (p : ZMod 2) : ℂ := if p=0 then 1 else -1

theorem sign_nonzero (p : ZMod 2) : sign p≠0 := by
  unfold sign
  split_ifs <;> norm_num

theorem sign_add (p q : ZMod 2) : sign (p+q)=sign p*sign q := by
  fin_cases p <;> fin_cases q <;> norm_num [sign,show (2 : ZMod 2)=0 from rfl]
  all_goals rfl

theorem sign_product (p q : ZMod 2) : sign p*sign q=if p=q then 1 else -1 := by
  fin_cases p <;> fin_cases q <;> norm_num [sign,show (2 : ZMod 2)=0 from rfl]

def derivative (P : (Fin 3 → Bool) → ZMod 2) (a b : Bool) : ZMod 2 :=
  P ![a,b,false]+P ![a,b,true]

def gram (P : (Fin 3 → Bool) → ZMod 2) : Holant.Signature ℂ 4 := fun x =>
  ∑ z : Bool,sign (P ![x 0,x 1,z])*sign (P ![x 2,x 3,z])

theorem sign_translate (p q : ZMod 2) : sign q=sign p*sign (p+q) := by
  fin_cases p <;> fin_cases q <;> norm_num [sign,show (2 : ZMod 2)=0 from rfl]
  all_goals rfl

theorem sign_eq_power (p : ZMod 2) : sign p=(-1 : ℂ)^p.val := by
  fin_cases p <;> norm_num [sign,show (1 : ZMod 2).val=1 from rfl]

theorem gram_value (P : (Fin 3 → Bool) → ZMod 2) (a b c d : Bool) :
    gram P ![a,b,c,d]=
      (if derivative P a b=derivative P c d then (2 : ℂ) else 0)*
        sign (P ![a,b,false])*sign (P ![c,d,false]) := by
  simp only [gram,Fintype.sum_bool]
  change sign (P ![a,b,true])*sign (P ![c,d,true])+
    sign (P ![a,b,false])*sign (P ![c,d,false])=_
  rw [sign_translate (P ![a,b,false]) (P ![a,b,true]),
    sign_translate (P ![c,d,false]) (P ![c,d,true])]
  change (sign (P ![a,b,false])*sign (derivative P a b))*
    (sign (P ![c,d,false])*sign (derivative P c d))+
    sign (P ![a,b,false])*sign (P ![c,d,false])=_
  have product := sign_product (derivative P a b) (derivative P c d)
  calc
    _=sign (P ![a,b,false])*sign (P ![c,d,false])*
      (sign (derivative P a b)*sign (derivative P c d)+1) := by ring
    _= _ := by rw [product]; split_ifs <;> ring

theorem gram_nonzero_iff (P : (Fin 3 → Bool) → ZMod 2) (a b c d : Bool) :
    gram P ![a,b,c,d]≠0 ↔ derivative P a b=derivative P c d := by
  rw [gram_value]
  by_cases equal : derivative P a b=derivative P c d
  · simp only [equal,ite_true,iff_true]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (sign_nonzero _)) (sign_nonzero _)
  · simp [equal]

theorem odd_four_pattern (A B C D : ZMod 2) (odd : A+B+C+D=1) :
    (A=B ∧ ((C=A ∧ D≠A) ∨ (D=A ∧ C≠A))) ∨
      (C=D ∧ ((A=C ∧ B≠C) ∨ (B=C ∧ A≠C))) := by
  fin_cases A <;> fin_cases B <;> fin_cases C <;> fin_cases D <;> norm_num at * <;>
    simp_all [show (2 : ZMod 2)=0 from rfl,show (4 : ZMod 2)=0 from rfl]

theorem odd_derivative_pattern (q : Bool → Bool → ZMod 2)
    (odd : q false false+q true false+q false true+q true true=1) :
    ∃ b a,q false b=q true b ∧ q a (!b)=q false b ∧ q (!a) (!b)≠q false b := by
  rcases odd_four_pattern (q false false) (q true false) (q false true) (q true true) odd with
    ⟨constant,⟨first,second⟩|⟨first,second⟩⟩|
    ⟨constant,⟨first,second⟩|⟨first,second⟩⟩
  · exact ⟨false,false,constant,first,second⟩
  · exact ⟨false,true,constant,first,second⟩
  · exact ⟨true,false,constant,first,second⟩
  · exact ⟨true,true,constant,first,second⟩

/-- A full row and a supported singleton row overlap, so they can be
neither magnitude-proportional nor disjoint. -/
theorem not_bo_of_full_singleton {X : Type} (G : X → Bool → ℂ) (x y : X) (a : Bool)
    (full : ∀ b,G x b≠0) (live : G y a≠0) (zero : G y (!a)=0) :
    ¬BlockOrthogonal G := by
  intro orthogonal
  have hx : G x≠0 := fun hz => full a (congrFun hz a)
  have hy : G y≠0 := fun hz => live (congrFun hz a)
  rcases orthogonal.1 x y hx hy with proportional|disjoint
  · obtain ⟨c,positive,equation⟩ := proportional
    have impossible := equation (!a)
    rw [zero,norm_zero,mul_zero] at impossible
    exact norm_ne_zero_iff.mpr (full (!a)) impossible
  · exact Set.disjoint_left.mp disjoint (full a) live

/-- The genuine two-copy Gram of an odd three-bit sign table fails BO on
the actual first-coordinate flattening. -/
theorem odd_derivative_not_bo (P : (Fin 3 → Bool) → ZMod 2)
    (odd : derivative P false false+derivative P true false+
      derivative P false true+derivative P true true=1) :
    ¬BlockOrthogonal (fun (row : Fin 3 → Bool) (a : Bool) => gram P ![a,row 0,row 1,row 2]) := by
  obtain ⟨b,a,constant,matching,opposite⟩ := odd_derivative_pattern (derivative P) odd
  apply not_bo_of_full_singleton _ (![b,false,b]) (![!b,false,b]) a
  · intro v
    apply (gram_nonzero_iff P v b false b).mpr
    cases v
    · rfl
    · exact constant.symm
  · exact (gram_nonzero_iff P a (!b) false b).mpr matching
  · exact not_ne_iff.mp (fun live => opposite ((gram_nonzero_iff P (!a) (!b) false b).mp live))

def wordEquiv : (Fin 3 → Bool) ≃ Bool × (Bool × Bool) where
  toFun x := (x 0,x 1,x 2)
  invFun p := ![p.1,p.2.1,p.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl

@[simp] theorem wordEquiv_symm_apply (p : Bool × (Bool × Bool)) :
    wordEquiv.symm p=![p.1,p.2.1,p.2.2] := rfl

theorem derivative_sum (P : (Fin 3 → Bool) → ZMod 2) :
    derivative P false false+derivative P true false+
      derivative P false true+derivative P true true=∑ x,P x := by
  rw [←wordEquiv.symm.sum_comp P]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,wordEquiv_symm_apply,derivative]
  abel

/-- Eight actual sign exponents of odd parity give a BO obstruction. -/
theorem odd_table_not_bo (P : (Fin 3 → Bool) → ZMod 2) (odd : (∑ x,P x)=1) :
    ¬BlockOrthogonal (fun (row : Fin 3 → Bool) (a : Bool) => gram P ![a,row 0,row 1,row 2]) := by
  apply odd_derivative_not_bo P
  rw [derivative_sum,odd]

def face {n : ℕ} (P : (Fin n → Bool) → ZMod 2) (z : Fin n → Bool)
    (i j k : Fin n) : (Fin 3 → Bool) → ZMod 2 := fun x =>
  P (Holant.Tractable.AffinePhase.xor
    (Holant.Tractable.AffinePhase.xor
      (Holant.Tractable.AffinePhase.xor z
        (if x 0 then Holant.Tractable.AffinePhase.basis i else Holant.Tractable.AffinePhase.origin n))
      (if x 1 then Holant.Tractable.AffinePhase.basis j else Holant.Tractable.AffinePhase.origin n))
    (if x 2 then Holant.Tractable.AffinePhase.basis k else Holant.Tractable.AffinePhase.origin n))

theorem face_sum {n : ℕ} (P : (Fin n → Bool) → ZMod 2) (z : Fin n → Bool)
    (i j k : Fin n) :
    (∑ x,face P z i j k x)=BooleanQuadratic.cubeParity P z i j k := by
  rw [←wordEquiv.symm.sum_comp (face P z i j k)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,wordEquiv_symm_apply,face,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have tail (a b c : Bool) : (![a,b,c] : Fin 3 → Bool) 2=c := rfl
  simp only [tail,ite_true,Bool.false_eq_true,ite_false,Holant.Tractable.AffinePhase.xor_origin]
  rw [BooleanQuadratic.cubeParity_eq_eight]
  abel

/-- The nonquadraticity witness already gives the actual offending Gram
table on its three-coordinate face. -/
theorem bad_face_not_bo {n : ℕ} (P : (Fin n → Bool) → ZMod 2) (z : Fin n → Bool)
    (i j k : Fin n) (odd : BooleanQuadratic.cubeParity P z i j k=1) :
    ¬BlockOrthogonal (fun (row : Fin 3 → Bool) (a : Bool) =>
      gram (face P z i j k) ![a,row 0,row 1,row 2]) := by
  apply odd_table_not_bo
  rw [face_sum,odd]

theorem nonquadratic_gram_witness {n : ℕ} (P : (Fin n → Bool) → ZMod 2)
    (nonquadratic : ¬BooleanQuadratic.Quadratic P) :
    ∃ z i j k,BooleanQuadratic.Distinct i j k ∧
      ¬BlockOrthogonal (fun (row : Fin 3 → Bool) (a : Bool) =>
        gram (face P z i j k) ![a,row 0,row 1,row 2]) := by
  obtain ⟨z,i,j,k,distinct,odd⟩ := BooleanQuadratic.exists_bad_cube P nonquadratic
  exact ⟨z,i,j,k,distinct,bad_face_not_bo P z i j k odd⟩

end
end Paper2.DegreeCSP.BadCubeGram

