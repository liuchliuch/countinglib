import Holant.Tractable.AffinePhaseCriterion
import Paper2.Tractable.Affine
import Mathlib.Algebra.CharP.Two

/-! Literal quadratic reconstruction of Boolean signs. All third coordinate
differences are tested on actual three-coordinate cube faces; repeated
coordinate differences vanish automatically in characteristic two. -/
namespace Paper2.DegreeCSP.BooleanQuadratic
open scoped BigOperators
open Holant.Tractable.AffinePhase (Word xor origin basis word)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def difference (P : Word n → ZMod 2) (u : Word n) : Word n → ZMod 2 :=
  fun z => P (xor z u)+P z

def Distinct (i j k : Fin n) : Prop := i≠j ∧ j≠k ∧ i≠k

def cubeParity (P : Word n → ZMod 2) (z : Word n) (i j k : Fin n) : ZMod 2 :=
  difference (difference (difference P (basis i)) (basis j)) (basis k) z

def ThirdCoordinateTrivial (P : Word n → ZMod 2) : Prop :=
  ∀ z i j k,Distinct i j k → cubeParity P z i j k=0

theorem cubeParity_eq_eight (P : Word n → ZMod 2) (z : Word n) (i j k : Fin n) :
    cubeParity P z i j k=
      P z+P (xor z (basis i))+P (xor z (basis j))+P (xor z (basis k))+
      P (xor (xor z (basis i)) (basis j))+
      P (xor (xor z (basis i)) (basis k))+
      P (xor (xor z (basis j)) (basis k))+
      P (xor (xor (xor z (basis i)) (basis j)) (basis k)) := by
  simp only [cubeParity,difference]
  have swap (x u v : Word n) : xor (xor x u) v=xor (xor x v) u := by
    rw [Holant.Tractable.AffinePhase.xor_assoc,Holant.Tractable.AffinePhase.xor_comm u v,
      ←Holant.Tractable.AffinePhase.xor_assoc]
  rw [swap z (basis j) (basis i),swap z (basis k) (basis i),
    swap z (basis k) (basis j)]
  have triple : xor (xor (xor z (basis j)) (basis k)) (basis i)=
      xor (xor (xor z (basis i)) (basis j)) (basis k) := by
    rw [swap (xor z (basis j)) (basis k) (basis i),swap z (basis j) (basis i)]
  rw [triple]
  abel

theorem difference_commute (P : Word n → ZMod 2) (u v : Word n) :
    difference (difference P u) v=difference (difference P v) u := by
  funext z
  simp only [difference]
  have swap : xor (xor z v) u=xor (xor z u) v := by
    rw [Holant.Tractable.AffinePhase.xor_assoc,Holant.Tractable.AffinePhase.xor_comm v u,
      ←Holant.Tractable.AffinePhase.xor_assoc]
  rw [swap]
  abel

@[simp] theorem difference_twice (P : Word n → ZMod 2) (u : Word n) :
    difference (difference P u) u=fun _ => 0 := by
  funext z
  simp only [difference,Holant.Tractable.AffinePhase.xor_cancel_right]
  calc
    P z+P (xor z u)+(P (xor z u)+P z)=
      (P z+P z)+(P (xor z u)+P (xor z u)) := by abel
    _=0 := by rw [CharTwo.add_self_eq_zero,CharTwo.add_self_eq_zero,add_zero]

@[simp] theorem difference_zero (u : Word n) : difference (fun _ => (0 : ZMod 2)) u=fun _ => 0 := by
  funext z
  simp [difference]

theorem all_coordinate_cubes (P : Word n → ZMod 2) (h : ThirdCoordinateTrivial P)
    (z : Word n) (i j k : Fin n) : cubeParity P z i j k=0 := by
  by_cases ij : i=j
  · subst j
    simp [cubeParity]
  by_cases jk : j=k
  · subst k
    simp [cubeParity]
  by_cases ik : i=k
  · subst k
    rw [cubeParity,difference_commute (difference P (basis i)) (basis j) (basis i),
      difference_twice,difference_zero]
  · exact h z i j k ⟨ij,jk,ik⟩

theorem constant_of_coordinate_differences (P : Word n → ZMod 2)
    (h : ∀ i z,difference P (basis i) z=0) (x : Word n) : P x=P (origin n) := by
  classical
  have finite (s : Finset (Fin n)) : P (word s)=P (origin n) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Holant.Tractable.AffinePhase.word_insert s i hi]
      have hd := h i (word s)
      have equal : P (xor (word s) (basis i))=P (word s) := by
        exact (add_eq_zero_iff_eq_neg.mp hd).trans (ZMod.neg_eq_self_mod_two _)
      exact equal.trans ih
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x i=true)
  have word_eq : word s=x := by
    funext i
    simp [word,s]
  simpa only [word_eq] using finite s

def linearCoefficient (P : Word n → ZMod 2) (i : Fin n) : ZMod 2 :=
  difference P (basis i) (origin n)

def mixedCoefficient (P : Word n → ZMod 2) (i j : Fin n) : ZMod 2 :=
  difference (difference P (basis i)) (basis j) (origin n)

theorem mixed_comm (P : Word n → ZMod 2) (i j : Fin n) :
    mixedCoefficient P i j=mixedCoefficient P j i := by
  exact congrFun (difference_commute P (basis i) (basis j)) (origin n)

theorem second_constant (P : Word n → ZMod 2) (h : ThirdCoordinateTrivial P)
    (z : Word n) (i j : Fin n) :
    difference (difference P (basis i)) (basis j) z=mixedCoefficient P i j := by
  apply constant_of_coordinate_differences
  intro k x
  exact all_coordinate_cubes P h x i j k

theorem first_translate (P : Word n → ZMod 2) (h : ThirdCoordinateTrivial P)
    (z : Word n) (i j : Fin n) :
    difference P (basis i) (xor z (basis j))=
      difference P (basis i) z+mixedCoefficient P i j := by
  have constant := second_constant P h z i j
  change difference P (basis i) (xor z (basis j))+difference P (basis i) z=_ at constant
  calc
    _=(difference P (basis i) (xor z (basis j))+difference P (basis i) z)+
      difference P (basis i) z := (CharTwo.add_cancel_right _ _).symm
    _=mixedCoefficient P i j+difference P (basis i) z := by rw [constant]
    _=_ := add_comm _ _

theorem first_word (P : Word n → ZMod 2) (h : ThirdCoordinateTrivial P)
    (i : Fin n) (s : Finset (Fin n)) :
    difference P (basis i) (word s)=linearCoefficient P i+∑ j ∈ s,mixedCoefficient P i j := by
  induction s using Finset.induction_on with
  | empty => simp [linearCoefficient]
  | @insert j s hj ih =>
    rw [Holant.Tractable.AffinePhase.word_insert s j hj,first_translate P h,ih,
      Finset.sum_insert hj]
    abel

theorem value_insert (P : Word n → ZMod 2) (h : ThirdCoordinateTrivial P)
    (i : Fin n) (s : Finset (Fin n)) (hi : i∉s) :
    P (word (insert i s))=P (word s)+linearCoefficient P i+∑ j ∈ s,mixedCoefficient P i j := by
  rw [Holant.Tractable.AffinePhase.word_insert s i hi]
  have first := first_word P h i s
  change P (xor (word s) (basis i))+P (word s)=_ at first
  calc
    _=(P (xor (word s) (basis i))+P (word s))+P (word s) :=
      (CharTwo.add_cancel_right _ _).symm
    _=_ := by rw [first]; abel

structure Polynomial (n : ℕ) where
  constant : ZMod 2
  linear : Fin n → ZMod 2
  mixed : Fin n → Fin n → ZMod 2

def Polynomial.eval (Q : Polynomial n) (x : Word n) : ZMod 2 :=
  Q.constant+(∑ i,Q.linear i*Tractable.bitValue (ZMod 2) (x i))+
    ∑ i,∑ j,if i<j then Q.mixed i j*Tractable.bitValue (ZMod 2) (x i)*
      Tractable.bitValue (ZMod 2) (x j) else 0

def polynomial (P : Word n → ZMod 2) : Polynomial n :=
  ⟨P (origin n),linearCoefficient P,mixedCoefficient P⟩

theorem eval_word (Q : Polynomial n) (s : Finset (Fin n)) :
    Q.eval (word s)=Q.constant+(∑ i ∈ s,Q.linear i)+
      ∑ i ∈ s,∑ j ∈ s,if i<j then Q.mixed i j else 0 := by
  classical
  have linear (i : Fin n) : Q.linear i*Tractable.bitValue (ZMod 2) (word s i)=
      if i∈s then Q.linear i else 0 := by
    by_cases hi : i∈s <;> simp [word,Tractable.bitValue,hi]
  have mixed (i j : Fin n) :
      (if i<j then Q.mixed i j*Tractable.bitValue (ZMod 2) (word s i)*
        Tractable.bitValue (ZMod 2) (word s j) else 0)=
      if i∈s then if j∈s then (if i<j then Q.mixed i j else 0) else 0 else 0 := by
    by_cases hi : i∈s <;> by_cases hj : j∈s <;> by_cases order : i<j <;>
      simp [word,Tractable.bitValue,hi,hj,order]
  simp only [Polynomial.eval,linear,mixed]
  simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero,←Finset.sum_filter]
  simp

theorem eval_insert_max (Q : Polynomial n) (s : Finset (Fin n))
    (i : Fin n) (hi : i∉s) (maximal : ∀ j ∈ s, j < i) :
    Q.eval (word (insert i s))=Q.eval (word s)+Q.linear i+∑ j∈s,Q.mixed j i := by
  classical
  have new : (∑ j∈s,if i<j then Q.mixed i j else 0)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [not_lt_of_ge (le_of_lt (maximal j hj))]
  have old (j : Fin n) (hj : j∈s) :
      (∑ k∈insert i s,if j<k then Q.mixed j k else 0)=
      Q.mixed j i+∑ k∈s,if j<k then Q.mixed j k else 0 := by
    rw [Finset.sum_insert hi,ite_eq_left (maximal j hj)]
  rw [eval_word,eval_word,Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]
  simp only [lt_self_iff_false,ite_false,zero_add,new]
  rw [Finset.sum_congr rfl old,Finset.sum_add_distrib]
  abel

/-- Every coefficient is the literal constant, first, or second difference
at the zero word; only strictly ordered pairs contribute. -/
theorem reconstruct (P : Word n → ZMod 2) (h : ThirdCoordinateTrivial P) :
    ∀ x,P x=(polynomial P).eval x := by
  classical
  have finite (s : Finset (Fin n)) : P (word s)=(polynomial P).eval (word s) := by
    induction s using Finset.induction_on_max with
    | empty => simp [Polynomial.eval,polynomial,origin,Tractable.bitValue]
    | insert i s maximal ih =>
      have hi : i∉s := by
        intro member
        exact (lt_irrefl i) (maximal i member)
      rw [value_insert P h i s hi,ih,eval_insert_max _ s i hi maximal]
      change _=(polynomial P).eval (word s)+linearCoefficient P i+∑ j∈s,mixedCoefficient P j i
      simp_rw [mixed_comm P i]
  intro x
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x i=true)
  have word_eq : word s=x := by
    funext i
    simp [word,s]
  simpa only [word_eq] using finite s

def Quadratic (P : Word n → ZMod 2) : Prop := ∃ Q : Polynomial n,∀ x,P x=Q.eval x

/-- Failure of quadraticity exposes eight actual face values of odd parity. -/
theorem exists_bad_cube (P : Word n → ZMod 2) (nonquadratic : ¬Quadratic P) :
    ∃ z i j k,Distinct i j k ∧ cubeParity P z i j k=1 := by
  classical
  by_contra none
  apply nonquadratic
  refine ⟨polynomial P,reconstruct P ?_⟩
  intro z i j k distinct
  by_contra nonzero
  have one : cubeParity P z i j k=1 := by
    generalize cubeParity P z i j k=a at nonzero ⊢
    fin_cases a <;> simp_all
  exact none ⟨z,i,j,k,distinct,one⟩

end
end Paper2.DegreeCSP.BooleanQuadratic

