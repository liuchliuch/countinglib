import Holant.TensorClosure
import Mathlib.Tactic

/-! Exact coefficient inheritance for the sheared class in Lemma 59 of
arXiv:2502.05597.  The generators are literal scalar multiples of pin zero and
the positive-arity rows [2,1,0,...].  Tensor closure retains its actual ordered
partition and normalization scalar. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

def pin {n : ℕ} (c : K) : Holant.Signature K n :=
  fun x => if Holant.weight x = 0 then c else 0

def row {n : ℕ} (c : K) : Holant.Signature K n :=
  fun x => if Holant.weight x = 0 then 2*c else
    if Holant.weight x = 1 then c else 0

def Generator (n : ℕ) (f : Holant.Signature K n) : Prop :=
  (n=1 ∧ ∃ c, f=pin c) ∨ (0<n ∧ ∃ c, f=row c)

def Closed {n : ℕ} (f : Holant.Signature K n) : Prop :=
  f=0 ∨ Holant.Signature.TensorClosure Generator f

/-- A live entry decreases by a factor of two when a permitted zero is
changed to one; changing a one back to zero always doubles its value. -/
def Inheritance {n : ℕ} (f : Holant.Signature K n) : Prop :=
  (∀ x i, x i=true → f x≠0 → f (Function.update x i false)=2*f x) ∧
  (∀ x i, x i=false → f x≠0 →
    2*f (Function.update x i true)=f x ∨ f (Function.update x i true)=0)

theorem weight_update {n : ℕ} (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    Holant.weight (Function.update x i b)+(if x i then 1 else 0)=
      Holant.weight x+(if b then 1 else 0) := by
  classical
  have updated : (fun j => if Function.update x i b j then 1 else 0)=
      Function.update (fun j => if x j then 1 else 0) i (if b then 1 else 0) := by
    funext j
    by_cases h : j=i <;> simp [h]
  have h := Finset.sum_update_of_mem (Finset.mem_univ i)
    (fun j => if x j then 1 else 0) (if b then 1 else 0)
  have original := Finset.sum_erase_add (s:=Finset.univ)
    (f:=fun j => if x j then 1 else 0) (Finset.mem_univ i)
  unfold Holant.weight
  rw [updated,h]
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

theorem weight_positive {n : ℕ} (x : Fin n → Bool) (i : Fin n) (hi : x i=true) :
    0<Holant.weight x := by
  have h := weight_update x i false
  simp only [hi,Bool.false_eq_true,ite_true,ite_false,Nat.add_zero] at h
  omega

theorem row_inheritance {n : ℕ} (c : K) : Inheritance (row (n:=n) c) := by
  constructor
  · intro x i hi live
    have pos := weight_positive x i hi
    have bound : Holant.weight x=1 := by
      by_contra h
      exact live (by simp [row,Nat.ne_of_gt pos,h])
    have upd : Holant.weight (Function.update x i false)=0 := by
      have h := weight_update x i false
      simp only [hi,Bool.false_eq_true,ite_true,ite_false,bound,Nat.add_zero] at h
      omega
    simp [row,bound,upd]
  · intro x i hi live
    have upd := weight_update x i true
    simp [hi] at upd
    by_cases zero : Holant.weight x=0
    · left
      have one : Holant.weight (Function.update x i true)=1 := by omega
      simp [row,zero,one]
    · right
      have high : Holant.weight (Function.update x i true)≠0 ∧
          Holant.weight (Function.update x i true)≠1 := by omega
      simp [row,high.1,high.2]

theorem pin_inheritance {n : ℕ} (c : K) : Inheritance (pin (n:=n) c) := by
  constructor
  · intro x i hi live
    exact False.elim (live (by simp [pin,Nat.ne_of_gt (weight_positive x i hi)]))
  · intro x i hi live
    right
    have upd := weight_update x i true
    simp [hi] at upd
    have pos : Holant.weight (Function.update x i true)≠0 := by omega
    simp [pin,pos]

theorem generator_inheritance {n : ℕ} {f : Holant.Signature K n}
    (hf : Generator n f) : Inheritance f := by
  rcases hf with ⟨_,c,rfl⟩|⟨_,c,rfl⟩
  · exact pin_inheritance c
  · exact row_inheritance c

theorem block_update_same {n : ℕ} (D : TensorDecomposition K n)
    (x : Fin n → Bool) (a : Fin D.count) (b : Fin (D.arity a)) (v : Bool) :
    (fun j => Function.update x (D.ports ⟨a,b⟩) v (D.ports ⟨a,j⟩))=
      Function.update (fun j => x (D.ports ⟨a,j⟩)) b v := by
  classical
  funext j
  by_cases hj : j=b
  · simp [hj]
  · have ne : D.ports ⟨a,j⟩ ≠ D.ports ⟨a,b⟩ := by
      intro eq
      have hs := D.ports.injective eq
      exact hj (by simpa using hs)
    simp [hj,ne]

theorem block_update_other {n : ℕ} (D : TensorDecomposition K n)
    (x : Fin n → Bool) (a k : Fin D.count) (b : Fin (D.arity a)) (v : Bool)
    (hk : k≠a) :
    (fun j => Function.update x (D.ports ⟨a,b⟩) v (D.ports ⟨k,j⟩))=
      (fun j => x (D.ports ⟨k,j⟩)) := by
  classical
  funext j
  have ne : D.ports ⟨k,j⟩ ≠ D.ports ⟨a,b⟩ := by
    intro eq
    exact hk (congrArg Sigma.fst (D.ports.injective eq))
  simp [ne]

theorem decomposition_update {n : ℕ} (D : TensorDecomposition K n)
    (x : Fin n → Bool) (a : Fin D.count) (b : Fin (D.arity a)) (v : Bool) :
    D.value (Function.update x (D.ports ⟨a,b⟩) v)=
      (D.scale:K)*D.factor a (Function.update (fun j => x (D.ports ⟨a,j⟩)) b v)*
        ∏ k ∈ Finset.univ.erase a, D.factor k (fun j => x (D.ports ⟨k,j⟩)) := by
  classical
  have factors : (fun k => D.factor k
      (fun j => Function.update x (D.ports ⟨a,b⟩) v (D.ports ⟨k,j⟩)))=
      Function.update (fun k => D.factor k (fun j => x (D.ports ⟨k,j⟩))) a
        (D.factor a (Function.update (fun j => x (D.ports ⟨a,j⟩)) b v)) := by
    funext k
    by_cases hk : k=a
    · subst k
      simp [block_update_same]
    · simp only [Function.update_of_ne hk,block_update_other D x a k b v hk]
  unfold TensorDecomposition.value
  rw [factors,Finset.prod_update_of_mem (Finset.mem_univ a)]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

theorem decomposition_original {n : ℕ} (D : TensorDecomposition K n)
    (x : Fin n → Bool) (a : Fin D.count) :
    D.value x=(D.scale:K)*D.factor a (fun j => x (D.ports ⟨a,j⟩))*
      ∏ k ∈ Finset.univ.erase a, D.factor k (fun j => x (D.ports ⟨k,j⟩)) := by
  classical
  unfold TensorDecomposition.value
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  ring

theorem decomposition_inheritance {n : ℕ} (D : TensorDecomposition K n)
    (hD : ∀ k, Inheritance (D.factor k)) : Inheritance D.value := by
  classical
  constructor
  · intro x i hi live
    rcases hs : D.ports.symm i with ⟨a,b⟩
    have port : D.ports ⟨a,b⟩=i := by simpa only [hs] using D.ports.apply_symm_apply i
    have factorlive : D.factor a (fun j => x (D.ports ⟨a,j⟩))≠0 := by
      intro zero
      apply live
      simp [decomposition_original D x a,zero]
    have inherited :=  (hD a).1 (fun j => x (D.ports ⟨a,j⟩)) b (by simpa [port] using hi) factorlive
    rw [←port,decomposition_update,decomposition_original D x a,inherited]
    ring
  · intro x i hi live
    rcases hs : D.ports.symm i with ⟨a,b⟩
    have port : D.ports ⟨a,b⟩=i := by simpa only [hs] using D.ports.apply_symm_apply i
    have factorlive : D.factor a (fun j => x (D.ports ⟨a,j⟩))≠0 := by
      intro zero
      apply live
      simp [decomposition_original D x a,zero]
    rcases (hD a).2 (fun j => x (D.ports ⟨a,j⟩)) b (by simpa [port] using hi) factorlive with half|zero
    · left
      rw [←port,decomposition_update,decomposition_original D x a]
      linear_combination (D.scale:K)*
        (∏ k ∈ Finset.univ.erase a,D.factor k (fun j => x (D.ports ⟨k,j⟩)))*half
    · right
      rw [←port,decomposition_update,zero]
      simp

theorem closed_inheritance {n : ℕ} {f : Holant.Signature K n}
    (hf : Closed f) : Inheritance f := by
  rcases hf with rfl|⟨D,hD,rfl⟩
  · constructor <;> intro x i _ live <;> exact False.elim (live rfl)
  · exact decomposition_inheritance D (fun k => generator_inheritance (hD k))

theorem word_eq_zero_of_weight_zero {n : ℕ} (x : Fin n → Bool)
    (hx : Holant.weight x=0) : x=fun _ => false := by
  funext i
  cases hi : x i
  · rfl
  · have pos := weight_positive x i hi
    omega

theorem exists_true_of_weight_positive {n : ℕ} (x : Fin n → Bool)
    (hx : 0<Holant.weight x) : ∃ i,x i=true := by
  classical
  by_contra none
  have zero : x=fun _ => false := by
    funext i
    cases hi : x i
    · rfl
    · exact False.elim (none ⟨i,hi⟩)
  simp [zero,Holant.weight] at hx

variable [CharZero K]

/-- All supported coefficients have the exact same normalization by Hamming
weight. This statement includes the live all-zero coefficient. -/
theorem inheritance_normalizes {n : ℕ} {f : Holant.Signature K n}
    (hf : Inheritance f) (x : Fin n → Bool) (live : f x≠0) :
    (2:K)^(Holant.weight x)*f x=f (fun _ => false) := by
  classical
  have main : ∀ k,∀ x : Fin n → Bool,Holant.weight x=k → f x≠0 →
      (2:K)^k*f x=f (fun _ => false) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hx live
      by_cases zero : k=0
      · have xzero := word_eq_zero_of_weight_zero x (by omega)
        simp [zero,xzero]
      · obtain ⟨i,hi⟩ := exists_true_of_weight_positive x (by omega)
        let y := Function.update x i false
        have yw : Holant.weight y+1=k := by
          have h := weight_update x i false
          simpa [y,hi,hx] using h
        have fy : f y=2*f x := hf.1 x i hi live
        have yl : f y≠0 := by rw [fy]; exact mul_ne_zero (by norm_num) live
        have previous := ih (Holant.weight y) (by omega) y rfl yl
        rw [←yw,pow_succ]
        rw [fy] at previous
        linear_combination previous
  exact main (Holant.weight x) x rfl live

theorem inheritance_origin_live {n : ℕ} {f : Holant.Signature K n}
    (hf : Inheritance f) (x : Fin n → Bool) (live : f x≠0) :
    f (fun _ => false)≠0 := by
  rw [←inheritance_normalizes hf x live]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) live

theorem closed_origin_live {n : ℕ} {f : Holant.Signature K n}
    (hf : Closed f) (nonzero : f≠0) : f (fun _ => false)≠0 := by
  classical
  obtain ⟨x,live⟩ : ∃ x,f x≠0 := by
    by_contra none
    apply nonzero
    funext x
    by_contra live
    exact none ⟨x,live⟩
  exact inheritance_origin_live (closed_inheritance hf) x live

/-- Support is inherited by every coordinatewise smaller Boolean word. -/
theorem inheritance_support_downward {n : ℕ} {f : Holant.Signature K n}
    (hf : Inheritance f) (x y : Fin n → Bool) (live : f x≠0)
    (le : ∀ i,y i=true → x i=true) : f y≠0 := by
  classical
  have main : ∀ k,∀ x y : Fin n → Bool,Holant.weight x=k → f x≠0 →
      (∀ i,y i=true → x i=true) → f y≠0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x y hx live le
      by_cases same : x=y
      · simpa [←same] using live
      · obtain ⟨i,xi,yi⟩ : ∃ i,x i=true ∧ y i=false := by
          by_contra none
          apply same
          funext i
          cases xi : x i <;> cases yi : y i
          · rfl
          · have impossible := le i yi
            simp [xi] at impossible
          · exact False.elim (none ⟨i,xi,yi⟩)
          · rfl
        let z := Function.update x i false
        have zw : Holant.weight z+1=k := by
          have h := weight_update x i false
          simpa [z,xi,hx] using h
        have fz : f z=2*f x := hf.1 x i xi live
        have zl : f z≠0 := by rw [fz]; exact mul_ne_zero (by norm_num) live
        apply ih (Holant.weight z) (by omega) z y rfl zl
        intro j hj
        by_cases ji : j=i
        · subst j
          simp [yi] at hj
        · simp only [z,Function.update_of_ne ji]
          exact le j hj
  exact main (Holant.weight x) x y rfl live le

end
end Paper2.Paper1Proved.OddUnary.NR

