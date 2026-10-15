import Paper2.DegreeCSP.GeneratedHadamardUnary
import Paper2.DegreeCSP.GeneratedRestrictions

/-! An actual generated Hadamard anchor produces a parity constraint with
its scalar retained. Finite XOR circuits then implement affine Boolean maps
using actual hidden-variable sums, without changing the degree promise. -/
namespace Paper2.DegreeCSP.GeneratedAffineSubstitution
open scoped BigOperators
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def parity (a : AlgebraicComplex) : Signature AlgebraicComplex 3 :=
  fun x=>(2*a^3)*(if x 2=Bool.xor (x 0) (x 1) then 1 else 0)

theorem parity_generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    {a : AlgebraicComplex} (h : Generated F k (GeneratedHadamardUnary.anchor a)) :
    Generated F k (parity a) := by
  have h0 := generated_pullback h (![3,0] : Fin 2→Fin 4)
  have h1 := generated_pullback h (![3,1] : Fin 2→Fin 4)
  have h2 := generated_pullback h (![3,2] : Fin 2→Fin 4)
  have hg := generated_sum_last (generated_hadamard (generated_hadamard h0 h1) h2)
  convert hg using 1
  funext x
  have hw0 (z : Bool) : (fun i : Fin 2=>Fin.snoc (α:=fun _=>Bool) x z (![3,0] i))=![z,x 0] := by
    funext i; fin_cases i <;> rfl
  have hw1 (z : Bool) : (fun i : Fin 2=>Fin.snoc (α:=fun _=>Bool) x z (![3,1] i))=![z,x 1] := by
    funext i; fin_cases i <;> rfl
  have hw2 (z : Bool) : (fun i : Fin 2=>Fin.snoc (α:=fun _=>Bool) x z (![3,2] i))=![z,x 2] := by
    funext i; fin_cases i <;> rfl
  simp only [hw0,hw1,hw2]
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;>
    simp [parity,GeneratedHadamardUnary.anchor,hx0,hx1,hx2] <;> ring

theorem parity_scale_ne_zero {a : AlgebraicComplex} (ha : a≠0) : 2*a^3≠0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)

theorem parity_tuple (a : AlgebraicComplex) (u v w : Bool) :
    parity a ![u,v,w]=(2*a^3)*(if w=Bool.xor u v then 1 else 0) := rfl

def evaluate {m : ℕ} (indices : List (Fin m)) (b : Bool) (x : Fin m→Bool) : Bool :=
  indices.foldr (fun i r=>Bool.xor (x i) r) b

def relation {m : ℕ} (indices : List (Fin m)) (b : Bool) : Signature AlgebraicComplex (m+1) :=
  fun x=>if x (Fin.last m)=evaluate indices b (fun i=>x i.castSucc) then 1 else 0

theorem relation_snoc {m : ℕ} (indices : List (Fin m)) (b : Bool)
    (x : Fin m→Bool) (z : Bool) :
    relation indices b (Fin.snoc (α:=fun _=>Bool) x z)=
      if z=evaluate indices b x then 1 else 0 := by
  unfold relation
  rw [Fin.snoc_last]
  have hp : (fun i=>Fin.snoc (α:=fun _=>Bool) x z i.castSucc)=x := by
    funext i; exact Fin.snoc_castSucc (α:=fun _=>Bool) z x i
  rw [hp]

theorem relation_cons {m : ℕ} (i : Fin m) (indices : List (Fin m)) (b : Bool)
    (x : Fin (m+1)→Bool) : relation (i::indices) b x=
      if x (Fin.last m)=Bool.xor (x i.castSucc)
        (evaluate indices b (fun j=>x j.castSucc)) then 1 else 0 := rfl

def copyRoute (m : ℕ) : Fin (m+1)→Fin (m+2) :=
  Fin.lastCases (Fin.last (m+1)) (fun i=>i.castSucc.castSucc)

theorem copyRoute_word {m : ℕ} (x : Fin (m+1)→Bool) (z : Bool) :
    (fun j=>Fin.snoc (α:=fun _=>Bool) x z (copyRoute m j))=
      Fin.snoc (α:=fun _=>Bool) (fun i=>x i.castSucc) z := by
  funext j
  refine Fin.lastCases ?_ (fun i=>?_) j <;> simp [copyRoute]

theorem xor_indicator_sum (c s : AlgebraicComplex) (u v w : Bool) :
    (∑ z : Bool,(c*(if z=v then 1 else 0))*(s*(if w=Bool.xor u z then 1 else 0)))=
      (c*s)*(if w=Bool.xor u v then 1 else 0) := by
  cases u <;> cases v <;> cases w <;> simp

/-- Each list element adds one parity gate and one uniquely determined
hidden bit. Every gate contributes its actual nonzero scalar. -/
theorem relation_generated {F : SignatureFamily AlgebraicComplex} {k m : ℕ}
    (a : AlgebraicComplex) (ha : a≠0)
    (hanchor : Generated F k (GeneratedHadamardUnary.anchor a))
    (hpin0 : Generated F k (literalPin false)) (hpin1 : Generated F k (literalPin true))
    (indices : List (Fin m)) (b : Bool) :
    ∃ c : AlgebraicComplex,c≠0 ∧ Generated F k (fun x=>c*relation indices b x) := by
  induction indices with
  | nil =>
    have hp : Generated F k (literalPin b) := by
      cases b
      · exact hpin0
      · exact hpin1
    refine ⟨1,one_ne_zero,?_⟩
    convert generated_pullback hp (fun _ : Fin 1=>Fin.last m) using 1
    funext x
    simp [relation,evaluate,literalPin]
  | cons i indices ih =>
    obtain ⟨c,hc,hcgen⟩ := ih
    have hR := generated_pullback hcgen (copyRoute m)
    have hP := generated_pullback (parity_generated hanchor)
      (![i.castSucc.castSucc,Fin.last (m+1),(Fin.last m).castSucc] : Fin 3→Fin (m+2))
    have h := generated_sum_last (generated_hadamard hR hP)
    refine ⟨c*(2*a^3),mul_ne_zero hc (parity_scale_ne_zero ha),?_⟩
    convert h using 1
    funext x
    simp only [copyRoute_word]
    change (c*(2*a^3))*relation (i::indices) b x=
      ∑ z : Bool,(c*relation indices b (Fin.snoc (α:=fun _=>Bool) (fun j=>x j.castSucc) z))*
        parity a (fun j=>Fin.snoc (α:=fun _=>Bool) x z
          (![i.castSucc.castSucc,Fin.last (m+1),(Fin.last m).castSucc] j))
    have hw (z : Bool) :
        (fun j=>Fin.snoc (α:=fun _=>Bool) x z
          (![i.castSucc.castSucc,Fin.last (m+1),(Fin.last m).castSucc] j))=
          ![x i.castSucc,z,x (Fin.last m)] := by
      funext j
      fin_cases j <;> simp
    rw [relation_cons]
    simp_rw [relation_snoc,hw,parity_tuple]
    exact (xor_indicator_sum c (2*a^3) (x i.castSucc)
      (evaluate indices b (fun j=>x j.castSucc)) (x (Fin.last m))).symm

private theorem product_generated {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {ι : Type} [Fintype ι] (g : ι→Signature AlgebraicComplex n)
    (hg : ∀ i,Generated F k (g i)) : Generated F k (fun x=>∏ i,g i x) := by
  classical
  have h : ∀ s : Finset ι,Generated F k (fun x=>∏i∈s,g i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using generated_one F k n
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using generated_hadamard (hg i) ih
  simpa using h Finset.univ

def outputRoute {m n : ℕ} (i : Fin n) : Fin (m+1)→Fin (m+n) :=
  Fin.lastCases (Fin.natAdd m i) (fun j=>j.castAdd n)

theorem outputRoute_append {m n : ℕ} (i : Fin n) (x : Fin m→Bool) (y : Fin n→Bool) :
    (fun j=>Fin.append x y (outputRoute i j))=Fin.snoc (α:=fun _=>Bool) x (y i) := by
  funext j
  refine Fin.lastCases ?_ (fun t=>?_) j <;> simp [outputRoute]

/-- Every component is a finite XOR list with a fixed offset. Its actual
circuit has a unique hidden output word, and its nonzero scale is retained. -/
theorem generated_substitution {F : SignatureFamily AlgebraicComplex} {k m n : ℕ}
    (a : AlgebraicComplex) (ha : a≠0)
    (hanchor : Generated F k (GeneratedHadamardUnary.anchor a))
    (hpin0 : Generated F k (literalPin false)) (hpin1 : Generated F k (literalPin true))
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (indices : Fin n→List (Fin m)) (offset : Fin n→Bool) :
    ∃ c : AlgebraicComplex,c≠0 ∧
      Generated F k (fun x : Fin m→Bool=>c*f (fun i=>evaluate (indices i) (offset i) x)) := by
  classical
  have hrel (i : Fin n) := relation_generated a ha hanchor hpin0 hpin1 (indices i) (offset i)
  let c (i : Fin n) := Classical.choose (hrel i)
  have hc (i : Fin n) : c i≠0 := (Classical.choose_spec (hrel i)).1
  have hgen (i : Fin n) : Generated F k (fun x=>c i*relation (indices i) (offset i) x) :=
    (Classical.choose_spec (hrel i)).2
  let g (i : Fin n) : Signature AlgebraicComplex (m+n) :=
    fun w=>c i*relation (indices i) (offset i) (fun j=>w (outputRoute i j))
  have hg (i : Fin n) : Generated F k (g i) := generated_pullback (hgen i) (outputRoute i)
  have hprod := product_generated g hg
  have h := generated_sum_suffix
    (generated_hadamard (generated_pullback hf (Fin.natAdd m)) hprod)
  refine ⟨∏i,c i,Finset.prod_ne_zero_iff.mpr (fun i _=>hc i),?_⟩
  convert h using 1
  funext x
  simp only [g]
  simp_rw [outputRoute_append]
  simp only [relation,Fin.snoc_last,Fin.snoc_castSucc,Fin.append_right]
  let y0 : Fin n→Bool := fun i=>evaluate (indices i) (offset i) x
  rw [Finset.sum_eq_single y0]
  · simp only [y0,ite_true,mul_one]
    exact mul_comm (∏i,c i) (f (fun i=>evaluate (indices i) (offset i) x))
  · intro y _ hy
    have bad : ∃ i,y i≠evaluate (indices i) (offset i) x := by
      by_contra hn
      apply hy
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i,hi⟩ := bad
    have hz : (∏j:Fin n,c j*(if y j=evaluate (indices j) (offset j) x then 1 else 0))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hz,mul_zero]
  · simp

end
end Paper2.DegreeCSP.GeneratedAffineSubstitution
