import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.Basic
import Mathlib.Logic.Encodable.Pi

/-!
# Executable finite sparse polynomial programs

A program is a literal list of coefficient/exponent-vector pairs. Repeated
monomials, repeated coefficients, and zero coefficients are allowed. All program
constructors and the interpreter are executable from the supplied coefficient
operations. Only the semantic translation into mathlib's `MvPolynomial` is
marked noncomputable; algorithms do not call that translation.
-/
namespace ComplexCSP.PolynomialPrograms
open scoped BigOperators

structure Term (K : Type*) (n : ℕ) where
  coefficient : K
  exponent : Fin n → ℕ

abbrev Program (K : Type*) (n : ℕ) := List (Term K n)

variable {K R S : Type*} {n m : ℕ}

/-- Literal coefficient/vector data supplies a finite natural-number encoding
whenever the coefficient representation already has one. -/
def termDataEquiv : Term K n ≃ K × (Fin n → ℕ) where
  toFun t := (t.coefficient, t.exponent)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Encodable K] : Encodable (Term K n) :=
  Encodable.ofEquiv (K × (Fin n → ℕ)) termDataEquiv

/-- Expand the finite exponent vector into a literal factor-index list. -/
def expandedVariables (t : Term K n) : List (Fin n) :=
  (List.ofFn (fun i => List.replicate (t.exponent i) i)).flatten

theorem expandedVariables_product [CommMonoid R] (t : Term K n) (x : Fin n → R) :
    ((expandedVariables t).map x).prod = ∏ i, x i ^ t.exponent i := by
  simp only [expandedVariables, List.map_flatten, List.prod_flatten,
    List.map_ofFn, List.prod_ofFn, Function.comp_def, List.map_replicate, List.prod_replicate]

def zero : Program K n := []

def constant (c : K) : Program K n := [⟨c, fun _ => 0⟩]

def coordinate [One K] (i : Fin n) : Program K n :=
  [⟨1, fun j => if j = i then 1 else 0⟩]

def add (P Q : Program K n) : Program K n := P ++ Q

def scale [Mul K] (c : K) (P : Program K n) : Program K n :=
  P.map (fun t => ⟨c * t.coefficient, t.exponent⟩)

def multiplyTerm [Mul K] (t u : Term K n) : Term K n :=
  ⟨t.coefficient * u.coefficient, fun i => t.exponent i + u.exponent i⟩

def multiply [Mul K] (P Q : Program K n) : Program K n :=
  P.flatMap (fun t => Q.map (multiplyTerm t))

def power [One K] [Mul K] (P : Program K n) : ℕ → Program K n
  | 0 => constant 1
  | k + 1 => multiply (power P k) P

def product [One K] [Mul K] : List (Program K n) → Program K n
  | [] => constant 1
  | P :: Ps => multiply P (product Ps)

def sum : List (Program K n) → Program K n := List.flatten

def mapCoefficients (f : K → R) (P : Program K n) : Program R n :=
  P.map (fun t => ⟨f t.coefficient, t.exponent⟩)

def conjugateCoefficients [Star K] (P : Program K n) : Program K n :=
  mapCoefficients star P

/-- Simultaneous ordinary formal substitution, including repeated variables. -/
def substitute [One K] [Mul K] (P : Program K n) (q : Fin n → Program K m) : Program K m :=
  P.flatMap (fun t => scale t.coefficient
    (product (List.ofFn (fun i => power (q i) (t.exponent i)))))

def rename [One K] [Mul K] (P : Program K n) (f : Fin n → Fin m) : Program K m :=
  substitute P (fun i => coordinate (f i))

/-- Enumerate one equation from each branch and multiply. An empty branch
produces no products; no branches produce the one polynomial. -/
def branchProducts [One K] [Mul K] : List (List (Program K n)) → List (Program K n)
  | [] => [constant 1]
  | E :: Es => E.flatMap (fun P => (branchProducts Es).map (multiply P))

section Interpretation
variable [CommSemiring K] [CommSemiring R]

def interpretTerm (f : K →+* R) (x : Fin n → R) (t : Term K n) : R :=
  f t.coefficient * ∏ i, x i ^ t.exponent i

def interpret (f : K →+* R) (x : Fin n → R) (P : Program K n) : R :=
  (P.map (interpretTerm f x)).sum

def eval (x : Fin n → K) (P : Program K n) : K := interpret (RingHom.id K) x P

@[simp] theorem interpret_nil (f : K →+* R) (x : Fin n → R) :
    interpret f x [] = 0 := rfl

@[simp] theorem interpret_cons (f : K →+* R) (x : Fin n → R) (t : Term K n)
    (P : Program K n) : interpret f x (t :: P) = interpretTerm f x t + interpret f x P := rfl

@[simp] theorem interpret_constant (f : K →+* R) (x : Fin n → R) (c : K) :
    interpret f x (constant c) = f c := by simp [interpret, interpretTerm, constant]

@[simp] theorem interpret_variable (f : K →+* R) (x : Fin n → R) (j : Fin n) :
    interpret f x (coordinate j) = x j := by
  simp [interpret, interpretTerm, coordinate, apply_ite]

@[simp] theorem interpret_add (f : K →+* R) (x : Fin n → R) (P Q : Program K n) :
    interpret f x (add P Q) = interpret f x P + interpret f x Q := by
  simp [interpret, add]

@[simp] theorem interpret_scale (f : K →+* R) (x : Fin n → R) (c : K) (P : Program K n) :
    interpret f x (scale c P) = f c * interpret f x P := by
  simp only [interpret, scale, List.map_map, Function.comp_def, interpretTerm, map_mul, mul_assoc]
  exact List.sum_map_mul_left P _ (f c)

@[simp] theorem interpret_multiplyTerm (f : K →+* R) (x : Fin n → R) (t u : Term K n) :
    interpretTerm f x (multiplyTerm t u) = interpretTerm f x t * interpretTerm f x u := by
  simp only [interpretTerm, multiplyTerm, map_mul, pow_add, Finset.prod_mul_distrib]
  ac_rfl

@[simp] theorem interpret_multiply (f : K →+* R) (x : Fin n → R) (P Q : Program K n) :
    interpret f x (multiply P Q) = interpret f x P * interpret f x Q := by
  induction P with
  | nil => simp [multiply]
  | cons t P ih =>
    change interpret f x (Q.map (multiplyTerm t) ++ multiply P Q) = _
    rw [show interpret f x (Q.map (multiplyTerm t) ++ multiply P Q) =
      interpret f x (Q.map (multiplyTerm t)) + interpret f x (multiply P Q) from
      interpret_add f x _ _, ih, interpret_cons, add_mul]
    congr 1
    simp only [interpret, List.map_map, Function.comp_def, interpret_multiplyTerm]
    exact List.sum_map_mul_left Q _ (interpretTerm f x t)

@[simp] theorem interpret_power (f : K →+* R) (x : Fin n → R) (P : Program K n) (k : ℕ) :
    interpret f x (power P k) = interpret f x P ^ k := by
  induction k with
  | zero => simp [power]
  | succ k ih => simp [power, ih, pow_succ]

@[simp] theorem interpret_product (f : K →+* R) (x : Fin n → R) (Ps : List (Program K n)) :
    interpret f x (product Ps) = (Ps.map (interpret f x)).prod := by
  induction Ps with
  | nil => simp [product]
  | cons P Ps ih => simp [product, ih]

@[simp] theorem interpret_sum (f : K →+* R) (x : Fin n → R) (Ps : List (Program K n)) :
    interpret f x (sum Ps) = (Ps.map (interpret f x)).sum := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih =>
    simpa only [sum, add, List.flatten_cons, List.map_cons, List.sum_cons] using
      (interpret_add f x P Ps.flatten).trans (congrArg (interpret f x P + ·) ih)

@[simp] theorem interpret_substitute (f : K →+* R) (x : Fin m → R)
    (P : Program K n) (q : Fin n → Program K m) :
    interpret f x (substitute P q) = interpret f (fun i => interpret f x (q i)) P := by
  induction P with
  | nil => simp [substitute]
  | cons t P ih =>
    change interpret f x (add (scale t.coefficient
      (product (List.ofFn (fun i => power (q i) (t.exponent i))))) (substitute P q)) = _
    rw [interpret_add, ih, interpret_cons, interpret_scale, interpret_product]
    simp only [List.map_ofFn, List.prod_ofFn, Function.comp_def, interpret_power, interpretTerm]

@[simp] theorem interpret_rename (f : K →+* R) (x : Fin m → R)
    (P : Program K n) (r : Fin n → Fin m) :
    interpret f x (rename P r) = interpret f (x ∘ r) P := by
  simp only [rename, interpret_substitute, interpret_variable, Function.comp_def]

variable [CommSemiring S]

@[simp] theorem interpret_mapCoefficients (f : K →+* R) (h : R →+* S)
    (x : Fin n → S) (P : Program K n) :
    interpret h x (mapCoefficients f P) = interpret (h.comp f) x P := by
  simp only [interpret, mapCoefficients, List.map_map, Function.comp_def,
    interpretTerm ]
  rfl

/-- Every semiring homomorphism commutes with the literal finite interpreter. -/
theorem map_interpret (f : K →+* R) (h : R →+* S) (x : Fin n → R) (P : Program K n) :
    h (interpret f x P) = interpret (h.comp f) (fun i => h (x i)) P := by
  simp only [interpret, map_list_sum, List.map_map, Function.comp_def, interpretTerm,
    map_mul, map_prod, map_pow ]
  rfl

/-- The finite coefficient/monomial sum expected by the character identity
oracle. Duplicate syntax terms remain separate indices. -/
theorem interpret_eq_indexed_sum (f : K →+* R) (x : Fin n → R) (P : Program K n) :
    interpret f x P = ∑ i : Fin P.length,
      f (P.get i).coefficient * ∏ j, x j ^ (P.get i).exponent j := by
  have h := congrArg (fun l : List (Term K n) => (l.map (interpretTerm f x)).sum)
    (List.ofFn_get P)
  rw [List.map_ofFn, List.sum_ofFn] at h
  exact h.symm

theorem interpretTerm_eq_expanded_product (f : K →+* R) (x : Fin n → R) (t : Term K n) :
    interpretTerm f x t = f t.coefficient * ((expandedVariables t).map x).prod := by
  rw [expandedVariables_product]
  rfl

end Interpretation

section Semantics
variable [CommSemiring K]

/-- Semantic translation only. None of the executable constructors calls this. -/
noncomputable def denote (P : Program K n) : MvPolynomial (Fin n) K :=
  interpret MvPolynomial.C MvPolynomial.X P

@[simp] theorem denote_constant (c : K) : denote (constant (n := n) c) = MvPolynomial.C c :=
  interpret_constant _ _ _

@[simp] theorem denote_coordinate (j : Fin n) :
    denote (coordinate (K := K) j) = MvPolynomial.X j := interpret_variable _ _ _

@[simp] theorem denote_add (P Q : Program K n) : denote (add P Q) = denote P + denote Q :=
  interpret_add _ _ _ _

@[simp] theorem denote_scale (c : K) (P : Program K n) :
    denote (scale c P) = MvPolynomial.C c * denote P := interpret_scale _ _ _ _

@[simp] theorem denote_multiply (P Q : Program K n) :
    denote (multiply P Q) = denote P * denote Q := interpret_multiply _ _ _ _

@[simp] theorem denote_power (P : Program K n) (k : ℕ) :
    denote (power P k) = denote P ^ k := interpret_power _ _ _ _

@[simp] theorem denote_product (Ps : List (Program K n)) :
    denote (product Ps) = (Ps.map denote).prod := interpret_product _ _ _

@[simp] theorem denote_sum (Ps : List (Program K n)) :
    denote (sum Ps) = (Ps.map denote).sum := interpret_sum _ _ _

/-- The program interpreter agrees with ordinary multivariate-polynomial
semantics under arbitrary coefficient homomorphisms and variable assignments. -/
theorem eval₂_denote [CommSemiring R] (f : K →+* R) (x : Fin n → R) (P : Program K n) :
    (MvPolynomial.eval₂Hom f x) (denote P) = interpret f x P := by
  have hf : (MvPolynomial.eval₂Hom f x).comp MvPolynomial.C = f := by
    ext c
    exact MvPolynomial.eval₂Hom_C f x c
  simpa only [denote, hf, MvPolynomial.eval₂Hom_X'] using
    map_interpret MvPolynomial.C (MvPolynomial.eval₂Hom f x) MvPolynomial.X P

/-- Executable evaluation has exactly the MvPolynomial meaning. -/
theorem eval_eq_mvPolynomial_eval (x : Fin n → K) (P : Program K n) :
    eval x P = MvPolynomial.eval x (denote P) := (eval₂_denote (RingHom.id K) x P).symm

/-- A syntax-level simultaneous substitution is exactly the corresponding
MvPolynomial substitution homomorphism, with no runtime normalization. -/
theorem denote_substitute (P : Program K n) (q : Fin n → Program K m) :
    denote (substitute P q) =
      (MvPolynomial.eval₂Hom MvPolynomial.C (fun i => denote (q i))) (denote P) := by
  rw [eval₂_denote]
  exact interpret_substitute MvPolynomial.C MvPolynomial.X P q

theorem denote_mapCoefficients [CommSemiring R] (f : K →+* R) (P : Program K n) :
    denote (mapCoefficients f P) = MvPolynomial.map f (denote P) := by
  unfold denote
  rw [map_interpret]
  simp only [interpret_mapCoefficients, MvPolynomial.map_X]
  congr 1
  apply RingHom.ext
  intro c
  exact (MvPolynomial.map_C f c).symm

/-- The sparse syntax denotes every ordinary finite-variable polynomial.
This expressiveness theorem is semantic; it is not a runtime traversal of
mathlib's noncomputable polynomial representation. -/
theorem exists_program_denote (p : MvPolynomial (Fin n) K) :
    ∃ P : Program K n, denote P = p := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨constant c, denote_constant c⟩
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    exact ⟨add P Q, by rw [denote_add, hP, hQ]⟩
  | mul_X p j hp =>
    obtain ⟨P, hP⟩ := hp
    exact ⟨multiply P (coordinate j), by rw [denote_multiply, hP, denote_coordinate]⟩

end Semantics
section Conjugation
variable [CommSemiring K] [StarRing K]

/-- Coefficient conjugation and conjugation of the assigned values commute
with exact polynomial evaluation. -/
theorem eval_conjugateCoefficients (x : Fin n → K) (P : Program K n) :
    eval (fun i => star (x i)) (conjugateCoefficients P) = star (eval x P) := by
  change interpret (RingHom.id K) (fun i => star (x i))
    (mapCoefficients (starRingEnd K) P) = _
  rw [interpret_mapCoefficients]
  simpa only [eval, RingHom.id_comp, RingHom.comp_id, starRingEnd_apply] using
    (map_interpret (RingHom.id K) (starRingEnd K) x P).symm

theorem denote_conjugateCoefficients (P : Program K n) :
    denote (conjugateCoefficients P) = MvPolynomial.map (starRingEnd K) (denote P) :=
  denote_mapCoefficients (starRingEnd K) P

/-- Exchange the two formal variable blocks X and Y. -/
def swapBlocks (n : ℕ) : Fin (n + n) ≃ Fin (n + n) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin n) (Fin n)).trans finSumFinEquiv)

def jointValues (x y : Fin n → K) : Fin (n + n) → K :=
  Sum.elim x y ∘ finSumFinEquiv.symm

/-- Conjugate coefficients and exchange formal X/Y variables. -/
def formalConjugate (P : Program K (n + n)) : Program K (n + n) :=
  rename (conjugateCoefficients P) (swapBlocks n)

/-- Under the intended Y=conjugate(X) substitution, formal conjugation means
exact conjugation of the numerical value. -/
theorem eval_formalConjugate (x : Fin n → K) (P : Program K (n + n)) :
    eval (jointValues x (fun i => star (x i))) (formalConjugate P) =
      star (eval (jointValues x (fun i => star (x i))) P) := by
  let v := jointValues x (fun i => star (x i))
  have hv : v ∘ swapBlocks n = fun i => star (v i) := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    change jointValues x (fun i => star (x i)) (swapBlocks n (finSumFinEquiv j)) =
      star (jointValues x (fun i => star (x i)) (finSumFinEquiv j))
    simp only [swapBlocks, Equiv.trans_apply, Equiv.symm_apply_apply]
    simp only [jointValues, Function.comp_apply, Equiv.symm_apply_apply]
    cases j <;> simp
  change interpret (RingHom.id K) v (rename (conjugateCoefficients P) (swapBlocks n)) = _
  rw [interpret_rename, hv]
  exact eval_conjugateCoefficients v P
end Conjugation

section BranchEnumeration
variable [CommSemiring K] [CommSemiring R]

@[simp] theorem mem_branchProducts_cons (E : List (Program K n))
    (Es : List (List (Program K n))) (q : Program K n) :
    q ∈ branchProducts (E :: Es) ↔
      ∃ P ∈ E, ∃ Q ∈ branchProducts Es, multiply P Q = q := by
  simp only [branchProducts, List.mem_flatMap, List.mem_map]

/-- Exact finite-union/product-identity equivalence for executable programs.
This includes empty branches and the empty collection of branches. -/
theorem branchProducts_zero_iff [NoZeroDivisors R] [Nontrivial R]
    (f : K →+* R) (x : Fin n → R) (Es : List (List (Program K n))) :
    (∀ q ∈ branchProducts Es, interpret f x q = 0) ↔
      ∃ E ∈ Es, ∀ p ∈ E, interpret f x p = 0 := by
  classical
  induction Es with
  | nil => simp [branchProducts]
  | cons E Es ih =>
    constructor
    · intro h
      by_cases hE : ∀ p ∈ E, interpret f x p = 0
      · exact ⟨E, List.mem_cons_self, hE⟩
      · push_neg at hE
        obtain ⟨p, hp, hpn⟩ := hE
        have ht : ∀ q ∈ branchProducts Es, interpret f x q = 0 := by
          intro q hq
          have he := h (multiply p q) ((mem_branchProducts_cons E Es _).mpr
            ⟨p, hp, q, hq, rfl⟩)
          rw [interpret_multiply] at he
          exact (mul_eq_zero.mp he).resolve_left hpn
        obtain ⟨F, hF, hz⟩ := ih.mp ht
        exact ⟨F, List.mem_cons_of_mem _ hF, hz⟩
    · rintro ⟨F, hF, hz⟩ q hq
      obtain ⟨p, hp, r, hr, rfl⟩ := (mem_branchProducts_cons E Es q).mp hq
      rw [interpret_multiply]
      rcases List.mem_cons.mp hF with rfl | hF
      · rw [hz p hp, zero_mul]
      · rw [ih.mpr ⟨F, hF, hz⟩ r hr, mul_zero]

/-- Corollary 4.4's executable syntax has exactly the ordinary MvPolynomial
zero-locus meaning once the semantic translation is applied. -/
theorem branchProducts_mvPolynomial_zero_iff [NoZeroDivisors K] [Nontrivial K]
    (x : Fin n → K) (Es : List (List (Program K n))) :
    (∀ q ∈ branchProducts Es, MvPolynomial.eval x (denote q) = 0) ↔
      ∃ E ∈ Es, ∀ p ∈ E, MvPolynomial.eval x (denote p) = 0 := by
  simpa only [← eval_eq_mvPolynomial_eval, eval] using
    branchProducts_zero_iff (RingHom.id K) x Es

@[simp] theorem branchProducts_nil : branchProducts ([] : List (List (Program K n))) = [constant 1] := rfl

@[simp] theorem branchProducts_empty_head (Es : List (List (Program K n))) :
    branchProducts ([] :: Es) = [] := rfl

end BranchEnumeration
end ComplexCSP.PolynomialPrograms
