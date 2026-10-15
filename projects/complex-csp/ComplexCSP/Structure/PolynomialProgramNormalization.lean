import ComplexCSP.Structure.PolynomialPrograms

/-! # Executable sparse-program simplification

Duplicate monomials are merged using finite exponent-vector equality. Zero
coefficients are discarded, so tautological certificate equations do not cause
an unnecessary product-family explosion. Every simplification preserves values.
-/
namespace ComplexCSP.PolynomialPrograms

variable {K : Type} {n : ℕ} [CommSemiring K] [DecidableEq K]

/-- Insert one term and merge its first equal exponent vector, if present. -/
def insertTerm (t : Term K n) : Program K n → Program K n
  | [] => if t.coefficient = 0 then [] else [t]
  | u :: us =>
      if t.exponent = u.exponent then
        if t.coefficient + u.coefficient = 0 then us
        else ⟨t.coefficient + u.coefficient,t.exponent⟩ :: us
      else u :: insertTerm t us

def normalize : Program K n → Program K n
  | [] => []
  | t :: ts => insertTerm t (normalize ts)

theorem eval_insertTerm (x : Fin n → K) (t : Term K n) (P : Program K n) :
    eval x (insertTerm t P) = interpretTerm (RingHom.id K) x t + eval x P := by
  induction P with
  | nil =>
    by_cases ht : t.coefficient = 0 <;>
      simp [insertTerm,ht,eval,interpretTerm,interpret]
  | cons u us ih =>
    by_cases he : t.exponent = u.exponent
    · by_cases hc : t.coefficient + u.coefficient = 0
      · have hz : interpretTerm (RingHom.id K) x t +
            interpretTerm (RingHom.id K) x u = 0 := by
          simp only [interpretTerm,RingHom.id_apply,he,← add_mul,hc,zero_mul]
        simp only [insertTerm,he,if_true,hc,eval,interpret_cons]
        rw [← add_assoc,hz,zero_add]
      · simp only [insertTerm,he,if_true,hc,if_false,eval,interpret_cons,
          interpretTerm,RingHom.id_apply]
        rw [← he,add_mul]
        ac_rfl
    · simp only [insertTerm,he,if_false,eval,interpret_cons] at ih ⊢
      rw [ih]
      ac_rfl

@[simp] theorem eval_normalize (x : Fin n → K) (P : Program K n) :
    eval x (normalize P) = eval x P := by
  induction P with
  | nil => rfl
  | cons t ts ih =>
    rw [normalize,eval_insertTerm,ih]
    rfl

/-- Remove equations which normalize to the zero program. -/
def simplifyBranch (E : List (Program K n)) : List (Program K n) :=
  (E.map normalize).filter (fun P => !P.isEmpty)

theorem simplifyBranch_zero_iff (x : Fin n → K) (E : List (Program K n)) :
    (∀ P ∈ simplifyBranch E, eval x P = 0) ↔ ∀ P ∈ E, eval x P = 0 := by
  constructor
  · intro h P hP
    by_cases hz : normalize P = []
    · rw [← eval_normalize x P,hz]
      rfl
    · have hm : normalize P ∈ simplifyBranch E := by
        simp only [simplifyBranch,List.mem_filter,List.mem_map]
        exact ⟨⟨P,hP,rfl⟩,by simpa using hz⟩
      simpa only [eval_normalize] using h (normalize P) hm
  · intro h P hP
    obtain ⟨hmem,hne⟩ := List.mem_filter.mp hP
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hmem
    simpa only [eval_normalize] using h Q hQ

/-- The complete product family after sound, computable branch simplification. -/
def simplifiedBranchProducts (Es : List (List (Program K n))) : List (Program K n) :=
  branchProducts (Es.map simplifyBranch)

theorem simplifiedBranchProducts_zero_iff [NoZeroDivisors K] [Nontrivial K]
    (x : Fin n → K) (Es : List (List (Program K n))) :
    (∀ P ∈ simplifiedBranchProducts Es, eval x P = 0) ↔
      ∃ E ∈ Es, ∀ P ∈ E, eval x P = 0 := by
  unfold simplifiedBranchProducts eval
  rw [branchProducts_zero_iff]
  simp only [List.mem_map,exists_exists_and_eq_and]
  exact exists_congr (fun E => and_congr_right (fun _ => simplifyBranch_zero_iff x E))

end ComplexCSP.PolynomialPrograms
