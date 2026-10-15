import ComplexCSP.Recognition.Certificates
import ComplexCSP.Structure.PolynomialPrograms
import ComplexCSP.Structure.PolynomialProgramNormalization
import Mathlib.Data.Finset.Sort

/-! # Executable certificate equation compilation

Each of the five source equation forms becomes literal sparse-program syntax.
Coordinate naming is an explicit finite map; no noncomputable MvPolynomial
traversal occurs at runtime. Semantic identities hold for any naming map.
-/
namespace ComplexCSP.Certificates
open PolynomialPrograms

variable {X D R K : Type} {n : ℕ} [DecidableEq D] [CommRing K]

/-- Subtraction on raw sparse syntax retains duplicates and needs no normalization. -/
def programSub (P Q : Program K n) : Program K n := add P (scale (-1) Q)

/-- Actual finite program for every support, minor and anchor equation. -/
def equationProgram (name : X × D → Fin n) (roots : RootAlphabet K R)
    (c : Certificate X D R) : EquationIndex X D → Program K n
  | .support x z => if c.Allowed x z then zero else coordinate (name (x,z))
  | .twisted x y z w =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ c.Allowed x w then
        programSub (multiply (coordinate (name (x,z))) (coordinate (name (y,w))))
          (scale (roots.value ((c.pair x y).twist z w))
            (multiply (coordinate (name (x,w))) (coordinate (name (y,z))))) else zero
  | .ordinary x y z w =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ c.Allowed x w ∧
          (c.pair x y).dependent = true then
        programSub (multiply (coordinate (name (x,z))) (coordinate (name (y,w))))
          (multiply (coordinate (name (x,w))) (coordinate (name (y,z)))) else zero
  | .firstAnchor x y z =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ (c.pair x y).dependent = false then
        programSub (coordinate (name (x,z)))
          (scale (roots.value ((c.pair x y).firstRoot z))
            (coordinate (name (x,(c.pair x y).group z)))) else zero
  | .secondAnchor x y z =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ (c.pair x y).dependent = false then
        programSub (coordinate (name (y,z)))
          (scale (roots.value ((c.pair x y).secondRoot z))
            (coordinate (name (y,(c.pair x y).group z)))) else zero

/-- The code evaluates exactly the intended equation on its named coordinates. -/
theorem eval_equationProgram (name : X × D → Fin n) (roots : RootAlphabet K R)
    (c : Certificate X D R) (i : EquationIndex X D) (a : Fin n → K) :
    PolynomialPrograms.eval a (equationProgram name roots c i) =
      equationValue roots c (fun x z => a (name (x,z))) i := by
  cases i <;> simp only [equationProgram,equationValue] <;> split_ifs <;>
    simp [programSub,PolynomialPrograms.eval,PolynomialPrograms.zero,sub_eq_add_neg]

/-- Equation correctness for a genuine matrix enumeration. -/
theorem eval_equationProgram_matrix (name : X × D ≃ Fin n) (roots : RootAlphabet K R)
    (c : Certificate X D R) (i : EquationIndex X D) (A : X → D → K) :
    PolynomialPrograms.eval (fun j => A (name.symm j).1 (name.symm j).2)
      (equationProgram name roots c i) = equationValue roots c A i := by
  rw [eval_equationProgram]
  simp

/-- Compile a concrete finite branch list. Its enumeration order is immaterial
for correctness, and repeated equation indices are permitted. -/
def branchProgram (name : X × D → Fin n) (roots : RootAlphabet K R)
    (c : Certificate X D R) (indices : List (EquationIndex X D)) : List (Program K n) :=
  indices.map (equationProgram name roots c)

/-- Compile the finite union's full family of product equations. -/
def certificateProductPrograms (name : X × D → Fin n) (roots : RootAlphabet K R)
    (certificates : List (Certificate X D R)) (indices : List (EquationIndex X D)) :
    List (Program K n) :=
  branchProducts (certificates.map (fun c => branchProgram name roots c indices))

/-- A complete index list faithfully represents the whole polynomial branch. -/
theorem branchProgram_zero_iff (name : X × D ≃ Fin n) (roots : RootAlphabet K R)
    (c : Certificate X D R) (indices : List (EquationIndex X D))
    (hindices : ∀ i, i ∈ indices) (A : X → D → K) :
    (∀ P ∈ branchProgram name roots c indices,
      PolynomialPrograms.eval (fun j => A (name.symm j).1 (name.symm j).2) P = 0) ↔
      Satisfies roots c A := by
  rw [satisfies_iff_equationValues]
  simp only [branchProgram,List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,
    eval_equationProgram_matrix]
  exact ⟨fun h i => h i (hindices i),fun h i hi => h i⟩

/-- A computable canonical finite enumeration using supplied natural-number
encodings. Unlike Finset.toList, this does not choose a quotient representative. -/
def enumerateFinite (A : Type) [Fintype A] [Encodable A] : List A := by
  letI : LinearOrder A := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  exact Finset.univ.sort (· ≤ ·)

theorem mem_enumerateFinite (A : Type) [Fintype A] [Encodable A] (a : A) :
    a ∈ enumerateFinite A := by
  simp only [enumerateFinite, Finset.mem_sort, Finset.mem_univ]

def pairDataCodeEquiv : PairData D R ≃
    Bool × (D → D → R) × (D → D) × (D → R) × (D → R) where
  toFun p := ⟨p.dependent,p.twist,p.group,p.firstRoot,p.secondRoot⟩
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype D] [Encodable D] [Encodable R] : Encodable (PairData D R) :=
  Encodable.ofEquiv _ pairDataCodeEquiv

def certificateCodeEquiv : Certificate X D R ≃
    (X → Finset D) × (D → Finset D) × (X → X → PairData D R) where
  toFun c := ⟨c.rowLabel,c.columnLabel,c.pair⟩
  invFun c := ⟨c.1,c.2.1,c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype X] [Encodable X] [Fintype D] [Encodable D] [Encodable R] :
    Encodable (Certificate X D R) := Encodable.ofEquiv _ certificateCodeEquiv

def equationIndexCodeEquiv : EquationIndex X D ≃
    (X × D) ⊕ (X × X × D × D) ⊕ (X × X × D × D) ⊕ (X × X × D) ⊕ (X × X × D) where
  toFun
    | .support x z => .inl (x,z)
    | .twisted x y z w => .inr (.inl (x,y,z,w))
    | .ordinary x y z w => .inr (.inr (.inl (x,y,z,w)))
    | .firstAnchor x y z => .inr (.inr (.inr (.inl (x,y,z))))
    | .secondAnchor x y z => .inr (.inr (.inr (.inr (x,y,z))))
  invFun
    | .inl (x,z) => .support x z
    | .inr (.inl (x,y,z,w)) => .twisted x y z w
    | .inr (.inr (.inl (x,y,z,w))) => .ordinary x y z w
    | .inr (.inr (.inr (.inl (x,y,z)))) => .firstAnchor x y z
    | .inr (.inr (.inr (.inr (x,y,z)))) => .secondAnchor x y z
  left_inv i := by cases i <;> rfl
  right_inv i := by rcases i with p | p | p | p | p <;> rfl

instance [Encodable X] [Encodable D] : Encodable (EquationIndex X D) :=
  Encodable.ofEquiv _ equationIndexCodeEquiv

/-- All retained certificate branches are selected by actual finite tests and a
computable enumeration, not by a classical list extraction. -/
def retainedCertificateList [Fintype X] [DecidableEq X] [Encodable X]
    [Fintype D] [Encodable D] [Fintype R] [Encodable R] [DecidableEq K]
    (roots : RootAlphabet K R) : List (Certificate X D R) :=
  (enumerateFinite (Certificate X D R)).filter (fun c => decide (c.Retained roots))

@[simp] theorem mem_retainedCertificateList [Fintype X] [DecidableEq X] [Encodable X]
    [Fintype D] [Encodable D] [Fintype R] [Encodable R] [DecidableEq K]
    (roots : RootAlphabet K R) (c : Certificate X D R) :
    c ∈ retainedCertificateList roots ↔ c.Retained roots := by
  simp [retainedCertificateList,mem_enumerateFinite]

/-- The fully enumerated finite family of source product-equation programs. -/
def allProductPrograms [Fintype X] [DecidableEq X] [Encodable X]
    [Fintype D] [Encodable D] [Fintype R] [Encodable R] [DecidableEq K]
    (name : X × D → Fin n) (roots : RootAlphabet K R) : List (Program K n) :=
  certificateProductPrograms name roots (retainedCertificateList roots)
    (enumerateFinite (EquationIndex X D))

/-- The fully executable product family has exactly the desired finite-union
semantics, including disappearing and empty branches. -/
theorem allProductPrograms_zero_iff [IsDomain K]
    [Fintype X] [DecidableEq X] [Encodable X]
    [Fintype D] [Encodable D] [Fintype R] [Encodable R] [DecidableEq K]
    (name : X × D ≃ Fin n) (roots : RootAlphabet K R) (A : X → D → K) :
    (∀ P ∈ allProductPrograms name roots,
      PolynomialPrograms.eval (fun j => A (name.symm j).1 (name.symm j).2) P = 0) ↔
      ∃ c : Certificate X D R, c.Retained roots ∧ Satisfies roots c A := by
  unfold allProductPrograms certificateProductPrograms PolynomialPrograms.eval
  rw [PolynomialPrograms.branchProducts_zero_iff]
  constructor
  · rintro ⟨E,hE,hzero⟩
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hE
    refine ⟨c,(mem_retainedCertificateList roots c).mp hc,?_⟩
    exact (branchProgram_zero_iff name roots c _ (mem_enumerateFinite _) A).mp hzero
  · rintro ⟨c,hc,hzero⟩
    refine ⟨branchProgram name roots c (enumerateFinite (EquationIndex X D)),
      List.mem_map.mpr ⟨c,(mem_retainedCertificateList roots c).mpr hc,rfl⟩,?_⟩
    exact (branchProgram_zero_iff name roots c _ (mem_enumerateFinite _) A).mpr hzero

/-- The same finite identity family with verified duplicate/zero simplification.
A tautological branch is detected before the Cartesian product is expanded. -/
def optimizedProductPrograms [Fintype X] [DecidableEq X] [Encodable X]
    [Fintype D] [Encodable D] [Fintype R] [Encodable R] [DecidableEq K]
    (name : X × D → Fin n) (roots : RootAlphabet K R) : List (Program K n) :=
  simplifiedBranchProducts ((retainedCertificateList roots).map (fun c =>
    branchProgram name roots c (enumerateFinite (EquationIndex X D))))

theorem optimizedProductPrograms_zero_iff [IsDomain K]
    [Fintype X] [DecidableEq X] [Encodable X]
    [Fintype D] [Encodable D] [Fintype R] [Encodable R] [DecidableEq K]
    (name : X × D ≃ Fin n) (roots : RootAlphabet K R) (A : X → D → K) :
    (∀ P ∈ optimizedProductPrograms name roots,
      PolynomialPrograms.eval (fun j => A (name.symm j).1 (name.symm j).2) P = 0) ↔
      ∃ c : Certificate X D R, c.Retained roots ∧ Satisfies roots c A := by
  unfold optimizedProductPrograms
  rw [simplifiedBranchProducts_zero_iff]
  constructor
  · rintro ⟨E,hE,hzero⟩
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hE
    exact ⟨c,(mem_retainedCertificateList roots c).mp hc,
      (branchProgram_zero_iff name roots c _ (mem_enumerateFinite _) A).mp hzero⟩
  · rintro ⟨c,hc,hzero⟩
    exact ⟨branchProgram name roots c (enumerateFinite (EquationIndex X D)),
      List.mem_map.mpr ⟨c,(mem_retainedCertificateList roots c).mpr hc,rfl⟩,
      (branchProgram_zero_iff name roots c _ (mem_enumerateFinite _) A).mpr hzero⟩

end ComplexCSP.Certificates
