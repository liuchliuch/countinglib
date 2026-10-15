import ComplexCSP.Recognition.CertificateAlgebra
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.Powerset

/-!
# Finite Block Orthogonality certificate branches

Rectangles are encoded by shared finite labels: row labels and column labels
are finite column subsets, and the empty label permits no entries. Equal
nonempty labels specify disjoint rectangles. All entries within a certified
rectangle may still vanish. Pair data specifies twisted minors and either
dependent mode or root-anchored groups. Equations below are actual unbarred
multivariate polynomials, not a predicate postulating Block Orthogonality.
-/

namespace ComplexCSP.Certificates

open scoped BigOperators

/-- A finite alphabet of field roots, including one and a conjugation lookup.
The realization laws are stated separately when complex semantics are used. -/
structure RootAlphabet (K R : Type*) [One K] where
  value : R → K
  one : R
  conj : R → R
  value_one : value one = 1

/-- All choices for one row pair. `dependent = true` selects ordinary minors;
otherwise `group` maps every column to its certified anchor. -/
structure PairData (D R : Type*) where
  dependent : Bool
  twist : D → D → R
  group : D → D
  firstRoot : D → R
  secondRoot : D → R

instance {D R : Type*} [Fintype D] [DecidableEq D] [Fintype R] : Fintype (PairData D R) :=
  Fintype.ofEquiv (Bool × (D → D → R) × (D → D) × (D → R) × (D → R))
    { toFun := fun p ↦ ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
      invFun := fun p ↦ ⟨p.dependent, p.twist, p.group, p.firstRoot, p.secondRoot⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- Shared nonempty labels describe pairwise disjoint certified rectangles.
Labels with no rows or no columns are harmless empty rectangles. -/
structure Certificate (X D R : Type*) where
  rowLabel : X → Finset D
  columnLabel : D → Finset D
  pair : X → X → PairData D R

instance {X D R : Type*} [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]
    [Fintype R] : Fintype (Certificate X D R) :=
  Fintype.ofEquiv ((X → Finset D) × (D → Finset D) × (X → X → PairData D R))
    { toFun := fun p ↦ ⟨p.1, p.2.1, p.2.2⟩
      invFun := fun p ↦ ⟨p.rowLabel, p.columnLabel, p.pair⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

namespace Certificate

variable {X D R K : Type*}

def Allowed (c : Certificate X D R) (x : X) (z : D) : Prop :=
  c.rowLabel x ≠ ∅ ∧ c.rowLabel x = c.columnLabel z

def SameRectangle (c : Certificate X D R) (x y : X) : Prop :=
  c.rowLabel x ≠ ∅ ∧ c.rowLabel x = c.rowLabel y

instance [DecidableEq D] (c : Certificate X D R) (x : X) (z : D) :
    Decidable (c.Allowed x z) := inferInstanceAs (Decidable (_ ∧ _))

instance [DecidableEq D] (c : Certificate X D R) (x y : X) :
    Decidable (c.SameRectangle x y) := inferInstanceAs (Decidable (_ ∧ _))

def columns [Fintype D] [DecidableEq D] (c : Certificate X D R) (x : X) : Finset D :=
  Finset.univ.filter (c.Allowed x)

@[simp] theorem mem_columns [Fintype D] [DecidableEq D]
    (c : Certificate X D R) (x : X) (z : D) : z ∈ c.columns x ↔ c.Allowed x z := by
  simp [columns]

theorem allowed_other_row (c : Certificate X D R) {x y : X} {z : D}
    (hxy : c.SameRectangle x y) (hxz : c.Allowed x z) : c.Allowed y z := by
  exact ⟨hxy.2 ▸ hxy.1, hxy.2.symm.trans hxz.2⟩

theorem sameRectangle_of_overlap (c : Certificate X D R) {x y : X} {z : D}
    (hxz : c.Allowed x z) (hyz : c.Allowed y z) : c.SameRectangle x y :=
  ⟨hxz.1, hxz.2.trans hyz.2.symm⟩

/-- Retention is a finite check involving only discrete group consistency and
root sums. It never inspects a candidate table or assumes that table is BO. -/
def Retained [Fintype D] [DecidableEq D] [CommSemiring K]
    (roots : RootAlphabet K R) (c : Certificate X D R) : Prop :=
  ∀ x y, c.SameRectangle x y → (c.pair x y).dependent = false →
    (∀ z, c.Allowed x z → c.Allowed x ((c.pair x y).group z)) ∧
    (∀ z, c.Allowed x z → (c.pair x y).group ((c.pair x y).group z) =
      (c.pair x y).group z) ∧
    (∀ z, c.Allowed x z → roots.value ((c.pair x y).firstRoot ((c.pair x y).group z)) = 1 ∧
      roots.value ((c.pair x y).secondRoot ((c.pair x y).group z)) = 1) ∧
    ∀ g, (∑ z ∈ (c.columns x).filter (fun z ↦ (c.pair x y).group z = g),
      roots.value ((c.pair x y).firstRoot z) *
      roots.value (roots.conj ((c.pair x y).secondRoot z))) = 0

instance [Fintype X] [Fintype D] [DecidableEq D] [CommSemiring K] [DecidableEq K]
    (roots : RootAlphabet K R) (c : Certificate X D R) : Decidable (c.Retained roots) := by
  unfold Retained
  infer_instance

/-- All retained branches are genuinely finite and can be enumerated from exact
root arithmetic. -/
def retainedBranches [Fintype X] [DecidableEq X] [Fintype D] [Fintype R] [DecidableEq D]
    [CommSemiring K] [DecidableEq K] (roots : RootAlphabet K R) :
    Finset (Certificate X D R) := Finset.univ.filter (fun c ↦ c.Retained roots)

end Certificate

/-- The five concrete polynomial-equation forms from Section 4.2. -/
inductive EquationIndex (X D : Type*)
  | support (x : X) (z : D)
  | twisted (x y : X) (z w : D)
  | ordinary (x y : X) (z w : D)
  | firstAnchor (x y : X) (z : D)
  | secondAnchor (x y : X) (z : D)
  deriving Fintype

open MvPolynomial

/-- Every enabled equation is homogeneous of degree one or two in the original
unbarred table coordinates. Disabled equations are represented by zero. -/
noncomputable def equation {X D R K : Type*} [DecidableEq D] [CommRing K]
    (roots : RootAlphabet K R) (c : Certificate X D R) :
    EquationIndex X D → MvPolynomial (X × D) K
  | .support x z => if c.Allowed x z then 0 else MvPolynomial.X (x, z)
  | .twisted x y z w =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ c.Allowed x w then
        MvPolynomial.X (x, z) * MvPolynomial.X (y, w) - C (roots.value ((c.pair x y).twist z w)) *
          (MvPolynomial.X (x, w) * MvPolynomial.X (y, z)) else 0
  | .ordinary x y z w =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ c.Allowed x w ∧
          (c.pair x y).dependent = true then
        MvPolynomial.X (x, z) * MvPolynomial.X (y, w) - MvPolynomial.X (x, w) * MvPolynomial.X (y, z) else 0
  | .firstAnchor x y z =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ (c.pair x y).dependent = false then
        MvPolynomial.X (x, z) - C (roots.value ((c.pair x y).firstRoot z)) *
          MvPolynomial.X (x, (c.pair x y).group z) else 0
  | .secondAnchor x y z =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ (c.pair x y).dependent = false then
        MvPolynomial.X (y, z) - C (roots.value ((c.pair x y).secondRoot z)) *
          MvPolynomial.X (y, (c.pair x y).group z) else 0

/-- The common zero locus of the actual branch polynomials. -/
def Satisfies {X D R K : Type*} [DecidableEq D] [CommRing K]
    (roots : RootAlphabet K R) (c : Certificate X D R) (A : X → D → K) : Prop :=
  ∀ i, MvPolynomial.eval (fun p : X × D ↦ A p.1 p.2) (equation roots c i) = 0

theorem satisfies_zero {X D R K : Type*} [DecidableEq D] [CommRing K]
    (roots : RootAlphabet K R) (c : Certificate X D R) :
    Satisfies roots c (fun _ _ ↦ 0) := by
  intro i
  cases i <;> simp only [equation] <;> split_ifs <;> simp

/-- Direct executable evaluation of the finite equation syntax. Polynomial
semantics are noncomputable in mathlib, but this evaluator uses only the supplied
ring operations and discrete equality decisions. -/
def equationValue {X D R K : Type*} [DecidableEq D] [CommRing K]
    (roots : RootAlphabet K R) (c : Certificate X D R) (A : X → D → K) :
    EquationIndex X D → K
  | .support x z => if c.Allowed x z then 0 else A x z
  | .twisted x y z w =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ c.Allowed x w then
        A x z * A y w - roots.value ((c.pair x y).twist z w) * (A x w * A y z) else 0
  | .ordinary x y z w =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ c.Allowed x w ∧
          (c.pair x y).dependent = true then
        A x z * A y w - A x w * A y z else 0
  | .firstAnchor x y z =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ (c.pair x y).dependent = false then
        A x z - roots.value ((c.pair x y).firstRoot z) * A x ((c.pair x y).group z) else 0
  | .secondAnchor x y z =>
      if c.SameRectangle x y ∧ c.Allowed x z ∧ (c.pair x y).dependent = false then
        A y z - roots.value ((c.pair x y).secondRoot z) * A y ((c.pair x y).group z) else 0

theorem eval_equation_eq {X D R K : Type*} [DecidableEq D] [CommRing K]
    (roots : RootAlphabet K R) (c : Certificate X D R) (A : X → D → K)
    (i : EquationIndex X D) :
    MvPolynomial.eval (fun p : X × D ↦ A p.1 p.2) (equation roots c i) =
      equationValue roots c A i := by
  cases i <;> simp only [equation, equationValue] <;> split_ifs <;> simp

theorem satisfies_iff_equationValues {X D R K : Type*} [DecidableEq D] [CommRing K]
    (roots : RootAlphabet K R) (c : Certificate X D R) (A : X → D → K) :
    Satisfies roots c A ↔ ∀ i, equationValue roots c A i = 0 := by
  simp only [Satisfies, eval_equation_eq]

section Consequences

variable {X D R K : Type*} [DecidableEq D] [CommRing K]
variable {roots : RootAlphabet K R} {c : Certificate X D R} {A : X → D → K}
variable (hA : Satisfies roots c A)
include hA

theorem support_zero (x : X) (z : D) (h : ¬ c.Allowed x z) : A x z = 0 := by
  have hh := (satisfies_iff_equationValues roots c A).mp hA (.support x z)
  simpa only [equationValue, if_neg h] using hh

theorem nonzero_allowed (x : X) (z : D) (h : A x z ≠ 0) : c.Allowed x z := by
  by_contra hn
  exact h (support_zero hA x z hn)

theorem twisted_minor (x y : X) (z w : D)
    (hxy : c.SameRectangle x y) (hz : c.Allowed x z) (hw : c.Allowed x w) :
    A x z * A y w = roots.value ((c.pair x y).twist z w) * (A x w * A y z) := by
  have hh := (satisfies_iff_equationValues roots c A).mp hA (.twisted x y z w)
  simpa only [equationValue, hxy, hz, hw, and_self, if_true, sub_eq_zero] using hh

theorem ordinary_minor (x y : X) (z w : D)
    (hxy : c.SameRectangle x y) (hz : c.Allowed x z) (hw : c.Allowed x w)
    (hd : (c.pair x y).dependent = true) : A x z * A y w = A x w * A y z := by
  have hh := (satisfies_iff_equationValues roots c A).mp hA (.ordinary x y z w)
  simpa only [equationValue, hxy, hz, hw, hd, and_self, if_true, sub_eq_zero] using hh

theorem first_anchor (x y : X) (z : D)
    (hxy : c.SameRectangle x y) (hz : c.Allowed x z)
    (hd : (c.pair x y).dependent = false) :
    A x z = roots.value ((c.pair x y).firstRoot z) * A x ((c.pair x y).group z) := by
  have hh := (satisfies_iff_equationValues roots c A).mp hA (.firstAnchor x y z)
  simpa only [equationValue, hxy, hz, hd, and_self, if_true, sub_eq_zero] using hh

theorem second_anchor (x y : X) (z : D)
    (hxy : c.SameRectangle x y) (hz : c.Allowed x z)
    (hd : (c.pair x y).dependent = false) :
    A y z = roots.value ((c.pair x y).secondRoot z) * A y ((c.pair x y).group z) := by
  have hh := (satisfies_iff_equationValues roots c A).mp hA (.secondAnchor x y z)
  simpa only [equationValue, hxy, hz, hd, and_self, if_true, sub_eq_zero] using hh

end Consequences

/-- Realization laws for the finite root alphabet in the complex numbers. -/
structure ComplexRealization {K R : Type*} [Field K] (roots : RootAlphabet K R) where
  hom : K →+* ℂ
  norm_root : ∀ r, ‖hom (roots.value r)‖ = 1
  conj_root : ∀ r, hom (roots.value (roots.conj r)) = star (hom (roots.value r))

/-- Exact local entry tests supplied by intrinsic purification. None of these
fields states Block Orthogonality, certificate existence, or the desired locus
equality. Constructing this interface from legal generators is separate. -/
structure IntrinsicTests {X D R K : Type*} [Field K]
    (roots : RootAlphabet K R) (realize : ComplexRealization roots)
    (A : X → D → K) (P : X → D → ℂ) : Prop where
  zero : ∀ x z, P x z = 0 ↔ A x z = 0
  ordinary_minor : ∀ x y z w,
    P x z * P y w = P x w * P y z ↔ A x z * A y w = A x w * A y z
  magnitude_minor : ∀ x y z w,
    ‖P x z * P y w‖ = ‖P x w * P y z‖ ↔
      ∃ r, A x z * A y w = roots.value r * (A x w * A y z)
  root_covariance : ∀ x z w r, A x z = roots.value r * A x w →
    P x z = realize.hom (roots.value r) * P x w
  magnitude_anchor : ∀ x z w, A x w ≠ 0 →
    (‖P x z‖ = ‖P x w‖ ↔ ∃ r, A x z = roots.value r * A x w)

end ComplexCSP.Certificates
