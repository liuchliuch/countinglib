import ComplexCSP.Structure.SupportRealization

/-! # Executable finite-instance transformations

This is computational data, rather than existential closure interfaces. Hidden
variables have canonical natural-number encodings throughout. The field/ring
operations and exact equality are explicit computational inputs; constructing
them uniformly from algebraic-number encodings is a separate open obligation.
-/
namespace ComplexCSP

variable {D K ι B C : Type} {L : Language D K ι}

/-- A finite presentation of a generated boundary table. -/
structure Presentation (L : Language D K ι) (B : Type) where
  hidden : ℕ
  inst : Instance L B (Fin hidden)

namespace Presentation

def table [CommSemiring K] [Fintype D] (P : Presentation L B) : (B → D) → K :=
  P.inst.partition

theorem table_generated [CommSemiring K] [Fintype D] (P : Presentation L B) :
    Instance.Generated L P.table := ⟨P.hidden, P.inst, fun _ => rfl⟩

/-- Actual external-variable relabeling, retaining a canonical hidden encoding. -/
def rename (P : Presentation L B) (f : B → C) : Presentation L C :=
  ⟨P.hidden, P.inst.renameBoundary f⟩

@[simp] theorem table_rename [CommSemiring K] [Fintype D]
    (P : Presentation L B) (f : B → C) (a : C → D) :
    (P.rename f).table a = P.table (a ∘ f) :=
  Instance.partition_renameBoundary P.inst f a

/-- Empty constraint list; no hidden variables. -/
def one : Presentation L B := ⟨0, ⟨[]⟩⟩

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem table_one [CommSemiring K] [Fintype D] (a : B → D) :
    (one : Presentation L B).table a = 1 := by simp [one, table, Instance.partition, Instance.eval]

/-- Disjoint hidden-variable copies are encoded by the computable sum equivalence. -/
def mul (P Q : Presentation L B) : Presentation L B :=
  ⟨P.hidden + Q.hidden, (P.inst.glue Q.inst).renameHidden finSumFinEquiv⟩

@[simp] theorem table_mul [CommSemiring K] [Fintype D]
    (P Q : Presentation L B) (a : B → D) :
    (P.mul Q).table a = P.table a * Q.table a := by
  unfold table mul
  rw [Instance.partition_renameHidden_equiv, Instance.partition_glue]

/-- Primitive-recursive construction of independent-copy entrywise powers. -/
def power (P : Presentation L B) : ℕ → Presentation L B
  | 0 => one
  | n + 1 => (P.power n).mul P

@[simp] theorem table_power [CommSemiring K] [Fintype D]
    (P : Presentation L B) (n : ℕ) (a : B → D) :
    (P.power n).table a = P.table a ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, pow_succ]

/-- Sequential finite products of presentations. -/
def product : List (Presentation L B) → Presentation L B
  | [] => one
  | P :: Ps => P.mul (product Ps)

@[simp] theorem table_product [CommSemiring K] [Fintype D]
    (Ps : List (Presentation L B)) (a : B → D) :
    (product Ps).table a = (Ps.map (fun P => P.table a)).prod := by
  induction Ps with
  | nil => simp [product]
  | cons P Ps ih => simp [product, ih]

/-- Sum an explicitly encoded retained block, moving it into the hidden indices. -/
def marginal {h : ℕ} (P : Presentation L (B ⊕ Fin h)) : Presentation L B :=
  ⟨h + P.hidden, P.inst.hideBoundary.renameHidden finSumFinEquiv⟩

@[simp] theorem table_marginal [CommSemiring K] [Fintype D] {h : ℕ}
    (P : Presentation L (B ⊕ Fin h)) (a : B → D) :
    P.marginal.table a = ∑ b : Fin h → D, P.table (Sum.elim a b) := by
  unfold marginal table
  rw [Instance.partition_renameHidden_equiv, Instance.partition_hideBoundary]

/-- Compute the support of an existentially quantified table by exact power
search, then build the witnessing finite instance with independent hidden copies. -/
def existentialSupport [Fintype D] [Fintype B] [DecidableEq B]
    [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K] {h : ℕ}
    (P : Presentation L (B ⊕ Fin h)) : Presentation L B :=
  let m := findSupportPower (fun (a : B → D) (b : Fin h → D) => P.table (Sum.elim a b))
  (P.power m).marginal

/-- Correctness of the actual support-realizing compiler. -/
theorem existentialSupport_correct [Fintype D] [Fintype B] [DecidableEq B]
    [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K] {h : ℕ}
    (P : Presentation L (B ⊕ Fin h)) (a : B → D) :
    P.existentialSupport.table a ≠ 0 ↔ ∃ b : Fin h → D, P.table (Sum.elim a b) ≠ 0 := by
  simp only [existentialSupport, table_marginal, table_power]
  exact (findSupportPower_spec (fun (a : B → D) (b : Fin h → D) => P.table (Sum.elim a b))).2 a

end Presentation
/-- One literal equality-free atom, carrying its source generated presentation. -/
structure PresentedAtom (L : Language D K ι) (V : Type) where
  arity : ℕ
  presentation : Presentation L (Fin arity)
  scope : Fin arity → V

namespace PresentedAtom

def lift {V : Type} (A : PresentedAtom L V) : Presentation L V :=
  A.presentation.rename A.scope

/-- The complete equality-free pp compiler for Lemma 7.2. It takes finite
presentations, forms the conjunction, computes a suitable exact amplification
power, and marginalizes the existential variables. -/
def compile [Fintype D] [Fintype B] [DecidableEq B]
    [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K] {h : ℕ}
    (atoms : List (PresentedAtom L (B ⊕ Fin h))) : Presentation L B :=
  (Presentation.product (atoms.map PresentedAtom.lift)).existentialSupport

/-- Soundness and completeness of the actual finite-instance output. -/
theorem compile_correct [Fintype D] [Fintype B] [DecidableEq B]
    [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K] {h : ℕ}
    (atoms : List (PresentedAtom L (B ⊕ Fin h))) (a : B → D) :
    (compile atoms).table a ≠ 0 ↔ ∃ b : Fin h → D,
      ∀ atom ∈ atoms, atom.presentation.table (Sum.elim a b ∘ atom.scope) ≠ 0 := by
  simp only [compile, Presentation.existentialSupport_correct, Presentation.table_product,
    List.map_map]
  simp [lift]

end PresentedAtom

end ComplexCSP
