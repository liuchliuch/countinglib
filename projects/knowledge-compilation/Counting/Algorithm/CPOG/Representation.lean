import Counting.Algorithm.CPOG.CNF
import ProofChecker.Data.Pog

/-! Ordered finite CNF syntax to the upstream integer-literal CNF syntax.
These conversions retain every literal and every clause occurrence. -/
namespace Counting.Algorithm.CPOG
open LeanSAT Model
namespace CNF

/-- Finite variable index `i` is represented by the positive integer `i+1`. -/
def Literal.toILit {n : Nat} (l : Literal n) : ILit :=
  if l.positive then .mkPos (Nat.succPNat l.index.val)
  else .mkNeg (Nat.succPNat l.index.val)

def Clause.toIClause {n : Nat} (C : Clause n) : IClause :=
  (C.map Literal.toILit).toArray

def Formula.toICnf {n : Nat} (F : Formula n) : ICnf :=
  (F.map Clause.toIClause).toArray

@[simp] theorem clause_size {n : Nat} (C : Clause n) : C.toIClause.size = C.length := by
  simp only [Clause.toIClause, List.size_toArray, List.length_map]

@[simp] theorem formula_size {n : Nat} (F : Formula n) : F.toICnf.size = F.length := by
  simp only [Formula.toICnf, List.size_toArray, List.length_map]

theorem literal_eval {n : Nat} (l : Literal n) (τ : PropAssignment Var) :
    (LitVar.toPropForm l.toILit).eval τ = l.apply (τ (Nat.succPNat l.index.val)) := by
  cases hp : l.positive <;> simp [Literal.toILit, hp, Literal.apply,
    LitVar.toPropForm_mkPos, LitVar.toPropForm_mkNeg]

theorem clause_eval {n : Nat} (C : Clause n) (τ : PropAssignment Var) :
    (C.toIClause.toPropForm).eval τ = C.eval (fun i => τ (Nat.succPNat i.val)) := by
  change (List.foldr (fun l φ => (LitVar.toPropForm l).disj φ) PropForm.fls
    (C.map Literal.toILit)).eval τ = C.eval (fun i => τ (Nat.succPNat i.val))
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [List.map_cons, List.foldr_cons, PropForm.eval, literal_eval,
      Clause.eval, List.any_cons, Literal.eval] at ih ⊢
    rw [ih]

theorem formula_eval {n : Nat} (F : Formula n) (τ : PropAssignment Var) :
    F.toICnf.toPropForm.eval τ = F.eval (fun i => τ (Nat.succPNat i.val)) := by
  change (List.foldr (fun C φ => C.toPropForm.conj φ) PropForm.tr
    (F.map Clause.toIClause)).eval τ = F.eval (fun i => τ (Nat.succPNat i.val))
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp only [List.map_cons, List.foldr_cons, PropForm.eval, clause_eval,
      Formula.eval, List.all_cons] at ih ⊢
    rw [ih]

end CNF
end Counting.Algorithm.CPOG
