import ComplexCSP.Algebra.GramGadget
import ComplexCSP.Instances.PresentationAlgorithms

/-! # The directed two-power Gram gadget

The same construction covers the absolute Gram matrix and the phase detector
A_t(u,v) = sum_z F(u,z) F(v,z)^(tK-1). Exponents are fixed gadget constants.
-/
namespace ComplexCSP.GramPowerGadget
open scoped BigOperators
variable {D K : Type} {r : ℕ}

/-- A literal two-port matrix language on tuple-valued graph colors. -/
def matrixLanguage (A : (Fin r → D) → (Fin r → D) → K) :
    Language (Fin r → D) K (Fin 1) :=
  ⟨fun _ => 2, fun _ => Nat.zero_lt_succ 1, fun _ a => A (a 0) (a 1)⟩

def matrix [Fintype D] [CommSemiring K] (F : (Fin (r+1) → D) → K) (p q : ℕ)
    (a b : Fin r → D) : K := ∑ z, GramGadget.row F a z ^ p * GramGadget.row F b z ^ q

/-- One edge endpoint shares precisely its r coordinate variables. -/
def edgeConstraint (F : (Fin (r+1) → D) → K) (v : Fin 2) :
    Constraint (GramGadget.language F) (Fin (2*r) ⊕ Fin 1) :=
  ⟨0,Fin.snoc (fun k => Sum.inl (finProdFinEquiv (v,k))) (Sum.inr 0)⟩

def gadget (F : (Fin (r+1) → D) → K) (p q : ℕ) :
    Presentation (GramGadget.language F) (Fin (2*r)) :=
  ⟨1,⟨List.replicate p (edgeConstraint F 0) ++ List.replicate q (edgeConstraint F 1)⟩⟩

@[simp] theorem constraints_length (F : (Fin (r+1) → D) → K) (p q : ℕ) :
    (gadget F p q).inst.constraints.length = p+q := by simp [gadget]

@[simp] theorem eval_edge [CommMonoid K] (F : (Fin (r+1) → D) → K)
    (v : Fin 2) (a : Fin (2*r) → D) (b : Fin 1 → D) :
    (edgeConstraint F v).eval (Sum.elim a b) =
      GramGadget.row F (fun k => a (finProdFinEquiv (v,k))) (b 0) := by
  unfold edgeConstraint Constraint.eval GramGadget.language GramGadget.row
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i <;> simp

/-- Exact evaluation of the concrete constraint list with multiplicity p+q. -/
theorem table_gadget [Fintype D] [CommSemiring K] (F : (Fin (r+1) → D) → K)
    (p q : ℕ) (a : Fin (2*r) → D) :
    (gadget F p q).table a = matrix F p q
      (fun k => a (finProdFinEquiv (0,k))) (fun k => a (finProdFinEquiv (1,k))) := by
  simp only [Presentation.table,Instance.partition,Instance.eval,gadget,List.map_append,
    List.map_replicate,List.prod_append,List.prod_replicate,eval_edge,matrix]
  exact (Equiv.funUnique (Fin 1) D).sum_comp (fun z =>
    GramGadget.row F (fun k => a (finProdFinEquiv (0,k))) z ^ p *
      GramGadget.row F (fun k => a (finProdFinEquiv (1,k))) z ^ q)

@[simp] theorem matrix_one_one [Fintype D] [CommSemiring K]
    (F : (Fin (r+1) → D) → K) (a b : Fin r → D) :
    matrix F 1 1 a b = GramGadget.gram F a b := by simp [matrix,GramGadget.gram]

end ComplexCSP.GramPowerGadget
