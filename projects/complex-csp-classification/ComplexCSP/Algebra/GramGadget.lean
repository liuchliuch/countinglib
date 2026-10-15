import ComplexCSP.Instances.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Literal Gram gadgets for arbitrary-arity functions

A graph vertex is represented by a tuple of base-domain variables. Each edge
gets one fresh private variable and exactly two copies of the original table.
This is the actual finite construction in Cai–Chen's Lemma 4, without a
homomorphism-hardness hypothesis.
-/
namespace ComplexCSP.GramGadget
open scoped BigOperators
variable {D K : Type} {r : ℕ}

def language (F : (Fin (r+1) → D) → K) : Language D K (Fin 1) :=
  ⟨fun _ => r+1, fun _ => Nat.succ_pos _, fun _ => F⟩

def row (F : (Fin (r+1) → D) → K) (a : Fin r → D) (z : D) : K := F (Fin.snoc a z)

def gram [Fintype D] [CommSemiring K] (F : (Fin (r+1) → D) → K)
    (a b : Fin r → D) : K := ∑ z, row F a z * row F b z

/-- Graph edges have separate indices, so parallel edges and loops are retained. -/
structure Graph (V E : Type) where
  left : E → V
  right : E → V

variable {V : Type} {m : ℕ}

def edgeConstraint (F : (Fin (r+1) → D) → K) (v : V) (e : Fin m) :
    Constraint (language F) ((V × Fin r) ⊕ Fin m) :=
  ⟨0, Fin.snoc (fun k => Sum.inl (v,k)) (Sum.inr e)⟩

def inst (F : (Fin (r+1) → D) → K) (G : Graph V (Fin m)) :
    Instance (language F) (V × Fin r) (Fin m) :=
  ⟨(List.ofFn fun e =>
    [edgeConstraint F (G.left e) e, edgeConstraint F (G.right e) e]).flatten⟩

theorem constraints_length (F : (Fin (r+1) → D) → K) (G : Graph V (Fin m)) :
    (inst F G).constraints.length = 2*m := by
  simp [inst, List.length_flatten, List.sum_ofFn, Nat.mul_comm]

@[simp] theorem eval_edge [CommMonoid K] (F : (Fin (r+1) → D) → K)
    (v : V) (e : Fin m) (a : V × Fin r → D) (b : Fin m → D) :
    (edgeConstraint F v e).eval (Sum.elim a b) = row F (fun k => a (v,k)) (b e) := by
  unfold Constraint.eval edgeConstraint language row
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i <;> simp

theorem eval_instance [CommMonoid K] (F : (Fin (r+1) → D) → K)
    (G : Graph V (Fin m)) (a : V × Fin r → D) (b : Fin m → D) :
    (inst F G).eval a b =
      ∏ e, row F (fun k => a (G.left e,k)) (b e) *
        row F (fun k => a (G.right e,k)) (b e) := by
  simp [Instance.eval,inst,List.map_flatten,List.prod_flatten,List.map_ofFn,
    List.prod_ofFn]

/-- Summing the fresh edge variables gives exactly the Gram edge product. -/
theorem partition_instance [Fintype D] [CommSemiring K]
    (F : (Fin (r+1) → D) → K) (G : Graph V (Fin m)) (a : V × Fin r → D) :
    (inst F G).partition a =
      ∏ e, gram F (fun k => a (G.left e,k)) (fun k => a (G.right e,k)) := by
  simp only [Instance.partition,eval_instance,gram]
  exact (Fintype.prod_sum (fun e z => row F (fun k => a (G.left e,k)) z *
    row F (fun k => a (G.right e,k)) z)).symm

/-- The source graph partition is a literal finite sum on tuple-valued vertices. -/
def partition [Fintype V] [DecidableEq V] [Fintype D] [CommSemiring K]
    (A : (Fin r → D) → (Fin r → D) → K) (G : Graph V (Fin m)) : K :=
  ∑ a : V → Fin r → D, ∏ e, A (a (G.left e)) (a (G.right e))

/-- Full partition preservation, including isolated graph vertices. -/
theorem full_partition [Fintype V] [DecidableEq V] [Fintype D] [CommSemiring K]
    (F : (Fin (r+1) → D) → K) (G : Graph V (Fin m)) :
    (∑ a : V × Fin r → D, (inst F G).partition a) = partition (gram F) G := by
  simp only [partition_instance,partition]
  exact (Equiv.curry V (Fin r) D).sum_comp (fun a => ∏ e, gram F (a (G.left e)) (a (G.right e)))

/-- Exact resource count: r variables per old vertex, one per edge, two
constraints per edge, and all repeated positions survive. -/
theorem resource_counts [Fintype V] (F : (Fin (r+1) → D) → K)
    (G : Graph V (Fin m)) :
    Fintype.card ((V × Fin r) ⊕ Fin m) = r*Fintype.card V+m ∧
      (inst F G).constraints.length = 2*m := by
  simp [Fintype.card_sum,Fintype.card_prod,constraints_length,Nat.mul_comm]

end ComplexCSP.GramGadget
