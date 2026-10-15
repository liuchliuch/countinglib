import Counting.Algorithm.CPOG.Evaluator
import Counting.Algorithm.CPOG.Representation
import Counting.Algorithm.CPOG.FiniteSemantics

/-! The correctness bridge consumes an equality in the original upstream PropFun
semantics. A full certificate checker can supply such an equality, but no checker
or parser is implemented or assumed to exist in this component. -/
namespace Counting.Algorithm.CPOG
open LeanSAT Model
open FiniteSemantics
open scoped BigOperators

/-- The actual original CNF equality implies pointwise agreement on all declared assignments. -/
theorem eval_of_compiled_equivalence {n : Nat} (F : CNF.Formula n) (pog : Pog) (root : ILit)
    (heq : F.toICnf.toPropFun = (⟦pog.toPropForm root⟧ : PropFun Var))
    (a : Fin n → Bool) : (pog.toPropForm root).eval (extend a) = F.eval a := by
  have h := PropFun.exact ((LeanSAT.Cnf.mk_toPropForm F.toICnf).trans heq)
  rw [← h (extend a), CNF.formula_eval]
  simp only [extend_at]

/-- Supplied compiled POG evaluation equals the occurrence-preserving S1 model count.
Partitioning and support coverage are independent hypotheses, as in the original counter. -/
theorem countRoot_eq_partition {n : Nat} (F : CNF.Formula n) (pog : Pog) (root : ILit)
    (hvars : (pog.toPropForm root).vars ⊆ declared n)
    (hpart : partitioned (pog.toPropForm root))
    (heq : F.toICnf.toPropFun = (⟦pog.toPropForm root⟧ : PropFun Var)) :
    countRoot pog n root = F.toInstance.partition Empty.elim := by
  calc
    countRoot pog n root = ((pog.toPropForm root).models (declared n)).card := by
      simpa only [declared_card] using countRoot_eq_models pog root (declared n) hvars hpart
    _ = ∑ a : Fin n → Bool, if (pog.toPropForm root).eval (extend a) then 1 else 0 :=
      models_card_eq_sum n _
    _ = F.toInstance.partition Empty.elim := by
      rw [CNF.Formula.partition_eq_sum]
      simp only [eval_of_compiled_equivalence F pog root heq]

/-- The same actual array evaluator computes complementary-weight S1 partitions.
Weights may be negative or zero. Each declared variable contributes one unary occurrence. -/
theorem ringRoot_eq_partition {R : Type} [CommRing R] {n : Nat}
    (F : CNF.Formula n) (pog : Pog) (root : ILit) (w : Var → R)
    (hvars : (pog.toPropForm root).vars ⊆ declared n)
    (hpart : partitioned (pog.toPropForm root))
    (heq : F.toICnf.toPropFun = (⟦pog.toPropForm root⟧ : PropFun Var)) :
    ringRoot pog w root =
      (F.weightedInstance (fun i => w (Nat.succPNat i.val))).partition Empty.elim := by
  rw [ringRoot_eq_weightSum pog w root (declared n) hvars hpart,
    weightSum_eq_sum, CNF.Formula.weighted_partition_eq_sum]
  simp only [eval_of_compiled_equivalence F pog root heq]

end Counting.Algorithm.CPOG
