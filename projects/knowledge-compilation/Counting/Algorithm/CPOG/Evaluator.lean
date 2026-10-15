import ProofChecker.Count.Pog

/-! Literal-root evaluation reuses the imported array algorithms. Graph well-formedness
ensures that array references point backwards. Partitioning and declared-variable
coverage are separate semantic preconditions, supplied to correctness theorems. -/
namespace Counting.Algorithm.CPOG
open LeanSAT Model

/-- Natural model count at a signed root, including negative roots. -/
def countRoot (pog : Pog) (n : Nat) (root : ILit) : Nat :=
  if root.polarity then pog.count n root.var else 2 ^ n - pog.count n root.var

/-- Ring evaluation with complementary weights at a signed root. -/
def ringRoot {R : Type} [CommRing R] (pog : Pog) (w : Var → R) (root : ILit) : R :=
  if root.polarity then pog.ringEval w root.var else 1 - pog.ringEval w root.var

theorem countRoot_eq_countModels (pog : Pog) (n : Nat) (root : ILit) :
    countRoot pog n root = (pog.toPropForm root).countModels n := by
  rcases LitVar.mkPos_or_mkNeg root with h | h <;> rw [h]
  · simp [countRoot, ILit.polarity, ILit.var, Pog.count_eq_countModels]
  · simp [countRoot, ILit.polarity, ILit.var, Pog.count_eq_countModels,
      Pog.toPropForm_neg, PropForm.countModels]

theorem ringRoot_eq_ringEval {R : Type} [CommRing R] (pog : Pog) (w : Var → R)
    (root : ILit) : ringRoot pog w root = (pog.toPropForm root).ringEval w := by
  rcases LitVar.mkPos_or_mkNeg root with h | h <;> rw [h]
  · simp [ringRoot, ILit.polarity, ILit.var, Pog.ringEval_eq_ringEval]
  · simp [ringRoot, ILit.polarity, ILit.var, Pog.ringEval_eq_ringEval,
      Pog.toPropForm_neg, PropForm.ringEval]

theorem countRoot_eq_models (pog : Pog) (root : ILit) (declared : Finset Var)
    (hvars : (pog.toPropForm root).vars ⊆ declared)
    (hpart : partitioned (pog.toPropForm root)) :
    countRoot pog declared.card root = ((pog.toPropForm root).models declared).card := by
  rw [countRoot_eq_countModels]
  exact PropForm.countModels_eq_card_models hvars hpart

theorem ringRoot_eq_weightSum {R : Type} [CommRing R] (pog : Pog) (w : Var → R)
    (root : ILit) (declared : Finset Var)
    (hvars : (pog.toPropForm root).vars ⊆ declared)
    (hpart : partitioned (pog.toPropForm root)) :
    ringRoot pog w root = (pog.toPropForm root).weightSum w declared := by
  rw [ringRoot_eq_ringEval, PropForm.ringEval_eq_weightSum w hpart,
    PropForm.weightSum_of_vars_subset w hvars]

end Counting.Algorithm.CPOG
