import ComplexCSP.Instances.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Equivalence with the paper's ordered-variable presentation

All variables of an ordered instance are `Fin n`. Its first `r` variables are
retained, and the remaining `h` variables are summed, where `n = r + h`.
This is exactly the partial marginal in Section 2.2. A list retains all constraint
multiplicities and scopes remain allowed to repeat indices.
-/
namespace ComplexCSP

variable {D K ι : Type} {L : Language D K ι}

structure OrderedInstance (L : Language D K ι) (n : ℕ) where
  constraints : List (Constraint L (Fin n))

namespace OrderedInstance
variable {r h : ℕ}

/-- The ordinary all-variable product in an ordered constraint instance. -/
def eval [CommMonoid K] {n : ℕ} (I : OrderedInstance L n) (a : Fin n → D) : K :=
  (I.constraints.map (fun c => c.eval a)).prod

/-- Keep the first `r` variables and sum all assignments of the final `h`.
`finSumFinEquiv` sends left indices to their unchanged initial positions and
right indices to their offset final positions. -/
def marginal [CommSemiring K] [Fintype D] (I : OrderedInstance L (r + h))
    (a : Fin r → D) : K :=
  ∑ b : Fin h → D, I.eval (Sum.elim a b ∘ finSumFinEquiv.symm)

def split (I : OrderedInstance L (r + h)) : Instance L (Fin r) (Fin h) :=
  ⟨I.constraints.map (fun c => c.rename finSumFinEquiv.symm)⟩

@[simp] theorem eval_split [CommMonoid K] (I : OrderedInstance L (r + h))
    (a : Fin r → D) (b : Fin h → D) :
    I.split.eval a b = I.eval (Sum.elim a b ∘ finSumFinEquiv.symm) := by
  simp only [Instance.eval, split, List.map_map, eval]
  rfl

@[simp] theorem partition_split [CommSemiring K] [Fintype D]
    (I : OrderedInstance L (r + h)) (a : Fin r → D) :
    I.split.partition a = I.marginal a := by
  simp only [Instance.partition, eval_split, marginal]

end OrderedInstance

namespace Instance
variable {r h : ℕ}

/-- Flatten separate boundary/hidden indices into one ordered variable list. -/
def flatten (I : Instance L (Fin r) (Fin h)) : OrderedInstance L (r + h) :=
  ⟨I.constraints.map (fun c => c.rename finSumFinEquiv)⟩

@[simp] theorem eval_flatten [CommMonoid K] (I : Instance L (Fin r) (Fin h))
    (a : Fin r → D) (b : Fin h → D) :
    I.flatten.eval (Sum.elim a b ∘ finSumFinEquiv.symm) = I.eval a b := by
  simp only [OrderedInstance.eval, flatten, List.map_map, eval]
  congr 2
  funext c
  simp only [Function.comp_apply, Constraint.eval_rename]
  congr 1
  funext x
  simp

@[simp] theorem marginal_flatten [CommSemiring K] [Fintype D]
    (I : Instance L (Fin r) (Fin h)) (a : Fin r → D) :
    I.flatten.marginal a = I.partition a := by
  simp only [OrderedInstance.marginal, eval_flatten, partition]

end Instance

/-- The paper's generated family, in one fixed external arity. For `r ≥ 1`,
the total variable set is nonempty as required in the paper. -/
def PaperGenerated [CommSemiring K] [Fintype D] {r : ℕ}
    (L : Language D K ι) (G : (Fin r → D) → K) : Prop :=
  ∃ h : ℕ, ∃ I : OrderedInstance L (r + h), ∀ a, I.marginal a = G a

/-- Exact equivalence between the internal finite-instance presentation and the
paper's ordered constraint instance followed by partial summation. -/
theorem generated_iff_paperGenerated [CommSemiring K] [Fintype D] {r : ℕ}
    (G : (Fin r → D) → K) : Instance.Generated L G ↔ PaperGenerated L G := by
  constructor
  · rintro ⟨h, I, hI⟩
    exact ⟨h, I.flatten, fun a => by simpa using hI a⟩
  · rintro ⟨h, I, hI⟩
    exact ⟨h, I.split, fun a => by simpa using hI a⟩

/-- Paper Lemma 3.3 with its actual ordered generated-family semantics.
The paper's positive arity, bound, and surjectivity hypotheses can be supplied;
the constructive statement is stronger and permits legal isolated variables. -/
theorem paper_generated_diagonal_minor [CommSemiring K] [Fintype D] {r s : ℕ}
    {G : (Fin r → D) → K} (hG : PaperGenerated L G) (π : Fin r → Fin s) :
    PaperGenerated L (fun a => G (a ∘ π)) := by
  apply (generated_iff_paperGenerated _).mp
  exact Instance.generated_diagonal_minor ((generated_iff_paperGenerated _).mpr hG) π

/-- Paper Lemma 8.1 with the literal generated-family semantics. -/
theorem paper_generated_pow [CommSemiring K] [Fintype D] {r : ℕ}
    {G : (Fin r → D) → K} (hG : PaperGenerated L G) (n : ℕ) :
    PaperGenerated L (fun a => G a ^ n) := by
  apply (generated_iff_paperGenerated _).mp
  exact Instance.generated_pow ((generated_iff_paperGenerated _).mpr hG) n

end ComplexCSP
