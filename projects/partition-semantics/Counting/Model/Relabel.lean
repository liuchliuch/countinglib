import Counting.Model.Basic

/-!
# Renaming and degenerate cases for open instances

The boundary and hidden-variable renaming constructions and their semantic
proofs adapt `ComplexCSP/Instances/Basic.lean`. The present interface permits
empty domains and nullary signatures; none of the proofs needs positivity or
nonemptiness. Occurrence permutations preserve evaluation but multiplicity is
retained. The empty-instance formula explicitly counts isolated hidden variables.
-/

namespace Counting.Model.OpenInstance

variable {D R ι B C H H₁ H₂ : Type} {L : Language D R ι}

/-- Rename boundary variables, retaining labels, ordered ports and hidden variables.
The map may identify boundary variables or leave new boundary variables isolated. -/
def renameBoundary (I : OpenInstance L B H) (f : B → C) : OpenInstance L C H :=
  ⟨I.occurrences.map (fun c => c.rename (Sum.map f id))⟩

@[simp] theorem eval_renameBoundary [CommMonoid R]
    (I : OpenInstance L B H) (f : B → C) (a : C → D) (b : H → D) :
    (I.renameBoundary f).eval a b = I.eval (a ∘ f) b := by
  simp only [eval, renameBoundary, List.map_map]
  congr 2
  funext c
  simp only [Function.comp_apply, Occurrence.eval_rename]
  congr 1
  funext v
  cases v <;> rfl

/-- Boundary identification is assignment pullback. No surjectivity is needed. -/
@[simp] theorem partition_renameBoundary [CommSemiring R] [Fintype D]
    [Fintype H] [DecidableEq H]
    (I : OpenInstance L B H) (f : B → C) (a : C → D) :
    (I.renameBoundary f).partition a = I.partition (a ∘ f) := by
  simp only [partition, eval_renameBoundary]

/-- Rename hidden variables without changing labels, port order or multiplicity.
A general map need not preserve the partition table. -/
def renameHidden (I : OpenInstance L B H₁) (f : H₁ → H₂) : OpenInstance L B H₂ :=
  ⟨I.occurrences.map (fun c => c.rename (Sum.map id f))⟩

@[simp] theorem eval_renameHidden [CommMonoid R]
    (I : OpenInstance L B H₁) (f : H₁ → H₂) (a : B → D) (b : H₂ → D) :
    (I.renameHidden f).eval a b = I.eval a (b ∘ f) := by
  simp only [eval, renameHidden, List.map_map]
  congr 2
  funext c
  simp only [Function.comp_apply, Occurrence.eval_rename]
  congr 1
  funext v
  cases v <;> rfl

/-- A bijective hidden-variable renaming preserves the complete partition table. -/
theorem partition_renameHidden_equiv [CommSemiring R] [Fintype D]
    [Fintype H₁] [Fintype H₂] [DecidableEq H₁] [DecidableEq H₂]
    (I : OpenInstance L B H₁) (e : H₁ ≃ H₂) (a : B → D) :
    (I.renameHidden e).partition a = I.partition a := by
  simp only [partition, eval_renameHidden]
  exact (Equiv.arrowCongr e (Equiv.refl D)).symm.sum_comp (I.eval a)

/-- Short form of `partition_renameHidden_equiv`. -/
theorem partition_renameHidden [CommSemiring R] [Fintype D]
    [Fintype H₁] [Fintype H₂] [DecidableEq H₁] [DecidableEq H₂]
    (I : OpenInstance L B H₁) (e : H₁ ≃ H₂) (a : B → D) :
    (I.renameHidden e).partition a = I.partition a :=
  partition_renameHidden_equiv I e a

/-- An instance with no occurrences, retaining its declared variable types. -/
def empty (L : Language D R ι) (B H : Type) : OpenInstance L B H := ⟨[]⟩

@[simp] theorem eval_empty [CommMonoid R] (a : B → D) (b : H → D) :
    (empty L B H).eval a b = 1 := rfl

/-- Every hidden variable, including an isolated variable, contributes a free
choice of domain element. This includes `0 ^ 0 = 1` when both types are empty. -/
@[simp] theorem partition_empty [CommSemiring R] [Fintype D] [Fintype H]
    [DecidableEq H] (a : B → D) :
    (empty L B H).partition a = (Fintype.card D : R) ^ Fintype.card H := by
  simp [partition]

/-- If the hidden type is empty, its unique assignment contributes one summand.
The chosen assignment is arbitrary, so this statement needs no domain element. -/
theorem partition_of_isEmpty [CommSemiring R] [Fintype D] [Fintype H]
    [DecidableEq H] [IsEmpty H]
    (I : OpenInstance L B H) (a : B → D) (b : H → D) :
    I.partition a = I.eval a b := by
  simp only [partition, Fintype.sum_unique]
  congr 1
  exact Subsingleton.elim _ _

/-- The canonical no-hidden-variable formula. -/
@[simp] theorem partition_noHidden [CommSemiring R] [Fintype D]
    (I : OpenInstance L B Empty) (a : B → D) :
    I.partition a = I.eval a Empty.elim :=
  partition_of_isEmpty I a Empty.elim

/-- Reordering occurrences preserves their product and retains repeated factors. -/
theorem eval_eq_of_perm [CommMonoid R] {I J : OpenInstance L B H}
    (h : I.occurrences.Perm J.occurrences) (a : B → D) (b : H → D) :
    I.eval a b = J.eval a b := by
  exact (h.map (fun c => c.eval (Sum.elim a b))).prod_eq

/-- Reordering the occurrence list preserves every pinned partition value. -/
theorem partition_eq_of_perm [CommSemiring R] [Fintype D] [Fintype H]
    [DecidableEq H] {I J : OpenInstance L B H}
    (h : I.occurrences.Perm J.occurrences) (a : B → D) :
    I.partition a = J.partition a := by
  unfold partition
  exact Finset.sum_congr rfl (fun b _ => eval_eq_of_perm h a b)

end Counting.Model.OpenInstance
