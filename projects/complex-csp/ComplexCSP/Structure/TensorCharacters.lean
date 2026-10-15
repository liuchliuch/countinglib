import ComplexCSP.Instances.Basic
import Mathlib.Algebra.Star.Basic

/-!
# Tensor realization of pinned monomial values

Actual tensorized language tables and constraint-instance templates are built
below. The proof rearranges finite assignments, finite products and finite sums;
it does not assume the desired partition factorization as a character axiom.
-/

namespace ComplexCSP

open scoped BigOperators

namespace Language

variable {D K ι J : Type} [CommSemiring K] [Fintype J]

/-- Tensor the table of each language symbol over a finite family of layers.
The endomorphism on a layer can be identity or complex conjugation. -/
def tensor (L : Language D K ι) (φ : J → K →+* K) : Language (J → D) K ι where
  arity := L.arity
  arity_pos := L.arity_pos
  value i a := ∏ j, φ j (L.value i (fun t => a t j))

end Language

namespace Constraint

variable {D K ι J V : Type} [CommSemiring K] [Fintype J]
variable {L : Language D K ι}

/-- Retain the symbol and its complete ordered scope in the tensor language. -/
def tensor (c : Constraint L V) (φ : J → K →+* K) : Constraint (L.tensor φ) V :=
  ⟨c.symbol, c.scope⟩

@[simp] theorem eval_tensor (c : Constraint L V) (φ : J → K →+* K)
    (a : V → J → D) :
    (c.tensor φ).eval a = ∏ j, φ j (c.eval (fun v => a v j)) := rfl

end Constraint

namespace Instance

variable {D K ι J B H : Type} [CommSemiring K] [Fintype J]
variable {L : Language D K ι}

/-- Tensor every constraint while preserving the exact list, all variables,
all label pins, and all scopes (including repetitions). -/
def tensor (I : Instance L B H) (φ : J → K →+* K) : Instance (L.tensor φ) B H :=
  ⟨I.constraints.map (fun c => c.tensor φ)⟩

/-- Factorization of the constraint weight of one tensor-valued assignment. -/
theorem eval_tensor (I : Instance L B H) (φ : J → K →+* K)
    (a : B → J → D) (b : H → J → D) :
    (I.tensor φ).eval a b =
      ∏ j, φ j (I.eval (fun v => a v j) (fun v => b v j)) := by
  have hsplit (j : J) :
      (fun v : B ⊕ H => Sum.elim a b v j) =
        Sum.elim (fun v => a v j) (fun v => b v j) := by
    funext v
    cases v <;> rfl
  cases I with
  | mk cs =>
    induction cs with
    | nil => simp [tensor, eval]
    | cons c cs ih =>
      simp only [tensor, eval, List.map_cons, List.prod_cons, Constraint.eval_tensor,
        hsplit, map_mul, Finset.prod_mul_distrib] at ih ⊢
      exact congrArg (fun z => (∏ j, φ j (c.eval
        (Sum.elim (fun v => a v j) (fun v => b v j)))) * z) ih

/-- Lemma 5.3, at the level of actual finite constraint instances.
The equivalence transposes a tensor assignment `H → J → D` into independent
layer assignments `J → H → D`, then distributivity factors the finite sum. -/
theorem partition_tensor [Fintype D] [Fintype H] [DecidableEq H] [DecidableEq J]
    (I : Instance L B H) (φ : J → K →+* K) (a : B → J → D) :
    (I.tensor φ).partition a =
      ∏ j, φ j (I.partition (fun v => a v j)) := by
  simp only [partition, eval_tensor, map_sum]
  rw [Fintype.prod_sum]
  exact (Equiv.piComm (fun (_ : H) (_ : J) => D)).sum_comp
    (fun b => ∏ j, φ j (I.eval (fun v => a v j) (b j)))

end Instance

section ConjugateLayers

variable {D K ι B H : Type} [CommSemiring K] [StarRing K]
variable {L : Language D K ι}

/-- The first `p` layers use their original values; the last `q` use star.
For `K = ℂ`, star is exactly complex conjugation. -/
def tensorLayerMaps (p q : ℕ) : (Fin p ⊕ Fin q) → K →+* K :=
  Sum.elim (fun _ => RingHom.id K) (fun _ => starRingEnd K)

/-- The paper's `T_{p,q}` table, with coordinates indexed by the disjoint sum
of the original and conjugate layers. -/
def Language.tensorConjugate (L : Language D K ι) (p q : ℕ) :
    Language ((Fin p ⊕ Fin q) → D) K ι :=
  L.tensor (tensorLayerMaps p q)

@[simp] theorem Language.tensorConjugate_value (L : Language D K ι) (p q : ℕ)
    (i : ι) (a : Fin (L.arity i) → (Fin p ⊕ Fin q) → D) :
    (L.tensorConjugate p q).value i a =
      (∏ j, L.value i (fun t => a t (Sum.inl j))) *
      ∏ j, star (L.value i (fun t => a t (Sum.inr j))) := by
  simp [Language.tensorConjugate, Language.tensor, tensorLayerMaps, Fintype.prod_sum_type, starRingEnd_apply]

/-- The actual instance transformation `I ↦ I^M` for `p` direct and `q`
conjugate monomial factors. -/
def Instance.tensorConjugate (I : Instance L B H) (p q : ℕ) :
    Instance (L.tensorConjugate p q) B H :=
  I.tensor (tensorLayerMaps p q)

/-- The pin transposition in Lemma 5.3, including every boundary label. -/
def tensorPins {p q : ℕ} (a : Fin p → B → D) (b : Fin q → B → D) :
    B → (Fin p ⊕ Fin q) → D :=
  fun v => Sum.elim (fun j => a j v) (fun j => b j v)

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 5.3's displayed formula, now for original and conjugate layers.
Both empty products are included, so `p = q = 0` is covered. -/
theorem Instance.partition_tensorConjugate [Fintype D] [Fintype H] [DecidableEq H]
    (I : Instance L B H) (p q : ℕ) (a : Fin p → B → D) (b : Fin q → B → D) :
    (I.tensorConjugate p q).partition (tensorPins a b) =
      (∏ j, I.partition (a j)) * ∏ j, star (I.partition (b j)) := by
  unfold Instance.tensorConjugate
  rw [Instance.partition_tensor, Fintype.prod_sum_type]
  rfl

/-- Degree-zero tensorization has value one, even with hidden variables:
there is exactly one assignment into the zero-fold tensor domain. -/
theorem Instance.partition_tensorConjugate_zero [Fintype D] [Fintype H] [DecidableEq H]
    (I : Instance L B H) :
    (I.tensorConjugate 0 0).partition
      (tensorPins (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)) = 1 := by
  rw [Instance.partition_tensorConjugate]
  simp

end ConjugateLayers

end ComplexCSP
