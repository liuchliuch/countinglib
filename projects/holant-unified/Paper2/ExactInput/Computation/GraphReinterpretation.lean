import Paper2.ExactInput.Computation.HolographicSemantics
import Paper2.Problem

/-! Reinterpret one validated raw graph under indexed tables with the same count
and arity function. Its serialization, endpoint order, loops, multiplicity and
nullary vertices are unchanged. -/
namespace Paper2.ExactInput.Computation
open Paper2.Complexity Paper2.Tractable

/-- Only validation proofs are transported; the raw graph record is identical. -/
def reinterpret {s t e : ℕ} {a b : ℕ → ℕ} (hs : s = t) (ha : a = b)
    (G : {r : RawClosedNetwork // r.WellFormed s e a}) :
    {r : RawClosedNetwork // r.WellFormed t e b} :=
  ⟨G.val, by simpa only [← hs, ← ha] using G.property⟩

@[simp] theorem reinterpret_raw {s t e : ℕ} {a b : ℕ → ℕ} (hs : s = t) (ha : a = b)
    (G : {r : RawClosedNetwork // r.WellFormed s e a}) :
    (reinterpret hs ha G).val = G.val := rfl

@[simp] theorem reinterpret_bytes {s t e : ℕ} {a b : ℕ → ℕ} (hs : s = t) (ha : a = b)
    (G : {r : RawClosedNetwork // r.WellFormed s e a}) :
    ((RawClosedNetwork.validatedEncoding t e b).encode (reinterpret hs ha G)) =
      (RawClosedNetwork.validatedEncoding s e a).encode G := rfl

/-- The reinterpretation is a genuine bijection on valid original graph records. -/
def reinterpretEquiv {s t e : ℕ} {a b : ℕ → ℕ} (hs : s = t) (ha : a = b) :
    {r : RawClosedNetwork // r.WellFormed s e a} ≃
      {r : RawClosedNetwork // r.WellFormed t e b} where
  toFun := reinterpret hs ha
  invFun := reinterpret hs.symm ha.symm
  left_inv G := Subtype.ext rfl
  right_inv G := Subtype.ext rfl

/-- A fully proved semantic transport on precisely that same serialized graph.
The explicit inverse matrices and edge pullbacks account for every incidence. -/
theorem reinterpret_denote {K : Type*} [CommSemiring K]
    {s t e : ℕ} {a b : ℕ → ℕ} (hs : s = t) (ha : a = b)
    (G : {r : RawClosedNetwork // r.WellFormed s e a})
    (f : (i : Fin s) → Signature K (a i.val))
    (g : (i : Fin t) → Signature K (b i.val))
    (E D : Fin e → Kernel K) (M N : Kernel K)
    (hMN : Kernel.mul M N = Signature.equality)
    (hvertex : ∀ i, HEq (g (Fin.cast hs i))
      (Signature.coordinateAction (fun _ => N) (f i)))
    (hedge : ∀ j, D j = Kernel.pullback (E j) M) :
    ((reinterpret hs ha G).val.realize (reinterpret hs ha G).property g D).denote =
      (G.val.realize G.property f E).denote := by
  cases hs
  cases ha
  have hg : g = fun i => Signature.coordinateAction (fun _ => N) (f i) := by
    funext i
    exact eq_of_heq (hvertex i)
  have hD : D = fun j => Kernel.pullback (E j) M := funext hedge
  subst g
  subst D
  exact Network.denote_holographicTransform (G.val.realize G.property f E) M N hMN

end Paper2.ExactInput.Computation
