import Paper2.DegreeCSP.GeneratedCoordinateRows

/-! Actual original-table BO implies the singleton-column support rectangle.
This is a consequence of the retained magnitude-proportional row alternative;
it introduces no relational closure or common-operation assumption. -/
namespace Paper2.DegreeCSP.BooleanSupportFromBO
open Tractable OriginalBO
noncomputable section

/-- Three supported corners force the fourth, with empty rows allowed. -/
def Rectangular {X Y : Type} (R : X → Y → Prop) : Prop :=
  ∀ x y a b,R x a → R y a → R x b → R y b

/-- The positive magnitude-row alternative transfers support along a row.
Overlap excludes the other, disjoint-support alternative. -/
theorem support_rectangular {X J : Type} {G : X → J → ℂ}
    (h : BlockRankOne G) : Rectangular (fun x j => G x j≠0) := by
  intro x y a b hxa hya hxb
  have hx : G x≠0 := fun hz => hxa (congrFun hz a)
  have hy : G y≠0 := fun hz => hya (congrFun hz a)
  rcases h x y hx hy with ⟨c,hc,hm⟩ | hd
  · intro hyb
    have he := hm b
    rw [hyb,norm_zero,mul_zero] at he
    exact hxb (norm_eq_zero.mp he)
  · exact False.elim (Set.disjoint_left.mp hd hxa hya)

/-- Exact support rectangles for the literal generated table rows. -/
theorem rows_rectangular {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : AllGeneratedOriginalBO F k) {f : Signature AlgebraicComplex (n+1)}
    (hf : Generated F k f) :
    Rectangular (fun x b => f (Fin.snoc x b)≠0) := by
  have h := support_rectangular (hBO n f hf).1
  unfold Rectangular tableRows at h
  intro x y a b hxa hya hxb
  exact_mod_cast h x y a b (by exact_mod_cast hxa)
    (by exact_mod_cast hya) (by exact_mod_cast hxb)

/-- Any coordinate is a literal retained column, via the proved boundary swap. -/
theorem coordinate_rectangular {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : AllGeneratedOriginalBO F k) {f : Signature AlgebraicComplex (n+1)}
    (hf : Generated F k f) (i : Fin (n+1)) :
    Rectangular (fun x b => f (Function.update x i b)≠0) := by
  have h := support_rectangular (coordinate_rows_bo hBO f hf i).1
  unfold Rectangular coordinateRows at h
  intro x y a b hxa hya hxb
  exact_mod_cast h x y a b (by exact_mod_cast hxa)
    (by exact_mod_cast hya) (by exact_mod_cast hxb)

/-- Literal language members inherit the rectangle through their actual
k-copy presentation. No identification with support indicators is used. -/
theorem original_coordinate_rectangular {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : AllGeneratedOriginalBO F k) (hk : 0<k)
    (f : Signature AlgebraicComplex (n+1))
    (hf : (⟨n+1,f⟩ : AnySignature AlgebraicComplex) ∈ F) (i : Fin (n+1)) :
    Rectangular (fun x b => f (Function.update x i b)≠0) := by
  have h := coordinate_rectangular hBO (generated_power F f hf (dvd_refl k)) i
  intro x y a b hxa hya hxb
  have hr := h x y a b (pow_ne_zero k hxa) (pow_ne_zero k hya) (pow_ne_zero k hxb)
  intro hz
  exact hr (by simp only [hz,zero_pow (Nat.ne_of_gt hk)])

end
end Paper2.DegreeCSP.BooleanSupportFromBO
