import Paper2.DegreeCSP.BooleanOrthogonality

/-! A necessary coefficient constraint from original block orthogonality of
the actual degree-generated family. This is not the full shared-phase
classification: a 2k-th cross-product equality alone does not imply P or A^r_k. -/
namespace Paper2.DegreeCSP.OriginalBO
open Tractable
noncomputable section

def tableRows {n : ℕ} (f : Signature AlgebraicComplex (n + 1))
    (x : Fin n → Bool) (b : Bool) : ℂ := (f (Fin.snoc x b) : ℂ)

def AllGeneratedOriginalBO (F : SignatureFamily AlgebraicComplex) (k : ℕ) : Prop :=
  ∀ (n : ℕ) (f : Signature AlgebraicComplex (n + 1)),
    Generated F k f → BlockOrthogonal (tableRows f)

theorem precompose_rows {X Y J : Type} [Fintype J] {G : X → J → ℂ}
    (h : BlockOrthogonal G) (r : Y → X) : BlockOrthogonal (fun y => G (r y)) :=
  ⟨fun x y hx hy => h.1 (r x) (r y) hx hy,
    fun x y hx hy hm => h.2 (r x) (r y) hx hy hm⟩

private theorem one_snoc (b c : Bool) :
    Fin.snoc (fun _ : Fin 1 => b) c = ![b,c] := by
  funext i
  fin_cases i <;> rfl

theorem generated_binary_bo {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hBO : AllGeneratedOriginalBO F k) (f : Signature AlgebraicComplex 2)
    (hf : Generated F k f) :
    BlockOrthogonal (fun b c : Bool => (f ![b,c] : ℂ)) := by
  have h := precompose_rows (hBO 1 f hf) (fun b _ => b)
  convert h using 1
  funext b c
  simp [tableRows,one_snoc]

/-- The k and 2k copies are genuine degree-k witnesses. Their full binary
rows obey a finite-order cross-product condition on the original coefficients. -/
theorem original_binary_cross_power (F : SignatureFamily AlgebraicComplex) (k : ℕ)
    (hBO : AllGeneratedOriginalBO F k) (f : Signature AlgebraicComplex 2)
    (hf : (⟨2,f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hne : ∀ b c, f ![b,c] ≠ 0) :
    ((f ![false,false] : ℂ) * (f ![true,true] : ℂ)) ^ (2 * k) =
      ((f ![false,true] : ℂ) * (f ![true,false] : ℂ)) ^ (2 * k) := by
  let G : Bool → Bool → ℂ := fun b c => (f ![b,c] : ℂ) ^ k
  have hG : BlockOrthogonal G := by
    have h := precompose_rows
      (hBO 1 (fun x => f x ^ k) (generated_power F f hf (dvd_refl k)))
      (fun b _ => b)
    convert h using 1
    funext b c
    simp [G,tableRows,one_snoc]
  have hG2 : BlockOrthogonal (fun b c => G b c ^ 2) := by
    have h := precompose_rows
      (hBO 1 (fun x => f x ^ (k * 2))
        (generated_power F f hf (show k ∣ k * 2 from ⟨2,rfl⟩)))
      (fun b _ => b)
    convert h using 1
    funext b c
    simp [G,tableRows,one_snoc,pow_mul]
  have hn (b c : Bool) : G b c ≠ 0 := by
    apply pow_ne_zero k
    exact_mod_cast hne b c
  have he := binary_squared_cross G hn hG hG2
  simpa only [G,← mul_pow,← pow_mul,Nat.mul_comm k 2] using he

end
end Paper2.DegreeCSP.OriginalBO
