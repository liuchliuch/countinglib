import Paper2.DegreeCSP.CodeSeven
import Paper2.DegreeCSP.NoAnchorWeightedParity
import Paper2.DegreeCSP.GeneratedPins

/-! A seven-character support mask is constructed from one genuine
generated affine parity face. Fourth powers remove its original weights;
a real repeated disequality constraint corrects the parity offset. Four
actual pulled-back parity constraints then enforce the entire code. -/
namespace Paper2.DegreeCSP.GeneratedCodeSeven
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 800000

def scaledParity (c : AlgebraicComplex) (offset : Bool) : Signature AlgebraicComplex 3 :=
  fun x=>if x 2=Bool.xor (Bool.xor (x 0) (x 1)) offset then c else 0

theorem generated_X {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F) :
    Generated F k (kernelSignature Signature.disequality) := by
  have h := generated_power F (kernelSignature Signature.disequality) hX (dvd_refl k)
  convert h using 1
  funext x
  cases hx0:x 0 <;> cases hx1:x 1 <;>
    simp [kernelSignature,Signature.disequality,hx0,hx1,Nat.ne_of_gt hk]

/-- Actual fourth powers of the parity face keep the common scalar, rather
than adding a normalized unweighted table to the language for free. -/
theorem generated_scaled_parity {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (A B : Bool→AlgebraicComplex) (offset : Bool)
    (hA : ∀ b,A b≠0) (hB : ∀ b,B b≠0)
    (hf : Generated F k (NoAnchorWeightedParity.table A B offset))
    (ha : Affine (NoAnchorWeightedParity.table A B offset)) :
    ∃ c : AlgebraicComplex,c≠0 ∧ Generated F k (scaledParity c offset) := by
  let f := NoAnchorWeightedParity.table A B offset
  let z : Fin 3→Bool := ![false,false,offset]
  have hz : f z≠0 := by
    simpa [f,z,NoAnchorWeightedParity.table] using mul_ne_zero (hA false) (hB false)
  let c := f z^4
  have hc : c≠0 := pow_ne_zero 4 hz
  have hp := generated_pow hf 4
  have he : (fun x=>f x^4)=scaledParity c offset := by
    funext x
    by_cases hv : x 2=Bool.xor (Bool.xor (x 0) (x 1)) offset
    · have hx : f x≠0 := by
        simpa only [f,NoAnchorWeightedParity.table,ite_eq_left hv] using mul_ne_zero (hA _) (hB _)
      have h := ha.fourth_power_eq x z hx hz
      simpa only [scaledParity,ite_eq_left hv,c] using h
    · simp only [f,NoAnchorWeightedParity.table,scaledParity,ite_eq_right hv,zero_pow (by decide : 4≠0)]
  exact ⟨c,hc,he ▸ hp⟩

/-- A genuine degree-generated disequality corrects a nonzero parity
offset with one actual hidden Boolean sum. -/
theorem generated_zero_offset {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (c : AlgebraicComplex) (offset : Bool)
    (hf : Generated F k (scaledParity c offset)) :
    Generated F k (scaledParity c false) := by
  cases offset
  · exact hf
  have hP := generated_pullback hf (![0,1,3] : Fin 3→Fin 4)
  have hD := generated_pullback (generated_X hk hX) (![3,2] : Fin 2→Fin 4)
  have h := generated_sum_last (generated_hadamard hP hD)
  convert h using 1
  funext x
  have hp (b : Bool) : (fun i : Fin 3=>Fin.snoc (α:=fun _=>Bool) x b (![0,1,3] i))=
      ![x 0,x 1,b] := by funext i;fin_cases i <;> rfl
  have hd (b : Bool) : (fun i : Fin 2=>Fin.snoc (α:=fun _=>Bool) x b (![3,2] i))=
      ![b,x 2] := by funext i;fin_cases i <;> rfl
  simp only [hp,hd,Fintype.sum_bool]
  cases h0:x 0 <;> cases h1:x 1 <;> cases h2:x 2 <;>
    simp [scaledParity,kernelSignature,Signature.disequality,h0,h1,h2]

/-- Four actual parity constraints enforce all seven nonzero characters.
The output scalar is the fourth power of the parity-mask scalar. -/
theorem generated_code {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (c : AlgebraicComplex) (hf : Generated F k (scaledParity c false)) :
    Generated F k (fun x : Fin 7→Bool=>c^4*indicator x) := by
  have h0 := generated_pullback hf (![1,2,3] : Fin 3→Fin 7)
  have h1 := generated_pullback hf (![0,2,4] : Fin 3→Fin 7)
  have h2 := generated_pullback hf (![0,1,5] : Fin 3→Fin 7)
  have h3 := generated_pullback hf (![5,2,6] : Fin 3→Fin 7)
  have h := generated_hadamard (generated_hadamard (generated_hadamard h0 h1) h2) h3
  convert h using 1
  funext x
  change c^4*indicator x=
    ((scaledParity c false ![x 1,x 2,x 3]*scaledParity c false ![x 0,x 2,x 4])*
      scaledParity c false ![x 0,x 1,x 5])*scaledParity c false ![x 5,x 2,x 6]
  by_cases h0 : x 3=Bool.xor (x 1) (x 2)
  all_goals by_cases h1 : x 4=Bool.xor (x 0) (x 2)
  all_goals by_cases h2 : x 5=Bool.xor (x 0) (x 1)
  all_goals by_cases h3 : x 6=Bool.xor (x 5) (x 2)
  all_goals simp [scaledParity,indicator,Valid,h0,h1,h2,h3]
  all_goals try split_ifs
  all_goals ring

/-- The exact support mask needed to preserve original partial contexts
through later degree-balanced cubic recipes. -/
theorem exists_scaled_code {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hk : 0<k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈F)
    (A B : Bool→AlgebraicComplex) (offset : Bool)
    (hA : ∀ b,A b≠0) (hB : ∀ b,B b≠0)
    (hf : Generated F k (NoAnchorWeightedParity.table A B offset))
    (ha : Affine (NoAnchorWeightedParity.table A B offset)) :
    ∃ c : AlgebraicComplex,c≠0 ∧ Generated F k (fun x : Fin 7→Bool=>c*indicator x) := by
  obtain ⟨c,hc,hp⟩ := generated_scaled_parity A B offset hA hB hf ha
  exact ⟨c^4,pow_ne_zero 4 hc,
    generated_code c (generated_zero_offset hk hX c offset hp)⟩


end
end Paper2.DegreeCSP.GeneratedCodeSeven
