import Paper2.DegreeCSP.CodeSeven
import Paper2.DegreeCSP.AffineCoordinateSubstitution
import Paper2.DegreeCSP.CyclicPhaseCharacterGenerators
import Paper2.DegreeCSP.GeneratedCompose

/-! A genuine affine seven-character packet cannot carry a nontrivial
pure cubic coefficient. The original packet scalar is cancelled explicitly;
finite packet products retain both scalar and character parameter. -/
namespace Paper2.DegreeCSP.CodeSevenAffineObstruction
open scoped BigOperators
open Tractable GeneratedCodeSeven
open Holant.Tractable.AffinePhase (Word xor origin basis)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def cubic (C : AlgebraicComplex) (x : Word 3) : AlgebraicComplex :=
  C^(bitValue ℕ (x 0)*bitValue ℕ (x 1)*bitValue ℕ (x 2))

def payload (c C : AlgebraicComplex) : Signature AlgebraicComplex 7 :=
  fun y=>if Valid y then c*cubic C (decode y) else 0

set_option maxRecDepth 100000 in
theorem code_isAffineMap : Holant.Tractable.TwoTranslate.IsAffineMap code := by
  unfold Holant.Tractable.TwoTranslate.IsAffineMap
  decide +kernel

theorem payload_code (c C : AlgebraicComplex) (x : Word 3) :
    payload c C (code x)=c*cubic C x := by
  simp only [payload,valid_code,ite_true,decode_code]

theorem cubic_nonzero (C : AlgebraicComplex) (hC : C≠0) (x : Word 3) :
    cubic C x≠0 := pow_ne_zero _ hC

/-- The signed eight-entry ratio at the zero word and the three coordinate
basis directions is exactly C. This works for every nonzero C. -/
theorem cubic_affine_parameter (C : AlgebraicComplex) (hC : C≠0)
    (h : Affine (cubic C)) : C=1 := by
  have ht := Holant.Tractable.AffinePhase.thirdTrivial_of_affine
    (f:=cubic C) (cubic_nonzero C hC) ((Paper1Proved.affine_iff _).mp h)
  have he := ht (origin 3) (basis (0:Fin 3)) (basis (1:Fin 3)) (basis (2:Fin 3))
  simpa [Holant.Tractable.AffinePhase.thirdRatio,cubic,bitValue,
    Holant.Tractable.AffinePhase.xor,Holant.Tractable.AffinePhase.origin,
    Holant.Tractable.AffinePhase.basis] using he

/-- Actual affinity of the code-supported packet forces its cubic
parameter to be one, without assuming that parameter is a fourth root. -/
theorem affine_parameter (c C : AlgebraicComplex) (hc : c≠0) (hC : C≠0)
    (h : Affine (payload c C)) : C=1 := by
  have hp := ((Paper1Proved.affine_iff _).mp h).precompose code code_isAffineMap
  have ht : Affine (fun x : Word 3=>c*cubic C x) := by
    apply (Paper1Proved.affine_iff _).mpr
    simpa only [payload_code] using hp
  have hu := ht.scale c⁻¹
  have he : (fun x : Word 3=>c⁻¹*(c*cubic C x))=cubic C := by
    funext x
    rw [←mul_assoc,inv_mul_cancel₀ hc,one_mul]
  rw [he] at hu
  exact cubic_affine_parameter C hC hu

/-- A code mask also handles an empty finite product, retaining zero outside
all seven-character codewords. -/
theorem masked_product {ι : Type*} (s : Finset ι) (c C : ι→AlgebraicComplex)
    (y : Word 7) :
    payload 1 1 y*(∏i∈s,payload (c i) (C i) y)=
      payload (∏i∈s,c i) (∏i∈s,C i) y := by
  classical
  by_cases hy : Valid y
  · simp only [payload,hy,ite_true,cubic,one_pow,mul_one,one_mul,
      Finset.prod_mul_distrib,Finset.prod_pow]
  · simp only [payload,hy,ite_false,zero_mul]

/-- Repeating actual code packets gives the same parameter product and the
same nonzero scalar product, before any degree balance is imposed. -/
theorem product {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (c C : ι→AlgebraicComplex) (y : Word 7) :
    (∏i∈s,payload (c i) (C i) y)=payload (∏i∈s,c i) (∏i∈s,C i) y := by
  classical
  by_cases hy : Valid y
  · simp only [payload,hy,ite_true,cubic,Finset.prod_mul_distrib,Finset.prod_pow]
  · simp only [payload,hy,ite_false]
    exact Finset.prod_eq_zero hs.choose_spec rfl

/-- The scalar in every balanced packet remains nonzero. Actual balanced
packet realizations and their proved affinity therefore give the finite
cycle relation required for one common character. -/
theorem common_character (F : SignatureFamily AlgebraicComplex) {k s : ℕ}
    (hk : 0<k) (d : Fin s→ℕ) (c C : Fin s→AlgebraicComplex)
    (hc : ∀i,c i≠0) (hC : ∀i,C i≠0)
    (affine : ∀f : Signature AlgebraicComplex 7,Generated F k f→Affine f)
    (balanced : ∀a : Fin s→ℕ,k∣∑i,a i*d i→
      Generated F k (payload (∏i,c i^a i) (∏i,C i^a i))) :
    ∃theta : AlgebraicComplex,theta^k=1 ∧ ∀i,C i=theta^(d i) := by
  apply CyclicPhaseCharacterGenerators.exists_phase_of_cycles hk d C
  intro a ha
  exact affine_parameter _ _
    (Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (hc i)))
    (Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (hC i)))
    (affine _ (balanced a ha))

end
end Paper2.DegreeCSP.CodeSevenAffineObstruction

