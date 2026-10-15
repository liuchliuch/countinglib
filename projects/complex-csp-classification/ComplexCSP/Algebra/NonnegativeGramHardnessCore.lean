import ComplexCSP.Algebra.PositiveMatrixHardnessCore
import ComplexCSP.Structure.SupportComponentReduction
import ComplexCSP.Algebra.PositiveGramComponent

/-! # Complete nonnegative Gram hardness reduction chain

The only separately named foundation parameter is discharged by the closed
Potts source theorem in the final wrapper. Component restriction, positive
powers, conditioning, coordinate transport and every oracle compiler are
actual proved reductions.
-/
noncomputable section
open Classical
namespace ComplexCSP.NonnegativeGramHardnessCore
local instance (priority := 10000) decEq (α : Type*) : DecidableEq α := Classical.decEq α
open PlanarHom PlanarHom.Complexity AlgebraicProductInterpolation
open scoped BigOperators
variable {I C : Type} [Fintype I] [Fintype C]
variable (K : IntermediateField ℚ ℝ) {d : ℕ}

theorem hard_of_potts (basis : Module.Basis (Fin d) ℚ K)
    (hPotts : RealLanguage.PositivePottsFoundation) (A : Matrix I I K)
    (hA : ∀ i j,0≤A i j) (hs : ∀ i j,A i j=A j i)
    (B : I → C → ℝ) (hB : ∀ i z,0≤B i z)
    (hGram : ∀ i j,(A i j : ℝ)=∑ z,B i z*B j z)
    (i j : I) (hm : PositiveGramPowerField.StrictMinor K A i j) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) := by
  letI : IsStrictOrderedRing K := Subfield.toIsStrictOrderedRing K.toSubfield
  let X := PositiveGramComponent.component K A i
  let S : Matrix X X K := fun x y => A x.val y.val
  let x : X := ⟨i,PositiveGramComponent.root_mem K A i⟩
  let y : X := ⟨j,PositiveGramComponent.adjacent_mem K A i j hm.2.1⟩
  have hn : ∀ x y,0≤S x y := fun x y => hA x.val y.val
  have hd : ∀ x,0<S x x := PositiveGramComponent.diagonal_positive K A B hB hGram i hm.1
  have hc : ∀ x y,Relation.ReflTransGen (fun u v => 0<S u v) x y := PositiveGramComponent.connected K A hs i
  have hsym : ∀ x y,S x y=S y x := fun x y => hs x.val y.val
  have hminor : PositiveGramPowerField.StrictMinor K S x y := hm
  have hp := PositiveGramPowerField.positive_power_and_minor K S hn hd hc hsym x y hminor
  have hpowerSymm : ∀ u v,(S^(2^Fintype.card X)) u v=(S^(2^Fintype.card X)) v u := by
    have hS : S.IsSymm := Matrix.IsSymm.ext (fun u v => hsym v u)
    exact fun u v => (hS.pow _).apply v u
  have hh := PositiveMatrixHardnessCore.positive_strict_minor_hard_of_potts K basis hPotts
    (S^(2^Fintype.card X)) hp.1 hpowerSymm x y hp.2.2.2.2
  have hcomponent := hh.trans (PositiveGramPowerField.reduction K S basis)
  exact hcomponent.trans (SupportComponentReduction.reduction basis A hs X
    (PositiveGramComponent.colorClosed K A hA i))

end ComplexCSP.NonnegativeGramHardnessCore
