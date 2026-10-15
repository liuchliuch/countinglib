import Paper2.HeightOne.Cyclic.BalancedTables

/-! A pattern table for evaluating the already proved balanced Walsh tensor.
It does not assert graph realizability of any formal coefficient table. -/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards Dihedral

def balancedCoefficients (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex) :
    Signature AlgebraicComplex 4 := fun x =>
  match x 0,x 1,x 2,x 3 with
  | false,false,false,false => p
  | true,true,true,true => p
  | true,true,false,false => s 0
  | false,false,true,true => s 0
  | true,false,true,false => s 1
  | false,true,false,true => s 1
  | true,false,false,true => s 2
  | false,true,true,false => s 2
  | _,_,_,_ => 0

lemma balancedWalsh_eq_coefficients (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex) :
    balancedWalsh p s = balancedCoefficients p s := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [balancedWalsh,balancedCoefficients,point,centralWord,flipPair,flipAll,
    Fin.sum_univ_three,funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

end
end Paper2.HeightOne.Cyclic
