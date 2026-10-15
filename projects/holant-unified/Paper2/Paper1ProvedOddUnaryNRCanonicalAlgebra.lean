import Paper2.Paper1ProvedOddUnaryTernarySymmetricWSource
import Paper2.Paper1ProvedOddUnaryNRInheritance

/-! The concrete sheared chart in the exceptional isotropic W case. Its
columns are fixed by the real zero-pin covector and the repeated W column.
The exceptional equation is used to put both original W and the original
pin in the NR class, while their actual cap covectors become its two slices. -/
namespace Paper2.Paper1Proved.OddUnary.NRCanonical
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

def alpha (R : Kernel AlgebraicComplex) (v : Bool → AlgebraicComplex) : AlgebraicComplex :=
  R false false*v false+R true false*v true
def beta (R : Kernel AlgebraicComplex) (v : Bool → AlgebraicComplex) : AlgebraicComplex :=
  R false true*v false+R true true*v true
def excitationNorm (R : Kernel AlgebraicComplex) : AlgebraicComplex :=
  R false true^2+R true true^2
def exceptional (R : Kernel AlgebraicComplex) (v : Bool → AlgebraicComplex) : Prop :=
  beta R v*TernaryW.cross R+alpha R v*excitationNorm R=0

def chartKernel (R : Kernel AlgebraicComplex) (v : Bool → AlgebraicComplex) : Kernel AlgebraicComplex :=
  fun t b => if b then 2*alpha R v*R t true-2*beta R v*R t false else 3*beta R v*R t false

theorem chart_determinant (R : Kernel AlgebraicComplex) (v : Bool → AlgebraicComplex) :
    SymmetricBinaryPullback.determinant (chartKernel R v) =
      6*alpha R v*beta R v*SymmetricBinaryPullback.determinant R := by
  simp [SymmetricBinaryPullback.determinant,chartKernel]
  ring

theorem exceptional_beta_nonzero (R : InvertibleKernel) (v : Bool → AlgebraicComplex)
    (iso : R.matrix false false^2+R.matrix true false^2=0)
    (norm : v false^2+v true^2≠0) (ha : alpha R.matrix v≠0)
    (he : exceptional R.matrix v) : beta R.matrix v≠0 := by
  intro zero
  have qzero : excitationNorm R.matrix=0 := by
    have h : alpha R.matrix v*excitationNorm R.matrix=0 := by simpa [exceptional,zero] using he
    exact (mul_eq_zero.mp h).resolve_left ha
  have identity : (v false^2+v true^2)*(SymmetricBinaryPullback.determinant R.matrix)^2=0 := by
    dsimp [alpha,beta,excitationNorm,exceptional,TernaryW.cross,SymmetricBinaryPullback.determinant] at *
    linear_combination (R.matrix false false*v false+R.matrix true false*v true)^2*qzero +
      (R.matrix false true*v false+R.matrix true true*v true)^2*iso -
      2*(R.matrix false false*v false+R.matrix true false*v true)*
        (R.matrix false false*R.matrix false true+R.matrix true false*R.matrix true true)*zero
  exact mul_ne_zero norm (pow_ne_zero _ (SymmetricBinaryPullback.determinant_ne_zero R)) identity

def chart (R : InvertibleKernel) (v : Bool → AlgebraicComplex)
    (ha : alpha R.matrix v≠0) (hb : beta R.matrix v≠0) : InvertibleKernel :=
  SymmetricBinaryPullback.invertibleOfDeterminant (chartKernel R.matrix v)
    (by
      rw [chart_determinant]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb)
        (SymmetricBinaryPullback.determinant_ne_zero R))

theorem chart_pin_pairing (R : Kernel AlgebraicComplex) (v : Bool → AlgebraicComplex) (b : Bool) :
    v false*chartKernel R v false b+v true*chartKernel R v true b =
      if b=false then 3*alpha R v*beta R v else 0 := by
  cases b <;> simp [chartKernel,alpha,beta] <;> ring

theorem chart_isotropic_pairing (R : Kernel AlgebraicComplex) (v : Bool → AlgebraicComplex)
    (iso : R false false^2+R true false^2=0) (kappa : AlgebraicComplex) (b : Bool) :
    (kappa*R false false)*chartKernel R v false b+
      (kappa*R true false)*chartKernel R v true b =
      if b=true then 2*alpha R v*kappa*TernaryW.cross R else 0 := by
  cases b <;> simp only [chartKernel,Bool.false_eq_true,ite_false,ite_true,TernaryW.cross]
  · linear_combination 3*kappa*beta R v*iso
  · linear_combination -(2*kappa*beta R v)*iso

theorem chart_isotropic (R : Kernel AlgebraicComplex) (v : Bool → AlgebraicComplex)
    (iso : R false false^2+R true false^2=0) :
    chartKernel R v false false^2+chartKernel R v true false^2=0 := by
  simp only [chartKernel,Bool.false_eq_true,ite_false]
  linear_combination 9*(beta R v)^2*iso

theorem chart_gram (R : Kernel AlgebraicComplex) (v : Bool → AlgebraicComplex)
    (iso : R false false^2+R true false^2=0) (he : exceptional R v) (i j : Bool) :
    chartKernel R v false i*chartKernel R v false j+
      chartKernel R v true i*chartKernel R v true j =
      if i=j then (if i then -2*(6*alpha R v*beta R v*TernaryW.cross R) else 0)
      else 6*alpha R v*beta R v*TernaryW.cross R := by
  cases i <;> cases j <;>
    simp only [chartKernel,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
  · linear_combination 9*(beta R v)^2*iso
  · dsimp [TernaryW.cross]
    linear_combination -(6*(beta R v)^2)*iso
  · dsimp [TernaryW.cross]
    linear_combination -(6*(beta R v)^2)*iso
  · dsimp [exceptional,excitationNorm,TernaryW.cross] at he ⊢
    linear_combination 4*(alpha R v)*he+4*(beta R v)^2*iso

theorem pin_expansion (R : InvertibleKernel) (v : Bool → AlgebraicComplex)
    (iso : R.matrix false false^2+R.matrix true false^2=0)
    (he : exceptional R.matrix v) :
    ∀ t,TernaryW.cross R.matrix*v t=2*beta R.matrix v*R.matrix t false+
      alpha R.matrix v*R.matrix t true := by
  have det := SymmetricBinaryPullback.determinant_ne_zero R
  intro t
  have identity : SymmetricBinaryPullback.determinant R.matrix*
      (TernaryW.cross R.matrix*v t-2*beta R.matrix v*R.matrix t false-alpha R.matrix v*R.matrix t true)=0 := by
    cases t <;> dsimp [TernaryW.cross,alpha,beta,exceptional,excitationNorm,SymmetricBinaryPullback.determinant] at *
    · linear_combination R.matrix true false*he+
        -(2*R.matrix true true*(R.matrix false true*v false+R.matrix true true*v true))*iso
    · linear_combination -(R.matrix false false*he)+
        (2*R.matrix false true*(R.matrix false true*v false+R.matrix true true*v true))*iso
  have zero := (mul_eq_zero.mp identity).resolve_left det
  linear_combination zero

end
end Paper2.Paper1Proved.OddUnary.NRCanonical
