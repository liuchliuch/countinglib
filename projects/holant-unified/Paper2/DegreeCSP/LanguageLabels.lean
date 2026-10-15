import Paper2.DegreeCSP.Generated
import Paper2.ExactInput.FiniteLanguage

/-! The finite presentation's literal constraints select fixed dictionary
slots before any instance is read. Equal arities and coefficients are retained
by the dependent signature equality. -/
namespace Paper2.DegreeCSP.LanguageLabels
open Tractable ExactInput
noncomputable section

def ofMember (L : Language) (f : AnySignature AlgebraicComplex) (hf : f∈L.family) :
    Fin L.count := Classical.choose hf

theorem ofMember_literal (L : Language) (f : AnySignature AlgebraicComplex)
    (hf : f∈L.family) :
    (⟨L.arity (ofMember L f hf).val,L.signature (ofMember L f hf)⟩ :
      AnySignature AlgebraicComplex)=f := Classical.choose_spec hf

def ofUses {B : Type} (L : Language) (P : Presentation AlgebraicComplex B)
    (hUses : P.Uses L.family) (c : Fin P.constraints) : Fin L.count :=
  ofMember L ⟨P.arity c,P.constraint c⟩ (hUses c)

theorem ofUses_literal {B : Type} (L : Language) (P : Presentation AlgebraicComplex B)
    (hUses : P.Uses L.family) (c : Fin P.constraints) :
    (⟨L.arity (ofUses L P hUses c).val,L.signature (ofUses L P hUses c)⟩ :
      AnySignature AlgebraicComplex)=⟨P.arity c,P.constraint c⟩ :=
  ofMember_literal L ⟨P.arity c,P.constraint c⟩ (hUses c)

def naturals {B : Type} (L : Language) (P : Presentation AlgebraicComplex B)
    (hUses : P.Uses L.family) : Fin P.constraints→ℕ :=
  fun c=>(ofUses L P hUses c).val

theorem naturals_lt {B : Type} (L : Language) (P : Presentation AlgebraicComplex B)
    (hUses : P.Uses L.family) (c : Fin P.constraints) :
    naturals L P hUses c<L.count := (ofUses L P hUses c).isLt

theorem naturals_arity {B : Type} (L : Language) (P : Presentation AlgebraicComplex B)
    (hUses : P.Uses L.family) (c : Fin P.constraints) :
    L.arity (naturals L P hUses c)=P.arity c :=
  congrArg Sigma.fst (ofUses_literal L P hUses c)

end
end Paper2.DegreeCSP.LanguageLabels
