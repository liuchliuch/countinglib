import Paper2.Paper1ProvedOddUnaryOneHotFaces
import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionTernary
import Paper2.Paper1ProvedOddUnaryNRActualCaps

/-! Prime ternaries outside the common isotropic matching orientation admit
a nonsingular binary projection that breaks that line. The interpolation cap
is chosen in the original infinite field, although the matching chart is
used only over algebraic complex coefficients. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotLineProjection
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.TractChainV1
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {K : Type} [Field K]

def line (u : Bool → K) : (Bool → Bool → K) →ₗ[K] K where
  toFun D := u false*(D false false*u false+D false true*u true)+
    u true*(D true false*u false+D true true*u true)
  map_add' D E := by simp only [Pi.add_apply];ring
  map_smul' c D := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring

def reorder (f : Holant.Signature K 3) (i : Fin 3) : Holant.Signature K 3 :=
  Holant.Tensor.reindex (NR.ActualCaps.order i) f

omit [Field K] in
theorem reorder_word (f : Holant.Signature K 3) (i : Fin 3) (v a b : Bool) :
    reorder f i ![v,a,b]=f (i.insertNth v ![a,b]) := by
  unfold reorder
  rw [Holant.Tensor.reindex_apply]
  have h : (![v,a,b] : Fin 3 → Bool)=Fin.cons v ![a,b] := rfl
  rw [h,NR.ActualCaps.order_word]

theorem pin_cap (f : Holant.Signature K 3) (i : Fin 3) (v : Bool) (x : Fin 2 → Bool) :
    NR.cap (OneHotFaces.pin v) f i x=f (i.insertNth v x) := by
  simp only [NR.cap,OneHotFaces.pin,Fintype.sum_bool]
  cases v <;> simp

theorem mapped_line (phi : K →+* AlgebraicComplex) (u : Bool → K)
    (D : Bool → Bool → K) (opposite : Bool) (c : AlgebraicComplex)
    (form : ∀ v,phi (u v)=c*(TensorDecisionMatching.basis opposite).matrix v false) :
    phi (line u D)=c^2*TernaryW.column_pairing
      (fun i j => phi (D i j)) (TensorDecisionMatching.basis opposite).matrix
        (TensorDecisionMatching.basis opposite).matrix := by
  simp only [line,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_mul,form,TernaryW.column_pairing]
  ring

/-- Failure of one-hot support cannot be hidden in every literal pin face.
The visible measurement itself has coefficients in the unchanged field. -/
theorem visible_face (phi : K →+* AlgebraicComplex) (f : Holant.Signature K 3)
    (u : Bool → K) (opposite : Bool) (c : AlgebraicComplex) (cnz : c≠0)
    (form : ∀ v,phi (u v)=c*(TensorDecisionMatching.basis opposite).matrix v false)
    (outside : ¬matchingImage opposite 3 (RingHomRealization.mapSignature phi f)) :
    ∃ i : Fin 3,∃ v : Bool,line u (fun a b => reorder f i ![v,a,b])≠0 := by
  have notHot : ¬ Holant.Signature.OneHot
      ((TensorDecisionMatching.basis opposite).symm.action
        (RingHomRealization.mapSignature phi f)) := by
    intro hot
    have h := TensorDecisionMatching.forward_factor opposite 3
      ((TensorDecisionMatching.basis opposite).symm.action
        (RingHomRealization.mapSignature phi f)) hot
    apply outside
    simpa only [InvertibleKernel.action_symm_action] using h
  obtain ⟨i,v,bad⟩ := OneHotFaces.exists_outside_face
    (TensorDecisionMatching.basis opposite) (RingHomRealization.mapSignature phi f) notHot
  let D : Bool → Bool → K := fun a b => reorder f i ![v,a,b]
  have capForm : NR.cap (OneHotFaces.pin v) (RingHomRealization.mapSignature phi f) i=
      kernelSignature (fun a b => phi (D a b)) := by
    funext x
    rw [pin_cap]
    change phi (f (i.insertNth v x))=phi (D (x 0) (x 1))
    unfold D
    rw [reorder_word]
    have hx : x=![x 0,x 1] := by
      funext j
      fin_cases j <;> rfl
    rw [hx]
    rfl
  have notMatch : ¬matchingImage opposite 2 (kernelSignature (fun a b => phi (D a b))) := by
    intro matched
    apply bad
    rw [capForm]
    exact TensorDecisionMatching.inverse_factor opposite 2 _ matched
  have breaks : TernaryW.column_pairing (fun a b => phi (D a b))
      (TensorDecisionMatching.basis opposite).matrix (TensorDecisionMatching.basis opposite).matrix≠0 := by
    rwa [WEscape.matchingImage_binary_iff] at notMatch
  refine ⟨i,v,?_⟩
  change line u D≠0
  intro hz
  have hm := mapped_line phi u D opposite c form
  rw [hz,map_zero] at hm
  exact (mul_ne_zero (pow_ne_zero 2 cnz) breaks) hm.symm

/-- The selected binary has a nonzero determinant and nonzero pairing along
the actual repeated W line. Both cap entries belong to the original field. -/
theorem exists_projection [Infinite K] (phi : K →+* AlgebraicComplex)
    (f : Holant.Signature K 3)
    (prime : Prime (⟨3,RingHomRealization.mapSignature phi f⟩ : Holant.AnySignature AlgebraicComplex))
    (u : Bool → K) (opposite : Bool) (c : AlgebraicComplex) (cnz : c≠0)
    (form : ∀ v,phi (u v)=c*(TensorDecisionMatching.basis opposite).matrix v false)
    (outside : ¬matchingImage opposite 3 (RingHomRealization.mapSignature phi f)) :
    ∃ i : Fin 3,∃ cap : Bool → K,
      line u (OneHotBinaryProjection.ternaryCap (reorder f i) cap)≠0 ∧
      OneHotBinaryProjection.determinant (OneHotBinaryProjection.ternaryCap (reorder f i) cap)≠0 := by
  obtain ⟨i,v,visible⟩ := visible_face phi f u opposite c cnz form outside
  have mapped : RingHomRealization.mapSignature phi (reorder f i)=
      Holant.Tensor.reindex (NR.ActualCaps.order i) (RingHomRealization.mapSignature phi f) := rfl
  have hp : Prime (⟨3,RingHomRealization.mapSignature phi (reorder f i)⟩ :
      Holant.AnySignature AlgebraicComplex) := by
    rw [mapped]
    exact GlobalCloseCompletionC2Q4PrimeTools.prime_reindex _ prime _
  obtain ⟨cap,good,det⟩ := OneHotBinaryProjection.ternary_linear_projection phi (reorder f i) hp
    (line u) ⟨v,visible⟩
  exact ⟨i,cap,good,det⟩

end
end Paper2.Paper1Proved.OddUnary.OneHotLineProjection

