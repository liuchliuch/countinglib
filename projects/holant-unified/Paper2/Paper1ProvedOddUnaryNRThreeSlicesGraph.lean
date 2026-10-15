import Paper2.Paper1ProvedOddUnaryNRThreeSlices
import Paper2.Paper1ProvedOddUnaryNRCanonicalSource
import Holant.ReedMuller.CoefficientAtlas.ContractionTransport

/-! The ternary support exit is a literal ordinary self-loop in the
unchanged finite source table. Its canonical coordinates have the exact
nonzero Gram scale; no extra signature is adjoined. -/
namespace Paper2.Paper1Proved.OddUnary.NRCanonical.ThreeSlicesGraph
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

def order (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective ![i,j,k] (Finite.injective_iff_bijective.mp (by
    rcases hd with ⟨hij,hjk,hik⟩
    intro a b equal
    fin_cases a <;> fin_cases b <;> simp_all))

@[simp] theorem order_zero (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    order i j k hd 0=i := rfl
@[simp] theorem order_one (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    order i j k hd 1=j := rfl
@[simp] theorem order_two (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    order i j k hd 2=k := rfl

def assignment (e : Equiv.Perm (Fin 3)) (a b c : Bool) : Fin 3 → Bool :=
  fun t => ![a,b,c] (e.symm t)

theorem assignment_single_left (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    assignment (order i j k hd) true false false=NR.single i := by
  funext t
  obtain ⟨s,rfl⟩ := (order i j k hd).surjective t
  dsimp only [assignment]
  rw [Equiv.symm_apply_apply]
  have hij := hd.1
  have hjk := hd.2.1
  have hik := hd.2.2
  have hji := Ne.symm hij
  have hkj := Ne.symm hjk
  have hki := Ne.symm hik
  fin_cases s <;> simp_all [NR.single,NR.word]

theorem assignment_single_right (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    assignment (order i j k hd) false true false=NR.single j := by
  funext t
  obtain ⟨s,rfl⟩ := (order i j k hd).surjective t
  dsimp only [assignment]
  rw [Equiv.symm_apply_apply]
  have hij := hd.1
  have hjk := hd.2.1
  have hik := hd.2.2
  have hji := Ne.symm hij
  have hkj := Ne.symm hjk
  have hki := Ne.symm hik
  fin_cases s <;> simp_all [NR.single,NR.word]

theorem assignment_double_left (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    assignment (order i j k hd) true false true=NR.double i k := by
  funext t
  obtain ⟨s,rfl⟩ := (order i j k hd).surjective t
  dsimp only [assignment]
  rw [Equiv.symm_apply_apply]
  have hij := hd.1
  have hjk := hd.2.1
  have hik := hd.2.2
  have hji := Ne.symm hij
  have hkj := Ne.symm hjk
  have hki := Ne.symm hik
  fin_cases s <;> simp_all [NR.double,NR.word]

theorem assignment_double_right (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    assignment (order i j k hd) false true true=NR.double j k := by
  funext t
  obtain ⟨s,rfl⟩ := (order i j k hd).surjective t
  dsimp only [assignment]
  rw [Equiv.symm_apply_apply]
  have hij := hd.1
  have hjk := hd.2.1
  have hik := hd.2.2
  have hji := Ne.symm hij
  have hkj := Ne.symm hjk
  have hki := Ne.symm hik
  fin_cases s <;> simp_all [NR.double,NR.word]

theorem assignment_double_joined (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    assignment (order i j k hd) true true false=NR.double i j := by
  funext t
  obtain ⟨s,rfl⟩ := (order i j k hd).surjective t
  dsimp only [assignment]
  rw [Equiv.symm_apply_apply]
  have hij := hd.1
  have hjk := hd.2.1
  have hik := hd.2.2
  have hji := Ne.symm hij
  have hkj := Ne.symm hjk
  have hki := Ne.symm hik
  fin_cases s <;> simp_all [NR.double,NR.word]

theorem assignment_full (e : Equiv.Perm (Fin 3)) :
    assignment e true true true=fun _ => true := by
  funext t
  dsimp only [assignment]
  generalize e.symm t=s
  fin_cases s <;> rfl

theorem cons_word (a b : Bool) (x : Fin 1 → Bool) :
    (Fin.cons a (Fin.cons b x) : Fin 3 → Bool)=![a,b,x 0] := by
  funext t
  fin_cases t
  · rfl
  · rfl
  · exact (Fin.cons_succ (α:=fun _ : Fin 3 => Bool) a
      (Fin.cons (α:=fun _ : Fin 2 => Bool) b x) (1 : Fin 2)).trans
      (Fin.cons_one (α:=fun _ : Fin 2 => Bool) b x)

variable {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (b i.val)}

def graph (N : NoXOrdinaryGraphAdjoin.Output H 3) (i j k : Fin 3)
    (hd : NR.ThreeSlices.Distinct i j k) : NoXOrdinaryGraphAdjoin.Output H 1 :=
  output (((⟨N.network,N.labels,N.exact,N.ordinary⟩ : Macro H 3).reindex
    (order i j k hd).symm).contract)

theorem mapped_graph (phi : K →+* AlgebraicComplex)
    (N : NoXOrdinaryGraphAdjoin.Output H 3) (i j k : Fin 3)
    (hd : NR.ThreeSlices.Distinct i j k) :
    RingHomRealization.mapSignature phi (graph N i j k hd).network.denote=
      Holant.Signature.contract Holant.Signature.equality
        (Holant.Tensor.reindex (order i j k hd).symm
          (RingHomRealization.mapSignature phi N.network.denote)) := by
  funext x
  change phi ((((⟨N.network,N.labels,N.exact,N.ordinary⟩ : Macro H 3).reindex
    (order i j k hd).symm).contract).network.denote x)=_
  rw [Macro.contract_denote,map_add,Macro.reindex_denote]
  simp [Holant.Signature.contract,Holant.Signature.equality,Holant.Tensor.reindex,
    RingHomRealization.mapSignature]
  exact add_comm _ _

theorem gram_contract (phi : K →+* AlgebraicComplex)
    {R : InvertibleKernel} {v : Bool → AlgebraicComplex}
    (C : Receipt (H:=H) phi R v) (f : Holant.Signature AlgebraicComplex 3)
    (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    Holant.Signature.contract (Holant.Kernel.pullback Holant.Signature.equality C.basis.matrix)
      (Holant.Tensor.reindex (order i j k hd).symm f)=
      fun x => C.gramScale*NR.ThreeSlices.loop f i j k x := by
  have gram : Holant.Kernel.pullback Holant.Signature.equality C.basis.matrix=
      fun a b => if a=b then (if a then -2*C.gramScale else 0) else C.gramScale := by
    funext a b
    rw [←C.gramForm]
    simp [Holant.Kernel.pullback,Holant.Kernel.mul,Holant.Kernel.transpose,
      Holant.Signature.equality]
    exact add_comm _ _
  rw [gram]
  funext x
  simp only [Holant.Signature.contract,Fintype.sum_bool,ite_true,Bool.false_eq_true,
    Bool.true_eq_false,ite_false,zero_mul,add_zero,Holant.Tensor.reindex,cons_word]
  change ((-2*C.gramScale)*f (assignment (order i j k hd) true true (x 0))+
    C.gramScale*f (assignment (order i j k hd) true false (x 0)))+
      C.gramScale*f (assignment (order i j k hd) false true (x 0))=_
  cases hx : x 0
  · rw [assignment_single_left,assignment_single_right,assignment_double_joined]
    simp only [NR.ThreeSlices.loop,hx,Bool.false_eq_true,ite_false]
    ring
  · rw [assignment_double_left,assignment_double_right,assignment_full]
    simp only [NR.ThreeSlices.loop,hx,ite_true]
    ring

theorem chart_graph (phi : K →+* AlgebraicComplex)
    {R : InvertibleKernel} {v : Bool → AlgebraicComplex}
    (C : Receipt (H:=H) phi R v) (N : NoXOrdinaryGraphAdjoin.Output H 3)
    (i j k : Fin 3) (hd : NR.ThreeSlices.Distinct i j k) :
    C.basis.symm.action (RingHomRealization.mapSignature phi (graph N i j k hd).network.denote)=
      fun x => C.gramScale*NR.ThreeSlices.loop
        (C.basis.symm.action (RingHomRealization.mapSignature phi N.network.denote)) i j k x := by
  rw [mapped_graph]
  let f := C.basis.symm.action (RingHomRealization.mapSignature phi N.network.denote)
  have source : RingHomRealization.mapSignature phi N.network.denote=C.basis.action f :=
    (InvertibleKernel.action_symm_action C.basis _).symm
  rw [source]
  change C.basis.symm.action (Holant.Signature.contract Holant.Signature.equality
    (Holant.Tensor.reindex (order i j k hd).symm
      (Holant.Signature.coordinateAction (fun _ => C.basis.matrix) f)))=_
  rw [←Holant.ReedMuller.CoefficientAtlas.coordinateAction_reindex,
    Holant.ReedMuller.CoefficientAtlas.coordinateAction_contract]
  change C.basis.symm.action (C.basis.action _) = _
  rw [InvertibleKernel.symm_action_action,gram_contract phi C]
  simp only [InvertibleKernel.symm_action_action]

/-- An actual one-loop unary leaves the criterion in the same canonical
coordinates and the same finite ordinary source table. -/
theorem exists_outside_graph (phi : K →+* AlgebraicComplex)
    {R : InvertibleKernel} {v : Bool → AlgebraicComplex}
    (C : Receipt (H:=H) phi R v) (N : NoXOrdinaryGraphAdjoin.Output H 3)
    (outside : ¬NR.Closed
      (C.basis.symm.action (RingHomRealization.mapSignature phi N.network.denote)))
    (slices : ∀ i b,NR.Closed (NR.slice
      (C.basis.symm.action (RingHomRealization.mapSignature phi N.network.denote)) i b)) :
    ∃ U : NoXOrdinaryGraphAdjoin.Output H 1,¬NR.Closed
      (C.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) := by
  obtain ⟨i,j,k,hd,bad⟩ := NR.ThreeSlices.exists_outside_loop _ slices outside
  refine ⟨graph N i j k hd,?_⟩
  rw [chart_graph phi C]
  exact fun closed => bad ((NR.closed_scale_iff C.gramScale C.gramScaleNonzero _).mp closed)

end
end Paper2.Paper1Proved.OddUnary.NRCanonical.ThreeSlicesGraph

