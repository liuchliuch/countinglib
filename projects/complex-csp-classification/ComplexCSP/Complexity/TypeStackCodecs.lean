import ComplexCSP.Structure.MaltsevTypeStack
import ComplexCSP.Complexity.TypeCache
import ComplexCSP.Complexity.WitnessPrimitives
import PlanarHom.UnaryPolynomialMachines

/-! # Literal codecs and FP primitives for the type-search continuation stack

Lengths are unary. Targets, remaining colors, labels, stack frames and cache
entries are physically stored, with no function closures in any encoded record.
-/
namespace ComplexCSP.ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open MaltsevTypeStack ComplexityWitnessPrimitives
variable {A : Type}

def optionCode (e : BitEncoding A) : BitEncoding (Option A) :=
  e.list.retract Option.toList List.head? (by intro x; cases x <;> rfl)

theorem fp_some (e : BitEncoding A) : FP e (optionCode e) Option.some := by
  have h := ((fp_id e).pair (fp_const e e.list [])).comp (ListMutationMachines.fp_cons e)
  exact h.transportOutput (fun _ => rfl)

theorem fp_headOption (e : BitEncoding A) (fallback : A) :
    FP e.list (optionCode e) List.head? := by
  have hz := ((ListCodecMachines.fp_length e).pair (fp_const e.list BitEncoding.nat 0)).comp
    NatListSumMachines.fp_equal
  have hv := (ListDecompositionMachines.fp_headD e fallback).comp (fp_some e)
  exact (hz.ite (fp_const e.list (optionCode e) none) hv).congr
    (fun xs => by cases xs <;> rfl)

abbrev FrameView (A : Type) := ℕ × (List ℕ × (List ℕ × List A))
def frameView (f : Frame A) : FrameView A :=
  (f.parentLen,f.parentTarget,f.remainingColors,f.accumulatedLabels)
def frameOfView (p : FrameView A) : Frame A := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩
def frameViewCode (e : BitEncoding A) : BitEncoding (FrameView A) :=
  BitEncoding.unaryNat.prod (wordCode.prod (wordCode.prod e.list))
def frameCode (e : BitEncoding A) : BitEncoding (Frame A) :=
  (frameViewCode e).retract frameView frameOfView (by intro f; cases f; rfl)

abbrev StateView (A : Type) := Bool × (ℕ × (List ℕ × (List A × (List (Frame A) × ComplexityTypeCache.Cache A))))
def stateView (s : State A) : StateView A :=
  (s.returning,s.currentLen,s.currentTarget,s.returnedLabels,s.stack,s.cache)
def stateOfView (p : StateView A) : State A :=
  ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2⟩
def stateViewCode (e : BitEncoding A) : BitEncoding (StateView A) :=
  BitEncoding.bool.prod (BitEncoding.unaryNat.prod (wordCode.prod
    (e.list.prod ((frameCode e).list.prod (ComplexityTypeCache.cacheEncoding e)))))
def stateCode (e : BitEncoding A) : BitEncoding (State A) :=
  (stateViewCode e).retract stateView stateOfView (by intro s; cases s; rfl)

theorem fp_frameView (e : BitEncoding A) : FP (frameCode e) (frameViewCode e) frameView :=
  fp_code_view _ _ _ (fun _ => rfl)
theorem fp_frameOfView (e : BitEncoding A) : FP (frameViewCode e) (frameCode e) frameOfView :=
  fp_code_view _ _ _ (fun _ => rfl)
theorem fp_stateView (e : BitEncoding A) : FP (stateCode e) (stateViewCode e) stateView :=
  fp_code_view _ _ _ (fun _ => rfl)
theorem fp_stateOfView (e : BitEncoding A) : FP (stateViewCode e) (stateCode e) stateOfView :=
  fp_code_view _ _ _ (fun _ => rfl)

theorem fp_parentLen (e : BitEncoding A) : FP (frameCode e) (BitEncoding.unaryNat) Frame.parentLen :=
  ((fp_frameView e).comp (fp_fst (BitEncoding.unaryNat) ((wordCode).prod ((wordCode).prod (e.list)))))

theorem fp_parentTarget (e : BitEncoding A) : FP (frameCode e) (wordCode) Frame.parentTarget :=
  (((fp_frameView e).comp (fp_snd (BitEncoding.unaryNat) ((wordCode).prod ((wordCode).prod (e.list))))).comp (fp_fst (wordCode) ((wordCode).prod (e.list))))

theorem fp_remainingColors (e : BitEncoding A) : FP (frameCode e) (wordCode) Frame.remainingColors :=
  ((((fp_frameView e).comp (fp_snd (BitEncoding.unaryNat) ((wordCode).prod ((wordCode).prod (e.list))))).comp (fp_snd (wordCode) ((wordCode).prod (e.list)))).comp (fp_fst (wordCode) (e.list)))

theorem fp_accumulatedLabels (e : BitEncoding A) : FP (frameCode e) (e.list) Frame.accumulatedLabels :=
  ((((fp_frameView e).comp (fp_snd (BitEncoding.unaryNat) ((wordCode).prod ((wordCode).prod (e.list))))).comp (fp_snd (wordCode) ((wordCode).prod (e.list)))).comp (fp_snd (wordCode) (e.list)))

theorem fp_returning (e : BitEncoding A) : FP (stateCode e) (BitEncoding.bool) State.returning :=
  ((fp_stateView e).comp (fp_fst (BitEncoding.bool) ((BitEncoding.unaryNat).prod ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e))))))))

theorem fp_currentLen (e : BitEncoding A) : FP (stateCode e) (BitEncoding.unaryNat) State.currentLen :=
  (((fp_stateView e).comp (fp_snd (BitEncoding.bool) ((BitEncoding.unaryNat).prod ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))))).comp (fp_fst (BitEncoding.unaryNat) ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))))

theorem fp_currentTarget (e : BitEncoding A) : FP (stateCode e) (wordCode) State.currentTarget :=
  ((((fp_stateView e).comp (fp_snd (BitEncoding.bool) ((BitEncoding.unaryNat).prod ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))))).comp (fp_snd (BitEncoding.unaryNat) ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e))))))).comp (fp_fst (wordCode) ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e))))))

theorem fp_returnedLabels (e : BitEncoding A) : FP (stateCode e) (e.list) State.returnedLabels :=
  (((((fp_stateView e).comp (fp_snd (BitEncoding.bool) ((BitEncoding.unaryNat).prod ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))))).comp (fp_snd (BitEncoding.unaryNat) ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e))))))).comp (fp_snd (wordCode) ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))).comp (fp_fst (e.list) (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))

theorem fp_stack (e : BitEncoding A) : FP (stateCode e) ((frameCode e).list) State.stack :=
  ((((((fp_stateView e).comp (fp_snd (BitEncoding.bool) ((BitEncoding.unaryNat).prod ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))))).comp (fp_snd (BitEncoding.unaryNat) ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e))))))).comp (fp_snd (wordCode) ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))).comp (fp_snd (e.list) (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e))))).comp (fp_fst ((frameCode e).list) ((ComplexityTypeCache.cacheEncoding e))))

theorem fp_cache (e : BitEncoding A) : FP (stateCode e) ((ComplexityTypeCache.cacheEncoding e)) State.cache :=
  ((((((fp_stateView e).comp (fp_snd (BitEncoding.bool) ((BitEncoding.unaryNat).prod ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))))).comp (fp_snd (BitEncoding.unaryNat) ((wordCode).prod ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e))))))).comp (fp_snd (wordCode) ((e.list).prod (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e)))))).comp (fp_snd (e.list) (((frameCode e).list).prod ((ComplexityTypeCache.cacheEncoding e))))).comp (fp_snd ((frameCode e).list) ((ComplexityTypeCache.cacheEncoding e))))

theorem fp_buildFrame {C : Type} (ec : BitEncoding C) (e : BitEncoding A)
    (len : C → ℕ) (target colors : C → List ℕ) (labels : C → List A)
    (hl : FP ec BitEncoding.unaryNat len) (ht : FP ec wordCode target)
    (hc : FP ec wordCode colors) (ha : FP ec e.list labels) :
    FP ec (frameCode e) (fun x => Frame.mk (len x) (target x) (colors x) (labels x)) :=
  (hl.pair (ht.pair (hc.pair ha))).comp (fp_frameOfView e)

theorem fp_buildState {C : Type} (ec : BitEncoding C) (e : BitEncoding A)
    (returning : C → Bool) (len : C → ℕ) (target : C → List ℕ) (labels : C → List A)
    (stack : C → List (Frame A)) (cache : C → ComplexityTypeCache.Cache A)
    (hr : FP ec BitEncoding.bool returning) (hl : FP ec BitEncoding.unaryNat len)
    (ht : FP ec wordCode target) (ha : FP ec e.list labels)
    (hs : FP ec (frameCode e).list stack) (hc : FP ec (ComplexityTypeCache.cacheEncoding e) cache) :
    FP ec (stateCode e) (fun x => State.mk (returning x) (len x) (target x) (labels x) (stack x) (cache x)) :=
  (hr.pair (hl.pair (ht.pair (ha.pair (hs.pair hc))))).comp (fp_stateOfView e)

/-- Dynamic index replacement preserves the exact target length on every raw word. -/
theorem fp_replaceAt : FP ((BitEncoding.nat.prod BitEncoding.nat).prod wordCode) wordCode
    (fun p => replaceAt p.2 p.1.1 p.1.2) := by
  let ec := BitEncoding.nat.prod BitEncoding.nat
  let ei := BitEncoding.nat.prod BitEncoding.nat
  have hc := fp_fst ec ei
  have hk := hc.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have ha := hc.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hp := fp_snd ec ei
  have hx := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hi := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have htest := (hi.pair hk).comp NatListSumMachines.fp_equal
  have hbody := htest.ite ha hx
  have hz := (fp_snd ec wordCode).comp (ListIndexMachines.fp_zipIdx BitEncoding.nat)
  exact ((fp_fst ec wordCode).pair hz).comp
    (ListContextMachines.fp_mapWithContext ec ei BitEncoding.nat _ hbody)

theorem fp_unarySucc : FP BitEncoding.unaryNat BitEncoding.unaryNat Nat.succ :=
  (UnaryPolynomialMachines.fp_eval (Polynomial.X+1)).congr (fun n => by simp)

end ComplexCSP.ComplexityTypeStackMachines
