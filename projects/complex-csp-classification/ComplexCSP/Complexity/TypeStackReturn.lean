import ComplexCSP.Complexity.TypeStackCodecs

/-! # Actual FP return/continuation transitions for memoized type search -/
namespace ComplexCSP.ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives
open MaltsevTypeStack ComplexityWitnessPrimitives
variable {A : Type}

theorem fp_isEmpty (e : BitEncoding A) : FP e.list BitEncoding.bool List.isEmpty := by
  have hz := ((ListCodecMachines.fp_length e).pair (fp_const e.list BitEncoding.nat 0)).comp
    NatListSumMachines.fp_equal
  exact hz.congr (fun xs => by cases xs <;> rfl)

theorem fp_isNone (e : BitEncoding A) : FP (optionCode e) BitEncoding.bool Option.isNone := by
  have hv : FP (optionCode e) e.list Option.toList := fp_code_view _ _ _ (fun _ => rfl)
  exact (hv.comp (fp_isEmpty e)).congr (fun x => by cases x <;> rfl)

theorem fp_boolChoice {C B : Type} (ec : BitEncoding C) (eb : BitEncoding B)
    {test : C → Bool} {yes no : C → B} (ht : FP ec BitEncoding.bool test)
    (hy : FP ec eb yes) (hn : FP ec eb no) :
    FP ec eb (fun x => if test x then yes x else no x) := by
  have hp : FP ec BitEncoding.bool (fun x => decide (test x = true)) := ht.congr (fun _ => by simp)
  exact hp.ite hy hn

def defaultFrame : Frame A := ⟨0,[],[],[]⟩
def defaultState : State A := ⟨true,0,[],[],[],[]⟩

variable [DecidableEq A]

def returnTransition (state : State A) : Option (State A) :=
  let frame := state.stack.headD defaultFrame
  let rest := state.stack.tail
  let combined := (frame.accumulatedLabels ++ state.returnedLabels).dedup
  if state.stack.isEmpty then none else
    if frame.remainingColors.isEmpty then
      some (returnState frame.parentLen frame.parentTarget combined rest
        ((frame.parentLen,combined)::state.cache))
    else
      let next := frame.remainingColors.headD 0
      let frame' : Frame A := ⟨frame.parentLen,frame.parentTarget,frame.remainingColors.tail,combined⟩
      some (callState (frame.parentLen+1) (replaceAt frame.parentTarget frame.parentLen next)
        (frame'::rest) state.cache)

theorem returnTransition_correct (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    (state : State A) (hs : state.returning = true) :
    returnTransition state = MaltsevTypeStack.step dimension colors reconstruct label state := by
  unfold returnTransition MaltsevTypeStack.step
  rw [hs]
  cases hstack : state.stack with
  | nil => rfl
  | cons frame rest =>
    cases hcolors : frame.remainingColors <;> simp [hstack,hcolors]

/-- Every stored continuation field is parsed by actual pair/list machines. -/
theorem fp_returnTransition (e : BitEncoding A) :
    FP (stateCode e) (optionCode (stateCode e)) returnTransition := by
  let inputCode := stateCode e
  let entryCode := BitEncoding.nat.prod e.list
  have hstack := fp_stack e
  have hframe := hstack.comp (ListDecompositionMachines.fp_headD (frameCode e) defaultFrame)
  have hrest := hstack.comp (ListDecompositionMachines.fp_tail (frameCode e) defaultFrame)
  have hlen := hframe.comp (fp_parentLen e)
  have hlenNat := hlen.comp UnaryNatConversionMachine.fp_conversion
  have htarget := hframe.comp (fp_parentTarget e)
  have hcolors := hframe.comp (fp_remainingColors e)
  have hacc := hframe.comp (fp_accumulatedLabels e)
  have hcombined := ((hacc.pair (fp_returnedLabels e)).comp
    (ListMutationMachines.fp_append e)).comp (ComplexityTypeCache.fp_dedup e)
  have hcache := fp_cache e
  have hnewCache := ((hlenNat.pair hcombined).pair hcache).comp
    (ListMutationMachines.fp_cons entryCode)
  have hreturn := fp_buildState inputCode e _ _ _ _ _ _
    (fp_const inputCode BitEncoding.bool true) hlen htarget hcombined hrest hnewCache
  have hreturnSome := hreturn.comp (fp_some (stateCode e))
  have hnext := hcolors.comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)
  have hremaining := hcolors.comp (ListDecompositionMachines.fp_tail BitEncoding.nat 0)
  have hnewFrame := fp_buildFrame inputCode e _ _ _ _ hlen htarget hremaining hcombined
  have hnewStack := (hnewFrame.pair hrest).comp (ListMutationMachines.fp_cons (frameCode e))
  have hnextTarget := ((hlenNat.pair hnext).pair htarget).comp fp_replaceAt
  have hcall := fp_buildState inputCode e _ _ _ _ _ _
    (fp_const inputCode BitEncoding.bool false) (hlen.comp fp_unarySucc)
    hnextTarget (fp_const inputCode e.list []) hnewStack hcache
  have hcallSome := hcall.comp (fp_some (stateCode e))
  have hcolorsEmpty := hcolors.comp (fp_isEmpty BitEncoding.nat)
  have hbody := fp_boolChoice inputCode (optionCode (stateCode e)) hcolorsEmpty hreturnSome hcallSome
  have hstackEmpty := hstack.comp (fp_isEmpty (frameCode e))
  exact fp_boolChoice inputCode (optionCode (stateCode e)) hstackEmpty
    (fp_const inputCode (optionCode (stateCode e)) none) hbody

end ComplexCSP.ComplexityTypeStackMachines
