import ComplexCSP.Complexity.TypeStackReturn

/-! # Actual FP call transitions and full type-search control step

The immutable context is ordinary encoded input. Callback compilation is a
modular theorem whose concrete instantiations are the already proved witness
reconstruction and ComputeF/normalization machines, not supplied runtime oracles.
-/
set_option maxHeartbeats 3000000
namespace ComplexCSP.ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open MaltsevTypeStack ComplexityWitnessPrimitives
variable {A C : Type} [DecidableEq A]

omit [DecidableEq A] in
theorem fp_optionGetD (e : BitEncoding A) (fallback : A) :
    FP (optionCode e) e (fun x => x.getD fallback) := by
  have hv : FP (optionCode e) e.list Option.toList := fp_code_view _ _ _ (fun _ => rfl)
  exact (hv.comp (ListDecompositionMachines.fp_headD e fallback)).congr
    (fun x => by cases x <;> rfl)

def callTransition (dimension : C → ℕ) (colors : List ℕ)
    (reconstruct : C × (ℕ × List ℕ) → Option (List ℕ)) (label : C × List ℕ → A)
    (p : C × State A) : Option (State A) :=
  let c := p.1
  let s := p.2
  let result := reconstruct (c,s.currentLen,s.currentTarget)
  let a := label (c,result.getD [])
  let cached := ComplexityTypeCache.lookup s.cache s.currentLen a
  if result.isNone then some (returnState s.currentLen s.currentTarget [] s.stack s.cache)
  else if cached.1 then some (returnState s.currentLen s.currentTarget cached.2.dedup s.stack s.cache)
  else if s.currentLen < dimension c then
    match colors with
    | [] => some (returnState s.currentLen s.currentTarget [] s.stack ((s.currentLen,[])::s.cache))
    | b::rest =>
      let frame : Frame A := ⟨s.currentLen,s.currentTarget,rest,[]⟩
      some (callState (s.currentLen+1) (replaceAt s.currentTarget s.currentLen b) (frame::s.stack) s.cache)
  else some (returnState s.currentLen s.currentTarget [a] s.stack ((s.currentLen,[a])::s.cache))

theorem callTransition_correct (dimension : C → ℕ) (colors : List ℕ)
    (reconstruct : C × (ℕ × List ℕ) → Option (List ℕ)) (label : C × List ℕ → A)
    (p : C × State A) (hs : p.2.returning = false) :
    callTransition dimension colors reconstruct label p =
      MaltsevTypeStack.step (dimension p.1) colors
        (fun len word => reconstruct (p.1,len,word)) (fun word => label (p.1,word)) p.2 := by
  unfold callTransition MaltsevTypeStack.step
  dsimp only
  rw [hs]
  cases hr : reconstruct (p.1,p.2.currentLen,p.2.currentTarget) with
  | none => simp
  | some witness =>
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
    rw [ComplexityTypeCache.lookup_eq_cachedTypeList]
    cases hc : MaltsevWitness.cachedTypeList p.2.cache p.2.currentLen (label (p.1,witness)) <;> simp <;> rfl

theorem fp_callTransition (ec : BitEncoding C) (e : BitEncoding A)
    (dimension : C → ℕ) (colors : List ℕ)
    (reconstruct : C × (ℕ × List ℕ) → Option (List ℕ)) (label : C × List ℕ → A)
    (hdim : FP ec BitEncoding.unaryNat dimension)
    (hrec : FP (ec.prod (BitEncoding.unaryNat.prod wordCode)) (optionCode wordCode) reconstruct)
    (hlab : FP (ec.prod wordCode) e label) :
    FP (ec.prod (stateCode e)) (optionCode (stateCode e))
      (callTransition dimension colors reconstruct label) := by
  let inputCode := ec.prod (stateCode e)
  let entryCode := BitEncoding.nat.prod e.list
  have hc := fp_fst ec (stateCode e)
  have hs := fp_snd ec (stateCode e)
  have hlen := hs.comp (fp_currentLen e)
  have hlenNat := hlen.comp UnaryNatConversionMachine.fp_conversion
  have htarget := hs.comp (fp_currentTarget e)
  have hstack := hs.comp (fp_stack e)
  have hcache := hs.comp (fp_cache e)
  have hresult := (hc.pair (hlen.pair htarget)).comp hrec
  have hwitness := hresult.comp (fp_optionGetD wordCode [])
  have ha := (hc.pair hwitness).comp hlab
  have hcached := ((hlenNat.pair ha).pair hcache).comp (ComplexityTypeCache.fp_lookup e)
  have hcacheHit := hcached.comp (fp_fst BitEncoding.bool e.list)
  have hcacheLabels := (hcached.comp (fp_snd BitEncoding.bool e.list)).comp (ComplexityTypeCache.fp_dedup e)
  have hreturnEmpty := fp_buildState inputCode e _ _ _ _ _ _
    (fp_const inputCode BitEncoding.bool true) hlen htarget (fp_const inputCode e.list []) hstack hcache
  have hreturnCached := fp_buildState inputCode e _ _ _ _ _ _
    (fp_const inputCode BitEncoding.bool true) hlen htarget hcacheLabels hstack hcache
  have hone := (ha.pair (fp_const inputCode e.list [])).comp (ListMutationMachines.fp_cons e)
  have hcacheOne := ((hlenNat.pair hone).pair hcache).comp (ListMutationMachines.fp_cons entryCode)
  have hreturnOne := fp_buildState inputCode e _ _ _ _ _ _
    (fp_const inputCode BitEncoding.bool true) hlen htarget hone hstack hcacheOne
  have hchild : FP inputCode (stateCode e) (fun p =>
      match colors with
      | [] => returnState p.2.currentLen p.2.currentTarget [] p.2.stack ((p.2.currentLen,[])::p.2.cache)
      | b::rest => callState (p.2.currentLen+1) (replaceAt p.2.currentTarget p.2.currentLen b)
          (Frame.mk p.2.currentLen p.2.currentTarget rest [] :: p.2.stack) p.2.cache) := by
    cases colors with
    | nil =>
      have hcacheEmpty := ((hlenNat.pair (fp_const inputCode e.list [])).pair hcache).comp
        (ListMutationMachines.fp_cons entryCode)
      exact fp_buildState inputCode e _ _ _ _ _ _
        (fp_const inputCode BitEncoding.bool true) hlen htarget (fp_const inputCode e.list []) hstack hcacheEmpty
    | cons b rest =>
      have hframe := fp_buildFrame inputCode e _ _ _ _ hlen htarget
        (fp_const inputCode wordCode rest) (fp_const inputCode e.list [])
      have hnextStack := (hframe.pair hstack).comp (ListMutationMachines.fp_cons (frameCode e))
      have hnextTarget := ((hlenNat.pair (fp_const inputCode BitEncoding.nat b)).pair htarget).comp fp_replaceAt
      exact fp_buildState inputCode e _ _ _ _ _ _
        (fp_const inputCode BitEncoding.bool false) (hlen.comp fp_unarySucc) hnextTarget
        (fp_const inputCode e.list []) hnextStack hcache
  have hdimension := (hc.comp hdim).comp UnaryNatConversionMachine.fp_conversion
  have hlt := (hlenNat.pair hdimension).comp BinaryArithmetic.fp_comparison
  have hmiss := hlt.ite hchild hreturnOne
  have hhave := fp_boolChoice inputCode (stateCode e) hcacheHit hreturnCached hmiss
  have hnone := hresult.comp (fp_isNone wordCode)
  have hnext := fp_boolChoice inputCode (stateCode e) hnone hreturnEmpty hhave
  apply (hnext.comp (fp_some (stateCode e))).congr
  intro p
  dsimp only [Function.comp_apply, Function.comp_def, callTransition, returnState, callState, id_eq]
  split_ifs <;> cases colors <;> rfl

def contextualStep (dimension : C → ℕ) (colors : List ℕ)
    (reconstruct : C × (ℕ × List ℕ) → Option (List ℕ)) (label : C × List ℕ → A)
    (p : C × State A) : Option (State A) :=
  if p.2.returning then returnTransition p.2 else callTransition dimension colors reconstruct label p

theorem contextualStep_correct (dimension : C → ℕ) (colors : List ℕ)
    (reconstruct : C × (ℕ × List ℕ) → Option (List ℕ)) (label : C × List ℕ → A)
    (p : C × State A) : contextualStep dimension colors reconstruct label p =
      MaltsevTypeStack.step (dimension p.1) colors
        (fun len word => reconstruct (p.1,len,word)) (fun word => label (p.1,word)) p.2 := by
  unfold contextualStep
  cases hs : p.2.returning with
  | false => exact callTransition_correct dimension colors reconstruct label p hs
  | true => exact returnTransition_correct _ _ _ _ p.2 hs

theorem fp_contextualStep (ec : BitEncoding C) (e : BitEncoding A)
    (dimension : C → ℕ) (colors : List ℕ)
    (reconstruct : C × (ℕ × List ℕ) → Option (List ℕ)) (label : C × List ℕ → A)
    (hdim : FP ec BitEncoding.unaryNat dimension)
    (hrec : FP (ec.prod (BitEncoding.unaryNat.prod wordCode)) (optionCode wordCode) reconstruct)
    (hlab : FP (ec.prod wordCode) e label) :
    FP (ec.prod (stateCode e)) (optionCode (stateCode e))
      (contextualStep dimension colors reconstruct label) := by
  have hs := fp_snd ec (stateCode e)
  exact fp_boolChoice _ _ (hs.comp (fp_returning e)) (hs.comp (fp_returnTransition e))
    (fp_callTransition ec e dimension colors reconstruct label hdim hrec hlab)

end ComplexCSP.ComplexityTypeStackMachines
