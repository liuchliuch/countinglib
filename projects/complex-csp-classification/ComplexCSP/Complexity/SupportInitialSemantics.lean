import ComplexCSP.Complexity.SupportInitialMachine

/-! # Exact original-constructor agreement for the initial support machine -/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityProjectedClosure ComplexityCSPValidation
variable {K : Type} [Field K] [DecidableEq K] {d s : ℕ}
variable (L : Language (Fin d) K (Fin s))

def packPositive {n : ℕ} (W : Code (Fin d) n) (hn : 0<n) : PositiveData d :=
  ⟨encodeCode W,n,hn,W,rfl⟩

omit [Field K] [DecidableEq K] in
theorem scopeWord_scope (g : ComplexityCSPCode.Code) (c : RawConstraint)
    (hc : ComplexityCSPCode.ConstraintValid L g.vertices c) :
    scopeWord (ComplexityCSPCode.scope L g c hc) = c.2 := by
  apply List.ext_getElem
  · simpa [scopeWord] using hc.choose_spec.1.symm
  · intro i hi hi'
    simp [scopeWord,ComplexityCSPCode.scope]

def decodedConstraint (g : ComplexityCSPCode.Code) (c : RawConstraint) : FiniteConstraint d g.vertices :=
  if hc : ComplexityCSPCode.ConstraintValid L g.vertices c then
    { arity := L.arity ⟨c.1,hc.choose⟩
      scope := ComplexityCSPCode.scope L g c hc
      accept := fun x => decide (L.value ⟨c.1,hc.choose⟩ x ≠ 0) }
  else { arity := 0, scope := Fin.elim0, accept := fun _ => true }

theorem decodedConstraints_eq (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    supportConstraints L g hg = g.constraints.map (decodedConstraint L g) := by
  unfold supportConstraints
  calc
    _ = g.constraints.attach.map (fun c => decodedConstraint L g c.val) := by
      apply List.map_congr_left
      intro c _
      simp only [decodedConstraint,dif_pos (hg c.val c.property)]
    _ = _ := List.attach_map_val

/-- A valid runtime row invokes precisely the original typed insertion step. -/
theorem supportStep_pack (m : Operation (Fin d)) (g : ComplexityCSPCode.Code)
    (W : Code (Fin d) g.vertices) (hn : 0<g.vertices) (c : RawConstraint)
    (hc : ComplexityCSPCode.ConstraintValid L g.vertices c) :
    supportStep L (fun a b c => m (a,b,c)) (packPositive W hn) c =
      packPositive (MaltsevWitness.insertConstraint m W
        (decodedConstraint L g c).scope (decodedConstraint L g c).accept) hn := by
  apply Subtype.ext
  have ht := (constraintValidTest_correct L g.vertices c).mpr hc
  simp only [supportStep,packPositive,encodeCode_table_length,ht,↓reduceIte,insertBySymbol]
  rw [dif_pos hc.choose]
  change insertConstraint (fun a b c => m (a,b,c)) (fun x => decide (L.value ⟨c.1,hc.choose⟩ x≠0))
    (encodeCode W,safeScope (L.arity ⟨c.1,hc.choose⟩) (encodeCode W,c.2)) = _
  have hs : safeScope (L.arity ⟨c.1,hc.choose⟩) (encodeCode W,c.2) = c.2 := by
    simpa only [scopeWord_scope L g c hc] using safeScope_actual W (ComplexityCSPCode.scope L g c hc)
  rw [hs]
  rw [decodedConstraint,dif_pos hc]
  simpa only [scopeWord_scope L g c hc] using
    insertConstraint_encodeCode m W (ComplexityCSPCode.scope L g c hc)
      (fun x => decide (L.value ⟨c.1,hc.choose⟩ x≠0))

/-- The raw fold and the source's recursive materialized constructor agree
literally, including each intermediate anchor choice. -/
theorem supportFold_constructFrom (m : Operation (Fin d)) (g : ComplexityCSPCode.Code)
    (cs : List RawConstraint) (hcs : ∀ c∈cs, ComplexityCSPCode.ConstraintValid L g.vertices c)
    (W : Code (Fin d) g.vertices) (hn : 0<g.vertices) :
    (cs.foldl (supportStep L (fun a b c => m (a,b,c))) (packPositive W hn)).val =
      encodeCode (constructFrom m W (cs.map (decodedConstraint L g))).toCode := by
  induction cs generalizing W with
  | nil => simp [constructFrom,packPositive]
  | cons c cs ih =>
    have hc := hcs c (by simp)
    have htail : ∀ c∈cs, ComplexityCSPCode.ConstraintValid L g.vertices c := fun c hc => hcs c (by simp [hc])
    rw [List.foldl_cons,supportStep_pack L m g W hn c hc]
    simp only [List.map_cons,constructFrom,storeCode_toCode]
    exact ih htail _

theorem initialWitness_pack (defaultValue : Fin d) (g : ComplexityCSPCode.Code) (hn : 0<g.vertices) :
    initialWitness defaultValue g = packPositive (MaltsevWitness.fullCode defaultValue g.vertices) hn := by
  apply Subtype.ext
  exact preparePositiveWitness_actual defaultValue (MaltsevWitness.fullCode defaultValue g.vertices) hn

omit [Field K] [DecidableEq K] in
theorem valid_zero_constraints (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (hn : g.vertices=0) : g.constraints=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro c hc
  have hv := hg c hc
  have hpos := L.arity_pos ⟨c.1,hv.choose⟩
  cases hs : c.2 with
  | nil =>
    have he := hv.choose_spec.1
    simp only [hs,List.length_nil] at he
    omega
  | cons v vs =>
    have he := hv.choose_spec.2 v (by simp [hs])
    omega

/-- The actual FP compiler returns exactly the existing computed support
constructor for every valid raw instance, including zero variables. -/
theorem rawSupportCompiler_encode (m : Operation (Fin d)) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    rawSupportCompiler L (fun a b c => m (a,b,c)) defaultValue g =
      encodeCode (rawSupportWitness L m defaultValue g hg).toCode := by
  by_cases hn : g.vertices=0
  · have hnil := valid_zero_constraints L g hg hn
    have hsc : supportConstraints L g hg = [] := by
      rw [decodedConstraints_eq L g hg,hnil]
      rfl
    simp only [rawSupportCompiler,hn,↓reduceIte,rawSupportWitness,construct,hsc,
      constructFrom,storeCode_toCode,fullCode_encode]
    rw [hn]
  · have hpos : 0<g.vertices := by omega
    rw [rawSupportCompiler,if_neg hn]
    unfold constructPositive
    rw [initialWitness_pack defaultValue g hpos,supportFold_constructFrom L m g g.constraints hg]
    rw [← decodedConstraints_eq L g hg]
    rfl

/-- Unconditional output shape at the exact original variable dimension.
Malformed constraints are allowed here; no validity or correctness premise is
used. This supplies the honest runtime context promise to the final evaluator. -/
theorem rawSupportCompiler_shape (m : Fin d → Fin d → Fin d → Fin d) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) :
    ∃ W : Code (Fin d) g.vertices, rawSupportCompiler L m defaultValue g = encodeCode W := by
  by_cases hn : g.vertices=0
  · refine ⟨MaltsevWitness.fullCode defaultValue g.vertices,?_⟩
    simp only [rawSupportCompiler,hn,↓reduceIte,fullCode_encode]
    rw [hn]
  · have hpos : 0<g.vertices := by omega
    have hinit : (initialWitness defaultValue g).val.1.length = g.vertices := by
      rw [initialWitness_pack defaultValue g hpos]
      exact encodeCode_table_length _
    have hdim := fold_supportStep_dimension L m (initialWitness defaultValue g) g.constraints
    change (constructPositive L m defaultValue g).val.1.length = _ at hdim
    rw [hinit] at hdim
    obtain ⟨k,_,W,hW⟩ := (constructPositive L m defaultValue g).property
    rw [hW,encodeCode_table_length] at hdim
    subst k
    exact ⟨W,by simpa only [rawSupportCompiler,if_neg hn] using hW⟩

/-- In the original literal table/seed representation expected by the runtime
membership and class machines. -/
theorem rawSupportCompiler_stored (m : Operation (Fin d)) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    rawSupportCompiler L (fun a b c => m (a,b,c)) defaultValue g =
      (rawTable (rawSupportWitness L m defaultValue g hg),maybeWord (rawSupportWitness L m defaultValue g hg).seed) := by
  rw [rawSupportCompiler_encode L m defaultValue g hg,encodeCode_stored]

end ComplexCSP.ComplexitySupportWitnessPrimitives
