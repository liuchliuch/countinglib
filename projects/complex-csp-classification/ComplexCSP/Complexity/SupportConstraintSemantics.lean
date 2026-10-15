import ComplexCSP.Complexity.SupportConstraintMachines
import ComplexCSP.Structure.MaltsevWitnessInsert

/-! # Literal fixed-arity constraint-insertion agreement -/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityProjectedClosure
open PlanarHom PlanarHom.Complexity
variable {d n r : ℕ}

theorem filterAccepted_word (accept : (Fin r → Fin d) → Bool) (ρ : Fin r → Fin n)
    (xs : List (Tuple (Fin d) n)) :
    filterAccepted accept (scopeWord ρ) (xs.map word) =
      (xs.filter (fun x => accept (projectionKey ρ x))).map word := by
  simp only [filterAccepted,List.filter_map,Function.comp_def,project_word,acceptWord_key]

theorem constraintSeeds_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (ρ : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) :
    constraintSeeds (fun a b c => m (a,b,c)) accept (encodeCode W,scopeWord ρ) =
      (MaltsevWitness.constraintSeeds m W ρ accept).map word := by
  rw [constraintSeeds,storedRows_encodeCode,projectedClosure_word,filterAccepted_word]
  rfl

theorem scopeWord_cons (i : Fin n) (ρ : Fin r → Fin n) :
    scopeWord (Fin.cons i ρ) = i.val::scopeWord ρ := by
  simp only [scopeWord,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]

theorem constraintCandidates_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (ρ : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) :
    constraintCandidates (fun a b c => m (a,b,c)) accept ((encodeCode W,scopeWord ρ),i.val) =
      (MaltsevWitness.constraintCandidates m W ρ accept i).map word := by
  rw [constraintCandidates,storedRows_encodeCode,← scopeWord_cons i ρ,projectedClosure_word,filterAccepted_word]
  rfl

theorem constraintExtension_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (ρ : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) (a : Fin d)
    (z : Tuple (Fin d) n) :
    constraintExtension (fun a b c => m (a,b,c)) accept ((encodeCode W,scopeWord ρ),i.val,a.val,word z) =
      maybeWord (MaltsevWitness.constraintExtension m W ρ accept i a z) := by
  rw [constraintExtension,replaceAt_word,safeTarget_actual,prefixFrame_word,
    projectedClosure_word,filterAccepted_word,first_map_word]
  rfl

private theorem maybeWord_isSome (x : Option (Tuple (Fin d) n)) :
    !(decide (maybeWord x=[])) = x.isSome := by cases x <;> rfl

theorem constraintAnchor_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (ρ : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) (a : Fin d) :
    constraintAnchor (fun a b c => m (a,b,c)) accept ((encodeCode W,scopeWord ρ),i.val,a.val) =
      maybeWord (MaltsevWitness.constraintAnchor m W ρ accept i a) := by
  simp only [constraintAnchor,constraintCandidates_encodeCode,List.filter_map,
    Function.comp_def,constraintExtension_encodeCode]
  rw [first_map_word,List.head?_filter]
  apply congrArg maybeWord
  unfold MaltsevWitness.constraintAnchor
  congr 1
  funext x
  cases MaltsevWitness.constraintExtension m W ρ accept i a x <;> simp [maybeWord]

theorem insertLookup_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (ρ : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) (a : Fin d) :
    insertLookup (fun a b c => m (a,b,c)) accept ((encodeCode W,scopeWord ρ),i.val,a.val) =
      maybeWord ((MaltsevWitness.insertConstraint m W ρ accept).lookup i a) := by
  rw [insertLookup,constraintAnchor_encodeCode]
  simp only [MaltsevWitness.insertConstraint]
  cases h : MaltsevWitness.constraintAnchor m W ρ accept i a with
  | none => simp [maybeWord]
  | some z =>
    simp only [maybeWord,Option.toList_some,List.map_singleton,List.cons_ne_self,
      List.headD_cons,↓reduceIte,Option.bind_some]
    exact constraintExtension_encodeCode m W ρ accept i a z

private theorem map_range_eq_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

/-- Complete ordered table/seed agreement with the source constructor, without
assuming preservation or correctness of the relation represented by W. -/
theorem insertConstraint_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (ρ : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) :
    insertConstraint (fun a b c => m (a,b,c)) accept (encodeCode W,scopeWord ρ) =
      encodeCode (MaltsevWitness.insertConstraint m W ρ accept) := by
  apply Prod.ext
  · simp only [insertConstraint,encodeCode_table_length,map_range_eq_ofFn]
    change List.ofFn _ = List.ofFn _
    congr 1
    funext i
    congr 1
    funext a
    exact insertLookup_encodeCode m W ρ accept i a
  · change first (constraintSeeds (fun a b c => m (a,b,c)) accept (encodeCode W,scopeWord ρ)) = _
    rw [constraintSeeds_encodeCode,first_map_word]
    rfl

variable (m : Fin d → Fin d → Fin d → Fin d)

def insertScoped (accept : (Fin r → Fin d) → Bool)
    (p : {p : RawWitness × List ℕ // ScopeInputValid (d:=d) r p}) :
    {W : RawWitness // PositiveWitness (d:=d) W} :=
  ⟨insertConstraint m accept p.val,by
    obtain ⟨n,hn,W,ρ,hW,hρ⟩ := p.property
    refine ⟨n,hn,MaltsevWitness.insertConstraint (fun p => m p.1 p.2.1 p.2.2) W ρ accept,?_⟩
    have he : p.val = (encodeCode W,scopeWord ρ) := Prod.ext hW hρ
    rw [he]
    exact insertConstraint_encodeCode (fun p => m p.1 p.2.1 p.2.2) W ρ accept⟩

/-- The raw machine returns its reachable-shape promise by the proved literal
constructor identity; no runtime witness-shape oracle is called. -/
theorem fp_insertScoped (accept : (Fin r → Fin d) → Bool) :
    FP (validScopeInputCode d r) (positiveWitnessCode d) (insertScoped m accept) :=
  (fp_insertConstraint m accept).transportOutput (fun _ => rfl)

@[simp] theorem insertScoped_dimension (accept : (Fin r → Fin d) → Bool)
    (p : {p : RawWitness × List ℕ // ScopeInputValid (d:=d) r p}) :
    (insertScoped m accept p).val.1.length = p.val.1.1.length := by
  simp [insertScoped,insertConstraint]

end ComplexCSP.ComplexitySupportWitnessPrimitives
