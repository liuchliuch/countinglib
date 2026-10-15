import ComplexCSP.Structure.MaltsevWitnessInsert
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ}
structure FiniteConstraint (d n : ℕ) where
  arity : ℕ
  scope : Fin arity → Fin n
  accept : (Fin arity → Fin d) → Bool
def Satisfies (cs : List (FiniteConstraint d n)) (x : Fin n → Fin d) : Prop :=
  ∀ c ∈ cs, c.accept (x ∘ c.scope) = true
def TablesPreserved (m : Operation (Fin d)) (cs : List (FiniteConstraint d n)) : Prop :=
  ∀ c ∈ cs, Preserves m {x | c.accept x = true}
def fullCode (a : Fin d) (n : ℕ) : Code (Fin d) n where
  seed := some (Vector.ofFn (fun _ => a))
  lookup i b := some (Vector.ofFn (Function.update (fun _ => a) i b))
theorem fullCode_correct (a : Fin d) (n : ℕ) : Correct (fullCode a n) Set.univ := by
  constructor
  · intro x _; trivial
  · intro _; exact ⟨_, rfl⟩
  · intro i b x hx
    have he := Option.some.inj hx
    subst x
    exact ⟨Set.mem_univ _, by simp⟩
  · intro i x _; exact ⟨_, rfl⟩
  · intro i b c x y _ hx hy
    have he := Option.some.inj hx
    have he' := Option.some.inj hy
    subst x y
    intro j hj
    have hji : j ≠ i := by intro h; subst j; omega
    simp [hji]
def constructFrom (m : Operation (Fin d)) : Code (Fin d) n → List (FiniteConstraint d n) → StoredCode d n
  | W, [] => storeCode W
  | W, c :: cs => constructFrom m (storeCode (insertConstraint m W c.scope c.accept)).toCode cs
theorem constructFrom_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    (cs : List (FiniteConstraint d n)) (hcs : TablesPreserved m cs)
    (W : Code (Fin d) n) (R : Set (Fin n → Fin d)) (hR : Preserves m R) (hW : Correct W R) :
    Correct (constructFrom m W cs).toCode {x | x ∈ R ∧ Satisfies cs x} := by
  induction cs generalizing W R with
  | nil => simpa [constructFrom, Satisfies] using hW
  | cons c cs ih =>
    have hc : Preserves m {x | c.accept x = true} := hcs c List.mem_cons_self
    have htail : TablesPreserved m cs := fun c hc => hcs c (List.mem_cons_of_mem _ hc)
    have hW' := insertConstraint_correct hm hR hW c.scope c.accept hc
    have hR' := constraintRelation_preserves hR c.scope c.accept hc
    have h := ih htail (insertConstraint m W c.scope c.accept) (constraintRelation R c.scope c.accept) hR' hW'
    simp only [constructFrom, storeCode_toCode]
    convert h using 1
    ext x
    simp only [Set.mem_ofPred_eq, Satisfies, List.mem_cons, forall_eq_or_imp, constraintRelation]
    tauto
def construct (m : Operation (Fin d)) (defaultValue : Fin d) (cs : List (FiniteConstraint d n)) : StoredCode d n :=
  constructFrom m (fullCode defaultValue n) cs
theorem construct_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    (defaultValue : Fin d) (cs : List (FiniteConstraint d n)) (hcs : TablesPreserved m cs) :
    Correct (construct m defaultValue cs).toCode {x | Satisfies cs x} := by
  have h := constructFrom_correct hm cs hcs (fullCode defaultValue n) Set.univ
    (fun _ _ _ _ _ _ => Set.mem_univ _) (fullCode_correct defaultValue n)
  simpa [construct] using h
theorem satisfies_preserved {m : Operation (Fin d)} (cs : List (FiniteConstraint d n)) (hcs : TablesPreserved m cs) :
    Preserves m {x | Satisfies cs x} := by
  intro x hx y hy z hz c hc
  exact hcs c hc _ (hx c hc) _ (hy c hc) _ (hz c hc)
theorem construct_member_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    (defaultValue : Fin d) (cs : List (FiniteConstraint d n)) (hcs : TablesPreserved m cs) (x : Tuple (Fin d) n) :
    member m (construct m defaultValue cs).toCode x = true ↔ Satisfies cs (view x) :=
  member_correct hm (satisfies_preserved cs hcs) (construct_correct hm defaultValue cs hcs) x
theorem construct_seed_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    (defaultValue : Fin d) (cs : List (FiniteConstraint d n)) (hcs : TablesPreserved m cs) :
    (construct m defaultValue cs).seed.isSome = true ↔ ∃ x, Satisfies cs x := by
  have h := construct_correct hm defaultValue cs hcs
  constructor
  · intro hs
    cases he : (construct m defaultValue cs).seed with
    | none => simp [he] at hs
    | some x => exact ⟨view x, h.seed_sound x he⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := h.seed_complete ⟨x, hx⟩
    simpa [StoredCode.toCode] using congrArg Option.isSome hy
end ComplexCSP.MaltsevWitness
