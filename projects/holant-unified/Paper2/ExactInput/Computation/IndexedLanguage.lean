import Paper2.ExactInput.FiniteLanguage

/-! A fixed transformed language with the same table indices and arities.
Constructing these finite constants is semantic existence, not an algorithm run
on the graph input and not a uniform conversion on arbitrary input languages. -/
set_option backward.isDefEq.respectTransparency false

namespace Paper2.ExactInput.Computation
open Paper2.Tractable

noncomputable def rootOf (z : AlgebraicComplex) : RootCode :=
  Classical.choose (RootCode.minimal_coverage z)

theorem rootOf_spec (z : AlgebraicComplex) : (rootOf z).MinimalRepresents (z : ℂ) :=
  Classical.choose_spec (RootCode.minimal_coverage z)

noncomputable def codeOf {n : ℕ} (f : Signature AlgebraicComplex n) : SignatureCode :=
  ⟨n, List.ofFn (fun i : Fin (2 ^ n) => rootOf (f ((wordIndex n).symm i)))⟩

@[simp] theorem codeOf_arity {n : ℕ} (f : Signature AlgebraicComplex n) :
    (codeOf f).arity = n := rfl

theorem codeOf_valid {n : ℕ} (f : Signature AlgebraicComplex n) : (codeOf f).Valid := by
  refine ⟨by simp [codeOf], ?_⟩
  intro i
  simp only [codeOf, List.get_eq_getElem, List.getElem_ofFn]
  exact ⟨_, rootOf_spec _⟩

@[simp] theorem codeOf_denote {n : ℕ} (f : Signature AlgebraicComplex n) :
    (codeOf f).denote (codeOf_valid f) = f := by
  funext x
  apply RootCode.value_eq
  have he : (codeOf f).entry (codeOf_valid f) x = rootOf (f x) := by
    simp only [SignatureCode.entry, codeOf, List.get_eq_getElem, List.getElem_ofFn]
    change rootOf (f ((wordIndex n).symm (wordIndex n x))) = rootOf (f x)
    rw [Equiv.symm_apply_apply]
  rw [he]
  exact rootOf_spec _

/-- Label i in the new language denotes exactly A applied to old label i. -/
noncomputable def indexedLanguage (L : Language)
    (A : (n : ℕ) → Signature AlgebraicComplex n → Signature AlgebraicComplex n) : Language := by
  let raw := List.ofFn (fun i : Fin L.count => codeOf (A _ (L.signature i)))
  refine ⟨raw, ?_⟩
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact codeOf_valid _

@[simp] theorem indexedLanguage_count (L : Language)
    (A : (n : ℕ) → Signature AlgebraicComplex n → Signature AlgebraicComplex n) :
    (indexedLanguage L A).count = L.count := by simp [Language.count, indexedLanguage]

@[simp] theorem indexedLanguage_code (L : Language)
    (A : (n : ℕ) → Signature AlgebraicComplex n → Signature AlgebraicComplex n)
    (i : Fin L.count) :
    (indexedLanguage L A).code (Fin.cast (indexedLanguage_count L A).symm i) =
      codeOf (A _ (L.signature i)) := by
  simp only [Language.code, indexedLanguage, List.get_eq_getElem, List.getElem_ofFn]
  rfl

@[simp] theorem indexedLanguage_arity (L : Language)
    (A : (n : ℕ) → Signature AlgebraicComplex n → Signature AlgebraicComplex n) :
    (indexedLanguage L A).arity = L.arity := by
  funext i
  by_cases hi : i < L.count
  · have h := (indexedLanguage L A).arity_index
      (Fin.cast (indexedLanguage_count L A).symm ⟨i, hi⟩)
    simpa only [Fin.val_cast, indexedLanguage_code, codeOf_arity] using h
  · have hiL : L.val.length ≤ i := Nat.le_of_not_gt hi
    have hiM : (indexedLanguage L A).val.length ≤ i := by
      change (indexedLanguage L A).count ≤ i
      rw [indexedLanguage_count]
      exact hiL
    simp [Language.arity, List.getElem?_eq_none hiL, List.getElem?_eq_none hiM]

/-- Dependent arity transport changes no table values. -/
lemma signature_cast_heq {n m : ℕ} (h : n = m) (f : Signature AlgebraicComplex m) :
    HEq (fun x : Fin n → Bool => f (fun j => x (Fin.cast h.symm j))) f := by
  cases h
  rfl

lemma language_signature_heq (L : Language) (i : Fin L.count) :
    HEq (L.signature i) ((L.code i).denote (L.code_valid i)) :=
  signature_cast_heq (L.arity_index i) _

lemma denote_code_heq {c d : SignatureCode} (h : c = d) (hc : c.Valid) (hd : d.Valid) :
    HEq (c.denote hc) (d.denote hd) := by
  cases h
  rfl

/-- Exact values at each original label, including its ordered ports. -/
theorem indexedLanguage_signature (L : Language)
    (A : (n : ℕ) → Signature AlgebraicComplex n → Signature AlgebraicComplex n)
    (i : Fin L.count) :
    HEq ((indexedLanguage L A).signature (Fin.cast (indexedLanguage_count L A).symm i))
      (A _ (L.signature i)) := by
  apply (language_signature_heq _ _).trans
  exact (denote_code_heq (indexedLanguage_code L A i) _ _).trans (heq_of_eq (codeOf_denote _))

theorem indexedLanguage_any (L : Language)
    (A : (n : ℕ) → Signature AlgebraicComplex n → Signature AlgebraicComplex n)
    (i : Fin L.count) :
    (⟨(indexedLanguage L A).arity i.val,
      (indexedLanguage L A).signature (Fin.cast (indexedLanguage_count L A).symm i)⟩ :
        AnySignature AlgebraicComplex) = ⟨L.arity i.val, A _ (L.signature i)⟩ :=
  Sigma.ext (congrFun (indexedLanguage_arity L A) i.val) (indexedLanguage_signature L A i)

/-- The exact denoted family of a shape-preserving table transformation. -/
theorem indexedLanguage_family (L : Language)
    (A : (n : ℕ) → Signature AlgebraicComplex n → Signature AlgebraicComplex n) :
    (indexedLanguage L A).family =
      (fun f : AnySignature AlgebraicComplex => ⟨f.1, A f.1 f.2⟩) '' L.family := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    let j : Fin L.count := Fin.cast (indexedLanguage_count L A) i
    refine ⟨⟨L.arity j.val, L.signature j⟩, ⟨j, rfl⟩, ?_⟩
    have h := indexedLanguage_any L A j
    have hback : Fin.cast (indexedLanguage_count L A).symm j = i := Fin.ext rfl
    exact h.symm.trans (congrArg (fun k : Fin (indexedLanguage L A).count =>
      (⟨(indexedLanguage L A).arity k.val, (indexedLanguage L A).signature k⟩ :
        AnySignature AlgebraicComplex)) hback)
  · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
    exact ⟨Fin.cast (indexedLanguage_count L A).symm i, indexedLanguage_any L A i⟩

end Paper2.ExactInput.Computation
