import Paper2.ExactInput.FiniteLanguage

namespace Paper2.ExactInput
open Paper2.Tractable

private theorem sigma_cast_signature {m n : ℕ} (h : m = n)
    (f : Signature AlgebraicComplex n) :
    (⟨m, fun x => f (fun j => x (Fin.cast h.symm j))⟩ : AnySignature AlgebraicComplex) = ⟨n, f⟩ := by
  subst n
  rfl

private theorem signatureCode_denote_congr {a b : SignatureCode} (h : a = b)
    (ha : a.Valid) (hb : b.Valid) :
    (⟨a.arity, a.denote ha⟩ : AnySignature AlgebraicComplex) = ⟨b.arity, b.denote hb⟩ := by
  subst b
  rfl

namespace Language

/-- The semantic family exactly retains the table denotation despite arity transport. -/
theorem member_as_code (L : Language) (i : Fin L.count) :
    (⟨L.arity i.val, L.signature i⟩ : AnySignature AlgebraicComplex) =
      ⟨(L.code i).arity, (L.code i).denote (L.code_valid i)⟩ :=
  sigma_cast_signature (L.arity_index i) _

/-- Every finite indexed semantic table family has a literal exact input.
This is semantic coverage, not an executable algorithm for symbolic complex inputs. -/
theorem coverage_indexed {k : ℕ} (f : Fin k → AnySignature AlgebraicComplex) :
    ∃ L : Language, L.family = Set.range f := by
  classical
  have hc : ∀ i : Fin k, ∃ c : SignatureCode, ∃ h : c.Valid,
      (⟨c.arity, c.denote h⟩ : AnySignature AlgebraicComplex) = f i := by
    intro i
    exact SignatureCode.coverage (f i).2
  choose c hc he using hc
  let raw : RawLanguage := List.ofFn c
  have hv : raw.Valid := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hc i
  let L : Language := ⟨raw, hv⟩
  have hlen : L.count = k := by simp [count, L, raw]
  have hcode (i : Fin L.count) : L.code i = c (Fin.cast hlen i) := by
    change (List.ofFn c).get ⟨i.val, _⟩ = c (Fin.cast hlen i)
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    rfl
  have hmember (i : Fin L.count) :
      (⟨L.arity i.val, L.signature i⟩ : AnySignature AlgebraicComplex) = f (Fin.cast hlen i) := by
    rw [L.member_as_code i]
    exact (signatureCode_denote_congr (hcode i) _ _).trans (he (Fin.cast hlen i))
  refine ⟨L, Set.ext (fun a => ?_)⟩
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast hlen i, (hmember i).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast hlen.symm i, ?_⟩
    simpa using hmember (Fin.cast hlen.symm i)

/-- The literal input language covers every finite algebraic signature set. -/
theorem coverage_family (F : SignatureFamily AlgebraicComplex) (hF : F.Finite) :
    ∃ L : Language, L.family = F := by
  classical
  letI := hF.fintype
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  obtain ⟨L, hL⟩ := coverage_indexed (fun i => (e i).val)
  refine ⟨L, hL.trans ?_⟩
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).property
  · intro hf
    exact ⟨e.symm ⟨f, hf⟩, by simp⟩

end Language
end Paper2.ExactInput
