import Paper2.BellReduction.RawCharge
import Paper2.BellReduction.ValueSurgery

/-! The source high-charge family implies the raw supported-row hypothesis
used by the arbitrary-incidence Bell eliminator. -/
namespace Paper2.BellReduction.RawCharge
open Complexity ExactInput Tractable RawNative

 theorem signature_charge {K : Type} [Zero K] {n : ℕ} (f : Signature K n)
    (he : Even n) (hf : Tensor.HalfChargeDivisible f 4)
    (xs : List Bool) (hlen : xs.length = n)
    (hn : f (fun i => xs.get (Fin.cast hlen.symm i)) ≠ 0) :
    (8 : ℤ) ∣ listCharge xs := by
  let x : Fin n → Bool := fun i => xs.get (Fin.cast hlen.symm i)
  have hx : List.ofFn x = xs := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp [x]
  rw [← hx,listCharge_ofFn]
  have hd := hf x hn
  obtain ⟨k,hk⟩ := hd
  have ht := twice_halfCharge (by simpa using he) x
  refine ⟨k,?_⟩
  omega

/-- Only non-designated rows need the ambient high-charge property. The
introduced Bell may have different supported charge and is left unrestricted. -/
theorem language_charge (L : Language)
    (hF : ∀ i : Fin L.count, i.val ≠ 0 →
      Even (L.arity i.val) ∧ Tensor.HalfChargeDivisible (L.signature i) 4)
    (label : ℕ) (hlabel : label ≠ 0) (xs : List Bool)
    (hn : languageTable L label xs ≠ 0) : (8 : ℤ) ∣ listCharge xs := by
  unfold languageTable at hn
  split at hn
  next hi =>
    split at hn
    next hlen =>
      exact signature_charge (L.signature ⟨label,hi⟩) (hF ⟨label,hi⟩ hlabel).1
        (hF ⟨label,hi⟩ hlabel).2 xs hlen hn
    next hlen => exact (hn rfl).elim
  next hi => exact (hn rfl).elim

/-- The actual tagged extension inherits this premise from its original
language, including duplicate original labels and nullary vertices. -/
theorem tagged_language_charge (L : Language) {n : ℕ} (g : Signature AlgebraicComplex n)
    (hF : HighCharge L.family) (label : ℕ) (hlabel : label ≠ 0) (xs : List Bool)
    (hn : languageTable (RelativeEO.tagged L g) label xs ≠ 0) :
    (8 : ℤ) ∣ listCharge xs := by
  apply language_charge (RelativeEO.tagged L g) ?_ label hlabel xs hn
  intro i hi
  obtain ⟨j,hj⟩ : ∃ j : Fin L.count, i = j.succ := by
    have hk : i.val - 1 < L.count := by
      have hh := i.isLt
      change i.val < L.count + 1 at hh
      omega
    refine ⟨⟨i.val-1,hk⟩,?_⟩
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  subst i
  have hh := hF _ (show (⟨L.arity j.val,L.signature j⟩ : AnySignature AlgebraicComplex) ∈ L.family
    from ⟨j,rfl⟩)
  have he := RelativeEO.tagged_succ L g j
  have hc : (RelativeEO.tagged L g).signature j.succ = L.signature j := by
    exact eq_of_heq ((Sigma.mk.inj he).2)
  change Even (L.arity j.val) ∧ _
  rw [hc]
  exact hh

end Paper2.BellReduction.RawCharge
