import Paper2.ExactInput.Encoding
import Paper2.Tractable.Criteria

/-! Literal finite algebraic tables, with a fixed executable dense table order.
Validity is a proof about monic irreducible isolated roots. Only byte syntax and
finite table indexing are executable here; there is no classical validity decider. -/
namespace Paper2.ExactInput
open Computability Paper2.Complexity Paper2.Tractable

/-- Least-significant port first, an explicit bijection, including the nullary table. -/
def wordIndex (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

structure SignatureCode where
  arity : ℕ
  entries : List RootCode
  deriving DecidableEq

namespace SignatureCode

def encoding : Encoding SignatureCode Bool where
  encode c := (framedProductEncoding encodingNatBool (framedListEncoding rootEncoding)).encode
    (c.arity, c.entries)
  decode bits := ((framedProductEncoding encodingNatBool (framedListEncoding rootEncoding)).decode bits).map
    (fun p => ⟨p.1, p.2⟩)
  decode_encode c := by simp

/-- Every table cell is a valid minimal root descriptor, without hidden missing cells. -/
def Valid (c : SignatureCode) : Prop :=
  c.entries.length = 2 ^ c.arity ∧ ∀ i : Fin c.entries.length, (c.entries.get i).Valid

def entry (c : SignatureCode) (h : c.Valid) (x : Fin c.arity → Bool) : RootCode :=
  c.entries.get (Fin.cast h.1.symm (wordIndex c.arity x))

theorem entry_valid (c : SignatureCode) (h : c.Valid) (x : Fin c.arity → Bool) :
    (c.entry h x).Valid := h.2 _

noncomputable def denote (c : SignatureCode) (h : c.Valid) : Signature AlgebraicComplex c.arity :=
  fun x => (c.entry h x).value (c.entry_valid h x)

theorem denote_spec (c : SignatureCode) (h : c.Valid) (x : Fin c.arity → Bool) :
    (c.entry h x).MinimalRepresents (c.denote h x : ℂ) := RootCode.value_spec _ _

/-- Code coverage is mathematical existence, and is not a claimed root-isolation algorithm. -/
theorem coverage {n : ℕ} (f : Signature AlgebraicComplex n) :
    ∃ c : SignatureCode, ∃ h : c.Valid, (⟨c.arity, c.denote h⟩ : AnySignature AlgebraicComplex) = ⟨n, f⟩ := by
  classical
  choose codes hc using (fun x : Fin n → Bool => RootCode.minimal_coverage (f x))
  let entries := List.ofFn (fun i : Fin (2 ^ n) => codes ((wordIndex n).symm i))
  let c : SignatureCode := ⟨n, entries⟩
  have hlen : entries.length = 2 ^ n := by simp [entries]
  have hv : c.Valid := by
    refine ⟨hlen, ?_⟩
    intro i
    have hi : (entries.get i) = codes ((wordIndex n).symm (Fin.cast hlen i)) := by
      simp [entries]
      rfl
    rw [show c.entries.get i = entries.get i from rfl, hi]
    exact ⟨_, hc _⟩
  refine ⟨c, hv, ?_⟩
  have he : c.denote hv = f := by
    funext x
    apply RootCode.value_eq
    have hi : c.entry hv x = codes x := by
      simp [entry, c, entries]
    rw [hi]
    exact hc x
  exact congrArg (Sigma.mk n) he

end SignatureCode

abbrev RawLanguage := List SignatureCode

def rawLanguageEncoding : Encoding RawLanguage Bool := framedListEncoding SignatureCode.encoding

def RawLanguage.Valid (L : RawLanguage) : Prop := ∀ c ∈ L, c.Valid

abbrev Language := { L : RawLanguage // L.Valid }

namespace Language

def count (L : Language) : ℕ := L.val.length

/-- Total arity table is computationally read from the literal input syntax. -/
def arity (L : Language) (i : ℕ) : ℕ := ((L.val[i]?).map SignatureCode.arity).getD 0

def code (L : Language) (i : Fin L.count) : SignatureCode := L.val.get i

theorem code_valid (L : Language) (i : Fin L.count) : (L.code i).Valid :=
  L.property _ (List.get_mem _ _)

@[simp] theorem arity_index (L : Language) (i : Fin L.count) : L.arity i.val = (L.code i).arity := by
  have hi : i.val < L.val.length := i.isLt
  simp [arity, code, List.getElem?_eq_getElem hi]
  rfl

noncomputable def signature (L : Language) (i : Fin L.count) : Signature AlgebraicComplex (L.arity i.val) :=
  fun x => (L.code i).denote (L.code_valid i) (fun j => x (Fin.cast (L.arity_index i).symm j))

noncomputable def family (L : Language) : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin L.count => (⟨L.arity i.val, L.signature i⟩ : AnySignature AlgebraicComplex))

theorem family_finite (L : Language) : L.family.Finite := Set.finite_range _

/-- The recognition machine reads exactly the raw descriptor list, including all
arity/table data. Semantic validity proofs add no bits and supply no algorithm. -/
def bits (L : Language) : List Bool := rawLanguageEncoding.encode L.val

theorem bits_injective : Function.Injective bits := by
  intro L M h
  exact Subtype.ext (rawLanguageEncoding.encode_injective h)

end Language
end Paper2.ExactInput
