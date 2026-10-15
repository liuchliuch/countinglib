import Counting.Model.Basic
import Counting.Upstream.ComplexCSP

/-!
# Bridge from the original ComplexCSP instance semantics

`Counting.Upstream.ComplexCSP` retains the declarations from the pinned original
source, in their original `ComplexCSP` namespace. This module translates those
actual declarations to `Counting.Model` and proves preservation of evaluation
and the complete pinned partition table.

The old language requires positive arities. Translation forgets that proof and
keeps every table, ordered port, repeated scope variable and list occurrence.
The inverse instance translation is relative to an old language; it does not
claim that arbitrary nullary languages can be represented in the old API.
-/

namespace Counting.Bridge.ComplexCSP

variable {D R ι V W B H : Type}

/-- Forget only the old positivity certificate; tables and labels are unchanged. -/
def toLanguage (L : _root_.ComplexCSP.Language D R ι) : Model.Language D R ι where
  arity := L.arity
  value := L.value

/-- A core language can be viewed as an old language when positive arities are
supplied explicitly. In particular this constructor does not eliminate nullaries. -/
def ofLanguage (L : Model.Language D R ι) (hpos : ∀ i, 0 < L.arity i) :
    _root_.ComplexCSP.Language D R ι where
  arity := L.arity
  arity_pos := hpos
  value := L.value

@[simp] theorem toLanguage_ofLanguage (L : Model.Language D R ι)
    (hpos : ∀ i, 0 < L.arity i) : toLanguage (ofLanguage L hpos) = L := rfl

@[simp] theorem ofLanguage_toLanguage (L : _root_.ComplexCSP.Language D R ι) :
    ofLanguage (toLanguage L) L.arity_pos = L := rfl

variable {L : _root_.ComplexCSP.Language D R ι}

/-- Translate one original constraint without changing its ordered scope. -/
def toOccurrence (c : _root_.ComplexCSP.Constraint L V) :
    Model.Occurrence (toLanguage L) V :=
  ⟨c.symbol, c.scope⟩

/-- Recover an original constraint over the translated language. -/
def ofOccurrence (c : Model.Occurrence (toLanguage L) V) :
    _root_.ComplexCSP.Constraint L V :=
  ⟨c.symbol, c.scope⟩

@[simp] theorem ofOccurrence_toOccurrence (c : _root_.ComplexCSP.Constraint L V) :
    ofOccurrence (toOccurrence c) = c := rfl

@[simp] theorem toOccurrence_ofOccurrence (c : Model.Occurrence (toLanguage L) V) :
    toOccurrence (ofOccurrence c) = c := rfl

/-- The bridge is an equivalence of literal occurrences, including repeated ports. -/
def occurrenceEquiv (L : _root_.ComplexCSP.Language D R ι) (V : Type) :
    _root_.ComplexCSP.Constraint L V ≃ Model.Occurrence (toLanguage L) V where
  toFun := toOccurrence
  invFun := ofOccurrence
  left_inv := ofOccurrence_toOccurrence
  right_inv := toOccurrence_ofOccurrence

@[simp] theorem toOccurrence_rename (c : _root_.ComplexCSP.Constraint L V)
    (f : V → W) :
    toOccurrence (c.rename f) = (toOccurrence c).rename f := rfl

/-- The same assignment gives exactly the original constraint value. -/
@[simp] theorem eval_toOccurrence (c : _root_.ComplexCSP.Constraint L V)
    (a : V → D) : (toOccurrence c).eval a = c.eval a := rfl

/-- Translate the complete constraint list without discarding isolated variables. -/
def toOpenInstance (I : _root_.ComplexCSP.Instance L B H) :
    Model.OpenInstance (toLanguage L) B H :=
  ⟨I.constraints.map toOccurrence⟩

/-- The inverse retains the same boundary and hidden-variable types. -/
def ofOpenInstance (I : Model.OpenInstance (toLanguage L) B H) :
    _root_.ComplexCSP.Instance L B H :=
  ⟨I.occurrences.map ofOccurrence⟩

@[simp] theorem ofOpenInstance_toOpenInstance (I : _root_.ComplexCSP.Instance L B H) :
    ofOpenInstance (toOpenInstance I) = I := by
  cases I
  simp [ofOpenInstance, toOpenInstance, List.map_map, Function.comp_def]

@[simp] theorem toOpenInstance_ofOpenInstance
    (I : Model.OpenInstance (toLanguage L) B H) :
    toOpenInstance (ofOpenInstance I) = I := by
  cases I
  simp [ofOpenInstance, toOpenInstance, List.map_map, Function.comp_def]

/-- Literal instances, not just their values, are equivalent over an old language. -/
def instanceEquiv (L : _root_.ComplexCSP.Language D R ι) (B H : Type) :
    _root_.ComplexCSP.Instance L B H ≃ Model.OpenInstance (toLanguage L) B H where
  toFun := toOpenInstance
  invFun := ofOpenInstance
  left_inv := ofOpenInstance_toOpenInstance
  right_inv := toOpenInstance_ofOpenInstance

/-- The number of occurrences, hence every repeated factor, is retained. -/
@[simp] theorem length_toOpenInstance (I : _root_.ComplexCSP.Instance L B H) :
    (toOpenInstance I).occurrences.length = I.constraints.length := by
  simp [toOpenInstance]

/-- Pointwise preservation of the original `ComplexCSP.Instance.eval`. -/
@[simp] theorem eval_toOpenInstance [CommMonoid R]
    (I : _root_.ComplexCSP.Instance L B H) (a : B → D) (b : H → D) :
    (toOpenInstance I).eval a b = I.eval a b := by
  simp only [Model.OpenInstance.eval, toOpenInstance, List.map_map,
    _root_.ComplexCSP.Instance.eval]
  rfl

/-- The new partition table equals the imported original partition table for
all instances and boundary assignments, including empty finite domains. -/
@[simp] theorem partition_toOpenInstance [CommSemiring R] [Fintype D]
    [Fintype H] [DecidableEq H] (I : _root_.ComplexCSP.Instance L B H) (a : B → D) :
    (toOpenInstance I).partition a = I.partition a := by
  simp only [Model.OpenInstance.partition, _root_.ComplexCSP.Instance.partition,
    eval_toOpenInstance]

@[simp] theorem eval_ofOpenInstance [CommMonoid R]
    (I : Model.OpenInstance (toLanguage L) B H) (a : B → D) (b : H → D) :
    (ofOpenInstance I).eval a b = I.eval a b := by
  simpa only [toOpenInstance_ofOpenInstance] using
    (eval_toOpenInstance (ofOpenInstance I) a b).symm

@[simp] theorem partition_ofOpenInstance [CommSemiring R] [Fintype D]
    [Fintype H] [DecidableEq H] (I : Model.OpenInstance (toLanguage L) B H)
    (a : B → D) : (ofOpenInstance I).partition a = I.partition a := by
  simpa only [toOpenInstance_ofOpenInstance] using
    (partition_toOpenInstance (ofOpenInstance I) a).symm

/-- The original generated-family predicate is exactly generation by core
instances over the translated language, with the same canonical hidden types. -/
theorem generated_iff [CommSemiring R] [Fintype D] (G : (B → D) → R) :
    _root_.ComplexCSP.Instance.Generated L G ↔
      ∃ n : Nat, ∃ I : Model.OpenInstance (toLanguage L) B (Fin n),
        ∀ a, I.partition a = G a := by
  constructor
  · rintro ⟨n, I, hI⟩
    exact ⟨n, toOpenInstance I, fun a => (partition_toOpenInstance I a).trans (hI a)⟩
  · rintro ⟨n, I, hI⟩
    exact ⟨n, ofOpenInstance I, fun a => (partition_ofOpenInstance I a).trans (hI a)⟩

end Counting.Bridge.ComplexCSP
