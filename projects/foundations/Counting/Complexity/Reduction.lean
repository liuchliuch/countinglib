import Counting.Computation.PolyTime

/-!
# Parsimonious counting reductions over explicit encodings

A reduction contains an actual finite TM2 polynomial-time computer for its instance
map, together with pointwise preservation of the natural-number answer. Composition
uses the proved machine compiler in `Counting.Computation.PolyTime`; no abstract
closure assumption or unfinished mathlib composition declaration is used here.

The consequences proved below are transitivity, class-relative hardness transport,
and downward transport of FP algorithms. Closure of `#P` under these reductions
requires a separate verifier construction, including unique witness padding, and is
not asserted in this module.
-/

namespace Counting.Complexity

open Computability
open Counting.Computation

variable {α β γ δ Γα Γβ Γγ Γδ Γn : Type}
variable [Fintype Γα] [Fintype Γβ] [Fintype Γγ] [Fintype Γδ] [Fintype Γn]

/-- A count-preserving instance transformation, implemented by a concrete finite
machine whose transition count is polynomial in the explicitly encoded input. -/
structure ParsimoniousReduction (ea : Encoding α Γα) (eb : Encoding β Γβ)
    (f : α → ℕ) (g : β → ℕ) where
  map : α → β
  machine : PolyTime ea eb map
  correct : ∀ a, f a = g (map a)

namespace ParsimoniousReduction

variable {ea : Encoding α Γα} {eb : Encoding β Γβ} {ec : Encoding γ Γγ}
variable {ed : Encoding δ Γδ} {en : Encoding ℕ Γn}
variable {f f' : α → ℕ} {g g' : β → ℕ} {h : γ → ℕ} {k : δ → ℕ}

/-- Reflexivity uses the actual one-transition identity machine. -/
noncomputable def refl (ea : Encoding α Γα) (f : α → ℕ) :
    ParsimoniousReduction ea ea f f where
  map := id
  machine := PolyTime.identity ea
  correct _ := rfl

/-- Compose instance maps by compiling their finite machines and compose the
count-preservation equations in the same direction. -/
noncomputable def trans (r : ParsimoniousReduction ea eb f g)
    (s : ParsimoniousReduction eb ec g h) : ParsimoniousReduction ea ec f h where
  map := s.map ∘ r.map
  machine := PolyTime.comp r.machine s.machine
  correct a := (r.correct a).trans (s.correct (r.map a))

/-- The composed cost charges the second machine at the derived bound on the
first map's encoded output length. -/
@[simp] theorem trans_time (r : ParsimoniousReduction ea eb f g)
    (s : ParsimoniousReduction eb ec g h) :
    (r.trans s).machine.time =
      s.machine.time.comp (PolyTime.outputLengthPolynomial r.machine) + r.machine.time := rfl

/-- The compiled reduction executes the original machines' two concrete runs. -/
@[simp] theorem trans_steps (r : ParsimoniousReduction ea eb f g)
    (s : ParsimoniousReduction eb ec g h) (a : α) :
    ((r.trans s).machine.outputsFun a).steps =
      (s.machine.outputsFun (r.map a)).steps + (r.machine.outputsFun a).steps := rfl

/-- Every reduction has a proved polynomial bound on the size of its output
instance, rather than merely an assumed output-size condition. -/
theorem map_encoded_length_le (r : ParsimoniousReduction ea eb f g) (a : α) :
    (eb.encode (r.map a)).length ≤
      (PolyTime.outputLengthPolynomial r.machine).eval (ea.encode a).length :=
  PolyTime.encoded_output_length_le r.machine a

@[simp] theorem refl_map (ea : Encoding α Γα) (f : α → ℕ) (a : α) :
    (refl ea f).map a = a := rfl

@[simp] theorem trans_map (r : ParsimoniousReduction ea eb f g)
    (s : ParsimoniousReduction eb ec g h) (a : α) :
    (r.trans s).map a = s.map (r.map a) := rfl

/-- The semantic maps of the two compiled associations agree. This makes no claim
that differently associated compiler outputs have identical syntax. -/
theorem trans_assoc_map (r : ParsimoniousReduction ea eb f g)
    (s : ParsimoniousReduction eb ec g h) (t : ParsimoniousReduction ec ed h k) :
    ((r.trans s).trans t).map = (r.trans (s.trans t)).map := rfl

/-- Change the presentation of the two counting functions using proved pointwise
equalities; the instance map and its real machine stay the same. -/
def congr (r : ParsimoniousReduction ea eb f g)
    (hf : ∀ a, f' a = f a) (hg : ∀ b, g b = g' b) :
    ParsimoniousReduction ea eb f' g' where
  map := r.map
  machine := r.machine
  correct a := (hf a).trans ((r.correct a).trans (hg (r.map a)))

/-- Equal functions reduce by the concrete identity machine. -/
noncomputable def ofEq (ea : Encoding α Γα) {f g : α → ℕ}
    (h : ∀ a, f a = g a) : ParsimoniousReduction ea ea f g :=
  (refl ea f).congr (fun _ => rfl) h

/-- A target FP computer yields a source FP computer by actual TM2 composition.
The natural-number output encoding is explicit and is preserved by the transport. -/
noncomputable def computer (r : ParsimoniousReduction ea eb f g)
    (m : PolyTime eb en g) : PolyTime ea en f := by
  have hcomp : g ∘ r.map = f := funext fun a => (r.correct a).symm
  exact hcomp ▸ PolyTime.comp r.machine m

/-- Downward closure of FP under the implemented parsimonious reduction. -/
theorem inFP (r : ParsimoniousReduction ea eb f g)
    (hg : InFP eb en g) : InFP ea en f := by
  obtain ⟨m⟩ := hg
  exact ⟨r.computer m⟩

end ParsimoniousReduction

/-- Proposition-valued reducibility; witnesses retain the map, finite machine,
polynomial bound and all correctness proofs. -/
def ParsimoniousReduces (ea : Encoding α Γα) (eb : Encoding β Γβ)
    (f : α → ℕ) (g : β → ℕ) : Prop :=
  Nonempty (ParsimoniousReduction ea eb f g)

namespace ParsimoniousReduces

variable {ea : Encoding α Γα} {eb : Encoding β Γβ} {ec : Encoding γ Γγ}
variable {en : Encoding ℕ Γn} {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}

theorem refl (ea : Encoding α Γα) (f : α → ℕ) :
    ParsimoniousReduces ea ea f f := ⟨ParsimoniousReduction.refl ea f⟩

theorem trans (r : ParsimoniousReduces ea eb f g)
    (s : ParsimoniousReduces eb ec g h) : ParsimoniousReduces ea ec f h := by
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  exact ⟨r.trans s⟩

theorem inFP (r : ParsimoniousReduces ea eb f g)
    (hg : InFP eb en g) : InFP ea en f := by
  obtain ⟨r⟩ := r
  exact r.inFP hg

end ParsimoniousReduces

/-- Hardness for a specified class of natural-valued functions with fixed source
encoding. Instantiating the class by `#P` needs no change to the reduction itself. -/
def HardFor (ea : Encoding α Γα) (eb : Encoding β Γβ)
    (C : (α → ℕ) → Prop) (g : β → ℕ) : Prop :=
  ∀ f, C f → ParsimoniousReduces ea eb f g

namespace HardFor

variable {ea : Encoding α Γα} {eb : Encoding β Γβ} {ec : Encoding γ Γγ}
variable {en : Encoding ℕ Γn} {C : (α → ℕ) → Prop} {g : β → ℕ} {h : γ → ℕ}

/-- Hardness propagates forward along an implemented parsimonious reduction. -/
theorem transport (hg : HardFor ea eb C g) (r : ParsimoniousReduces eb ec g h) :
    HardFor ea ec C h := by
  intro f hf
  exact (hg f hf).trans r

/-- The machine-valued form does not discard a supplied reduction witness. -/
theorem transportReduction (hg : HardFor ea eb C g)
    (r : ParsimoniousReduction eb ec g h) : HardFor ea ec C h :=
  hg.transport ⟨r⟩

/-- An FP algorithm for a hard target supplies FP algorithms for every member of
the specified class. This is a conditional transport, not a complexity separation. -/
theorem all_inFP (hg : HardFor ea eb C g) (hfp : InFP eb en g) :
    ∀ f, C f → InFP ea en f := by
  intro f hf
  exact (hg f hf).inFP hfp

end HardFor

/-- Mutual parsimonious reducibility, retaining each encoding as a parameter. -/
def ParsimoniousEquivalent (ea : Encoding α Γα) (eb : Encoding β Γβ)
    (f : α → ℕ) (g : β → ℕ) : Prop :=
  ParsimoniousReduces ea eb f g ∧ ParsimoniousReduces eb ea g f

namespace ParsimoniousEquivalent

variable {ea : Encoding α Γα} {eb : Encoding β Γβ} {ec : Encoding γ Γγ}
variable {en : Encoding ℕ Γn} {f : α → ℕ} {g : β → ℕ} {h : γ → ℕ}

theorem refl (ea : Encoding α Γα) (f : α → ℕ) :
    ParsimoniousEquivalent ea ea f f :=
  ⟨ParsimoniousReduces.refl ea f, ParsimoniousReduces.refl ea f⟩

theorem symm (r : ParsimoniousEquivalent ea eb f g) :
    ParsimoniousEquivalent eb ea g f := ⟨r.2, r.1⟩

theorem trans (r : ParsimoniousEquivalent ea eb f g)
    (s : ParsimoniousEquivalent eb ec g h) : ParsimoniousEquivalent ea ec f h :=
  ⟨r.1.trans s.1, s.2.trans r.2⟩

/-- Equivalent counting problems have equivalent FP membership for the same
explicit encoding of their natural-number answers. -/
theorem inFP_iff (r : ParsimoniousEquivalent ea eb f g) :
    InFP ea en f ↔ InFP eb en g :=
  ⟨r.2.inFP, r.1.inFP⟩

end ParsimoniousEquivalent

end Counting.Complexity
