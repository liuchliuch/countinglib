import Paper2.DegreeCSP.Model
import Holant.Proofs.Tetrahedral.EvenCSPReduction.Grouping

/-! The original ordered CSP record format with a degree-k promise. Only its
raw payload and proved framing/size facts are reused; the validity predicate
below checks divisibility by k, without imposing an even-degree restriction. -/
namespace Paper2.DegreeCSP
open Holant.Complexity Computability
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Raw := Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw

namespace Raw
abbrev encoding := Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.encoding
abbrev factorEncoding := Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.factorEncoding
abbrev Ports (r : Raw) := Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.Ports r
abbrev address (r : Raw) := Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.address r
abbrev portList (r : Raw) := Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.portList r
abbrev occurrences (r : Raw) := Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.occurrences r
abbrev degree (r : Raw) := Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.degree r

def Valid (s : ℕ) (a : ℕ → ℕ) (k : ℕ) (r : Raw) : Prop :=
  (∀ v : Fin r.factors.length,
    (r.factors.get v).1 < s ∧ (r.factors.get v).2.length = a (r.factors.get v).1) ∧
  (∀ p : Ports r, address r p < r.variables) ∧
  (∀ i < r.variables, k ∣ degree r i)

instance validDecidable (s : ℕ) (a : ℕ → ℕ) (k : ℕ) (r : Raw) :
    Decidable (Valid s a k r) := by
  unfold Valid
  infer_instance

abbrev Input (s : ℕ) (a : ℕ → ℕ) (k : ℕ) := {r : Raw // Valid s a k r}

def validatedEncoding (s : ℕ) (a : ℕ → ℕ) (k : ℕ) : Encoding (Input s a k) Bool where
  encode r := encoding.encode r.val
  decode bits := (encoding.decode bits).bind (fun r =>
    if h : Valid s a k r then some ⟨r,h⟩ else none)
  decode_encode r := by simp [r.property]

variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}

def route (r : Input s a k) (p : Ports r.val) : Fin r.val.variables :=
  ⟨address r.val p,r.property.2.1 p⟩

def label (r : Input s a k) (v : Fin r.val.factors.length) : Fin s :=
  ⟨(r.val.factors.get v).1,(r.property.1 v).1⟩

def portCast (r : Input s a k) (v : Fin r.val.factors.length)
    (j : Fin (a (label r v).val)) : Ports r.val :=
  ⟨v,Fin.cast (r.property.1 v).2.symm j⟩

def fibers (r : Input s a k) : Ports r.val ≃
    Σ i : Fin r.val.variables,{p : Ports r.val // route r p = i} where
  toFun p := ⟨route r p,⟨p,rfl⟩⟩
  invFun q := q.2.val
  left_inv p := rfl
  right_inv := by
    rintro ⟨i,p,hi⟩
    subst i
    rfl

def fiberMembership (r : Input s a k) (i : Fin r.val.variables) :
    {p : Ports r.val // route r p = i} ≃ {p : Ports r.val // p ∈ occurrences r.val i.val} where
  toFun p := ⟨p.val,(r.val.occurrences_mem i.val p.val).mpr (congrArg Fin.val p.property)⟩
  invFun p := ⟨p.val,Fin.ext ((r.val.occurrences_mem i.val p.val).mp p.property)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def fiberOrdinal (r : Input s a k) (i : Fin r.val.variables) :
    {p : Ports r.val // route r p = i} ≃ Fin (degree r.val i.val) :=
  (fiberMembership r i).trans
    (List.Nodup.getEquiv (occurrences r.val i.val) (r.val.occurrences_nodup i.val)).symm

/-- An occurrence's ordinal is its position in the filtered original list. -/
def grouping (r : Input s a k) : Ports r.val ≃
    Σ i : Fin r.val.variables,Fin (degree r.val i.val) :=
  (fibers r).trans (Equiv.sigmaCongrRight (fiberOrdinal r))

theorem grouping_variable (r : Input s a k) (p : Ports r.val) :
    (grouping r p).1 = route r p := rfl

theorem grouping_ordinal (r : Input s a k) (p : Ports r.val) :
    (grouping r p).2.val = (occurrences r.val (address r.val p)).idxOf p := rfl

theorem grouping_inverse (r : Input s a k) (i : Fin r.val.variables)
    (j : Fin (degree r.val i.val)) :
    (grouping r).symm ⟨i,j⟩ = (occurrences r.val i.val).get j := rfl

theorem degree_sum (r : Input s a k) :
    (∑ i : Fin r.val.variables,degree r.val i.val) = Fintype.card (Ports r.val) := by
  have h := Fintype.card_congr (grouping r)
  simpa only [Fintype.card_sigma,Fintype.card_fin] using h.symm

section Value
variable {K : Type} [CommSemiring K]
variable (G : (i : Fin s) → Signature K (a i.val))

def toInstance (r : Input s a k) : Instance K where
  variableCount := r.val.variables
  constraints := r.val.factors.length
  arity c := (r.val.factors.get c).2.length
  table c x := G (label r c) (fun j => x (portCast r c j).2)
  scope c j := route r ⟨c,j⟩

omit [CommSemiring K] in
theorem instance_degree (r : Input s a k) (i : Fin r.val.variables) :
    (toInstance G r).degree i = degree r.val i.val := by
  exact (Fintype.card_congr (fiberOrdinal r i)).trans (Fintype.card_fin _)

omit [CommSemiring K] in
theorem instance_divisible (r : Input s a k) : (toInstance G r).DegreeDivisible k := by
  intro i
  rw [instance_degree]
  exact r.property.2.2 i.val i.isLt

def factorWeight (r : Input s a k) (z : Ports r.val → Bool) : K :=
  ∏ v : Fin r.val.factors.length,G (label r v) (fun j => z (portCast r v j))

def value (r : Input s a k) : K :=
  ∑ x : Fin r.val.variables → Bool,factorWeight G r (fun p => x (route r p))

theorem instance_partition (r : Input s a k) : (toInstance G r).partition = value G r := rfl

omit [CommSemiring K] in
private theorem castSignature_heq {n m : ℕ} (h : n = m) (f : Signature K m) :
    HEq (fun x : Fin n → Bool => f (fun j => x (Fin.cast h.symm j))) f := by
  cases h
  rfl

omit [CommSemiring K] in
theorem instance_uses (r : Input s a k) (F : SignatureFamily K)
    (hG : ∀ i,(⟨a i.val,G i⟩ : AnySignature K) ∈ F) : (toInstance G r).Uses F := by
  intro c
  have hl := (r.property.1 c).2
  have he : (⟨(r.val.factors.get c).2.length,(toInstance G r).table c⟩ : AnySignature K) =
      ⟨a (label r c).val,G (label r c)⟩ := by
    exact Sigma.ext hl (castSignature_heq hl (G (label r c)))
  change (⟨(r.val.factors.get c).2.length,(toInstance G r).table c⟩ : AnySignature K) ∈ F
  rw [he]
  exact hG _

end Value
end Raw
end
end Paper2.DegreeCSP
