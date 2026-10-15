import ComplexCSP.Complexity.CSPCode
import ComplexCSP.Instances.GadgetSubstitution

/-! # Raw arbitrary-arity fixed-gadget substitution

A fixed list of literal templates is finite program data. Every gate occurrence
gets a fresh consecutive private-variable block; only its boundary ports are
identified. The total compiler also defines behavior on malformed input labels.
-/
namespace ComplexCSP.ComplexityGadgetSubstitution
open ComplexityCSPCode

structure Template where
  boundary : ℕ
  privateCount : ℕ
  constraints : List (ℕ × List ℕ)
  deriving DecidableEq

def Template.code (t : Template) : Code := ⟨t.boundary + t.privateCount, t.constraints⟩
def emptyTemplate : Template := ⟨0,0,[]⟩
abbrev Gate := ℕ × List ℕ

def gateTemplate (ts : List Template) (a : Gate) : Template := ts.getD a.1 emptyTemplate

def remapVertex (t : Template) (offset : ℕ) (ports : List ℕ) (v : ℕ) : ℕ :=
  if v < t.boundary then ports.getD v 0 else offset + (v - t.boundary)

def remapConstraint (t : Template) (offset : ℕ) (ports : List ℕ) (c : Gate) : Gate :=
  (c.1, c.2.map (remapVertex t offset ports))

def attachTemplate (t : Template) (g : Code) (ports : List ℕ) : Code :=
  ⟨g.vertices + t.privateCount,
    g.constraints ++ t.constraints.map (remapConstraint t g.vertices ports)⟩

def compileStep (ts : List Template) (g : Code) (a : Gate) : Code :=
  attachTemplate (gateTemplate ts a) g a.2

/-- Compiled output retains the complete original vertex count, including all
isolated variables, and starts with no base-language constraints. -/
def compile (ts : List Template) (g : Code) : Code :=
  g.constraints.foldl (compileStep ts) ⟨g.vertices,[]⟩

def compileFrom (ts : List Template) (g : Code) (as : List Gate) : Code :=
  as.foldl (compileStep ts) g

theorem remapVertex_lt (t : Template) (offset : ℕ) (ports : List ℕ)
    (hp : ports.length = t.boundary) (hr : ∀ v ∈ ports, v < offset)
    (v : ℕ) (hv : v < t.boundary + t.privateCount) :
    remapVertex t offset ports v < offset + t.privateCount := by
  unfold remapVertex
  split_ifs with h
  · have hi : v < ports.length := by omega
    have hm : ports.getD v 0 ∈ ports := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact (hr _ hm).trans_le (Nat.le_add_right _ _)
  · omega

variable {D K : Type} {s : ℕ} (L : Language D K (Fin s))

theorem attachTemplate_valid (t : Template) (g : Code) (ports : List ℕ)
    (ht : Valid L t.code) (hg : Valid L g)
    (hp : ports.length = t.boundary) (hr : ∀ v ∈ ports, v < g.vertices) :
    Valid L (attachTemplate t g ports) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨hj,ha,hv⟩ := hg c hc
    exact ⟨hj,ha,fun v hm => (hv v hm).trans_le (Nat.le_add_right _ _)⟩
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
    obtain ⟨hj,hlen,hv⟩ := ht a ha
    refine ⟨hj, ?_, ?_⟩
    · simpa only [remapConstraint, List.length_map] using hlen
    · intro v hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact remapVertex_lt t g.vertices ports hp hr w (hv w hw)

theorem gateTemplate_mem {ts : List Template} {a : Gate} (h : a.1 < ts.length) :
    gateTemplate ts a ∈ ts := by
  rw [gateTemplate,List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

def Gate.Valid (ts : List Template) (shared : ℕ) (a : Gate) : Prop :=
  a.1 < ts.length ∧ a.2.length = (gateTemplate ts a).boundary ∧ ∀ v ∈ a.2, v < shared

theorem compileFrom_valid (ts : List Template) (shared : ℕ)
    (ht : ∀ t ∈ ts, Valid L t.code) (g : Code) (as : List Gate)
    (hg : Valid L g) (hs : shared ≤ g.vertices)
    (ha : ∀ a ∈ as, a.Valid ts shared) : Valid L (compileFrom ts g as) := by
  induction as generalizing g with
  | nil => exact hg
  | cons a as ih =>
    have hv := ha a (by simp)
    exact ih (compileStep ts g a)
      (attachTemplate_valid L _ _ _ (ht _ (gateTemplate_mem hv.1)) hg hv.2.1
        (fun v hm => (hv.2.2 v hm).trans_le hs))
      (hs.trans (Nat.le_add_right _ _)) (fun b hb => ha b (by simp [hb]))

omit L in
@[simp] theorem compileFrom_vertices (ts : List Template) (g : Code) (as : List Gate) :
    (compileFrom ts g as).vertices =
      g.vertices + (as.map (fun a => (gateTemplate ts a).privateCount)).sum := by
  induction as generalizing g with
  | nil => simp [compileFrom]
  | cons a as ih =>
    change (compileFrom ts (compileStep ts g a) as).vertices = _
    rw [ih]
    simp [compileStep,attachTemplate,Nat.add_assoc]

omit L in
@[simp] theorem compileFrom_constraints_length (ts : List Template) (g : Code) (as : List Gate) :
    (compileFrom ts g as).constraints.length = g.constraints.length +
      (as.map (fun a => (gateTemplate ts a).constraints.length)).sum := by
  induction as generalizing g with
  | nil => simp [compileFrom]
  | cons a as ih =>
    change (compileFrom ts (compileStep ts g a) as).constraints.length = _
    rw [ih]
    simp [compileStep,attachTemplate,Nat.add_assoc]

end ComplexCSP.ComplexityGadgetSubstitution
