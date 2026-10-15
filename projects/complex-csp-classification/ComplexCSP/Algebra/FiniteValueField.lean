import ComplexCSP.Algebra.WorkingField
import ComplexCSP.Instances.ValueTransport

/-! # A constructed common coefficient field for finitely many algebraic values -/
noncomputable section
namespace ComplexCSP.FiniteValueField
variable {A : Type} [Fintype A] (w : A → ℂ)

def language : Language A ℂ (Fin 1) :=
  ⟨fun _ => 1,fun _ => Nat.zero_lt_succ 0,fun _ a => w (a 0)⟩

def field : IntermediateField ℚ ℂ := (language w).workingField

omit [Fintype A] in
theorem mem_field (a : A) : w a ∈ field w :=
  (language w).value_mem_workingField 0 (fun _ => a)

theorem finiteDimensional (hw : ∀ a,IsAlgebraic ℚ (w a)) :
    FiniteDimensional ℚ (field w) :=
  (language w).workingField_finiteDimensional (fun _ a => hw (a (0 : Fin 1)))

def basis (hw : ∀ a,IsAlgebraic ℚ (w a)) :
    Module.Basis (Fin (Module.finrank ℚ (field w))) ℚ (field w) := by
  letI := finiteDimensional w hw
  exact Module.finBasis ℚ (field w)

variable {D : Type} {s : ℕ}

def liftLanguage (L : Language D ℂ (Fin s))
    (hL : ∀ i a,L.value i a ∈ field w) : Language D (field w) (Fin s) :=
  ⟨L.arity,L.arity_pos,fun i a => ⟨L.value i a,hL i a⟩⟩

omit [Fintype A] in
@[simp] theorem liftLanguage_map (L : Language D ℂ (Fin s))
    (hL : ∀ i a,L.value i a ∈ field w) :
    (liftLanguage w L hL).mapValues (field w).subtype = L := rfl

/-- The original presentation is reinterpreted in the new common field without
changing a scope or summation variable. Its complex table is proved exactly. -/
def liftPresentation {B : Type} (L : Language D ℂ (Fin s))
    (hL : ∀ i a,L.value i a ∈ field w) (P : Presentation L B) :
    Presentation (liftLanguage w L hL) B :=
  ⟨P.hidden,P.inst.sourceValues (L:=liftLanguage w L hL) (field w).subtype⟩

omit [Fintype A] in
theorem table_liftPresentation [Fintype D] {B : Type} (L : Language D ℂ (Fin s))
    (hL : ∀ i a,L.value i a ∈ field w) (P : Presentation L B) (a : B → D) :
    ((liftPresentation w L hL P).table a : ℂ) = P.table a :=
  Instance.partition_sourceValues (L:=liftLanguage w L hL) (field w).subtype P.inst a

section Input
variable {D E : Type} [Fintype D] [Fintype E] {s : ℕ}
variable (L : Language D ℂ (Fin s)) (extra : E → ℂ)

def inputValues : ((i : Fin s) × (Fin (L.arity i) → D)) ⊕ E → ℂ :=
  Sum.elim (fun p => L.value p.1 p.2) extra

def inputField := field (inputValues L extra)

omit [Fintype D] [Fintype E] in
theorem input_mem (i : Fin s) (a : Fin (L.arity i) → D) :
    L.value i a ∈ inputField L extra := mem_field (inputValues L extra) (Sum.inl ⟨i,a⟩)

omit [Fintype D] [Fintype E] in
theorem extra_mem (e : E) : extra e ∈ inputField L extra :=
  mem_field (inputValues L extra) (Sum.inr e)

theorem inputFinite (hL : ∀ i a,IsAlgebraic ℚ (L.value i a))
    (he : ∀ e,IsAlgebraic ℚ (extra e)) : FiniteDimensional ℚ (inputField L extra) :=
  finiteDimensional (inputValues L extra) (Sum.rec (fun p => hL p.1 p.2) he)

def inputBasis (hL : ∀ i a,IsAlgebraic ℚ (L.value i a))
    (he : ∀ e,IsAlgebraic ℚ (extra e)) :
    Module.Basis (Fin (Module.finrank ℚ (inputField L extra))) ℚ (inputField L extra) :=
  basis (inputValues L extra) (Sum.rec (fun p => hL p.1 p.2) he)

def inputLanguage := liftLanguage (inputValues L extra) L (input_mem L extra)

def inputPresentation {B : Type} (P : Presentation L B) :
    Presentation (inputLanguage L extra) B :=
  liftPresentation (inputValues L extra) L (input_mem L extra) P

theorem table_inputPresentation {B : Type} (P : Presentation L B) (a : B → D) :
    ((inputPresentation L extra P).table a : ℂ)=P.table a :=
  table_liftPresentation (inputValues L extra) L (input_mem L extra) P a

end Input
end ComplexCSP.FiniteValueField
