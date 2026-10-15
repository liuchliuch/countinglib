import ComplexCSP.Complexity.LegalPurification
import ComplexCSP.Recognition.GlobalConditions
import ComplexCSP.Algebra.GramGadget

/-! # The exact singleton purification table used by the global obstruction -/
noncomputable section
open Classical
namespace ComplexCSP.LegalSingletonPurification
open GeneratingSet BlockOrthogonality
variable {D : Type} [Fintype D]

private theorem purify_eq_of_value_eq {X Y A B : Type} {S : Finset ℂˣ}
    (P : LegalGeneratingSet S) (G : X → A → ℂ) (H : Y → B → ℂ)
    (hG : LegalGeneratingSet.ContainsTable S G) (hH : LegalGeneratingSet.ContainsTable S H)
    (x : X) (a : A) (y : Y) (b : B) (he : G x a=H y b) :
    P.purifyTable G hG x a=P.purifyTable H hH y b := by
  by_cases hz : G x a=0
  · rw [P.purifyTable_zero G hG x a hz,P.purifyTable_zero H hH y b (he.symm.trans hz)]
  · have hz' : H y b≠0 := by rw [←he]; exact hz
    rw [P.purifyTable_nonzero G hG x a hz,P.purifyTable_nonzero H hH y b hz']
    apply congrArg (fun g : LegalGeneratingSet.EntryGroup S => (P.purifiedHom g : ℂ))
    apply Subtype.ext
    exact Units.ext he

def choice (T : PositiveTable D) := LegalGeneratingSet.choose T.nonzeroValues

theorem contains_rows (T : PositiveTable D) :
    LegalGeneratingSet.ContainsTable T.nonzeroValues T.rows := by
  intro x z hz
  exact (T.mem_nonzeroValues _).mpr ⟨x,z,rfl⟩

def value (T : PositiveTable D) (a : Fin (T.rowArity+1) → D) : ℂ :=
  (choice T).purifyTable T.rows (contains_rows T) (Fin.init a) (a (Fin.last _))

theorem rows_value (T : PositiveTable D) : RowTypes.tableRows (value T)=T.singletonRows := by
  funext x z
  simp only [RowTypes.tableRows,value,Fin.init_snoc,Fin.snoc_last]
  rfl

theorem algebraic (T : PositiveTable D) : ∀ a,IsAlgebraic ℚ (value T a) :=
  fun a => PurificationProductCompatibility.legal_algebraic (choice T) T.rows (contains_rows T)
    (Fin.init a) (a (Fin.last _))

theorem contains_language (T : PositiveTable D) :
    ComplexityLegalPurification.Contains (GramGadget.language T.value) (S:=T.nonzeroValues) := by
  intro i a hz
  apply (T.mem_nonzeroValues _).mpr
  refine ⟨Fin.init a,a (Fin.last _),?_⟩
  change T.value a = T.value (Fin.snoc (Fin.init a) (a (Fin.last T.rowArity)))
  exact congrArg T.value (Fin.snoc_init_self a).symm

theorem machine_values (T : PositiveTable D) (i : Fin 1) (a : Fin (T.rowArity+1) → D) :
    ComplexityLegalPurification.values (GramGadget.language T.value) (choice T) (contains_language T) i a =
      value T a := by
  apply purify_eq_of_value_eq (choice T)
  simp [ComplexityLegalPurification.rows,GramGadget.language,PositiveTable.rows,RowTypes.tableRows]

/-- This is the exact optional-entry compatibility required by the actual
replacement machine for the source table and literal singleton purification. -/
theorem entries_compatible (T : PositiveTable D) :
    PlanarHom.ProductCompatibility.Compatible (ComplexityCSPCode.entryValue (GramGadget.language T.value))
      (ComplexityCSPReplacement.targetEntry (GramGadget.language T.value) (fun _ => value T)) := by
  have h := ComplexityLegalPurification.entries_compatible (GramGadget.language T.value)
    (choice T) (contains_language T)
  have he : ComplexityLegalPurification.values (GramGadget.language T.value) (choice T)
      (contains_language T) = fun _ => value T := funext (fun i => funext (machine_values T i))
  rw [he] at h
  exact h

theorem zero (T : PositiveTable D) (a : Fin (T.rowArity+1) → D) (hz : T.value a=0) : value T a=0 := by
  rw [←machine_values T 0 a]
  exact ComplexityLegalPurification.values_zero (GramGadget.language T.value)
    (choice T) (contains_language T) 0 a hz

end ComplexCSP.LegalSingletonPurification
