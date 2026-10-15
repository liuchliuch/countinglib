import ComplexCSP.Complexity.TypeStackCall
import ComplexCSP.Complexity.TypeRowCallback

/-! # Closed type-search transition with actual reconstruction and row programs

All hypotheses of the generic transition compiler are discharged here. Context
contains only the original instance, computed layers, dimension, witness table
and seed. There is no function-evaluation, relation or equality oracle argument.
-/
namespace ComplexCSP.ComplexityTypeStackConcrete
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexityTypeStackMachines
open WeightedMaltsev MaltsevTypeStack
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d)

abbrev Context (K : Type) := ComplexityTypeRowCallback.Context K × (ℕ × (RawTable × MaybeWord))
noncomputable def contextCode : BitEncoding (Context K) :=
  (ComplexityTypeRowCallback.contextCode basis).prod
    (BitEncoding.unaryNat.prod (tableCode.prod maybeCode))

def dimensionOf (c : Context K) : ℕ := c.2.1

def reconstruct (p : Context K × (ℕ × List ℕ)) : Option (List ℕ) :=
  (reconstructRawTo d m p.1.2.2.1 p.2.2 p.1.2.2.2 p.2.1).head?

def rowLabelOf (p : Context K × List ℕ) : RowLabel K d :=
  ComplexityTypeRowCallback.label L m p.1.1 p.2

def step (p : Context K × State (RowLabel K d)) : Option (State (RowLabel K d)) :=
  contextualStep dimensionOf (List.range d) (reconstruct m) (rowLabelOf L m) p

theorem fp_dimensionOf : FP (contextCode basis) BitEncoding.unaryNat (dimensionOf : Context K → ℕ) :=
  (fp_snd (ComplexityTypeRowCallback.contextCode basis)
    (BitEncoding.unaryNat.prod (tableCode.prod maybeCode))).comp (fp_fst BitEncoding.unaryNat (tableCode.prod maybeCode))

theorem fp_reconstruct :
    FP ((contextCode basis).prod (BitEncoding.unaryNat.prod wordCode)) (optionCode wordCode)
      (reconstruct m : Context K × (ℕ × List ℕ) → Option (List ℕ)) := by
  let ec := contextCode basis
  have hc := fp_fst ec (BitEncoding.unaryNat.prod wordCode)
  have hquery := fp_snd ec (BitEncoding.unaryNat.prod wordCode)
  have hlen := hquery.comp (fp_fst BitEncoding.unaryNat wordCode)
  have hword := hquery.comp (fp_snd BitEncoding.unaryNat wordCode)
  have hmeta := hc.comp (fp_snd (ComplexityTypeRowCallback.contextCode basis)
    (BitEncoding.unaryNat.prod (tableCode.prod maybeCode)))
  have hw := hmeta.comp (fp_snd BitEncoding.unaryNat (tableCode.prod maybeCode))
  have ht := hw.comp (fp_fst tableCode maybeCode)
  have hs := hw.comp (fp_snd tableCode maybeCode)
  have hresult := (hlen.pair (ht.pair (hword.pair hs))).comp (fp_reconstructRawTo d m)
  exact hresult.comp (fp_headOption wordCode [])

theorem fp_rowLabelOf :
    FP ((contextCode basis).prod wordCode) (ComplexityCSPMarginalRowBounds.labelEncoding basis d)
      (rowLabelOf L m) := by
  have hc := (fp_fst (contextCode basis) wordCode).comp
    (fp_fst (ComplexityTypeRowCallback.contextCode basis)
      (BitEncoding.unaryNat.prod (tableCode.prod maybeCode)))
  have hw := fp_snd (contextCode basis) wordCode
  exact (hc.pair hw).comp (ComplexityTypeRowCallback.fp_label L basis m)

/-- Actual FP full control step, with no remaining callback premise. -/
theorem fp_step :
    FP ((contextCode basis).prod (stateCode (ComplexityCSPMarginalRowBounds.labelEncoding basis d)))
      (optionCode (stateCode (ComplexityCSPMarginalRowBounds.labelEncoding basis d)))
      (step L m) :=
  fp_contextualStep (contextCode basis) (ComplexityCSPMarginalRowBounds.labelEncoding basis d)
    dimensionOf (List.range d) (reconstruct m) (rowLabelOf L m)
    (fp_dimensionOf basis) (fp_reconstruct basis m) (fp_rowLabelOf L basis m)

omit [Algebra ℚ K] in
def storedContext {n : ℕ} (base : ComplexityTypeRowCallback.Context K)
    (W : MaltsevWitness.StoredCode d n) : Context K :=
  (base,n,rawTable W,maybeWord W.seed)

/-- Precise reconstruction law used by the independent continuation simulation. -/
theorem reconstruct_stored {n : ℕ} (base : ComplexityTypeRowCallback.Context K)
    (operation : MaltsevRelations.Operation (Fin d)) (W : MaltsevWitness.StoredCode d n)
    (target : MaltsevWitness.Tuple (Fin d) n) (k : ℕ) (hk : k ≤ n) :
    reconstruct (fun a b c => operation (a,b,c)) (storedContext base W,k,word target) =
      (MaltsevWitness.reconstructTo operation W.toCode target k).map word := by
  unfold reconstruct storedContext
  rw [reconstructRawTo_stored operation W target k hk]
  cases h : MaltsevWitness.reconstructTo operation W.toCode target k <;> rfl

end ComplexCSP.ComplexityTypeStackConcrete
