import Counting.Algorithm.KarpLubyRequest.Preparation.Program

/-! Explicit full physical banks and the literal tagged output convention. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby

/-- A specification of stored words, never a machine register or instruction. -/
structure Data where
  counts : ParameterCountsBank.Stack → List Bool := fun _ => []
  formula : Fin 13 → List Bool := fun _ => []
  mass : Sampling.TotalMass.Stack → List Bool := fun _ => []
  budget : TapeBudget.Bank.Stack → List Bool := fun _ => []
  scratch : List Bool := []
  output : List Bool := []

def Data.tapes (d : Data) : Stack → List Bool :=
  Sum.elim (Sum.elim d.counts (Sum.elim d.formula (Sum.elim d.mass
    (Sum.elim d.budget (fun _ => d.scratch))))) (fun _ => d.output)

def configuration (label : Label) (state : State) (d : Data) : computer.Cfg :=
  ⟨some label, state, d.tapes⟩

def parameterData (old : ParameterProgram.Stack → List Bool) : Data :=
  { counts := Sum.elim old (fun _ => []) }

def inputData (raw : List Bool) : Data :=
  parameterData (wordTape ParameterProgram.computer.k₀ raw)

def finalConfiguration (word : List Bool) : computer.Cfg :=
  ⟨none, initial, ({output := word} : Data).tapes⟩

/-- This literal payload is consumed by the later sampling caller. The tag is
unframed, the four fields are framed, and the random tape is the raw tail. -/
def payload (rows mass samples groups tape : List Bool) : List Bool :=
  true :: (Encoding.frame rows ++ (Encoding.frame mass ++
    (Encoding.frame samples ++ (Encoding.frame groups ++ tape))))

@[simp] theorem tapes_counts (d : Data) (k : ParameterCountsBank.Stack) :
    d.tapes (countsStacks k) = d.counts k := rfl
@[simp] theorem tapes_formula (d : Data) (k : Fin 13) :
    d.tapes (formulaStacks k) = d.formula k := rfl
@[simp] theorem tapes_mass (d : Data) (k : Sampling.TotalMass.Stack) :
    d.tapes (massStacks k) = d.mass k := rfl
@[simp] theorem tapes_budget (d : Data) (k : TapeBudget.Bank.Stack) :
    d.tapes (budgetStacks k) = d.budget k := rfl
@[simp] theorem tapes_scratch (d : Data) : d.tapes scratch = d.scratch := rfl
@[simp] theorem tapes_output (d : Data) : d.tapes output = d.output := rfl

theorem input_eq (raw : List Bool) :
    initList computer raw =
      configuration (.parameter ParameterProgram.computer.main) initial (inputData raw) := by
  dsimp only [initList, configuration]
  congr 1
  funext k
  by_cases hk : k = parameterStacks ParameterProgram.computer.k₀
  · subst k; rfl
  · simp only [hk, dif_neg]
    rcases k with ((j | j) | (j | (j | (j | j)))) | j
    · change [] = wordTape ParameterProgram.computer.k₀ raw j
      apply Eq.symm
      apply wordTape_other
      intro hj
      exact hk (congrArg parameterStacks hj)
    all_goals rfl

theorem halt_eq (word : List Bool) : haltList computer word = finalConfiguration word := by
  dsimp only [haltList, finalConfiguration]
  congr 1
  funext k
  cases k with
  | inl k =>
    have hk : (Sum.inl k : Stack) ≠ output := by intro h; cases h
    simp only [hk, dif_neg]
    rcases k with j | (j | (j | (j | j))) <;> rfl
  | inr k => cases k; rfl

end
end Counting.Algorithm.KarpLubyRequest.Preparation
