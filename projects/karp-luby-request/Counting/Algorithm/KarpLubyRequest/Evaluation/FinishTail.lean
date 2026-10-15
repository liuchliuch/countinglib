import Counting.Algorithm.KarpLubyRequest.Evaluation.Finish

/-! # Actual component transfer, rational output, and complete final cleanup -/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing BinaryCompose
open Counting.Algorithm.KarpLuby

set_option backward.isDefEq.respectTransparency false

/-- Mathlib's dependent input-tape convention has this concrete Boolean bank. -/
theorem median_initial_tapes (xs : List ℕ) :
    (initList Median.Program.computer (Median.input xs)).stk =
      wordTape Median.Program.Stack.input (Median.input xs) := by
  funext k
  cases k <;> rfl

private theorem move_between {K Λ τ : Type} [DecidableEq K]
    (src dst : K) (hne : src ≠ dst) (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (loop next : Λ) (code : ExecutesAt step loop (copyMoveStmt src dst loop next))
    (memory : τ) (bank : K → List Bool) :
    RunsExactly step (cfg loop memory bank)
      (cfg next memory (Function.update (Function.update bank src []) dst
        ((bank src).reverse ++ bank dst))) ((bank src).length + 1) := by
  have h := copy_move_exact src dst dst hne hne step loop next code memory bank
    (bank src) (bank dst) (bank dst)
  simpa only [tapes3, Function.update_idem, Function.update_eq_self] using h

private theorem transfer_between {K Λ τ : Type} [DecidableEq K]
    (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (move restore next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore next))
    (memory : τ) (bank : K → List Bool) (hd : bank dst = []) (ht : bank tmp = []) :
    RunsExactly step (cfg move memory bank)
      (cfg next memory (Function.update (Function.update bank src []) dst (bank src)))
      (2 * (bank src).length + 2) := by
  let middle := Function.update (Function.update bank src []) tmp (bank src).reverse
  have h1 := move_between src tmp hst step move restore hm memory bank
  simp only [ht, List.append_nil] at h1
  have h2 := move_between tmp dst hdt.symm step restore next hr memory middle
  have hfrom : middle tmp = (bank src).reverse := Function.update_self _ _ _
  have hto : middle dst = [] := by
    simp [middle, Function.update_apply, hdt, Ne.symm hsd, hd]
  simp only [hfrom, hto, List.append_nil, List.reverse_reverse, List.length_reverse] at h2
  have hend : Function.update (Function.update middle tmp []) dst (bank src) =
      Function.update (Function.update bank src []) dst (bank src) := by
    clear h1 h2 hm hr
    funext k
    by_cases h0 : k = src <;> by_cases h1 : k = dst <;> by_cases h2 : k = tmp <;>
      simp_all [middle, Function.update_apply]
  rw [hend] at h2
  convert h1.trans h2 using 1 <;> omega

def tailData (r m : List Bool) (a s : ℕ) : Data :=
  { fields := fieldWords r m (encodeNat s) [] [] []
    median := Median.Program.bank [] [] [] [] (encodeNat a) 0 0 }

def numeratorData (r m : List Bool) (a s : ℕ) : Data :=
  { fields := fieldWords r m (encodeNat s) [] [] []
    output := Output.Program.bank (encodeNat a) [] [] [] }

def componentData (r m : List Bool) (a s : ℕ) : Data :=
  { fields := fieldWords r m [] [] [] []
    output := Output.Program.bank (encodeNat a) (encodeNat s) [] [] }

def outputData (r m output : List Bool) : Data :=
  { fields := fieldWords r m [] [] [] []
    output := wordTape Output.Program.computer.k₁ output }

private theorem numerator_bank (r m : List Bool) (a s : ℕ) :
    Function.update (Function.update (tailData r m a s).tapes (medianStacks .chosen) [])
      (outputStacks (Output.Program.ex .num)) (encodeNat a) = (numeratorData r m a s).tapes := by
  rw [update_median, update_output]
  funext k
  rcases k with k | (k | (k | k))
  · rfl
  · rfl
  · cases k <;> rfl
  · cases k with
    | inl k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl
    | inr k => cases k <;> rfl

private theorem denominator_bank (r m : List Bool) (a s : ℕ) :
    Function.update (Function.update (numeratorData r m a s).tapes samples [])
      (outputStacks (Output.Program.ex .den)) (encodeNat s) = (componentData r m a s).tapes := by
  dsimp only [samples]
  rw [update_field, update_output]
  funext k
  rcases k with k | (k | (k | k))
  · rfl
  · fin_cases k <;> rfl
  · rfl
  · cases k with
    | inl k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl
    | inr k => cases k <;> rfl

/-- Both passes are required to preserve little-endian word order while
consuming the median bank's one remaining chosen word. -/
theorem numerator_transfer (memory : Memory) (r m : List Bool) (a s : ℕ) :
    RunsExactly computer.step (configuration .numMove (none, memory) (tailData r m a s))
      (configuration .denMove (none, memory) (numeratorData r m a s))
      (2 * (encodeNat a).length + 2) := by
  have h := transfer_between (medianStacks .chosen) (outputStacks (Output.Program.ex .num)) scratch
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    computer.step .numMove .numRestore .denMove (by intro v t; rfl) (by intro v t; rfl)
    memory (tailData r m a s).tapes rfl rfl
  change RunsExactly computer.step _
    (cfg .denMove memory (Function.update (Function.update (tailData r m a s).tapes
      (medianStacks .chosen) []) (outputStacks (Output.Program.ex .num)) (encodeNat a))) _ at h
  rw [numerator_bank] at h
  exact h

theorem denominator_transfer (memory : Memory) (r m : List Bool) (a s : ℕ) :
    RunsExactly computer.step (configuration .denMove (none, memory) (numeratorData r m a s))
      (configuration .outputStart (none, memory) (componentData r m a s))
      (2 * (encodeNat s).length + 2) := by
  have h := transfer_between samples (outputStacks (Output.Program.ex .den)) scratch
    (by intro h; cases h) (by decide) (by intro h; cases h)
    computer.step .denMove .denRestore .outputStart (by intro v t; rfl) (by intro v t; rfl)
    memory (numeratorData r m a s).tapes rfl rfl
  change RunsExactly computer.step _
    (cfg .outputStart memory (Function.update (Function.update (numeratorData r m a s).tapes
      samples []) (outputStacks (Output.Program.ex .den)) (encodeNat s))) _ at h
  rw [denominator_bank] at h
  exact h

theorem output_start (state : State) (d : Data) :
    computer.step (configuration .outputStart state d) =
      some (configuration (.output (.inl (RationalArithmetic.Normalization.ph .start))) initial d) := rfl

private theorem clear_rows_bank (r m output : List Bool) :
    Function.update (outputData r m output).tapes rows [] = (outputData [] m output).tapes := by
  dsimp only [rows]
  rw [update_field]
  funext k
  rcases k with k | (k | (k | k)) <;> first | rfl | (fin_cases k <;> rfl)

private theorem clear_mass_bank (m output : List Bool) :
    Function.update (outputData [] m output).tapes mass [] = (finalData output).tapes := by
  dsimp only [mass]
  rw [update_field]
  funext k
  rcases k with k | (k | (k | k)) <;> first | rfl | (fin_cases k <;> rfl)

theorem final_step (output : List Bool) :
    computer.step (configuration .done initial (finalData output)) = some (finalConfiguration output) := rfl

theorem final_cleanup (r m output : List Bool) :
    RunsExactly computer.step (configuration .clearRow initial (outputData r m output))
      (finalConfiguration output) (r.length + m.length + 3) := by
  have h1 := clear_exact computer.step rows .clearRow .clearMass (by intro v t; rfl)
    initial.2 (outputData r m output).tapes
  rw [clear_rows_bank] at h1
  change RunsExactly computer.step
    (configuration .clearRow initial (outputData r m output))
    (configuration .clearMass initial (outputData [] m output)) (r.length + 1) at h1
  have h2 := clear_exact computer.step mass .clearMass .done (by intro v t; rfl)
    initial.2 (outputData [] m output).tapes
  rw [clear_mass_bank] at h2
  change RunsExactly computer.step
    (configuration .clearMass initial (outputData [] m output))
    (configuration .done initial (finalData output)) (m.length + 1) at h2
  have h3 := runsExactly_one (final_step output)
  convert (h1.trans h2).trans h3 using 1 <;> omega

def tailTime (r m : List Bool) (a s : ℕ) : ℕ :=
  2 * (encodeNat a).length + 2 * (encodeNat s).length + Output.componentTime a s + r.length + m.length + 8

/-- Actual median-to-output control flow. The starting finite memory may carry
any returned median flags; the installed outputStart resets it before calling
the normalizer. Every non-output stack is empty at the actual final halt. -/
theorem finish_tail (memory : Memory) (r m : List Bool) (a s : ℕ) :
    RunsExactly computer.step (configuration .numMove (none, memory) (tailData r m a s))
      (finalConfiguration (Encoding.encodeOutput ((a : ℚ) / s))) (tailTime r m a s) := by
  have h1 := numerator_transfer memory r m a s
  have h2 := denominator_transfer memory r m a s
  have h3 := runsExactly_one (output_start (none, memory) (componentData r m a s))
  have h4 := output_call (componentData r m a s) (none, initial.2.1, initial.2.2.1) a s
  have h5 := final_cleanup r m (Encoding.encodeOutput ((a : ℚ) / s))
  convert (((h1.trans h2).trans h3).trans h4).trans h5 using 1 <;> dsimp only [tailTime] <;> omega

end Counting.Algorithm.KarpLubyRequest.Evaluation
