import Counting.Algorithm.KarpLubyRequest.Preparation.Physical

/-! The four-component count result is actually consumed. Both reciprocal
frames are discarded by pop loops; samples and the unframed groups tail are
physically installed in the tape-budget bank with their canonical bit order. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def countTuple (a b samples groups : List Bool) : List Bool :=
  Encoding.frame a ++ (Encoding.frame b ++ (Encoding.frame samples ++ groups))

theorem output_tuple (a b samples groups : ℕ) :
    ParameterCounts.outputEncoding.encode (a, b, samples, groups) =
      countTuple (encodeNat a) (encodeNat b) (encodeNat samples) (encodeNat groups) := by
  change Holant.Algebraic.frame (encodeNat a) ++
    (Holant.Algebraic.frame (encodeNat b) ++
      (Holant.Algebraic.frame (encodeNat samples) ++ encodeNat groups)) = _
  simp only [countTuple, Contract.frame_eq]

def tupleResult (bank : Stack → List Bool) (samples groups : List Bool) : Stack → List Bool :=
  Function.update (Function.update (Function.update bank countOutput [])
    (budgetOriginal 0) samples) (budgetOriginal 1) groups

/-- The complete four-field physical transfer, including clearing both
reciprocals. No numeric value or tuple component is stored in control. -/
theorem tuple_run (memory : Memory) (bank : Stack → List Bool)
    (a b samples groups : List Bool)
    (hword : bank countOutput = countTuple a b samples groups)
    (hs : bank (budgetOriginal 0) = []) (hg : bank (budgetOriginal 1) = [])
    (ht : bank scratch = []) :
    RunsExactly computer.step (cfg (.dropScan 0) memory bank)
      (cfg (.copyMove .mass) memory (tupleResult bank samples groups))
      (2 * (a.length + b.length + samples.length + groups.length) + 8) := by
  let bank1 := Function.update bank countOutput
    (Encoding.frame b ++ (Encoding.frame samples ++ groups))
  let bank2 := Function.update bank countOutput (Encoding.frame samples ++ groups)
  let bank3 := Function.update (Function.update bank countOutput groups)
    (budgetOriginal 0) samples
  have h0 := drop_into 0 memory bank a
    (Encoding.frame b ++ (Encoding.frame samples ++ groups)) hword ht
  have h1 := drop_into 1 memory bank1 b (Encoding.frame samples ++ groups)
    (Function.update_self _ _ _) (by
      change Function.update bank countOutput _ scratch = []
      rw [Function.update_of_ne (by intro h; cases h)]; exact ht)
  have hb1 : Function.update bank1 countOutput (Encoding.frame samples ++ groups) = bank2 := by
    exact Function.update_idem _ _ _
  rw [hb1] at h1
  have h2 := BankProtocol.extract_into countOutput (budgetOriginal 0) scratch
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    computer.step .sampleScan .sampleRestore .groupMove .zero
    (by intro m t; rfl) (by intro m t; rfl) memory bank2 samples groups
    (Function.update_self _ _ _)
    (by change Function.update bank countOutput _ (budgetOriginal 0) = []
        rw [Function.update_of_ne (by intro h; cases h)]; exact hs)
    (by change Function.update bank countOutput _ scratch = []
        rw [Function.update_of_ne (by intro h; cases h)]; exact ht)
  have hb2 : Function.update (Function.update bank2 countOutput groups)
      (budgetOriginal 0) samples = bank3 := by
    dsimp only [bank2, bank3]
    rw [Function.update_idem]
  rw [hb2] at h2
  have h3 := move_into countOutput (budgetOriginal 1) scratch
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    .groupMove .groupRestore (.copyMove .mass)
    (by intro m t; rfl) (by intro m t; rfl) memory bank3
    (by dsimp only [bank3]; rw [Function.update_of_ne (by decide),
          Function.update_of_ne (by intro h; cases h)]; exact hg)
    (by dsimp only [bank3]; rw [Function.update_of_ne (by intro h; cases h),
          Function.update_of_ne (by intro h; cases h)]; exact ht)
  have hb3 : bank3 countOutput = groups := by
    dsimp only [bank3]
    rw [Function.update_of_ne (by intro h; cases h), Function.update_self]
  rw [hb3] at h3
  have hb4 : Function.update (Function.update bank3 countOutput [])
      (budgetOriginal 1) groups = tupleResult bank samples groups := by
    dsimp only [bank3, tupleResult]
    rw [Function.update_comm (show budgetOriginal 0 ≠ countOutput by intro h; cases h),
      Function.update_idem]
  rw [hb4] at h3
  convert ((h0.trans h1).trans h2).trans h3 using 1 <;> omega

end
end Counting.Algorithm.KarpLubyRequest.Preparation
