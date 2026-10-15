import Counting.Algorithm.KarpLubyRequest.Sampling.SelectorSpec
import Counting.Algorithm.KarpLubyRequest.Sampling.OwnerRun
import Counting.Algorithm.KarpLubyRequest.FairTape

/-!
# The stored-row trial branch agrees with the original estimator

Selection, unranking and prefix ownership retain occurrence order and repeated
rows. The scale is determined by the actual encoded mass word's length. These
value equations do not assert a machine implementation or a running-time bound.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.TrialSpec
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

abbrev selected (rows : List RowSemantics.Cells) (r : ℕ) : SelectorSpec.Result :=
  SelectorSpec.seek rows r []

def accepted (rows : List RowSemantics.Cells) (r : ℕ) : Bool :=
  (selected rows r).selected &&
    Owner.answer (selected rows r).prior
      (RowSemantics.sample (selected rows r).row (selected rows r).rank)

def trialValue (rows : List RowSemantics.Cells) (r : ℕ) : ℕ :=
  if accepted rows r then 2 ^ (Computability.encodeNat (TotalMass.rowSum rows)).length
  else 0

theorem selected_sample_length (n : ℕ) (rows : List RowSemantics.Cells) (r : ℕ)
    (hlen : ∀ row ∈ rows, row.length = n)
    (hs : (selected rows r).selected = true) :
    (RowSemantics.sample (selected rows r).row (selected rows r).rank).length = n := by
  rw [RowSemantics.sample_length]
  exact SelectorSpec.selected_row_length n rows r [] hlen hs

theorem selected_prior_length (n : ℕ) (rows : List RowSemantics.Cells) (r : ℕ)
    (hlen : ∀ row ∈ rows, row.length = n)
    (hs : (selected rows r).selected = true) :
    ∀ row ∈ (selected rows r).prior, row.length = n := by
  obtain ⟨before, hb, hp⟩ := SelectorSpec.selected_decomposition rows r [] hs
  intro row hm
  have hm' : row ∈ before := by
    simpa only [hp, List.append_nil, List.mem_reverse] using hm
  have hm'' : row ∈ before ++ (selected rows r).row :: (selected rows r).remaining :=
    List.mem_append_left _ hm'
  exact hlen row (by simpa only [← hb] using hm'')

theorem selected_sample_original (n : ℕ) (rows : List RowSemantics.Cells) (r : ℕ)
    (hlen : ∀ row ∈ rows, row.length = n)
    (hs : (selected rows r).selected = true) :
    List.ofFn (DNF.sampleNat (DenseNormalization.denote n (selected rows r).row)
      (selected rows r).rank) =
        RowSemantics.sample (selected rows r).row (selected rows r).rank := by
  have hl := SelectorSpec.selected_row_length n rows r [] hlen hs
  subst n
  exact RowSemantics.sample_denote (selected rows r).row (selected rows r).rank

theorem selected_owner_original (n : ℕ) (rows : List RowSemantics.Cells) (r : ℕ)
    (hlen : ∀ row ∈ rows, row.length = n)
    (hs : (selected rows r).selected = true) :
    Owner.answer (selected rows r).prior
        (RowSemantics.sample (selected rows r).row (selected rows r).rank) =
      Program.owner (rows.map (DenseNormalization.denote n)) (selected rows r).prior.length
        (DNF.sampleNat (DenseNormalization.denote n (selected rows r).row)
          (selected rows r).rank) := by
  rw [← selected_sample_original n rows r hlen hs]
  rw [Owner.answer_original n _ (selected_prior_length n rows r hlen hs)]
  exact (SelectorSpec.owner_seek n rows r hs _).symm

/-- Padding rejection and ownership use exactly the original selector's result. -/
theorem accepted_original (n : ℕ) (rows : List RowSemantics.Cells) (r : ℕ)
    (hlen : ∀ row ∈ rows, row.length = n) :
    accepted rows r =
      match Program.select (rows.map (DenseNormalization.denote n)) r with
      | none => false
      | some (i, a) => Program.owner (rows.map (DenseNormalization.denote n)) i a := by
  rw [SelectorSpec.select_seek n rows r [] hlen]
  simp only [List.length_nil, Nat.sub_zero]
  cases hs : (selected rows r).selected with
  | false => simp only [accepted, hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  | true =>
    simp only [accepted, hs, Bool.true_and, ↓reduceIte]
    exact selected_owner_original n rows r hlen hs

theorem scale_original (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) :
    2 ^ (Computability.encodeNat (TotalMass.rowSum rows)).length =
      dyadicSize (Program.totalMass (rows.map (DenseNormalization.denote n))) := by
  have hw : (Computability.encodeNat (TotalMass.rowSum rows)).length =
      Nat.size (TotalMass.rowSum rows) := Encoding.nat_length _
  rw [hw, TotalMass.rowSum_original n rows hlen]
  rfl

/-- The concrete selection/ownership branch is the unchanged original trial. -/
theorem trialValue_original (n : ℕ) (rows : List RowSemantics.Cells) (r : ℕ)
    (hlen : ∀ row ∈ rows, row.length = n) :
    trialValue rows r = Program.trial (rows.map (DenseNormalization.denote n)) r := by
  rw [trialValue, accepted_original n rows r hlen, scale_original n rows hlen]
  unfold Program.trial
  cases Program.select (rows.map (DenseNormalization.denote n)) r <;> rfl

theorem trialValue_of_mass_le (n : ℕ) (rows : List RowSemantics.Cells) (r : ℕ)
    (hlen : ∀ row ∈ rows, row.length = n) (hr : TotalMass.rowSum rows ≤ r) :
    trialValue rows r = 0 := by
  rw [trialValue_original n rows r hlen]
  apply Program.trial_of_mass_le
  simpa only [TotalMass.rowSum_original n rows hlen] using hr

end Counting.Algorithm.KarpLubyRequest.Sampling.TrialSpec
