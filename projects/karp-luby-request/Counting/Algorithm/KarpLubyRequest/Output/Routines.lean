import Counting.Algorithm.KarpLubyRequest.Output.Program

/-! Exact physical input preparation, source normalization, and output framing. -/
namespace Counting.Algorithm.KarpLubyRequest.Output.Program
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open RationalArithmetic
open Counting.Algorithm.KarpLuby

/-- Only the four named work/output tapes may be nonempty at stage boundaries. -/
def bank (num den temp stream : List Bool) : Stack → List Bool
  | .inr .num => num
  | .inr .den => den
  | .inr .temp => temp
  | .inr .stream => stream
  | _ => []

theorem bank_data (n d t s : List Bool) :
    bank n d t s = (Normalization.Data.mk [] [] [] [] [] [] [] [] [] n d t [] s).tapes := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem tapes_snt (x y z : List Bool) :
    tapes3 (fun _ : Stack => []) (ex .stream) (ex .num) (ex .temp) x y z = bank y [] z x := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem tapes_tnd (x y z : List Bool) :
    tapes3 (fun _ : Stack => []) (ex .temp) (ex .num) (ex .den) x y z = bank y z x [] := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem tapes_stn (x y z : List Bool) :
    tapes3 (fun _ : Stack => []) (ex .stream) (ex .temp) (ex .num) x y z = bank z [] y x := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem tapes_snd (x y z : List Bool) :
    tapes3 (fun _ : Stack => []) (ex .stream) (ex .num) (ex .den) x y z = bank y z [] x := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem tapes_ndt (x y z : List Bool) :
    tapes3 (fun _ : Stack => []) (ex .num) (ex .den) (ex .temp) x y z = bank x y z [] := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

/-- Real framing removal, not a decoding callback. -/
theorem input_frame_run (a s : ℕ) :
    RunsExactly computer.step (cfg (ph .inputScan) initial (bank [] [] [] (input a s)))
      (cfg (ph .denominatorReverse) initial (bank (encodeNat a) [] [] (encodeNat s)))
      (2 * ((encodeNat a).length + 1)) := by
  have h := Frame.extract_exact (ex .stream) (ex .num) (ex .temp)
    (by decide) (by decide) (by decide) computer.step
    (ph .inputScan) (ph .inputRestore) (ph .denominatorReverse) (ph .bad)
    (by intro m t; rfl) (by intro m t; rfl) initial (fun _ => [])
    (encodeNat a) (encodeNat s) []
  rw [input_eq, Contract.frame_eq]
  simpa only [List.append_nil, tapes_snt] using h

/-- Two physical reversals move the canonical denominator into the normalizer. -/
theorem denominator_run (n d : List Bool) :
    RunsExactly computer.step
      (cfg (ph .denominatorReverse) initial (bank n [] [] d))
      (cfg (.inl (Normalization.ph .start)) initial (bank n d [] []))
      (2 * d.length + 2) := by
  have a := copy_move_exact (ex .stream) (ex .num) (ex .temp) (by decide) (by decide)
    computer.step (ph .denominatorReverse) (ph .denominatorRestore)
    (by intro m t; rfl) initial (fun _ => []) d n []
  have b := copy_move_exact (ex .temp) (ex .num) (ex .den) (by decide) (by decide)
    computer.step (ph .denominatorRestore) (.inl (Normalization.ph .start))
    (by intro m t; rfl) initial (fun _ => []) d.reverse n []
  have a' : RunsExactly computer.step
      (cfg (ph .denominatorReverse) initial (bank n [] [] d))
      (cfg (ph .denominatorRestore) initial (bank n [] d.reverse [])) (d.length + 1) := by
    simpa only [List.append_nil, tapes_snt] using a
  have b' : RunsExactly computer.step
      (cfg (ph .denominatorRestore) initial (bank n [] d.reverse []))
      (cfg (.inl (Normalization.ph .start)) initial (bank n d [] [])) (d.length + 1) := by
    simpa only [List.append_nil, List.reverse_reverse, List.length_reverse, tapes_tnd] using b
  convert a'.trans b' using 1 <;> omega

/-- This is the existing source gcd and two quotient calls, with identical steps. -/
theorem normalize_run (a s : ℕ) :
    RunsExactly computer.step
      (cfg (.inl (Normalization.ph .start)) initial (bank (encodeNat a) (encodeNat s) [] []))
      (cfg (ph .componentScan) initial (bank [] [] []
        (Holant.Algebraic.frame (parityWord (numerator a s)).reverse ++
          (encodeNat (denominator a s)).reverse)))
      (Normalization.normalizeTime false a s) := by
  let start := Normalization.active (Normalization.ph .start) (false, false)
    {n := encodeNat a, e := encodeNat s}
  let finish := Normalization.cfg none (false, false)
    {s := Holant.Algebraic.frame (parityWord (numerator a s)).reverse ++
      (encodeNat (denominator a s)).reverse}
  have sourceRun : Normalization.Runs start finish (Normalization.normalizeTime false a s) := by
    have h := Normalization.normalize_exact false a s
    rw [normalized_components] at h
    exact h
  apply MachineCall.run (Function.Embedding.refl Stack) Sum.inl (ph .componentScan)
    normalizerState Normalization.program program (fun _ => rfl)
    none (fun _ => []) start finish _ _ _ _ _ sourceRun
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k
      change (bank (encodeNat a) (encodeNat s) [] []) k = _
      rw [bank_data]
      rfl
    · intro j hj
      exact False.elim (hj j rfl)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k
      change (bank [] [] [] _) k = _
      rw [bank_data]
      rfl
    · intro j hj
      exact False.elim (hj j rfl)

/-- Source-normalizer components have reversed payloads. One frame scan puts
its integer numerator in ordinary little-endian order. -/
theorem component_scan_run (p d : List Bool) :
    RunsExactly computer.step
      (cfg (ph .componentScan) initial
        (bank [] [] [] (Holant.Algebraic.frame p.reverse ++ d.reverse)))
      (cfg (ph .dropTag) initial (bank p [] [] d.reverse)) (p.length + 1) := by
  have h := Frame.scan_exact (ex .stream) (ex .temp) (ex .num)
    (by decide) (by decide) computer.step
    (ph .componentScan) (ph .dropTag) (ph .bad) (by intro m t; rfl)
    initial (fun _ => []) p.reverse d.reverse [] []
  simpa only [List.reverse_reverse, List.length_reverse, List.append_nil, tapes_stn] using h

/-- Zero has an empty canonical integer word; popping it still yields zero. -/
theorem drop_tag_run (n : ℕ) (d : List Bool) :
    RunsExactly computer.step
      (cfg (ph .dropTag) initial (bank (parityWord n) [] [] d))
      (cfg (ph .moveDenominator) initial (bank (encodeNat n) [] [] d)) 1 := by
  apply runsExactly_one
  change TM2.step program _ = _
  change some (⟨some (ph .moveDenominator), (none, initial),
    Function.update (bank (parityWord n) [] [] d) (ex .num) (parityWord n).tail⟩ : computer.Cfg) = _
  rw [parityWord_tail]
  congr 2
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem move_denominator_run (n d : List Bool) :
    RunsExactly computer.step
      (cfg (ph .moveDenominator) initial (bank n [] [] d.reverse))
      (cfg (ph .moveNumerator) initial (bank n d [] [])) (d.length + 1) := by
  have h := copy_move_exact (ex .stream) (ex .num) (ex .den) (by decide) (by decide)
    computer.step (ph .moveDenominator) (ph .moveNumerator)
    (by intro m t; rfl) initial (fun _ => []) d.reverse n []
  simpa only [List.reverse_reverse, List.length_reverse, List.append_nil, tapes_snd] using h

/-- Actual frame emission consumes its source and scratch and keeps the raw
denominator suffix. -/
theorem emit_run (n d : List Bool) :
    RunsExactly computer.step (cfg (ph .moveNumerator) initial (bank n d [] []))
      (cfg (ph .sign) initial (bank [] (Encoding.frame n ++ d) [] []))
      (2 * n.length + 3) := by
  have h := FixedFieldMachines.FrameEmit.prepend_exact (ex .num) (ex .den) (ex .temp)
    (by decide) (by decide) (by decide) computer.step
    (ph .moveNumerator) (ph .delimiter) (ph .emit) (ph .sign)
    (by intro m t; rfl) (by intro m t; rfl) (by intro m t; rfl)
    initial (fun _ => []) n d
  rw [Contract.frame_eq]
  simpa only [tapes_ndt] using h

theorem sign_run (word : List Bool) :
    RunsExactly computer.step (cfg (ph .sign) initial (bank [] word [] []))
      ⟨none, (none, initial), bank [] (signPrefix ++ word) [] []⟩ 1 := by
  apply runsExactly_one
  change TM2.step program _ = _
  simp only [TM2.step, program, TM2.stepAux, cfg,
    Function.update_self, Function.update_idem]
  congr 2
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

/-- Complete literal serializer, including zero, both reversals and the sign
bits. Its time is linear in the actual component-word lengths. -/
theorem serialize_run (n d : ℕ) :
    RunsExactly computer.step
      (cfg (ph .componentScan) initial (bank [] [] []
        (Holant.Algebraic.frame (parityWord n).reverse ++ (encodeNat d).reverse)))
      ⟨none, (none, initial),
        bank [] (signPrefix ++ Encoding.frame (encodeNat n) ++ encodeNat d) [] []⟩
      ((parityWord n).length + (encodeNat d).length + 2 * (encodeNat n).length + 7) := by
  have h := ((((component_scan_run (parityWord n) (encodeNat d)).trans
    (drop_tag_run n (encodeNat d).reverse)).trans
    (move_denominator_run (encodeNat n) (encodeNat d))).trans
    (emit_run (encodeNat n) (encodeNat d))).trans
    (sign_run (Encoding.frame (encodeNat n) ++ encodeNat d))
  simp only [List.append_assoc] at h ⊢
  convert h using 1 <;> omega

end Counting.Algorithm.KarpLubyRequest.Output.Program
