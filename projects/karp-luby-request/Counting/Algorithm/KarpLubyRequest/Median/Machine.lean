import Counting.Algorithm.KarpLubyRequest.Median.Select
import Holant.Complexity.GraphPreprocessing.Primitive

/-!
# A finite machine for binary natural upper medians

The prepared input is exactly the existing canonical natural-list codec. Its
binary header is physically parsed and cleared; both nested scans, comparison
calls, retained-minimum copies, and final cleanup belong to one actual run.
The bound is a polynomial in the entire serialized bit length, not in the
decoded natural values. This is a median postprocessor, not a whole FPRAS.
-/
namespace Counting.Algorithm.KarpLubyRequest.Median
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby
open Program

def input (xs : List ℕ) : List Bool := (Encoding.list Encoding.nat).encode xs

theorem input_eq (xs : List ℕ) :
    input xs = Encoding.frame (encodeNat xs.length) ++ words xs := rfl

theorem input_length (xs : List ℕ) :
    (input xs).length = 2 * (encodeNat xs.length).length + (words xs).length + 1 := by
  rw [input_eq, List.length_append, Encoding.frame_length]
  omega

theorem count_le_words_length (xs : List ℕ) : xs.length ≤ (words xs).length := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [words_cons, List.length_append, Encoding.frame_length, List.length_cons]
    omega

theorem member_length_le_words (xs : List ℕ) (a : ℕ) (ha : a ∈ xs) :
    (encodeNat a).length ≤ (words xs).length := by
  induction xs with
  | nil => simp at ha
  | cons b bs ih =>
    rw [words_cons, List.length_append, Encoding.frame_length]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have h := ih ha; omega

theorem input_bounds (xs : List ℕ) :
    xs.length ≤ (input xs).length ∧ (words xs).length ≤ (input xs).length ∧
      (encodeNat xs.length).length ≤ (input xs).length ∧
      ∀ a ∈ xs, (encodeNat a).length ≤ (input xs).length := by
  have h := input_length xs
  have hc := count_le_words_length xs
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro a ha
  have hw := member_length_le_words xs a ha
  omega

theorem words_length_le (xs : List ℕ) (W : ℕ)
    (h : ∀ a ∈ xs, (encodeNat a).length ≤ W) :
    (words xs).length ≤ xs.length * (2 * W + 1) := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have hs := ih (fun b hb => h b (by simp [hb]))
    rw [words_cons, List.length_append, Encoding.frame_length, List.length_cons]
    nlinarith

/-- Materializing g numerators of width at most W has this charged input size.
The group count is not an uncharged finite-control parameter. -/
theorem input_ofFn_length_le (g : ℕ) (z : Fin g → ℕ) (W : ℕ)
    (h : ∀ i, (encodeNat (z i)).length ≤ W) :
    (input (List.ofFn z)).length ≤ 2 * (encodeNat g).length + g * (2 * W + 1) + 1 := by
  have hw := words_length_le (List.ofFn z) W (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact h i)
  rw [List.length_ofFn] at hw
  rw [input_length, List.length_ofFn]
  omega

/-- Explicit loose cubic, in the physical input length. -/
def timeBound (N : ℕ) : ℕ := 100 * (N + 1) ^ 3

theorem timeBound_cubic (N : ℕ) :
    timeBound N = 100 * N ^ 3 + 300 * N ^ 2 + 300 * N + 100 := by
  unfold timeBound
  ring

theorem prepared_list (xs : List ℕ) :
    ∃ selected lastFlag time, time ≤ timeBound (input xs).length ∧
      RunsExactly computer.step (initList computer (input xs))
        ⟨none, (none, memory selected lastFlag), bank [] [] [] [] (encodeNat (value xs)) 0 0⟩ time := by
  let N := (input xs).length
  have hb := input_bounds xs
  have h₁ := frame_run .header (memory false false)
    (bank (input xs) [] [] [] [] 0 0) (encodeNat xs.length) (words xs) (input_eq xs) rfl rfl
  have e₁ : Function.update (Function.update (bank (input xs) [] [] [] [] 0 0)
      (frameSrc .header) (words xs)) (frameDst .header) (encodeNat xs.length) =
      Function.update (bank (words xs) [] [] [] [] 0 0) Stack.right (encodeNat xs.length) := by
    funext k; cases k <;> rfl
  rw [e₁] at h₁
  have h₂ := clear_run .header (memory false false)
    (Function.update (bank (words xs) [] [] [] [] 0 0) Stack.right (encodeNat xs.length))
  have e₂ : Function.update
      (Function.update (bank (words xs) [] [] [] [] 0 0) Stack.right (encodeNat xs.length))
      (clearStack .header) [] = bank (words xs) [] [] [] [] 0 0 := by
    funext k; cases k <;> rfl
  rw [e₂] at h₂
  have h₃ := copy_run .save (memory false false) (bank (words xs) [] [] [] [] 0 0) rfl rfl
  have e₃ : Function.update (bank (words xs) [] [] [] [] 0 0) (copyDst .save)
      ((bank (words xs) [] [] [] [] 0 0) (copySrc .save)) =
      bank (words xs) (words xs) [] [] [] 0 0 := by funext k; cases k <;> rfl
  rw [e₃] at h₃
  obtain ⟨lastFlag, h₄⟩ := select_run xs xs none false N hb.2.2.2 hb.2.2.2 (by intro b h; cases h)
  have run := (((Run.exact h₁).trans (Run.exact h₂)).trans (Run.exact h₃)).trans h₄
  have ei : cfg (.scan .header) (memory false false) (bank (input xs) [] [] [] [] 0 0) =
      initList computer (input xs) := by
    congr 1
    funext k; cases k <;> rfl
  rw [ei] at run
  have ht : 2 * ((encodeNat xs.length).length + 1) +
      ((Function.update (bank (words xs) [] [] [] [] 0 0) Stack.right (encodeNat xs.length))
        (clearStack .header)).length + 1 +
      (2 * ((bank (words xs) [] [] [] [] 0 0) (copySrc .save)).length + 2) +
      (xs.length * iterationBound xs N + (words xs).length + 3) ≤ timeBound N := by
    simp only [bank, clearStack, copySrc, Function.update_self]
    have hg : xs.length ≤ N := hb.1
    have hw : (words xs).length ≤ N := hb.2.1
    have hh : (encodeNat xs.length).length ≤ N := hb.2.2.1
    have hi : iterationBound xs N ≤ 5 * N ^ 2 + 22 * N + 29 := by
      unfold iterationBound
      have hp := Nat.mul_le_mul_right (5 * N + 8) hg
      nlinarith
    have hp := Nat.mul_le_mul hg hi
    rw [timeBound_cubic]
    nlinarith [Nat.zero_le (N ^ 3)]
  obtain ⟨time, ht, hr⟩ := run.mono (by simpa only [Nat.add_assoc] using ht)
  exact ⟨(select (eligible xs) xs none).isSome, lastFlag, time, ht, hr⟩

/-- Canonical g/z entry: identical natural result to the frozen R1 selector. -/
theorem prepared_run (g : ℕ) (z : Fin g → ℕ) :
    ∃ selected lastFlag time, time ≤ timeBound (input (List.ofFn z)).length ∧
      RunsExactly computer.step (initList computer (input (List.ofFn z)))
        ⟨none, (none, memory selected lastFlag),
          bank [] [] [] [] (encodeNat (KarpLubyMachine.NumeratorMedian.median g z).value) 0 0⟩ time := by
  simpa only [value_ofFn] using prepared_list (List.ofFn z)

/-- The same execution, measured by the actual primitive-instruction interpreter. -/
theorem primitive_cost (xs : List ℕ) :
    ∃ selected lastFlag time, time ≤ timeBound (input xs).length ∧
      (Primitive.run program time (some (initList computer (input xs)))).2 =
        some (⟨none, (none, memory selected lastFlag),
          bank [] [] [] [] (encodeNat (value xs)) 0 0⟩ : computer.Cfg) ∧
      (Primitive.run program time (some (initList computer (input xs)))).1 ≤
        9 * timeBound (input xs).length := by
  obtain ⟨selected, lastFlag, time, ht, hr⟩ := prepared_list xs
  have hc := Primitive.execution_cost program 9 statement_budget time _ _ hr
  exact ⟨selected, lastFlag, time, ht, hc.1, hc.2.trans (Nat.mul_le_mul_left 9 ht)⟩

/-- The same source instructions may be embedded in a caller bank. The premise
describes only the concrete initial stack/register layout and installed code;
every stack outside the selected bank is retained by the actual execution. -/
theorem caller_run {J R : Type} [DecidableEq J] (e : Stack ↪ J)
    (labels : Label → R) (ret : R)
    (caller : R → TM2.Stmt (fun _ : J => Bool) R State)
    (code : ∀ l, caller (labels l) = Embedded.block e labels ret (program l))
    (xs : List ℕ) (start : TM2.Cfg (fun _ : J => Bool) R State) (frame : J → List Bool)
    (initial : Embedded.Rel e labels ret frame (initList computer (input xs)) start) :
    ∃ ending time, time ≤ timeBound (input xs).length ∧
      (fun p => p.bind (TM2.step caller))^[time] (some start) = some ending ∧
      ending.l = some ret ∧ ending.stk (e .chosen) = encodeNat (value xs) ∧
      (∀ k, k ≠ Stack.chosen → ending.stk (e k) = []) ∧
      (∀ j, (∀ k, j ≠ e k) → ending.stk j = frame j) := by
  obtain ⟨selected, lastFlag, time, ht, hr⟩ := prepared_list xs
  obtain ⟨ending, run, rel⟩ := Embedded.run e labels ret program caller code _ _ start frame time initial hr
  refine ⟨ending, time, ht, run, rel.1, rel.2.2.1 .chosen, ?_, rel.2.2.2⟩
  intro k hk
  have h := rel.2.2.1 k
  cases k <;> first | exact False.elim (hk rfl) | exact h

end Counting.Algorithm.KarpLubyRequest.Median
