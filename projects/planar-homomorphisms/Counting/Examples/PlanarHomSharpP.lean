import Counting.Bridge.PlanarHomSharpP

/-! Distinct accepting choices and canonical post-halt padding are essential
for parsimonious compilation, even when successor configurations coincide. -/
namespace Counting.Examples.PlanarHomSharpP

open PlanarHom.NondeterministicComputationTree PlanarHom.Complexity

/-- Both labelled choices reach the same accepting state. -/
def mergedView : Bool → NodeView Bool
  | false => .binary true true
  | true => .accept

theorem merged_choices_count : acceptingCount mergedView 1 false = 2 := rfl

theorem merged_false_certificate : replay mergedView false [false, false, false] = true := rfl
theorem merged_true_certificate : replay mergedView false [true, false, false] = true := rfl
theorem rejects_free_padding : replay mergedView false [true, false, true] = false := rfl

theorem merged_bounded : Bounded mergedView false 1 :=
  .binary rfl (.accept rfl) (.accept rfl)

theorem larger_clock_preserves_count (n : ℕ) : acceptingCount mergedView (n + 1) false = 2 := by
  simpa [merged_choices_count] using merged_bounded.acceptingCount_eq_of_le (show 1 ≤ n + 1 by omega)

/-- A concrete polynomial witness length used by the actual generator compiler. -/
noncomputable def lengthPolynomial : Polynomial ℕ := Polynomial.X + 1

noncomputable def allCertificatesMachine : PolynomialNondeterministicMachine :=
  PlanarHom.CertificateNondeterministicCompiler.compile lengthPolynomial (fun _ => true)
    (fp_const (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool true)

/-- The compiled finite machine has exponentially many paths, all individually
bounded in polynomial time, with no free padding multiplicity. -/
theorem allCertificatesMachine_count (x : Bits) :
    allCertificatesMachine.count x = 2 ^ (x.length + 1) := by
  rw [allCertificatesMachine, PlanarHom.CertificateNondeterministicCompiler.count_eq_certificateCount]
  classical
  unfold certificateCount
  calc
    _ = Fintype.card (Fin (lengthPolynomial.eval x.length) → Bool) :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => rfl))
    _ = _ := by simp [lengthPolynomial]

theorem powers_of_two_acceptingPaths : SharpP (fun x : Bits => 2 ^ (x.length + 1)) :=
  ⟨allCertificatesMachine, fun x => (allCertificatesMachine_count x).symm⟩

theorem powers_of_two_certificates : CertificateSharpP (fun x : Bits => 2 ^ (x.length + 1)) :=
  powers_of_two_acceptingPaths.certificateSharpP

end Counting.Examples.PlanarHomSharpP
