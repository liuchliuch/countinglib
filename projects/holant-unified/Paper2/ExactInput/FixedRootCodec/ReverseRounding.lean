import Paper2.ExactInput.FixedRootCodec.ReverseRational
import Paper2.ExactInput.FixedRootCodec.Signs
import Holant.Complexity.BinaryArithmetic.EncodedDivision
import Holant.Complexity.RationalArithmetic.Inverse
import Mathlib.Data.Rat.Floor

/-! Exact lattice rounding by actual binary long division. A positive rational
is rounded using its canonical numerator and denominator; a finite sign test
handles negative inputs. Every cast, division, and sign branch has a concrete
polynomial-time Boolean-stack program. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev naturalQuotientMachine : Machine where
  K := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).K
  decidableK := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).kDecidableEq
  finiteK := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).kFin
  input := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).k₀
  output := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).k₁
  Label := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).Λ
  finiteLabel := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).ΛFin
  main := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).main
  State := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).σ
  finiteState := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).σFin
  initial := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).initialState
  program := (Holant.Complexity.BinaryArithmetic.EncodedDivision.computer false).m

def naturalQuotientReversedComputes :
    Computes (pairEncoding (reverseEncoding encodingNatBool) (reverseEncoding encodingNatBool)) encodingNatBool
      (fun p : ℕ × ℕ => p.1/p.2) where
  machine := naturalQuotientMachine
  time := 3*Polynomial.X^2+10*Polynomial.X+7
  outputs p := by
    have h := Holant.Complexity.BinaryArithmetic.EncodedDivision.divisionPolyTime.outputsFun p
    change Turing.TM2OutputsInTime naturalQuotientMachine.computer
      (List.map id (Holant.Complexity.BinaryArithmetic.EncodedDivision.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1/p.2)))) _ at h
    simpa only [List.map_id,Holant.Complexity.BinaryArithmetic.EncodedDivision.inputEncoding,
      Holant.Complexity.BinaryArithmetic.EncodedAddition.inputEncoding,
      pairEncoding,reverseEncoding,encodingNatBool,TractableAlgorithms.Paper1Machine.frame_eq,
      Holant.Complexity.BinaryArithmetic.EncodedDivision.divisionPolyTime,
      Holant.Complexity.BinaryArithmetic.EncodedDivision.quotientRemainderPolyTime] using h

def naturalQuotientComputes :
    Computes (pairEncoding encodingNatBool encodingNatBool) encodingNatBool
      (fun p : ℕ × ℕ => p.1/p.2) :=
  congrComputes ((RationalArithmetic.reversePairComputes encodingNatBool encodingNatBool).andThen
    naturalQuotientReversedComputes) (fun _ => rfl)

def roundNaturalCastComputes : Computes encodingNatBool rationalEncoding (fun n : ℕ => (n : ℚ)) :=
  congrComputes ((pairComputes RationalArithmetic.natCastComputes
    (constantComputes encodingNatBool encodingNatBool 1)).andThen
      RationalArithmetic.normalizationForwardComputes) (fun n => by simp [Rat.mkRat_eq_div])

def positiveFloor (q : ℚ) : ℕ := q.num.toNat/q.den

def positiveFloorComputes : Computes rationalEncoding encodingNatBool positiveFloor :=
  (pairComputes (RationalArithmetic.numeratorComputes.andThen integerToNatComputes)
    RationalArithmetic.denominatorComputes).andThen naturalQuotientComputes

theorem positiveFloor_eq_floor (q : ℚ) (h : 0≤q) : (positiveFloor q : ℤ)=⌊q⌋ := by
  rw [Rat.floor_def']
  have hn : 0≤q.num := Rat.num_nonneg.mpr h
  unfold positiveFloor
  rw [Int.natCast_ediv,Int.toNat_of_nonneg hn]

def signedNearest (q : ℚ) : ℚ :=
  if q<0 then -(positiveFloor (-q+1/2) : ℚ) else (positiveFloor (q+1/2) : ℚ)

def signedNearestComputes : Computes rationalEncoding rationalEncoding signedNearest := by
  let q := identityComputes rationalEncoding
  let neg := rationalProvider.mulComputes (constantComputes rationalEncoding rationalEncoding (-1)) q
  let positive := (rationalProvider.addComputes q
    (constantComputes rationalEncoding rationalEncoding (1/2))).andThen
      (positiveFloorComputes.andThen roundNaturalCastComputes)
  let negative := (rationalProvider.addComputes neg
    (constantComputes rationalEncoding rationalEncoding (1/2))).andThen
      (positiveFloorComputes.andThen roundNaturalCastComputes)
  exact congrComputes (ifComputes rationalNegativeComputes
    (rationalProvider.mulComputes (constantComputes rationalEncoding rationalEncoding (-1)) negative)
    positive) (fun q => by simp [signedNearest])

/-- Strict half-unit accuracy recovers every signed integer exactly. Ties are
irrelevant to this theorem and therefore need no prescribed convention. -/
theorem signedNearest_correct (q : ℚ) (a : ℤ) (h : |q-(a : ℚ)|<1/2) :
    signedNearest q=(a : ℚ) := by
  obtain ⟨hl,hu⟩ := abs_lt.mp h
  unfold signedNearest
  by_cases hq : q<0
  · rw [if_pos hq]
    have hn : 0≤-q+1/2 := by linarith
    have hf : ⌊-q+1/2⌋=(-a) := Int.floor_eq_iff.mpr (by push_cast; constructor <;> linarith)
    have hp := (positiveFloor_eq_floor (-q+1/2) hn).trans hf
    have hc : (positiveFloor (-q+1/2) : ℚ)=(-a : ℤ) := by exact_mod_cast hp
    rw [hc]
    simp
  · rw [if_neg hq]
    have hn : 0≤q+1/2 := by linarith
    have hf : ⌊q+1/2⌋=a := Int.floor_eq_iff.mpr (by constructor <;> linarith)
    have hp := (positiveFloor_eq_floor (q+1/2) hn).trans hf
    exact_mod_cast hp

def latticeRound (d : ℕ) (q : ℚ) : ℚ := signedNearest ((d : ℚ)*q)/(d : ℚ)

def latticeRoundComputes :
    Computes (pairEncoding encodingNatBool rationalEncoding) rationalEncoding
      (fun p : ℕ × ℚ => latticeRound p.1 p.2) := by
  let den := (Wiring.firstComputes encodingNatBool rationalEncoding).andThen roundNaturalCastComputes
  let q := Wiring.secondComputes encodingNatBool rationalEncoding
  let rounded := (rationalProvider.mulComputes den q).andThen signedNearestComputes
  let reciprocal := recode (TractableAlgorithms.Paper1Machine.computes
    Holant.Complexity.RationalArithmetic.inverseComputes) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (rationalProvider.mulComputes rounded (den.andThen reciprocal))
    (fun p => by simp [latticeRound,div_eq_mul_inv])

theorem latticeRound_correct (d : ℕ) (q : ℚ) (a : ℤ) (_hd : 0<d)
    (h : |(d : ℚ)*q-(a : ℚ)|<1/2) : latticeRound d q=(a : ℚ)/(d : ℚ) := by
  unfold latticeRound
  rw [signedNearest_correct _ a h]

end
end Paper2.ExactInput.FixedRootCodec
