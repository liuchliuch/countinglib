import Paper2.Paper1Accepted
import Paper2.Complexity.ControlledCompose
import Paper2.NetworkRealization

/-! Exact-output selector reductions keep root descriptions noncanonical.
A source output convention is constructed from the target convention, rather
than requiring a machine to reproduce an arbitrarily chosen isolating rectangle.
The target's bounded-answer existence is intentionally a separate obligation. -/
namespace Paper2.Problem
open Computability Paper2.Complexity Paper2.ExactInput

/-- A concrete encoded Turing reduction for every valid bounded target convention. -/
def Reduces (w : Wiring) (source target : Language) : Prop :=
  ∀ targetAnswers : BoundedAnswers w target,
    ∃ sourceAnswers : BoundedAnswers w source,
      Nonempty (LengthControlledOracleReduction
        (inputEncoding source) rootEncoding (inputEncoding target) rootEncoding
        sourceAnswers.answer targetAnswers.answer)

/-- Once a genuine target convention exists, a reduction supplies a genuine
source convention; the definition does not manufacture public output bounds. -/
theorem Reduces.sourceAnswers {w : Wiring} {source target : Language}
    (h : Reduces w source target) (ht : Nonempty (BoundedAnswers w target)) :
    Nonempty (BoundedAnswers w source) := by
  obtain ⟨t⟩ := ht
  obtain ⟨s, _⟩ := h t
  exact ⟨s⟩

/-- Actual length-controlled compiled machines establish transitivity. -/
theorem Reduces.trans {w : Wiring} {A B C : Language}
    (hAB : Reduces w A B) (hBC : Reduces w B C) : Reduces w A C := by
  intro c
  obtain ⟨b, ⟨rBC⟩⟩ := hBC c
  obtain ⟨a, ⟨rAB⟩⟩ := hAB b
  exact ⟨a, ⟨rAB.controlledCompose rBC⟩⟩

/-- Hardness transport is a theorem about actual finite machines. The explicit
bounded-target-output witness is still required and is not conjured by reduction. -/
theorem SharpPHard.transport {w : Wiring} {source target : Language}
    (hard : SharpPHard w source) (reduction : Reduces w source target)
    (targetAnswers : Nonempty (BoundedAnswers w target)) : SharpPHard w target := by
  refine ⟨targetAnswers, ?_⟩
  intro targetAnswer f hf
  obtain ⟨sourceAnswer, ⟨r⟩⟩ := reduction targetAnswer
  obtain ⟨counting⟩ := hard.2 sourceAnswer f hf
  exact ⟨counting.controlledCompose r⟩

end Paper2.Problem

namespace Paper2
open Tractable ExactInput

/-- Exact source §2.5 direct-gadget convention, separately visible from the
classification inputs. Every augmented signature is realized by a genuine finite
native-X network with actual resource membership and a recorded nonzero scalar.
This accepts no formal slice, conjugate, sum, arbitrary closure, or Paper 2 reduction. -/
def NativeNetworkRealizesUpTo (F : SignatureFamily AlgebraicComplex)
    {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∃ N : Network AlgebraicComplex n,
    N.Uses F ∧ N.NativeX ∧
    ∃ c : AlgebraicComplex, c ≠ 0 ∧ N.denote = fun x => c * f x

structure Paper1DirectGadgetAccepted where
  directGadget_2_5 : ∀ source augmented : Language,
    source.family ⊆ augmented.family →
    (∀ f ∈ augmented.family, NativeNetworkRealizesUpTo source.family f.2) →
      Problem.Reduces .nativeX augmented source

end Paper2
