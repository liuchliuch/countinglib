import Counting.Model.Basic

/-!
# Finite occurrence edge cases

These closed examples are proved by kernel reduction. They check that zero and
nullary signatures, repeated factors, repeated scope variables, ordered ports,
isolated hidden variables, and empty domains survive the semantic definitions.
No equality or pinning signatures are added to the example languages.
-/

namespace Counting.Examples

open Model

/-- The unique assignment on an empty boundary. -/
def emptyAssignment (D : Type) : Empty → D := Empty.elim

/-- The empty family is a valid language. -/
def emptyLanguage (D R : Type) : Language D R Empty where
  arity := Empty.elim
  value i := nomatch i

/-- An instance can retain variables even when its language and factor list are empty. -/
def emptyInstance (D R B H : Type) : OpenInstance (emptyLanguage D R) B H := ⟨[]⟩

/-- A nullary factor retains its value independently of the domain. -/
def constantLanguage (D : Type) (r : Nat) : Language D Nat Unit where
  arity _ := 0
  value _ _ := r

def constantOccurrence (D B H : Type) (r : Nat) :
    Occurrence (constantLanguage D r) (B ⊕ H) := ⟨(), Fin.elim0⟩

def constantInstance (D B H : Type) (r : Nat) :
    OpenInstance (constantLanguage D r) B H :=
  ⟨[constantOccurrence D B H r]⟩

theorem empty_no_variables :
    (emptyInstance Bool Nat Empty Empty).partition (emptyAssignment Bool) = 1 := by
  decide

theorem isolated_boolean_variable :
    (emptyInstance Bool Nat Empty Unit).partition (emptyAssignment Bool) = 2 := by
  decide

theorem isolated_boolean_pair :
    (emptyInstance Bool Nat Empty Bool).partition (emptyAssignment Bool) = 4 := by
  decide

theorem nullary_factor :
    (constantInstance Bool Empty Empty 3).partition (emptyAssignment Bool) = 3 := by
  decide

theorem zero_nullary_factor :
    (constantInstance Bool Empty Empty 0).partition (emptyAssignment Bool) = 0 := by
  decide

theorem nullary_with_isolated_variable :
    (constantInstance Bool Empty Unit 3).partition (emptyAssignment Bool) = 6 := by
  decide

theorem repeated_nullary_factors :
    (OpenInstance.mk [constantOccurrence Bool Empty Empty 3,
      constantOccurrence Bool Empty Empty 3]).partition (emptyAssignment Bool) = 9 := by
  decide

theorem empty_domain_no_variables :
    (emptyInstance Empty Nat Empty Empty).partition (emptyAssignment Empty) = 1 := by
  decide

theorem empty_domain_hidden_variable :
    (emptyInstance Empty Nat Empty Unit).partition (emptyAssignment Empty) = 0 := by
  decide

theorem empty_domain_nullary_factor :
    (constantInstance Empty Empty Empty 3).partition (emptyAssignment Empty) = 3 := by
  decide

/-- A unary factor that distinguishes the two domain elements. -/
def unaryLanguage : Language Bool Nat Unit where
  arity _ := 1
  value _ x := if x 0 then 3 else 2

def unaryOccurrence : Occurrence unaryLanguage (Empty ⊕ Unit) :=
  ⟨(), fun _ => Sum.inr ()⟩

theorem single_unary_factor :
    (OpenInstance.mk [unaryOccurrence]).partition (emptyAssignment Bool) = 5 := by
  decide

/-- List multiplicity squares each assignment's factor before summation. -/
theorem repeated_unary_occurrences :
    (OpenInstance.mk [unaryOccurrence, unaryOccurrence]).partition
      (emptyAssignment Bool) = 13 := by
  decide

/-- A zero signature of positive arity is also allowed. -/
def zeroUnaryLanguage : Language Bool Nat Unit where
  arity _ := 1
  value _ _ := 0

theorem zero_unary_factor :
    (OpenInstance.mk [⟨(), fun _ => Sum.inr ()⟩] :
      OpenInstance zeroUnaryLanguage Empty Unit).partition (emptyAssignment Bool) = 0 := by
  decide

/-- The off-diagonal entries distinguish port order. -/
def binaryLanguage : Language Bool Nat Unit where
  arity _ := 2
  value _ x := if x 0 then (if x 1 then 11 else 7) else (if x 1 then 5 else 2)

def repeatedScopeOccurrence : Occurrence binaryLanguage (Empty ⊕ Unit) :=
  ⟨(), fun _ => Sum.inr ()⟩

/-- Reusing one variable at both ports selects only the two diagonal entries. -/
theorem repeated_scope_variable :
    (OpenInstance.mk [repeatedScopeOccurrence]).partition (emptyAssignment Bool) = 13 := by
  decide

def orderedPortsOccurrence : Occurrence binaryLanguage (Bool ⊕ Empty) :=
  ⟨(), fun i => Sum.inl (i.val == 1)⟩

def reversedPortsOccurrence : Occurrence binaryLanguage (Bool ⊕ Empty) :=
  ⟨(), fun i => Sum.inl (i.val == 0)⟩

theorem ordered_ports_forward :
    (OpenInstance.mk [orderedPortsOccurrence]).partition id = 5 := by
  decide

theorem ordered_ports_reversed :
    (OpenInstance.mk [reversedPortsOccurrence]).partition id = 7 := by
  decide

end Counting.Examples
