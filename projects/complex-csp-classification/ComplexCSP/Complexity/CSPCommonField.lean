import Mathlib.Algebra.Algebra.Hom.Rat
import ComplexCSP.Complexity.CSPFieldTransport
import ComplexCSP.Algebra.FiniteValueField

/-! # Representation-independent fixed-field partition reductions

Two finite rational-basis fields interpreting the same complex constraint table
need not include one another. We construct a finite common subfield of the
complex numbers from both basis images. Both embeddings and all answer-coordinate
maps are actual fixed-field polynomial-time machines.
-/
noncomputable section
open Classical
open scoped BigOperators
namespace ComplexCSP.ComplexityCSPCommonField
open PlanarHom PlanarHom.Complexity
variable {K R : Type} [Field K] [Field R] [Algebra ℚ K] [Algebra ℚ R]
variable {d e : ℕ} (bK : Module.Basis (Fin d) ℚ K) (bR : Module.Basis (Fin e) ℚ R)
variable (σ : K →+* ℂ) (τ : R →+* ℂ)

def values : Fin d ⊕ Fin e → ℂ := Sum.elim (fun i => σ (bK i)) (fun i => τ (bR i))

theorem values_algebraic : ∀ i,IsAlgebraic ℚ (values bK bR σ τ i) := by
  letI : FiniteDimensional ℚ K := Module.Finite.of_basis bK
  letI : FiniteDimensional ℚ R := Module.Finite.of_basis bR
  intro i
  cases i with
  | inl i => exact (IsIntegral.map σ.toRatAlgHom (IsIntegral.of_finite (R:=ℚ) (bK i))).isAlgebraic
  | inr i => exact (IsIntegral.map τ.toRatAlgHom (IsIntegral.of_finite (R:=ℚ) (bR i))).isAlgebraic

def field : IntermediateField ℚ ℂ := FiniteValueField.field (values bK bR σ τ)

theorem finiteDimensional : FiniteDimensional ℚ (field bK bR σ τ) :=
  FiniteValueField.finiteDimensional _ (values_algebraic bK bR σ τ)

def basis : Module.Basis (Fin (Module.finrank ℚ (field bK bR σ τ))) ℚ (field bK bR σ τ) :=
  FiniteValueField.basis _ (values_algebraic bK bR σ τ)

/-- Basis-image membership implies membership of every element. This derives
field inclusion from finite spanning, rather than assuming an image oracle. -/
theorem mem_of_basis {n : ℕ} (b : Module.Basis (Fin n) ℚ K)
    (φ : K →ₐ[ℚ] ℂ) (F : IntermediateField ℚ ℂ)
    (hb : ∀ i,φ (b i) ∈ F) (x : K) : φ x ∈ F := by
  rw [←b.sum_equivFun x,map_sum]
  apply F.sum_mem
  intro i hi
  rw [map_smul,Algebra.smul_def]
  exact F.mul_mem (F.algebraMap_mem _) (hb i)

theorem left_mem (x : K) : σ x ∈ field bK bR σ τ :=
  mem_of_basis bK σ.toRatAlgHom _
    (fun i => FiniteValueField.mem_field (values bK bR σ τ) (Sum.inl i)) x

theorem right_mem (x : R) : τ x ∈ field bK bR σ τ :=
  mem_of_basis bR τ.toRatAlgHom _
    (fun i => FiniteValueField.mem_field (values bK bR σ τ) (Sum.inr i)) x

def left : K →+* field bK bR σ τ where
  toFun x := ⟨σ x,left_mem bK bR σ τ x⟩
  map_zero' := Subtype.ext σ.map_zero
  map_one' := Subtype.ext σ.map_one
  map_add' x y := Subtype.ext (σ.map_add x y)
  map_mul' x y := Subtype.ext (σ.map_mul x y)

def right : R →+* field bK bR σ τ where
  toFun x := ⟨τ x,right_mem bK bR σ τ x⟩
  map_zero' := Subtype.ext τ.map_zero
  map_one' := Subtype.ext τ.map_one
  map_add' x y := Subtype.ext (τ.map_add x y)
  map_mul' x y := Subtype.ext (τ.map_mul x y)

section Language
variable {D : Type} {s : ℕ}

theorem mapValues_injective {A B : Type} [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (hφ : Function.Injective φ) :
    Function.Injective (fun L : Language D A (Fin s) => L.mapValues φ) := by
  rintro ⟨ar,ha,v⟩ ⟨br,hb,w⟩ h
  have hab := congrArg Language.arity h
  change ar=br at hab
  subst br
  have hv : (fun i a => φ (v i a))=(fun i a => φ (w i a)) := by
    exact eq_of_heq (Language.mk.inj h).2
  have hw : v=w := by
    funext i a
    exact hφ (congrFun (congrFun hv i) a)
  subst w
  rfl

theorem mapped_languages (L : Language D K (Fin s)) (M : Language D R (Fin s))
    (h : L.mapValues σ=M.mapValues τ) :
    L.mapValues (left bK bR σ τ)=M.mapValues (right bK bR σ τ) := by
  apply mapValues_injective (field bK bR σ τ).subtype Subtype.val_injective
  exact h

variable [Fintype D] [DecidableEq K] [DecidableEq R]

/-- Same literal complex language, arbitrary prescribed finite rational bases:
one charged query suffices in each of two actual field-transport stages. -/
def reduction (L : Language D K (Fin s)) (M : Language D R (Fin s))
    (h : L.mapValues σ=M.mapValues τ) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem L bK)
      (ComplexityCSPCountReduction.partitionProblem M bR) := by
  let J := field bK bR σ τ
  let bJ := basis bK bR σ τ
  have h₁ := ComplexityCSPFieldTransport.descentReduction L bK bJ
    (left bK bR σ τ).toRatAlgHom
  have h₂ := ComplexityCSPFieldTransport.embeddingReduction M bR bJ
    (right bK bR σ τ).toRatAlgHom
  change PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem L bK)
    (ComplexityCSPCountReduction.partitionProblem (L.mapValues (left bK bR σ τ)) bJ) at h₁
  change PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem (M.mapValues (right bK bR σ τ)) bJ)
    (ComplexityCSPCountReduction.partitionProblem M bR) at h₂
  rw [mapped_languages bK bR σ τ L M h] at h₁
  exact h₁.trans h₂

/-- The converse uses the same theorem with the two realizations exchanged. -/
def reverseReduction (L : Language D K (Fin s)) (M : Language D R (Fin s))
    (h : L.mapValues σ=M.mapValues τ) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem M bR)
      (ComplexityCSPCountReduction.partitionProblem L bK) :=
  reduction bR bK τ σ M L h.symm

end Language
end ComplexCSP.ComplexityCSPCommonField
