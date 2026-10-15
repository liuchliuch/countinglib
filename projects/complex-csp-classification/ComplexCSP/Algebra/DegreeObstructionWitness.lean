import ComplexCSP.Recognition.DegreeConditions
import ComplexCSP.Recognition.DegreeConditionsTransport
import ComplexCSP.Algebra.GramGadget
import ComplexCSP.Structure.MaltsevCSPGlobal

/-! # Actual degree-divisible witnesses for the hard implication

Literal failure of degree joint BO selects a positive-arity singleton obstruction.
Its presentation descends to the original coefficient field without changing any
scope or degree. The singleton language is then an ordinary non-BO language.
-/
namespace ComplexCSP.DegreeObstructionWitness
open BlockOrthogonality
variable {D K : Type} [Fintype D] [CommSemiring K] {s : ℕ}

/-- The original degree quantifier supplies an actual bad singleton presentation;
no finite-witness or purification-correctness oracle is an argument. -/
theorem finite_witness (L : Language D ℂ (Fin s)) (δ : ℕ) (h : ¬DegreeJointBO L δ) :
    ∃ T : PositiveTable D, ∃ P : Presentation L (Fin (T.rowArity+1)),
      P.DegreeDivisible δ ∧ P.table=T.value ∧ 0<T.rowArity ∧
        ¬BlockOrthogonal T.singletonRows := by
  classical
  have hs : ¬DegreeSingletonBO L δ := fun hs => h ((degreeJointBO_iff_singletonBO L δ).mpr hs)
  unfold DegreeSingletonBO at hs
  push_neg at hs
  obtain ⟨T,⟨P,hP,hT⟩,hpos,hnot⟩ := hs
  exact ⟨T,P,hP,hT,hpos,hnot⟩

/-- This is precisely the finite gadget needed by Lin's unrestricted-to-degree
substitution: the ordinary non-BO singleton is realized by one actual degree
presentation over the prescribed original field. -/
theorem exists_singleton (M : Language D K (Fin s)) (σ : K →+* ℂ) (δ : ℕ)
    (h : ¬DegreeJointBO (M.mapValues σ) δ) :
    ∃ n : ℕ, 0<n ∧ ∃ P : Presentation M (Fin (n+1)), P.DegreeDivisible δ ∧
      ¬JointBO ((GramGadget.language P.table).mapValues σ) := by
  classical
  obtain ⟨T,Q,hQ,hT,hpos,hnot⟩ := finite_witness (M.mapValues σ) δ h
  let P : Presentation M (Fin (T.rowArity+1)) := ⟨Q.hidden,Q.inst.sourceValues σ⟩
  have hP : P.DegreeDivisible δ :=
    (Instance.degreeDivisible_sourceValues_iff σ Q.inst δ).mpr hQ
  have htable (a : Fin (T.rowArity+1) → D) : σ (P.table a)=T.value a := by
    rw [←hT]
    exact Instance.partition_sourceValues σ Q.inst a
  refine ⟨T.rowArity,hpos,P,hP,?_⟩
  intro hb
  have hg : Instance.Generated ((GramGadget.language P.table).mapValues σ) T.value := by
    have hv := MaltsevWitness.language_value_generated ((GramGadget.language P.table).mapValues σ) 0
    have he : ((GramGadget.language P.table).mapValues σ).value 0=T.value := funext htable
    rwa [he] at hv
  exact hnot ((jointBO_iff_singletonBO _).mp hb T hg hpos)

end ComplexCSP.DegreeObstructionWitness
