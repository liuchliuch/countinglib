import Paper2.DegreeCSP.CodeSevenAffineObstruction
import Paper2.DegreeCSP.PartialContextProducts

/-! A finite family of actual partial contexts selects one common cyclic
phase. The concrete presentations retain their source labels and hidden
degrees. Multiplying a balanced cycle by the genuine seven-character mask
gives an actual generated pure cubic table, whose affinity forces its parameter
to be one. No context or mask construction is postulated by this lemma. -/
namespace Paper2.DegreeCSP.CubicContextCharacter
open scoped BigOperators
open Tractable GeneratedCodeSeven CodeSevenAffineObstruction
noncomputable section
set_option backward.isDefEq.respectTransparency false

def sign (j : Fin 7) : ℤ := if j.val<3 ∨ j=6 then 1 else -1

structure Packet (F : SignatureFamily AlgebraicComplex) (k : ℕ) where
  presentation : Presentation AlgebraicComplex (Fin 7)
  charge : ℕ
  scalar : AlgebraicComplex
  parameter : AlgebraicComplex
  scalar_nonzero : scalar≠0
  parameter_nonzero : parameter≠0
  uses : presentation.Uses F
  hidden : PartialUnaryProducts.HiddenDivisible presentation k
  boundary : ∀j : Fin 7,(presentation.degree (.inl j) : ZMod k)=
    (charge : ZMod k)*(sign j : ZMod k)
  on_code : ∀x,presentation.value (code x)=scalar*cubic parameter x

variable {F : SignatureFamily AlgebraicComplex} {k s : ℕ}

theorem boundary_divisible (P : Fin s→Packet F k) (q : Fin s→ℕ)
    (balance : k∣∑i,q i*(P i).charge) (j : Fin 7) :
    k∣∑i,q i*(P i).presentation.degree (.inl j) := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simp only [Nat.cast_sum,Nat.cast_mul,Packet.boundary]
  have h : (∑i,(q i : ZMod k)*((P i).charge : ZMod k))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_mul] using
      (ZMod.natCast_eq_zero_iff _ _).mpr balance
  calc
    _ = (∑i,(q i : ZMod k)*((P i).charge : ZMod k))*(sign j : ZMod k) := by
      simp only [Finset.sum_mul,mul_assoc]
    _ = 0 := by rw [h,zero_mul]

theorem masked_product (P : Fin s→Packet F k) (q : Fin s→ℕ)
    (maskScalar : AlgebraicComplex) :
    (fun y=>maskScalar*indicator y*∏i,(P i).presentation.value y^(q i))=
      payload (maskScalar*∏i,(P i).scalar^(q i))
        (∏i,(P i).parameter^(q i)) := by
  classical
  funext y
  by_cases hy:Valid y
  · have he : y=code (decode y) := (valid_iff_code y).mp hy
    rw [he]
    rw [payload_code,indicator_code,mul_one]
    simp only [Packet.on_code,mul_pow,Finset.prod_mul_distrib,cubic]
    let e := bitValue ℕ (decode y 0)*bitValue ℕ (decode y 1)*bitValue ℕ (decode y 2)
    have hp : (∏i,((P i).parameter^e)^(q i))=
        (∏i,(P i).parameter^(q i))^e := by
      calc
        _ = ∏i,((P i).parameter^(q i))^e := by
          apply Finset.prod_congr rfl
          intro i _
          rw [←pow_mul,←pow_mul,Nat.mul_comm]
        _ = _ := Finset.prod_pow _ _ _
    rw [hp]
    exact (mul_assoc _ _ _).symm
  · simp only [indicator,hy,ite_false,mul_zero,zero_mul,payload]

/-- The mask is an actual generated table with its nonzero scalar retained. -/
theorem generated_cycle (P : Fin s→Packet F k) (q : Fin s→ℕ)
    (balance : k∣∑i,q i*(P i).charge) (maskScalar : AlgebraicComplex)
    (mask : Generated F k (fun y=>maskScalar*indicator y)) :
    Generated F k (payload (maskScalar*∏i,(P i).scalar^(q i))
      (∏i,(P i).parameter^(q i))) := by
  have hp := PartialContextProducts.generated (fun i=>(P i).presentation) q
    (fun i=>(P i).uses) (fun i=>(P i).hidden)
    (boundary_divisible P q balance)
  have hg := generated_hadamard mask hp
  rw [masked_product P q maskScalar] at hg
  exact hg

theorem cycle_relations (P : Fin s→Packet F k)
    (maskScalar : AlgebraicComplex) (hm : maskScalar≠0)
    (mask : Generated F k (fun y=>maskScalar*indicator y))
    (affine : ∀{n}(f : Signature AlgebraicComplex n),Generated F k f→Affine f) :
    CyclicPhaseCharacterGenerators.CycleRelations (fun i=>(P i).charge)
      (fun i=>(P i).parameter) k := by
  classical
  intro q balance
  apply affine_parameter (maskScalar*∏i,(P i).scalar^(q i))
    (∏i,(P i).parameter^(q i))
  · apply mul_ne_zero hm
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (P i).scalar_nonzero)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (P i).parameter_nonzero)
  · exact affine _ (generated_cycle P q balance maskScalar mask)

/-- All provided concrete unary, mixed and cubic context packets share the
same character, including an empty finite family of packets. -/
theorem exists_phase (hk : 0<k) (P : Fin s→Packet F k)
    (maskScalar : AlgebraicComplex) (hm : maskScalar≠0)
    (mask : Generated F k (fun y=>maskScalar*indicator y))
    (affine : ∀{n}(f : Signature AlgebraicComplex n),Generated F k f→Affine f) :
    ∃theta : AlgebraicComplex,theta^k=1 ∧
      ∀i,(P i).parameter=theta^((P i).charge) :=
  CyclicPhaseCharacterGenerators.exists_phase_of_cycles hk
    (fun i=>(P i).charge) (fun i=>(P i).parameter)
    (cycle_relations P maskScalar hm mask affine)

end
end Paper2.DegreeCSP.CubicContextCharacter
