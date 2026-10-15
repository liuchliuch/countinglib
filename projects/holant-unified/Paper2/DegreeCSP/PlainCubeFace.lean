import Paper2.DegreeCSP.BadCubeGram

/-! A cube obtained by fixing three actual coordinates has the same parity as
the XOR cube. Changing between the two cube parametrizations only permutes
the eight Boolean inputs. -/
namespace Paper2.DegreeCSP.BadCubeGram

open scoped BigOperators
open OriginalBO
open Holant.Tractable.AffinePhase (Word xor origin basis)

noncomputable section
set_option backward.isDefEq.respectTransparency false

def plainFace {n : ℕ} (P : Word n → ZMod 2) (z : Word n)
    (i j k : Fin n) : Word 3 → ZMod 2 := fun x =>
  P (Function.update (Function.update (Function.update z i (x 0)) j (x 1)) k (x 2))

private def translateCube {n : ℕ} (z : Word n) (i j k : Fin n) : Word 3 ≃ Word 3 where
  toFun x := xor x ![z i,z j,z k]
  invFun x := xor x ![z i,z j,z k]
  left_inv x := Holant.Tractable.AffinePhase.xor_cancel_right x _
  right_inv x := Holant.Tractable.AffinePhase.xor_cancel_right x _

private theorem face_translate {n : ℕ} (P : Word n → ZMod 2) (z : Word n)
    (i j k : Fin n) (hd : BooleanQuadratic.Distinct i j k) (x : Word 3) :
    face P z i j k (translateCube z i j k x) = plainFace P z i j k x := by
  unfold face plainFace
  congr 1
  funext l
  rcases hd with ⟨hij,hjk,hik⟩
  by_cases li : l=i
  · subst l
    cases hzi : z i <;> cases hxi : x 0 <;>
      simp [translateCube,Holant.Tractable.AffinePhase.xor,basis,origin,ite_apply,Function.update,hij,hik,hzi,hxi]
  by_cases lj : l=j
  · subst l
    cases hzj : z j <;> cases hxj : x 1 <;>
      simp [translateCube,Holant.Tractable.AffinePhase.xor,basis,origin,ite_apply,Function.update,li,hjk,hzj,hxj]
  by_cases lk : l=k
  · subst l
    cases hzk : z k <;> cases hxk : x 2 <;>
      simp [translateCube,Holant.Tractable.AffinePhase.xor,basis,origin,ite_apply,Function.update,li,lj,hzk,hxk]
  · simp [Holant.Tractable.AffinePhase.xor,basis,origin,ite_apply,Function.update,li,lj,lk]

theorem plainFace_sum {n : ℕ} (P : Word n → ZMod 2) (z : Word n)
    (i j k : Fin n) (hd : BooleanQuadratic.Distinct i j k) :
    (∑ x, plainFace P z i j k x) = BooleanQuadratic.cubeParity P z i j k := by
  classical
  calc
    (∑ x, plainFace P z i j k x) =
        ∑ x, face P z i j k (translateCube z i j k x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (face_translate P z i j k hd x).symm
    _ = ∑ x, face P z i j k x := (translateCube z i j k).sum_comp _
    _ = _ := face_sum P z i j k

theorem bad_plain_face_not_bo {n : ℕ} (P : Word n → ZMod 2) (z : Word n)
    (i j k : Fin n) (hd : BooleanQuadratic.Distinct i j k)
    (odd : BooleanQuadratic.cubeParity P z i j k=1) :
    ¬BlockOrthogonal (fun (row : Fin 3 → Bool) (a : Bool) =>
      gram (plainFace P z i j k) ![a,row 0,row 1,row 2]) := by
  apply odd_table_not_bo
  rw [plainFace_sum P z i j k hd,odd]

theorem nonquadratic_plain_gram_witness {n : ℕ} (P : Word n → ZMod 2)
    (h : ¬BooleanQuadratic.ThirdCoordinateTrivial P) :
    ∃ z i j k,BooleanQuadratic.Distinct i j k ∧
      ¬BlockOrthogonal (fun (row : Fin 3 → Bool) (a : Bool) =>
        gram (plainFace P z i j k) ![a,row 0,row 1,row 2]) := by
  classical
  unfold BooleanQuadratic.ThirdCoordinateTrivial at h
  push Not at h
  obtain ⟨z,i,j,k,hd,hn⟩ := h
  have odd : BooleanQuadratic.cubeParity P z i j k=1 := by
    generalize hval : BooleanQuadratic.cubeParity P z i j k=a at hn ⊢
    fin_cases a
    · exact (hn rfl).elim
    · rfl
  exact ⟨z,i,j,k,hd,bad_plain_face_not_bo P z i j k hd odd⟩

end
end Paper2.DegreeCSP.BadCubeGram
