import Paper2.Certificates.DihedralSupport.AtlasGeometryCore
import Mathlib.Tactic

/-! An exact projective-pencil lift. Three distinct collinear projective
points assigned to any three distinct field phases determine one affine
pencil up to one common nonzero scalar. The phases need not be specialized to
third roots for the algebraic proof. -/
namespace Paper2.Certificates.DihedralSupport.AtlasPencils
open AtlasGeometry
set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] {I : Type*}

structure Pencil (K I : Type*) where
  A : I → K
  B : I → K

def Pencil.value (P : Pencil K I) (s : K) : I → K := P.A - s • P.B
def Presents (v : Fin 3 → I → K) (s : Fin 3 → K) (P : Pencil K I) : Prop :=
  ∀ j, ∃ c : K, c ≠ 0 ∧ P.value (s j) = c • v j
def Equivalent (P Q : Pencil K I) : Prop :=
  ∃ c : K, c ≠ 0 ∧ Q.A = c • P.A ∧ Q.B = c • P.B
def Nonconstant (P : Pencil K I) : Prop :=
  ∃ a b : I, minor2 P.A P.B a b ≠ 0
def PairIndependent (v : Fin 3 → I → K) : Prop :=
  ∀ i j, i ≠ j → ∃ a b : I, minor2 (v i) (v j) a b ≠ 0

private theorem coefficients_zero {u v : I → K} {a b : I}
    (h : minor2 u v a b ≠ 0) (c d : K) (he : c • u + d • v = 0) :
    c = 0 ∧ d = 0 := by
  have ha := congrFun he a
  have hb := congrFun he b
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at ha hb
  have hc : c * minor2 u v a b = 0 := by
    dsimp [minor2]
    linear_combination v b * ha - v a * hb
  have hd : d * minor2 u v a b = 0 := by
    dsimp [minor2]
    linear_combination u a * hb - u b * ha
  exact ⟨(mul_eq_zero.mp hc).resolve_right h,(mul_eq_zero.mp hd).resolve_right h⟩

private theorem affine_relation (P : Pencil K I) (s : Fin 3 → K) :
    (s 1 - s 2) • P.value (s 0) + (s 2 - s 0) • P.value (s 1) =
      (s 1 - s 0) • P.value (s 2) := by
  funext x
  simp only [Pencil.value,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

private def lift (v : Fin 3 → I → K) (s : Fin 3 → K) (α β : K) : Pencil K I :=
  let c₀ := α * (s 1 - s 0) / (s 1 - s 2)
  let c₁ := β * (s 1 - s 0) / (s 2 - s 0)
  ⟨fun x => (s 1 * (c₀ * v 0 x) - s 0 * (c₁ * v 1 x)) / (s 1 - s 0),
   fun x => (c₀ * v 0 x - c₁ * v 1 x) / (s 1 - s 0)⟩

/-- This construction is valid for the actual values of the three points;
it does not assume pre-normalized representatives or an accepted pencil. -/
theorem exists_unique_pencil (v : Fin 3 → I → K) (s : Fin 3 → K)
    (hv : PairIndependent v) (hs : Function.Injective s)
    (hline : OnLine (v 0) (v 1) (v 2)) :
    ∃ P : Pencil K I, Nonconstant P ∧ Presents v s P ∧
      ∀ Q : Pencil K I, Presents v s Q → Equivalent P Q := by
  obtain ⟨α,β,hv2⟩ := hline
  obtain ⟨a,b,hbasis⟩ := hv 0 1 (by decide)
  have hα : α ≠ 0 := by
    intro hz
    obtain ⟨c,d,hh⟩ := hv 1 2 (by decide)
    apply not_proportional_of_minor2 hh
    exact ⟨β,by simpa [hz] using hv2⟩
  have hβ : β ≠ 0 := by
    intro hz
    obtain ⟨c,d,hh⟩ := hv 0 2 (by decide)
    apply not_proportional_of_minor2 hh
    exact ⟨α,by simpa [hz] using hv2⟩
  have h10 : s 1 - s 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1 : Fin 3) ≠ 0) (hs h))
  have h12 : s 1 - s 2 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (1 : Fin 3) ≠ 2) (hs h))
  have h20 : s 2 - s 0 ≠ 0 := sub_ne_zero.mpr (fun h => (by decide : (2 : Fin 3) ≠ 0) (hs h))
  let c₀ : K := α * (s 1 - s 0) / (s 1 - s 2)
  let c₁ : K := β * (s 1 - s 0) / (s 2 - s 0)
  have hc₀ : c₀ ≠ 0 := div_ne_zero (mul_ne_zero hα h10) h12
  have hc₁ : c₁ ≠ 0 := div_ne_zero (mul_ne_zero hβ h10) h20
  let P := lift v s α β
  have hp0 : P.value (s 0) = c₀ • v 0 := by
    funext x
    dsimp [P,lift,Pencil.value,c₀,c₁]
    field_simp [h10,h12,h20]
    ring
  have hp1 : P.value (s 1) = c₁ • v 1 := by
    funext x
    dsimp [P,lift,Pencil.value,c₀,c₁]
    field_simp [h10,h12,h20]
    ring
  have hp2 : P.value (s 2) = v 2 := by
    rw [←hv2]
    funext x
    dsimp [P,lift,Pencil.value,c₀,c₁]
    field_simp [h10,h12,h20]
    ring
  have hdet : minor2 P.A P.B a b = -(c₀ * c₁ / (s 1 - s 0)) * minor2 (v 0) (v 1) a b := by
    dsimp [P,lift,minor2,c₀,c₁]
    field_simp [h10,h12,h20]
    ring
  refine ⟨P,⟨a,b,?_⟩,?_,?_⟩
  · rw [hdet]
    exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hc₀ hc₁) h10)) hbasis
  · intro j
    fin_cases j
    · exact ⟨c₀,hc₀,hp0⟩
    · exact ⟨c₁,hc₁,hp1⟩
    · exact ⟨1,one_ne_zero,by simpa using hp2⟩
  · intro Q hQ
    obtain ⟨d₀,hd₀,hq0⟩ := hQ 0
    obtain ⟨d₁,hd₁,hq1⟩ := hQ 1
    obtain ⟨d₂,hd₂,hq2⟩ := hQ 2
    have hr := affine_relation Q s
    rw [hq0,hq1,hq2,←hv2] at hr
    have he : ((s 1 - s 2) * d₀ - (s 1 - s 0) * d₂ * α) • v 0 +
        ((s 2 - s 0) * d₁ - (s 1 - s 0) * d₂ * β) • v 1 = 0 := by
      funext x
      have hx := congrFun hr x
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hx
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      linear_combination hx
    obtain ⟨he0,he1⟩ := coefficients_zero hbasis _ _ he
    have hd0 : d₀ = d₂ * c₀ := by
      dsimp [c₀]
      field_simp [h12]
      linear_combination he0
    have hd1 : d₁ = d₂ * c₁ := by
      dsimp [c₁]
      field_simp [h20]
      linear_combination he1
    refine ⟨d₂,hd₂,?_,?_⟩
    · funext x
      have hq0x := congrFun hq0 x
      have hq1x := congrFun hq1 x
      simp only [Pencil.value,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hq0x hq1x
      dsimp [P,lift]
      change Q.A x = d₂ * ((s 1 * (c₀ * v 0 x) - s 0 * (c₁ * v 1 x)) / (s 1 - s 0))
      field_simp [h10]
      rw [hd0] at hq0x
      rw [hd1] at hq1x
      linear_combination s 1 * hq0x - s 0 * hq1x
    · funext x
      have hq0x := congrFun hq0 x
      have hq1x := congrFun hq1 x
      simp only [Pencil.value,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hq0x hq1x
      change Q.B x = d₂ * ((c₀ * v 0 x - c₁ * v 1 x) / (s 1 - s 0))
      field_simp [h10]
      rw [hd0] at hq0x
      rw [hd1] at hq1x
      linear_combination hq0x - hq1x

end Paper2.Certificates.DihedralSupport.AtlasPencils

