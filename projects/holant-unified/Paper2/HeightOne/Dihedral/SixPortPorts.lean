import Paper2.HeightOne.Dihedral.SixPortIndexing

/-! The complete ordered-port dictionary for the six-port support argument.
The residual four ports are related to the true Remaining subtype by an
explicit equivalence, so every finite-support pencil is an actual xor card in
the same external order. -/
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Cyclic Tractable EndpointSelfLoop PhaseCards SixPortSupport SixPortPencils
local instance {ι : Type} : DecidableEq ι := Classical.decEq ι

def tailPort (i : Fin 4) : Fin 6 := Fin.succ (Fin.succ i)

lemma tailPort_ne_zero (i : Fin 4) : tailPort i ≠ 0 := by simp [tailPort]
lemma tailPort_ne_one (i : Fin 4) : tailPort i ≠ 1 := by
  intro h
  have hh := congrArg Fin.val h
  simp [tailPort] at hh

def tailMap (p : Equiv.Perm (Fin 6)) (i : Fin 4) : Remaining (p 0) (p 1) :=
  ⟨p (tailPort i),
    fun h => tailPort_ne_zero i (p.injective h),
    fun h => tailPort_ne_one i (p.injective h)⟩

lemma tailMap_bijective (p : Equiv.Perm (Fin 6)) : Function.Bijective (tailMap p) := by
  constructor
  · intro i j h
    have hh := p.injective (congrArg Subtype.val h)
    exact Fin.succ_injective _ (Fin.succ_injective _ hh)
  · intro y
    generalize hk : p.symm y.val = k
    have hpk : p k = y.val := by rw [← hk]; exact p.apply_symm_apply _
    fin_cases k
    · exact False.elim (y.property.1 hpk.symm)
    · exact False.elim (y.property.2 hpk.symm)
    · exact ⟨0,Subtype.ext hpk⟩
    · exact ⟨1,Subtype.ext hpk⟩
    · exact ⟨2,Subtype.ext hpk⟩
    · exact ⟨3,Subtype.ext hpk⟩

def tailEquiv (p : Equiv.Perm (Fin 6)) : Fin 4 ≃ Remaining (p 0) (p 1) :=
  Equiv.ofBijective (tailMap p) (tailMap_bijective p)

@[simp] lemma tailEquiv_apply (p : Equiv.Perm (Fin 6)) (i : Fin 4) :
    tailEquiv p i = tailMap p i := rfl

lemma pair_ports_ne (p : Equiv.Perm (Fin 6)) : p 0 ≠ p 1 :=
  fun h => (by decide : (0 : Fin 6) ≠ 1) (p.injective h)

lemma lift_extendBits (p : Equiv.Perm (Fin 6)) (ξ b : Bool) (r : Fin 4 → Bool) :
    lift p ξ b r = extendBits (p 0) (p 1) (pair_ports_ne p)
      (fun k => r ((tailEquiv p).symm k)) b (b ^^ ξ) := by
  classical
  funext k
  obtain ⟨i,rfl⟩ := p.surjective k
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) i
  · simp [lift,extend,extendBits,splitPorts]
  · simp [lift,extend,extendBits,splitPorts,pair_ports_ne p,Ne.symm (pair_ports_ne p)]
  · have hn0 : p (tailPort l) ≠ p 0 := fun h => tailPort_ne_zero l (p.injective h)
    have hn1 : p (tailPort l) ≠ p 1 := fun h => tailPort_ne_one l (p.injective h)
    change lift p ξ b r (p (tailPort l)) = _
    simp only [lift,p.symm_apply_apply,extend,tailPort,Fin.cons_succ]
    simp only [tailPort] at hn0 hn1
    simp only [extendBits,splitPorts,dif_neg hn0,dif_neg hn1,Equiv.coe_fn_mk,Sum.elim_inl]
    change r l = r ((tailEquiv p).symm (tailEquiv p l))
    rw [Equiv.symm_apply_apply]

lemma ordered_pencil_card (f : Signature AlgebraicComplex 6) (p : Equiv.Perm (Fin 6))
    (ξ : Bool) (s : AlgebraicComplex) :
    (fun r => first f p ξ r - s * second f p ξ r) =
      Tensor.reindex (tailEquiv p).symm
        (card (xorKernel false ξ s) (p 0) (p 1) (pair_ports_ne p) f) := by
  funext r
  rw [Tensor.reindex_apply,card_xor_apply]
  unfold first second
  rw [lift_extendBits,lift_extendBits]
  cases ξ <;> rfl

def pairPerm (a b : Fin 6) : Equiv.Perm (Fin 6) :=
  (Equiv.swap 1 (Equiv.swap 0 a b)).trans (Equiv.swap 0 a)

lemma pairPerm_zero (a b : Fin 6) (hab : a ≠ b) : pairPerm a b 0 = a := by
  have hc : Equiv.swap 0 a b ≠ 0 := by
    intro h
    have hh := congrArg (Equiv.swap 0 a) h
    simp only [Equiv.swap_apply_self,Equiv.swap_apply_left] at hh
    exact hab hh.symm
  simp [pairPerm,Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 6) ≠ 1) (Ne.symm hc)]

lemma pairPerm_one (a b : Fin 6) : pairPerm a b 1 = b := by
  simp [pairPerm]

lemma support_reindex_card {K : Type*} [Field K] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : Tensor K ι) :
    (Cyclic.support (Tensor.reindex e f)).card = (Cyclic.support f).card := by
  classical
  have he : Cyclic.support (Tensor.reindex e f) =
      (Cyclic.support f).image (fun x => fun j => x (e.symm j)) := by
    ext y
    simp only [mem_support,Tensor.reindex_apply,Finset.mem_image]
    constructor
    · intro hy
      refine ⟨fun i => y (e i),?_,?_⟩
      · simpa only [Equiv.apply_symm_apply] using hy
      · simp only [Equiv.apply_symm_apply]
    · rintro ⟨x,hx,rfl⟩
      simpa only [Equiv.symm_apply_apply] using hx
  have hi : Function.Injective (fun x : ι → Bool => fun j => x (e.symm j)) := by
    intro x y h
    funext i
    simpa only [Equiv.symm_apply_apply] using congrFun h (e i)
  rw [he,Finset.card_image_of_injective _ hi]

lemma jointSupport_card_comp {K : Type*} [Field K] {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (A B : X → K) :
    (jointSupport (fun y => A (e.symm y)) (fun y => B (e.symm y))).card =
      (jointSupport A B).card := by
  classical
  have he : jointSupport (fun y => A (e.symm y)) (fun y => B (e.symm y)) =
      (jointSupport A B).image e := by
    ext y
    simp only [mem_jointSupport,Finset.mem_image]
    constructor
    · intro hy
      exact ⟨e.symm y,hy,e.apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      simpa only [Equiv.symm_apply_apply] using hx
  rw [he,Finset.card_image_of_injective _ e.injective]

lemma equal_joint_card (f : Signature AlgebraicComplex 6) (p : Equiv.Perm (Fin 6)) :
    (jointSupport (first f p false) (second f p false)).card =
      (jointSupport
        (fun x => f (extendBits (p 0) (p 1) (pair_ports_ne p) x false false))
        (fun x => f (extendBits (p 0) (p 1) (pair_ports_ne p) x true true))).card := by
  have hA : first f p false = fun r =>
      f (extendBits (p 0) (p 1) (pair_ports_ne p) (fun k => r ((tailEquiv p).symm k)) false false) := by
    funext r
    unfold first
    rw [lift_extendBits]
    rfl
  have hB : second f p false = fun r =>
      f (extendBits (p 0) (p 1) (pair_ports_ne p) (fun k => r ((tailEquiv p).symm k)) true true) := by
    funext r
    unfold second
    rw [lift_extendBits]
    rfl
  rw [hA,hB]
  exact jointSupport_card_comp (Equiv.arrowCongr (tailEquiv p).symm (Equiv.refl Bool))
    (fun x => f (extendBits (p 0) (p 1) (pair_ports_ne p) x false false))
    (fun x => f (extendBits (p 0) (p 1) (pair_ports_ne p) x true true))

lemma equal_joint_card_as (f : Signature AlgebraicComplex 6) (p : Equiv.Perm (Fin 6))
    (a b : Fin 6) (hab : a ≠ b) (ha : p 0 = a) (hb : p 1 = b) :
    (jointSupport (first f p false) (second f p false)).card =
      (jointSupport (fun x => f (extendBits a b hab x false false))
        (fun x => f (extendBits a b hab x true true))).card := by
  subst a
  subst b
  exact equal_joint_card f p

lemma first_reindex (f : Signature AlgebraicComplex 6) (p q : Equiv.Perm (Fin 6)) (ξ : Bool) :
    first (Tensor.reindex p.symm f) q ξ = first f (q.trans p) ξ := rfl

lemma second_reindex (f : Signature AlgebraicComplex 6) (p q : Equiv.Perm (Fin 6)) (ξ : Bool) :
    second (Tensor.reindex p.symm f) q ξ = second f (q.trans p) ξ := rfl

end
end Paper2.HeightOne.Dihedral
