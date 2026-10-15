import Paper2.Certificates.DihedralSupport.Semantics
import Paper2.HeightOne.Dihedral.SixPortSupport
import Mathlib.Tactic

/-! The fifteen unordered port pairs suffice for every ordered six-port
permutation. The residual four ports are in the certificate's literal sorted
order. Reversing the selected pair changes the chosen first bit precisely in
the xor-one sector. -/
namespace Paper2.Certificates.DihedralSupport.SixPortCanonicalPairs
open Paper2.HeightOne.Dihedral
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def canonicalPort (q : Fin 15) : Fin 6 → Fin 6 :=
  ![(pairPorts q).1,(pairPorts q).2,residualPorts q 0,residualPorts q 1,
    residualPorts q 2,residualPorts q 3]

def canonicalPosition (q : Fin 15) (i : Fin 6) : Fin 6 :=
  if i = (pairPorts q).1 then 0 else if i = (pairPorts q).2 then 1
  else if i = residualPorts q 0 then 2 else if i = residualPorts q 1 then 3
  else if i = residualPorts q 2 then 4 else 5

theorem canonical_left : ∀ q i, canonicalPosition q (canonicalPort q i) = i := by
  decide +kernel
theorem canonical_right : ∀ q i, canonicalPort q (canonicalPosition q i) = i := by
  decide +kernel

def canonical (q : Fin 15) : Equiv.Perm (Fin 6) where
  toFun := canonicalPort q
  invFun := canonicalPosition q
  left_inv := canonical_left q
  right_inv := canonical_right q

@[simp] theorem canonical_zero (q : Fin 15) : canonical q 0 = (pairPorts q).1 := rfl
@[simp] theorem canonical_one (q : Fin 15) : canonical q 1 = (pairPorts q).2 := rfl
@[simp] theorem canonical_tail (q : Fin 15) (k : Fin 4) :
    canonical q k.succ.succ = residualPorts q k := by fin_cases k <;> rfl

theorem residual_injective : ∀ q, Function.Injective (residualPorts q) := by
  decide +kernel
theorem residual_ne_first : ∀ q k, residualPorts q k ≠ (pairPorts q).1 := by
  decide +kernel
theorem residual_ne_second : ∀ q k, residualPorts q k ≠ (pairPorts q).2 := by
  decide +kernel

@[simp] theorem lift_zero (p : Equiv.Perm (Fin 6)) (ξ b : Bool) (r : Fin 4 → Bool) :
    SixPortSupport.lift p ξ b r (p 0) = b := by simp [SixPortSupport.lift,SixPortSupport.extend]
@[simp] theorem lift_one (p : Equiv.Perm (Fin 6)) (ξ b : Bool) (r : Fin 4 → Bool) :
    SixPortSupport.lift p ξ b r (p 1) = (b ^^ ξ) := by
  simp [SixPortSupport.lift,SixPortSupport.extend]
@[simp] theorem lift_tail (p : Equiv.Perm (Fin 6)) (ξ b : Bool) (r : Fin 4 → Bool)
    (k : Fin 4) : SixPortSupport.lift p ξ b r (p k.succ.succ) = r k := by
  simp [SixPortSupport.lift,SixPortSupport.extend]

private theorem residual_reindex (p : Equiv.Perm (Fin 6)) (q : Fin 15)
    (hheads : ((pairPorts q).1 = p 0 ∧ (pairPorts q).2 = p 1) ∨
      ((pairPorts q).1 = p 1 ∧ (pairPorts q).2 = p 0)) :
    ∃ e : Equiv.Perm (Fin 4), ∀ k, residualPorts q k = p (e k).succ.succ := by
  classical
  have hb : ∀ k : Fin 4, 2 ≤ (p.symm (residualPorts q k)).val := by
    intro k
    have h0 : p.symm (residualPorts q k) ≠ 0 := by
      intro he
      have hh : residualPorts q k = p 0 := by simpa using congrArg p he
      rcases hheads with ⟨ha,_⟩ | ⟨_,ha⟩
      · exact residual_ne_first q k (hh.trans ha.symm)
      · exact residual_ne_second q k (hh.trans ha.symm)
    have h1 : p.symm (residualPorts q k) ≠ 1 := by
      intro he
      have hh : residualPorts q k = p 1 := by simpa using congrArg p he
      rcases hheads with ⟨_,ha⟩ | ⟨ha,_⟩
      · exact residual_ne_second q k (hh.trans ha.symm)
      · exact residual_ne_first q k (hh.trans ha.symm)
    have hn0 : (p.symm (residualPorts q k)).val ≠ 0 := by
      intro he; exact h0 (Fin.ext he)
    have hn1 : (p.symm (residualPorts q k)).val ≠ 1 := by
      intro he; exact h1 (Fin.ext he)
    omega
  let f : Fin 4 → Fin 4 := fun k =>
    ⟨(p.symm (residualPorts q k)).val - 2,by have := hb k; omega⟩
  have hf : ∀ k, (f k).succ.succ = p.symm (residualPorts q k) := by
    intro k
    apply Fin.ext
    dsimp [f]
    have := hb k
    omega
  have hinj : Function.Injective f := by
    intro i j he
    apply residual_injective q
    apply p.symm.injective
    rw [←hf i,←hf j,he]
  let e : Equiv.Perm (Fin 4) := Equiv.ofBijective f
    ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨e,fun k => by rw [show (e k).succ.succ = p.symm (residualPorts q k) from hf k]; simp⟩

/-- Exact word identity, not merely a correspondence of supports. The flag
records reversal of the selected pair, and `e` carries the actual residual
coordinates to their increasing canonical order. -/
theorem exists_lift_reindex (p : Equiv.Perm (Fin 6)) :
    ∃ q : Fin 15, ∃ flag : Bool, ∃ e : Equiv.Perm (Fin 4),
      ∀ ξ b r, SixPortSupport.lift p ξ b r =
        liftWord q ξ (b ^^ (flag && ξ)) (fun i => r (e i)) := by
  classical
  have hne : p 0 ≠ p 1 := fun he => (by decide : (0 : Fin 6) ≠ 1) (p.injective he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨q,hq⟩ := pairPorts_complete (p 0) (p 1) hlt
    have hheads : (pairPorts q).1 = p 0 ∧ (pairPorts q).2 = p 1 := by
      constructor <;> exact congrArg _ hq
    obtain ⟨e,he⟩ := residual_reindex p q (Or.inl hheads)
    refine ⟨q,false,e,?_⟩
    intro ξ b r
    have h0 : SixPortSupport.lift p ξ b r (pairPorts q).1 = b := by rw [hheads.1]; simp
    have h1 : SixPortSupport.lift p ξ b r (pairPorts q).2 = (b ^^ ξ) := by rw [hheads.2]; simp
    have hr : (fun k => SixPortSupport.lift p ξ b r (residualPorts q k)) =
        (fun k => r (e k)) := by funext k; rw [he]; simp
    have hx := liftWord_exhaustive q (SixPortSupport.lift p ξ b r)
    rw [h0,h1,hr] at hx
    cases ξ <;> cases b <;> simpa using hx.symm
  · obtain ⟨q,hq⟩ := pairPorts_complete (p 1) (p 0) hgt
    have hheads : (pairPorts q).1 = p 1 ∧ (pairPorts q).2 = p 0 := by
      constructor <;> exact congrArg _ hq
    obtain ⟨e,he⟩ := residual_reindex p q (Or.inr hheads)
    refine ⟨q,true,e,?_⟩
    intro ξ b r
    have h0 : SixPortSupport.lift p ξ b r (pairPorts q).1 = (b ^^ ξ) := by rw [hheads.1]; simp
    have h1 : SixPortSupport.lift p ξ b r (pairPorts q).2 = b := by rw [hheads.2]; simp
    have hr : (fun k => SixPortSupport.lift p ξ b r (residualPorts q k)) =
        (fun k => r (e k)) := by funext k; rw [he]; simp
    have hx := liftWord_exhaustive q (SixPortSupport.lift p ξ b r)
    rw [h0,h1,hr] at hx
    cases ξ <;> cases b <;> simpa using hx.symm

/-- The canonical fifteen permutations use the precise existing certificate
port order. -/
theorem canonical_lift (q : Fin 15) (ξ b : Bool) (r : Fin 4 → Bool) :
    SixPortSupport.lift (canonical q) ξ b r = liftWord q ξ b r := by
  have h0 : SixPortSupport.lift (canonical q) ξ b r (pairPorts q).1 = b := by
    simpa only [canonical_zero] using lift_zero (canonical q) ξ b r
  have h1 : SixPortSupport.lift (canonical q) ξ b r (pairPorts q).2 = (b ^^ ξ) := by
    simpa only [canonical_one] using lift_one (canonical q) ξ b r
  have hr : (fun k => SixPortSupport.lift (canonical q) ξ b r (residualPorts q k)) = r := by
    funext k
    simpa only [canonical_tail] using lift_tail (canonical q) ξ b r k
  have hx := liftWord_exhaustive q (SixPortSupport.lift (canonical q) ξ b r)
  rw [h0,h1,hr] at hx
  cases ξ <;> cases b <;> simpa using hx.symm

end Paper2.Certificates.DihedralSupport.SixPortCanonicalPairs

