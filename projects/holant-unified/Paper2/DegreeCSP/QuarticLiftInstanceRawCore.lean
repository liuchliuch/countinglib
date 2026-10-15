import Paper2.DegreeCSP.RawData

/-! Finite occurrence semantics for a literally enumerated raw CSP record. -/
namespace Paper2.DegreeCSP.QuarticLiftInstance
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) rawCoreDecEq (α : Type) : DecidableEq α := Classical.decEq α
local instance (priority := 3000) rawCoreBoolEq : DecidableEq Bool := Bool.decEq

variable {J : Type} [Fintype J]

def rawPortEquiv (R : Raw) (a : J → ℕ) (ce : J ≃ Fin R.factors.length)
    (hlen : ∀ c,(R.factors.get (ce c)).2.length = a c) :
    (Σ c : J,Fin (a c)) ≃ Raw.Ports R :=
  (Equiv.sigmaCongrRight (fun c => finCongr (hlen c).symm)).trans
    (Equiv.sigmaCongrLeft (β := fun c : Fin R.factors.length => Fin (R.factors.get c).2.length) ce)

theorem rawPort_address (R : Raw) (a : J → ℕ) (ce : J ≃ Fin R.factors.length)
    (lab : J → ℕ) (sc : (c : J) → Fin (a c) → Fin R.variables)
    (hrow : ∀ c,R.factors.get (ce c) = (lab c,List.ofFn (fun j => (sc c j).val)))
    (c : J) (j : Fin (a c)) :
    Raw.address R (rawPortEquiv R a ce (fun c => by rw [hrow]; exact List.length_ofFn) ⟨c,j⟩) =
      (sc c j).val := by
  change (R.factors.get (ce c)).2[j.val]'_ = (sc c j).val
  simp only [hrow,List.getElem_ofFn]

def rawFiberOrdinal (R : Raw) (i : ℕ) :
    {p : Raw.Ports R // Raw.address R p = i} ≃ Fin (Raw.degree R i) :=
  (Equiv.subtypeEquivRight (fun p => (R.occurrences_mem i p).symm)).trans
    (List.Nodup.getEquiv (Raw.occurrences R i) (R.occurrences_nodup i)).symm

theorem raw_degree_card (R : Raw) (i : ℕ) :
    Raw.degree R i = Nat.card {p : Raw.Ports R // Raw.address R p = i} := by
  rw [Nat.card_congr (rawFiberOrdinal R i),Nat.card_fin]

theorem literal_eval {K : Type} {n m : ℕ} (f : Signature K n) (g : Signature K m)
    (h : (⟨n,f⟩ : AnySignature K) = ⟨m,g⟩) (x : Fin m → Bool) :
    f (fun j => x (Fin.cast (congrArg Sigma.fst h) j)) = g x := by
  cases h
  rfl


theorem raw_degree_scope (R : Raw) (a : J → ℕ) (ce : J ≃ Fin R.factors.length)
    (lab : J → ℕ) (sc : (c : J) → Fin (a c) → Fin R.variables)
    (hrow : ∀ c,R.factors.get (ce c) = (lab c,List.ofFn (fun j => (sc c j).val)))
    (i : Fin R.variables) :
    Raw.degree R i.val = Nat.card {o : Σ c : J,Fin (a c) // sc o.1 o.2 = i} := by
  rw [raw_degree_card]
  apply Nat.card_congr
  apply Equiv.symm
  refine Equiv.subtypeEquiv (rawPortEquiv R a ce (fun c => by rw [hrow]; exact List.length_ofFn)) ?_
  intro o
  rw [rawPort_address R a ce lab sc hrow o.1 o.2]
  exact Fin.ext_iff


theorem instance_degree_natCard {K : Type} (I : Instance K) (i : Fin I.variableCount) :
    I.degree i = Nat.card (I.Fiber i) := by
  exact (@Nat.card_eq_fintype_card (I.Fiber i)
    (@Subtype.fintype I.Occurrence (fun o => I.route o = i)
      (fun o => instDecidableEqFin I.variableCount (I.route o) i) inferInstance)).symm

theorem label_eval {K : Type} {s : ℕ} {a : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (a i.val)) {i j : Fin s}
    (h : i=j) (x : Fin (a i.val) → Bool) :
    G i x = G j (fun u => x (Fin.cast (congrArg (fun z => a z.val) h).symm u)) := by
  cases h
  rfl

theorem raw_value_named {K : Type} [CommSemiring K]
    {s k : ℕ} {dictArity : ℕ → ℕ}
    (G : (i : Fin s) → Signature K (dictArity i.val))
    (R : Raw) (hvalid : Raw.Valid s dictArity k R)
    (a : J → ℕ) (ce : J ≃ Fin R.factors.length) (lab : J → Fin s)
    (sc : (c : J) → Fin (a c) → Fin R.variables)
    (tab : (c : J) → Signature K (a c))
    (hrow : ∀ c,R.factors.get (ce c) = ((lab c).val,List.ofFn (fun j => (sc c j).val)))
    (hlit : ∀ c,(⟨dictArity (lab c).val,G (lab c)⟩ : AnySignature K) = ⟨a c,tab c⟩) :
    Raw.value G ⟨R,hvalid⟩ = ∑ x : Fin R.variables → Bool,
      ∏ c : J,tab c (fun j => x (sc c j)) := by
  unfold Raw.value Raw.factorWeight
  refine Finset.sum_congr ?_ ?_
  · ext x; simp only [Finset.mem_univ]
  intro x _
  calc
    _ = ∏ c : J,G (Raw.label ⟨R,hvalid⟩ (ce c))
        (fun j => x (Raw.route ⟨R,hvalid⟩ (Raw.portCast ⟨R,hvalid⟩ (ce c) j))) :=
      (ce.prod_comp _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro c _
      have hl : Raw.label ⟨R,hvalid⟩ (ce c) = lab c := by
        apply Fin.ext
        exact congrArg Prod.fst (hrow c)
      have ha := congrArg Sigma.fst (hlit c)
      have hp (j : Fin (dictArity (lab c).val)) :
          Raw.route ⟨R,hvalid⟩ (Raw.portCast ⟨R,hvalid⟩ (ce c) (Fin.cast (congrArg (fun z => dictArity z.val) hl).symm j)) =
            sc c (Fin.cast ha j) := by
        apply Fin.ext
        change (R.factors.get (ce c)).2[j.val]'_ = (sc c (Fin.cast ha j)).val
        simp only [hrow,List.getElem_ofFn]
        rfl
      have he := literal_eval (G (lab c)) (tab c) (hlit c) (fun j => x (sc c j))
      rw [label_eval G hl]
      convert he using 1
      congr 1
      funext j
      rw [hp]

end
end Paper2.DegreeCSP.QuarticLiftInstance
