import Paper2.HeightThree.SubsetSum

/-! Exact occupied-port sets of both copies of the actual four-wire network. -/
namespace Paper2.HeightThree
open Certificates.Q6
noncomputable section

lemma pairSplit_first (a b : Port) (h : a ≠ b) : pairSplit a b h a = .inr false := by
  simp [pairSplit,EndpointSelfLoop.splitPorts]
lemma pairSplit_second (a b : Port) (h : a ≠ b) : pairSplit a b h b = .inr true := by
  simp [pairSplit,EndpointSelfLoop.splitPorts,h,Ne.symm h]
lemma pairSplit_interior (a b : Port) (h : a ≠ b) (v : Interior a b) :
    pairSplit a b h v.val = .inl v := by
  have hv : v.val ≠ a ∧ v.val ≠ b := by
    simpa only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,
      true_and,not_or] using v.property
  simp [pairSplit,EndpointSelfLoop.splitPorts,hv.1,hv.2,remainingInterior]
  rfl

lemma subset_not_external (a b : Port) (T : PortSet) (hT : T ⊆ Finset.univ \ {a,b}) :
    a ∉ T ∧ b ∉ T := by
  constructor <;> intro h
  · have hh := hT h
    simp only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,
      true_or,not_true_eq_false,and_false] at hh
  · have hh := hT h
    simp only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,
      or_true,not_true_eq_false,and_false] at hh

lemma pairWord_subset (a b : Port) (h : a ≠ b) (x₀ x₁ : Bool) (T : PortSet)
    (hT : T ⊆ Finset.univ \ {a,b}) (v : Port) :
    Sum.elim (fun u : Interior a b => decide (u.val ∈ T)) (fun t => if t then x₁ else x₀)
      (pairSplit a b h v) = subsetWord (selected a b x₀ x₁ ∪ T) v := by
  have hn := subset_not_external a b T hT
  by_cases ha : v = a
  · subst v
    rw [pairSplit_first]
    cases x₀ <;> cases x₁ <;> simp [subsetWord,selected,hn.1,hn.2,h,Ne.symm h]
  by_cases hb : v = b
  · subst v
    rw [pairSplit_second]
    cases x₀ <;> cases x₁ <;> simp [subsetWord,selected,hn.1,hn.2,h,Ne.symm h]
  have hv : v ∈ Finset.univ \ {a,b} := by simp [ha,hb]
  rw [show v = (⟨v,hv⟩ : Interior a b).val from rfl,pairSplit_interior]
  cases x₀ <;> cases x₁ <;> simp [subsetWord,selected,ha,hb]

def sourceSetsAt (s : CardSpec) (x : Fin 4 → Bool) (T : PortSet) : PortSet × PortSet :=
  (selected s.left0 s.left1 (x 0) (x 1) ∪ T,
    selected s.right0 s.right1 (x 2) (x 3) ∪ (internalRight s \ T.image s.wiring))

lemma cardWord_left (s : CardSpec) (hs : RawValidCardSpec s) (x : Fin 4 → Bool)
    (T : PortSet) (hT : T ⊆ internalLeft s) :
    cardWord s hs x (internalAssignment s T) false = subsetWord (sourceSetsAt s x T).1 := by
  funext v
  change Sum.elim (fun u : LeftInterior s => decide (u.val ∈ T))
    (fun b => x (boundaryIndex false b)) (pairSplit s.left0 s.left1 hs.1 v) = _
  have hb : (fun b => x (boundaryIndex false b)) = (fun b => if b then x 1 else x 0) := by
    funext b; cases b <;> rfl
  rw [hb]
  exact pairWord_subset _ _ _ _ _ _ hT v

lemma right_complement_assignment (s : CardSpec) (hs : RawValidCardSpec s)
    (T : PortSet) (u : RightInterior s) :
    (!(internalAssignment s T ((interiorWiring s hs).symm u))) =
      decide (u.val ∈ internalRight s \ T.image s.wiring) := by
  obtain ⟨v,rfl⟩ := (interiorWiring s hs).surjective u
  rw [Equiv.symm_apply_apply]
  have hm : s.wiring v.val ∈ T.image s.wiring ↔ v.val ∈ T := by
    constructor
    · rintro h
      obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
      exact hs.2.2.1.1 he ▸ hw
    · intro hv
      exact Finset.mem_image.mpr ⟨v.val,hv,rfl⟩
  have hv := (interiorWiring s hs v).property
  change s.wiring v.val ∈ internalRight s at hv
  change (!(decide (v.val ∈ T))) = decide (s.wiring v.val ∈ internalRight s \ T.image s.wiring)
  simp only [Finset.mem_sdiff,hv,true_and,hm,decide_not]

lemma cardWord_right (s : CardSpec) (hs : RawValidCardSpec s) (x : Fin 4 → Bool)
    (T : PortSet) :
    cardWord s hs x (internalAssignment s T) true = subsetWord (sourceSetsAt s x T).2 := by
  funext v
  change Sum.elim (fun e : LeftInterior s => !(internalAssignment s T e))
    (fun b => x (boundaryIndex true b))
    (Equiv.sumCongr (interiorWiring s hs).symm (Equiv.refl Bool)
      (pairSplit s.right0 s.right1 hs.2.1 v)) = _
  have hh : Sum.elim (fun e : LeftInterior s => !(internalAssignment s T e))
      (fun b => x (boundaryIndex true b))
      (Equiv.sumCongr (interiorWiring s hs).symm (Equiv.refl Bool)
        (pairSplit s.right0 s.right1 hs.2.1 v)) =
      Sum.elim (fun u : RightInterior s => decide (u.val ∈ internalRight s \ T.image s.wiring))
        (fun b => if b then x 3 else x 2) (pairSplit s.right0 s.right1 hs.2.1 v) := by
    cases pairSplit s.right0 s.right1 hs.2.1 v with
    | inl u => exact right_complement_assignment s hs T u
    | inr b => cases b <;> rfl
  rw [hh]
  exact pairWord_subset _ _ _ _ _ _ Finset.sdiff_subset v

end
end Paper2.HeightThree
