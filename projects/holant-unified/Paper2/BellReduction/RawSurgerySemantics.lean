import Paper2.BellReduction.RawNativeSemantics
import Paper2.BellReduction.RawOccurrence
import Paper2.BellReduction.OccurrenceGraph

/-! Exact semantics of the raw 3-to-1 Bell surgery. The new native bits are
summed explicitly; every old edge assignment and every other vertex survives. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.BellReduction.RawNative
open Complexity RawOccurrence Bell Bell.Closures ReedMuller
variable {K : Type} [CommRing K]

/-- Add two independent native edge bits, after all original edge indices. -/
theorem sum_append_two (n : ℕ) (f : (Fin (n+2) → Bool) → K) :
    (∑ x, f x) = ∑ z : Fin n → Bool, ∑ w : Fin 2 → Bool, f (Fin.append z w) := by
  rw [← (Fin.appendEquiv n 2).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

theorem readEnd_append_old {n : ℕ} (z : Fin n → Bool) (w : Fin 2 → Bool)
    (p : RawEndpoint) (hp : p.1 < n) :
    readEnd (Fin.append z w) p = readEnd z p := by
  have hp' : p.1 < n+2 := by omega
  simp only [readEnd,dif_pos hp,dif_pos hp']
  change (if p.2 then !(Fin.append z w (Fin.castAdd 2 ⟨p.1,hp⟩))
    else Fin.append z w (Fin.castAdd 2 ⟨p.1,hp⟩)) = _
  rw [Fin.append_left]

theorem readEnd_append_new {n : ℕ} (z : Fin n → Bool) (w : Fin 2 → Bool)
    (i : Fin 2) (b : Bool) :
    readEnd (Fin.append z w) (n+i.val,b) = if b then !(w i) else w i := by
  have hi : n+i.val < n+2 := by omega
  simp only [readEnd,dif_pos hi]
  change (if b then !(Fin.append z w (Fin.natAdd n i))
    else Fin.append z w (Fin.natAdd n i)) = _
  rw [Fin.append_right]

theorem rowValue_append_old {n : ℕ} (T : ℕ → List Bool → K)
    (z : Fin n → Bool) (w : Fin 2 → Bool) (v : RawVertex)
    (hv : ∀ p ∈ v.2, p.1 < n) :
    rowValue T (Fin.append z w) v = rowValue T z v := by
  apply congrArg (T v.1)
  apply List.map_congr_left
  intro p hp
  exact readEnd_append_old z w p (hv p hp)

/-- The numerical contraction underlying the actual occurrence graph, in the
new-edge-last coordinate order used by the raw compiler. -/
theorem bell_native_sum (c : K) (d l : Bool) (x : Fin 6 → Bool) :
    (∑ w : Fin 2 → Bool, (c * core (Fin.append w x)) * ordered d l (!(w 0)) (!(w 1))) =
      c * sign l * bellTriple d l x := by
  have h := congrFun (contract_core_bell (K := K) d l) x
  simp only [Signature.contract,Fintype.sum_bool] at h
  simp only [sum_word_succ,sum_word_zero,Fintype.sum_bool,
    Fin.cons_zero,Fin.cons_one,Bool.not_false,Bool.not_true]
  have he (a b : Bool) : Fin.append (Fin.cons a (Fin.cons b Fin.elim0)) x =
      Fin.cons a (Fin.cons b x) := by
    funext i
    fin_cases i <;> rfl
  simp only [he]
  rw [← h]
  cases d <;> cases l <;> simp [ordered,sign] <;> ring

/-- The Bell occurrence identity in the literal list-table interface. -/
theorem list_bell_native_sum (T : ℕ → List Bool → K) (coreLabel : ℕ) (c : K)
    (d l : Bool) (hB : ∀ a b, T 0 [a,b] = ordered d l a b)
    (hC : ∀ x : Fin 8 → Bool, T coreLabel (List.ofFn x) = c * core x)
    (p q r : List Bool) (hp : p.length = 2) (hq : q.length = 2) (hr : r.length = 2) :
    (∑ w : Fin 2 → Bool, T coreLabel ([w 0,w 1] ++ p ++ q ++ r) *
      T 0 [!(w 0),!(w 1)]) = c * sign l * (T 0 p * T 0 q * T 0 r) := by
  obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hp
  obtain ⟨u,v,rfl⟩ := List.length_eq_two.mp hq
  obtain ⟨s,t,rfl⟩ := List.length_eq_two.mp hr
  have hc (w : Fin 2 → Bool) :
      T coreLabel ([w 0,w 1] ++ [a,b] ++ [u,v] ++ [s,t]) =
        c * core (Fin.append w ![a,b,u,v,s,t]) := by
    rw [← hC]
    congr 1
  simp only [hc,hB]
  exact bell_native_sum c d l ![a,b,u,v,s,t]

/-- The old vertex product splits into the three removed rows and all retained
rows, without losing disconnected components or nullary factors. -/
theorem old_product (T : ℕ → List Bool → K) (G : RawClosedNetwork) (t : Split)
    (hs : splitThree G.vertices = some t) (z : Fin G.edges.length → Bool) :
    (G.vertices.map (rowValue T z)).prod = (t.rest.map (rowValue T z)).prod *
      (T 0 (t.first.map (readEnd z)) * T 0 (t.second.map (readEnd z)) *
        T 0 (t.third.map (readEnd z))) := by
  have h := ((splitThree_perm hs).map (rowValue T z)).prod_eq
  simp only [List.map_cons,List.prod_cons,rowValue] at h
  rw [h]
  ring

/-- The complete raw step multiplies the old partition value by the retained
nonzero-normalization factor c*(-1)^l, even when the three selected vertices
have self-loops or edges between one another. -/
theorem evaluate_perform (T : ℕ → List Bool → K) (G : RawClosedNetwork)
    (coreLabel : ℕ) (t : Split) (hs : splitThree G.vertices = some t)
    (hb : ∀ p ∈ G.endpoints, p.1 < G.edges.length)
    (hfirst : t.first.length = 2) (hsecond : t.second.length = 2) (hthird : t.third.length = 2)
    (c : K) (d l : Bool) (hB : ∀ a b, T 0 [a,b] = ordered d l a b)
    (hC : ∀ x : Fin 8 → Bool, T coreLabel (List.ofFn x) = c * core x) :
    evaluate T (perform G coreLabel t) = c * sign l * evaluate T G := by
  have hrow (v : RawVertex) (hv : v ∈ G.vertices) (p : RawEndpoint) (hp : p ∈ v.2) :
      p.1 < G.edges.length := hb p (List.mem_flatten.mpr
        ⟨v.2,List.mem_map.mpr ⟨v,hv,rfl⟩,hp⟩)
  have hperm := splitThree_perm hs
  have hb₁ : ∀ p ∈ t.first, p.1 < G.edges.length :=
    hrow (0,t.first) (hperm.mem_iff.mpr (by simp))
  have hb₂ : ∀ p ∈ t.second, p.1 < G.edges.length :=
    hrow (0,t.second) (hperm.mem_iff.mpr (by simp))
  have hb₃ : ∀ p ∈ t.third, p.1 < G.edges.length :=
    hrow (0,t.third) (hperm.mem_iff.mpr (by simp))
  have hbrest (v : RawVertex) (hv : v ∈ t.rest) : ∀ p ∈ v.2, p.1 < G.edges.length :=
    hrow v (hperm.mem_iff.mpr (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))))
  unfold evaluate
  rw [perform_edges,sum_append_two,Finset.mul_sum]
  dsimp only [perform]
  apply Finset.sum_congr rfl
  intro z _
  have hrest (w : Fin 2 → Bool) :
      (t.rest.map (rowValue T (Fin.append z w))).prod = (t.rest.map (rowValue T z)).prod := by
    congr 1
    apply List.map_congr_left
    intro v hv
    exact rowValue_append_old T z w v (hbrest v hv)
  have hm (p : List RawEndpoint) (hp : ∀ a ∈ p, a.1 < G.edges.length) (w : Fin 2 → Bool) :
      p.map (readEnd (Fin.append z w)) = p.map (readEnd z) := by
    apply List.map_congr_left
    intro a ha
    exact readEnd_append_old z w a (hp a ha)
  have h0 (w : Fin 2 → Bool) (b : Bool) :
      readEnd (Fin.append z w) (G.edges.length,b) = if b then !(w 0) else w 0 := by
    simpa using readEnd_append_new z w (0 : Fin 2) b
  have h1 (w : Fin 2 → Bool) (b : Bool) :
      readEnd (Fin.append z w) (G.edges.length+1,b) = if b then !(w 1) else w 1 := by
    simpa using readEnd_append_new z w (1 : Fin 2) b
  simp only [List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,
    List.prod_nil,mul_one,hrest]
  simp only [rowValue,List.map_append,List.map_cons,List.map_nil,h0,h1,Bool.false_eq_true,ite_false,ite_true,
    hm t.first hb₁,hm t.second hb₂,hm t.third hb₃]
  rw [← Finset.mul_sum]
  rw [list_bell_native_sum T coreLabel c d l hB hC _ _ _
    (by simpa using hfirst) (by simpa using hsecond) (by simpa using hthird)]
  rw [old_product T G t hs z]
  ring

end Paper2.BellReduction.RawNative
