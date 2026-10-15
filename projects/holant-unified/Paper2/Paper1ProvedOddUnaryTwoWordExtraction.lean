import Paper2.Paper1ProvedOddUnaryTwoWordGap
import Paper2.RelativeEO.GeneralizedEqualityGadget

/-! Least-arity extraction with physical pin caps and native X loops. The
least positive occupied weight gap is preserved throughout the descent. A
common selected coordinate can be pinned away; a mixed complementary pair
has either a two-pin exit or a cancellation-free X-loop exit. Minimality
therefore leaves exactly two endpoint words, at arity equal to that gap. -/
namespace Paper2.Paper1Proved.OddUnary.TwoWordExtraction
open Paper2 Paper2.Tractable Paper2.ExactInput Paper2.Paper1Proved
open TwoWordDescent
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def RetainsGap (F : SignatureFamily AlgebraicComplex) (d m : ℕ) : Prop :=
  ∃ f : Signature AlgebraicComplex m, NetworkRealizable F f ∧ MinimumGap f d ∧
    ∃ x y, f x≠0 ∧ f y≠0 ∧ gap x y=(d : ℤ)

theorem minimal_endpoints (F : SignatureFamily AlgebraicComplex) {d m : ℕ}
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hd : 0<d) (f : Signature AlgebraicComplex m) (hf : NetworkRealizable F f)
    (hgap : MinimumGap f d) (x y : Fin m → Bool) (hx : f x≠0) (hy : f y≠0)
    (hxy : gap x y=(d : ℤ))
    (hminimal : ∀ q, q<m → ¬RetainsGap F d q) :
    m=d ∧ f (fun _=>false)≠0 ∧ f (fun _=>true)≠0 := by
  classical
  have hpin (b : Bool) :
      (⟨1,TensorDecomposition.literalPin (!b)⟩ : AnySignature AlgebraicComplex) ∈ F := by
    cases b
    · exact h1
    · exact h0
  cases m with
  | zero =>
    have hwx : weight x=0 := le_antisymm (weight_le x) (Nat.zero_le _)
    have hwy : weight y=0 := le_antisymm (weight_le y) (Nat.zero_le _)
    simp [gap,hwx,hwy] at hxy
    omega
  | succ n =>
    have noAgree : ∀ i, x i≠y i := by
      intro i hi
      obtain ⟨hcx,hcy,hcd⟩ := agreeing_pin f i x y hx hy hi
      apply hminimal n (by omega)
      refine ⟨PinDeletion.pinCoordinate f i (x i),
        PinDeletion.pinCoordinate_of_realizable_family F f i (x i) hf (hpin _),
        minimumGap_pin f d hgap i (x i),Fin.removeNth i x,Fin.removeNth i y,hcx,hcy,?_⟩
      exact hcd.trans hxy
    have comp : ∀ i, y i=!(x i) := by
      intro i
      have hi := noAgree i
      cases hx' : x i <;> cases hy' : y i <;> simp_all
    have endpoints : x=(fun _=>false) ∨ x=(fun _=>true) := by
      by_contra hn
      push Not at hn
      have ez : ∃ i, x i=false := by
        by_contra he
        push Not at he
        apply hn.2
        funext i
        cases h : x i
        · exact False.elim (he i h)
        · rfl
      have eo : ∃ k, x k=true := by
        by_contra he
        push Not at he
        apply hn.1
        funext k
        cases h : x k
        · rfl
        · exact False.elim (he k h)
      obtain ⟨i,hi⟩ := ez
      obtain ⟨k,hk⟩ := eo
      have hki : k≠i := by
        intro he
        subst k
        rw [hi] at hk
        contradiction
      cases n with
      | zero => exact hki ((Fin.eq_zero k).trans (Fin.eq_zero i).symm)
      | succ q =>
        obtain ⟨j,hj⟩ := (Fin.eq_self_or_eq_succAbove i k).resolve_left hki
        have hxi : x (i.succAbove j)=!(x i) := by rw [←hj,hi,hk]; rfl
        have hyi : y (i.succAbove j)=!(y i) := by rw [comp,comp,hxi]
        let xx := Fin.removeNth j (Fin.removeNth i x)
        let yy := Fin.removeNth j (Fin.removeNth i y)
        have hxw : f (PinPairLoop.pairWord i j (x i) xx)≠0 := by
          simpa only [xx,pairWord_remove i j x hxi] using hx
        have hyw : f (PinPairLoop.pairWord i j (!(x i)) yy)≠0 := by
          rw [←comp i]
          simpa only [yy,pairWord_remove i j y hyi] using hy
        have ht : gap xx yy=(d : ℤ) :=
          (pair_gap_remove i j x y hxi hyi).trans hxy
        rcases pair_step f i j (x i) xx yy hxw hyw with hfixed | hloop
        · obtain ⟨a,ha,hb⟩ := hfixed
          apply hminimal q (by omega)
          exact ⟨PinPairLoop.pairPin f i j a (!a),
            PinPairLoop.pairPin_realizable_of_realizable_family F f i j a (!a) hf
              (hpin a) (hpin (!a)),minimumGap_pairPin f d hgap i j a (!a),
            xx,yy,ha,hb,ht⟩
        · apply hminimal q (by omega)
          exact ⟨PinPairLoop.pairLoop f i j,
            PinPairLoop.pairLoop_realizable_of_realizable_family F f i j hf,
            minimumGap_pairLoop f d hgap i j,xx,yy,hloop.1,hloop.2,ht⟩
    rcases endpoints with ex | ex
    · have ey : y=(fun _=>true) := by funext i; rw [comp,ex]; rfl
      have he : n+1=d := by
        rw [ex,ey,endpoints_gap] at hxy
        exact_mod_cast hxy
      exact ⟨he,ex ▸ hx,ey ▸ hy⟩
    · have ey : y=(fun _=>false) := by funext i; rw [comp,ex]; rfl
      simp [gap,ex,ey] at hxy
      omega

theorem generalizedEquality_of_minimumGap (F : SignatureFamily AlgebraicComplex)
    {n d : ℕ} (f : Signature AlgebraicComplex n) (hf : NetworkRealizable F f)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hd : 0<d) (hgap : MinimumGap f d) (x y : Fin n → Bool)
    (hx : f x≠0) (hy : f y≠0) (hxy : gap x y=(d : ℤ)) :
    ∃ a b : AlgebraicComplex, a≠0 ∧ b≠0 ∧
      NetworkRealizable F (RelativeEO.generalizedEquality (n := d) a b) := by
  classical
  have existsP : ∃ m,RetainsGap F d m := ⟨n,f,hf,hgap,x,y,hx,hy,hxy⟩
  let m := Nat.find existsP
  obtain ⟨g,hg,hm,u,v,hu,hv,huv⟩ := Nat.find_spec existsP
  have hminimal : ∀ q,q<m → ¬RetainsGap F d q := by
    intro q hq hretain
    have hle := Nat.find_min' existsP hretain
    dsimp only [m] at hq
    omega
  obtain ⟨he,hzero,hone⟩ := minimal_endpoints F h0 h1 hd g hg hm u v hu hv huv hminimal
  have he' : Nat.find existsP=d := he
  rw [←he']
  refine ⟨g (fun _=>false),g (fun _=>true),hzero,hone,?_⟩
  have hm' : MinimumGap g (Nat.find existsP) :=
    Eq.mp (congrArg (fun r : ℕ => MinimumGap g r) he'.symm) hm
  have form : g=RelativeEO.generalizedEquality (n := Nat.find existsP)
      (g (fun _=>false)) (g (fun _=>true)) := by
    have hn : 0<Nat.find existsP := by omega
    have distinct : (fun _ : Fin (Nat.find existsP)=>false)≠(fun _=>true) := by
      intro h
      exact Bool.false_ne_true (congrFun h ⟨0,hn⟩)
    funext z
    by_cases hz : z=(fun _=>false)
    · subst z
      simp [RelativeEO.generalizedEquality,distinct]
    · by_cases hz' : z=(fun _=>true)
      · subst z
        simp [RelativeEO.generalizedEquality,Ne.symm distinct]
      · have zero := endpoint_only_of_minimumGap g hm' hzero z hz hz'
        simp [RelativeEO.generalizedEquality,hz,hz',zero]
  exact form ▸ hg

theorem generalizedEquality_of_not_singleLayer (F : SignatureFamily AlgebraicComplex)
    {n : ℕ} (f : Signature AlgebraicComplex n) (hf : NetworkRealizable F f)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hmulti : ¬∃ c,Signature.SingleLayer f c) :
    ∃ k : ℕ, ∃ a b : AlgebraicComplex, 0<k ∧ a≠0 ∧ b≠0 ∧
      NetworkRealizable F (RelativeEO.generalizedEquality (n := k) a b) := by
  obtain ⟨d,hd,hgap,x,y,hx,hy,hxy⟩ := least_occupied_gap f hmulti
  obtain ⟨a,b,ha,hb,hgraph⟩ :=
    generalizedEquality_of_minimumGap F f hf h0 h1 hd hgap x y hx hy hxy
  exact ⟨d,a,b,hd,ha,hb,hgraph⟩

end
end Paper2.Paper1Proved.OddUnary.TwoWordExtraction
