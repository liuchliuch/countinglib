import Paper2.Certificates.Q8Support
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The literal plane--unordered-port-pair incidence graph in Proposition A.10.
Canonical increasing pairs represent each unordered two-element port set once.
Its connectivity follows from the checked common-reference crossing witness,
and every pair is incident with a genuine affine plane. -/
namespace Paper2.SourceFaithful.SourceStatements.AppendixSupport
open Paper2.ReedMuller Paper2.Certificates.Q8
noncomputable section

abbrev Plane := {x : Word // weight x = 4 ∧ supportXor x = fun _ => false}
abbrev PortPair := {p : Fin 8 × Fin 8 // p.1 < p.2}

def planeSet : Finset Word :=
  Finset.univ.filter (fun x => weight x = 4 ∧ supportXor x = fun _ => false)

theorem planeSet_eq_central : planeSet = code.filter (fun x => weight x = 4) := by
  ext x
  simp only [planeSet,Finset.mem_filter,Finset.mem_univ,true_and,mem_code]
  exact (central_iff_plane x).symm

theorem plane_count : Fintype.card Plane = 14 := by
  rw [Fintype.card_subtype]
  change planeSet.card=14
  rw [planeSet_eq_central,card_central]

theorem nonplane_count : Fintype.card {x : Word //
    weight x=4 ∧ supportXor x≠fun _=>false} = 56 := by
  rw [Fintype.card_subtype]
  exact card_nonplanes

def referencePlane : Plane := ⟨fromMask 15,by decide +kernel⟩

def orderedPair (p q : Fin 8) (h : p≠q) : PortPair :=
  if ht : p<q then ⟨(p,q),ht⟩ else
    ⟨(q,p),by exact lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm h)⟩

lemma orderedPair_cross (x : Word) (p q : Fin 8) (h : p≠q) :
    x (orderedPair p q h).val.1 ≠ x (orderedPair p q h).val.2 ↔ x p≠x q := by
  unfold orderedPair
  split_ifs <;> simp only
  exact ne_comm

def Incidence : (Plane ⊕ PortPair) → (Plane ⊕ PortPair) → Prop
  | .inl x,.inr p => x.val p.val.1 ≠ x.val p.val.2
  | .inr p,.inl x => x.val p.val.1 ≠ x.val p.val.2
  | _,_ => False

def H : SimpleGraph (Plane ⊕ PortPair) where
  Adj := Incidence
  symm := ⟨by rintro (x|p) (y|q) <;> simp only [Incidence] <;> exact id⟩
  loopless := ⟨by rintro (x|p) <;> simp only [Incidence,not_false_eq_true]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pair_has_plane (p q : Fin 8) (h : p≠q) :
    ∃ x : Word,weight x=4 ∧ supportXor x=(fun _=>false) ∧ x p≠x q := by
  revert p q
  decide +kernel

lemma reference_reachable_plane (x : Plane) : H.Reachable (.inl referencePlane) (.inl x) := by
  obtain ⟨p,q,hp,hq,hcross⟩ := common_reference_pair x.val x.property.1 x.property.2
  have hne : p≠q := by intro he; subst q; simp_all
  let pair := orderedPair p q hne
  have hx : H.Adj (.inl x) (.inr pair) := by
    exact (orderedPair_cross x.val p q hne).mpr (by rw [hp,hq]; decide)
  have hr : H.Adj (.inl referencePlane) (.inr pair) :=
    (orderedPair_cross (fromMask 15) p q hne).mpr hcross
  exact hr.reachable.trans hx.reachable.symm

theorem incidence_connected : H.Connected := by
  apply H.connected_iff_exists_forall_reachable.mpr
  refine ⟨.inl referencePlane,?_⟩
  rintro (x|p)
  · exact reference_reachable_plane x
  · have hpq : p.val.1≠p.val.2 := ne_of_lt p.property
    obtain ⟨x,hw,hxor,hcross⟩ := pair_has_plane p.val.1 p.val.2 hpq
    let plane : Plane := ⟨x,hw,hxor⟩
    have hi : H.Adj (.inl plane) (.inr p) := hcross
    exact (reference_reachable_plane plane).trans hi.reachable

end
end Paper2.SourceFaithful.SourceStatements.AppendixSupport

