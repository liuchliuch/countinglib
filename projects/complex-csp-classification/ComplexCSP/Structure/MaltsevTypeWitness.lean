import ComplexCSP.Structure.MaltsevTypeMaterialized

/-! # Finding a full support tuple with a prescribed computed type label -/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*} [DecidableEq A]

def labelExtension (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) :
    ℕ → ℕ → Tuple (Fin d) n → Option (Tuple (Fin d) n)
  | 0, len, target => (reconstructTo m W target len).filter (fun x => label x == wanted)
  | fuel + 1, len, target =>
    if h : len < n then do
      let a ← (List.finRange d).find? (fun a => decide (wanted ∈
        (materializedTypeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, h⟩ a) []).1))
      labelExtension m W label wanted fuel (len + 1) (replaceCoordinate target ⟨len, h⟩ a)
    else (reconstructTo m W target len).filter (fun x => label x == wanted)

theorem labelExtension_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (wanted : A) (fuel len : ℕ) (hdepth : len + fuel = n)
    (target : Tuple (Fin d) n) {result : Tuple (Fin d) n}
    (he : labelExtension m W label wanted fuel len target = some result) :
    view result ∈ R ∧ PrefixEq len (view result) (view target) ∧ label result = wanted := by
  induction fuel generalizing len target with
  | zero =>
    obtain ⟨hr, hp⟩ := Option.filter_eq_some_iff.mp he
    exact ⟨reconstructTo_sound hR hW _ _ hr,
      reconstructTo_prefix hm hW _ _ (by omega) hr, by simpa using hp⟩
  | succ fuel ih =>
    have hlt : len < n := by omega
    simp only [labelExtension, dif_pos hlt] at he
    cases ha : (List.finRange d).find? (fun a => decide (wanted ∈
        (materializedTypeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) []).1)) with
    | none => simp [ha] at he
    | some a =>
      simp only [ha] at he
      have hr := ih (len + 1) (by omega) _ he
      exact ⟨hr.1, ((prefix_replace_iff target ⟨len, hlt⟩ a _).mp hr.2.1).1.symm, hr.2.2⟩

theorem labelExtension_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label) (wanted : A)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (ht : HasType R label len target wanted) :
    ∃ result, labelExtension m W label wanted fuel len target = some result := by
  induction fuel generalizing len target with
  | zero =>
    have hln : len = n := by omega
    subst len
    obtain ⟨x, hx, hp, hlabel⟩ := ht
    have hfull : x = view target := hp.eq
    have htR : view target ∈ R := hfull ▸ hx
    obtain ⟨result, hr, hpre⟩ := reconstructTo_complete hm hR hW target htR n le_rfl
    have heq : result = target := view_injective hpre.eq
    have hl : label result = wanted := by simpa [heq, hfull] using hlabel
    exact ⟨result, by simp [labelExtension, hr, hl]⟩
  | succ fuel ih =>
    have hlt : len < n := by omega
    obtain ⟨a, hta⟩ := (type_children R label target ⟨len, hlt⟩ wanted).mp ht
    have hsearch := materializedTypeSearch_correct hm hR hW label hTP fuel (len + 1) (by omega)
      (replaceCoordinate target ⟨len, hlt⟩ a) wanted
    have hmem := hsearch.mpr hta
    have hex : ((List.finRange d).find? (fun a => decide (wanted ∈
        (materializedTypeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) []).1))).isSome = true :=
      List.find?_isSome.mpr ⟨a, List.mem_finRange _, by simpa using hmem⟩
    cases hb : (List.finRange d).find? (fun a => decide (wanted ∈
        (materializedTypeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) []).1)) with
    | none => simp [hb] at hex
    | some b =>
      have hp := List.find?_some hb
      have hsearch' := materializedTypeSearch_correct hm hR hW label hTP fuel (len + 1) (by omega)
        (replaceCoordinate target ⟨len, hlt⟩ b) wanted
      have htb := hsearch'.mp (of_decide_eq_true hp)
      obtain ⟨result, hr⟩ := ih (len + 1) (by omega) _ htb
      exact ⟨result, by simp only [labelExtension, dif_pos hlt, hb]; exact hr⟩

theorem labelExtension_isSome {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label) (wanted : A)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n) :
    (labelExtension m W label wanted fuel len target).isSome = true ↔ HasType R label len target wanted := by
  constructor
  · intro h
    cases he : labelExtension m W label wanted fuel len target with
    | none => simp [he] at h
    | some result =>
      obtain ⟨hr, hp, hl⟩ := labelExtension_spec hm hR hW label wanted fuel len hdepth target he
      exact ⟨view result, hr, hp, by simpa using hl⟩
  · intro h
    obtain ⟨result, hr⟩ := labelExtension_complete hm hR hW label hTP wanted fuel len hdepth target h
    simp [hr]

end ComplexCSP.MaltsevWitness
