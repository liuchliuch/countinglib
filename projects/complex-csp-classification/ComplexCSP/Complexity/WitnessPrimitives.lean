import ComplexCSP.Complexity.FiniteLookup
import PlanarHom.ListDropMachines
import PlanarHom.ListIndexMachines

/-! # Bit-costed primitives for materialized Mal'tsev witness algorithms

All tables and list lengths below are runtime data. Only the finite domain and
its ternary operation are fixed program constants. Binary indices are capped by
the existing bounded suffix machine, so invalid large indices cannot cause an
exponentially long unary loop.
-/
namespace ComplexCSP.ComplexityWitnessPrimitives
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives

abbrev wordCode : BitEncoding (List ℕ) := BitEncoding.nat.list
abbrev tripleCode := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)

/-- Total runtime list access, with an explicitly fixed default value. -/
theorem fp_getD {A : Type} (ea : BitEncoding A) (fallback : A) :
    FP (ea.list.prod BitEncoding.nat) ea (fun p => p.1.getD p.2 fallback) := by
  have hi := fp_snd ea.list BitEncoding.nat
  have hx := fp_fst ea.list BitEncoding.nat
  exact (((hi.pair hx).comp (ListDropMachines.fp_drop ea fallback)).comp
    (ListDecompositionMachines.fp_headD ea fallback)).congr (fun p => by
      simp only [Function.comp_apply, List.headD_eq_head?_getD, List.head?_drop,
        List.getD_eq_getElem?_getD])

/-- Fixed finite-operation lookup, represented by nested finite tables. -/
def operation (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d) (x y z : ℕ) : ℕ :=
  if hx : x < d then
    if hy : y < d then
      if hz : z < d then (m ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩).val else 0
    else 0
  else 0

private theorem fp_fixedCase {A B : Type} (ea : BitEncoding A) (eb : BitEncoding B)
    (n : ℕ) (key : A → ℕ) (hk : FP ea BitEncoding.nat key)
    (f : Fin n → A → B) (hf : ∀ i, FP ea eb (f i)) (fallback : A → B)
    (hd : FP ea eb fallback) :
    FP ea eb (fun a => if h : key a < n then f ⟨key a,h⟩ a else fallback a) := by
  induction n with
  | zero => simpa using hd
  | succ n ih =>
    let g : Fin n → A → B := fun i => f i.castSucc
    have hg : ∀ i, FP ea eb (g i) := fun i => hf i.castSucc
    have hrec := ih g hg
    have ht := ((hk).pair (fp_const ea BitEncoding.nat n)).comp NatListSumMachines.fp_equal
    have hlast := hf (Fin.last n)
    apply (ht.ite hlast hrec).congr
    intro a
    by_cases he : key a = n
    · simp only [he, Nat.lt_succ_self, ↓reduceDIte, decide_true, ↓reduceIte]
      rfl
    · simp only [he, ↓reduceIte]
      by_cases hlt : key a < n
      · simp only [hlt, ↓reduceDIte, show key a < n+1 by omega]
        rfl
      · simp only [hlt, ↓reduceDIte, show ¬key a < n+1 by omega]

/-- The operation table is compiled into a finite circuit; no oracle is used. -/
theorem fp_operation (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d) :
    FP tripleCode BitEncoding.nat (fun p => operation d m p.1 p.2.1 p.2.2) := by
  have hx := fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)
  have hy := (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)).comp
    (fp_fst BitEncoding.nat BitEncoding.nat)
  have hz := (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat)).comp
    (fp_snd BitEncoding.nat BitEncoding.nat)
  exact fp_fixedCase tripleCode BitEncoding.nat d _ hx _
    (fun x => fp_fixedCase tripleCode BitEncoding.nat d _ hy _
      (fun y => fp_fixedCase tripleCode BitEncoding.nat d _ hz _
        (fun z => fp_const _ _ (m x y z).val) _ (fp_const _ _ 0)) _ (fp_const _ _ 0))
    _ (fp_const _ _ 0)

/-- Coordinatewise operation on raw words; the first word fixes output length. -/
def mapOperation (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d)
    (xs ys zs : List ℕ) : List ℕ :=
  xs.zipIdx.map (fun p => operation d m p.1 (ys.getD p.2 0) (zs.getD p.2 0))

@[simp] theorem mapOperation_length (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d)
    (xs ys zs : List ℕ) : (mapOperation d m xs ys zs).length = xs.length := by
  simp [mapOperation]

/-- Actual polynomial-time coordinatewise map for unbounded tuple length. -/
theorem fp_mapOperation (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d) :
    FP (wordCode.prod (wordCode.prod wordCode)) wordCode
      (fun p => mapOperation d m p.1 p.2.1 p.2.2) := by
  let ec := wordCode.prod wordCode
  let ei := BitEncoding.nat.prod BitEncoding.nat
  have hctx := fp_fst ec ei
  have hys := hctx.comp (fp_fst wordCode wordCode)
  have hzs := hctx.comp (fp_snd wordCode wordCode)
  have hrow := fp_snd ec ei
  have hx := hrow.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hi := hrow.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hy := (hys.pair hi).comp (fp_getD BitEncoding.nat 0)
  have hz := (hzs.pair hi).comp (fp_getD BitEncoding.nat 0)
  have hbody := (hx.pair (hy.pair hz)).comp (fp_operation d m)
  have hxs := (fp_fst wordCode ec).comp (ListIndexMachines.fp_zipIdx BitEncoding.nat)
  exact ((fp_snd wordCode ec).pair hxs).comp
    (ListContextMachines.fp_mapWithContext ec ei BitEncoding.nat _ hbody)

end ComplexCSP.ComplexityWitnessPrimitives
