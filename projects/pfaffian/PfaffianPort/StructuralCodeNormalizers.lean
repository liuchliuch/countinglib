import PfaffianPort.ValidEncodedWords
import PfaffianPort.NatCanonicalizationMachine
import PfaffianPort.InputLengthMachine
import PfaffianPort.MachinePairing
import PfaffianPort.MachineOutputTransport

/-! Actual normalization of every successfully decoded raw structural code.
Input words are retained literally by the valid-word representation; no
canonical-input restriction or raw-decoder identity is introduced. -/
namespace PfaffianPort.Complexity.BitEncoding
open Turing PfaffianPort.MachineComposition PfaffianPort.MachinePairing
open ValidWord

abbrev Normalizer {α : Type} (e : BitEncoding α):=
  TM2ComputableInPolyTime (ValidWord.encoding e).encode e.encode ValidWord.value

noncomputable def natNormalizer : Normalizer nat:=by
  let c:=transportInputComputer (ValidWord.encoding nat) bits nat ValidWord.raw (by intro w; rfl)
    PfaffianPort.NatCanonicalizationMachine.decodeComputer
  have he : (Computability.decodeNat ∘ (ValidWord.raw (e:=nat)))=ValidWord.value:=by
    funext w
    have h:=w.decode_raw
    exact Option.some.inj h
  rw [he] at c
  exact c

noncomputable def unaryNormalizer : Normalizer unaryNat:=by
  let c:=transportInputComputer (ValidWord.encoding unaryNat) bits unaryNat ValidWord.raw (by intro w; rfl)
    (PfaffianPort.InputLengthMachine.computer bits)
  have he : ((fun w : Bits=>w.length) ∘ (ValidWord.raw (e:=unaryNat)))=ValidWord.value:=by
    funext w
    have h:=w.decode_raw
    exact Option.some.inj h
  change TM2ComputableInPolyTime (ValidWord.encoding unaryNat).encode unaryNat.encode
    ((fun w : Bits=>w.length) ∘ ValidWord.raw) at c
  rw [he] at c
  exact c

noncomputable def prodFirstComputer {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) :
    TM2ComputableInPolyTime (ValidWord.encoding (ea.prod eb)).encode
      (ValidWord.encoding ea).encode (fun w=>(ValidWord.split eb w).1):=by
  let c:=transportInputComputer (ValidWord.encoding (ea.prod eb))
    ((ValidWord.encoding ea).prod (ValidWord.encoding eb)) (ValidWord.encoding ea)
    (ValidWord.split eb) (fun w=>(ValidWord.split_raw eb w).symm)
    (PairProjectionMachines.fstEncodingComputer (ValidWord.encoding ea) (ValidWord.encoding eb))
  exact c

noncomputable def prodSecondComputer {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) :
    TM2ComputableInPolyTime (ValidWord.encoding (ea.prod eb)).encode
      (ValidWord.encoding eb).encode (fun w=>(ValidWord.split eb w).2):=by
  let c:=transportInputComputer (ValidWord.encoding (ea.prod eb))
    ((ValidWord.encoding ea).prod (ValidWord.encoding eb)) (ValidWord.encoding eb)
    (ValidWord.split eb) (fun w=>(ValidWord.split_raw eb w).symm)
    (PairProjectionMachines.sndEncodingComputer (ValidWord.encoding ea) (ValidWord.encoding eb))
  exact c

/-- Normalize both recursively parsed raw components, then rebuild the exact
framed product. All parsing and pairing are actual previously proved machines. -/
noncomputable def prodNormalizer {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    (ha : Normalizer ea) (hb : Normalizer eb) : Normalizer (ea.prod eb):=by
  let left:=composeComputers (prodFirstComputer ea eb) ha
  let right:=composeComputers (prodSecondComputer ea eb) hb
  let c:=pairComputers left right
  have he : (fun w : ValidWord (ea.prod eb)=>
      ((ValidWord.split eb w).1.value,(ValidWord.split eb w).2.value))=ValidWord.value:=by
    funext w
    exact (ValidWord.split_value eb w).symm
  change TM2ComputableInPolyTime (ValidWord.encoding (ea.prod eb)).encode (ea.prod eb).encode
    (fun w=>((ValidWord.split eb w).1.value,(ValidWord.split eb w).2.value)) at c
  rw [he] at c
  exact c

noncomputable def retractWord {α β : Type} (e : BitEncoding β) (f : α→β) (g : β→α)
    (hgf : ∀a,g (f a)=a) (w : ValidWord (e.retract f g hgf)) : ValidWord e:=by
  refine ⟨w.raw,?_⟩
  obtain ⟨a,ha⟩:=w.property
  change (e.decode w.raw).map g=some a at ha
  cases hd:e.decode w.raw with
  | none=>simp only [hd, Option.map_none, reduceCtorEq] at ha
  | some b=>exact ⟨b,rfl⟩

theorem retractWord_value {α β : Type} (e : BitEncoding β) (f : α→β) (g : β→α)
    (hgf : ∀a,g (f a)=a) (w : ValidWord (e.retract f g hgf)) :
    w.value=g (retractWord e f g hgf w).value:=by
  apply ValidWord.value_eq
  change (e.decode w.raw).map g=some _
  have hd: e.decode w.raw=some (retractWord e f g hgf w).value:=
    (retractWord e f g hgf w).decode_raw
  rw [hd]
  rfl

/-- Bijective structural wrappers preserve normalization. The reverse identity
is essential: noninjective normalization such as rational reduction is not
smuggled through this codeword-only transport. -/
noncomputable def retractNormalizer {α β : Type} (e : BitEncoding β) (f : α→β) (g : β→α)
    (hgf : ∀a,g (f a)=a) (hfg : ∀b,f (g b)=b) (h : Normalizer e) :
    Normalizer (e.retract f g hgf):=by
  let c:=transportInputComputer (ValidWord.encoding (e.retract f g hgf))
    (ValidWord.encoding e) e (retractWord e f g hgf) (by intro w; rfl) h
  apply transportOutputComputer (ValidWord.encoding (e.retract f g hgf)) e (e.retract f g hgf)
    (computer:=c)
  intro w
  change e.encode (retractWord e f g hgf w).value = e.encode (f w.value)
  rw [retractWord_value, hfg]

end PfaffianPort.Complexity.BitEncoding
