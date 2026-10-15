import Paper2.Complexity.ClosedNetworkSemantics
import Paper2.Algebraic.EncodingSize
import Mathlib.Tactic.Linarith

/-! Polynomial length of the actual framed native graph bytes in terms of
literal vertex/edge counts and a fixed-family arity/label bound. -/
namespace Paper2.BellReduction
open Complexity Computability Algebraic

private theorem nat_code_bound (n : ℕ) : (encodingNatBool.encode n).length ≤ n+1 := by
  change (encodeNat n).length ≤ n+1
  rw [encodeNat_length]
  exact (Nat.size_le.mpr n.lt_two_pow_self).trans (Nat.le_succ n)

private theorem list_code_bound {A : Type} (e : Encoding A Bool) (xs : List A) (B : ℕ)
    (h : ∀ x ∈ xs, (e.encode x).length ≤ B) :
    ((framedListEncoding e).encode xs).length ≤ xs.length*(2*B+2)+1 := by
  induction xs with
  | nil => simp [framedListEncoding,framedListEncode]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [framedListEncoding,framedListEncode,List.length_cons,List.length_append,frame_length]
    change (framedListEncode e xs).length ≤ _ at ht
    nlinarith

private theorem endpoint_code_bound (E : ℕ) (p : RawEndpoint) (hp : p.1 < E) :
    (RawClosedNetwork.endpointEncoding.encode p).length ≤ 2*E+4 := by
  have hn := nat_code_bound p.1
  change ((framedProductEncoding encodingNatBool encodingBoolBool).encode p).length ≤ _
  rw [framedProductEncoding_length]
  change 2*(encodingNatBool.encode p.1).length+1+1 ≤ _
  omega

/-- A deliberately loose quadratic bound uses actual endpoint addresses and
fixed family sizes, never a freely chosen instance-size annotation. -/
theorem raw_encoding_length_bound (G : RawClosedNetwork) (s R : ℕ) (arity : ℕ → ℕ)
    (hG : G.WellFormed s 1 arity) (hR : ∀ i < s, arity i ≤ R) :
    (RawClosedNetwork.encoding.encode G).length ≤
      (8*s+56*R+16)*(G.vertices.length+G.edges.length+1)^2 := by
  let S := G.vertices.length+G.edges.length+1
  have hV : G.vertices.length ≤ S := by omega
  have hE : G.edges.length+1 ≤ S := by omega
  have hS : 1 ≤ S := by omega
  have hver (v : RawVertex) (hv : v ∈ G.vertices) :
      (RawClosedNetwork.vertexEncoding.encode v).length ≤ (2*s+14*R+2)*S := by
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hv
    have hs := (hG.1 i).1
    have hl := (hG.1 i).2
    rw [hi] at hs hl
    have hp (p : RawEndpoint) (hp : p ∈ v.2) : p.1 < G.edges.length := by
      apply (G.mem_expectedEndpoints_iff p).mp
      apply hG.2.2.mem_iff.mp
      exact List.mem_flatten.mpr ⟨v.2,List.mem_map.mpr ⟨v,hv,rfl⟩,hp⟩
    have he := list_code_bound RawClosedNetwork.endpointEncoding v.2 (2*G.edges.length+4)
      (fun p hm => endpoint_code_bound _ p (hp p hm))
    have hn := nat_code_bound v.1
    have har : v.2.length ≤ R := hl ▸ hR _ hs
    change ((framedProductEncoding encodingNatBool
      (framedListEncoding RawClosedNetwork.endpointEncoding)).encode v).length ≤ _
    rw [framedProductEncoding_length]
    have hx : v.2.length*(2*(2*G.edges.length+4)+2) ≤ R*(14*S) :=
      Nat.mul_le_mul har (by omega)
    have hn' : 2*(encodingNatBool.encode v.1).length+2 ≤ (2*s+2)*S := by
      have hm := Nat.mul_le_mul_left (2*s+2) hS
      omega
    nlinarith
  have hv := list_code_bound RawClosedNetwork.vertexEncoding G.vertices ((2*s+14*R+2)*S) hver
  have hedge (e : ℕ) (he : e ∈ G.edges) : (encodingNatBool.encode e).length ≤ 1 := by
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
    have hh := hG.2.1 i
    rw [hi] at hh
    have hz : e = 0 := by omega
    rw [hz]
    exact Nat.zero_le 1
  have he := list_code_bound encodingNatBool G.edges 1 hedge
  change ((framedProductEncoding (framedListEncoding RawClosedNetwork.vertexEncoding)
    (framedListEncoding encodingNatBool)).encode (G.vertices,G.edges)).length ≤ _
  rw [framedProductEncoding_length]
  have hv' : G.vertices.length*(2*((2*s+14*R+2)*S)+2) ≤ (4*s+28*R+6)*S^2 := by
    have hx := Nat.mul_le_mul hV (show 2*((2*s+14*R+2)*S)+2 ≤ (4*s+28*R+6)*S by nlinarith)
    nlinarith
  have he' : G.edges.length*4+4 ≤ 4*S^2 := by nlinarith
  change _ ≤ (8*s+56*R+16)*S^2
  nlinarith

end Paper2.BellReduction
