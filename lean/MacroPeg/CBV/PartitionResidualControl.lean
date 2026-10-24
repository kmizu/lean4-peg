import MacroPeg.CBV.CommonOriginCaptures
import MacroPeg.CBV.FiniteResidualControl

/-! Disjoint runtime capture values do not by themselves solve the body-entry
position problem. After all characters of a consumed prefix become absent
from the remaining alphabet, any fixed number of such values has only a
finite observable signature. Unbounded pending callers and suffix-dependent
selection are deliberately outside this local residual interface. -/
namespace Shallot.MacroPeg.CBV.PartitionResidualControl
open CaptureObservability FiniteResidualControl

/-- An absent or nonempty dead value is unmatchable. Only empty values remain
observable, and their positions form finite control for bounded arity. -/
def signature (arity : Nat) (E : List (List Char)) : List Nat :=
  (List.range arity).map (fun k => if E[k]? = some [] then 1 else 0)

theorem signature_length (arity : Nat) (E : List (List Char)) : (signature arity E).length = arity := by
  simp [signature]

theorem signature_bounded (arity : Nat) (E : List (List Char)) :
    ∀ k ∈ signature arity E, k ≤ 1 := by
  intro k hk
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hk
  split <;> omega

theorem signature_finite (arity : Nat) (E : List (List Char)) :
    signature arity E ∈ CommonOriginCaptures.controls 1 arity :=
  (CommonOriginCaptures.mem_controls _ _ _).mpr ⟨signature_length arity E,signature_bounded arity E⟩

theorem signature_lookup (arity : Nat) (E : List (List Char)) (k : Nat) (hk : k < arity) :
    (signature arity E)[k]? = some (if E[k]? = some [] then 1 else 0) := by
  simp [signature,hk]

theorem signature_empty_iff {arity : Nat} {E F : List (List Char)}
    (hE : E.length ≤ arity) (hF : F.length ≤ arity)
    (h : signature arity E = signature arity F) (k : Nat) :
    E[k]? = some [] ↔ F[k]? = some [] := by
  by_cases hk : k < arity
  · have he := congrArg (fun xs : List Nat => xs[k]?) h
    rw [signature_lookup _ _ _ hk,signature_lookup _ _ _ hk] at he
    split at he <;> split at he <;> simp_all
  · have he : E[k]? = none := List.getElem?_eq_none (by omega)
    have hf : F[k]? = none := List.getElem?_eq_none (by omega)
    simp [he,hf]

theorem parameterRest_dead {x : List Char} {E : List (List Char)}
    (hd : ∀ w ∈ E, w ≠ [] → Unreplayable x w) (k p : Nat) (hp : p ≤ x.length) :
    parameterRest x E k p = if E[k]? = some [] then some (sfx x p) else none := by
  cases he : E[k]? with
  | none => simp [parameterRest,he]
  | some w =>
    by_cases hw : w = []
    · subst w; simp [parameterRest,he,Shallot.stripPrefix?]
    · simp [parameterRest,he,hw,hd w (List.mem_of_getElem? he) hw p hp]

/-- The finite empty/nonempty signature determines every possible continuation
observation when all nonempty values are dead on the remaining input. -/
theorem signature_agree {arity : Nat} {x : List Char} {E F : List (List Char)}
    (hE : E.length ≤ arity) (hF : F.length ≤ arity)
    (h : signature arity E = signature arity F)
    (hdE : ∀ w ∈ E, w ≠ [] → Unreplayable x w)
    (hdF : ∀ w ∈ F, w ≠ [] → Unreplayable x w) : EnvAgree x E F := by
  intro k p hp
  rw [parameterRest_dead hdE k p hp,parameterRest_dead hdF k p hp]
  simp only [signature_empty_iff hE hF h k]

theorem parameterRest_at_end (x : List Char) (E : List (List Char)) (k : Nat) :
    parameterRest x E k 0 = if E[k]? = some [] then some [] else none := by
  cases he : E[k]? with
  | none => simp [parameterRest,he]
  | some w => cases w <;> simp [parameterRest,he,sfx,Shallot.stripPrefix?]

theorem signature_eq_of_agree {x : List Char} {E F : List (List Char)}
    (h : EnvAgree x E F) (arity : Nat) : signature arity E = signature arity F := by
  apply List.map_congr_left
  intro k _
  have he := h k 0 (Nat.zero_le _)
  rw [parameterRest_at_end,parameterRest_at_end] at he
  split at he <;> split at he <;> simp_all

/-- On a dead-valued bounded tuple this is the exact observational quotient,
not just a sufficient indistinguishability criterion. -/
theorem agree_iff_signature {arity : Nat} {x : List Char} {E F : List (List Char)}
    (hE : E.length ≤ arity) (hF : F.length ≤ arity)
    (hdE : ∀ w ∈ E, w ≠ [] → Unreplayable x w)
    (hdF : ∀ w ∈ F, w ≠ [] → Unreplayable x w) :
    EnvAgree x E F ↔ signature arity E = signature arity F :=
  ⟨fun h => signature_eq_of_agree h arity,fun h => signature_agree hE hF h hdE hdF⟩

private theorem lookup_idxOf {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ xs : List α, a ∈ xs → xs[xs.idxOf a]? = some a
  | [], h => by simp at h
  | b :: xs, h => by
    by_cases hb : b = a
    · subst b; simp
    · have hm := (List.mem_cons.mp h).resolve_left (fun he => hb he.symm)
      simpa [List.idxOf_cons,show (b == a) = false from beq_eq_false_iff_ne.mpr hb] using lookup_idxOf a xs hm

/-- Finite control plus any bounded tuple of dead runtime strings cannot carry
an unbounded count to the suffix. Empty chunks may encode bits; the proof
includes them in the finite signature instead of treating them as dead. -/
theorem no_finite_tuple_summary (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) (arity K : Nat)
    (body : Fin K → MExp) (hbody : ∀ q, (body q).FirstOrder)
    (state : Nat → Fin K) (E : Nat → List (List Char))
    (hlen : ∀ n, (E n).length ≤ arity)
    (hdead : ∀ n m w, w ∈ E n → w ≠ [] → Unreplayable (suffix m) w) :
    ¬ ∀ n m, SObs g s (MExp.subst ((E n).map MExp.lit) (body (state n)))
      (suffix m) (some []) ↔ n = m := by
  intro hspec
  let keys := CommonOriginCaptures.controls (K+1) (arity+1)
  let key : Nat → List Nat := fun n => (state n).val :: signature arity (E n)
  have hmem : ∀ n, key n ∈ keys := by
    intro n
    apply (CommonOriginCaptures.mem_controls _ _ _).mpr
    refine ⟨by simp [key,signature_length],?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · have hb := (state n).isLt; omega
    · have hb := signature_bounded arity (E n) j hj; omega
  let code : Nat → Fin keys.length := fun n => ⟨keys.idxOf (key n),List.idxOf_lt_length_of_mem (hmem n)⟩
  apply no_nat_embedding keys.length code
  intro n k hcode
  have hindex : keys.idxOf (key n) = keys.idxOf (key k) := congrArg Fin.val hcode
  have hkey : key n = key k := by
    have he := lookup_idxOf (key n) keys (hmem n)
    rw [hindex,lookup_idxOf (key k) keys (hmem k)] at he
    exact (Option.some.inj he).symm
  have hparts := List.cons.inj hkey
  have hstate : state n = state k := Fin.ext hparts.1
  have henv := signature_agree (hlen n) (hlen k) hparts.2
    (hdead n n) (hdead k n)
  have hstart := (hspec n n).mpr rfl
  have hnext := (observations_iff hg hs henv (body (state n)) (hbody _) (some [])).mp hstart
  have haccept : SObs g s (MExp.subst ((E k).map MExp.lit) (body (state k)))
      (suffix n) (some []) := by simpa only [hstate] using hnext
  exact ((hspec k n).mp haccept).symm

theorem partition_dead {parts : List (List Char)} {n : Nat}
    (h : parts.flatten = capturedPrefix n) (m : Nat) :
    ∀ w ∈ parts, w ≠ [] → Unreplayable (suffix m) w := by
  intro w hw hne
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons c rest =>
    have hc : c ∈ capturedPrefix n := by
      rw [← h]
      exact List.mem_flatten.mpr ⟨c::rest,hw,by simp⟩
    have hc' : c = 'a' ∨ c = 'b' := by
      have hm : (n ≠ 0 ∧ c = 'a') ∨ c = 'b' := by simpa [capturedPrefix] using hc
      exact hm.elim (fun h => Or.inl h.2) Or.inr
    rcases hc' with rfl | rfl <;> apply absent_head <;> simp [suffix]

/-- Even an arbitrary prefix-selected partition of the consumed prefix,
with any fixed arity bound and finite body control, is insufficient for this
local factorization. The balanced language itself already has a Seq grammar. -/
theorem no_partitioned_factorization (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) (arity K : Nat)
    (body : Fin K → MExp) (hbody : ∀ q, (body q).FirstOrder)
    (state : Nat → Fin K) (parts : Nat → List (List Char))
    (hlen : ∀ n, (parts n).length ≤ arity)
    (hparts : ∀ n, (parts n).flatten = capturedPrefix n) :
    ¬ ∀ n m,
      SObs balancedGrammar .callByValuePar balancedStart (capturedPrefix n ++ suffix m) (some []) ↔
      SObs g s (MExp.subst ((parts n).map MExp.lit) (body (state n))) (suffix m) (some []) := by
  intro hspec
  apply no_finite_tuple_summary g hg s hs arity K body hbody state parts hlen
    (fun n m => partition_dead (hparts n) m)
  intro n m
  exact (hspec n m).symm.trans (balanced_recognizes .callByValuePar n m)

/-- In particular, the general common-origin chunk representation and any
finite prefix-selected body variants cannot alone repair body-entry position. -/
theorem no_common_origin_factorization (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) (arity K : Nat)
    (body : Fin K → MExp) (hbody : ∀ q, (body q).FirstOrder)
    (state : Nat → Fin K) (words : Nat → List (List Char))
    (hlen : ∀ n, (words n).length ≤ arity)
    (hprefix : ∀ n w, w ∈ words n → w <+: capturedPrefix n)
    (hlongest : ∀ n, capturedPrefix n ∈ words n) :
    ¬ ∀ n m,
      SObs balancedGrammar .callByValuePar balancedStart (capturedPrefix n ++ suffix m) (some []) ↔
      SObs g s (MExp.subst ((CommonOriginCaptures.chunks (words n)).map MExp.lit) (body (state n)))
        (suffix m) (some []) :=
  no_partitioned_factorization g hg s hs arity K body hbody state _
    (fun n => by simpa only [CommonOriginCaptures.chunks_length] using hlen n)
    (fun n => CommonOriginCaptures.chunks_cover (hprefix n) (hlongest n))

end Shallot.MacroPeg.CBV.PartitionResidualControl
