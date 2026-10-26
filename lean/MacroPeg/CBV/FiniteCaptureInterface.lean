import MacroPeg.CBV.FiniteResidualControl

namespace Shallot.MacroPeg.CBV.FiniteCaptureInterface

open CaptureObservability FiniteResidualControl

/-! This is an obstruction to flattening a prefix computation into finite
control and a bounded tuple of opaque strings. It is not a language-class
separation: the witnessing balanced language already has a macro-free PEG.
The entering control and captured tuple depend only on the consumed prefix;
an unbounded pending caller stack is not part of this interface. -/

def shape (E : List (List Char)) : List Bool := E.map List.isEmpty

def shapes : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (shapes n).map (true :: ·) ++ (shapes n).map (false :: ·)

theorem shape_mem (E : List (List Char)) : shape E ∈ shapes E.length := by
  induction E with
  | nil => simp [shape, shapes]
  | cons w E ih =>
    change E.map List.isEmpty ∈ shapes E.length at ih
    cases w <;> simp [shape, shapes, ih, List.mem_map]

/-- A nonempty dead value has no observable payload. Its only distinction
from an empty value is whether replay succeeds without consuming input. -/
theorem shape_agree {x : List Char} {E F : List (List Char)}
    (hE : ∀ w ∈ E, w ≠ [] → Unreplayable x w)
    (hF : ∀ w ∈ F, w ≠ [] → Unreplayable x w)
    (heq : shape E = shape F) : EnvAgree x E F := by
  induction E generalizing F with
  | nil =>
    cases F with
    | nil => intro k p hp; rfl
    | cons w F => simp [shape] at heq
  | cons u E ih =>
    cases F with
    | nil => simp [shape] at heq
    | cons v F =>
      have hh : u.isEmpty = v.isEmpty ∧ shape E = shape F := by
        simpa [shape] using heq
      have ht := ih (fun w hw => hE w (by simp [hw]))
        (fun w hw => hF w (by simp [hw])) hh.2
      intro k p hp
      cases k with
      | succ k => exact ht k p hp
      | zero =>
        cases u with
        | nil =>
          cases v with
          | nil => rfl
          | cons c v => simp at hh
        | cons c u =>
          cases v with
          | nil => simp at hh
          | cons d v =>
            simp only [parameterRest, List.getElem?_cons_zero, Option.bind_some]
            rw [hE _ (by simp) (by simp) p hp, hF _ (by simp) (by simp) p hp]

/-- Pigeonhole for an explicitly enumerated finite set; no classical
choice or computability assumption on the proposed encoding is needed. -/
theorem no_finite_encoding {α : Type} [BEq α] [LawfulBEq α]
    (codes : List α) (encode : Nat → α) (hin : ∀ n, encode n ∈ codes)
    (hinj : ∀ n k, encode n = encode k → n = k) : False := by
  apply no_nat_embedding codes.length (fun n =>
    ⟨codes.idxOf (encode n), List.idxOf_lt_length_of_mem (hin n)⟩)
  intro n k heq
  apply hinj n k
  have he := congrArg Fin.val heq
  change codes.idxOf (encode n) = codes.idxOf (encode k) at he
  have hnb := List.idxOf_lt_length_of_mem (hin n)
  have hkb := List.idxOf_lt_length_of_mem (hin k)
  have hn : codes[codes.idxOf (encode n)] = encode n := by
    exact beq_iff_eq.mp (List.findIdx_getElem (w := hnb))
  have hk : codes[codes.idxOf (encode k)] = encode k := by
    exact beq_iff_eq.mp (List.findIdx_getElem (w := hkb))
  simp only [he] at hn
  exact hn.symm.trans hk

/-- Any fixed number of independently chosen captures is insufficient,
even with arbitrary prefix-dependent finite control and arbitrary recursive
target rules. Empty values, duplication, and arbitrary dead payloads are
allowed. Only the bound on the number of slots is fixed; string lengths
and the actual number of slots may vary with the prefix. -/
theorem no_bounded_dead_equality (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) (K R : Nat)
    (body : Fin K → MExp) (hbody : ∀ q, (body q).FirstOrder)
    (input : Nat → List Char) (state : Nat → Fin K) (capture : Nat → List (List Char))
    (hlen : ∀ n, (capture n).length ≤ R)
    (hdead : ∀ n m w, w ∈ capture n → w ≠ [] → Unreplayable (input m) w) :
    ¬ ∀ n m,
      SObs g s (MExp.subst ((capture n).map MExp.lit) (body (state n)))
        (input m) (some []) ↔ n = m := by
  intro hspec
  let masks := (List.range (R + 1)).flatMap shapes
  let codes := (List.finRange K).flatMap (fun q => masks.map (q, ·))
  let encode := fun n => (state n, shape (capture n))
  apply no_finite_encoding codes encode
  · intro n
    have hm := shape_mem (capture n)
    have hmasks : shape (capture n) ∈ masks :=
      List.mem_flatMap.mpr ⟨(capture n).length, List.mem_range.mpr (by have := hlen n; omega), hm⟩
    exact List.mem_flatMap.mpr ⟨state n, List.mem_finRange _,
      List.mem_map.mpr ⟨shape (capture n), hmasks, rfl⟩⟩
  · intro n k heq
    have hstate : state n = state k := congrArg Prod.fst heq
    have hshape : shape (capture n) = shape (capture k) := congrArg Prod.snd heq
    have henv := shape_agree (hdead n n) (hdead k n) hshape
    have hstart := (hspec n n).mpr rfl
    have hnext := (observations_iff hg hs henv (body (state n)) (hbody _) (some [])).mp hstart
    rw [hstate] at hnext
    exact ((hspec k n).mp hnext).symm

theorem no_bounded_dead_interface (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) (K R : Nat)
    (body : Fin K → MExp) (hbody : ∀ q, (body q).FirstOrder)
    (state : Nat → Fin K) (capture : Nat → List (List Char))
    (hlen : ∀ n, (capture n).length ≤ R)
    (hdead : ∀ n m w, w ∈ capture n → w ≠ [] → Unreplayable (suffix m) w) :
    ¬ ∀ n m,
      SObs g s (MExp.subst ((capture n).map MExp.lit) (body (state n)))
        (suffix m) (some []) ↔ n = m :=
  no_bounded_dead_equality g hg s hs K R body hbody suffix state capture hlen hdead

def PrefixAlphabet (E : List (List Char)) : Prop :=
  ∀ w ∈ E, ∀ c ∈ w, c = 'a' ∨ c = 'b'

theorem prefix_alphabet_dead {E : List (List Char)} (h : PrefixAlphabet E)
    (m : Nat) (w : List Char) (hw : w ∈ E) (hne : w ≠ []) :
    Unreplayable (suffix m) w := by
  cases w with
  | nil => exact False.elim (hne rfl)
  | cons c w =>
    apply absent_head
    have hc := h _ hw c (by simp)
    rcases hc with rfl | rfl <;> simp [suffix]

/-- Splitting, copying or otherwise encoding the old prefix into any fixed
tuple over its alphabet cannot implement a general prefix derivative.
This compares whole-input languages at the interface, not exact residuals. -/
theorem no_balanced_factorization (g : MGrammar) (hg : g.FirstOrder)
    (s : Strategy) (hs : s ≠ .callByName) (K R : Nat)
    (body : Fin K → MExp) (hbody : ∀ q, (body q).FirstOrder)
    (state : Nat → Fin K) (capture : Nat → List (List Char))
    (hlen : ∀ n, (capture n).length ≤ R)
    (halphabet : ∀ n, PrefixAlphabet (capture n)) :
    ¬ ∀ n m,
      SObs balancedGrammar .callByValuePar balancedStart
          (capturedPrefix n ++ suffix m) (some []) ↔
      SObs g s (MExp.subst ((capture n).map MExp.lit) (body (state n)))
        (suffix m) (some []) := by
  intro hspec
  apply no_bounded_dead_interface g hg s hs K R body hbody state capture hlen
    (fun n m => prefix_alphabet_dead (halphabet n) m)
  intro n m
  exact (hspec n m).symm.trans (balanced_recognizes .callByValuePar n m)

end Shallot.MacroPeg.CBV.FiniteCaptureInterface
