import MacroPeg.CBV.PrefixDecrement
import MacroPeg.CBVtoCBN.SpanValues

namespace Shallot.MacroPeg.CBV.PrefixCounters

open RootObservation

def atPosition (counter body : MExp) : MExp := .andP (.seq counter body)

def charAt (x : List Char) (p : Nat) (c : Char) : Bool :=
  match x[p]? with
  | none => false
  | some d => Shallot.beqChar c d

/-- A stored prefix provides random access to the character immediately
following it, while the surrounding computation stays at the input root. -/
theorem charAt_test (g : MGrammar) (x : List Char) (p : Nat) (c : Char) :
    Test g .callByValuePar (atPosition (.lit (x.take p)) (.chr c)) x (charAt x p c) := by
  have hl : SObs g .callByValuePar (.lit (x.take p)) x (some (x.drop p)) :=
    ⟨_, literal_take g .callByValuePar x p, rfl⟩
  unfold charAt
  rw [← List.head?_drop]
  cases hd : x.drop p with
  | nil =>
    exact peek_failure (seq_ok hl ⟨_, by rw [hd]; exact .chrEmpty c, rfl⟩)
  | cons d ds =>
    cases hb : Shallot.beqChar c d with
    | true =>
      simp only [List.head?_cons, hb]
      exact peek_success (seq_ok hl ⟨_, by rw [hd]; exact .chrOk c d ds hb, rfl⟩)
    | false =>
      simp only [List.head?_cons, hb]
      exact peek_failure (seq_ok hl ⟨_, by rw [hd]; exact .chrFail c d ds hb, rfl⟩)

def sameCharacter (alphabet : List Char) (a b : MExp) : MExp :=
  alternatives (alphabet.map (fun c => .seq (atPosition a (.chr c)) (atPosition b (.chr c))))

def sameCharacterAt (alphabet : List Char) (x : List Char) (a b : Nat) : Bool :=
  alphabet.any (fun c => charAt x a c && charAt x b c)

theorem sameCharacter_test (g : MGrammar) (alphabet : List Char)
    (x : List Char) (a b : Nat) :
    Test g .callByValuePar
      (sameCharacter alphabet (.lit (x.take a)) (.lit (x.take b))) x
      (sameCharacterAt alphabet x a b) :=
  alternatives_test alphabet _ _ (fun c _ => test_seq (charAt_test g x a c) (charAt_test g x b c))

/-- Coverage of the finite alphabet gives an exact symbol-equality test.
This is equality of original input characters, not of a re-encoding. -/
theorem sameCharacterAt_iff (alphabet : List Char) (x : List Char) (a b : Nat)
    (hcover : ∀ c ∈ x, c ∈ alphabet) :
    sameCharacterAt alphabet x a b = true ↔ ∃ c, x[a]? = some c ∧ x[b]? = some c := by
  unfold sameCharacterAt
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, _, hc⟩
    have hh := Bool.and_eq_true_iff.mp hc
    cases hA : x[a]? with
    | none => simp [charAt, hA] at hh
    | some d =>
      cases hB : x[b]? with
      | none => simp [charAt, hB] at hh
      | some e =>
        have hcd : c = d := by
          have hn : c.toNat = d.toNat := by simpa [charAt, hA, Shallot.beqChar] using hh.1
          exact Char.toNat_inj.mp hn
        have hce : c = e := by
          have hn : c.toNat = e.toNat := by simpa [charAt, hB, Shallot.beqChar] using hh.2
          exact Char.toNat_inj.mp hn
        exact ⟨c, by simp [hcd], by simp [hce]⟩
  · rintro ⟨c, hA, hB⟩
    have hm : c ∈ x := List.mem_of_getElem? hA
    exact ⟨c, hcover c hm, by simp [charAt, hA, hB, Shallot.beqChar]⟩

end Shallot.MacroPeg.CBV.PrefixCounters
