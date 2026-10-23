import MacroPeg.Properties.QbfHard
import MacroPeg.Properties.ArgEquiv

namespace Shallot.MacroPeg.CBVtoCBN

/-- A closed counter denotes a fixed length on every input, independently of its characters. -/
def LenRep (g : MGrammar) (e : MExp) (k : Nat) : Prop :=
  ∀ x : List Char, MacroObs g e x (if k ≤ x.length then some (x.drop k) else none)

def skipN : Nat → MExp
  | 0 => .eps
  | k + 1 => .seq (skipN k) .any

theorem lenRep_eps (g : MGrammar) : LenRep g .eps 0 := by
  intro x
  simpa using obs_eps (g := g) x

theorem lenRep_any (g : MGrammar) : LenRep g .any 1 := by
  intro x
  cases x with
  | nil => exact obs_any_nil
  | cons c cs => simpa using obs_any_some (g := g) c cs

/-- Sequencing counter expressions adds their represented lengths, without inspecting input values. -/
theorem LenRep.seq {g : MGrammar} {a b : MExp} {k l : Nat} (ha : LenRep g a k) (hb : LenRep g b l) :
    LenRep g (.seq a b) (k + l) := by
  intro x
  by_cases hk : k ≤ x.length
  · have hax : MacroObs g a x (some (x.drop k)) := by simpa only [if_pos hk] using ha x
    have hbx := hb (x.drop k)
    by_cases hl : l ≤ (x.drop k).length
    · have hkl : k + l ≤ x.length := by simp only [List.length_drop] at hl; omega
      simp only [if_pos hl] at hbx
      simpa only [if_pos hkl, List.drop_drop] using obs_seq hax hbx
    · have hkl : ¬ k + l ≤ x.length := by simp only [List.length_drop] at hl; omega
      simp only [if_neg hl] at hbx
      simpa only [if_neg hkl] using obs_seq hax hbx
  · have hkl : ¬ k + l ≤ x.length := by omega
    have hax : MacroObs g a x none := by simpa only [if_neg hk] using ha x
    simpa only [if_neg hkl] using obs_seq_none (b := b) hax

theorem skipN_rep (g : MGrammar) : ∀ k, LenRep g (skipN k) k
  | 0 => lenRep_eps g
  | k + 1 => (skipN_rep g k).seq (lenRep_any g)

theorem skipN_firstOrder : ∀ k, (skipN k).FirstOrder
  | 0 => trivial
  | k + 1 => ⟨skipN_firstOrder k, trivial⟩

/-- Test whether a represented length reaches exactly the end, restoring the input. -/
def exactLengthP (e : MExp) : MExp := andP (.seq e (.notP .any))

/-- A bounded length test, also restoring the input on success. -/
def fitsLengthP (e : MExp) : MExp := andP e

theorem fitsLength_obs {g : MGrammar} {e : MExp} {k : Nat} (he : LenRep g e k) (x : List Char) :
    MacroObs g (fitsLengthP e) x (if k ≤ x.length then some x else none) := by
  by_cases hk : k ≤ x.length
  · simp only [fitsLengthP, if_pos hk]
    exact obs_and_some (by simpa only [if_pos hk] using he x)
  · simp only [fitsLengthP, if_neg hk]
    exact obs_and_none (by simpa only [if_neg hk] using he x)

theorem exactLength_obs {g : MGrammar} {e : MExp} {k : Nat} (he : LenRep g e k) (x : List Char) :
    MacroObs g (exactLengthP e) x (if k = x.length then some x else none) := by
  by_cases hk : k ≤ x.length
  · have hx : MacroObs g e x (some (x.drop k)) := by simpa only [if_pos hk] using he x
    by_cases hEq : k = x.length
    · have hd : x.drop k = [] := by simp [hEq]
      have hn : MacroObs g (.notP .any) (x.drop k) (some []) := by
        rw [hd]
        exact obs_not_none obs_any_nil
      simpa only [exactLengthP, if_pos hEq] using obs_and_some (obs_seq hx hn)
    · have hne : x.drop k ≠ [] := by
        intro hd
        have hlen := congrArg List.length hd
        simp only [List.length_drop, List.length_nil] at hlen
        omega
      have hn : MacroObs g (.notP .any) (x.drop k) none := by
        cases hd : x.drop k with
        | nil => exact False.elim (hne hd)
        | cons c cs => exact obs_not_some (obs_any_some c cs)
      simpa only [exactLengthP, if_neg hEq] using obs_and_none (obs_seq hx hn)
  · have hEq : k ≠ x.length := by omega
    have hx : MacroObs g e x none := by simpa only [if_neg hk] using he x
    simpa only [exactLengthP, if_neg hEq] using obs_and_none (obs_seq_none (b := .notP .any) hx)

/-- A position is supplied by its pre counter; the other argument is a complementary suf counter. -/
def equalPositionP (pre suf : MExp) : MExp := exactLengthP (.seq pre suf)
def lePositionP (pre suf : MExp) : MExp := fitsLengthP (.seq pre suf)
def ltPositionP (pre suf : MExp) : MExp := fitsLengthP (.seq (.seq pre suf) .any)

/-- Complementary counters allow position equality to be checked at the original input root. -/
theorem equalPosition_obs {g : MGrammar} {pre suf : MExp} {p q : Nat}
    (hp : LenRep g pre p) (hq : LenRep g suf q) (x : List Char) (hvalid : q ≤ x.length) :
    MacroObs g (equalPositionP pre suf) x (if p = x.length - q then some x else none) := by
  have he : p + q = x.length ↔ p = x.length - q := by omega
  simpa only [equalPositionP, he] using exactLength_obs (hp.seq hq) x

theorem lePosition_obs {g : MGrammar} {pre suf : MExp} {p q : Nat}
    (hp : LenRep g pre p) (hq : LenRep g suf q) (x : List Char) (hvalid : q ≤ x.length) :
    MacroObs g (lePositionP pre suf) x (if p ≤ x.length - q then some x else none) := by
  have he : p + q ≤ x.length ↔ p ≤ x.length - q := by omega
  simpa only [lePositionP, he] using fitsLength_obs (hp.seq hq) x

theorem ltPosition_obs {g : MGrammar} {pre suf : MExp} {p q : Nat}
    (hp : LenRep g pre p) (hq : LenRep g suf q) (x : List Char) (hvalid : q ≤ x.length) :
    MacroObs g (ltPositionP pre suf) x (if p < x.length - q then some x else none) := by
  have he : p + q + 1 ≤ x.length ↔ p < x.length - q := by omega
  simpa only [ltPositionP, he] using fitsLength_obs ((hp.seq hq).seq (lenRep_any g)) x

/-- A predicate with an explicit total observation has no other observable result. -/
theorem test_success_iff {g : MGrammar} {e : MExp} {x : List Char} (P : Prop) [Decidable P]
    (h : MacroObs g e x (if P then some x else none)) : MacroObs g e x (some x) ↔ P := by
  by_cases hP : P
  · simp only [if_pos hP] at h
    exact ⟨fun _ => hP, fun _ => h⟩
  · simp only [if_neg hP] at h
    constructor
    · intro hx
      have he := macroObs_unique h hx
      cases he
    · exact fun hp => False.elim (hP hp)

theorem equalPosition_iff {g : MGrammar} {pre suf : MExp} {p q : Nat}
    (hp : LenRep g pre p) (hq : LenRep g suf q) (x : List Char) (hvalid : q ≤ x.length) :
    MacroObs g (equalPositionP pre suf) x (some x) ↔ p = x.length - q :=
  test_success_iff _ (equalPosition_obs hp hq x hvalid)

theorem lePosition_iff {g : MGrammar} {pre suf : MExp} {p q : Nat}
    (hp : LenRep g pre p) (hq : LenRep g suf q) (x : List Char) (hvalid : q ≤ x.length) :
    MacroObs g (lePositionP pre suf) x (some x) ↔ p ≤ x.length - q :=
  test_success_iff _ (lePosition_obs hp hq x hvalid)

theorem ltPosition_iff {g : MGrammar} {pre suf : MExp} {p q : Nat}
    (hp : LenRep g pre p) (hq : LenRep g suf q) (x : List Char) (hvalid : q ≤ x.length) :
    MacroObs g (ltPositionP pre suf) x (some x) ↔ p < x.length - q :=
  test_success_iff _ (ltPosition_obs hp hq x hvalid)

theorem positionTests_firstOrder {pre suf : MExp} (hp : pre.FirstOrder) (hq : suf.FirstOrder) :
    (equalPositionP pre suf).FirstOrder ∧ (lePositionP pre suf).FirstOrder ∧
    (ltPositionP pre suf).FirstOrder := ⟨⟨⟨hp, hq⟩, trivial⟩, ⟨hp, hq⟩, ⟨⟨hp, hq⟩, trivial⟩⟩

end Shallot.MacroPeg.CBVtoCBN
