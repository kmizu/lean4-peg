import Shallot.Peg.Total.Guarded
import Shallot.Peg.Total.Transform

/-!
# The specification of the transformed expressions

The behavior of an original expression `e` at `x` with open set `S` (`Beh`) is one of four classes (`Cl`):
success consuming nothing (`okE`), success leaving a proper suffix `r` (`okC r`), failure (`fl`) or loop, i.e. no
checked derivation (`lp`). `Good G T x c` says what the three transformed expressions `T` (`Transform.lean`) do in
the grammar `G` for each class; `Spec` says that some class holds and the transformed expressions behave
accordingly. This file has the helpers on `Good`, the leaves and the calls; the compound expressions are in
`SpecSeq.lean` and `SpecStar.lean`.
-/

namespace Shallot

/-- The four behaviors of an expression at a position. -/
inductive Cl where
  | okE
  | okC (r : List Char)
  | fl
  | lp

/-- The behavior of `e` at `x` with open set `S`, in checked derivations. -/
def Beh (g : Grammar) (S : Nat) (e : PExp) (x : List Char) : Cl → Prop
  | .okE => ∃ t, DS g S e x (.ok t x)
  | .okC r => r ≠ x ∧ ∃ t, DS g S e x (.ok t r)
  | .fl => DS g S e x .fail
  | .lp => ∀ o, ¬ DS g S e x o

/-- `e` succeeds at `x` leaving `r`. -/
def OkD (G : Grammar) (e : PExp) (x r : List Char) : Prop := ∃ t, Derives G e x (.ok t r)

/-- `e` fails at `x`. -/
def FlD (G : Grammar) (e : PExp) (x : List Char) : Prop := Derives G e x .fail

/-- What the transformed expressions do, for each behavior of the original. -/
def Good (G : Grammar) (T : Tr) (x : List Char) : Cl → Prop
  | .okE => OkD G T.z x x ∧ FlD G T.p x ∧ FlD G T.l x
  | .okC r => FlD G T.z x ∧ OkD G T.p x r ∧ FlD G T.l x
  | .fl => FlD G T.z x ∧ FlD G T.p x ∧ FlD G T.l x
  | .lp => FlD G T.z x ∧ FlD G T.p x ∧ ∃ r, OkD G T.l x r

/-- **The specification**: the original has some behavior, and the transformed expressions follow it. -/
def Spec (g G : Grammar) (T : Tr) (S : Nat) (e : PExp) (x : List Char) : Prop :=
  ∃ c, Beh g S e x c ∧ Good G T x c

/-! ## Helpers -/

theorem fail0 {G : Grammar} {x : List Char} : FlD G fl0 x := .notOk _ _ _ _ (.eps x)

theorem r_okE {G : Grammar} {T : Tr} {x : List Char} (h : Good G T x .okE) : OkD G T.r x x := by
  obtain ⟨⟨t, hz⟩, -, -⟩ := h; exact ⟨_, .altL _ _ _ _ _ hz⟩

theorem r_okC {G : Grammar} {T : Tr} {x r : List Char} (h : Good G T x (.okC r)) : OkD G T.r x r := by
  obtain ⟨hz, ⟨t, hp⟩, -⟩ := h; exact ⟨_, .altR _ _ _ _ _ hz hp⟩

theorem r_fl {G : Grammar} {T : Tr} {x : List Char} (h : Good G T x .fl) : FlD G T.r x := by
  obtain ⟨hz, hp, -⟩ := h; exact .altFail _ _ _ hz hp

theorem r_lp {G : Grammar} {T : Tr} {x : List Char} (h : Good G T x .lp) : FlD G T.r x := by
  obtain ⟨hz, hp, -⟩ := h; exact .altFail _ _ _ hz hp

/-- `fl` succeeds where the original fails. -/
theorem fl_ok {G : Grammar} {T : Tr} {x : List Char} (h : Good G T x .fl) : OkD G T.fl x x := by
  exact ⟨_, .seqOk _ _ _ _ _ _ _ (.notFail _ _ (r_fl h)) (.notFail _ _ h.2.2)⟩

/-- `fl` fails where the original succeeds or loops. -/
theorem fl_fail {G : Grammar} {T : Tr} {x : List Char} {c : Cl} (h : Good G T x c) (hc : ¬ c = .fl) :
    FlD G T.fl x := by
  cases c with
  | okE => obtain ⟨t, hr⟩ := r_okE h; exact .seqFail₁ _ _ _ (.notOk _ _ _ _ hr)
  | okC r => obtain ⟨t, hr⟩ := r_okC h; exact .seqFail₁ _ _ _ (.notOk _ _ _ _ hr)
  | fl => exact absurd rfl hc
  | lp =>
    obtain ⟨r, t, hl⟩ := h.2.2
    exact .seqFail₂ _ _ _ _ _ (.notFail _ _ (r_lp h)) (.notOk _ _ _ _ hl)

/-- A checked success leaving a proper suffix shortens the input. -/
theorem ds_lt {g : Grammar} {S : Nat} {e : PExp} {x r : List Char} {t : PTree} (h : DS g S e x (.ok t r))
    (hne : r ≠ x) : r.length < x.length := by
  obtain ⟨p, hp⟩ := ds_suffix h; exact suffix_lt hp hne

/-! ## Leaves -/

theorem spec_eps (g G : Grammar) (S : Nat) (x : List Char) : Spec g G ⟨.eps, fl0, fl0⟩ S .eps x :=
  ⟨.okE, ⟨_, .eps S x⟩, ⟨_, .eps x⟩, fail0, fail0⟩

theorem spec_any (g G : Grammar) (S : Nat) (x : List Char) : Spec g G ⟨fl0, .any, fl0⟩ S .any x := by
  cases x with
  | nil => exact ⟨.fl, .anyFail S, fail0, .anyFail, fail0⟩
  | cons c rest => exact ⟨.okC rest, ⟨(List.cons_ne_self c rest).symm, _, .anyOk S c rest⟩, fail0, ⟨_, .anyOk c rest⟩, fail0⟩

theorem spec_chr (g G : Grammar) (S : Nat) (c : Char) (x : List Char) :
    Spec g G ⟨fl0, .chr c, fl0⟩ S (.chr c) x := by
  cases x with
  | nil => exact ⟨.fl, .chrEmpty S c, fail0, .chrEmpty c, fail0⟩
  | cons d rest =>
    cases h : beqChar c d with
    | true =>
      exact ⟨.okC rest, ⟨(List.cons_ne_self d rest).symm, _, .chrOk S c d rest h⟩, fail0, ⟨_, .chrOk c d rest h⟩,
        fail0⟩
    | false => exact ⟨.fl, .chrFail S c d rest h, fail0, .chrFail c d rest h, fail0⟩

theorem spec_range (g G : Grammar) (S : Nat) (lo hi : Char) (x : List Char) :
    Spec g G ⟨fl0, .range lo hi, fl0⟩ S (.range lo hi) x := by
  cases x with
  | nil => exact ⟨.fl, .rangeEmpty S lo hi, fail0, .rangeEmpty lo hi, fail0⟩
  | cons d rest =>
    cases h : (leChar lo d && leChar d hi) with
    | true =>
      exact ⟨.okC rest, ⟨(List.cons_ne_self d rest).symm, _, .rangeOk S lo hi d rest h⟩, fail0,
        ⟨_, .rangeOk lo hi d rest h⟩, fail0⟩
    | false => exact ⟨.fl, .rangeFail S lo hi d rest h, fail0, .rangeFail lo hi d rest h, fail0⟩

/-- A literal match removes as many characters as the literal has. -/
theorem stripPrefix?_length : ∀ (s x r : List Char), stripPrefix? s x = some r → x.length = s.length + r.length
  | [], x, r, h => by simp [stripPrefix?] at h; subst h; simp
  | _ :: _, [], _, h => by simp [stripPrefix?] at h
  | c :: cs, d :: ds, r, h => by
    simp only [stripPrefix?] at h
    split at h
    · have := stripPrefix?_length cs ds r h; simp; omega
    · cases h

theorem spec_lit (g G : Grammar) (S : Nat) (s x : List Char) : Spec g G (litT s) S (.lit s) x := by
  cases s with
  | nil =>
    have h : stripPrefix? [] x = some x := rfl
    exact ⟨.okE, ⟨_, .litOk S [] x x h⟩, ⟨_, .litOk [] x x h⟩, fail0, fail0⟩
  | cons c cs =>
    cases h : stripPrefix? (c :: cs) x with
    | none => exact ⟨.fl, .litFail S _ x h, fail0, .litFail _ x h, fail0⟩
    | some r =>
      have hne : r ≠ x := by
        intro hr; have := stripPrefix?_length _ _ _ h; subst hr; simp at this
      exact ⟨.okC r, ⟨hne, _, .litOk S _ x r h⟩, fail0, ⟨_, .litOk _ x r h⟩, fail0⟩

/-! ## Calls -/

/-- A call of a missing rule fails. -/
theorem spec_nt_missing (g G : Grammar) {S A : Nat} (x : List Char) (hr : ruleAt g.rules A = none) :
    Spec g G ⟨fl0, fl0, fl0⟩ S (.nt A) x :=
  ⟨.fl, .ntMissing S A x hr, fail0, fail0, fail0⟩

/-- A call of an open rule loops. -/
theorem spec_nt_open (g G : Grammar) {S A : Nat} {e : PExp} (x : List Char) (hr : ruleAt g.rules A = some e)
    (hm : S.testBit A = true) : Spec g G ⟨fl0, fl0, .eps⟩ S (.nt A) x := by
  refine ⟨.lp, ?_, fail0, fail0, x, _, .eps x⟩
  intro o h
  cases h with
  | ntOk _ _ _ _ _ _ _ hm' _ => rw [hm] at hm'; cases hm'
  | ntFail _ _ _ _ _ hm' _ => rw [hm] at hm'; cases hm'
  | ntMissing _ _ _ hr' => rw [hr] at hr'; cases hr'

/-- Lifting a transformed body to the call of its nonterminal. -/
theorem good_nt {G : Grammar} {T : Tr} {x : List Char} {c : Cl} {i0 i1 i2 : Nat} (h0 : ruleAt G.rules i0 = some T.z)
    (h1 : ruleAt G.rules i1 = some T.p) (h2 : ruleAt G.rules i2 = some T.l) (h : Good G T x c) :
    Good G ⟨.nt i0, .nt i1, .nt i2⟩ x c := by
  have lok : ∀ {i e r}, ruleAt G.rules i = some e → OkD G e x r → OkD G (.nt i) x r :=
    fun hr ⟨t, hd⟩ => ⟨_, .ntOk _ _ _ _ _ hr hd⟩
  have lfl : ∀ {i e}, ruleAt G.rules i = some e → FlD G e x → FlD G (.nt i) x :=
    fun hr hd => .ntFail _ _ _ hr hd
  cases c with
  | okE => obtain ⟨a, b, d⟩ := h; exact ⟨lok h0 a, lfl h1 b, lfl h2 d⟩
  | okC r => obtain ⟨a, b, d⟩ := h; exact ⟨lfl h0 a, lok h1 b, lfl h2 d⟩
  | fl => obtain ⟨a, b, d⟩ := h; exact ⟨lfl h0 a, lfl h1 b, lfl h2 d⟩
  | lp => obtain ⟨a, b, r, d⟩ := h; exact ⟨lfl h0 a, lfl h1 b, r, lok h2 d⟩

/-- A call of a closed rule behaves as its body with the rule added to the open set. -/
theorem spec_nt_call {g G : Grammar} {S A : Nat} {e : PExp} {x : List Char} {T : Tr} {i0 i1 i2 : Nat}
    (hr : ruleAt g.rules A = some e) (hm : S.testBit A = false) (h0 : ruleAt G.rules i0 = some T.z)
    (h1 : ruleAt G.rules i1 = some T.p) (h2 : ruleAt G.rules i2 = some T.l) (hb : Spec g G T (ins S A) e x) :
    Spec g G ⟨.nt i0, .nt i1, .nt i2⟩ S (.nt A) x := by
  obtain ⟨c, hB, hG⟩ := hb
  refine ⟨c, ?_, good_nt h0 h1 h2 hG⟩
  cases c with
  | okE => obtain ⟨t, hd⟩ := hB; exact ⟨_, .ntOk _ _ _ _ _ _ hr hm hd⟩
  | okC r => obtain ⟨hne, t, hd⟩ := hB; exact ⟨hne, _, .ntOk _ _ _ _ _ _ hr hm hd⟩
  | fl => exact .ntFail _ _ _ _ hr hm hB
  | lp =>
    intro o h
    cases h with
    | ntOk _ _ _ _ _ _ hr' _ hd => rw [hr] at hr'; cases hr'; exact hB _ hd
    | ntFail _ _ _ _ hr' _ hd => rw [hr] at hr'; cases hr'; exact hB _ hd
    | ntMissing _ _ _ hr' => rw [hr] at hr'; cases hr'

end Shallot
